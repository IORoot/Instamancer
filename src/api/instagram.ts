import AwaitLock from "await-lock";
import chalk from "chalk";
import {isLeft} from "fp-ts/lib/Either";
import {Type} from "io-ts";
import {PathReporter} from "io-ts/lib/PathReporter";
import {ThrowReporter} from "io-ts/lib/ThrowReporter";
import * as _ from "lodash/object";
import {
    Browser,
    Headers,
    launch,
    LaunchOptions,
    Page,
    Request,
    Response,
} from "puppeteer";
import * as winston from "winston";
import {
    AsyncPluginEventsType,
    IPlugin,
    IPluginContext,
    PluginEventsType,
    SyncPluginEvents,
    SyncPluginEventsType,
} from "../../plugins";
import {IOptions} from "./api";
import {PostIdSet} from "./postIdSet";
import { exit } from "process";
// import creds from "./creds.json";


type AsyncPluginFunctions = {
    [key in AsyncPluginEventsType]: ((...args: any[]) => Promise<void>)[];
};
type SyncPluginFunctions = {
    [key in SyncPluginEventsType]: ((...args: any[]) => void)[];
};
type PluginFunctions = AsyncPluginFunctions & SyncPluginFunctions;

/**
 * Instagram API wrapper
 */
export class Instagram<PostType> {
    /**
     * Apply defaults to undefined options
     */
    private static defaultOptions(options: IOptions) {
        if (options.enableGrafting === undefined) {
            options.enableGrafting = true;
        }
        if (options.sameBrowser === undefined) {
            options.sameBrowser = false;
        }
        if (options.fullAPI === undefined) {
            options.fullAPI = false;
        }
        if (options.headless === undefined) {
            options.headless = true;
        }
        if (options.logger === undefined) {
            options.logger = winston.createLogger({
                silent: true,
            });
        }
        if (options.silent === undefined) {
            options.silent = true;
        }
        if (options.sleepTime === undefined) {
            options.sleepTime = 2;
        }
        if (options.hibernationTime === undefined) {
            options.hibernationTime = 60 * 20;
        }
        if (options.total === undefined) {
            options.total = 0;
        }
        if (options.screenshots === undefined) {
            options.screenshots = false;
        }
        if (options.screenshotPath === undefined) {
            options.screenshotPath = '/tmp/instamancer';
        }
        if (options.user === undefined) {
            options.user = '';
        }
        if (options.pass === undefined) {
            options.pass = '';
        }
        return options;
    }

    // Resource identifier
    public id: string;
    public url: string;

    // Iteration state
    public started: boolean = false;
    public paused: boolean = false;
    public finished: boolean = false;
    public finishedReason: FinishedReasons;

    // Instagram URLs
    public catchURL: string = "https://www.instagram.com/graphql/query";
    public postURL: string = "https://www.instagram.com/p/";
    public defaultPostURL: string = "https://www.instagram.com/p/";

    // Number of jumps before grafting
    public jumpMod: number = 100;

    // Depth of jumps
    public jumpSize: number = 2;

    // Puppeteer resources
    public page: Page;

    // Logging object
    public logger: winston.Logger;

    // Implementation-specific page functions
    public defaultPageFunctions: (() => void)[] = [];

    // Validations
    private readonly strict: boolean = false;
    private readonly validator: Type<unknown>;

    // Puppeteer state
    private browser: Browser;
    private browserDisconnected: boolean = true;
    private readonly browserInstance?: Browser;
    private readonly headless: boolean;

    // Array of scraped posts and lock
    private postBuffer: PostType[] = [];
    private postBufferLock: AwaitLock = new AwaitLock();

    // Request and Response buffers and locks
    private requestBuffer: Request[] = [];
    private requestBufferLock: AwaitLock = new AwaitLock();
    private responseBuffer: Response[] = [];
    private responseBufferLock: AwaitLock = new AwaitLock();

    // Get full amount of data from API
    private readonly fullAPI: boolean = false;
    private pagePromises: Promise<void>[] = [];

    // Grafting state
    private readonly enableGrafting: boolean = true;
    private readonly sameBrowser: boolean = false;
    private graft: boolean = false;
    private graftURL: string = null;
    private graftHeaders: Headers = null;
    private foundGraft: boolean = false;

    // Hibernation due to rate limiting
    private hibernate: boolean = false;
    private readonly hibernationTime: number = 60 * 20; // 20 minutes

    // Number of jumps before exiting because lack of data
    private failedJumps: number = 20;
    private responseFromAPI: boolean = false;

    // Strings denoting the access methods of API objects
    private readonly pageQuery: string;
    private readonly edgeQuery: string;

    // Cache of post ids
    private postIds: PostIdSet;

    // Iteration variables
    private readonly total: number;
    private index: number = 0;
    private jumps: number = 0;

    // Number of times to attempt to visit url initially
    private readonly maxPageUrlAttempts = 3;
    private pageUrlAttempts = 0;
    private postPageRetries = 5;

    // Output
    private readonly silent: boolean = false;
    private writeLock: AwaitLock = new AwaitLock();

    // Sleep time remaining
    private sleepRemaining: number = 0;

    // Length of time to sleep for
    private readonly sleepTime: number = 2;

    // Proxy for Instagram connection
    private readonly proxyURL: string;

    // Location of chromium / chrome binary executable
    private readonly executablePath: string;

    // Plugins to be run
    private pluginFunctions: PluginFunctions = {
        browser: [],
        construction: [],
        grafting: [],
        postPage: [],
        request: [],
        response: [],
    };

    // AndyP added
    public ipconfig: boolean = false;
    // public creds;
    public endpoint;
    public screenshots;
    public user;
    public pass;
    public screenshotPath: string = "/tmp/instamancer";

    /**
     * Create API wrapper instance
     * @param endpoint the url for the type of resource to scrape
     * @param id the identifier for the resource
     * @param pageQuery the query to identify future pages in the nested API structure
     * @param edgeQuery the query to identify posts in the nested API structure
     * @param options configuration details
     * @param validator response type validator
     */
    constructor(
        endpoint: string,
        id: string,
        pageQuery: string,
        edgeQuery: string,
        options: IOptions = {},
        validator: Type<unknown>,
    ) {
        this.id = id;
        this.postIds = new PostIdSet();
        this.url = endpoint.replace("[id]", id);

        options = Instagram.defaultOptions(options);
        this.total = options.total;
        this.pageQuery = pageQuery;
        this.edgeQuery = edgeQuery;
        this.browserInstance = options.browserInstance;
        this.headless = options.headless;
        this.logger = options.logger;
        this.silent = options.silent;
        this.strict = options.strict;
        this.enableGrafting = options.enableGrafting;
        this.sameBrowser = options.sameBrowser;
        this.sleepTime = options.sleepTime;
        this.hibernationTime = options.hibernationTime;
        this.fullAPI = options.fullAPI;
        this.proxyURL = options.proxyURL;
        this.executablePath = options.executablePath;
        this.validator = options.validator || validator;

        this.addPlugins(options["plugins"]);
        this.executePlugins("construction");

        // ANDYP - Login detection
        this.ipconfig = true;
        // this.creds = creds;
        this.user = options.user;
        this.pass = options.pass;
        this.endpoint = endpoint;
        this.screenshots = options.screenshots;
        this.screenshotPath = options.screenshotPath;
    }

    /**
     * Toggle pausing data collection
     */
    public pause() {
        this.paused = !this.paused;
    }

    /**
     * Toggle prolonged pausing
     */
    public toggleHibernation() {
        this.hibernate = true;
    }

    /**
     * Force the API to stop
     */
    public async forceStop(force?: boolean) {
        if (!force && !this.started) {
            return;
        }
        this.started = false;
        this.finish(FinishedReasons.FORCED_STOP);
        try {
            this.requestBufferLock.release();
            // tslint:disable-next-line: no-empty
        } catch (e) {}
        try {
            this.responseBufferLock.release();
            // tslint:disable-next-line: no-empty
        } catch (e) {}
        await this.stop();
    }

    /**
     * Generator of posts on page
     */
    public async *generator(): AsyncIterableIterator<PostType> {
        // Start if haven't done so already
        if (!this.started) {
            await this.start();
        }

        var index;

        // Handle the difference between a single ID (string)
        // and an Array of IDs.
        var a = [];
        a[0] = this.id; // Default to single ID and make it an array.
        if (Array.isArray(this.id)) {
            a = this.id; // If already an array, overwrite.
        }


        for (index = 0; index < a.length; ++index) {
            this.started = false;
            this.index = 0;
            this.id = a[index];
            this.url = this.endpoint.replace("[id]", a[index]);




            // ┌───────────────────────────────────────────────────┐
            // │                                                   │
            // │                  Goto first page                  │
            // │                                                   │
            // └───────────────────────────────────────────────────┘
            await this.gotoPage();
            await this.addListeners();

            while (true) {
                // Get more posts
                await this.getNext();
                // Yield posts from buffer
                let post = await this.postPop();
                while (post) {
                    yield post;
                    post = await this.postPop();
                }
                // End loop when finished, check for pagePromises if fullAPI
                if (this.finished && this.pagePromises.length === 0) {
                    break;
                }
            }

            this.logger.warn(Date() + ", ENDED, COMPLETE, Instamancer finished scrape." );
            this.logger.warn(Date() + ", -----, -----, -----" );

            // Close the profile page
            await this.page.close();
        }
        
        await this.stop();

        // Add newline to end of output
        if (!this.silent) {
            process.stdout.write("\n");
        }
    }





    /**
     * Construct page and add listeners
     */
    public async start() {
        let pageConstructed: boolean;
        this.pageUrlAttempts = 0;
        while (this.pageUrlAttempts++ < this.maxPageUrlAttempts) {
            pageConstructed = await this.constructPage();
            if (pageConstructed) {
                break;
            }
        }
        if (!pageConstructed) {
            await this.forceStop(true);
            throw new Error("Failed to visit URL");
        }

    }

    public async addListeners()
    {
        // Build page and visit url
        await this.executePlugins("browser");
        this.started = true;

        // Add event listeners for requests and responses
        await this.page.setRequestInterception(true);
        this.page.on("request", (req) => this.interceptRequest(req));
        this.page.on("response", (res) => this.interceptResponse(res));
        this.page.on("requestfailed", (res) => this.interceptFailure(res));
        this.page.on("console", (message) =>
            this.logger.info("Console log", {message}),
        );

        // Ignore dialog boxes
        this.page.on("dialog", (dialog) => dialog.dismiss());

        // Log errors
        /* istanbul ignore next */
        this.page.on("error", (error) =>
            this.logger.info("Console error", {error}),
        );

        // Gather initial posts from web page
        if (this.fullAPI) {
            await this.scrapeDefaultPosts();
        }
    }






    /**
     * Match the url to the url used in API requests
     */
    public matchURL(url: string) {
        return url.startsWith(this.catchURL) && !url.includes("include_reel");
    }






    /**
     * Close the page and browser
     */
    protected async stop() {
        await this.progress(Progress.CLOSING);

        // Remove listeners
        if (!this.page.isClosed()) {
            this.page.removeAllListeners("request");
            this.page.removeAllListeners("response");
            this.page.removeAllListeners("requestfailed");
        }

        // Clear request buffers
        await this.requestBufferLock.acquireAsync();
        this.requestBuffer = [];
        this.requestBufferLock.release();

        // Clear response buffers
        await this.responseBufferLock.acquireAsync();
        this.responseBuffer = [];
        this.responseBufferLock.release();

        // Wait for pagePromises to empty
        while (true) {
            if (this.pagePromises.length === 0) {
                break;
            } else {
                /* istanbul ignore next */
                await this.sleep(1);
            }
        }

        // Close page
        if (!this.page.isClosed()) {
            await this.page.close();
        }

        if (!this.browserDisconnected && !this.browserInstance) {
            await this.browser.close();
        }
    }






    /**
     * Finish retrieving data for the generator
     */
    protected finish(reason: FinishedReasons) {
        this.finished = true;
        this.finishedReason = reason;
        this.logger.info("Finished collecting", {reason});
    }






    /**
     * Process the requests in the request buffer
     */
    protected async processRequests() {
        await this.requestBufferLock.acquireAsync();

        let newApiRequest = false;
        for (const req of this.requestBuffer) {
            // Match url
            if (!this.matchURL(req.url())) {
                continue;
            } else {
                newApiRequest = true;
            }

            // Begin grafting if required, else continue the request
            if (this.graft) {
                if (this.foundGraft === false) {
                    // Gather details
                    this.graftURL = req.url();
                    this.graftHeaders = req.headers();
                    this.foundGraft = true;

                    // Cancel request
                    await req.abort();
                } else {
                    // Swap request
                    const overrides = {
                        headers: this.graftHeaders,
                        url: this.graftURL,
                    };
                    await this.executePlugins("request", req, overrides);
                    await req.continue(overrides);

                    // Reset grafting data
                    this.graft = false;
                    this.foundGraft = false;
                    this.graftURL = null;
                    this.graftHeaders = null;
                }

                // Stop reading requests
                break;
            } else {
                const overrides = {};
                this.executePlugins("request", req, overrides);
                await req.continue(overrides);
            }
        }

        // Clear buffer and release
        this.requestBuffer = [];
        this.requestBufferLock.release();

        if (this.foundGraft && newApiRequest) {
            // Restart browser and page, clearing all buffers
            await this.stop();
            await this.start();
        }
    }







    /**
     * Process the responses in the response buffer
     */
    protected async processResponses() {
        await this.responseBufferLock.acquireAsync();

        for (const res of this.responseBuffer) {
            // Match url
            if (!this.matchURL(res.url())) {
                continue;
            }

            // Acknowledge receipt of response
            this.responseFromAPI = true;

            // Get JSON data
            let data: unknown;
            try {
                data = await res.json();
                if (typeof data !== "object") {
                    this.logger.info("Response data is not an object", {data});
                    continue;
                }
            } catch (error) {
                this.logger.info("Error processing response JSON", {
                    data,
                    error,
                });
                continue;
            }

            // Emit event
            this.executePlugins("response", res, data);

            // Check for rate limiting
            if (data && "status" in data && data["status"] === "fail") {
                this.logger.info("Rate limited");
                this.hibernate = true;
                continue;
            }

            // Check for next page
            if (
                !(
                    _.get(data, this.pageQuery + ".has_next_page", false) &&
                    _.get(data, this.pageQuery + ".end_cursor", false)
                )
            ) {
                this.logger.info("No posts remaining", {data});
                this.finish(FinishedReasons.API_FINISHED);
            }

            await this.processResponseData(data);
        }

        // Clear buffer and release
        this.responseBuffer = [];
        this.responseBufferLock.release();
    }





    protected async processResponseData(data: unknown) {
        // Get posts
        const posts = _.get(data, this.edgeQuery, []);
        for (const post of posts) {
            const postId = post["node"]["id"];

            // Check it hasn't already been cached
            const contains = this.postIds.add(postId);
            if (contains) {
                this.logger.info("Duplicate id found", {postId});
                continue;
            }

            // Add to postBuffer
            if (this.index < this.total || this.total === 0) {
                this.index++;
                if (this.fullAPI) {
                    this.pagePromises.push(
                        this.postPage(
                            post["node"]["shortcode"],
                            this.postPageRetries,
                        ),
                    );
                } else {
                    await this.addToPostBuffer(post);
                }
            } else {
                this.finish(FinishedReasons.TOTAL_REACHED_API);
                break;
            }
        }
    }





    /**
     * Open a post in a new page, then extract its metadata
     */
    protected async postPage(post: string, retries: number) {
        // Create page
        const postPage = await this.browser.newPage();
        await postPage.setRequestInterception(true);
        postPage.on("request", async (req) => {
            if (!req.url().includes("/p/" + post)) {
                await req.abort();
            } else {
                await req.continue();
            }
        });
        postPage.on("requestfailed", async (req) => this.interceptFailure(req));

        // Visit post and read state
        let parsed;


        // ┌───────────────────────────────────────────────────┐
        // │                                                   │
        // │                     Goto Post                     │
        // │                                                   │
        // └───────────────────────────────────────────────────┘

        try {
            
            // Visit post page
            await postPage.goto(this.postURL + post + "/");


            // log
            this.logger.warn( Date() + ", VISIT, URL, visiting page loaded : " + postPage.url());


            // screenshot
            if (this.screenshots){
                await this.page.screenshot({path: this.screenshotPath + '/06_Post_' + post + '.png'});
                this.logger.warn( Date() + ', IMAGE, POSTCAPTURED, ' + this.screenshotPath + '/06_Post_' + post + '.png' );
            }

            // log
            this.logger.error(Date() + ", PASS, SCRAPE, Captured Post Page: " + this.postURL + post + "/" );

        } catch (error) {

            // log
            this.logger.error(Date() + ", FAIL, SCRAPE, Could not navigate to Post Page: " + this.postURL + post + "/" );

            await this.handlePostPageError(
                postPage,
                error,
                "Couldn't navigate to page",
                post,
                retries,
            );
            return;
        }

        // Load data from memory
        let data;
        try {
            /* istanbul ignore next */
            data = await postPage.evaluate(async () => {
                // Wait for _sharedData value to be set
                await new Promise((resolve) => {
                    let i = 0;
                    const findSharedData = setInterval(() => {
                        if (window["_sharedData"] !== undefined || i++ > 5) {
                            resolve();
                            clearInterval(findSharedData);
                        }
                    }, 2000);
                });

                return JSON.stringify(
                    window["_sharedData"].entry_data.PostPage[0].graphql,
                );
            });
        } catch (error) /* istanbul ignore next */ {
            await this.handlePostPageError(
                postPage,
                error,
                "Couldn't evaluate on page",
                post,
                retries,
            );
            return;
        }

        // ┌─────────────────────────────────────────────────────────────────────────┐ 
        // │                                                                         │░
        // │                                                                         │░
        // │                    CHECK IF LOGIN PAGE WAS USED                         │░
        // │                                                                         │░
        // │                                                                         │░
        // └─────────────────────────────────────────────────────────────────────────┘░
        //  ░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░

        if (data === undefined){
            try {
                /* istanbul ignore next */
                data = await postPage.evaluate(async () => {

                    await new Promise((resolve) => {
                        let i = 0;
                        const findSharedData = setInterval(() => {
                            if (window["__additionalData"] !== undefined || i++ > 5) {
                                resolve();
                                clearInterval(findSharedData);
                            }
                        }, 2000);
                    });
                    
                    return window["__additionalData"];                
    
                });
            }
            catch (error) /* istanbul ignore next */ {
                await this.handlePostPageError(postPage, error, "Couldn't evaluate on page", post, retries);
                return;
            }

            var page = "/p/" + post + "/";
            var graphql = data[page]["data"]["graphql"];
            data = JSON.stringify(graphql);
        }


        // Close page
        await postPage.close();

        // Parse data to PostType
        try {
            parsed = JSON.parse(data) as PostType;
        } catch (error) /* istanbul ignore next */ {
            await this.handlePostPageError(
                postPage,
                error,
                "Couldn't parse page data",
                post,
                retries,
            );
            return;
        }

        await this.executePlugins("postPage", parsed);
        await this.addToPostBuffer(parsed);
    }




    private async handlePostPageError(
        page: Page,
        error: Error,
        message: string,
        post: string,
        retries: number,
    ) {
        // Log error and wait
        this.logger.info(message, {error});
        await this.progress(Progress.ABORTED);
        await this.sleep(2);

        // Close existing attempt
        if (!page.isClosed()) {
            await page.close();
        }

        // Retry
        if (retries > 0) {
            await this.postPage(post, --retries);
        }
    }

    protected async validatePost(post: PostType) {
        const validationResult = this.validator.decode(post);
        if (this.strict) {
            ThrowReporter.report(validationResult);
            return;
        }
        if (isLeft(validationResult)) {
            const validationReporter = PathReporter.report(validationResult);
            this.logger.info(
                `
        Warning! The Instagram API has been changed since this version of instamancer was released.
        More info: https://scriptsmith.github.io/instamancer/api-change
        `,
                {validationReporter, post},
            );
        }
    }





    /**
     * Stimulate the page until responses gathered
     */
    protected async getNext() {
        await this.progress(Progress.SCRAPING);
        while (true) {
            // Process results (if any)
            await this.processRequests();
            await this.processResponses();

            // Finish page promises
            if (this.pagePromises.length > 0) {
                await this.progress(Progress.BRANCHING);
                await Promise.all(this.pagePromises);
                this.pagePromises = [];
            }

            // Check if finished
            if (this.finished) {
                break;
            }

            // Pause if paused
            await this.waitResume();

            // Interact with page to stimulate request
            await this.jump();

            // Stop if no data is being gathered
            if (this.jumps === this.failedJumps) {
                if (this.fullAPI) {
                    if (!this.responseFromAPI) {
                        this.finish(FinishedReasons.NO_RESPONSE);
                    }
                } else if (this.index === 0) {
                    this.finish(FinishedReasons.NO_INCREMENT);

                    const pageContent = {content: ""};
                    try {
                        pageContent.content = await this.page.content();
                    } catch (e) {
                        // No content
                    }

                    this.logger.info(
                        "Page failed to make requests",
                        pageContent,
                    );
                    break;
                }
            }

            // Enable grafting if required
            if (this.jumps % this.jumpMod === 0) {
                await this.initiateGraft();
            }

            // Sleep
            await this.sleep(this.sleepTime);

            // Hibernate if rate-limited
            if (this.hibernate) {
                await this.sleep(this.hibernationTime);
                this.hibernate = false;
            }

            // Break if posts in buffer
            await this.postBufferLock.acquireAsync();
            const posts = this.postBuffer.length;
            this.postBufferLock.release();
            if (posts > 0) {
                break;
            }
        }
    }





    /**
     * Halt execution
     * @param time Seconds
     */
    protected async sleep(time: number) {
        for (let i = time; i > 0; i--) {
            this.sleepRemaining = i;
            await this.progress(Progress.SCRAPING);

            await new Promise((resolve) => {
                setTimeout(resolve, i >= 1 ? 1000 : i * 1000);
            });
        }
        this.sleepRemaining = 0;
        await this.progress(Progress.SCRAPING);
    }






    /**
     * Create the browser and page, then visit the url
     */
    private async constructPage(): Promise<boolean> {
        // Browser args
        const args = [];
        /* istanbul ignore if */
        if (process.env.NO_SANDBOX) {
            args.push("--no-sandbox");
            args.push("--disable-setuid-sandbox");
        }
        if (this.proxyURL !== undefined) {
            args.push("--proxy-server=" + this.proxyURL);
        }

        // Browser launch options
        const options: LaunchOptions = {
            args,
            headless: this.headless,
        };
        if (this.executablePath !== undefined) {
            options.executablePath = this.executablePath;
        }

        // already got one.
        if (this.browser) {

        }
        // Launch browser
        else if (this.browserInstance) {
            await this.progress(Progress.LAUNCHING);
            this.browser = this.browserInstance;
            this.browserDisconnected = !this.browser.isConnected();
            this.browser.on(
                "disconnected",
                () => (this.browserDisconnected = true),
            );
        } else if (!this.sameBrowser || (this.sameBrowser && !this.started)) {
            await this.progress(Progress.LAUNCHING);
            this.browser = await launch(options);
            this.browserDisconnected = false;
            this.browser.on(
                "disconnected",
                () => (this.browserDisconnected = true),
            );
        }

        return true;
    }


    // ┌─────────────────────────────────────────────────────────────────────────┐ 
    // │                                                                         │░
    // │                                                                         │░
    // │                           MAIN PROCESSING                               │░
    // │                                                                         │░
    // │                                                                         │░
    // └─────────────────────────────────────────────────────────────────────────┘░
    //  ░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░

    public async gotoPage()
    {

        this.logger.warn( Date() + ", START, TRUE, Running Instamancer.");

        // ┌───────────────────────────────────────────────────┐
        // │                                                   │
        // │      Open new page and wait for it to finish      │
        // │                                                   │
        // └───────────────────────────────────────────────────┘

        this.page = await this.browser.newPage();
        await this.progress(Progress.OPENING);

        

        // ┌───────────────────────────────────────────────────┐
        // │                                                   │
        // │             Check IP / Browser Agent              │
        // │                                                   │
        // └───────────────────────────────────────────────────┘

        if (this.screenshots && this.ipconfig){
            
            await this.page.goto('http://atomurl.net/myip/');
            await this.page.screenshot({path: this.screenshotPath + '/00_IPConfig.png'});
            this.logger.warn( Date() + ", VISIT, URL, visiting page : http://atomurl.net/myip/");
            this.logger.warn( Date() + ", IMAGE, IPCONFIG, " + this.screenshotPath + "/00_IPConfig.png");
            this.ipconfig = false;
        }

        try {

            // ┌───────────────────────────────────────────────────┐
            // │                                                   │
            // │                 Try going to page                 │
            // │                                                   │
            // └───────────────────────────────────────────────────┘

            const response = await this.page.goto(this.url, {waitUntil: 'domcontentloaded'});

            
            this.logger.error(Date() + ", PAGE, RESPONSE CODE, " + response.status());


            // ┌───────────────────────────────────────────────────┐
            // │                                                   │
            // │                 Rate Limit Check                  │
            // │                                                   │
            // └───────────────────────────────────────────────────┘

            if ( response.status() !== 200)
            {
                this.logger.error(Date() + ", RATE, LIMITED - STOPPING, " + response.status());
                await this.handleConstructionError(
                    "RATE LIMITED",
                    10,
                );
                return false;
            }


            // Screenshot
            if (this.screenshots){
                await this.page.screenshot({path: this.screenshotPath + '/00_afterInitialPageLoaded.png'});
                this.logger.warn(Date() + ", IMAGE, INITIALPAGE, " + this.screenshotPath + "/00_afterInitialPageLoaded.png" );
            }

            


            // ┌───────────────────────────────────────────────────┐
            // │                                                   │
            // │                  PROXY Settings                   │
            // │                                                   │
            // └───────────────────────────────────────────────────┘

            if (this.proxyURL) {
                this.logger.warn(Date() + ", PROXY, TRUE, " + this.proxyURL);
            }


            // log
            this.logger.warn( Date() + ", VISIT, URL, visited page loaded : " + this.page.url());




            // ┌───────────────────────────────────────────────────┐
            // │                                                   │
            // │            Accept Cookies Popup Modal             │
            // │                                                   │
            // └───────────────────────────────────────────────────┘

            this.logger.warn(Date() + ", WAITS, TRUE, Waiting for Cookie Popup. 100ms" );

            // Screenshot
            if (this.screenshots){
                await this.page.screenshot({path: this.screenshotPath + '/01_BeforeLookForCookiePopup.png'});
            }

            try {

                // Wait 100ms to look for the Cookie Popup
                await this.page.waitForSelector('div[role=dialog] button:first-of-type', { timeout: 3000 });

                // Screenshot
                if (this.screenshots){
                    await this.page.screenshot({path: this.screenshotPath + '/01_beforeClickLookingForCookies.png'});
                    this.logger.warn(Date() + ", IMAGE, COOKIEACCEPT, " + this.screenshotPath + "/01_beforeClickLookingForCookies.png" );
                }

                // Click 'accept'.
                await this.page.click('div[role=dialog] button:first-of-type');

                // log
                this.logger.warn(Date() + ", POPUP, TRUE, Cookie Popup found - attempting to press accept button." );


                // Screenshot
                if (this.screenshots){
                    await this.page.screenshot({path: this.screenshotPath + '/01_afterClickLookingForCookies.png'});
                    this.logger.warn(Date() + ", IMAGE, COOKIEACCEPT, " + this.screenshotPath + "/01_afterClickLookingForCookies.png" );
                }


            } catch (error) {
                this.logger.warn(Date() + ", POPUP, FALSE, No Cookie Popup found." );
            }



            // ┌───────────────────────────────────────────────────┐
            // │                                                   │
            // │               Check for Login Page                │
            // │                                                   │
            // └───────────────────────────────────────────────────┘

            this.logger.warn(Date() + ", WAITS, TRUE, Waiting for Login Page. 100ms" );

            // Screenshot
            if (this.screenshots){
                await this.page.screenshot({path: this.screenshotPath + '/02_BeforeLookForLogin.png'});
            }

            try {

                // Look for Login Page
                await this.page.waitForSelector('input[name="username"]', { timeout: 3000 });

                await this.page.waitFor(3000);

                
                // Screenshot
                if (this.screenshots){
                    await this.page.screenshot({path: this.screenshotPath + '/02_beforeLogin.png'});
                    this.logger.warn(Date() + ", IMAGE, LOGIN, " + this.screenshotPath + "/02_beforeLogin.png" );
                }



                // Log
                this.logger.warn(Date() + ", LOGIN, TRUE, Login Page found - attempting to use credentials." );


                // Check for supplied username
                if (this.user == '')
                {
                    this.logger.error(Date() + ", FAIL, USERNAME, No Username Supplied. Exiting" );
                    return false;
                }


                // Check for supplied password
                if (this.pass == '')
                {
                    this.logger.error(Date() + ", FAIL, PASSWORD, No Password Supplied. Exiting" );
                    return false;
                }


                // Insert username and password
                await this.page.type('input[name="username"]', this.user);
                await this.page.type('input[name="password"]', this.pass);


                // Click the submit button
                await this.page.waitFor(100);
                await this.page.click('button[type="submit"]');


                // log
                this.logger.warn(Date() + ", LOGIN, TRUE, Login details entered and submitted." );


                // Screenshot
                if (this.screenshots){
                    await this.page.screenshot({path: this.screenshotPath + '/02_afterLogin.png'});
                    this.logger.warn(Date() + ", IMAGE, LOGIN, " + this.screenshotPath + "/02_afterLogin.png" );
                }



                // Pause for 3 seconds to allow the login to process.
                // Otherwise the "Save Details" button will not be 
                // available yet.
                await this.page.waitFor(3000);

            

                // ┌───────────────────────────────────────────────────┐
                // │                                                   │
                // │               'Save details' Button               │
                // │                                                   │
                // └───────────────────────────────────────────────────┘

                this.logger.warn(Date() + ", WAITS, TRUE, Waiting for Save Details Button. 100ms" );

                // Screenshot
                if (this.screenshots){
                    await this.page.screenshot({path: this.screenshotPath + '/03_BeforeSaveDetails.png'});
                }

                try {

                    // Look for button
                    await this.page.waitForSelector('button[type="button"]', { timeout: 3000 });

                    // Screenshot
                    if (this.screenshots){
                        await this.page.screenshot({path: this.screenshotPath + '/03_BeforeClickSaveDetails.png'});
                        this.logger.warn(Date() + ", IMAGE, SAVEDETAILS, " + this.screenshotPath + "/03_BeforeClickSaveDetails.png" );
                    }


                    // Click it
                    await this.page.click('button[type="button"]');


                    // wait 500ms
                    await this.page.waitFor(500);


                    // log
                    this.logger.warn(Date() + ", SAVED, TRUE , 'Save details' button found and clicked." );

                    // Screenshot
                    if (this.screenshots){
                        await this.page.screenshot({path: this.screenshotPath + '/03_AfterClickSaveDetails.png'});
                        this.logger.warn(Date() + ", IMAGE, SAVEDETAILS, " + this.screenshotPath + "/03_AfterClickSaveDetails.png" );
                    }

                
                } catch (error) {
                    this.logger.warn(Date() + ", SAVED, FALSE, No 'Save details' button found." );
                }



                // Pause for 3 seconds to allow the "save details" to process.
                // Otherwise the page will timeout.
                await this.page.waitFor(3000);


                // ┌───────────────────────────────────────────────────┐
                // │                                                   │
                // │    Goto original URL Request, now login done.     │
                // │                                                   │
                // └───────────────────────────────────────────────────┘

                this.logger.warn(Date() + ", WAITS, TRUE, Waiting to goto URL page now login done." );

                // Screenshot
                if (this.screenshots){
                    await this.page.screenshot({path: this.screenshotPath + '/04_BeforeGotoFirstPage.png'});
                }

                try {

                    // Visit page
                    await this.page.goto(this.url, {waitUntil: 'domcontentloaded'});


                    // Log expected / actual pages
                    this.logger.warn( Date() + ", VISIT, URL, visited page loaded : "+this.page.url());

                    

                    // Screenshot
                    if (this.screenshots){
                        // Pause for 3 seconds before screenshot
                        await this.page.waitFor(3000);
                        await this.page.screenshot({path: this.screenshotPath + '/04_GotoFirstPage.png'});
                        this.logger.warn(Date() + ", IMAGE, FIRSTPAGE, " + this.screenshotPath + "/04_GotoFirstPage.png" );
                    }

                } catch (error) {

                    this.logger.error(Date() + ", FAIL, NAVIGATE, After a login; Could not navigate to page : " + this.url );

                }



            // ┌───────────────────────────────────────────────────┐
            // │                                                   │
            // │               No Login Found. Good!               │
            // │                                                   │
            // └───────────────────────────────────────────────────┘ 
            
            } catch (error) {


                // log
                this.logger.warn(Date() + ", LOGIN, FALSE, Login Page not found - Continuing to page." );


                // Screenshot
                if (this.screenshots){
                    await this.page.screenshot({path: this.screenshotPath + '/05_noLoginScreenFound.png'});
                    this.logger.warn(Date() + ", IMAGE, NOLOGIN, " + this.screenshotPath + "/05_noLoginScreenFound.png" );
                }

            }




            // Check page loads
            /* istanbul ignore next */
            const pageLoaded = await this.page.evaluate(() => {
                const headings = document.querySelectorAll("h2");
                for (const heading of Array.from(headings)) {
                    if (
                        heading.innerHTML ===
                        "Sorry, this page isn't available."
                    ) {
                        return false;
                    }
                }
                return true;
            });
            if (!pageLoaded) {
                await this.handleConstructionError(
                    "Page loaded with no content",
                    10,
                );
                return false;
            }

            // Run defaultPagePlugins
            for (const f of this.defaultPageFunctions) {
                await this.page.evaluate(f);
            }

            // Fix issue with disabled scrolling
            /* istanbul ignore next */
            await this.page.evaluate(() => {
                setInterval(() => {
                    try {
                        document.body.style.overflow = "";
                    } catch (error) {
                        this.logger.info("Failed to update style", {error});
                    }
                }, 10000);
            });


        } catch (e) {

            this.logger.error(Date() + ", FAIL, NAVIGATE, Could not navigate to page : " + this.url );

            await this.handleConstructionError(e, 60);
            return false;
        }
        return true;
    }







    /***
     * Handle errors that occur during page construction
     */
    private async handleConstructionError(error: string, timeout: number) {
        // Log error and wait
        this.logger.info("Construction error", {error, url: this.url});
        await this.progress(Progress.ABORTED);
        await this.sleep(timeout);

        // Close existing attempt
        if (!this.page.isClosed()) {
            await this.page.close();
        }
        await this.browser.close();
    }







    /**
     * Pause and wait until resumed
     */
    private async waitResume() {
        // Pause for 200 milliseconds
        function f() {
            return new Promise((resolve) => {
                setTimeout(resolve, 200);
            });
        }

        // Pause until pause toggled
        while (this.paused === true) {
            await this.progress(Progress.PAUSED);
            await f();
        }
    }





    /**
     * Pop a post off the postBuffer (using locks). Returns null if no posts in buffer
     */
    private async postPop() {
        let post = null;
        await this.postBufferLock.acquireAsync();
        if (this.postBuffer.length > 0) {
            post = this.postBuffer.shift();
        }
        this.postBufferLock.release();
        return post;
    }






    /**
     * Print progress to stderr
     */
    private async progress(state: Progress) {
        // End if silent
        if (this.silent) {
            return;
        }

        // Lock
        await this.writeLock.acquireAsync();

        // Calculate total
        const total = this.total === 0 ? "Unlimited" : this.total;

        // Generate output string
        const idStr = chalk.bgYellow.black(` ${this.id} `);
        const totalStr = chalk.bgBlack(` Total: ${total} `);
        const stateStr = chalk.bgWhite.black(` State: ${state} `);
        const sleepStr = chalk.bgWhite.black(
            ` Sleeping: ${this.sleepRemaining} `,
        );
        const indexStr = chalk.bgWhite.black(` Scraped: ${this.index} `);

        this.logger.info({
            id: this.id,
            index: this.index,
            sleepRemaining: this.sleepRemaining,
            state,
            total,
        });

        // Print output
        process.stderr.write(
            `\r${idStr}${totalStr}${stateStr}${sleepStr}${indexStr}\u001B[K`,
        );

        // Release
        this.writeLock.release();
    }






    
    /**
     * Add request to the request buffer
     */
    private async interceptRequest(req: Request) {
        await this.requestBufferLock.acquireAsync();
        this.requestBuffer.push(req);
        await this.requestBufferLock.release();
    }

    /**
     * Add the response to the response buffer
     */
    private async interceptResponse(res: Response) {
        await this.responseBufferLock.acquireAsync();
        this.responseBuffer.push(res);
        await this.responseBufferLock.release();
    }

    /**
     * Log failed requests
     */
    private async interceptFailure(req: Request) {
        this.logger.info("Failed request", {url: req.url()});
        await this.progress(Progress.ABORTED);
    }

    /**
     * Add post to buffer
     */
    private async addToPostBuffer(post: PostType) {
        await this.postBufferLock.acquireAsync();
        await this.validatePost(post);
        this.postBuffer.push(post);
        this.postBufferLock.release();
    }

    /**
     * Manipulate the page to stimulate a request
     */
    private async jump() {
        await this.page.keyboard.press("PageUp");
        const jumpSize = this.graft ? 1 : this.jumpSize;
        for (let i = 0; i < jumpSize; i++) {
            await this.page.keyboard.press("End");
        }

        // Move mouse randomly
        const width = this.page.viewport()["width"];
        const height = this.page.viewport()["height"];
        await this.page.mouse.move(
            Math.round(width * Math.random()),
            Math.round(height * Math.random()),
        );

        ++this.jumps;
    }

    /**
     * Clear request and response buffers
     */
    private async initiateGraft() {
        // Check if enabled
        if (!this.enableGrafting) {
            return;
        }

        await this.progress(Progress.GRAFTING);

        this.executePlugins("grafting");

        // Enable grafting
        this.graft = true;
    }

    /**
     * Read the posts that are pre-loaded on the page
     */
    private async scrapeDefaultPosts() {
        // Get shortcodes from page
        /* istanbul ignore next */
        const shortCodes = await this.page.evaluate((url) => {
            return Array.from(document.links)
                .filter((link) => {
                    return (
                        link.href.startsWith(url) &&
                        link.href.split("/").length >= 2
                    );
                })
                .map((link) => {
                    const linkSplit = link.href.split("/");
                    return linkSplit[linkSplit.length - 2];
                });
        }, this.defaultPostURL);

        // Add postPage promises
        for (const shortCode of shortCodes) {
            if (this.index < this.total || this.total === 0) {
                this.index++;
                this.pagePromises.push(
                    this.postPage(shortCode, this.postPageRetries),
                );
            } else {
                this.finish(FinishedReasons.TOTAL_REACHED_PAGE);
                break;
            }
        }
    }

    private addPlugins(plugins: IPlugin<PostType>[]) {
        if (!plugins) {
            return;
        }

        for (const plugin of plugins) {
            for (const event of Object.keys(this.pluginFunctions)) {
                const pluginEvent = plugin[event + "Event"];
                if (pluginEvent) {
                    const context: IPluginContext<typeof plugin, PostType> = {
                        plugin,
                        state: this,
                    };

                    this.pluginFunctions[event].push(pluginEvent.bind(context));
                }
            }
        }
    }

    private executePlugins(event: SyncPluginEventsType, ...args): void;
    private executePlugins(
        event: AsyncPluginEventsType,
        ...args
    ): Promise<unknown>;
    private executePlugins(event: PluginEventsType, ...args) {
        if (event in SyncPluginEvents) {
            for (const pluginFunction of this.pluginFunctions["construction"]) {
                pluginFunction();
            }
            return;
        }

        return Promise.all(
            // @ts-ignore
            this.pluginFunctions[event].map((cb) => cb(...args)),
        );
    }
}

/**
 * The states of progress that the API can be in. Used to output status.
 */
enum Progress {
    LAUNCHING = "Launching",
    OPENING = "Navigating",
    SCRAPING = "Scraping",
    BRANCHING = "Branching",
    GRAFTING = "Grafting",
    CLOSING = "Closing",

    PAUSED = "Paused",
    ABORTED = "Request aborted",
}

/**
 * Reasons why the collection finished
 */
enum FinishedReasons {
    // forceStop used
    FORCED_STOP,

    // API response doesn't contain next page
    API_FINISHED,

    // Total posts required have been collected from the API
    TOTAL_REACHED_API,

    // Total posts required have been collected from the default posts
    TOTAL_REACHED_PAGE,

    // No API response intercepted after interacting with page
    NO_RESPONSE,

    // Index hasn't increased after interacting with page
    NO_INCREMENT,
}
