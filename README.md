<p align="center">
<img src="assets/logo.png" height="150" title="Icon made by Freepik (www.freepik.com) available at www.flaticon.com. CC 3.0 BY licensed (http://creativecommons.org/licenses/by/3.0/)">
</p>

<h1 align="center">Instamancer+</h1>

[![Build Status](https://img.shields.io/gitlab/pipeline/scriptsmith/instamancer)](https://gitlab.com/ScriptSmith/instamancer/pipelines)
[![Quality](https://img.shields.io/codacy/grade/98066a13fa444845aa3902d180581b86.svg)](https://app.codacy.com/project/ScriptSmith/instamancer/dashboard)
[![Coverage](https://img.shields.io/codacy/coverage/98066a13fa444845aa3902d180581b86.svg)](https://app.codacy.com/project/ScriptSmith/instamancer/dashboard)
[![Speed](https://firebasestorage.googleapis.com/v0/b/instagram-speed-test.appspot.com/o/instamancer.svg?alt=media&token=dcc3e623-ee88-4d74-ae86-2d969a1cd8ad)](https://scriptsmith.github.io/instagram-speed-test)
[![NPM](https://img.shields.io/npm/v/instamancer.svg)](https://www.npmjs.com/package/instamancer)
[![Dependencies](https://david-dm.org/scriptsmith/instamancer/status.svg)](https://david-dm.org/scriptsmith/instamancer)
[![Chat](https://img.shields.io/gitter/room/instamancer/instamancer.svg)](https://gitter.im/instamancer)

Scrape Instagram's API with Puppeteer. Now with login detection.

###### [Install](#Install) | [Usage](#Usage) | [Comparison](#Comparison) | [Website](https://scriptsmith.github.io/instamancer/) | [FAQ](FAQ.md) | [Examples](examples/README.md)


Instamancer is a new type of scraping tool that leverages Puppeteer's ability to intercept requests made by a webpage to an API.

Read more about how Instamancer works [here](https://scriptsmith.github.io/instamancer/).

### Features+
- Login detection
- Single browser instance option.
- Scrape multiple users.

### Features
- Scrape hashtags, users' posts, and individual posts
- Download images, albums, and videos
- Output JSON, CSV
- Batch scraping
- Search hashtags, users, and locations
- API response validation
- Upload files to [S3](https://github.com/ScriptSmith/instamancer/blob/master/FAQ.md#how-do-i-use-the---bucket-flag-and-s3) and [depot](https://github.com/ScriptSmith/instamancer/blob/master/FAQ.md#how-do-i-use-the---depot-flag-and-depot)
- [Plugins](plugins)

### Data
Metadata that Instamancer is able to gather from posts:

- Text
- Timestamps
- Tagged users
- Accessibility captions
- Like counts
- Comment counts
- Images (Thumbnails, Dimensions, URLs)
- Videos (URL, View count, Duration)
- Comments (Timestamp, Text, Like count, User)
- User (Username, Full name, Profile picture, Profile privacy)
- Location (Name, Street, Zip code, City, Region, Country)
- Sponsored status
- Gating information
- Fact checking information

## Install

#### Linux
Enable user namespace cloning:
```
sysctl -w kernel.unprivileged_userns_clone=1
```

Or run without a sandbox:

```
# WARNING: unsafe
export NO_SANDBOX=true
```

See [Puppeteer troubleshooting](https://github.com/GoogleChrome/puppeteer/blob/master/docs/troubleshooting.md#chrome-headless-fails-due-to-sandbox-issues)

#### Without downloading chromium
If you wish to install Instamancer without downloading chromium, enable the `PUPPETEER_SKIP_CHROMIUM_DOWNLOAD` environment variable before installation

```
export PUPPETEER_SKIP_CHROMIUM_DOWNLOAD=true
```

### From NPM

```
npm install -g instamancer
```

If you're using root to install globally, use the following command to install the Puppeteer dependency

```
sudo npm install -g instamancer --unsafe-perm=true
```

### From NPX

```
npx instamancer
```

### From this repository
```
git clone https://github.com/ScriptSmith/instamancer.git
cd instamancer
npm install
npm run build
npm install -g
```

### /src/api/creds.json

If a login screen is detected, then use the creds.json file to login as that user and carry on.
Copy the `creds_demo.json` to `creds.json` and enter real details to be used.

## Usage

### Command Line
```
$ instamancer
Usage: instamancer <command> [options]

Commands:
  instamancer hashtag [id]       Scrape a hashtag
  instamancer user [id]          Scrape a users posts
  instamancer users [ids]        Scrape a comma-separated list of users posts
  instamancer post [ids]         Scrape a comma-separated list of posts
  instamancer search [query]     Perform a search of users, tags and places
  instamancer batch [batchfile]  Read newline-separated arguments from a file

Configuration
  --count, -c    Number of posts to download (0 for all)   [number] [default: 0]
  --full, -f     Retrieve full post data              [boolean] [default: false]
  --sleep, -s    Seconds to sleep between interactions     [number] [default: 2]
  --graft, -g    Enable grafting                       [boolean] [default: true]
  --browser, -b  Browser path. Defaults to the puppeteer version        [string]
  --sameBrowser  Use a single browser when grafting   [boolean] [default: false]

Download
  --download, -d      Save images from posts          [boolean] [default: false]
  --downdir           Download path       [default: "downloads/[endpoint]/[id]"]
  --video, -v         Download videos (requires full) [boolean] [default: false]
  --sync              Force download between requests [boolean] [default: false]
  --threads, -k       Parallel download / depot threads    [number] [default: 4]
  --waitDownload, -w  Download media after scraping   [boolean] [default: false]

Upload
  --bucket  Upload files to an AWS S3 bucket                            [string]
  --depot   Upload files to a URL with a PUT request (depot)            [string]

Output
  --file, -o       Output filename. '-' for stdout    [string] [default: "[id]"]
  --type, -t       Filetype   [choices: "csv", "json", "both"] [default: "json"]
  --mediaPath, -m  Add filepaths to _mediaPath        [boolean] [default: false]

Display
  --visible    Show browser on the screen             [boolean] [default: false]
  --quiet, -q  Disable progress output                [boolean] [default: false]

Logging
  --logging, -l    [choices: "none", "error", "info", "debug"] [default: "none"]
  --logfile      Log file name             [string] [default: "instamancer.log"]

Validation
  --strict  Throw an error on response type mismatch  [boolean] [default: false]

Plugins
  --plugin, -p  Use a plugin from the plugins directory    [array] [default: []]

Options:
  --help     Show help                                                 [boolean]
  --version  Show version number                                       [boolean]

Examples:
  instamancer hashtag instagood -fvd        Download all the available posts,
                                            and their media from #instagood
  instamancer user arianagrande --type=csv  Download Ariana Grande's posts to a
  --logging=info --visible                  CSV file with a non-headless
                                            browser, and log all events
  instamancer users arianagrande,therock    Download Ariana Grande's and the
  -c 3                                      Rock's latest three posts.
Source code available at https://github.com/IORoot/instamancer

```

### Module

ES2018 Typescript example:
```typescript
import {createApi, IOptions} from "instamancer"

const options: IOptions = {
    total: 10
};
const hashtag = createApi("hashtag", "beach", options);

(async () => {
    for await (const post of hashtag.generator()) {
        console.log(post);
    }
})();
```

#### Generator functions

```typescript
import {createApi} from "instamancer"

createApi("hashtag", id, options);
createApi("user", id, options);
createApi("users", ids, options);
createApi("post", ids, options);
createApi("search", query, options);
```

#### Options
```typescript
const options: Instamancer.IOptions = {
    // Total posts to download. 0 for unlimited
    total: number,

    // Run Chrome in headless mode
    headless: boolean,

    // Logging events
    logger: winston.Logger,

    // Run without output to stdout
    silent: boolean,

    // Time to sleep between interactions with the page
    sleepTime: number,

    // Throw an error if type validation has been failed
    strict: boolean,

    // Time to sleep when rate-limited
    hibernationTime: number,

    // Enable the grafting process
    enableGrafting: boolean,

    // Extract the full amount of information from the API
    fullAPI: boolean,

    // Use a proxy in Chrome to connect to Instagram
    proxyURL: string,

    // Location of the chromium / chrome binary executable
    executablePath: string,

    // Custom io-ts validator
    validator: Type<unknown>,

    // Custom plugins
    plugins: IPlugin[]
}
```
