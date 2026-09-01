# 67 Columns Data 

`/docs` contains the code for the diffs website which is published at
<https://zona-motel.github.io/barkan-up-the-wrong-tree/>. diffs.js is the diffs data for the site in json format. Matches the markdown output from the scripts. 

`/scripts` contains two scripts.

### nymag_wayback_diff_barkan.py

This script crawls Ross Barkan's nymag author archive, finds the articles that have the August 14, 2026 correction notice, and for each one, fetches both the live page and the earliest usable Wayback capture from before the correction, then writes a markdown diff of the two.

To run:

```bash
python -m pip install requests beautifulsoup4 lxml readability-lxml
python nymag_wayback_diff_barkan.py --out nymag_wayback_diff_output
```

Everything goes to the folder after `--out` (default `nymag_wayback_diff_output/`):

```
diffs/                  67 .md files, one per article — the site's source data
raw_html/live/          the live page fetched for each article
raw_html/wayback/       the archived capture fetched for each article
results.jsonl           one record per article per pass
summary.csv             per-article outcome
failures.csv            articles that did not resolve
corpus.json             the discovered 67 and their URLs
run_log.json            per-request log
*_diffs.zip             the three directories above, zipped
*_live_html.zip
*_wayback_html.zip
```

If the script is interrupted it can be resumed. It retries the Wayback machine to fill gaps, in repeated passes, until all 67 articles validate, or you stop it with Ctrl-C. `--archive-cutoff` sets the snapshot timing boundary. Defaults to `20260813235959`, the just before the correction date.

### npr_first50_to_zip.py

This script saves the first 50 articles from Bobby Allyn's NPR author page as rendered HTML. It runs by using an automated Chrome browser via Selenium. 

```bash
python -m pip install selenium
python npr_first50_to_zip.py
```

```
bobby_allyn_first50_html/       the saved pages, plus manifest.txt and source_urls.txt
bobby_allyn_first50_html.zip
```

