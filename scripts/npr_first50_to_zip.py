#!/usr/bin/env python3
"""
npr_first50_to_zip.py

Opens Bobby Allyn's NPR author page, collects the FIRST 50 article URLs
in page order, saves each rendered article as HTML, and creates a ZIP.

Install:
    pip install selenium

Run:
    python npr_first50_to_zip.py

Output:
    bobby_allyn_first50_html/
    bobby_allyn_first50_html.zip
"""

from pathlib import Path
import shutil
import time
import zipfile

from selenium import webdriver
from selenium.common.exceptions import StaleElementReferenceException, TimeoutException
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.common.by import By
from selenium.webdriver.support.ui import WebDriverWait


AUTHOR_URL = "https://www.npr.org/people/638550790/bobby-allyn"
LIMIT = 50
PAGE_TIMEOUT = 60
WAIT_AFTER_CLICK = 20

OUTPUT_DIR = Path("bobby_allyn_first50_html")
ZIP_FILE = Path("bobby_allyn_first50_html.zip")


def log(message=""):
    print(message, flush=True)


def make_driver():
    options = Options()
    options.add_argument("--headless=new")
    options.add_argument("--window-size=1920,1200")
    options.add_argument("--disable-gpu")
    options.add_argument("--no-sandbox")
    options.add_argument("--disable-dev-shm-usage")
    options.add_argument(
        "--user-agent="
        "Mozilla/5.0 (X11; Linux x86_64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/140.0.0.0 Safari/537.36"
    )

    # Do not wait forever for ads/analytics.
    options.page_load_strategy = "eager"

    driver = webdriver.Chrome(options=options)
    driver.set_page_load_timeout(PAGE_TIMEOUT)
    return driver


def dismiss_cookie_banner(driver):
    selectors = [
        "#onetrust-accept-btn-handler",
        "button#onetrust-accept-btn-handler",
    ]

    for selector in selectors:
        try:
            buttons = driver.find_elements(By.CSS_SELECTOR, selector)
            if buttons:
                driver.execute_script("arguments[0].click();", buttons[0])
                time.sleep(0.5)
                return
        except Exception:
            pass


def get_story_links(driver):
    """Return NPR headline links currently visible in DOM order."""
    results = []

    elements = driver.find_elements(
        By.CSS_SELECTOR,
        "article.item h2.title a[href]",
    )

    for element in elements:
        try:
            href = element.get_attribute("href")
        except StaleElementReferenceException:
            continue

        if not href:
            continue

        href = href.split("#", 1)[0].split("?", 1)[0]

        if href.startswith("http://www.npr.org/"):
            href = href.replace(
                "http://www.npr.org/",
                "https://www.npr.org/",
                1,
            )

        if not href.startswith("https://www.npr.org/"):
            continue

        if "/people/638550790/bobby-allyn" in href:
            continue

        if href not in results:
            results.append(href)

    return results


def find_load_more(driver):
    selectors = [
        "button.options__load-more",
        ".options button",
    ]

    for selector in selectors:
        try:
            for element in driver.find_elements(By.CSS_SELECTOR, selector):
                if element.is_displayed() and element.is_enabled():
                    if "load more" in element.text.strip().lower():
                        return element
        except StaleElementReferenceException:
            pass

    xpath_candidates = [
        "//button[contains(translate(normalize-space(.), "
        "'ABCDEFGHIJKLMNOPQRSTUVWXYZ', 'abcdefghijklmnopqrstuvwxyz'), "
        "'load more stories')]",
        "//*[self::button or self::a][contains(translate(normalize-space(.), "
        "'ABCDEFGHIJKLMNOPQRSTUVWXYZ', 'abcdefghijklmnopqrstuvwxyz'), "
        "'load more')]",
    ]

    for xpath in xpath_candidates:
        try:
            for element in driver.find_elements(By.XPATH, xpath):
                if element.is_displayed() and element.is_enabled():
                    return element
        except StaleElementReferenceException:
            pass

    return None


def scroll_to_loader(driver):
    """Scroll through the archive page so NPR's loader initializes."""
    try:
        height = driver.execute_script("return document.body.scrollHeight")

        for i in range(1, 9):
            driver.execute_script(
                "window.scrollTo(0, arguments[0]);",
                int(height * i / 8),
            )
            time.sleep(0.25)

        driver.execute_script("window.scrollTo(0, document.body.scrollHeight);")
        time.sleep(1)
    except Exception:
        pass


def collect_first_50_urls(driver):
    log("Opening NPR author page:")
    log(AUTHOR_URL)
    log()

    driver.get(AUTHOR_URL)

    WebDriverWait(driver, 30).until(
        lambda d: len(
            d.find_elements(By.CSS_SELECTOR, "article.item h2.title a[href]")
        ) > 0
    )

    dismiss_cookie_banner(driver)

    links = []
    seen = set()
    no_growth_rounds = 0

    def harvest():
        added = 0
        for link in get_story_links(driver):
            if link not in seen:
                seen.add(link)
                links.append(link)
                added += 1

                if len(links) >= LIMIT:
                    break
        return added

    harvest()
    log(f"Found {len(links)} article links so far.")

    while len(links) < LIMIT:
        before = len(links)

        scroll_to_loader(driver)
        harvest()

        if len(links) >= LIMIT:
            break

        button = find_load_more(driver)

        if button is None:
            # One extra bottom-scroll/reflow attempt before counting this as no growth.
            driver.execute_script("window.scrollTo(0, document.body.scrollHeight);")
            time.sleep(3)
            harvest()
            button = find_load_more(driver)

        if len(links) >= LIMIT:
            break

        if button is not None:
            try:
                driver.execute_script(
                    "arguments[0].scrollIntoView({behavior: 'instant', block: 'center'});",
                    button,
                )
                time.sleep(0.5)
                driver.execute_script("arguments[0].click();", button)

                try:
                    WebDriverWait(driver, WAIT_AFTER_CLICK).until(
                        lambda d: len(get_story_links(d)) > before
                    )
                except TimeoutException:
                    pass

                time.sleep(1)
                harvest()
            except Exception as exc:
                log(f"Load More click failed: {exc}")

        if len(links) > before:
            no_growth_rounds = 0
            log(f"Found {len(links)} article links so far.")
        else:
            no_growth_rounds += 1
            log(f"No new links this round ({no_growth_rounds}/3).")

            if no_growth_rounds >= 3:
                break

    return links[:LIMIT]


def fully_render_page(driver):
    """Scroll through an article once so lazy-rendered content enters the DOM."""
    try:
        height = driver.execute_script("return document.body.scrollHeight")

        for i in range(1, 9):
            driver.execute_script(
                "window.scrollTo(0, arguments[0]);",
                int(height * i / 8),
            )
            time.sleep(0.25)

        driver.execute_script("window.scrollTo(0, 0);")
        time.sleep(1)
    except Exception:
        pass


def archive_urls(driver, urls):
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    successes = 0
    failures = 0
    manifest_lines = []

    log()
    log(f"Archiving {len(urls)} NPR articles...")
    log()

    for number, url in enumerate(urls, 1):
        log("=" * 78)
        log(f"[{number:02d}/{len(urls):02d}] {url}")

        filename = f"{number:03d}.html"
        output_path = OUTPUT_DIR / filename
        success = False
        error_message = ""

        for attempt in range(1, 3):
            try:
                if attempt > 1:
                    log(f"    Retry {attempt}/2...")

                driver.get(url)

                try:
                    WebDriverWait(driver, 20).until(
                        lambda d: len(d.find_elements(By.TAG_NAME, "body")) > 0
                    )
                except TimeoutException:
                    pass

                dismiss_cookie_banner(driver)
                fully_render_page(driver)

                html = driver.page_source
                if not html or len(html) < 1000:
                    raise RuntimeError(
                        f"Suspiciously small HTML ({len(html)} bytes)"
                    )

                output_path.write_text(html, encoding="utf-8")
                title = driver.title

                manifest_lines.append(f"{number:03d}\t{url}\t{title}")
                successes += 1
                success = True

                log(f"    SAVED: {filename}")
                log(f"    Title: {title}")
                break

            except Exception as exc:
                error_message = repr(exc)
                log(f"    Attempt {attempt} failed: {exc}")
                time.sleep(2)

        if not success:
            failures += 1
            manifest_lines.append(
                f"{number:03d}\t{url}\tERROR: {error_message}"
            )
            log("    FAILED after 2 attempts.")

        log(f"    Progress: {successes} saved, {failures} failed")

    (OUTPUT_DIR / "manifest.txt").write_text(
        "\n".join(manifest_lines) + "\n",
        encoding="utf-8",
    )

    (OUTPUT_DIR / "source_urls.txt").write_text(
        "\n".join(urls) + "\n",
        encoding="utf-8",
    )

    return successes, failures


def create_zip():
    if ZIP_FILE.exists():
        ZIP_FILE.unlink()

    with zipfile.ZipFile(ZIP_FILE, "w", compression=zipfile.ZIP_DEFLATED) as zf:
        for path in sorted(OUTPUT_DIR.iterdir()):
            if path.is_file():
                zf.write(path, arcname=path.name)


def main():
    # Start clean so stale HTML from an older run cannot enter the ZIP.
    if OUTPUT_DIR.exists():
        shutil.rmtree(OUTPUT_DIR)

    if ZIP_FILE.exists():
        ZIP_FILE.unlink()

    driver = make_driver()

    try:
        urls = collect_first_50_urls(driver)

        if len(urls) < LIMIT:
            raise RuntimeError(
                f"Only found {len(urls)} NPR article URLs; expected {LIMIT}."
            )

        log()
        log(f"Collected exactly {len(urls)} URLs. Starting archive step.")

        successes, failures = archive_urls(driver, urls)
    finally:
        driver.quit()

    log()
    log("Creating ZIP...")
    create_zip()

    log()
    log("=" * 78)
    log("DONE")
    log(f"Successfully archived: {successes}")
    log(f"Failed:                {failures}")
    log(f"ZIP: {ZIP_FILE.resolve()}")
    log("=" * 78)


if __name__ == "__main__":
    main()
