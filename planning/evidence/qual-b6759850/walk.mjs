// qual-b6759850 web reader pass: reader-daily's walk1.mjs + walk2.mjs (same
// selectors and order) plus the provenance panel of a signed article.
// A scripted walk, not a human study.  node walk.mjs OUTDIR PART
import { chromium } from "/Users/ember/tools/playwright/node_modules/playwright/index.mjs";
import { writeFileSync } from "fs";
const base = "http://127.0.0.1:8968", out = process.argv[2], part = process.argv[3];
const browser = await chromium.launch();
const page = await browser.newPage({ viewport: { width: 900, height: 1000 } });
const log = [];
async function step(name, fn) {
  try { await fn(); } catch (e) { log.push({ name, error: String(e).slice(0, 400) }); console.log(`=== ${name} ERROR ${e}`); return; }
  const text = (await page.innerText("body")).replace(/\n{2,}/g, "\n");
  await page.screenshot({ path: `${out}/${part}-${name}.png`, fullPage: true });
  log.push({ name, url: page.url(), text: text.slice(0, 2400) });
  console.log(`=== ${name} ${page.url()}\n${text.slice(0, 1400)}\n`);
}
if (part === "reading") {
  await step("01-home", () => page.goto(base + "/"));
  await step("02-group", () => page.click("text=fn.agents"));
  await step("03-open-tin-reply", () => page.click("a:has-text('Re: Daily walk')"));
  await step("04-conversation", () => page.click("nav >> text=Conversation"));
  await step("05-search", async () => {
    await page.click("nav >> a >> nth=0");
    await page.fill("input[name=q]", "*notes*");
    await page.click("button:has-text('Search')");
  });
  await step("06-withdrawn-number", () => page.goto(base + "/a?group=fn.agents&number=2"));
  await step("07-provenance-signed-root", () => page.goto(base + "/a?group=fn.agents&number=1"));
  await step("08-provenance-guest-carrying-Q", () => page.goto(base + "/a?group=fn.agents&number=9"));
} else if (part === "reply") {
  await step("01-conversation", () => page.goto(base + "/t?group=fn.agents&number=3"));
  await step("02-reply-form", () => page.click("nav >> text=Reply"));
  await step("03-dblclick-post", async () => {
    await page.fill("textarea[name=body]", "guest from the web: agreed, the shared doc.");
    await Promise.all([page.waitForURL(/\/result/), page.dblclick("button[value=post]")]);
  });
  await step("04-back-and-post-again", async () => {
    await page.goBack();
    await page.waitForLoadState();
    if (await page.locator("button[value=post]").count()) {
      await Promise.all([page.waitForURL(/\/result/), page.click("button[value=post]")]);
    }
  });
  await step("05-refresh", () => page.reload());
  await step("06-draft", async () => {
    await page.goto(base + "/compose?group=fn.agents");
    await page.fill("input[name=subject]", "draft: tomorrow's notes");
    await page.fill("textarea[name=body]", "half a thought");
    await page.click("button[value=save]");
  });
} else if (part === "lost") {
  await step("01-compose", () => page.goto(base + "/compose?group=fn.agents"));
  await step("02-post-node-unreachable", async () => {
    await page.fill("input[name=subject]", "walk: posted while the node was unreachable");
    await page.fill("textarea[name=body]", "sent with the tunnel down");
    await Promise.all([page.waitForURL(/\/result/), page.click("button[value=post]")]);
  });
} else if (part === "resume") {
  await step("01-home", () => page.goto(base + "/"));
  await step("02-outbox", () => page.click("text=Local outbox"));
  await step("03-uncertain-record", () => page.click("article:has(.badge.uncertain) a"));
  await step("04-reconcile", () => page.click("button:has-text('Re-send this same article')"));
  await step("05-outbox-after", () => page.goto(base + "/outbox"));
  await step("06-reconcile-again", async () => {
    await page.click("article:has-text('unreachable') a");
    if (await page.locator("button:has-text('Re-send this same article')").count())
      await page.click("button:has-text('Re-send this same article')");
  });
  await step("07-draft-back", async () => { await page.goto(base + "/outbox"); await page.click("article:has(.badge:text-is('draft')) a"); });
  await step("08-group", () => page.goto(base + "/g?name=fn.agents"));
}
await browser.close();
writeFileSync(`${out}/walk-${part}.json`, JSON.stringify(log, null, 1));
