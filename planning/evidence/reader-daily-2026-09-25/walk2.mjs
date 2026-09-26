// reader-daily scripted walk, part 2: reply, double-click, back and post again, save a draft.
import { chromium } from "/Users/ember/tools/playwright/node_modules/playwright/index.mjs";
import { writeFileSync } from "fs";
const base = "http://127.0.0.1:8968", out = process.argv[2], part = process.argv[3];
const browser = await chromium.launch();
const page = await browser.newPage({ viewport: { width: 900, height: 1000 } });
const log = [];
async function step(name, fn) {
  await fn();
  const text = (await page.innerText("body")).replace(/\n{2,}/g, "\n");
  await page.screenshot({ path: `${out}/${part}-${name}.png`, fullPage: true });
  log.push({ name, url: page.url(), text: text.slice(0, 1800) });
  console.log(`=== ${name} ${page.url()}\n${text.slice(0, 900)}\n`);
}
if (part === "reply") {
  await step("01-conversation", () => page.goto(base + "/t?group=fn.agents&number=3"));
  await step("02-reply-form", () => page.click("nav >> text=Reply"));
  await step("03-dblclick-post", async () => {
    await page.fill("textarea[name=body]", "ember from the web: agreed, the shared doc.");
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
  await step("06-check", () => page.click("button:has-text('Check whether the node serves')"));
  await step("07-draft-back", async () => { await page.goto(base + "/outbox"); await page.click("article:has(.badge:text-is('draft')) a"); });
  await step("08-group", () => page.goto(base + "/g?name=fn.agents"));
}
await browser.close();
writeFileSync(`${out}/walk2-${part}.json`, JSON.stringify(log, null, 1));
