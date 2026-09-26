// reader-daily scripted walk, part 1: reading as a person would (a script, not a human study).
import { chromium } from "/Users/ember/tools/playwright/node_modules/playwright/index.mjs";
const base = "http://127.0.0.1:8968";
const out = process.argv[2];
const browser = await chromium.launch();
const page = await browser.newPage({ viewport: { width: 900, height: 1000 } });
const log = [];
async function step(name, fn) {
  await fn();
  const text = (await page.innerText("body")).replace(/\n{2,}/g, "\n");
  await page.screenshot({ path: `${out}/${name}.png`, fullPage: true });
  log.push({ name, url: page.url(), text: text.slice(0, 1800) });
  console.log(`=== ${name} ${page.url()}\n${text.slice(0, 1400)}\n`);
}
await step("01-home", () => page.goto(base + "/"));
await step("02-group", () => page.click("text=fn.agents"));
await step("03-open-tin-reply", async () => {
  await page.click("a:has-text('Re: Daily walk')");
});
await step("04-conversation", () => page.click("nav >> text=Conversation"));
await step("05-search", async () => {
  await page.click("nav >> a >> nth=0");
  await page.fill("input[name=q]", "*notes*");
  await page.click("button:has-text('Search')");
});
await step("06-withdrawn-number", () => page.goto(base + "/a?group=fn.agents&number=2"));
await browser.close();
import { writeFileSync } from "fs";
writeFileSync(`${out}/walk1.json`, JSON.stringify(log, null, 1));
