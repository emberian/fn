// sanding scripted walk: the group view's withdrawn-parent flag and the
// conversation page agree (NNT-032).  A script, not a human study.
//   node web_walk.mjs BASE OUTDIR GROUP
import { chromium } from "/Users/ember/tools/playwright/node_modules/playwright/index.mjs";
import { writeFileSync } from "fs";
const [base, out, group] = process.argv.slice(2);
const browser = await chromium.launch();
const page = await browser.newPage({ viewport: { width: 1000, height: 1100 } });
const log = [];
async function step(name, fn) {
  await fn();
  const text = (await page.innerText("body")).replace(/\n{2,}/g, "\n");
  await page.screenshot({ path: `${out}/${name}.png`, fullPage: true });
  log.push({ name, url: page.url(), text: text.slice(0, 2400) });
  console.log(`=== ${name} ${page.url()}\n${text.slice(0, 1600)}\n`);
}
await step("01-home", () => page.goto(base + "/"));
await step("02-group", () => page.click(`text=${group}`));
const pill = page.locator("text=parent withdrawn");
const pills = await pill.count();
console.log(`parent-withdrawn pills on the group page: ${pills}`);
log.push({ name: "pills", count: pills });
// Open the conversation of the card that carries the pill.
// The flagged card's "conversation" link: the same parent, the same answer.
await step("03-flagged-card-conversation", async () => {
  const card = pill.first().locator("xpath=ancestor::*[.//a][1]");
  await card.locator("a").first().click();
});
const agree = (await page.innerText("body")).includes("the node answered 430 withdrawn");
console.log(`conversation shows the parent as 430 withdrawn: ${agree}`);
log.push({ name: "agree", conversationWithdrawn: agree });
writeFileSync(`${out}/web-walk.json`, JSON.stringify(log, null, 1));
await browser.close();
