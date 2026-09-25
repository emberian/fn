// Drive the loopback web reader through a browser (D28 reader spike).
//   node tools/spike_reader_drive.mjs OUTDIR [BASE]
// BASE defaults to http://127.0.0.1:8919 (an ssh tunnel to the web client).
import { chromium } from "/Users/ember/tools/playwright/node_modules/playwright/index.mjs";
import fs from "node:fs";
const out = process.argv[2], base = process.argv[3] || "http://127.0.0.1:8919";
const log = [];
const note = (k, v) => { log.push({ step: k, ...v }); console.log(k, JSON.stringify(v)); };
const browser = await chromium.launch();
const desk = await browser.newContext({ viewport: { width: 1100, height: 900 } });
const phone = await browser.newContext({ viewport: { width: 390, height: 844 }, isMobile: true, hasTouch: true });
const page = await desk.newPage();
async function snap(p, name) {
  fs.writeFileSync(`${out}/${name}.html`, await p.content());
  await p.screenshot({ path: `${out}/${name}.png`, fullPage: true });
}
async function post(group, { reply, subject, body, sign = true, from }) {
  await page.goto(`${base}/compose?group=${group}` + (reply ? `&reply=${reply}` : ""));
  if (subject !== undefined) await page.fill("input[name=subject]", subject);
  if (from) await page.fill("input[name=sender]", from);
  await page.fill("textarea[name=body]", body);
  const box = page.locator("input[name=sign]");
  if (await box.count()) await box.setChecked(sign);
  await Promise.all([page.waitForNavigation(), page.click("button[value=post]")]);
  const badge = await page.locator("article .badge").first().textContent();
  const reason = await page.locator(".reason").first().textContent().catch(() => "");
  const meta = await page.locator("article .meta").first().textContent();
  return { badge, reason, meta };
}
async function numberOf(group, subject) {
  await page.goto(`${base}/g?name=${group}`);
  const link = page.locator("article h2 a", { hasText: subject }).first();
  const hrefv = await link.getAttribute("href");
  return Number(new URL(hrefv, base).searchParams.get("number"));
}
await page.goto(base + "/"); await snap(page, "01-groups");
let r = await post("fn.test", { subject: "Signed hello from the reader spike", body: "This article is signed on the author's machine.\n.a dot-led line" });
note("signed-new", r); await snap(page, "02-signed-accepted");
const root = await numberOf("fn.test", "Signed hello from the reader spike");
r = await post("fn.test", { reply: root, body: "A signed reply; References carries the parent." });
note("signed-reply", r);
const reply = await numberOf("fn.test", "Re: Signed hello from the reader spike");
r = await post("fn.test", { reply, body: "An unsigned reply to the reply.", sign: false });
note("unsigned-reply", r);
r = await post("fn.test", { subject: "Bad From", body: "refuse me", from: "not a mailbox", sign: false });
note("refused-441", r); await snap(page, "03-refused-441");
r = await post("fn.test", { subject: "Signed but bad From", body: "refuse me signed", from: "not a mailbox" });
note("refused-signed", r); await snap(page, "03b-refused-signed");
await page.goto(`${base}/g?name=fn.test`); await snap(page, "04-group-threaded");
const rows = await page.locator("article.thread").evaluateAll(els => els.map(a => ({ cls: a.className, subject: a.querySelector("h2 a").textContent, badge: a.querySelector(".badge").textContent })));
note("thread-order", { rows });
await page.goto(`${base}/a?group=fn.test&number=${root}`); await snap(page, "05-article-verified");
note("article-verdict", { text: await page.locator(".meta", { hasText: "verification" }).first().textContent() });
await page.goto(`${base}/search?group=fn.test&field=subject&q=probe root`); await snap(page, "06-search-subject");
note("search-subject", { hits: await page.locator("article h2 a").allTextContents(), cmd: await page.locator("p.muted code").first().textContent() });
await page.goto(`${base}/search?group=fn.test&field=from&q=guest`);
note("search-from", { hits: await page.locator("article h2 a").allTextContents(), cmd: await page.locator("p.muted code").first().textContent() });
await page.goto(`${base}/search?group=fn.test&field=subject&q=SIGNED`);
note("search-case", { hits: await page.locator("article h2 a").allTextContents() });
await page.goto(`${base}/`);
note("unread", { badges: await page.locator("article h2 .badge").allTextContents() });
// draft survives a reload (browser origin storage)
await page.goto(`${base}/compose?group=fn.agents`);
await page.fill("input[name=subject]", "Draft that survives");
await page.fill("textarea[name=body]", "typed before the reload");
await page.reload();
note("draft-reload", { subject: await page.inputValue("input[name=subject]"), body: await page.inputValue("textarea[name=body]"), note: await page.locator("#draft-note").textContent() });
await snap(page, "07-draft-restored");
await page.goto(`${base}/operator`); await snap(page, "08-operator");
note("operator", { text: (await page.locator("main, body").first().innerText()).slice(0, 1500) });
const m = await phone.newPage();
for (const [path, name] of [["/", "09-phone-groups"], [`/g?name=fn.test`, "10-phone-group"], [`/a?group=fn.test&number=${reply}`, "11-phone-article"], ["/compose?group=fn.test", "12-phone-compose"]]) {
  await m.goto(base + path); await m.screenshot({ path: `${out}/${name}.png`, fullPage: true });
  note(name, { scrollWidth: await m.evaluate(() => document.documentElement.scrollWidth) });
}
fs.writeFileSync(`${out}/drive.json`, JSON.stringify(log, null, 1));
await browser.close();
