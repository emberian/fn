// Headless browser run of the friends' reader (SCN-173, WEB-003).
//
//   node tests/fn_reader_drive.mjs BASE_URL LOGINS_JSON OUT_DIR
//
// BASE_URL reaches tools/fn_reader.py in front of the scratch node that
// tests/fn_reader_scratch.py set up (an ssh -L tunnel to hbox). LOGINS_JSON
// holds that throwaway node's three passwords; they are never written to
// OUT_DIR. Every check records what the page showed; the node decided it.
import { chromium } from "/Users/ember/tools/playwright/node_modules/playwright/index.mjs";
import fs from "node:fs";
import path from "node:path";

const [base, loginsPath, out] = process.argv.slice(2);
const logins = JSON.parse(fs.readFileSync(loginsPath, "utf8"));
fs.mkdirSync(out, { recursive: true });
const checks = [];
const timings = [];
let failed = 0;

function check(name, ok, detail = "") {
  checks.push({ name, ok: !!ok, detail });
  if (!ok) failed += 1;
  console.log((ok ? "ok   " : "FAIL ") + name + (detail ? "  " + detail : ""));
}

async function shot(page, name) {
  await page.screenshot({ path: path.join(out, name + ".png"), fullPage: true });
}

async function timed(page, label, action) {
  const start = Date.now();
  await action();
  await page.waitForLoadState("load");
  timings.push({ label, ms: Date.now() - start });
}

async function signIn(page, user, password) {
  await page.goto(base + "/signin");
  await page.fill("#user", user);
  await page.fill("#password", password);
  await timed(page, "sign in " + user, () => page.click("button[type=submit]:has-text('Sign in')"));
}

async function noSideScroll(page, label) {
  await page.waitForLoadState("load");
  const width = await page.evaluate(() => document.documentElement.scrollWidth);
  check("phone: no sideways scrolling on " + label, width <= 390, "scrollWidth " + width);
}

const browser = await chromium.launch();
const bodies = [];
function watch(page) {
  page.on("response", async (response) => {
    try {
      if ((response.headers()["content-type"] || "").startsWith("text/html")) {
        bodies.push({ url: response.url(), csp: response.headers()["content-security-policy"] || "",
                      text: await response.text() });
      }
    } catch (error) { /* a redirect has no body */ }
  });
  return page;
}
const desktop = { viewport: { width: 1100, height: 900 }, ignoreHTTPSErrors: true, colorScheme: "light" };
const phone = { viewport: { width: 390, height: 844 }, ignoreHTTPSErrors: true, isMobile: true,
                hasTouch: true, deviceScaleFactor: 2, colorScheme: "light" };

// ---------------------------------------------------------------- alice
const alice = watch(await (await browser.newContext(desktop)).newPage());
await alice.goto(base + "/");
check("signed out: sent to the sign-in page", alice.url().includes("/signin"));
await shot(alice, "01-sign-in");
await alice.fill("#user", "alice");
await alice.fill("#password", "not-her-password");
await alice.click("button:has-text('Sign in')");
check("a wrong password is refused in plain words",
      (await alice.textContent("main")).includes("don't match"));
await shot(alice, "02-wrong-password");
await signIn(alice, "alice", logins.alice);
const groupsText = await alice.textContent("main");
check("alice signed in: groups listed", groupsText.includes("fn.friends"));
check("groups carry their descriptions", groupsText.includes("Say hello, share news"));
check("alice sees the private group", groupsText.includes("fn.private.club"));
check("alice (moderator) sees the approval queue", groupsText.includes("fn.mod.moderation"));
check("the moderated group says so", groupsText.includes("A moderator checks new posts"));
check("unread shown per group", /\d+ new/.test(groupsText));
await shot(alice, "03-groups-alice");

await timed(alice, "group page", () => alice.click("a.title:has-text('fn.friends')"));
await shot(alice, "04-group");
await timed(alice, "thread page", () => alice.click("a.title:has-text('Welcome')"));
check("reading an article", (await alice.textContent("main")).includes("This is our little news server"));
await shot(alice, "05-thread");

// reply
await alice.click("a:has-text('Reply')");
check("reply form fills the subject", (await alice.inputValue("#subject")) === "Re: Welcome, everyone!");
await alice.fill("#body", "Hello from the web reader! Grüße, ✓\n\n> quoting works too");
await shot(alice, "06-reply-form");
await timed(alice, "post reply", () => alice.click("button:has-text('Post')"));
check("reply posted", (await alice.textContent("main")).includes("Posted!"));
await shot(alice, "07-posted");
await alice.goto(base + "/g?name=fn.friends");
await alice.click("a.title:has-text('Welcome')");
const threadText = await alice.textContent("main");
check("the reply sits in the thread", threadText.includes("Hello from the web reader! Grüße, ✓"));
check("the reply is indented under its parent", (await alice.locator("article.post.d1").count()) === 1);
await shot(alice, "08-thread-with-reply");

// new post, then cancel it
await alice.goto(base + "/new?g=fn.friends");
await alice.fill("#subject", "Oops, wrong group");
await alice.fill("#body", "I will remove this one.");
await alice.click("button:has-text('Post')");
check("new post posted", (await alice.textContent("main")).includes("Posted!"));
await alice.goto(base + "/g?name=fn.friends");
await alice.click("a.title:has-text('Oops, wrong group')");
await alice.click("a:has-text('Remove my post')");
await shot(alice, "09-remove-confirm");
await alice.click("button:has-text('Remove it')");
const removed = await alice.textContent("main");
check("own post removed (the node withdrew it)", removed.includes("Your post has been removed"), removed.slice(0, 120));
await shot(alice, "10-removed");
await alice.goto(base + "/g?name=fn.friends");
check("removed post gone from the group", !(await alice.textContent("main")).includes("Oops, wrong group"));

// unread goes to zero after reading
await alice.goto(base + "/");
const friendsRow = await alice.locator("li", { hasText: "fn.friends" }).first().textContent();
check("fn.friends all read after reading", friendsRow.includes("all read"), friendsRow.trim());

// moderation: approve carol's held post
await alice.goto(base + "/g?name=fn.mod");
check("held post not yet in fn.mod", !(await alice.textContent("main")).includes("Garden party"));
await alice.goto(base + "/g?name=fn.mod.moderation");
check("queue lists the waiting post", (await alice.textContent("main")).includes("Waiting for approval: Garden party"));
await alice.click("a.title:has-text('Garden party')");
await shot(alice, "11-waiting-for-approval");
await alice.click("button:has-text('Approve and publish')");
check("approved", (await alice.textContent("main")).includes("Approved."));
await alice.goto(base + "/g?name=fn.mod");
check("approved post now in fn.mod", (await alice.textContent("main")).includes("Garden party"));
await shot(alice, "12-approved-in-group");

// dark theme
await alice.goto(base + "/g?name=fn.friends");
await alice.click("footer button:has-text('Dark')");
check("dark theme chosen", (await alice.getAttribute("html", "data-theme")) === "dark");
await alice.click("a.title:has-text('Welcome')");
await shot(alice, "13-thread-dark");
await alice.click("footer button:has-text('Light')");

// ---------------------------------------------------------------- bob
const bob = watch(await (await browser.newContext(desktop)).newPage());
await signIn(bob, "bob", logins.bob);
const bobGroups = await bob.textContent("main");
check("bob signed in", bobGroups.includes("fn.friends"));
check("private group hidden from bob", !bobGroups.includes("fn.private.club"));
check("approval queue hidden from bob", !bobGroups.includes("fn.mod.moderation"));
await shot(bob, "14-groups-bob");
const direct = await bob.goto(base + "/g?name=fn.private.club");
check("private group by address: not found for bob", direct.status() === 404 &&
      (await bob.textContent("main")).includes("couldn't find that group"));
await shot(bob, "15-private-hidden-bob");
await bob.goto(base + "/g?name=fn.friends");
await bob.click("a.title:has-text('Welcome')");
check("bob is offered no removal of alice's posts", (await bob.locator("a:has-text('Remove my post')").count()) === 0);

// ---------------------------------------------------------------- carol on a phone
const carol = watch(await (await browser.newContext(phone)).newPage());
await signIn(carol, "carol", logins.carol);
await shot(carol, "16-phone-groups");
await noSideScroll(carol, "groups");
await carol.goto(base + "/g?name=fn.friends");
await noSideScroll(carol, "group");
await carol.click("a.title:has-text('Welcome')");
await noSideScroll(carol, "thread");
await shot(carol, "17-phone-thread");
await carol.goto(base + "/new?g=fn.mod");
await noSideScroll(carol, "compose");
await carol.fill("#subject", "Lost umbrella");
await carol.fill("#body", "Did anyone find a blue umbrella?");
await shot(carol, "18-phone-compose");
await carol.click("button:has-text('Post')");
check("moderated post: told a moderator will look", (await carol.textContent("main")).includes("A moderator will look at it"));
await shot(carol, "19-phone-sent-for-approval");
const carolPrivate = await carol.goto(base + "/g?name=fn.private.club");
check("carol (no rule) can open the private group", carolPrivate.status() === 200);

// sign out
await alice.click("button:has-text('Sign out')");
check("signed out", alice.url().includes("/signin"));
await alice.goto(base + "/");
check("after sign-out the pages need a sign-in", alice.url().includes("/signin"));

const secrets = Object.values(logins);
check("no page ever carries a password (" + bodies.length + " pages)",
      bodies.every((b) => secrets.every((s) => !b.text.includes(s))));
check("every page forbids scripts and other sites (CSP default-src 'none')",
      bodies.every((b) => b.csp.includes("default-src 'none'")));
check("no page has a script element", bodies.every((b) => !/<script/i.test(b.text)));
await browser.close();
fs.writeFileSync(path.join(out, "drive.json"), JSON.stringify({ base, checks, timings, failed }, null, 1));
console.log("timings", JSON.stringify(timings));
console.log(failed ? `${failed} FAILED` : `all ${checks.length} checks ok`);
process.exit(failed ? 1 : 0);
