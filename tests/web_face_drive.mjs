// A friend's first visit to the node's own web face (WEB-005, SCN-187), in a
// real Chromium: make the account from an invitation code, read, post, see
// the post, remove it, sign out and in, and the same pages on a phone.
//
//   node tests/web_face_drive.mjs BASE_URL SECRETS_JSON OUT_DIR
//
// BASE_URL reaches the face of a scratch node that tests/web_face_scratch.sh
// set up ([web] tls = true, so the cookie is Secure; an ssh -L tunnel to
// hbox; the node's self-made certificate, so HTTPS errors are ignored;
// FN_DRIVE_RESOLVE below). SECRETS_JSON holds the invitation code, the
// password the friend chooses, and the subject and body of the welcome post
// the operator made; the password is never written to OUT_DIR. Every check
// records what the page showed; the node decided it. The same 16 checks the
// Python reader's rehearsal made (planning/evidence/release-web-reader-2026-09-27.md).
import { chromium } from "/Users/ember/tools/playwright/node_modules/playwright/index.mjs";
import fs from "node:fs";
import path from "node:path";

const [base, secretsPath, out] = process.argv.slice(2);
const secrets = JSON.parse(fs.readFileSync(secretsPath, "utf8"));
fs.mkdirSync(out, { recursive: true });
const checks = [];
let failed = 0;

function check(name, ok, detail = "") {
  checks.push({ name, ok: !!ok, detail });
  if (!ok) failed += 1;
  console.log((ok ? "ok   " : "FAIL ") + name + (detail ? "  " + detail : ""));
}

async function shot(page, name) {
  await page.screenshot({ path: path.join(out, name + ".png"), fullPage: true });
}

// FN_DRIVE_RESOLVE=NAME:ADDRESS maps a web name to the tunnel's end, so the
// browser sends that name (Host and Origin) while dialing the tunnel.
const resolve = process.env.FN_DRIVE_RESOLVE;
const browser = await chromium.launch(resolve ? {
  args: ["--host-resolver-rules=MAP " + resolve.split(":")[0] + " " + resolve.split(":")[1]] } : {});
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

const context = await browser.newContext(desktop);
const page = watch(await context.newPage());
await page.goto(base + "/");
check("a new visitor is sent to the sign-in page", page.url().includes("/signin"));
await shot(page, "01-sign-in");

// The invitation: the friend makes the account here (the node's own XREDEEM).
await page.click("a:has-text('Make your account')");
await shot(page, "02-make-account");
await page.fill("#code", secrets.code);
await page.fill("#user", "carol");
await page.fill("#password", secrets.password);
await page.fill("#again", secrets.password);
await page.click("button:has-text('Make my account')");
const groups = await page.textContent("main");
check("the code made the account and signed carol in", groups.includes("local.general"),
      groups.slice(0, 160));
await shot(page, "03-groups");

// Read the group and the operator's welcome post.
await page.click("a.title:has-text('local.general')");
await shot(page, "04-group");
check("the welcome post is listed", (await page.textContent("main")).includes(secrets.welcome));
await page.click("a.title:has-text('" + secrets.welcome + "')");
check("reading the welcome post", (await page.textContent("main")).includes(secrets.welcomeBody));
await shot(page, "05-welcome");

// Post.
await page.goto(base + "/new?g=local.general");
await page.fill("#subject", "Hello from carol");
await page.fill("#body", "My first post, from the browser. Grüße ✓");
await shot(page, "06-compose");
await page.click("button:has-text('Post')");
check("posted (the node accepted it)", (await page.textContent("main")).includes("Posted!"));
await shot(page, "07-posted");

// See the post.
await page.goto(base + "/g?name=local.general");
check("the post is in the group", (await page.textContent("main")).includes("Hello from carol"));
await shot(page, "08-group-with-post");
await page.click("a.title:has-text('Hello from carol')");
check("the post reads back", (await page.textContent("main")).includes("My first post, from the browser. Grüße ✓"));
await shot(page, "09-post");

// Cancel it.
await page.click("a:has-text('Remove my post')");
await shot(page, "10-remove-confirm");
await page.click("button:has-text('Remove it')");
const removed = await page.textContent("main");
check("removed (the node withdrew it: 430)", removed.includes("Your post has been removed"),
      removed.slice(0, 160));
await shot(page, "11-removed");
await page.goto(base + "/g?name=local.general");
check("the post is gone from the group", !(await page.textContent("main")).includes("Hello from carol"));
await shot(page, "12-group-after");

// The session cookie: HttpOnly and Secure (the face serves HTTPS itself).
const cookie = (await context.cookies()).find((c) => c.name === "fnr_session");
check("the session cookie is HttpOnly and Secure", cookie && cookie.httpOnly && cookie.secure,
      JSON.stringify(cookie && { httpOnly: cookie.httpOnly, secure: cookie.secure, sameSite: cookie.sameSite }));

// Sign out, then back in with the chosen name and password (AUTHINFO).
await page.click("button:has-text('Sign out')");
check("signed out", page.url().includes("/signin"));
await page.fill("#user", "carol");
await page.fill("#password", "not-the-password");
await page.click("button:has-text('Sign in')");
check("a wrong password is refused in plain words", (await page.textContent("main")).includes("don't match"));
await page.fill("#user", "carol");
await page.fill("#password", secrets.password);
await page.click("button:has-text('Sign in')");
check("signed in again with the chosen password", (await page.textContent("main")).includes("local.general"));

// The same page on a phone.
const small = watch(await (await browser.newContext(phone)).newPage());
await small.goto(base + "/signin");
await small.fill("#user", "carol");
await small.fill("#password", secrets.password);
await small.click("button:has-text('Sign in')");
await small.waitForLoadState("load");
const width = await small.evaluate(() => document.documentElement.scrollWidth);
check("phone: no sideways scrolling", width <= 390, "scrollWidth " + width);
await shot(small, "13-phone-groups");

check("no page ever carries the password (" + bodies.length + " pages)",
      bodies.every((b) => !b.text.includes(secrets.password)));
check("every page forbids scripts (CSP default-src 'none')",
      bodies.every((b) => b.csp.includes("default-src 'none'")));
await browser.close();
fs.writeFileSync(path.join(out, "drive.json"), JSON.stringify({ base, checks, failed }, null, 1));
console.log(failed ? `${failed} FAILED` : `all ${checks.length} checks ok`);
process.exit(failed ? 1 : 0);
