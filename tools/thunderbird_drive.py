#!/usr/bin/env python3
"""Drive stock Thunderbird against an fn node over implicit TLS, headless.

    python3 tools/thunderbird_drive.py --thunderbird BIN --work DIR --port TLS_PORT
        --cafile CA.pem --group GROUP --user LOGIN --password-file FILE
        --email ADDRESS --log WIRE.log [--parent-subject S]

Test tool (reader-clients lane, V0-CLIENT-THUNDERBIRD-*).  Thunderbird runs
`--headless --marionette` on a fresh profile under WORK; this script speaks
the Marionette wire protocol (stdlib only) and runs chrome-context
JavaScript that uses Thunderbird's own mail code, never a hand-written NNTP
dialogue:

  setup   the scratch CA goes into the profile's NSS store as an SSL trust
          anchor (nsIX509CertDB.addCertFromBase64(DER, "C,,")), so the
          node's certificate is verified, not overridden; an nntp server
          (socketType SSL, always_authenticate) with one identity is created
          through MailServices.accounts, and the login goes to the profile's
          login manager under the folder's signon URL
  read    the group is subscribed and fetched (folder.getNewMessages) and
          the first article streamed through the news message service
  reply   nsIMsgCompose, type ReplyToGroup on that article (Thunderbird
          derives Subject and References), sendMsg(DeliverNow)
  post    nsIMsgCompose, type New, Newsgroups = GROUP
  cancel  the group is fetched again and the posted article cancelled with
          nsIMsgNewsFolder.cancelMessage (Thunderbird's `Control: cancel`)

The wire log is Thunderbird's own NNTP logger (`mailnews.nntp.loglevel` =
All): every command it sent through _sendCommand (`C:`) and every chunk the
node sent after the TLS layer (`S:`), taken from the console API storage.
It is written in tools/nntp_wire_log.py's line format, `TIME CONN C|S: LINE`,
with one `TIME 0 --- action NAME` marker before each step.  Thunderbird
itself suppresses the AUTHINFO lines on release builds, and article bodies
it writes with send() rather than _sendCommand are not in its log; the POST
command and the node's reply lines are.  Prints one JSON object: per action
its outcome, the Message-IDs Thunderbird reported and any error.
"""
import argparse
import base64
import json
import os
import re
import shutil
import socket
import subprocess
import sys
import time
from pathlib import Path


class Marionette:
    """The Marionette protocol: `LEN:JSON` frames, [0, id, name, params]."""

    def __init__(self, port, deadline=90):
        end = time.monotonic() + deadline
        while True:
            try:
                self.sock = socket.create_connection(("127.0.0.1", port), timeout=5)
                break
            except OSError:
                if time.monotonic() > end:
                    raise
                time.sleep(0.5)
        self.sock.settimeout(600)
        self.buffer = b""
        self.next_id = 0
        self.hello = self.frame()

    def frame(self):
        while True:
            if b":" in self.buffer:
                size_text, _, rest = self.buffer.partition(b":")
                size = int(size_text)
                if len(rest) >= size:
                    self.buffer = rest[size:]
                    return json.loads(rest[:size])
            self.fill()

    def fill(self):
        chunk = self.sock.recv(65536)
        if not chunk:
            raise ConnectionError("marionette closed the connection")
        self.buffer += chunk

    def call(self, name, params=None):
        self.next_id += 1
        body = json.dumps([0, self.next_id, name, params or {}]).encode()
        self.sock.sendall(str(len(body)).encode() + b":" + body)
        while True:
            reply = self.frame()
            if reply[0] == 1 and reply[1] == self.next_id:
                if reply[2]:
                    raise RuntimeError("{}: {}".format(name, reply[2].get("message",
                                                                          reply[2])))
                return reply[3]

    def script(self, source, args=(), timeout_ms=240000):
        """Run SOURCE as an async chrome script; `resolve(value)` ends it."""
        wrapped = ("const resolve = arguments[arguments.length - 1];\n"
                   "(async () => {\n" + source + "\n})().catch(e => resolve("
                   "{error: String(e) + (e && e.stack ? ' @ ' + e.stack.split('\\n')[0] : '')}));")
        self.call("WebDriver:SetTimeouts", {"script": timeout_ms})
        return self.call("WebDriver:ExecuteAsyncScript",
                         {"script": wrapped, "args": list(args), "newSandbox": False,
                          "sandbox": "fnmatrix"}).get("value")


PREFS = {
    "mailnews.nntp.loglevel": "All",
    "mailnews.send.loglevel": "All",
    "mailnews.compose.loglevel": "All",
    "news.cancel.confirm": False,
    "mail.shell.checkDefaultClient": False,
    "mailnews.start_page.enabled": False,
    "mail.provider.enabled": False,
    "mail.rights.override": True,
    "mail.rights.version": 1,
    "app.update.disabledForTesting": True,
    "app.update.auto": False,
    "datareporting.policy.dataSubmissionEnabled": False,
    "toolkit.telemetry.reportingpolicy.firstRun": False,
    "mail.biff.show_alert": False,
    "mail.biff.play_sound": False,
    "mailnews.auto_config.fetchFromISP.enabled": False,
    "mail.startup.enabledMailCheckOnce": True,
    "signon.rememberSignons": True,
    "mail.account.hub.enabled": False,
}

# Everything below runs in Thunderbird's chrome context.  `window.fnm` keeps
# the collected log and the objects between steps.
SETUP_JS = r"""
const [port, caB64, group, user, password, email] = arguments;
const { MailServices } = ChromeUtils.importESModule("resource:///modules/MailServices.sys.mjs");
const fnm = window.fnm = { wire: [], mids: {} };
const storage = Cc["@mozilla.org/consoleAPI-storage;1"].getService(Ci.nsIConsoleAPIStorage);
fnm.diag = [];
fnm.listener = ev => {
  if (ev.prefix !== "mailnews.nntp") {
    fnm.diag.push([ev.level, ev.prefix || "", (ev.arguments || []).map(String).join(" ").slice(0, 400)]);
    return;
  }
  fnm.wire.push([ev.timeStamp || Date.now(), ev.level, (ev.arguments || []).map(String).join(" ")]);
};
storage.addLogEventListener(fnm.listener, Services.scriptSecurityManager.getSystemPrincipal());
fnm.consoleListener = { observe(m) { fnm.diag.push(["console", "", String(m.message || m).slice(0, 600)]); } };
Services.console.registerListener(fnm.consoleListener);
Services.obs.addObserver(subject => {
  try {
    const doc = subject.document || subject;
    fnm.diag.push(["dialog", "", String(doc.getElementById("infoBody")?.textContent || doc.documentElement?.textContent || "").slice(0, 400)]);
  } catch (e) { fnm.diag.push(["dialog", "", String(e)]); }
}, "common-dialog-loaded");
fnm.mark = name => fnm.wire.push([Date.now(), "mark", "--- action " + name]);
const certdb = Cc["@mozilla.org/security/x509certdb;1"].getService(Ci.nsIX509CertDB);
const ca = certdb.addCertFromBase64(caB64, "C,,");
const server = MailServices.accounts.createIncomingServer(user, "127.0.0.1", "nntp");
server.port = port;
server.socketType = Ci.nsMsgSocketType.SSL;
server.setBoolValue("always_authenticate", true);
server.valid = true;
const identity = MailServices.accounts.createIdentity();
identity.email = email;
identity.fullName = user;
identity.doFcc = false;
identity.archiveEnabled = false;
const account = MailServices.accounts.createAccount();
account.addIdentity(identity);
account.incomingServer = server;
const news = server.QueryInterface(Ci.nsINntpIncomingServer);
news.subscribeToNewsgroup(group);
const folder = server.rootFolder.getChildNamed(group).QueryInterface(Ci.nsIMsgNewsFolder);
const signons = new Set([server.rootFolder.QueryInterface(Ci.nsIMsgNewsFolder).urlForSignon,
                         folder.urlForSignon]);
for (const url of signons) {
  const info = Cc["@mozilla.org/login-manager/loginInfo;1"].createInstance(Ci.nsILoginInfo);
  info.init(Services.io.newURI(url).prePath, null, url, user, password, "", "");
  await Services.logins.addLoginAsync(info);
}
fnm.server = server; fnm.folder = folder; fnm.identity = identity; fnm.account = account;
fnm.group = group;
fnm.msgWindow = Cc["@mozilla.org/messenger/msgwindow;1"].createInstance(Ci.nsIMsgWindow);
fnm.fetch = () => new Promise(done => {
  const f = fnm.folder.QueryInterface(Ci.nsIMsgFolder);
  f.getNewMessages(fnm.msgWindow, { OnStartRunningUrl() {},
    OnStopRunningUrl(url, status) { done(status); } });
});
fnm.headers = () => [...fnm.folder.QueryInterface(Ci.nsIMsgFolder).messages].map(h => ({
  key: h.messageKey, subject: h.mime2DecodedSubject, mid: h.messageId, hdr: h }));
fnm.sleep = ms => new Promise(r => setTimeout(r, ms));
// A real compose window (headless windows are real windows): Thunderbird's
// own MsgComposeCommands.js fills Subject, References and Newsgroups for a
// followup from the parent article, exactly as for a person clicking
// Followup, and cmd_sendNow sends it.
fnm.compose = async (type, fields, originalURI, line) => {
  const params = Cc["@mozilla.org/messengercompose/composeparams;1"]
    .createInstance(Ci.nsIMsgComposeParams);
  params.composeFields = fields;
  params.type = type;
  params.format = Ci.nsIMsgCompFormat.PlainText;
  params.identity = fnm.identity;
  if (originalURI) { params.originalMsgURI = originalURI; }
  const before = new Set([...Services.wm.getEnumerator("msgcompose")]);
  MailServices.compose.OpenComposeWindowWithParams(null, params);
  let win = null;
  for (let i = 0; i < 240 && !win; i++) {
    await fnm.sleep(250);
    win = [...Services.wm.getEnumerator("msgcompose")].find(w => !before.has(w)) || null;
  }
  if (!win) { return {error: "no compose window opened"}; }
  for (let i = 0; i < 240; i++) {
    if (win.gMsgCompose && win.gMsgCompose.editor && win.document.readyState === "complete") { break; }
    await fnm.sleep(250);
  }
  await fnm.sleep(3000);
  const editor = win.GetCurrentEditor();
  editor.beginningOfDocument();
  editor.insertText(line + "\n");
  const composed = { subject: win.document.getElementById("msgSubject").value };
  let seen = null;
  const finished = new Promise(done => {
    win.gMsgCompose.addMsgSendListener({
      onStartSending() {}, onProgress() {}, onStatus() {}, onGetDraftFolderURI() {},
      onSendNotPerformed(mid, status) { seen = {mid, status, sent: false}; done(); },
      onTransportSecurityError() {},
      onStopSending(mid, status) { seen = {mid, status, sent: Components.isSuccessCode(status)}; done(); },
    });
  });
  win.goDoCommand("cmd_sendNow");
  await Promise.race([finished, fnm.sleep(120000)]);
  await fnm.sleep(1500);
  const fields2 = win.gMsgCompose ? win.gMsgCompose.compFields : null;
  return Object.assign(composed, seen || {sent: null}, fields2 ? {
    newsgroups: fields2.newsgroups, references: fields2.references,
    messageId: fields2.messageId } : {}, {windowClosed: win.closed});
};
resolve({ca: ca ? ca.subjectName : null, signons: [...signons], server: server.serverURI});
"""

READ_JS = r"""
const fnm = window.fnm;
fnm.mark("read");
const status = await fnm.fetch();
const list = fnm.headers();
if (!list.length) { resolve({status, count: 0}); return; }
const first = list[0];
const uri = fnm.folder.QueryInterface(Ci.nsIMsgFolder).getUriForMsg(first.hdr);
const { MailServices } = ChromeUtils.importESModule("resource:///modules/MailServices.sys.mjs");
const service = MailServices.messageServiceFromURI(uri);
const text = await new Promise(done => {
  let data = "";
  const sis = Cc["@mozilla.org/scriptableinputstream;1"].createInstance(Ci.nsIScriptableInputStream);
  service.streamMessage(uri, {
    QueryInterface: ChromeUtils.generateQI(["nsIStreamListener"]),
    onStartRequest() {},
    onDataAvailable(request, stream, offset, count) { sis.init(stream); data += sis.read(count); },
    onStopRequest(request, st) { done(data); },
  }, null, null, false, "", false);
});
fnm.parentURI = uri;
fnm.parentSubject = first.subject;
resolve({status, count: list.length, subject: first.subject, mid: first.mid,
         octets: text.length, head: text.split("\r\n").slice(0, 3)});
"""

REPLY_JS = r"""
const fnm = window.fnm;
fnm.mark("reply");
const fields = Cc["@mozilla.org/messengercompose/composefields;1"]
  .createInstance(Ci.nsIMsgCompFields);
const result = await fnm.compose(Ci.nsIMsgCompType.ReplyToGroup, fields, fnm.parentURI,
                                 "a line from Thunderbird in the v0 matrix");
resolve(result);
"""

POST_JS = r"""
const [subject] = arguments;
const fnm = window.fnm;
fnm.mark("post");
const fields = Cc["@mozilla.org/messengercompose/composefields;1"]
  .createInstance(Ci.nsIMsgCompFields);
fields.newsgroups = fnm.group;
fields.subject = subject;
const result = await fnm.compose(Ci.nsIMsgCompType.New, fields, null,
                                 "a new article from Thunderbird in the v0 matrix");
resolve(result);
"""

CANCEL_JS = r"""
const [subject] = arguments;
const fnm = window.fnm;
fnm.mark("cancel-fetch");
await fnm.fetch();
const own = fnm.headers().filter(h => h.subject === subject);
if (!own.length) { resolve({found: false, subjects: fnm.headers().map(h => h.subject)}); return; }
fnm.mark("cancel");
const target = own[own.length - 1];
const from = fnm.wire.length;
const listener = { OnStartRunningUrl() {}, OnStopRunningUrl(url, status) { fnm.cancelStatus = status; } };
// The signature mailCommon.js's cmd_cancel uses: (header, urlListener, msgWindow).
fnm.folder.cancelMessage(target.hdr, listener, fnm.msgWindow);
const start = Date.now();
const settled = () => {
  const tail = fnm.wire.slice(from).map(w => w[2]);
  const post = tail.indexOf("C: POST");
  return post >= 0 && tail.slice(post + 1).some(t => /^S: [0-9]{3}/.test(t) && !/^S: 340/.test(t));
};
while (Date.now() - start < 60000 && !settled()) {
  await new Promise(r => setTimeout(r, 500));
}
const parent = fnm.parentSubject || "";
// Thunderbird stores a followup's subject without "Re: " and sets HasRe.
const reply = fnm.headers().find(h => h.subject === parent &&
  (h.hdr.flags & Ci.nsMsgMessageFlags.HasRe)) || {};
resolve({found: true, mid: target.mid, key: target.key, reply_mid: reply.mid || "",
         cancelStatus: fnm.cancelStatus === undefined ? null : fnm.cancelStatus});
"""

DUMP_JS = r"""
const fnm = window.fnm;
resolve(fnm ? fnm.wire.concat(fnm.diag.map(d => [Date.now(), "diag", d.join(" ")])) : []);
"""


def pem_to_b64der(path):
    text = Path(path).read_text()
    body = re.search(r"-----BEGIN CERTIFICATE-----(.*?)-----END CERTIFICATE-----",
                     text, re.S).group(1)
    return "".join(body.split())


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


def wire_lines(entries):
    """Thunderbird's logger entries as nntp_wire_log.py lines, one per NNTP line."""
    out = []
    for stamp, level, text in entries:
        stamp = float(stamp) / 1000.0
        if level == "mark":
            out.append("%.3f 0 %s" % (stamp, text))
            continue
        for tag in ("S: ", "C: "):
            if text.startswith(tag):
                payload = text[len(tag):]
                parts = payload.split("\r\n")
                if parts and parts[-1] == "":
                    parts.pop()
                for part in parts:
                    out.append("%.3f 1 %s%s" % (stamp, tag, part[:300]))
                break
        else:
            out.append("%.3f 1 --- %s" % (stamp, text[:300]))
    return out


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--thunderbird", default="thunderbird")
    parser.add_argument("--work", required=True)
    parser.add_argument("--port", type=int, required=True, help="the node's TLS port")
    parser.add_argument("--cafile", required=True)
    parser.add_argument("--group", required=True)
    parser.add_argument("--user", required=True)
    parser.add_argument("--password-file", required=True)
    parser.add_argument("--email", required=True)
    parser.add_argument("--subject", default="Thunderbird in the v0 matrix")
    parser.add_argument("--log", required=True)
    args = parser.parse_args(argv)

    work = Path(args.work).resolve()
    profile = work / "tb-profile"
    if profile.exists():
        shutil.rmtree(profile)
    profile.mkdir(parents=True)
    mport = free_port()
    prefs = dict(PREFS, **{"marionette.port": mport})
    (profile / "user.js").write_text("".join(
        "user_pref({}, {});\n".format(json.dumps(k), json.dumps(v))
        for k, v in prefs.items()))
    password = Path(args.password_file).read_text().strip()
    result = {"client": "thunderbird", "actions": {}}
    version = subprocess.run([args.thunderbird, "--version"], capture_output=True,
                             text=True, timeout=120)
    result["version"] = (version.stdout or version.stderr).strip().splitlines()[-1:] or [""]
    result["version"] = result["version"][0]
    env = dict(os.environ, MOZ_HEADLESS="1")
    stderr = open(work / "thunderbird.stderr", "wb")
    proc = subprocess.Popen([args.thunderbird, "--headless", "--marionette", "--remote-allow-system-access",
                             "--no-remote",
                             "--profile", str(profile)], env=env,
                            stdout=stderr, stderr=subprocess.STDOUT)
    result["pid"] = proc.pid
    client = None
    try:
        client = Marionette(mport)
        client.call("WebDriver:NewSession",
                    {"capabilities": {"unhandledPromptBehavior": "ignore"}})
        client.call("Marionette:SetContext", {"value": "chrome"})
        result["setup"] = client.script(SETUP_JS, [args.port, pem_to_b64der(args.cafile),
                                                   args.group, args.user, password,
                                                   args.email])
        steps = (("read", READ_JS, []), ("reply", REPLY_JS, []),
                 ("post", POST_JS, [args.subject]), ("cancel", CANCEL_JS, [args.subject]))
        for name, source, extra in steps:
            if isinstance(result.get("setup"), dict) and result["setup"].get("error"):
                break
            try:
                result["actions"][name] = client.script(source, extra)
            except Exception as error:                  # noqa: BLE001
                result["actions"][name] = {"error": "{}: {}".format(
                    type(error).__name__, error)}
            time.sleep(1)
        wire = client.script(DUMP_JS)
    except Exception as error:                          # noqa: BLE001
        result["error"] = "{}: {}".format(type(error).__name__, error)
        wire = []
        try:
            if client:
                wire = client.script(DUMP_JS, timeout_ms=10000)
        except Exception:                               # noqa: BLE001
            pass
    finally:
        try:
            if client:
                client.call("Marionette:Quit", {"flags": ["eForceQuit"]})
        except Exception:                               # noqa: BLE001
            pass
        try:
            proc.wait(timeout=30)
        except subprocess.TimeoutExpired:
            proc.kill()
            proc.wait(timeout=30)
        stderr.close()
    diag = [one for one in (wire or []) if one[1] == "diag"]
    (work / "thunderbird-diag.log").write_text("".join(str(one[2]) + "\n" for one in diag))
    lines = wire_lines([one for one in (wire or []) if one[1] != "diag"])
    with open(args.log, "a", encoding="utf-8") as out:
        out.write("".join(line + "\n" for line in lines))
    result["wire_lines"] = len(lines)
    print(json.dumps(result, default=str))
    return 0 if not result.get("error") else 3


if __name__ == "__main__":
    sys.exit(main())
