#!/usr/bin/env python3
"""qual-e747dbcc manual web pass: a scratch node on the production image with
STARTTLS and [auth] required, then tools/fn_web.py as a separate process, driven
over HTTP like a browser. Every page is saved under OUT; only PIDs started here
are stopped."""
import http.client, os, re, socket, subprocess, sys, time
from html import unescape
from pathlib import Path
from urllib.parse import urlencode

S = Path("/tank/fn/scratch/qual-e747dbcc")
T = S / "tree"
I = Path("/tank/fn/gates/qual-e747dbcc-20260925/build/images/e747dbcc7f9f4ba6d86e0dc3ec8856a06f1994e6")
W = S / "web"
OUT = W / "pages"
OPENSSL = str(S / "bin" / "test-openssl")
USER, SECRET = "reader", "web-pass-e747dbcc"

def port():
    with socket.socket() as p:
        p.bind(("127.0.0.1", 0)); return p.getsockname()[1]

def log(*a):
    print(*a, flush=True)

subprocess.run(["rm", "-rf", str(W)], check=True)
OUT.mkdir(parents=True)
env = dict(os.environ, ACL2_CUSTOMIZATION="NONE", FN_ACL2="/tank/fn/toolchains/w28/acl2-literal-4g")
env.pop("ACL2_SYSTEM_BOOKS", None); env.pop("FN_HOST", None)
store, cert, key, auth, cfg = W / "store", W / "cert.pem", W / "key.pem", W / "credentials.toml", W / "fn.toml"
r = subprocess.run([str(I / "fn-host"), "--fn", "store", str(store), "init", "fn.agents"], cwd=T, env=env, capture_output=True)
log("store init rc", r.returncode)
subprocess.run([OPENSSL, "req", "-x509", "-newkey", "rsa:2048", "-keyout", str(key), "-out", str(cert),
                "-sha256", "-days", "1", "-nodes", "-subj", "/CN=localhost",
                "-addext", "subjectAltName=IP:127.0.0.1"], check=True, capture_output=True)
nport = port()
cfg.write_text('[store]\npath = "%s"\n\n[listener]\nhost = "127.0.0.1"\nport = %d\ntls_cert = "%s"\ntls_key = "%s"\n\n'
               '[auth]\nrequired = true\nprotected_only = true\npath = "%s"\n' % (store, nport, cert, key, auth))
r = subprocess.run([sys.executable, "bin/fn", "--config", str(cfg), "principal", "set-password", USER,
                    "--password", SECRET, "--posting"], cwd=T, env=env, capture_output=True)
log("set-password rc", r.returncode, r.stderr.decode()[-300:])
owner_err = open(W / "owner.err", "wb")
owner = subprocess.Popen([str(I / "fn-host"), "--fn", "operator", str(cfg), "run"], cwd=T, env=env,
                         stdout=subprocess.PIPE, stderr=owner_err)
while True:
    ann = owner.stdout.readline().decode().strip(); log("owner pid", owner.pid, "announce", ann)
    if ann.startswith("LISTENING") or not ann: break
cred = W / "cred"; cred.write_text("%s %s\n" % (USER, SECRET)); cred.chmod(0o600)
hport = port()
web_log = open(W / "fn_web.log", "wb")
web = subprocess.Popen([sys.executable, "tools/fn_web.py", "--node", "127.0.0.1:%d" % nport, "--tls-cert", str(cert),
                        "--credentials", str(cred), "--port", str(hport), "--marks", str(W / "marks.json"),
                        "--outbox", str(W / "outbox")],
                       cwd=T, env=dict(env, FN_CLIENT_FROM="Reader <reader@local.invalid>"),
                       stdout=web_log, stderr=subprocess.STDOUT)
log("fn_web pid", web.pid, "http", hport, "nntp", nport)
csrf = None

def req(method, path, fields=None, name=None):
    global csrf
    for _ in range(100):
        try:
            c = http.client.HTTPConnection("127.0.0.1", hport, timeout=60)
            headers, body = {}, None
            if method == "POST":
                headers = {"Content-Type": "application/x-www-form-urlencoded", "Origin": "http://127.0.0.1:%d" % hport}
                body = urlencode(dict({"csrf": csrf}, **fields))
            c.request(method, path, body=body, headers=headers)
            rep = c.getresponse(); ans = (rep.status, rep.getheader("Location"), rep.read().decode("utf-8")); c.close()
            break
        except ConnectionRefusedError:
            time.sleep(0.2)
    m = re.search(r"name='csrf' value='([^']+)'", ans[2])
    if m: csrf = unescape(m.group(1))
    if name:
        (OUT / (name + ".html")).write_text(ans[2])
    assert SECRET not in ans[2]
    if web.poll() is not None: raise SystemExit("fn_web exited %s" % web.returncode)
    return ans

def text(html):
    t = re.sub(r"<(script|style)[^>]*>.*?</\1>", "", html, flags=re.S)
    t = re.sub(r"<[^>]+>", " ", t); return re.sub(r"\s+", " ", unescape(t)).strip()

def post(subject, body, reply=None, name=None):
    form = req("GET", "/compose?group=fn.agents" + ("&reply=%d" % reply if reply else ""), name=name and name + "-compose")
    tok = unescape(re.search(r"name='submission_id' value='([^']+)'", form[2]).group(1))
    refs = unescape(re.search(r"name='references' value='([^']*)'", form[2]).group(1))
    ans = req("POST", "/post", {"submission_id": tok, "group": "fn.agents", "action": "post", "subject": subject,
                                "sender": "Reader <reader@local.invalid>", "references": refs, "body": body})
    log(name, "POST ->", ans[0], ans[1])
    res = req("GET", ans[1], name=name) if ans[0] == 303 else ans
    for _ in range(50):
        if "240" in res[2] and "pending" not in text(res[2]).lower()[:0]: break
        time.sleep(0.2); res = req("GET", ans[1], name=name)
    return res

try:
    home = req("GET", "/", name="01-groups-empty"); log("01 groups (empty):", home[0], text(home[2])[:600])
    p1 = post("qual root", "first article from the qualification web pass\n", name="02-post-root")
    log("02 result:", p1[0], text(p1[2])[:900])
    p2 = post("Re: qual root", "a reply in the thread\n", reply=1, name="03-post-reply")
    log("03 result:", p2[0], text(p2[2])[:900])
    p3 = post("second thread", "another root\n", name="04-post-second")
    log("04 result:", p3[0], text(p3[2])[:600])
    home = req("GET", "/", name="05-groups"); log("05 groups:", home[0], text(home[2])[:800])
    g = req("GET", "/g?name=fn.agents", name="06-thread"); log("06 group/thread:", g[0], text(g[2])[:1500])
    a = req("GET", "/a?group=fn.agents&number=1", name="07-article-1"); log("07 article 1:", a[0], text(a[2])[:1500])
    badges = re.findall(r"class='badge ([^']*)'[^>]*title='([^']*)'", a[2]) or re.findall(r"badge[^'\"]*", a[2])
    log("07 badges:", badges[:5])
    mk = req("POST", "/mark", {"group": "fn.agents", "through": "1"}); log("mark ->", mk[0], mk[1])
    home = req("GET", "/", name="08-groups-after-mark"); log("08 groups after mark through 1:", home[0], text(home[2])[:800])
    # the node's own LIST COUNTS for the same group, over TLS + login, via fn_client
    import ssl
    raw = socket.create_connection(("127.0.0.1", nport), 30); f = raw.makefile("rb")
    def cmd(sock, fh, line):
        sock.sendall(line.encode() + b"\r\n"); return fh.readline().decode().rstrip()
    log("nntp greeting", f.readline().decode().rstrip())
    log("STARTTLS", cmd(raw, f, "STARTTLS"))
    ctx = ssl.create_default_context(cafile=str(cert)); tls = ctx.wrap_socket(raw, server_hostname="127.0.0.1"); tf = tls.makefile("rb")
    log("AUTHINFO USER", cmd(tls, tf, "AUTHINFO USER " + USER)); log("AUTHINFO PASS", cmd(tls, tf, "AUTHINFO PASS " + SECRET))
    log("LIST COUNTS", cmd(tls, tf, "LIST COUNTS"))
    while True:
        l = tf.readline().decode().rstrip(); log("  |", l)
        if l == ".": break
    log("QUIT", cmd(tls, tf, "QUIT"))
finally:
    for p in (web, owner):
        p.terminate()
        try: p.wait(30)
        except subprocess.TimeoutExpired: p.kill(); p.wait()
    log("stopped web rc", web.returncode, "owner rc", owner.returncode)
