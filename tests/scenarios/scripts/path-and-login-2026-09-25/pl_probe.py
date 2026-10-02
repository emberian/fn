"""path-and-login lane probes on a scratch node (hbox /tank/fn/scratch/path-login).

    python3 pl_probe.py PHASE     # PHASE: path | bound | open

Uses the reader spike's fn_web client (Signer = local hybrid-sign-carrier).
Prints one line per POST: label, reply word, detail, then HDR :fn-verified.
"""
import json, sys, time
sys.path.insert(0, "/tank/fn/scratch/spike-reader/client/tools")
from pathlib import Path
from types import SimpleNamespace
import fn_web, fn_client

S = Path("/tank/fn/scratch/path-login")
IMG, TREE, NODE = S / "img/build/fn-host-developer", S / "img", S / "node"
args = SimpleNamespace(host="127.0.0.1", port=11929, timeout=30.0, plain=False,
                       cafile=str(NODE / "cert.pem"))
PW = {"ember": "reader-spike-ember", "guest": "reader-spike-guest"}
TAG = time.strftime("%H%M%S")


def backend(login, keys=None):
    signer = fn_web.Signer(NODE / "keys" / keys, IMG, TREE) if keys else None
    return fn_web.Backend(args, login, PW[login], "%s <%s@example.org>" % (login, login), signer)


def verdict(b, msgid):
    def q(c):
        return c.cmd("HDR :fn-verified " + msgid, multiline=True)
    try:
        return b.using(q)
    except Exception as exc:  # report, do not hide
        return ("error", str(exc))


def post_lines(label, b, lines, msgid):
    r = b.post("fn.test", tuple(lines), msgid)
    print(json.dumps({"label": label, "word": r.word, "detail": r.detail,
                      "msgid": msgid, "verified": verdict(b, msgid)}), flush=True)
    return r


def raw(label, b, headers, body="raw probe"):
    msgid = "<pl-%s-%s@example.org>" % (label, TAG)
    lines = headers + ["From: ember <ember@example.org>", "Newsgroups: fn.test",
                       "Subject: " + label, "Message-ID: " + msgid, "", body]
    return post_lines(label, b, lines, msgid)


def signed(label, b):
    lines, msgid = b.prepare("fn.test", label, "", "", "signed " + label, True)
    return post_lines(label, b, lines, msgid)


def unsigned(label, b):
    lines, msgid = b.prepare("fn.test", label, "", "", "unsigned " + label, False)
    return post_lines(label, b, lines, msgid)


phase = sys.argv[1]
if phase == "path":
    b = backend("ember")
    date = "Date: Fri, 25 Sep 2026 10:00:00 +0000"
    mid = "<pl-resend-%s@example.org>" % TAG
    base = ["Path: not-for-mail", "From: ember <ember@example.org>", "Newsgroups: fn.test",
            "Subject: resend with a supplied Path", date, "Message-ID: " + mid, "", "body"]
    post_lines("P1-supplied-path", b, base, mid)
    time.sleep(1.5)
    post_lines("P2-exact-resend", b, base, mid)
    changed = ["Path: example.org!elsewhere"] + base[1:]
    post_lines("P3-changed-path", b, changed, mid)
    # A Date-less resend two seconds later: Injection-Date moves, source is one.
    mid2 = "<pl-dateless-%s@example.org>" % TAG
    dl = ["Path: not-for-mail", "From: ember <ember@example.org>", "Newsgroups: fn.test",
          "Subject: dateless resend", "Message-ID: " + mid2, "", "body"]
    post_lines("P4-dateless", b, dl, mid2)
    time.sleep(2.2)
    post_lines("P5-dateless-resend", b, dl, mid2)
    raw("P6-malformed", b, ["Path: a b"])
    raw("P7-duplicate", b, ["Path: a", "Path: b"])
    raw("P8-posted", b, ["Path: x.example!.POSTED!not-for-mail"])
    raw("P9-xref", b, ["Path: not-for-mail", "Xref: h fn.test:1"])
    raw("P10-leading-wsp", b, ["Path:  not-for-mail"])
    signed_b = backend("ember", "ember")
    lines, msgid = signed_b.prepare("fn.test", "signed with a supplied Path", "", "",
                                    "signed body", True)
    post_lines("P11-signed-with-path", signed_b, ["Path: not-for-mail"] + lines, msgid)
elif phase == "bound":
    signed("B1-ember-signs-as-ember", backend("ember", "ember"))
    signed("B2-ember-signs-as-guest", backend("ember", "guest"))
    unsigned("B3-ember-unsigned", backend("ember"))
    unsigned("B4-guest-unsigned", backend("guest"))
    signed("B5-guest-signs-as-guest", backend("guest", "guest"))
elif phase == "open":
    signed("O1-ember-signs-as-guest", backend("ember", "guest"))
    unsigned("O2-ember-unsigned", backend("ember"))
