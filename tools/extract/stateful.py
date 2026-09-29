#!/usr/bin/env python3
"""tools/extract/stateful.py -- the extraction's STATEFUL differential (lane
extract-writable, E1): the writable store verbs through the SBCL developer
image and through the extracted program, step for step, on twin stores.

    stateful.py IMAGE PROGRAM OUT [--only CASE ...]

Each case starts from two byte-identical copies of one freshly initialized
store (the image's `store ROOT init'), A for the image and B for the program,
and runs the same steps on both: `store ROOT post|recover|node-secret ...'
with the same arguments, the same payload files and the same recorded
environment observations (FN_NATIVE_TEST_CLOCK: the prepare's clock reading;
FN_NATIVE_TEST_ENTROPY: the node secret's CSPRNG draws), and the same
developer fault selectors (FN_NATIVE_POST_FAULT, FN_NATIVE_RECOVERY_FAULT,
FN_NATIVE_LOG_FAULT, the positional FAULT argument).  After every step it
compares, and any difference fails the case:
  * the outcome: exit status (a SIGKILL cut is status -9 on both), standard
    output and standard error, with each store's root path written as ROOT;
  * the durable effects: every file under the root -- path, type, mode, size
    and content digest -- and every directory; a name under staging/ or keys/
    that carries a process id or random suffix (a stage the step left behind)
    is compared by content with the suffix masked;
  * the subsequent state: a read session over the store after the step (the
    image's `--fn model' and the program's `model', read-only), byte for byte,
    when the store opens.
Steps may also mutate both trees identically between runs (damage a byte, a
mode, a staging orphan): recorded as `mutate' steps.

Fail closed: the manifest of cases and steps (OUT/manifest.json) is written
first; the report (OUT/stateful.json) lists every step with its verdict; the
run is PASS only when every step of every case ran once and agreed, and the
cases covered the classes the gate requires (CLASSES below).  Prints
`stateful: PASS' or `stateful: FAIL CASE STEP: REASON'; exits 0 only on PASS.
"""
import hashlib
import json
import os
import re
import shutil
import signal
import stat
import subprocess
import sys
from pathlib import Path

X = Path(__file__).resolve().parent
CLOCK = "73000:1759000000:250000"
ENTROPY = "17"
TIMEOUT = 600

# The classes of behaviour the gate requires the cases to cover (the brief:
# posts, page faults, interrupted updates, malformed input, guard failures,
# key changes, failed writes, restart, late completion).
CLASSES = ("post", "page-fault", "interrupted", "malformed", "guard", "key-change",
           "failed-write", "restart", "late-completion", "recover-cut", "damage")

READ = (b"CAPABILITIES\r\nMODE READER\r\nLIST\r\nGROUP fn.test\r\nSTAT\r\nHEAD\r\nBODY\r\n"
        b"ARTICLE 1\r\nARTICLE 2\r\nNEXT\r\nOVER 1-9\r\nHDR Subject 1-9\r\nLISTGROUP fn.test\r\n"
        b"GROUP fn.letters\r\nARTICLE 1\r\nARTICLE 3\r\nARTICLE <big@x.invalid>\r\nNEWNEWS * 20000101 000000\r\nQUIT\r\n")


def article(n, size=0, group="fn.test", msgid=None):
    msgid = msgid or "<a%d@x.invalid>" % n
    body = b"line %d\r\n" % n + (b".dot-stuffed\r\n" if n % 2 else b"") + b"y" * size
    return (b"From: poster@x.invalid\r\nNewsgroups: %s\r\nSubject: article %d\r\n"
            b"Message-ID: %s\r\n\r\n%s\r\n" % (group.encode(), n, msgid.encode(), body))


def post(n, group="fn.test", payload=None, msgid=None, charge="-", fault="-", env=None, groups=None):
    """A post step: (argv-after-ROOT, payload name and bytes, env)."""
    msgid = msgid or "<a%d@x.invalid>" % n
    name = payload or "p%d" % n
    return {"do": "run", "words": ["post", msgid, "@" + name, charge, fault] + (groups or [group]),
            "payloads": {name: article(n, group=group, msgid=msgid)} if payload is None else {},
            "env": env or {}}


def run(words, env=None, payloads=None):
    return {"do": "run", "words": words, "env": env or {}, "payloads": payloads or {}}


def recover(env=None):
    return run(["recover"], env)


def mutate(kind, **kw):
    d = {"do": "mutate", "kind": kind}
    d.update(kw)
    return d


POST_CUTS = ("frontier-reserved", "record-completing", "finish-consumed", "finish-durable",
             "log-written", "log-fenced")
RECOVERY_CUTS = ("recover-replayed", "recover-barrier-1", "recover-barrier-2", "recover-barrier-3")
LOG_CUTS = ("log-written", "log-fenced", "log-truncated", "log-recovered", "log-extended", "log-extent-fenced")


def cases():
    c = {}
    three = [post(1), post(2, group="fn.letters"), post(3, groups=["fn.test", "fn.letters"])]
    c["posts"] = (("post", "restart"), three + [post(1), post(1, payload="p2"), recover(), post(4)])
    c["large-post"] = (("post", "page-fault"),
                       [dict(post(9), payloads={"big": article(9, size=300000, msgid="<big@x.invalid>")},
                             words=["post", "<big@x.invalid>", "@big", "-", "-", "fn.letters"]),
                        post(10), recover()])
    c["malformed"] = (("malformed",), [
        post(1, msgid="not-a-message-id"),
        post(2, group="no.such.group"),
        post(3, charge="12x"), post(4, charge=""), post(5, charge="0"), post(6, charge="-7"),
        post(7, charge=" 42 "),
        run(["post", "<a8@x.invalid>", "@missing", "-", "-", "fn.test"]),
        run(["post", "<a9@x.invalid>"]),
        run(["recover", "--repair"]),
        run(["node-secret", "frobnicate"]),
        post(11, fault="nosuchfault"),
        post(12, env={"FN_NATIVE_POST_FAULT": "nosuchcut:kill"}),
        post(13, env={"FN_NATIVE_POST_FAULT": "log-written:explode"}),
        post(14, env={"FN_NATIVE_POST_FAULT": "log-written"}),
        post(15, env={"FN_NATIVE_POST_FAULT": "log-written:eio", "FN_NATIVE_RECOVERY_FAULT": "recover-replayed:eio"}),
        post(16)])
    c["guard"] = (("guard",), [post(1, msgid="<\u00e9t\u00e9@x.invalid>"), post(2, msgid="<\u20ac@x.invalid>"),
                               post(3, charge="99999999999999999999999"), post(4)])
    for cut in POST_CUTS:
        for action in ("kill", "eio"):
            c["post-%s-%s" % (cut, action)] = (
                ("interrupted", "restart") + (("failed-write",) if action == "eio" else ())
                + (("late-completion",) if cut.startswith("finish") or cut == "log-fenced" else ()),
                [post(1), post(2, env={"FN_NATIVE_POST_FAULT": "%s:%s" % (cut, action)}), recover(), post(2), post(3)])
    c["post-prepublish-refuse"] = (("interrupted",), [post(1, env={"FN_NATIVE_POST_FAULT": "record-prepublish:refuse"}),
                                                      recover(), post(1)])
    for fault in ("postpublish", "recordbarrier"):
        c["post-inject-" + fault] = (("interrupted", "failed-write", "restart"),
                                     [post(1), post(2, fault=fault), recover(), post(3)])
    for cut in LOG_CUTS:
        steps = [post(1)]
        if cut in ("log-truncated", "log-recovered"):
            steps += [recover(env={"FN_NATIVE_LOG_FAULT": cut}), recover(), post(2)]
        elif cut.startswith("log-exten"):
            steps += [dict(post(2), payloads={"big": article(2, size=400000, msgid="<big@x.invalid>")},
                           words=["post", "<big@x.invalid>", "@big", "-", "-", "fn.test"],
                           env={"FN_NATIVE_LOG_FAULT": cut}), recover(), post(3)]
        else:
            steps += [post(2, env={"FN_NATIVE_LOG_FAULT": cut}), recover(), post(3)]
        c["log-cut-" + cut] = (("interrupted", "restart", "late-completion"), steps)
    for cut in RECOVERY_CUTS:
        for action in ("kill", "eio"):
            c["recover-%s-%s" % (cut, action)] = (("recover-cut", "restart"),
                                                  [post(1), recover(env={"FN_NATIVE_RECOVERY_FAULT": "%s:%s" % (cut, action)}),
                                                   recover(), post(2)])
    c["recover-stage-unlinked"] = (("recover-cut", "restart"), [
        post(1), mutate("orphan", name=".init-4242-deadbeefdeadbeefdeadbeef", data="orphan"),
        mutate("orphan", name=".init-4243-feedfacefeedfacefeedface", data="orphan two"),
        recover(env={"FN_NATIVE_RECOVERY_FAULT": "recovery-stage-unlinked:kill"}), recover(),
        mutate("orphan", name=".init-4244-0123456789abcdef01234567", data="three"),
        recover(env={"FN_NATIVE_RECOVERY_FAULT": "recovery-stage-unlinked:eio"}), recover()])
    c["key-changes"] = (("key-change",), [
        run(["node-secret", "create"], {"FN_NATIVE_TEST_ENTROPY": "3"}),
        run(["node-secret", "rotate"]), run(["node-secret", "rotate", "operator@x.invalid"]),
        post(1), mutate("chmod", path="keys/node-secret.key", mode=0o644),
        run(["node-secret", "rotate"]), mutate("chmod", path="keys/node-secret.key", mode=0o600),
        mutate("write", path="keys/node-secret-9.key", data="not a key"),
        run(["node-secret", "rotate"]), recover(), post(2)])
    c["failed-writes"] = (("failed-write",), [
        post(1), mutate("chmod", path="journal/000001.log", mode=0o444), post(2), recover(),
        mutate("chmod", path="journal/000001.log", mode=0o644), post(2),
        mutate("chmod", path="writer.lock", mode=0o000), post(3),
        mutate("chmod", path="writer.lock", mode=0o600), post(3)])
    c["damage"] = (("damage", "page-fault"), [
        post(1), post(2), post(3), mutate("flip", path="journal/000001.log", at=0.5), recover(), post(4),
        mutate("flip", path="journal/000001.log", at=0.2), recover()])
    c["torn-tail"] = (("damage", "restart"), [
        post(1), post(2), mutate("tear", path="journal/000001.log"), recover(), post(3)])
    return c


# ---------------------------------------------------------------------------

def tree(root):
    """Every file and directory under ROOT: {relpath: (kind, mode, size, digest)}."""
    out = {}
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames.sort()
        for name in sorted(dirnames + filenames):
            p = Path(dirpath) / name
            rel = str(p.relative_to(root))
            rel = re.sub(r"\.init-\d+-[0-9a-f]+$", ".init-PID-RANDOM", rel)
            rel = re.sub(r"\.node-secret-\d+-[0-9a-f]+\.stage$", ".node-secret-PID-RANDOM.stage", rel)
            st = p.lstat()
            if stat.S_ISDIR(st.st_mode):
                out[rel] = ("dir", oct(st.st_mode & 0o7777))
            elif stat.S_ISLNK(st.st_mode):
                out[rel] = ("link", os.readlink(p))
            else:
                out[rel] = ("file", oct(st.st_mode & 0o7777), st.st_size,
                            hashlib.sha256(p.read_bytes()).hexdigest() if os.access(p, os.R_OK) else "unreadable")
    return out


def mask(text, root):
    return text.replace(str(root).encode(), b"ROOT")


class Case:
    def __init__(self, image, program, out, name, steps, base):
        self.image, self.program, self.out, self.name, self.steps = image, program, out, name, steps
        self.dir = out / name
        if self.dir.exists():
            shutil.rmtree(self.dir)
        self.dir.mkdir(parents=True)
        # the two roots have the same length, so no text shifts between them
        self.a, self.b = self.dir / "A" / "store", self.dir / "B" / "store"
        for r in (self.a, self.b):
            shutil.copytree(base, r, symlinks=True)
        (self.dir / "payloads").mkdir()

    def env(self, extra):
        e = dict(os.environ, ACL2_CUSTOMIZATION="NONE", FN_NATIVE_TEST_CLOCK=CLOCK, FN_NATIVE_TEST_ENTROPY=ENTROPY)
        for k in ("FN_NATIVE_POST_FAULT", "FN_NATIVE_RECOVERY_FAULT", "FN_NATIVE_LOG_FAULT"):
            e.pop(k, None)
        e.update(extra)
        return e

    def words(self, step, root):
        ws = ["store", str(root)]
        for w in step["words"]:
            ws.append(str(self.dir / "payloads" / w[1:]) if w.startswith("@") else w)
        return ws

    def program_argv(self):
        # the Common Lisp product takes the image's CLI (`--fn ...'); the
        # CHICKEN program its own verbs
        return [str(self.program), "--fn"] if CORE else [str(self.program)]

    def run_one(self, argv, env):
        try:
            p = subprocess.run(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env, timeout=TIMEOUT)
            return p.returncode, p.stdout, p.stderr
        except subprocess.TimeoutExpired:
            return "timeout", b"", b""

    def read_state(self, root, which):
        f = self.dir / "read.chunks"
        if not f.exists():
            f.write_bytes(b"%d\n" % len(READ) + READ)
        if which == "image":
            argv = [str(self.image), "--fn", "model", str(f), str(root)]
        else:
            argv = self.program_argv() + ["model", str(f), str(root)]
        rc, out, err = self.run_one(argv, self.env({}))
        return rc, mask(out, root), mask(err, root)

    def apply_mutation(self, m, root):
        p = root / m.get("path", "staging")
        k = m["kind"]
        if k == "orphan":
            (root / "staging" / m["name"]).write_bytes(m["data"].encode())
        elif k == "chmod":
            os.chmod(p, m["mode"])
        elif k == "write":
            p.write_bytes(m["data"].encode())
            os.chmod(p, 0o600)
        elif k in ("flip", "tear"):
            # the segment's written prefix: its octets up to the last nonzero
            # one (the preallocated extent reads zeros past the log's end)
            data = bytearray(p.read_bytes())
            last = len(data.rstrip(b"\0"))
            if k == "tear":
                data[last - 16:last] = bytes(16)   # the last entry's trailer: a torn append
            else:
                data[int(last * m["at"])] ^= 0x40  # a byte inside an earlier entry: damage
            p.write_bytes(bytes(data))

    def run(self):
        steps = []
        for i, step in enumerate(self.steps):
            label = "%02d %s" % (i, step["do"] if step["do"] == "mutate" else " ".join(step["words"])[:60])
            if step["do"] == "mutate":
                self.apply_mutation(step, self.a)
                self.apply_mutation(step, self.b)
                steps.append({"step": label, "verdict": "applied"})
                continue
            for name, data in step["payloads"].items():
                (self.dir / "payloads" / name).write_bytes(data)
            env = self.env(step["env"])
            ra = self.run_one([str(self.image), "--fn"] + self.words(step, self.a), env)
            rb = self.run_one(self.program_argv() + self.words(step, self.b), env)
            oa = (ra[0], mask(ra[1], self.a).decode(errors="replace"), mask(ra[2], self.a).decode(errors="replace"))
            ob = (rb[0], mask(rb[1], self.b).decode(errors="replace"), mask(rb[2], self.b).decode(errors="replace"))
            rec = {"step": label, "image": {"status": oa[0], "stdout": oa[1], "stderr": oa[2]},
                   "program": {"status": ob[0], "stdout": ob[1], "stderr": ob[2]}}
            steps.append(rec)
            if "timeout" in (oa[0], ob[0]):
                return self.fail(steps, label, "a side ran past %d s" % TIMEOUT)
            if oa != ob:
                what = "exit %s/%s" % (oa[0], ob[0]) if oa[0] != ob[0] else \
                       "stdout" if oa[1] != ob[1] else "stderr"
                return self.fail(steps, label, "outcome differs (%s)" % what)
            ta, tb = tree(self.a), tree(self.b)
            if ta != tb:
                diff = sorted(k for k in set(ta) | set(tb) if ta.get(k) != tb.get(k))
                rec["tree"] = {k: [ta.get(k), tb.get(k)] for k in diff[:10]}
                return self.fail(steps, label, "durable state differs at %s" % ", ".join(diff[:4]))
            sa, sb = self.read_state(self.a, "image"), self.read_state(self.b, "program")
            rec["read"] = {"image_status": sa[0], "program_status": sb[0], "bytes": len(sa[1])}
            if sa != sb:
                return self.fail(steps, label, "subsequent read differs (exit %s/%s)" % (sa[0], sb[0]))
            rec["verdict"] = "agree"
        return {"case": self.name, "verdict": "agree", "steps": steps}

    def fail(self, steps, label, reason):
        steps[-1]["verdict"] = "DIFFER"
        return {"case": self.name, "verdict": "DIFFER", "step": label, "reason": reason, "steps": steps}


CORE = False


def main(argv):
    global CORE
    only = []
    args = []
    it = iter(argv[1:])
    for a in it:
        if a == "--only":
            only.append(next(it))
        elif a == "--core":
            CORE = True
        else:
            args.append(a)
    image, program, out = Path(args[0]).resolve(), Path(args[1]).resolve(), Path(args[2]).resolve()
    out.mkdir(parents=True, exist_ok=True)
    all_cases = cases()
    chosen = {k: v for k, v in all_cases.items() if not only or k in only}
    manifest = {"cases": {k: {"classes": list(v[0]), "steps": len(v[1])} for k, v in chosen.items()},
                "clock": CLOCK, "entropy": ENTROPY}
    (out / "manifest.json").write_text(json.dumps(manifest, indent=1) + "\n")
    # one fresh store: the image's init, then the program opens it first so
    # both start from a recovered store
    base = out / "base" / "store"
    if base.parent.exists():
        shutil.rmtree(base.parent)
    base.parent.mkdir(parents=True)
    env = dict(os.environ, ACL2_CUSTOMIZATION="NONE", FN_NATIVE_TEST_CLOCK=CLOCK, FN_NATIVE_TEST_ENTROPY=ENTROPY)
    r = subprocess.run([str(image), "--fn", "store", str(base), "init", "fn.test", "fn.letters"],
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env)
    if r.returncode != 0:
        print("stateful: FAIL setup: init exited %d: %s" % (r.returncode, r.stderr.decode()[-300:]))
        return 1
    results = []
    for name, (classes, steps) in chosen.items():
        res = Case(image, program, out, name, steps, base).run()
        res["classes"] = list(classes)
        results.append(res)
        print("%-34s %s%s" % (name, res["verdict"], "" if res["verdict"] == "agree" else
                              "  at %s: %s" % (res["step"], res["reason"])), flush=True)
    bad = [r for r in results if r["verdict"] != "agree"]
    covered = sorted({c for r in results if r["verdict"] == "agree" for c in r["classes"]})
    missing = [c for c in CLASSES if c not in covered] if not only else []
    ran = sum(1 for r in results for s in r["steps"] if s.get("verdict") in ("agree", "applied"))
    want = sum(len(v[1]) for v in chosen.values())
    status = "PASS" if not bad and not missing and ran == want else "FAIL"
    (out / "stateful.json").write_text(json.dumps({"status": status, "covered": covered, "missing": missing,
                                                    "steps_run": ran, "steps_expected": want,
                                                    "results": results}, indent=1) + "\n")
    if status == "PASS":
        print("stateful: PASS %d cases, %d steps, classes %s" % (len(results), ran, ",".join(covered)))
        return 0
    if bad:
        print("stateful: FAIL %s %s: %s" % (bad[0]["case"], bad[0]["step"], bad[0]["reason"]))
    elif missing:
        print("stateful: FAIL classes not covered: %s" % ", ".join(missing))
    else:
        print("stateful: FAIL %d of %d steps ran" % (ran, want))
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
