#!/usr/bin/env python3
"""tools/extract/gate.py TREE IMAGE -- the extraction differential's gate
(A-EXTRACT's qualification of one build, specs/failures.md); check.sh runs it.
The product under test is fn-core (tools/extract/core.sh: an SBCL core of ACL2's
own installed forms, no ACL2 resident); the reference is IMAGE, the developer
image.

Fail closed.  Every child process's exit status is checked here, one call at
a time (no shell pipeline, no reliance on `set -e'); every stage's output is
compared against the manifest of what it had to produce; an empty, truncated
or missing output, a case that ran twice or not at all, a missing completion
marker and zero executed cases each FAIL with a named reason.  Steps:
  1. core: tools/extract/core.sh (the export, X1/X2 and the SBCL build); its
     products must exist, the closure must have no gaps, and defs.lisp must be
     the file xt-verify-defs verified: its record, and the export and verify
     runs' completion evidence (image_run.py, one nonce, defs.lisp's SHA-256);
  1b. manifest: the frozen record of what was extracted (world digest, the
     core's products, the foreign libraries);
  1c. invariant-risk: no declared host entry that is not guard-verified
      carries ACL2's invariant-risk in core.json's world (its *1* would run
      every callee interpreted, guards checked: C's POST at 10.7 s); the
      shrink-only baseline is tools/invariant_risk_baseline.json;
  2. transcripts: every case transcripts.py lists (its manifest.json),
     through IMAGE's and fn-core's `--fn model', byte-identical;
  2b. rtc-exercise: the runtime contract's multi-instance exercise
     (`--fn rtc-exercise run 0..4', host/native/rtc-exercise.lisp): two
     interleaved connections over the executable layer and its array-backed
     pool; the image exits 0 (invariant, :out octets stable, no unmatched
     completion changed the state at any step), steps 10 and 12 discard
     stale completions, four injected host faults are reported by both
     sides (exit 4: :moved, :invp-violated, :moved, :moved), and fn-core's
     lines are the image's bytes;
  3. probes: the boundary probes through both sides, every probe identical;
  3b. obligations: X1's O2 and O3 (EXTRACTION-PROGRAM-20261007.md section 7) through
      both sides (obligations.py): every extracted global, every ACL2 state global
      the closure reads and every value core-world.lisp sets holds the image's
      value in fn-core before fn starts; every root has the image's entry-guard
      specification (fnn-entry-guard-spec, fnn-trailing-kind); exclusions are
      obligations.py's reviewed EXCLUDED list, each printed with its reason;
  4. store: a copy of a real format-9 store, rebound, read through both;
  5. stateful: the writable verbs (`store ROOT post|recover|node-secret')
     through IMAGE and fn-core on twin stores, step for step
     (stateful.py): outcomes, durable files and subsequent reads identical,
     every case of its manifest run once, every required class covered;
  5b. owner: actual barrier completion after the owner has told its poster
      uncertain; exact wire replies, durable reads and restart through the
      reference image and fn-core (owner.py);
  6. faults: the fault corpus through both sides, observation for observation
     (faults_diff.py): tests/fixtures/fuzz-nntp's reproducers, and the load
     fault corpus's traces when FN_EXTRACT_FAULT_TRACES names its directory.
There is no per-function differential step: the per-function evidence is X1
(xt-verify-defs: every emitted form EQUAL to what ACL2 installed) and X2 (no
undefined name), both inside core.sh.  The step this replaced generated
candidates from the retired extractor's IR (deleted, D63); `fn-core --xl-load' is a
developer-load hook, not a vector runner, so re-aiming it would need a new
candidate generator, not a re-target.
Writes TREE/build/extract/check/: the logs, status.json (RUNNING until the
verdict, then PASS or FAIL with the step, the reason and every child's exit
status) and extraction-manifest.json.  Prints `extract-check: PASS'
or `extract-check: FAIL at STEP: REASON'; exits 0 only on PASS.
"""
import collections
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path

X = Path(__file__).resolve().parent


class GateFail(Exception):
    def __init__(self, step, reason):
        super().__init__("%s: %s" % (step, reason))
        self.step, self.reason = step, reason


@dataclass
class Tools:
    """The external programs.  The command line builds these from the
    environment (FN_EXTRACT_ACL2, EXTRACT_STORE); the gate's own tests
    substitute stand-ins through this object, never through the command line."""
    acl2: list
    # the Common Lisp product's build (tools/extract/core.sh TREE): the SBCL
    # core without ACL2, the product under test
    core: list
    # the stateful differential's driver (tools/extract/stateful.py); the
    # gate's tests substitute a stand-in
    stateful: list = field(default_factory=lambda: ["python3", str(X / "stateful.py")])
    owner: list = field(default_factory=lambda: ["python3", str(X / "owner.py")])
    obligations: list = field(default_factory=lambda: ["python3", str(X / "obligations.py")])
    faults: list = field(default_factory=lambda: ["python3", str(X / "faults_diff.py")])
    invariant_risk: list = field(default_factory=lambda: ["python3", str(X.parent / "invariant_risk_check.py")])
    fault_traces: list = field(default_factory=list)
    store: str = "/tank/fn/scratch/fixtures/n1k-2k/store"
    source: str = None
    variant: str = "default"


def core_libraries(core_sh):
    """The libraries core.sh hands fn-core: each `export FN_*_LIBRARY=$LIB/NAME.so', as NAME."""
    names = re.findall(r"FN_[A-Z0-9_]+_LIBRARY=\$LIB/(libfn-[A-Za-z0-9-]+)\.so", Path(core_sh).read_text())
    if not names:
        raise SystemExit("gate: core.sh exports no FN_*_LIBRARY (%s)" % core_sh)
    return names


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def describe_status(rc):
    return "killed by signal %d" % -rc if rc < 0 else "exited %d" % rc


class Gate:
    def __init__(self, tree, image, tools):
        self.tree = Path(tree).resolve()
        self.image = Path(image).absolute()
        self.t = tools
        self.x = self.tree / "tools" / "extract"
        self.e = self.tree / "build" / "extract"
        self.c = self.e / "check"
        self.children = []
        self.step = "setup"
        self.env = dict(os.environ)
        self.env["FN_EXTRACT_VARIANT"] = tools.variant
        self.acl2_env = {k: v for k, v in self.env.items()}
        self.acl2_env["ACL2_CUSTOMIZATION"] = "NONE"

    # --- children ---------------------------------------------------------------
    def run(self, what, argv, stdout=None, stderr=None, stdin=None, cwd=None, env=None, append=False):
        """Run one child; record and return its exit status.  STDOUT/STDERR
        name files (STDERR "stdout" merges); nothing is inherited silently."""
        mode = "ab" if append else "wb"
        out = open(stdout, mode) if stdout else subprocess.DEVNULL
        if stderr == "stdout":
            err = subprocess.STDOUT
        else:
            err = open(stderr, mode) if stderr else subprocess.DEVNULL
        inp = open(stdin, "rb") if stdin else subprocess.DEVNULL
        t0 = time.time()
        try:
            rc = subprocess.run([str(a) for a in argv], stdout=out, stderr=err, stdin=inp,
                                cwd=str(cwd or self.tree), env=env or self.env, check=False).returncode
        except OSError as ex:
            rc = 127
            if stdout:
                out.write(("cannot run %s: %s\n" % (argv[0], ex)).encode())
        finally:
            for h in (out, err, inp):
                if hasattr(h, "close"):
                    h.close()
        self.children.append({"step": self.step, "what": what, "argv": [str(a) for a in argv][:12],
                              "status": rc, "seconds": round(time.time() - t0, 1)})
        return rc

    def need(self, what, argv, log=None, **kw):
        rc = self.run(what, argv, **kw)
        if rc != 0:
            self.fail("%s %s%s" % (what, describe_status(rc), self.tail(log)))
        return rc

    def fail(self, reason):
        raise GateFail(self.step, reason)

    @staticmethod
    def tail(path, n=3):
        if not path or not os.path.exists(path):
            return ""
        lines = Path(path).read_text(errors="replace").strip().splitlines()[-n:]
        return " (%s: %s)" % (path, " | ".join(l.strip() for l in lines)) if lines else " (%s is empty)" % path

    def nonempty(self, path, what):
        if not os.path.isfile(path):
            self.fail("%s: %s was not written" % (what, path))
        if os.path.getsize(path) == 0:
            self.fail("%s: %s is empty" % (what, path))

    def load_json(self, path, what):
        self.nonempty(path, what)
        try:
            return json.loads(Path(path).read_text())
        except ValueError as ex:
            self.fail("%s: %s does not parse (%s)" % (what, path, ex))

    def write_status(self, status, **more):
        doc = {"status": status, "tree": str(self.tree), "image": str(self.image),
               "source": self.t.source, "children": self.children}
        doc.update(more)
        tmp = self.c / "status.json.tmp"
        tmp.write_text(json.dumps(doc, indent=1) + "\n")
        os.replace(tmp, self.c / "status.json")

    # --- the steps ----------------------------------------------------------------
    def core(self):
        """The Common Lisp product (A-TARGET-COMPILER): fn's functions and
        host/native in a bare SBCL core, built from the same world."""
        self.step = "core"
        k = self.tree / "build" / "core"
        for stale in ("fn-core", "export.done", "verify.done"):
            (k / stale).unlink(missing_ok=True)
        log = self.c / "core-build.log"
        env = dict(self.env, FN_CORE_NAME="fn-core", FN_NATIVE_PROFILE="developer",
                   FN_CORE_OUT=str(k), FN_EXTRACT_IMAGE=str(self.image))
        self.need("core.sh", self.t.core, stdout=log, stderr="stdout", log=log, env=env)
        for name in ("tokens.lsp", "core.json", "defs.lisp", "manifest.tsv", "runtime.tsv", "packages.lisp",
                     "core-world.lisp", "host-block.lisp", "defs.lisp.verified-sha256", "fn-core.core"):
            self.nonempty(k / name, "core")
        gaps = k / "gaps.txt"
        if gaps.exists() and gaps.read_text().strip():
            self.fail("the closure has names nothing provides (%s)" % gaps)
        if (k / "defs.lisp.verified-sha256").read_text().strip() != sha256_file(k / "defs.lisp"):
            self.fail("defs.lisp is not the file xt-verify-defs verified")
        # O1's evidence: both world runs completed in this invocation over these defs.lisp bytes
        evidence = {}
        for phase in ("EXPORT", "VERIFY"):
            f = k / ("%s.done" % phase.lower())
            self.nonempty(f, "core")
            words = f.read_text().split()
            if len(words) != 3 or words[0] != "XT-%s-DONE" % phase:
                self.fail("%s is not completion evidence: %r" % (f, f.read_text()[:80]))
            evidence[phase] = words
        if evidence["EXPORT"][1] != evidence["VERIFY"][1]:
            self.fail("the export and verify evidence carry different nonces (not one core.sh run)")
        if {evidence["EXPORT"][2], evidence["VERIFY"][2]} != {sha256_file(k / "defs.lisp")}:
            self.fail("the completion evidence names other defs.lisp bytes")
        units = [l for l in (k / "manifest.tsv").read_text().splitlines() if l.strip() and not l.startswith("#")]
        if not units:
            self.fail("manifest.tsv lists no units")
        exe = k / "fn-core"
        if not (exe.is_file() and os.access(exe, os.X_OK)):
            self.fail("no executable %s" % exe)
        self.core_exe = exe
        self.core_units = len(units)
        print("core: %d units, %d runtime names" % (
            len(units), len([l for l in (k / "runtime.tsv").read_text().splitlines() if l.strip()])))

    def core_same(self, what, argv, expected, stderr_path):
        """Run the core; its stdout must be EXPECTED's bytes and its status 0."""
        out = Path(str(stderr_path).replace(".err", ""))
        rc = self.run("core " + what, argv, stdout=out, stderr=stderr_path, env=self.acl2_env)
        if rc != 0:
            self.fail("%s: the core %s%s" % (what, describe_status(rc), self.tail(stderr_path, 1)))
        if out.read_bytes() != Path(expected).read_bytes():
            self.fail("%s: the core's reply differs from the image's (%s against %s)" % (what, out, expected))

    def transcripts(self):
        self.step = "transcripts"
        d = self.c / "transcripts"
        self.need("transcripts.py", ["python3", self.x / "transcripts.py", d],
                  stdout=self.c / "transcripts-gen.log", stderr="stdout", log=self.c / "transcripts-gen.log")
        man = self.load_json(d / "manifest.json", "transcripts")
        expected = man.get("cases") or []
        if not expected:
            self.fail("the transcript manifest lists no cases")
        present = sorted(p.name[:-len(".chunks")] for p in d.glob("*.chunks"))
        if present != sorted(expected):
            self.fail("chunk files %s are not the manifest's cases %s" % (present, sorted(expected)))
        for n in expected:
            self.nonempty(d / (n + ".chunks"), "transcripts")
        for n in expected:
            a = self.c / "cmp" / ("%s.sbcl" % n)
            a.parent.mkdir(exist_ok=True)
            rc = self.run("image transcript " + n, [self.image, "--fn", "model", d / (n + ".chunks"), "-"],
                          stdout=a, stderr=str(a) + ".err", env=self.acl2_env)
            if rc != 0:
                self.fail("%s: the image %s%s" % (n, describe_status(rc), self.tail(str(a) + ".err", 1)))
            self.nonempty(a, "transcripts")
            self.core_same("transcript " + n, [self.core_exe, "--fn", "model", d / (n + ".chunks"), "-"],
                           a, self.c / "cmp" / ("%s.core.err" % n))
        print("transcripts: %d of %d identical (image, core)" % (len(expected), len(expected)))

    def rtc_exercise(self):
        """The runtime contract's multi-instance exercise: two interleaved
        connections over the executable layer and its array-backed pool
        (host/native/rtc-exercise.lisp, books/runtime-contract-echo.lisp
        fn-rce-exercise).  Variant 0: the image exits 0 (every step kept the
        invariant and the outstanding :out octets, no unmatched completion
        changed the state), steps 10 and 12 discard stale completions, and
        the core's lines are the image's bytes.  Variants 1-4 inject a host
        fault (a write into an :out-leased buffer, that buffer freed under its
        lease, the write followed by the send's own completion, the lease
        redirected to another instance): both sides exit 4 (fault) with the
        step reported :moved, :invp-violated, :moved, :moved, line for line
        identical."""
        self.step = "rtc-exercise"
        d = self.c / "cmp"
        d.mkdir(exist_ok=True)
        a = d / "rtc-exercise.sbcl"
        rc = self.run("image rtc-exercise", [self.image, "--fn", "rtc-exercise", "run", "0"],
                      stdout=a, stderr=str(a) + ".err", env=self.acl2_env)
        if rc != 0:
            self.fail("rtc-exercise: the image %s%s" % (describe_status(rc), self.tail(str(a) + ".err", 1)))
        lines = a.read_text().splitlines()
        if len(lines) != 17:
            self.fail("rtc-exercise: %d observation lines, not 17" % len(lines))
        discarded = [l.split()[0].lstrip("(") for l in lines if l.endswith(":discarded)")]
        if discarded != ["10", "12"]:
            self.fail("rtc-exercise: discarded steps %s, not [10, 12]" % discarded)
        self.core_same("rtc-exercise", [self.core_exe, "--fn", "rtc-exercise", "run", "0"],
                       a, d / "rtc-exercise.core.err")
        for variant, mark in (("1", ":moved"), ("2", ":invp-violated"), ("3", ":moved"), ("4", ":moved")):
            f = d / ("rtc-exercise-fault-%s.sbcl" % variant)
            rc = self.run("image rtc-exercise fault " + variant,
                          [self.image, "--fn", "rtc-exercise", "run", variant],
                          stdout=f, stderr=str(f) + ".err", env=self.acl2_env)
            if rc != 4:
                self.fail("rtc-exercise fault %s: the image %s, not exit 4" % (variant, describe_status(rc)))
            last = f.read_text().splitlines()[-1:]
            if not last or mark not in last[0]:
                self.fail("rtc-exercise fault %s: the injected fault is not reported %s" % (variant, mark))
            g = d / ("rtc-exercise-fault-%s.core" % variant)
            rc = self.run("core rtc-exercise fault " + variant,
                          [self.core_exe, "--fn", "rtc-exercise", "run", variant],
                          stdout=g, stderr=str(g) + ".err", env=self.acl2_env)
            if rc != 4:
                self.fail("rtc-exercise fault %s: the core %s, not exit 4" % (variant, describe_status(rc)))
            if g.read_bytes() != f.read_bytes():
                self.fail("rtc-exercise fault %s: the core's reply differs from the image's (%s against %s)"
                          % (variant, g, f))
        print("rtc-exercise: 17 steps, invariant held, stale completions 10 and 12 discarded; "
              "the four injected faults reported; core identical")

    def probes(self):
        self.step = "probes"
        c = self.c
        self.need("probes.py run-sbcl", ["python3", self.x / "probes.py", "run-sbcl", self.image, c / "probes.sbcl"],
                  stdout=c / "probes-sbcl.log", stderr="stdout", log=c / "probes-sbcl.log")
        self.nonempty(c / "probes.sbcl", "probes")
        self.need("probes.py run-core", ["python3", self.x / "probes.py", "run-core", self.core_exe, c / "probes.core"],
                  stdout=c / "probes-core.log", stderr="stdout", log=c / "probes-core.log")
        self.nonempty(c / "probes.core", "probes")
        self.need("probes.py compare core", ["python3", self.x / "probes.py", "compare", c / "probes.sbcl", c / "probes.core"],
                  stdout=c / "probes-core-cmp.log", stderr="stdout", log=c / "probes-core-cmp.log")
        print("core " + Path(c / "probes-core-cmp.log").read_text().strip().splitlines()[-1])

    STORE_READ = (b"CAPABILITIES\r\nMODE READER\r\nLIST\r\nLIST ACTIVE\r\nGROUP fn.test\r\nSTAT\r\nHEAD\r\nBODY\r\n"
                  b"ARTICLE 1\r\nARTICLE 2\r\nNEXT\r\nLAST\r\nOVER 1-3\r\nHDR Subject 1-3\r\nLISTGROUP fn.test 1-5\r\n"
                  b"ARTICLE 999\r\nARTICLE <nonexistent@example.invalid>\r\nNEWNEWS * 20000101 000000\r\nQUIT\r\n")

    def obligations(self):
        """O2 and O3 through both sides: the same forms, item for item (obligations.py)."""
        self.step = "obligations"
        d = self.c / "obligations"
        k = self.tree / "build" / "core"
        self.need("obligations.py forms", self.t.obligations + ["forms", d, k],
                  stdout=self.c / "obligations-forms.log", stderr="stdout", log=self.c / "obligations-forms.log")
        self.nonempty(d / "obligations.lisp", "obligations")
        self.need("obligations.py run-image", self.t.obligations + ["run-image", self.image, d],
                  stdout=self.c / "obligations-image.log", stderr="stdout", log=self.c / "obligations-image.log",
                  env=self.acl2_env)
        self.nonempty(d / "image.out", "obligations")
        self.need("obligations.py run-core", self.t.obligations + ["run-core", self.core_exe, d],
                  stdout=self.c / "obligations-core.log", stderr="stdout", log=self.c / "obligations-core.log",
                  env=self.acl2_env)
        self.nonempty(d / "core.out", "obligations")
        log = self.c / "obligations-compare.log"
        rc = self.run("obligations.py compare", self.t.obligations + ["compare", d], stdout=log, stderr="stdout")
        last = [l for l in log.read_text().splitlines() if l.startswith("obligations: ")]
        if rc != 0 or not last:
            first = [l for l in log.read_text().splitlines() if l.startswith("DIFFER ")][:3]
            self.fail("O2/O3 differ: %s%s" % ("; ".join(first) or describe_status(rc), self.tail(log, 1)))
        print(last[-1])

    def faults(self):
        """The fault corpus through both sides (faults_diff.py): every case runs, every case agrees."""
        self.step = "faults"
        d = self.c / "faults"
        log = self.c / "faults.log"
        argv = self.t.faults + [self.image, self.core_exe, d]
        for t in self.t.fault_traces:
            argv += ["--traces", t]
        rc = self.run("faults_diff.py", argv, stdout=log, stderr="stdout", env=self.acl2_env)
        doc = self.load_json(d / "faults.json", "faults")
        results = doc.get("results") or []
        if not results:
            self.fail("the fault differential ran no case")
        bad = [r for r in results if r.get("verdict") != "agree"]
        if bad:
            self.fail("%d of %d fault cases did not agree; first: %s %s%s" % (
                len(bad), len(results), bad[0].get("verdict"), bad[0].get("case"),
                (" " + bad[0]["error"]) if bad[0].get("error") else ""))
        if rc != 0:
            self.fail("faults_diff.py %s%s" % (describe_status(rc), self.tail(log, 1)))
        print("faults: %d cases agree" % len(results))

    def store(self):
        self.step = "store"
        c = self.c
        src = Path(self.t.store)
        if not src.is_dir():
            self.fail("no store at %s (EXTRACT_STORE)" % src)
        dst = c / "store"
        if dst.exists():
            shutil.rmtree(dst)
        self.need("cp -a store", ["cp", "-a", src, dst], stdout=c / "store-copy.log", stderr="stdout",
                  log=c / "store-copy.log")
        lock = dst / "writer.lock"
        lock.touch()
        lock.chmod(0o600)
        self.need("image rebind-filesystem", [self.image, "--fn", "store", dst, "rebind-filesystem"],
                  stdout=c / "rebind.log", stderr="stdout", log=c / "rebind.log", env=self.acl2_env)
        (c / "store-read.chunks").write_bytes(b"%d\n" % len(self.STORE_READ) + self.STORE_READ)
        for t in ("store-read", "reader-commands", "session-200"):
            f = c / (t + ".chunks")
            if not f.exists():
                f = c / "transcripts" / (t + ".chunks")
            self.nonempty(f, "store")
            a = c / ("%s.store.sbcl" % t)
            s1 = self.run("image model " + t, [self.image, "--fn", "model", f, dst], stdout=a,
                          stderr=str(a) + ".err", env=self.acl2_env)
            if s1 != 0:
                self.fail("%s: the image %s%s" % (t, describe_status(s1), self.tail(str(a) + ".err", 1)))
            self.nonempty(a, "store")
            self.core_same("store " + t, [self.core_exe, "--fn", "model", f, dst], a,
                           c / ("%s.store.core.err" % t))
            print("%s over the store: %d bytes IDENTICAL (image, core)" % (t, a.stat().st_size))

    def stateful(self):
        """The writable verbs, step for step on twin stores (stateful.py): the
        outcome, the durable files and the subsequent read of every step
        identical, every case of its manifest run once, every required class
        covered -- through fn-core (the product under test) against the image."""
        self.step = "stateful"
        for label, program, extra in (("core", self.core_exe, []),):
            d = self.c / ("stateful-" + label)
            if d.exists():
                shutil.rmtree(d)
            log = self.c / ("stateful-%s.log" % label)
            rc = self.run("stateful.py " + label, self.t.stateful + [self.image, program, d] + extra, stdout=log,
                          stderr="stdout", env=self.acl2_env)
            man = self.load_json(d / "manifest.json", "stateful")
            doc = self.load_json(d / "stateful.json", "stateful")
            cases = sorted((man.get("cases") or {}))
            if not cases:
                self.fail("%s: the stateful manifest lists no cases" % label)
            results = doc.get("results") or []
            seen = collections.Counter(r.get("case") for r in results)
            for c in cases:
                if seen[c] != 1:
                    self.fail("%s: case %s ran %d times (want once)" % (label, c, seen[c]))
            extra_cases = sorted(set(seen) - set(cases))
            if extra_cases:
                self.fail("%s: cases %s are not in the manifest" % (label, extra_cases))
            bad = [r for r in results if r.get("verdict") != "agree"]
            if bad:
                self.fail("%s: %s DIFFER at %s: %s" % (label, bad[0]["case"], bad[0].get("step"), bad[0].get("reason")))
            if doc.get("missing"):
                self.fail("%s: classes not covered: %s" % (label, ", ".join(doc["missing"])))
            if doc.get("steps_run") != doc.get("steps_expected") or not doc.get("steps_run"):
                self.fail("%s: %s of %s steps ran" % (label, doc.get("steps_run"), doc.get("steps_expected")))
            if doc.get("status") != "PASS":
                self.fail("%s: stateful.json status %r" % (label, doc.get("status")))
            if rc != 0:
                self.fail("%s: stateful.py %s" % (label, describe_status(rc)))
            print("stateful %s: %d cases, %d steps agree; classes %s"
                  % (label, len(cases), doc["steps_run"], ",".join(doc.get("covered", []))))

    def owner(self):
        """Actual asynchronous owner effects; no offline crash surrogate."""
        from owner import CASE, OBSERVATIONS
        self.step = "owner"
        d = self.c / "owner"
        if d.exists():
            shutil.rmtree(d)
        log = self.c / "owner.log"
        self.need("owner.py", self.t.owner + [self.image, self.core_exe, d],
                  stdout=log, stderr="stdout", log=log, env=self.acl2_env)
        doc = self.load_json(d / "owner.json", "owner")
        if doc.get("status") != "PASS" or doc.get("case") != CASE:
            self.fail("owner case did not pass")
        if doc.get("observations_expected") != list(OBSERVATIONS):
            self.fail("owner observation manifest differs")
        products = doc.get("products_before", {})
        if set(products) != {"image", "core"} or products != doc.get("products_after"):
            self.fail("owner product fingerprints missing or changed")
        for label in ("image", "core"):
            artifacts = products[label].get("artifacts", {})
            if not artifacts or any(not re.fullmatch(r"[0-9a-f]{64}", digest)
                                    for digest in artifacts.values()):
                self.fail("owner product fingerprints invalid")
        sides = doc.get("sides", {})
        if set(sides) != {"image", "core"}:
            self.fail("owner must execute both image and core")
        for label in ("image", "core"):
            observed = sides[label].get("observations", {})
            if set(observed) != set(OBSERVATIONS) or not all(observed.values()):
                self.fail("%s: missing owner observations" % label)
        if sides["image"]["observations"] != sides["core"]["observations"]:
            self.fail("owner observations differ")
        print("owner: %s, %d observations agree" % (CASE, len(OBSERVATIONS)))

    # --- the extraction manifest --------------------------------------------------
    def world(self):
        entries = []

        def add(kind, rel, path):
            if not path.is_file():
                self.fail("the world names %s, which is not in the tree" % path)
            entries.append({"kind": kind, "path": rel, "sha256": sha256_file(path)})

        suffix = "-dtn" if self.t.variant == "dtn" else ""
        world_file, host_file = "world" + suffix + ".lisp", "world-host" + suffix + ".lisp"
        for name in (world_file, host_file):
            add("world-file", "tools/extract/" + name, self.x / name)
        for m in re.finditer(r'^\(include-book "\.\./\.\./([^"]+)"\)', (self.x / world_file).read_text(), re.M):
            rel = m.group(1) + ".cert"
            if not (self.tree / rel).is_file():
                self.fail("the world includes %s, which has no certificate (%s)" % (m.group(1), rel))
            add("certificate", rel, self.tree / rel)
        for m in re.finditer(r'^\(ld "\.\./\.\./([^"]+)"', (self.x / host_file).read_text(), re.M):
            add("host-program", m.group(1), self.tree / m.group(1))
        digest = hashlib.sha256("".join("%s %s %s\n" % (x["kind"], x["path"], x["sha256"]) for x in entries)
                                .encode()).hexdigest()
        return digest, entries

    def foreign(self):
        """The libraries fn-core loads: build/core/lib must be the image's own
        lib/ (the native signature, digest and deflate code call the files beside
        the image's core, not a second build of the same source).  Which files:
        exactly those core.sh exports (CORE_LIBRARIES)."""
        k = self.tree / "build" / "core"
        image_lib = Path(os.path.realpath(self.image)).parent / "lib"
        core_lib = k / "lib"
        if os.path.realpath(core_lib) != os.path.realpath(image_lib):
            self.fail("the core's lib is %s, not the image's %s" % (os.path.realpath(core_lib), image_lib))
        found = {}
        for want in core_libraries(Path(__file__).with_name("core.sh")):
            path = next(iter(sorted(core_lib.glob(want + ".*"))), None)
            if path is None:
                self.fail("the core's lib has no %s (%s)" % (want, core_lib))
            found[want] = {"soname": path.name, "path": os.path.realpath(path), "sha256": sha256_file(path)}
        return found

    def core_manifest(self):
        k = self.tree / "build" / "core"
        if not getattr(self, "core_exe", None):
            return None
        return {"executable": str(self.core_exe), "sha256": sha256_file(self.core_exe),
                "saved_core_sha256": sha256_file(k / "fn-core.core"),
                "ir_sha256": sha256_file(k / "core.json"), "defs_sha256": sha256_file(k / "defs.lisp"),
                "manifest_tsv_sha256": sha256_file(k / "manifest.tsv"),
                "runtime_tsv_sha256": sha256_file(k / "runtime.tsv"),
                "host_tokens_sha256": sha256_file(k / "tokens.lsp"), "units": self.core_units,
                "compiler": "SBCL compile-file under ACL2's policy (speed 3) (space 1) (safety 0) "
                            "(acl2.lisp *acl2-optimize-form*), each raw definition with the type "
                            "declarations ACL2 compiled it with",
                "erased_checks": "none beyond ACL2's raw code: the policy and declarations are the image's"}

    def capture(self, argv):
        try:
            r = subprocess.run(argv, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False, env=self.env)
            text = r.stdout.decode(errors="replace").strip().splitlines()
            return {"argv": argv, "status": r.returncode, "first_line": text[0] if text else ""}
        except OSError as ex:
            return {"argv": argv, "status": 127, "first_line": str(ex)}

    def manifest(self):
        self.step = "manifest"
        digest, entries = self.world()
        image_core = Path(str(self.image) + ".core")
        doc = {
            "status": "frozen",
            "source": self.t.source,
            "variant": self.t.variant,
            "image": {"launcher": str(self.image), "launcher_sha256": sha256_file(self.image),
                      "core": str(image_core) if image_core.is_file() else None,
                      "core_sha256": sha256_file(image_core) if image_core.is_file() else None},
            "admitted_world": {"digest": digest,
                               "rule": "SHA-256 over each entry's `KIND PATH SHA256` line, in load order",
                               "entries": entries},
            "foreign_libraries": self.foreign(),
            "core": self.core_manifest(),
            "toolchain": {"acl2": self.t.acl2, "acl2_sha256": sha256_file(self.t.acl2[0])
                          if Path(self.t.acl2[0]).is_file() else None},
        }
        path = self.c / "extraction-manifest.json"
        path.write_text(json.dumps(doc, indent=1) + "\n")
        print("manifest: world %s; %d units -> %s" % (digest[:16], self.core_units, path))

    def invariant_risk(self):
        """1c: no declared host entry whose *1* runs its body carries ACL2's
        invariant-risk in the world core.sh exported (tools/invariant_risk_check.py,
        its shrink-only baseline tools/invariant_risk_baseline.json)."""
        self.step = "invariant-risk"
        log = self.c / "invariant-risk.log"
        self.need("invariant_risk_check.py",
                  self.t.invariant_risk + ["--ir", self.tree / "build" / "core" / "core.json"],
                  stdout=log, stderr="stdout", log=log)
        self.nonempty(log, "invariant-risk")
        print(log.read_text().strip().splitlines()[-1])

    def main(self):
        if self.c.exists():
            shutil.rmtree(self.c)
        self.c.mkdir(parents=True)
        self.write_status("RUNNING")
        try:
            if self.t.variant not in ("default", "dtn"):
                self.fail("unsupported extraction variant " + self.t.variant)
            for name, stepfn in (("1 core", self.core), ("1b manifest", self.manifest),
                                 ("1c invariant-risk", self.invariant_risk),
                                 ("2 transcripts", self.transcripts),
                                 ("2b rtc-exercise", self.rtc_exercise), ("3 probes", self.probes),
                                 ("3b obligations", self.obligations),
                                 ("4 store", self.store), ("5 stateful", self.stateful),
                                 ("5b owner", self.owner), ("6 faults", self.faults)):
                print("==", name, flush=True)
                stepfn()
                sys.stdout.flush()
        except GateFail as ex:
            self.write_status("FAIL", step=ex.step, reason=ex.reason)
            print("extract-check: FAIL at %s: %s" % (ex.step, ex.reason))
            return 1
        except Exception as ex:  # a gate defect is a failure, never a pass
            self.write_status("FAIL", step=self.step, reason="gate error %r" % ex)
            print("extract-check: FAIL at %s: gate error %r" % (self.step, ex))
            return 1
        self.write_status("PASS")
        print("extract-check: PASS")
        return 0


def tools_from_env():
    acl2 = os.environ.get("FN_EXTRACT_ACL2", "/tank/fn/toolchains/w28/acl2-literal-4g-tls64k")
    return Tools(acl2=[acl2], core=["sh", str(X / "core.sh")],
                 store=os.environ.get("EXTRACT_STORE", "/tank/fn/scratch/fixtures/n1k-2k/store"),
                 source=os.environ.get("FN_EXTRACT_SOURCE"),
                 variant=os.environ.get("FN_EXTRACT_VARIANT", "default"),
                 fault_traces=[t for t in os.environ.get("FN_EXTRACT_FAULT_TRACES", "").split(":") if t])


def main(argv):
    if len(argv) != 3:
        sys.exit(__doc__)
    tree = Path(argv[1]).resolve()
    tools = tools_from_env()
    tools.core = tools.core + [str(tree)]
    if not tools.source:
        r = subprocess.run(["git", "-C", str(tree), "rev-parse", "HEAD"], stdout=subprocess.PIPE,
                           stderr=subprocess.DEVNULL, check=False)
        tools.source = r.stdout.decode().strip() if r.returncode == 0 else None
    return Gate(tree, argv[2], tools).main()


if __name__ == "__main__":
    sys.exit(main(sys.argv))
