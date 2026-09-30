#!/usr/bin/env python3
"""tools/extract/gate.py TREE IMAGE -- the extraction differential's gate
(A-EXTRACT's qualification of one build, specs/failures.md); check.sh runs it.

Fail closed.  Every child process's exit status is checked here, one call at
a time (no shell pipeline, no reliance on `set -e'); every stage's output is
compared against the manifest of what it had to produce; an empty, truncated
or missing output, a case that ran twice or not at all, a missing completion
marker and zero executed cases each FAIL with a named reason.  Steps:
  1. build: tools/extract/build.sh (front end, backend, csc); its products
     must exist and parse, and every extractor blocker must be declared
     (declared-blockers.json);
  2. transcripts: every case transcripts.py lists (its manifest.json),
     through IMAGE's `--fn model' and the program's model and socket verbs,
     compared once each and byte-identical (compare.sh);
  3. probes: the boundary probes through both sides, every probe identical;
  4. store: a copy of a real format-9 store, rebound, read through both;
  5. stateful: the writable verbs (`store ROOT post|recover|node-secret')
     through IMAGE and the program on twin stores, step for step
     (stateful.py): outcomes, durable files and subsequent reads identical,
     every case of its manifest run once, every required class covered;
  5b. owner: actual barrier completion after the owner has told its poster
      uncertain; exact wire replies, durable reads and restart through the
      reference image and extracted core (owner.py);
  6. functions: the per-function differential (fcheck.py gen -> ACL2 ->
     fcheck.py scheme -> csc -> the fcheck program -> fcheck.py report): every
     vector of the manifest executed once and agreeing; uncovered functions
     are listed, never counted as agreement.
Writes TREE/build/extract/check/: the logs, status.json (RUNNING until the
verdict, then PASS or FAIL with the step, the reason and every child's exit
status) and extraction-manifest.json (the frozen record of what was
extracted: world digest, roots, attachments, data model, erased checks,
shims, compiler options, foreign libraries).  Prints `extract-check: PASS'
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
    environment check.sh always honoured (FN_EXTRACT_ACL2, CHICKEN,
    EXTRACT_STORE, EXTRACT_FCHECK_PER); the gate's own tests substitute
    stand-ins through this object, never through the command line."""
    acl2: list
    csc: str
    chicken_lib: str
    swarm: list
    build: list
    ldd: list = field(default_factory=lambda: ["ldd"])
    cc: list = field(default_factory=lambda: ["cc", "--version"])
    store: str = "/tank/fn/scratch/fixtures/n1k-2k/store"
    # the Common Lisp product's build (tools/extract/core.sh TREE): the SBCL
    # core without ACL2, the second product under test
    core: list = None
    # the stateful differential's driver (tools/extract/stateful.py); the
    # gate's tests substitute a stand-in
    stateful: list = field(default_factory=lambda: ["python3", str(X / "stateful.py")])
    owner: list = field(default_factory=lambda: ["python3", str(X / "owner.py")])
    per: int = 20
    source: str = None
    variant: str = "default"


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
        self.env["LD_LIBRARY_PATH"] = tools.chicken_lib
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
    def build(self):
        self.step = "build"
        # no product of an earlier build may stand in for this one's
        for name in ("served.json", "inventory.json", "erased.json", "served.scm", "fntable.scm",
                     "csc-served.args", "extract.lsp", "served", "fcheck"):
            (self.e / name).unlink(missing_ok=True)
        log = self.c / "build.log"
        self.need("build.sh", self.t.build, stdout=log, stderr="stdout", log=log)
        ir = self.load_json(self.e / "served.json", "build")
        if not ir.get("functions"):
            self.fail("served.json extracts no functions")
        inv = self.load_json(self.e / "inventory.json", "build")
        self.load_json(self.e / "erased.json", "build")
        for name in ("served.scm", "fntable.scm", "csc-served.args", "link.args", "lib/libfn-blake3.so"):
            self.nonempty(self.e / name, "build")
        served = self.e / "served"
        if not (served.is_file() and os.access(served, os.X_OK)):
            self.fail("no executable %s" % served)
        declared = {b["name"]: b["why"] for b in json.loads((self.x / "declared-blockers.json").read_text())["blockers"]}
        undeclared = [b for b in inv.get("blocker", []) if b["name"] not in declared]
        if undeclared:
            self.fail("undeclared extractor blocker %s (%s); an unsupported form is refused unless "
                      "tools/extract/declared-blockers.json says why it is unreachable"
                      % (undeclared[0]["name"], undeclared[0]["reason"]))
        self.ir, self.inv, self.declared = ir, inv, declared
        print("build: %d functions; %d blockers, all declared" % (len(ir["functions"]), len(inv.get("blocker", []))))

    def core(self):
        """The Common Lisp product (A-TARGET-COMPILER): fn's functions and
        host/native in a bare SBCL core, built from the same world."""
        self.step = "core"
        k = self.tree / "build" / "core"
        (k / "fn-core").unlink(missing_ok=True)
        log = self.c / "core-build.log"
        env = dict(self.env, FN_CORE_NAME="fn-core", FN_NATIVE_PROFILE="developer",
                   FN_CORE_OUT=str(k), FN_EXTRACT_IMAGE=str(self.image))
        self.need("core.sh", self.t.core, stdout=log, stderr="stdout", log=log, env=env)
        for name in ("core.json", "defs.lisp", "packages.lisp", "core-world.lisp", "host-block.lisp", "inventory.json", "fn-core.core"):
            self.nonempty(k / name, "core")
        exe = k / "fn-core"
        if not (exe.is_file() and os.access(exe, os.X_OK)):
            self.fail("no executable %s" % exe)
        self.core_exe = exe
        self.core_inv = self.load_json(k / "inventory.json", "core")
        print("core: %d defuns, %d *1* functions, %d stobj primitives; host-defined %s"
              % (self.core_inv["defun"], self.core_inv["star1"], self.core_inv["stobj-prim"],
                 ",".join(sorted(self.core_inv["host-defined"]))))

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
        log = self.c / "transcripts.log"
        rc = self.run("compare.sh", ["sh", self.x / "compare.sh", self.image, self.e / "served", d, self.c / "cmp"],
                      stdout=log, stderr=self.c / "transcripts.err")
        seen = collections.Counter()
        summary = None
        for line in log.read_text(errors="replace").splitlines():
            words = line.split()
            if line.startswith("== "):
                summary = line
            elif words and words[0] in expected:
                seen[words[0]] += 1
                if not line.endswith("IDENTICAL"):
                    self.fail("%s DIFFER: %s" % (words[0], line.strip()))
            elif line.strip():
                self.fail("unrecognized compare.sh line %r" % line[:80])
        for n in expected:
            if seen[n] != 1:
                self.fail("case %s compared %d times (want once)" % (n, seen[n]))
            for side in ("sbcl", "chicken-model", "chicken-socket"):
                self.nonempty(self.c / "cmp" / ("%s.%s" % (n, side)), "transcripts")
        if summary != "== %d identical, 0 differ" % len(expected):
            self.fail("compare.sh summary %r, want %d identical" % (summary, len(expected)))
        if rc != 0:
            self.fail("compare.sh %s" % describe_status(rc))
        for n in expected:
            self.core_same("transcript " + n, [self.core_exe, "--fn", "model", d / (n + ".chunks"), "-"],
                           self.c / "cmp" / ("%s.sbcl" % n), self.c / "cmp" / ("%s.core.err" % n))
        print("transcripts: %d of %d identical (image, program model and socket, core)"
              % (len(expected), len(expected)))

    def probes(self):
        self.step = "probes"
        c = self.c
        self.need("probes.py run-sbcl", ["python3", self.x / "probes.py", "run-sbcl", self.image, c / "probes.sbcl"],
                  stdout=c / "probes-sbcl.log", stderr="stdout", log=c / "probes-sbcl.log")
        self.need("served probe", [self.e / "served", "probe"], stdout=c / "probes.chicken",
                  stderr=c / "probes.chicken.err", log=c / "probes.chicken.err")
        self.nonempty(c / "probes.sbcl", "probes")
        self.nonempty(c / "probes.chicken", "probes")
        self.need("probes.py compare", ["python3", self.x / "probes.py", "compare", c / "probes.sbcl", c / "probes.chicken"],
                  stdout=c / "probes.log", stderr="stdout", log=c / "probes.log")
        print(Path(c / "probes.log").read_text().strip().splitlines()[-1])
        self.need("probes.py run-core", ["python3", self.x / "probes.py", "run-core", self.core_exe, c / "probes.core"],
                  stdout=c / "probes-core.log", stderr="stdout", log=c / "probes-core.log")
        self.nonempty(c / "probes.core", "probes")
        self.need("probes.py compare core", ["python3", self.x / "probes.py", "compare", c / "probes.sbcl", c / "probes.core"],
                  stdout=c / "probes-core-cmp.log", stderr="stdout", log=c / "probes-core-cmp.log")
        print("core " + Path(c / "probes-core-cmp.log").read_text().strip().splitlines()[-1])

    STORE_READ = (b"CAPABILITIES\r\nMODE READER\r\nLIST\r\nLIST ACTIVE\r\nGROUP fn.test\r\nSTAT\r\nHEAD\r\nBODY\r\n"
                  b"ARTICLE 1\r\nARTICLE 2\r\nNEXT\r\nLAST\r\nOVER 1-3\r\nHDR Subject 1-3\r\nLISTGROUP fn.test 1-5\r\n"
                  b"ARTICLE 999\r\nARTICLE <nonexistent@example.invalid>\r\nNEWNEWS * 20000101 000000\r\nQUIT\r\n")

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
            a, b = c / ("%s.store.sbcl" % t), c / ("%s.store.chicken" % t)
            s1 = self.run("image model " + t, [self.image, "--fn", "model", f, dst], stdout=a,
                          stderr=str(a) + ".err", env=self.acl2_env)
            s2 = self.run("served model " + t, [self.e / "served", "model", f, dst], stdout=b, stderr=str(b) + ".err")
            if s1 != 0 or s2 != 0:
                self.fail("%s: image %s, program %s%s" % (t, describe_status(s1), describe_status(s2),
                                                            self.tail(str(b) + ".err", 1)))
            self.nonempty(a, "store")
            if a.read_bytes() != b.read_bytes():
                self.fail("%s DIFFER (%s against %s)" % (t, a, b))
            self.core_same("store " + t, [self.core_exe, "--fn", "model", f, dst], a,
                           c / ("%s.store.core.err" % t))
            print("%s over the store: %d bytes IDENTICAL (image, program, core)" % (t, a.stat().st_size))

    def stateful(self):
        """The writable verbs, step for step on twin stores (stateful.py): the
        outcome, the durable files and the subsequent read of every step
        identical, every case of its manifest run once, every required class
        covered -- through the Common Lisp product (the product under test)
        and through the CHICKEN program (the independent oracle, its store
        verbs host/store-write-host.lisp)."""
        self.step = "stateful"
        for label, program, extra in (("core", self.core_exe, ["--core"]), ("chicken", self.e / "served", [])):
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

    def functions(self):
        self.step = "functions"
        c, e = self.c, self.e
        self.need("fcheck.py gen", ["python3", self.x / "fcheck.py", "gen", e / "served.json", "--out", c / "cands",
                                    "--per", str(self.t.per), "--seed", "1"],
                  stdout=c / "gen.log", stderr="stdout", log=c / "gen.log")
        cands = self.load_json(c / "cands.manifest.json", "functions")
        files = sorted(cands.get("files") or {})
        if not files or not cands.get("candidates"):
            self.fail("gen wrote no candidates")
        lsp = c / "fcheck.lsp"
        with open(lsp, "w") as h:
            suffix = "-dtn" if self.t.variant == "dtn" else ""
            for f in ("world" + suffix + ".lisp", "world-host" + suffix + ".lisp",
                      "frontend.lisp", "fcheck.lisp"):
                h.write('(ld "tools/extract/%s")\n' % f)
            for f in files:
                h.write('(xt-fcheck "%s" "%s.vec" state)\n' % (c / f, c / f))
        for f in files:
            (c / (f + ".vec")).unlink(missing_ok=True)
        self.need("ACL2 fcheck", self.t.swarm + self.t.acl2, stdin=lsp, stdout=c / "fcheck-acl2.log",
                  stderr="stdout", log=c / "fcheck-acl2.log")
        vectors = c / "vectors.scm"
        self.need("fcheck.py scheme", ["python3", self.x / "fcheck.py", "scheme", "--cands", c / "cands.manifest.json",
                                       "--ir", e / "served.json", "--out", vectors],
                  stdout=c / "scheme.log", stderr="stdout", log=c / "scheme.log")
        vman = self.load_json(c / "vectors.scm.manifest.json", "functions")
        if not vman.get("vectors"):
            self.fail("zero vectors")
        shutil.copy(self.x / "fcheck-main.scm", e / "fcheck-main.scm")
        (e / "fcheck").unlink(missing_ok=True)
        # the served program's own link line (build.sh's link.args: BLAKE3,
        # and the image's ML-DSA-65 library)
        link = (e / "link.args").read_text().strip() if (e / "link.args").is_file() else ""
        if not link:
            self.fail("build/extract/link.args is missing or empty")
        self.fcheck_args = ["-O2", "-d0", "fcheck-main.scm", "-o", "fcheck", "-L", "-lcrypto", "-L", link]
        env = dict(self.env)
        env["PATH"] = str(Path(self.t.csc).parent) + os.pathsep + env.get("PATH", "")
        self.need("csc fcheck-main", self.t.swarm + [self.t.csc] + self.fcheck_args, cwd=e, env=env,
                  stdout=c / "fcheck-csc.log", stderr="stdout", log=c / "fcheck-csc.log")
        rc = self.run("fcheck", [e / "fcheck", vectors], stdout=c / "fcheck.log", stderr=c / "fcheck.err")
        rrc = self.run("fcheck.py report", ["python3", self.x / "fcheck.py", "report", e / "served.json", c / "fcheck.log",
                                            "--manifest", c / "vectors.scm.manifest.json", "--exit-status", str(rc),
                                            "--json", c / "fcheck.json"],
                       stdout=c / "report.log", stderr="stdout")
        report = c / "report.log"
        text = report.read_text(errors="replace") if report.exists() else ""
        print("\n".join(text.strip().splitlines()[:3]))
        doc = self.load_json(c / "fcheck.json", "functions")
        if rrc != 0 or doc.get("status") != "PASS":
            reason = next((l[len("fcheck: FAIL "):] for l in text.splitlines() if l.startswith("fcheck: FAIL ")),
                          "report %s, status %s" % (describe_status(rrc), doc.get("status")))
            self.fail(reason)
        if rc != 0:
            self.fail("fcheck %s" % describe_status(rc))

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
        out = self.c / "ldd.log"
        self.need("ldd served", self.t.ldd + [self.e / "served"], stdout=out, stderr="stdout", log=out)
        libs = {}
        for line in out.read_text().splitlines():
            m = re.match(r"\s*(\S+)\s+=>\s+(/\S+)", line)
            if m:
                libs[m.group(1)] = m.group(2)
        found = {}
        for want in ("libfn-blake3", "libfn-mldsa65", "libfn-lz4", "libcrypto", "libchicken"):
            name = next((n for n in libs if n.startswith(want + ".")), None)
            if name is None:
                self.fail("the program does not resolve %s (%s)" % (want, out))
            found[want] = {"soname": name, "path": libs[name], "sha256": sha256_file(libs[name])}
        # A-SIG-NATIVE and the LZ4 encoder: the program calls the files beside
        # the image's core that the image loads (host/native/signatures.lisp,
        # host/native/lz4.lisp), not a second build of the same source.
        for want in ("libfn-mldsa65", "libfn-lz4"):
            image_lib = Path(os.path.realpath(self.image)).parent / "lib" / found[want]["soname"]
            if os.path.realpath(found[want]["path"]) != os.path.realpath(image_lib):
                self.fail("the program's %s is %s, not the image's %s"
                          % (found[want]["soname"], found[want]["path"], image_lib))
        return found

    def core_manifest(self):
        k = self.tree / "build" / "core"
        if not getattr(self, "core_exe", None):
            return None
        return {"executable": str(self.core_exe), "sha256": sha256_file(self.core_exe),
                "saved_core_sha256": sha256_file(k / "fn-core.core"),
                "ir_sha256": sha256_file(k / "core.json"), "defs_sha256": sha256_file(k / "defs.lisp"),
                "compiler": "SBCL compile-file under ACL2's policy (speed 3) (space 1) (safety 0) "
                            "(acl2.lisp *acl2-optimize-form*), each raw definition with the type "
                            "declarations ACL2 compiled it with",
                "erased_checks": "none beyond ACL2's raw code: the policy and declarations are the image's",
                "inventory": {k2: v for k2, v in self.core_inv.items() if k2 != "star1_names"}}

    def capture(self, argv):
        try:
            r = subprocess.run(argv, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False, env=self.env)
            text = r.stdout.decode(errors="replace").strip().splitlines()
            return {"argv": argv, "status": r.returncode, "first_line": text[0] if text else ""}
        except OSError as ex:
            return {"argv": argv, "status": 127, "first_line": str(ex)}

    def manifest(self):
        self.step = "manifest"
        lsp = (self.e / "extract.lsp").read_text() if (self.e / "extract.lsp").exists() else ""
        m = re.search(r"\(xt-extract-with \(quote \(([^)]*)\)\) \(quote \(([^)]*)\)\)", lsp)
        if not m:
            self.fail("build/extract/extract.lsp does not name the extraction roots")
        digest, entries = self.world()
        erased = json.loads((self.e / "erased.json").read_text())
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
            "extraction_roots": m.group(1).split(),
            "extraction_extra": m.group(2).split(),
            "ir": {"sha256": sha256_file(self.e / "served.json"), "roots": self.ir.get("roots"),
                   "boundary": [b["name"] for b in self.ir.get("boundary", [])],
                   "functions": len(self.ir["functions"])},
            "resolved_attachments": [{"name": f["name"], "target": f.get("target"), "via": f.get("via", "unrecorded")}
                                     for f in self.ir["functions"] if f["kind"] == "alias"],
            "blockers": [dict(b, declared_why=self.declared.get(b["name"])) for b in self.inv.get("blocker", [])],
            "target_data_model": self.inv.get("data_model"),
            "erased_checks": {"count": len(erased), "sha256": sha256_file(self.e / "erased.json"),
                              "by_kind": dict(collections.Counter(x.get("erased", "?") for x in erased)),
                              "entries": erased},
            "runtime_shims": {"shims": self.inv.get("shim", []),
                              "hand_runtime": {n: sha256_file(self.e / n) for n in
                                               ("runtime.scm", "native.scm", "hostio.scm", "served-main.scm")
                                               if (self.e / n).is_file()}},
            "compiler": {"served": (self.e / "csc-served.args").read_text().strip(),
                         "fcheck": ("csc " + " ".join(self.fcheck_args)) if hasattr(self, "fcheck_args") else None,
                         "csc_version": self.capture([self.t.csc, "-version"]),
                         "c_compiler": self.capture(self.t.cc),
                         "served_sha256": sha256_file(self.e / "served")},
            "foreign_libraries": self.foreign(),
            "core": self.core_manifest(),
            "toolchain": {"acl2": self.t.acl2, "acl2_sha256": sha256_file(self.t.acl2[0])
                          if Path(self.t.acl2[0]).is_file() else None,
                          "chicken_lib": self.t.chicken_lib},
        }
        path = self.c / "extraction-manifest.json"
        path.write_text(json.dumps(doc, indent=1) + "\n")
        print("manifest: world %s; %d attachments; %d erased checks; %d shims -> %s"
              % (digest[:16], len(doc["resolved_attachments"]), len(erased), len(doc["runtime_shims"]["shims"]), path))

    def main(self):
        if self.c.exists():
            shutil.rmtree(self.c)
        self.c.mkdir(parents=True)
        self.write_status("RUNNING")
        try:
            if self.t.variant not in ("default", "dtn"):
                self.fail("unsupported extraction variant " + self.t.variant)
            for name, stepfn in (("1 build", self.build), ("1b manifest", self.manifest), ("1c core", self.core),
                                 ("2 transcripts", self.transcripts), ("3 probes", self.probes),
                                 ("4 store", self.store), ("5 stateful", self.stateful),
                                 ("5b owner", self.owner),
                                 ("6 functions", self.functions)):
                print("==", name, flush=True)
                stepfn()
                sys.stdout.flush()
            self.step = "manifest"
            self.manifest()   # again, with the fcheck compile line
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
    chicken = os.environ.get("CHICKEN", "/tank/fn/toolchains/chicken-5.4.0")
    return Tools(acl2=[acl2], csc=chicken + "/bin/csc", chicken_lib=chicken + "/lib",
                 swarm=["swarm-build"], build=["sh", str(X / "build.sh")], core=["sh", str(X / "core.sh")],
                 store=os.environ.get("EXTRACT_STORE", "/tank/fn/scratch/fixtures/n1k-2k/store"),
                 per=int(os.environ.get("EXTRACT_FCHECK_PER", "20")),
                 source=os.environ.get("FN_EXTRACT_SOURCE"),
                 variant=os.environ.get("FN_EXTRACT_VARIANT", "default"))


def main(argv):
    if len(argv) != 3:
        sys.exit(__doc__)
    tree = Path(argv[1]).resolve()
    tools = tools_from_env()
    tools.build = tools.build + [str(tree)]
    tools.core = tools.core + [str(tree)]
    if not tools.source:
        r = subprocess.run(["git", "-C", str(tree), "rev-parse", "HEAD"], stdout=subprocess.PIPE,
                           stderr=subprocess.DEVNULL, check=False)
        tools.source = r.stdout.decode().strip() if r.returncode == 0 else None
    return Gate(tree, argv[2], tools).main()


if __name__ == "__main__":
    sys.exit(main(sys.argv))
