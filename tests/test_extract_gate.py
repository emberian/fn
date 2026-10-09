"""The extraction gate's own tests (tools/extract/gate.py, check.sh), no ACL2.

The gate must fail closed: GPT-6's 2026-09-28 review ran the old check.sh with
a stand-in function-test binary that exited 73 before producing results, and
it printed PASS.  Here every external program the gate runs -- core.sh, the
SBCL image, fn-core, the stateful and owner drivers -- is a stand-in in a
scratch tree, and each test breaks one of them: a stage killed or exiting
nonzero, an output emptied or truncated, a mismatch induced.  Each must FAIL
the gate with a named reason, status.json must say FAIL, and the clean run
must PASS with its extraction manifest written.  The real gate code runs
(gate.py, transcripts.py, probes.py); only the programs are stand-ins.
"""
import contextlib
import hashlib
import io
import json
import os
import shutil
import stat
import subprocess
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools" / "extract"))
import gate  # noqa: E402

PY = sys.executable
# the libraries core.sh hands fn-core, which the gate requires beside the image's core
CORE_LIBS = gate.core_libraries(ROOT / "tools" / "extract" / "core.sh")

# --- the stand-ins ----------------------------------------------------------------
# One script, dispatched on its first argument; FAKE_FAULT names the one fault.
STANDIN = r'''
import json, os, re, signal, sys, hashlib
FAULT = os.environ.get("FAKE_FAULT", "")
role = sys.argv[1]
args = sys.argv[2:]

def transcript(path, verb):
    data = open(path, "rb").read()
    out = b"200 stand-in\r\n" + hashlib.sha256(data).hexdigest().encode() + b"\r\n"
    return out

if role == "sbcl":
    # the image: `--fn model F S', `--fn store S rebind-filesystem', or
    # image_command's `--eval (load ...)' for the probes
    if "--fn" in args:
        i = args.index("--fn")
        verb, rest = args[i + 1], args[i + 2:]
        if verb == "store":
            if FAULT == "rebind-exit":
                print("rebind failed"); sys.exit(4)
            print("rebound"); sys.exit(0)
        if verb == "rtc-exercise":
            # variant 0: 17 observation lines, steps 10 and 12 discard stale
            # completions; variant 1: the injected write reported, exit 4
            if rest[1:] and rest[1] in ("1", "2", "3"):
                for i in range(4):
                    print("(%d :x nil nil :invp :stable :matched)" % i)
                inv, stab = (":invp-violated", ":stable") if rest[1] == "2" else (":invp", ":moved")
                if FAULT == "rtc-fault-unreported":
                    inv, stab = ":invp", ":stable"
                print("(4 :send nil nil %s %s :unmatched-changed)" % (inv, stab))
                if os.environ.get("FAKE_CORE") and FAULT == "rtc-fault-core-differ":
                    print("(5 :x nil nil :invp :stable :matched)")
                sys.exit(4)
            if FAULT == "rtc-image-exit" and not os.environ.get("FAKE_CORE"):
                sys.exit(9)
            for i in range(17):
                tail = ":discarded" if i in (10, 12) and FAULT != "rtc-not-discarded" else ":matched"
                print("(%d :x nil nil :invp :stable %s)" % (i, tail))
            if os.environ.get("FAKE_CORE") and FAULT == "rtc-core-differ":
                print("(17 :x nil nil :invp :stable :matched)")
            sys.exit(0)
        if verb == "model":
            if FAULT == "model-empty":
                sys.exit(0)
            if FAULT == "image-model-exit" and not os.environ.get("FAKE_CORE"):
                sys.exit(5)
            if FAULT == "core-store-exit" and os.environ.get("FAKE_CORE") and rest[1:] and rest[1] != "-":
                sys.exit(3)
            out = transcript(rest[0], "model")
            if os.environ.get("FAKE_CORE") and FAULT == "core-differ":
                out += b"core differs\r\n"
            if os.environ.get("FAKE_CORE") and FAULT == "core-store-differ" and rest[1:] and rest[1] != "-":
                out = b"500 core\r\n"
            sys.stdout.buffer.write(out); sys.exit(0)
    if FAULT == "probe-sbcl-exit":
        sys.exit(6)
    sys.path.insert(0, os.environ["FAKE_EXTRACT_DIR"])
    import probes
    ps = probes.PROBES[:-1] if os.environ.get("FAKE_CORE") and FAULT == "core-probe-truncated" else probes.PROBES
    for label, entry, a in ps:
        print("PROBE %s %s" % (label, "returned 1" if os.environ.get("FAKE_CORE") and FAULT == "core-probe-differ"
                                else "returned 0"))

elif role == "core":
    # stand-in for tools/extract/core.sh TREE: a core that answers as the image
    k = os.path.join(args[0], "build", "core")
    os.makedirs(k, exist_ok=True)
    json.dump({name: os.environ.get(name) for name in
               ("FN_CORE_NAME", "FN_CORE_OUT", "FN_NATIVE_PROFILE", "FN_EXTRACT_VARIANT", "FN_EXTRACT_IMAGE")},
              open(os.path.join(k, "build-env.json"), "w"))
    if FAULT == "core-build-exit":
        print("stand-in core build failing"); sys.exit(3)
    if os.path.exists(os.path.join(k, "gaps.txt")):
        os.unlink(os.path.join(k, "gaps.txt"))
    for n in ("core.json", "packages.lisp", "core-world.lisp", "host-block.lisp", "fn-core.core", "tokens.lsp"):
        open(os.path.join(k, n), "w").write("stand-in\n")
    defs = b"(defun foo (x) x)\n"
    open(os.path.join(k, "defs.lisp"), "wb").write(defs)
    sha = hashlib.sha256(defs).hexdigest()
    if FAULT == "core-defs-tampered":
        sha = "0" * 64
    open(os.path.join(k, "defs.lisp.verified-sha256"), "w").write(sha + "\n")
    nonce, evsha = "ab" * 16, hashlib.sha256(defs).hexdigest()
    for phase in ("EXPORT", "VERIFY"):
        if FAULT == "core-evidence-missing" and phase == "VERIFY":
            continue
        n = "cd" * 16 if FAULT == "core-evidence-nonce" and phase == "VERIFY" else nonce
        h = "0" * 64 if FAULT == "core-evidence-sha" else evsha
        open(os.path.join(k, phase.lower() + ".done"), "w").write("XT-%s-DONE %s %s\n" % (phase, n, h))
    open(os.path.join(k, "manifest.tsv"), "w").write("#world_key\tstand-in\n" + ("" if FAULT == "core-no-units" else "ACL2::FOO\t" + "a" * 64 + "\tworld\n"))
    open(os.path.join(k, "runtime.tsv"), "w").write("ACL2::HARD-ERROR\thost-only\n")
    if FAULT == "core-gaps":
        open(os.path.join(k, "gaps.txt"), "w").write("ACL2::NOWHERE\n")
    lib = os.path.join(args[0], "build", "lib")
    if FAULT == "core-other-lib":
        lib = os.path.join(args[0], "build", "other-lib")
        os.makedirs(lib, exist_ok=True)
    link = os.path.join(k, "lib")
    if os.path.lexists(link):
        os.unlink(link)
    os.symlink(lib, link)
    exe = os.path.join(k, "fn-core")
    open(exe, "w").write("#!/bin/sh\nFAKE_CORE=1 exec %s %s sbcl \"$@\"\n" % (sys.executable, os.path.abspath(__file__)))
    os.chmod(exe, 0o755)
    print("core: built (stand-in)")

elif role == "obligations":
    # stand-in for tools/extract/obligations.py VERB ...: two items; compare is the real one
    sys.path.insert(0, os.environ["FAKE_EXTRACT_DIR"])
    import obligations
    verb = args[0]
    if verb == "forms":
        os.makedirs(args[1], exist_ok=True)
        open(os.path.join(args[1], "obligations.lisp"), "w").write("(stand-in)\n")
        open(os.path.join(args[1], "expected.count"), "w").write("2\n")
    elif verb in ("run-image", "run-core"):
        core = verb == "run-core"
        lines = ["OB VAR ACL2::*X* 1", "OB ENTRY ACL2::F ((1) NIL)"]
        if core and FAULT == "obligations-differ":
            lines[1] = "OB ENTRY ACL2::F (:UNKNOWN NIL)"
        if core and FAULT == "obligations-truncated":
            lines = lines[:1]
        else:
            lines.append("OB-END 2")
        open(os.path.join(args[2], "core.out" if core else "image.out"), "w").write("\n".join(lines) + "\n")
        if core and FAULT == "obligations-core-exit":
            sys.exit(9)
    elif verb == "compare":
        sys.exit(obligations.compare(args[1]))

elif role == "faults":
    # stand-in for tools/extract/faults_diff.py IMAGE CORE OUT
    out = args[2]
    os.makedirs(out, exist_ok=True)
    results = [{"case": "a", "verdict": "agree"}, {"case": "b", "verdict": "agree"}]
    if FAULT == "faults-differ":
        results[1]["verdict"] = "DIFFER"
    if FAULT == "faults-error":
        results[1].update(verdict="ERROR", error="boom")
    if FAULT == "faults-none":
        results = []
    json.dump({"results": results}, open(os.path.join(out, "faults.json"), "w"))
    sys.exit(1 if FAULT in ("faults-differ", "faults-error", "faults-none", "faults-exit") else 0)

elif role == "owner":
    from owner import CASE, OBSERVATIONS
    out = args[2]
    os.makedirs(out)
    if FAULT == "owner-exit":
        sys.exit(73)
    observations = {key: "observed" for key in OBSERVATIONS}
    doc = {"status": "PASS", "case": CASE, "observations_expected": list(OBSERVATIONS),
           "sides": {label: {"observations": dict(observations)} for label in ("image", "core")}}
    products = {label: {"artifacts": {label: "a" * 64}} for label in ("image", "core")}
    doc.update(products_before=products, products_after=products)
    if FAULT == "owner-changed-product":
        doc["products_after"] = {}
    if FAULT == "owner-missing-side":
        del doc["sides"]["core"]
    if FAULT == "owner-missing-observation":
        del doc["sides"]["core"]["observations"]["closed"]
    if FAULT == "owner-differ":
        doc["sides"]["core"]["observations"]["uncertain"] = "accepted"
    if FAULT == "owner-fail":
        doc["status"] = "FAIL"
    if FAULT == "owner-empty":
        doc["sides"]["core"]["observations"]["closed"] = ""
    json.dump(doc, open(os.path.join(out, "owner.json"), "w"))

elif role == "stateful":
    # stand-in for tools/extract/stateful.py IMAGE PROGRAM OUT
    out = args[2]
    os.makedirs(out, exist_ok=True)
    cases = ["posts", "interrupted"]
    json.dump({"cases": {c: {"classes": ["post"], "steps": 2} for c in cases}},
              open(os.path.join(out, "manifest.json"), "w"))
    if FAULT == "stateful-no-report":
        sys.exit(0)
    results = [{"case": c, "verdict": "agree", "steps": [{"verdict": "agree"}] * 2} for c in cases]
    doc = {"status": "PASS", "covered": ["post"], "missing": [], "steps_run": 4, "steps_expected": 4}
    if FAULT == "stateful-differ":
        results[1] = {"case": "interrupted", "verdict": "DIFFER", "step": "01 post", "reason": "outcome differs (stdout)"}
        doc["status"] = "FAIL"
    if FAULT == "stateful-duplicate":
        results.append(dict(results[0]))
    if FAULT == "stateful-missing-case":
        results = results[:1]
    if FAULT == "stateful-missing-class":
        doc["missing"] = ["late-completion"]
    if FAULT == "stateful-short":
        doc["steps_run"] = 3
    doc["results"] = results
    json.dump(doc, open(os.path.join(out, "stateful.json"), "w"))
    print("stand-in stateful")
    sys.exit(7 if FAULT == "stateful-exit" else 0)

'''

LINKED = ("probes.py", "transcripts.py", "sig-vectors.json")


class Fixture:
    def __init__(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="fn-extract-gate-")
        t = self.tree = Path(self.tmp.name) / "tree"
        x = t / "tools" / "extract"
        x.mkdir(parents=True)
        for name in LINKED:
            (x / name).symlink_to(ROOT / "tools" / "extract" / name)
        # a stand-in admitted world: one certified book, one host file
        (x / "world.lisp").write_text('(in-package "ACL2")\n(include-book "../../books/a")\n')
        (x / "world-host.lisp").write_text('(in-package "ACL2")\n(ld "../../host/h.lisp" :ld-error-action :error)\n')
        (t / "books").mkdir()
        (t / "books" / "a.lisp").write_text("(in-package \"ACL2\")\n")
        (t / "books" / "a.cert").write_text("stand-in certificate\n")
        (t / "host").mkdir()
        (t / "host" / "h.lisp").write_text("; stand-in host file\n")
        bin_ = Path(self.tmp.name) / "bin"
        bin_.mkdir()
        self.standin = bin_ / "standin.py"
        self.standin.write_text(STANDIN)
        for role in ("sbcl", "acl2"):
            p = bin_ / role
            p.write_text("#!/bin/sh\nexec %s %s %s \"$@\"\n" % (PY, self.standin, role))
            p.chmod(p.stat().st_mode | stat.S_IEXEC)
        self.image = t / "build" / "fn-host-developer"
        self.image.parent.mkdir(parents=True)
        # image_command reads the runtime words from the launcher's exec line
        self.image.write_text("#!/bin/sh\nexec %s %s sbcl --end-runtime-options \"$@\"\n" % (PY, self.standin))
        self.image.chmod(0o755)
        (t / "build" / "lib").mkdir()
        for lib in CORE_LIBS:
            (t / "build" / "lib" / (lib + ".so")).write_text("stand-in %s\n" % lib)
        self.store = Path(self.tmp.name) / "store"
        self.store.mkdir()
        (self.store / "segment").write_text("stand-in store\n")
        self.tools = gate.Tools(acl2=[str(bin_ / "acl2")],
                                stateful=[PY, str(self.standin), "stateful"],
                                owner=[PY, str(self.standin), "owner"],
                                obligations=[PY, str(self.standin), "obligations"],
                                faults=[PY, str(self.standin), "faults"],
                                core=[PY, str(self.standin), "core", str(t)],
                                store=str(self.store), source="stand-in")
        self.env = {"FAKE_EXTRACT_DIR": str(ROOT / "tools" / "extract"),
                    "PYTHONPATH": str(ROOT / "tools" / "extract")}

    def run(self, fault=""):
        g = gate.Gate(self.tree, self.image, self.tools)
        for env in (g.env, g.acl2_env):
            env.update(self.env)
            env["FAKE_FAULT"] = fault
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            rc = g.main()
        status = json.loads((g.c / "status.json").read_text())
        return rc, out.getvalue(), status, g

    def close(self):
        self.tmp.cleanup()


class ExtractGateTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.fx = Fixture()

    @classmethod
    def tearDownClass(cls):
        cls.fx.close()

    def assertFails(self, fault, step, reason):
        rc, out, status, _ = self.fx.run(fault)
        self.assertEqual(rc, 1, out)
        self.assertNotIn("extract-check: PASS", out)
        self.assertIn("extract-check: FAIL at %s:" % step, out)
        self.assertIn(reason, out)
        self.assertEqual(status["status"], "FAIL")
        self.assertEqual(status["step"], step)
        self.assertIn(reason, status["reason"])
        return out, status

    def test_dtn_gate_uses_only_dtn_world_in_every_stage(self):
        fx = Fixture()
        try:
            fx.tools.variant = "dtn"
            for name in ("world", "world-host"):
                source = fx.tree / "tools/extract" / (name + ".lisp")
                source.rename(source.with_name(name + "-dtn.lisp"))
            rc, out, status, g = fx.run()
            self.assertEqual(rc, 0, out)
            self.assertEqual(status["status"], "PASS")
            manifest = json.loads((g.c / "extraction-manifest.json").read_text())
            self.assertEqual(manifest["variant"], "dtn")
            paths = [e["path"] for e in manifest["admitted_world"]["entries"]]
            self.assertEqual(paths[:2], ["tools/extract/world-dtn.lisp", "tools/extract/world-host-dtn.lisp"])
            env = json.loads((fx.tree / "build/core/build-env.json").read_text())
            self.assertEqual(env, {"FN_CORE_NAME": "fn-core", "FN_NATIVE_PROFILE": "developer",
                                  "FN_CORE_OUT": str(fx.tree.resolve() / "build/core"),
                                  "FN_EXTRACT_VARIANT": "dtn", "FN_EXTRACT_IMAGE": str(fx.image)})
        finally:
            fx.close()

    def test_unknown_variant_refuses_before_any_child(self):
        fx = Fixture()
        try:
            fx.tools.variant = "unknown"
            rc, out, status, _ = fx.run()
            self.assertEqual(rc, 1, out)
            self.assertEqual(status["step"], "setup")
            self.assertEqual(status["children"], [])
        finally:
            fx.close()

    def test_owner_gate_refuses_incomplete_or_disagreeing_runs(self):
        for fault, reason in (("owner-exit", "exited 73"),
                              ("owner-changed-product", "fingerprints missing or changed"),
                              ("owner-missing-side", "both image and core"),
                              ("owner-missing-observation", "missing owner observations"),
                              ("owner-differ", "observations differ"),
                              ("owner-fail", "did not pass"),
                              ("owner-empty", "missing owner observations")):
            with self.subTest(fault=fault):
                self.assertFails(fault, "owner", reason)

    def test_clean_run_passes_with_manifest(self):
        rc, out, status, g = self.fx.run("")
        self.assertEqual(rc, 0, out)
        self.assertIn("extract-check: PASS", out)
        self.assertEqual(status["status"], "PASS")
        # the rtc-exercise fault variant exits 4 by design on both sides
        self.assertTrue(all(c["status"] == (4 if " rtc-exercise fault " in c["what"] + " " else 0)
                            for c in status["children"]), status["children"])
        for step in ("core", "transcripts", "rtc-exercise", "probes", "store", "stateful", "owner"):
            self.assertIn(step, {c["step"] for c in status["children"]})
        m = json.loads((g.c / "extraction-manifest.json").read_text())
        for key in ("admitted_world", "foreign_libraries", "core", "toolchain", "image"):
            self.assertIn(key, m)
        self.assertEqual(len(m["admitted_world"]["digest"]), 64)
        self.assertEqual([e["path"] for e in m["admitted_world"]["entries"]],
                         ["tools/extract/world.lisp", "tools/extract/world-host.lisp", "books/a.cert", "host/h.lisp"])
        self.assertEqual(set(m["foreign_libraries"]), set(CORE_LIBS))
        self.assertEqual(m["core"]["units"], 1)
        self.assertEqual(m["core"]["defs_sha256"], hashlib.sha256(b"(defun foo (x) x)\n").hexdigest())

    # 1 core: the build and its products
    def test_core_evidence_missing(self):
        self.assertFails("core-evidence-missing", "core", "verify.done was not written")

    def test_core_evidence_of_two_runs(self):
        self.assertFails("core-evidence-nonce", "core", "different nonces")

    def test_core_evidence_names_other_defs(self):
        self.assertFails("core-evidence-sha", "core", "names other defs.lisp bytes")

    def test_obligations_differ(self):
        self.assertFails("obligations-differ", "obligations", "ENTRY ACL2::F")

    def test_obligations_truncated(self):
        self.assertFails("obligations-truncated", "obligations", "incomplete")

    def test_obligations_core_exit(self):
        self.assertFails("obligations-core-exit", "obligations", "run-core")

    def test_faults_differ(self):
        self.assertFails("faults-differ", "faults", "1 of 2 fault cases did not agree")

    def test_faults_case_error(self):
        self.assertFails("faults-error", "faults", "ERROR b boom")

    def test_faults_no_case(self):
        self.assertFails("faults-none", "faults", "ran no case")

    def test_faults_exit_after_agreement(self):
        self.assertFails("faults-exit", "faults", "faults_diff.py")

    def test_core_build_exit(self):
        self.assertFails("core-build-exit", "core", "core.sh exited 3")

    def test_core_closure_gaps(self):
        self.assertFails("core-gaps", "core", "names nothing provides")

    def test_core_defs_not_the_verified_file(self):
        self.assertFails("core-defs-tampered", "core", "not the file xt-verify-defs verified")

    def test_core_manifest_lists_no_units(self):
        self.assertFails("core-no-units", "core", "manifest.tsv lists no units")

    def test_uncertified_world(self):
        cert = self.fx.tree / "books" / "a.cert"
        text = cert.read_text()
        cert.unlink()
        try:
            self.assertFails("", "manifest", "has no certificate")
        finally:
            cert.write_text(text)

    # A-SIG-NATIVE: a second build of the verifier is not the image's library.
    def test_other_lib_directory_fails(self):
        self.assertFails("core-other-lib", "manifest", "not the image's")

    def test_missing_library(self):
        lib = self.fx.tree / "build" / "lib" / "libfn-blake3.so"
        text = lib.read_text()
        lib.unlink()
        try:
            self.assertFails("", "manifest", "has no libfn-blake3")
        finally:
            lib.write_text(text)

    # 2 transcripts
    def test_core_transcript_differ(self):
        self.assertFails("core-differ", "transcripts", "the core's reply differs")

    def test_transcript_image_exit(self):
        self.assertFails("image-model-exit", "transcripts", "the image exited 5")

    def test_transcripts_empty(self):
        self.assertFails("model-empty", "transcripts", "is empty")

    # 2b rtc-exercise
    def test_rtc_exercise_refuses_a_failed_image_run_and_a_differing_core(self):
        for fault, reason in (("rtc-image-exit", "the image exited 9"),
                              ("rtc-not-discarded", "discarded steps"),
                              ("rtc-core-differ", "the core's reply differs"),
                              ("rtc-fault-unreported", "is not reported :moved"),
                              ("rtc-fault-core-differ", "the core's reply differs")):
            with self.subTest(fault=fault):
                self.assertFails(fault, "rtc-exercise", reason)

    # 3 probes
    def test_probe_sbcl_exit(self):
        self.assertFails("probe-sbcl-exit", "probes", "probes.py run-sbcl exited 6")

    def test_core_probe_differ(self):
        self.assertFails("core-probe-differ", "probes", "probes.py compare core")

    def test_core_probe_output_truncated(self):
        self.assertFails("core-probe-truncated", "probes", "probes.py compare core exited 1")

    # 4 store
    def test_store_rebind_exit(self):
        self.assertFails("rebind-exit", "store", "image rebind-filesystem exited 4")

    def test_core_store_exit(self):
        self.assertFails("core-store-exit", "store", "the core exited 3")

    def test_core_store_differ(self):
        self.assertFails("core-store-differ", "store", "the core's reply differs")

    # 5 stateful: every way its report can fall short fails the gate
    def test_stateful_differ(self):
        self.assertFails("stateful-differ", "stateful", "core: interrupted DIFFER at 01 post")

    def test_stateful_no_report(self):
        self.assertFails("stateful-no-report", "stateful", "stateful.json")

    def test_stateful_duplicate_case(self):
        self.assertFails("stateful-duplicate", "stateful", "ran 2 times")

    def test_stateful_missing_case(self):
        self.assertFails("stateful-missing-case", "stateful", "ran 0 times")

    def test_stateful_missing_class(self):
        self.assertFails("stateful-missing-class", "stateful", "classes not covered")

    def test_stateful_short(self):
        self.assertFails("stateful-short", "stateful", "3 of 4 steps ran")

    def test_stateful_nonzero_exit(self):
        self.assertFails("stateful-exit", "stateful", "exited 7")


class CheckShTest(unittest.TestCase):
    def test_usage(self):
        import subprocess
        r = subprocess.run(["sh", str(ROOT / "tools" / "extract" / "check.sh")], capture_output=True, text=True)
        self.assertEqual(r.returncode, 2)


class CoreLibraries(unittest.TestCase):
    def test_the_gate_requires_exactly_the_libraries_core_sh_exports(self):
        self.assertEqual(sorted(CORE_LIBS), ["libfn-blake3", "libfn-deflate", "libfn-mldsa65"])


if __name__ == "__main__":
    unittest.main()
