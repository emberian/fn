"""The extraction gate's own tests (tools/extract/gate.py, check.sh), no ACL2.

The gate (lane extract-gate) must fail closed: GPT-6's 2026-09-28 review ran
the old check.sh with a stand-in function-test binary that exited 73 before
producing results, and it printed PASS.  Here every external program the
gate runs -- build.sh, the SBCL image, the extracted program, ACL2, csc, the
fcheck program, ldd -- is a stand-in in a scratch tree, and each test breaks
one of them: a stage killed or exiting nonzero, an output emptied or
truncated, a vector file removed, an expected result corrupted, a mismatch
induced.  Each must FAIL the gate with a named reason, status.json must say
FAIL, and the clean run must PASS with its extraction manifest written.  The
real gate code runs (gate.py, fcheck.py gen/scheme/report, transcripts.py,
compare.sh, probes.py); only the programs are stand-ins.
"""
import contextlib
import io
import json
import os
import shutil
import stat
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools" / "extract"))
import gate  # noqa: E402

PY = sys.executable

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

if role == "build":
    tree = args[0]
    e = os.path.join(tree, "build", "extract")
    os.makedirs(os.path.join(e, "lib"), exist_ok=True)
    if FAULT == "build-exit":
        print("stand-in build failing"); sys.exit(2)
    fn = lambda name, guard=["q", ["y", "COMMON-LISP::T"]]: {
        "name": name, "kind": "defun", "class": "common-lisp-compliant", "formals": ["ACL2::X"],
        "stobjs_in": [None], "stobjs_out": [None], "predefined": False, "invariant_risk": False,
        "guard": guard, "body": ["v", "ACL2::X"]}
    ir = {"roots": ["ACL2::FOO"], "boundary": [{"name": "ACL2::FOO"}],
          "functions": [fn("ACL2::FOO"), fn("ACL2::BAR"), fn("ACL2::UNCOV"),
                        {"name": "ACL2::ATT", "kind": "alias", "formals": [], "stobjs_in": [],
                         "stobjs_out": [], "target": "ACL2::FOO", "via": "attachment"}],
          "stobjs": []}
    if FAULT == "build-undeclared-blocker":
        ir["functions"].append({"name": "ACL2::NEWBLOCK", "kind": "blocker", "reason": "no body"})
    open(os.path.join(e, "served.json"), "w").write("" if FAULT == "build-empty-ir" else json.dumps(ir))
    blockers = [{"name": f["name"], "reason": f["reason"]} for f in ir["functions"] if f["kind"] == "blocker"]
    json.dump({"defun": 3, "shim": [{"name": "ACL2::HARD-ERROR", "why": "raw-only error"}],
               "blocker": blockers, "data_model": {"target": "stand-in"}},
              open(os.path.join(e, "inventory.json"), "w"))
    json.dump([{"fn": "ACL2::FOO", "erased": "generic-arithmetic dispatch and overflow promotion"}],
              open(os.path.join(e, "erased.json"), "w"))
    for n in ("served.scm", "fntable.scm", "runtime.scm", "native.scm", "hostio.scm", "served-main.scm"):
        open(os.path.join(e, n), "w").write(";; stand-in\n")
    open(os.path.join(e, "lib", "libfn-blake3.so"), "w").write("stand-in blake3\n")
    open(os.path.join(e, "csc-served.args"), "w").write("csc -O3 served-main.scm -o served\n")
    open(os.path.join(e, "extract.lsp"), "w").write(
        "(xt-extract-with (quote (FOO)) (quote (CREATE-X)) \"build/extract/served.json\" state)\n")
    if FAULT != "build-no-served":
        p = os.path.join(e, "served")
        open(p, "w").write("#!/bin/sh\nexec %s %s served \"$@\"\n" % (sys.executable, os.path.abspath(__file__)))
        os.chmod(p, 0o755)
    print("extract: built (stand-in)")

elif role == "sbcl":
    # the image: `--fn model F S', `--fn store S rebind-filesystem', or
    # image_command's `--eval (load ...)' for the probes
    if "--fn" in args:
        i = args.index("--fn")
        verb, rest = args[i + 1], args[i + 2:]
        if verb == "store":
            if FAULT == "rebind-exit":
                print("rebind failed"); sys.exit(4)
            print("rebound"); sys.exit(0)
        if verb == "model":
            if FAULT == "model-empty":
                sys.exit(0)
            if FAULT == "image-model-exit":
                sys.exit(5)
            sys.stdout.buffer.write(transcript(rest[0], "model")); sys.exit(0)
    if FAULT == "probe-sbcl-exit":
        sys.exit(6)
    sys.path.insert(0, os.environ["FAKE_EXTRACT_DIR"])
    import probes
    for label, entry, a in probes.PROBES:
        print("PROBE %s returned 0" % label)

elif role == "served":
    verb = args[0]
    if verb in ("model", "socket"):
        if FAULT == "model-empty":
            sys.exit(0)
        if FAULT == "served-socket-killed" and verb == "socket":
            os.kill(os.getpid(), signal.SIGKILL)
        out = transcript(args[1], verb)
        if FAULT == "served-model-differ" and verb == "model":
            out += b"extra\r\n"
        if FAULT == "store-served-exit" and len(args) > 2:
            sys.exit(3)
        if FAULT == "store-differ" and len(args) > 2:
            out = b"500 different\r\n"
        sys.stdout.buffer.write(out); sys.exit(0)
    if verb == "probe":
        sys.path.insert(0, os.environ["FAKE_EXTRACT_DIR"])
        import probes
        ps = probes.PROBES[:-1] if FAULT == "probe-truncated" else probes.PROBES
        for label, entry, a in ps:
            print("PROBE %s returned 0" % label)
        if FAULT == "probe-served-exit":
            sys.exit(7)

elif role == "acl2":
    # reads the fcheck session from stdin; for each (xt-fcheck "IN" "OUT"
    # state) writes one vector per candidate (FOO: x, BAR: 2x) and the trailer
    if FAULT == "acl2-exit":
        sys.exit(1)
    calls = re.findall(r'\(xt-fcheck "([^"]+)" "([^"]+)" state\)', sys.stdin.read())
    for n, (inp, out) in enumerate(calls):
        if FAULT == "acl2-missing-vec" and n == 1:
            continue
        cands = [l for l in open(inp) if l.startswith("((:y")]
        ok = gf = 0
        with open(out, "w") as h:
            for k, c in enumerate(cands):
                codes = re.match(r'\(\(:y "ACL2" \(([\d ]+)\)\)', c).group(1)
                name = "ACL2::" + "".join(chr(int(x)) for x in codes.split())
                if name == "ACL2::UNCOV" or FAULT == "acl2-all-guard-false":
                    gf += 1
                    continue
                result = k * 2 if name == "ACL2::BAR" else k
                if FAULT == "acl2-corrupt-result" and n == 0 and ok == 3:
                    result += 1
                h.write(json.dumps({"fn": name, "args": [k], "result": result}) + "\n")
                ok += 1
            if FAULT == "acl2-no-trailer" and n == 0:
                continue
            cand = len(cands) - (1 if FAULT == "acl2-short" and n == 0 else 0)
            h.write(json.dumps({"done": 1, "candidates": cand, "ok": ok, "guard_false": gf, "error": 0}) + "\n")

elif role == "csc":
    if args and args[0] == "-version":
        print("Version 5.4.0 (stand-in)"); sys.exit(0)
    if FAULT == "csc-exit":
        print("csc: error"); sys.exit(1)
    out = args[args.index("-o") + 1]
    open(out, "w").write("#!/bin/sh\nexec %s %s fcheck \"$@\"\n" % (sys.executable, os.path.abspath(__file__)))
    os.chmod(out, 0o755)
    if FAULT == "tamper-vectors":
        v = os.path.join(os.getcwd(), "check", "vectors.scm")
        open(v, "a").write(";; tampered\n")

elif role == "fcheck":
    # the extracted functions, for the stand-in: FOO(x) = x, BAR(x) = 2x
    if FAULT == "fcheck-exit73":
        sys.exit(73)
    if FAULT == "fcheck-empty":
        sys.exit(0)
    lines = [l for l in open(args[0]) if l.startswith("(")]
    print("FCHECK-BEGIN", flush=True)
    for i, l in enumerate(lines):
        m = re.match(r'^\((\d+) "([^"]+)" \((\S*)\) (\S+) (\d+)\)$', l.strip())
        cid, name, x, expected = m.group(1), m.group(2), int(m.group(3)), int(m.group(4))
        if FAULT in ("fcheck-truncated", "fcheck-killed") and i == len(lines) // 2:
            sys.stdout.flush()
            if FAULT == "fcheck-killed":
                os.kill(os.getpid(), signal.SIGKILL)
            sys.exit(0)
        got = 2 * x if name == "ACL2::BAR" else x
        if FAULT == "fcheck-differ" and i == 2:
            got += 1
        if FAULT == "fcheck-skip" and i == 1:
            continue
        if FAULT == "fcheck-unknown-id" and i == 0:
            cid = "999999"
        if FAULT == "fcheck-raise" and i == 0:
            print("RAISE\t%s\t%s\t(%d)\t(exn)" % (cid, name, x)); continue
        if FAULT == "fcheck-hang" and i == 0:
            print("HANG\t%s\t%s\t(%d)" % (cid, name, x)); continue
        if got == expected:
            print("AGREE\t%s\t%s" % (cid, name))
        else:
            print("DIFFER\t%s\t%s\t(%d)\t%d\t%d" % (cid, name, x, expected, got))
        if FAULT == "fcheck-duplicate" and i == 0:
            print("AGREE\t%s\t%s" % (cid, name))
    if FAULT == "fcheck-no-newline":
        sys.stdout.write("FCHECK-COMPLETE\t%d" % len(lines)); sys.exit(0)
    print("FCHECK-COMPLETE\t%d" % len(lines))
    if FAULT == "fcheck-after-complete":
        print("AGREE\t0\tACL2::FOO")
    if FAULT == "fcheck-exit-after":
        sys.exit(9)

elif role == "ldd":
    e = os.path.dirname(args[0])
    print("\tlibfn-blake3.so => %s/lib/libfn-blake3.so (0x0)" % e)
    if FAULT != "ldd-no-libcrypto":
        print("\tlibcrypto.so.3 => %s (0x0)" % os.environ["FAKE_LIBCRYPTO"])
    print("\tlibchicken.so.11 => %s (0x0)" % os.environ["FAKE_LIBCRYPTO"])
'''

LINKED = ("fcheck.py", "chicken.py", "probes.py", "transcripts.py", "compare.sh",
          "fcheck-main.scm", "declared-blockers.json")


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
        for role in ("sbcl", "acl2", "csc", "ldd"):
            p = bin_ / role
            p.write_text("#!/bin/sh\nexec %s %s %s \"$@\"\n" % (PY, self.standin, role))
            p.chmod(p.stat().st_mode | stat.S_IEXEC)
        self.image = t / "build" / "fn-host-developer"
        self.image.parent.mkdir(parents=True)
        # image_command reads the runtime words from the launcher's exec line
        self.image.write_text("#!/bin/sh\nexec %s %s sbcl --end-runtime-options \"$@\"\n" % (PY, self.standin))
        self.image.chmod(0o755)
        (bin_ / "libcrypto.so.3").write_text("stand-in libcrypto\n")
        self.store = Path(self.tmp.name) / "store"
        self.store.mkdir()
        (self.store / "segment").write_text("stand-in store\n")
        self.tools = gate.Tools(acl2=[str(bin_ / "acl2")], csc=str(bin_ / "csc"), chicken_lib=str(bin_),
                                swarm=[], build=[PY, str(self.standin), "build", str(t)],
                                ldd=[str(bin_ / "ldd")], cc=["echo", "cc stand-in"],
                                store=str(self.store), per=400, source="stand-in")
        self.env = {"FAKE_EXTRACT_DIR": str(ROOT / "tools" / "extract"),
                    "FAKE_LIBCRYPTO": str(bin_ / "libcrypto.so.3")}

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

    def test_clean_run_passes_with_manifests(self):
        rc, out, status, g = self.fx.run("")
        self.assertEqual(rc, 0, out)
        self.assertIn("extract-check: PASS", out)
        self.assertEqual(status["status"], "PASS")
        self.assertTrue(all(c["status"] == 0 for c in status["children"]), status["children"])
        report = json.loads((g.c / "fcheck.json").read_text())
        self.assertEqual(report["status"], "PASS")
        self.assertGreater(report["executed_vectors"], 0)
        self.assertEqual(report["executed_vectors"], report["manifest_vectors"])
        # UNCOV had only guard-false candidates: listed, not folded into agreement
        self.assertEqual(report["uncovered"], ["ACL2::UNCOV"])
        self.assertEqual(report["uncovered_count"], 1)
        self.assertIn("UNCOVERED 1", out)
        m = json.loads((g.c / "extraction-manifest.json").read_text())
        for key in ("admitted_world", "extraction_roots", "resolved_attachments", "target_data_model",
                    "erased_checks", "runtime_shims", "compiler", "foreign_libraries"):
            self.assertIn(key, m)
        self.assertEqual(len(m["admitted_world"]["digest"]), 64)
        self.assertEqual([e["path"] for e in m["admitted_world"]["entries"]],
                         ["tools/extract/world.lisp", "tools/extract/world-host.lisp", "books/a.cert", "host/h.lisp"])
        self.assertEqual(m["extraction_roots"], ["FOO"])
        self.assertEqual(m["resolved_attachments"], [{"name": "ACL2::ATT", "target": "ACL2::FOO", "via": "attachment"}])
        self.assertEqual(set(m["foreign_libraries"]), {"libfn-blake3", "libcrypto", "libchicken"})
        self.assertTrue(m["compiler"]["fcheck"].startswith("csc -O2"))

    # GPT-6's witness: the function-test binary exits 73 before any result.
    def test_gpt6_exit_73_standin_fails(self):
        out, status = self.assertFails("fcheck-exit73", "functions", "the fcheck program exited 73")
        self.assertIn("no FCHECK-BEGIN", out)
        self.assertTrue(any(c["what"] == "fcheck" and c["status"] == 73 for c in status["children"]))

    # 1 build
    def test_build_exit(self):
        self.assertFails("build-exit", "build", "build.sh exited 2")

    def test_build_without_program(self):
        self.assertFails("build-no-served", "build", "no executable")

    def test_build_empty_ir(self):
        self.assertFails("build-empty-ir", "build", "served.json is empty")

    def test_undeclared_blocker(self):
        self.assertFails("build-undeclared-blocker", "build", "undeclared extractor blocker ACL2::NEWBLOCK")

    def test_uncertified_world(self):
        cert = self.fx.tree / "books" / "a.cert"
        text = cert.read_text()
        cert.unlink()
        try:
            self.assertFails("", "manifest", "has no certificate")
        finally:
            cert.write_text(text)

    def test_missing_libcrypto(self):
        self.assertFails("ldd-no-libcrypto", "manifest", "does not resolve libcrypto")

    # 2 transcripts
    def test_transcript_mismatch(self):
        self.assertFails("served-model-differ", "transcripts", "DIFFER")

    def test_transcript_stage_killed(self):
        self.assertFails("served-socket-killed", "transcripts", "DIFFER")

    def test_transcript_image_exit(self):
        self.assertFails("image-model-exit", "transcripts", "DIFFER")

    def test_transcripts_empty_on_both_sides(self):
        self.assertFails("model-empty", "transcripts", "is empty")

    # 3 probes
    def test_probe_sbcl_exit(self):
        self.assertFails("probe-sbcl-exit", "probes", "probes.py run-sbcl exited 6")

    def test_probe_served_exit(self):
        self.assertFails("probe-served-exit", "probes", "served probe exited 7")

    def test_probe_output_truncated(self):
        self.assertFails("probe-truncated", "probes", "probes.py compare exited 1")

    # 4 store
    def test_store_rebind_exit(self):
        self.assertFails("rebind-exit", "store", "image rebind-filesystem exited 4")

    def test_store_program_exit(self):
        self.assertFails("store-served-exit", "store", "program exited 3")

    def test_store_mismatch(self):
        self.assertFails("store-differ", "store", "store-read DIFFER")

    # 5 functions: ACL2's side
    def test_acl2_exit(self):
        self.assertFails("acl2-exit", "functions", "ACL2 fcheck exited 1")

    def test_vector_file_removed(self):
        self.assertFails("acl2-missing-vec", "functions", "missing vector file")

    def test_vector_file_truncated(self):
        self.assertFails("acl2-no-trailer", "functions", "no completion trailer")

    def test_vector_counts_do_not_add_up(self):
        self.assertFails("acl2-short", "functions", "gen wrote")

    def test_zero_vectors(self):
        self.assertFails("acl2-all-guard-false", "functions", "zero vectors")

    def test_corrupted_expected_result(self):
        self.assertFails("acl2-corrupt-result", "functions", "DIFFER ACL2::")

    def test_vectors_tampered_after_manifest(self):
        self.assertFails("tamper-vectors", "functions", "is not the file the manifest names")

    def test_csc_exit(self):
        self.assertFails("csc-exit", "functions", "csc fcheck-main exited 1")

    # 5 functions: the extracted program's side
    def test_fcheck_empty_output(self):
        self.assertFails("fcheck-empty", "functions", "no FCHECK-BEGIN")

    def test_fcheck_truncated_output(self):
        self.assertFails("fcheck-truncated", "functions", "no FCHECK-COMPLETE")

    def test_fcheck_killed(self):
        self.assertFails("fcheck-killed", "functions", "killed by signal 9")

    def test_fcheck_missing_case(self):
        self.assertFails("fcheck-skip", "functions", "have no verdict (first: case 1")

    def test_fcheck_duplicate_case(self):
        self.assertFails("fcheck-duplicate", "functions", "duplicate case id 0")

    def test_fcheck_unknown_case(self):
        self.assertFails("fcheck-unknown-id", "functions", "case id 999999 is not in the manifest")

    def test_fcheck_mismatch(self):
        self.assertFails("fcheck-differ", "functions", "DIFFER ACL2::")

    def test_fcheck_raise(self):
        self.assertFails("fcheck-raise", "functions", "RAISE ACL2::FOO")

    def test_fcheck_hang(self):
        self.assertFails("fcheck-hang", "functions", "HANG ACL2::FOO")

    def test_fcheck_output_after_completion(self):
        self.assertFails("fcheck-after-complete", "functions", "a verdict after FCHECK-COMPLETE")

    def test_fcheck_last_line_without_newline(self):
        self.assertFails("fcheck-no-newline", "functions", "truncated")

    def test_fcheck_nonzero_exit_after_complete_output(self):
        self.assertFails("fcheck-exit-after", "functions", "the fcheck program exited 9")


class CheckShTest(unittest.TestCase):
    def test_usage(self):
        import subprocess
        r = subprocess.run(["sh", str(ROOT / "tools" / "extract" / "check.sh")], capture_output=True, text=True)
        self.assertEqual(r.returncode, 2)


if __name__ == "__main__":
    unittest.main()
