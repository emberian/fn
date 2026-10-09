"""bp-checkpoint-open: build the SCN-077 first-half fixture (1,311 held rows)
at a fixed path, snapshot it before and after the rotation."""
import os, sys, time, unittest, subprocess, shutil
sys.path.insert(0, os.getcwd())
from pathlib import Path
import tests.test_bp_fragment_node_native as bp_native
from tests.test_bp_fragment_node_native import NativeBpFragmentNodeTests as Base, IMAGE, ROOT

FIX = Path(os.environ["FIXTURE_DIR"])
WORK = FIX / "t"


class Fixture(Base):
    def setUp(self):
        # Base.setUp takes its directory from native_harness.scratch(case,
        # prefix), which registers the directory's removal; the fixture is
        # built at FIXTURE_DIR/t and kept, so it supplies that directory.
        WORK.mkdir(parents=True)
        real = bp_native.scratch
        bp_native.scratch = lambda case, prefix="": WORK
        try:
            Base.setUp(self)
        finally:
            bp_native.scratch = real

    def test_fixture(self):
        paths, total = self.author_large_fragments(10 * 1024 * 1024, 4000)
        raised = self.invoke("bp-node", "profile", self.journal, "dtn://receiver/",
                             4096, 16777216, 11 * 1024 * 1024, 1048576)
        self.assertEqual(raised.returncode, 0, raised.stderr)
        order = list(reversed(range(len(paths))))
        half = len(paths) // 2
        first, port = self.start_receiver(once=False)
        drained = self.drain(first)
        self.send_many(port, order[:half], paths)
        first.kill(); drained(120)
        print(f"FIXTURE sent={half} of {len(paths)}", flush=True)
        subprocess.run(["tar", "-C", str(FIX), "-cf", str(FIX / "pre-rotation.tar"), "t"], check=True)
        env = dict(self.env); env["FN_BP_TEST_PROFILE"] = "999999"
        t = time.monotonic()
        p = subprocess.run([str(IMAGE), "--fn", "bp-node", "checkpoint", str(self.journal),
                            "dtn://receiver/"], cwd=ROOT, env=env,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=7200)
        print(f"FIXTURE rotation rc={p.returncode} wall={time.monotonic()-t:.1f}s", flush=True)
        self.assertEqual(p.returncode, 0, p.stderr[-2000:])
        subprocess.run(["tar", "-C", str(FIX), "-cf", str(FIX / "post-rotation.tar"), "t"], check=True)
        print("FIXTURE-DONE", flush=True)


if __name__ == "__main__":
    unittest.main(argv=[sys.argv[0], "Fixture.test_fixture"], verbosity=2)
