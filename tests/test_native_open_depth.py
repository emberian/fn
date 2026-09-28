"""PKT-876: a registered fixture store opens at the deployed control stack.

A node's every thread, the main one included, runs on the control stack the
installed launcher passes (books/heap-reservation.lisp fn-heap-stack-kib,
1,024 KiB), and since lane open-depth so does every native test: the image's
own launcher carries the same figure (tools/build_native_host.sh).  At that
stack a full-replay open of syn100k-2k (100,000 retained articles) died in
30,527 frames of fn-retain-obligation-ids, one of the per-article walks under
the node recognizer the open runs (fn-cnode-statep from fn-sco-cpr-finish;
lane thread-stacks).  Here each named fixture is copied, rebound to this
filesystem, and opened by the owner (`operator CONFIG run`):

* by full replay (the fixture has no checkpoint): the owner LISTENs, a
  connection is greeted and answers DATE, and the owner stops cleanly with
  no stack exhaustion;
* on a second copy, from a checkpoint `operator CONFIG store checkpoint'
  writes first, the open line naming it: the same.

Each open's seconds to LISTENING are printed (`OPEN-DEPTH NAME MODE
seconds=S`).  The fixtures live on hbox (tools/fixtures.py): set
FN_OPEN_DEPTH_FIXTURES to their directory (/tank/fn/scratch/fixtures) and
FN_OPEN_DEPTH_NAMES to a comma list (default syn100k-2k; syn1m-2k needs an
80G scope, its init reservation is 57,158 MB).  FN_OPEN_DEPTH_CHECKPOINT_STACK_KB
writes the checkpoint at another stack (with FN_TEST_CONTROL_STACK_REASON),
to ask whether an image that cannot full-replay-open can open a checkpoint.
Skips, naming the variable, without them.
"""
import os
from pathlib import Path
import select
import shutil
import socket
import subprocess
import tempfile
import time
import unittest

from tests import test_native_operator_verbs as verbs


FIXTURES = os.environ.get("FN_OPEN_DEPTH_FIXTURES")
NAMES = [n for n in os.environ.get("FN_OPEN_DEPTH_NAMES", "syn100k-2k").split(",") if n]
OPEN_SECONDS = 3600


def env_at(kib):
    env = verbs.environment()
    if kib:
        env["SBCL_USER_ARGS"] = "--control-stack-size {}KB".format(kib)
    return env


class OpenDepthTests(unittest.TestCase):
    def setUp(self):
        if not verbs.executable(verbs.IMAGE):
            self.skipTest("needs the production image {}".format(verbs.IMAGE))
        if not FIXTURES or not Path(FIXTURES).is_dir():
            self.skipTest("FN_OPEN_DEPTH_FIXTURES names no directory (hbox: /tank/fn/scratch/fixtures)")
        self.work = Path(tempfile.mkdtemp(prefix="fn-open-depth-", dir=os.environ.get("FN_OPEN_DEPTH_WORK")))
        self.addCleanup(shutil.rmtree, self.work, True)

    def prepare(self, name):
        source = Path(FIXTURES) / name / "store"
        if not source.is_dir():
            self.skipTest("no fixture store {}".format(source))
        root = self.work / name
        store = root / "store"
        shutil.copytree(source, store, symlinks=True)
        lock = store / "writer.lock"
        if not lock.exists():
            lock.touch(mode=0o600)
        rebound = subprocess.run([str(verbs.IMAGE), "--fn", "store", str(store), "rebind-filesystem"],
                                 env=verbs.environment(), stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE, timeout=600)
        self.assertEqual(rebound.returncode, 0, rebound.stderr)
        port = verbs.free_port()
        config = root / "fn.toml"
        config.write_text('[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
                          '[control]\npath = "{}"\n'.format(store, port, root / "control.sock"),
                          encoding="ascii")
        return root, config, port

    def open_and_serve(self, name, mode, root, config, port):
        err_path = root / "owner-{}.err".format(mode)
        with open(err_path, "wb") as err:
            started = time.monotonic()
            owner = subprocess.Popen([str(verbs.IMAGE), "--fn", "operator", str(config), "run"],
                                     env=verbs.environment(), stdout=subprocess.PIPE, stderr=err)
            try:
                listening = None
                while listening is None:
                    ready = select.select([owner.stdout], [], [], OPEN_SECONDS)[0]
                    self.assertTrue(ready, "no LISTENING in {} s".format(OPEN_SECONDS))
                    line = owner.stdout.readline()
                    if not line:
                        owner.wait(60)
                        self.fail("{} {}: the owner stopped at open (exit {}): {}".format(
                            name, mode, owner.returncode,
                            err_path.read_bytes()[-3000:].decode("utf-8", "replace")))
                    if line.startswith(b"LISTENING"):
                        listening = time.monotonic() - started
                opened = [l for l in err_path.read_text("utf-8", "replace").splitlines()
                          if l.startswith("OWNER-OPEN")]
                print("OPEN-DEPTH {} {} seconds={:.1f} {}".format(
                    name, mode, listening, opened[-1] if opened else "(no OWNER-OPEN line)"),
                      flush=True)
                # One command that reads no article list: the served reads
                # that walk a group's whole article list (LIST ACTIVE, GROUP:
                # fn-nntp-group-low/-high/-count) still recurse per article
                # and die at this stack past ~30,000 (PKT-877, not this
                # packet's); the open is what this module certifies.
                with socket.create_connection(("127.0.0.1", port), timeout=600) as conn:
                    f = conn.makefile("rwb")
                    self.assertTrue(f.readline().startswith(b"20"))
                    f.write(b"DATE\r\n")
                    f.flush()
                    reply = f.readline()
                    print("OPEN-DEPTH {} {} {}".format(name, mode, reply.strip().decode("ascii")),
                          flush=True)
                    self.assertTrue(reply.startswith(b"111 "), reply)
                    f.write(b"QUIT\r\n")
                    f.flush()
                return opened[-1] if opened else ""
            finally:
                if owner.poll() is None:
                    owner.terminate()
                    owner.wait(600)
                text = err_path.read_text("utf-8", "replace")
                self.assertNotIn("Control stack exhausted", text)
                self.assertEqual(owner.returncode, 0, text[-3000:])

    def test_full_replay_open_at_the_deployed_stack(self):
        for name in NAMES:
            with self.subTest(fixture=name):
                root, config, port = self.prepare(name)
                line = self.open_and_serve(name, "full-replay", root, config, port)
                self.assertIn("open=full-replay", line)

    def test_checkpoint_open_at_the_deployed_stack(self):
        kib = os.environ.get("FN_OPEN_DEPTH_CHECKPOINT_STACK_KB")
        if kib:
            self.assertTrue(os.environ.get("FN_TEST_CONTROL_STACK_REASON"),
                            "FN_OPEN_DEPTH_CHECKPOINT_STACK_KB needs FN_TEST_CONTROL_STACK_REASON")
        for name in NAMES:
            with self.subTest(fixture=name):
                root, config, port = self.prepare(name)
                started = time.monotonic()
                made = subprocess.run([str(verbs.IMAGE), "--fn", "operator", str(config), "store",
                                       "checkpoint"], env=env_at(kib), stdout=subprocess.PIPE,
                                      stderr=subprocess.PIPE, timeout=OPEN_SECONDS)
                print("OPEN-DEPTH {} store-checkpoint stack={} seconds={:.1f} exit={} {}".format(
                    name, kib or "launcher", time.monotonic() - started, made.returncode,
                    made.stdout.decode("utf-8", "replace").strip()[-200:]), flush=True)
                self.assertEqual(made.returncode, 0, made.stderr[-3000:])
                line = self.open_and_serve(name, "checkpoint", root, config, port)
                self.assertIn("open=checkpoint:", line)

if __name__ == "__main__":
    unittest.main()
