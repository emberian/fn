"""Opt-in native case: the open refuses a pre-C1 control record by name (PKT-444 (1)).

The fixture tests/fixtures/pre-c1-control-store/witness is the store the
pre-C1 developer image f358dbac (9ffef4ac's first parent 19cf7397) wrote on
hbox (control-across-peers, prec1_replay.py, log prec1-replay-control.log
1c7b10de...): a keyring snapshot, a signed target in fn.test and a signed
cancel of it that the pre-C1 image filed under its Newsgroups (fn.test).
`ordinary` is the same procedure without the cancel (prec1-replay-ordinary.log
56d8a925...).  Each case opens a fresh copy; the fixture is never modified.

The current image refuses every open of the witness by name, exit 1
(specs/host.md "CLI exit codes": a refusal), never the generic fault
(exit 4) it answered before: `store ROOT recover`, `store ROOT inspect`,
`store ROOT checkpoint`, `operator CONFIG run` (the owner's start) and the
offline `operator CONFIG health`.  The line is ACL2's
(books/store-open-pre-c1.lisp fn-sopc-refusal-text over
fn-sopc-classified-open, the open host/store-node-host.lisp
fn-store-sn-open-extended runs; theorem
fn-replay-never-faults-on-a-pre-c1-control-record).  `store ROOT
repair-control` exists and refuses (its semantics wait on ember, PKT-444).
The ordinary store opens (fn-sopc-classified-open-is-the-open-without-a-
pre-c1-record).

Run: FN_NATIVE_HOST=<launcher> python3 -m unittest -v tests.test_native_pre_c1_open
"""

import os
from pathlib import Path
import shutil
import socket
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
FIXTURE = ROOT / "tests" / "fixtures" / "pre-c1-control-store"
IMAGE_TEXT = os.environ.get("FN_NATIVE_HOST")
IMAGE = (Path(IMAGE_TEXT) if IMAGE_TEXT else
         next((p for p in (ROOT / "build" / "fn-host-developer", ROOT / "build" / "fn-host")
               if p.is_file()), None))
READY = bool(IMAGE is not None and IMAGE.is_file() and os.access(IMAGE, os.X_OK))

LINE = ("pre-C1 control record (txid 2, <prec1-cancel@example.invalid>): "
        "run store repair-control")
REFUSED = 1


def free_port():
    with socket.socket() as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


@unittest.skipUnless(READY, "set FN_NATIVE_HOST to a saved native image")
class PreC1OpenTest(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="fn-pre-c1-"))
        self.addCleanup(shutil.rmtree, self.tmp, True)
        self.env = dict(os.environ, ACL2_CUSTOMIZATION="NONE")

    def copy(self, name):
        store = self.tmp / name / "store"
        shutil.copytree(FIXTURE / name, store)
        (store / "staging").mkdir()
        (store / "writer.lock").touch()
        for path in [store, *store.rglob("*")]:
            path.chmod(0o700 if path.is_dir() else 0o600)
        return store

    def fn(self, *args):
        r = subprocess.run([str(IMAGE), "--fn", *map(str, args)], cwd=ROOT, env=self.env,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=300)
        out = (r.stdout + r.stderr).decode("utf-8", "replace")
        print("$ fn", *args, "->", r.returncode, "\n" + out.strip())
        return r.returncode, out

    def config(self, store):
        cfg = store.parent / "fn.toml"
        cfg.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n'
                       '[control]\npath = "%s"\n'
                       % (store, free_port(), store.parent / "control.sock"))
        return cfg

    def assert_named(self, rc, out, prefix):
        self.assertEqual(rc, REFUSED, out)
        self.assertIn(prefix + LINE, out)
        self.assertNotIn("ACL2 replay rejected", out)

    def test_every_open_of_the_witness_refuses_by_name(self):
        store = self.copy("witness")
        self.assert_named(*self.fn("store", store, "recover"), "store: ")
        self.assert_named(*self.fn("store", store, "inspect", "<prec1-target@example.invalid>"),
                          "store: ")
        self.assert_named(*self.fn("store", store, "checkpoint"), "store: ")
        cfg = self.config(store)
        self.assert_named(*self.fn("operator", cfg, "run"), "refused operator run ")
        self.assert_named(*self.fn("operator", cfg, "health"), "refused operator health ")
        # Refused, never mutated: the transactions are the fixture's octets.
        for name in ("00000000000000000000.txn", "00000000000000000001.txn",
                     "00000000000000000002.txn"):
            self.assertEqual((store / "transactions" / name).read_bytes(),
                             (FIXTURE / "witness" / "transactions" / name).read_bytes())

    def test_repair_control_refuses_until_its_semantics_are_decided(self):
        store = self.copy("witness")
        rc, out = self.fn("store", store, "repair-control")
        self.assertEqual(rc, REFUSED, out)
        self.assertIn("store: repair semantics undecided (PKT-444)", out)

    def test_the_store_without_the_cancel_opens(self):
        store = self.copy("ordinary")
        rc, out = self.fn("store", store, "recover")
        self.assertIn("recovered transactions=2", out)
        self.assertNotIn("pre-C1", out)
        rc, out = self.fn("store", store, "status")
        self.assertEqual(rc, 0, out)


if __name__ == "__main__":
    unittest.main()
