"""Source boundary controls; these do not qualify the ACL2 declaration."""
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import certs
from lisp_rewrite import match, parse, flat


class SimulatorFaultBoundary(unittest.TestCase):
    def test_one_family_and_preserved_meanings(self):
        source = parse(ROOT / "sim/faults.lisp")
        families = match("(fn2-fault ?*entries)", source.forms)
        self.assertEqual(len(families), 1)
        entries = {row.items[0].text: int(row.items[1].text)
                   for row in families[0].node.items[1:]}
        names = ("fragment short-send delay reset half-open nonreading read-io bitrot "
                 "misread miswrite lying-flush tear no-space dead fail-slow crash "
                 "monotonic-jump realtime-back duplicate stale forged overcount "
                 "malformed flush-io short-write release-order none").split()
        self.assertEqual({":" + name: entries[":" + name] for name in names},
                         {":" + name: index for index, name in enumerate(names)})
        self.assertFalse(match("(fn2-fault ?*entries)", parse(ROOT / "books/operations.lisp").forms))
        declarations = match("(fn2-declare ?name ?fields ?span ?events)", source.forms)
        self.assertEqual(len(declarations), 1)
        self.assertEqual(flat(declarations[0].captures["name"]), "'(:operation-set fn2-sim-faults)")

    def test_fault_edit_changes_only_simulator_closure(self):
        with certs.closure_scope():
            served = certs.closure(ROOT, "books/assembly-init")
            simulated = certs.closure(ROOT, "sim/sim")
        self.assertNotIn("sim/faults", served)
        self.assertIn("sim/faults", simulated)
        with tempfile.TemporaryDirectory(prefix="fn-fault-boundary-") as directory:
            root = Path(directory)
            for name in set(served) | set(simulated):
                target = root / (name + ".lisp")
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / (name + ".lisp"), target)
            before = [certs.closure_key(root, name)[0]
                      for name in ("books/assembly-init", "sim/sim")]
            with (root / "sim/faults.lisp").open("a") as output:
                output.write("\n(defconst *fn-fault-boundary-probe* 1)\n")
            after = [certs.closure_key(root, name)[0]
                     for name in ("books/assembly-init", "sim/sim")]
            self.assertEqual(before[0], after[0])
            self.assertNotEqual(before[1], after[1])


if __name__ == "__main__":
    unittest.main()
