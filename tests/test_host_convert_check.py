"""tools/host_convert_check.py and host_check --load's world check (obstructions-5 item 34)."""
import contextlib
import io
import sys
import unittest
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import host_check  # noqa: E402
import host_convert_check  # noqa: E402


class GateTests(unittest.TestCase):
    def run_gates(self, codes, files=()):
        seen = []

        def runner(command):
            seen.append(command[1:])
            return codes.get(command[1] + " " + " ".join(command[2:3]), 0)
        with contextlib.redirect_stdout(io.StringIO()) as out:
            code = host_convert_check.run(list(files), runner)
        return code, out.getvalue(), seen

    def test_all_six_gates_run_in_order_and_file_reaches_load(self):
        code, out, seen = self.run_gates({}, ["host/native/x.lisp"])
        self.assertEqual(code, 0)
        self.assertEqual([one[0] for one in seen],
                         ["tools/extract/world.py", "tools/interface_emit.py"]
                         + ["tools/host_check.py"] * 4)
        self.assertEqual(seen[4], ["tools/host_check.py", "--load", "host/native/x.lisp"])
        self.assertEqual(seen[5], ["tools/host_check.py"])  # the certified-world default
        self.assertIn("GREEN", out)

    def test_a_stale_world_is_red_and_the_rest_still_run(self):
        code, out, seen = self.run_gates({"tools/extract/world.py --check": 1})
        self.assertEqual((code, len(seen)), (1, 6))
        self.assertIn("world FAIL: python3 tools/extract/world.py", out)
        self.assertIn("RED (1 of 6)", out)

    def test_a_class_gate_that_did_not_run_is_red(self):
        code, out, _ = self.run_gates({"tools/host_check.py ": 2})
        self.assertEqual(code, 1)
        self.assertIn("class NOT RUN", out)

    def test_it_refuses_the_laptop(self):
        with mock.patch("socket.gethostname", lambda: "laptop"), \
                mock.patch.dict("os.environ", {"FN_LAPTOP_OK": ""}):
            with self.assertRaises(SystemExit) as refused:
                host_convert_check.main([])
        self.assertIn("build box", str(refused.exception))

    def test_the_make_target_exists(self):
        text = (ROOT / "Makefile").read_text()
        self.assertIn("host-convert-check:\n\t@$(PYTHON) tools/host_convert_check.py $(FILE)", text)


class LoadRunsWorldCheckTests(unittest.TestCase):
    def test_world_stale_prints_fail_lines(self):
        with contextlib.redirect_stdout(io.StringIO()) as out:
            found = host_check.world_stale(lambda: (1, "world.py: books/image-world.lisp is not ...\n"))
        self.assertEqual(len(found), 1)
        self.assertIn("FAIL world.py: books/image-world.lisp", out.getvalue())
        self.assertIn("STALE (1)", out.getvalue())

    def test_a_stale_world_makes_a_clean_load_red(self):
        with mock.patch.object(host_check, "world_stale", lambda: ["stale"]), \
                mock.patch.object(host_check, "forward_references", lambda build: []), \
                mock.patch.object(host_check, "executable", lambda: Path("/bin/true")), \
                mock.patch.object(host_check, "raw_load_order", lambda build: ["a.lisp"]), \
                mock.patch.object(host_check, "load_check", lambda *a: 0), \
                contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(host_check.main(["--load"]), 1)

    def test_a_current_world_keeps_a_clean_load_green(self):
        with mock.patch.object(host_check, "world_stale", lambda: []), \
                mock.patch.object(host_check, "forward_references", lambda build: []), \
                mock.patch.object(host_check, "executable", lambda: Path("/bin/true")), \
                mock.patch.object(host_check, "raw_load_order", lambda build: ["a.lisp"]), \
                mock.patch.object(host_check, "load_check", lambda *a: 0), \
                contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(host_check.main(["--load"]), 0)


if __name__ == "__main__":
    unittest.main()
