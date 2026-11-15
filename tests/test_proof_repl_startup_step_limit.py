"""Exercise startup ordering and fail-closed setup without running ACL2."""
import contextlib
import io
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import proof_repl as repl


class StartupStepLimit(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.directory = Path(self.tmp.name) / "session"
        self.events = []
        self.acl2 = mock.Mock(pgid=123, protocol_error=None)
        self.acl2.send.side_effect = self.send
        self.acl2.alive.return_value = False
        self.response = (" :OK\n", False)
        self.socket = mock.Mock()

    def send(self, command, timeout):
        self.events.append(("send", command, timeout))
        return self.response

    def load(self, acl2, book, state, *args, **kwargs):
        self.assertIs(acl2, self.acl2)
        self.events.append(("load", book))
        return True

    def run_serve(self, value):
        with contextlib.ExitStack() as stack:
            stack.enter_context(mock.patch.dict(os.environ, {}, clear=False))
            if value is None:
                os.environ.pop("FN_REPL_STEP_LIMIT", None)
            else:
                os.environ["FN_REPL_STEP_LIMIT"] = value
            stack.enter_context(mock.patch.object(repl, "session_dir", return_value=self.directory))
            stack.enter_context(mock.patch.object(repl, "sock_file", return_value=self.directory / "socket"))
            stack.enter_context(mock.patch.object(repl, "Acl2", return_value=self.acl2))
            stack.enter_context(mock.patch.object(repl, "load_book", side_effect=self.load))
            stack.enter_context(mock.patch.object(repl, "note_lock_holder"))
            stack.enter_context(mock.patch.object(repl.signal, "signal"))
            self.socket_factory = stack.enter_context(mock.patch.object(repl.socket, "socket", return_value=self.socket))
            fd = os.open(os.devnull, os.O_RDONLY)
            return repl.serve("cap", "books/target", None, None, 60, 19, fd,
                              ld=["books/dependency"], idle_seconds=0)

    def assert_closed(self):
        self.acl2.kill.assert_called_once_with()
        self.socket_factory.assert_not_called()
        self.assertFalse(any(event[0] == "load" for event in self.events))
        state = json.loads((self.directory / "state.json").read_text())
        self.assertFalse(state["ready"])
        self.assertNotIn("prover_step_limit", state)

    def test_cap_precedes_dependency_and_target(self):
        self.assertEqual(self.run_serve("1000"), 0)
        self.assertEqual(self.events, [("send", "(set-prover-step-limit 1000)", 19),
                                       ("load", "books/dependency"), ("load", "books/target")])
        state = json.loads((self.directory / "state.json").read_text())
        self.assertEqual(state["prover_step_limit"], 1000)

    def test_unset_does_not_send_setup(self):
        self.assertEqual(self.run_serve(None), 0)
        self.assertEqual(self.events, [("load", "books/dependency"), ("load", "books/target")])

    def test_invalid_values_never_load_or_expose_socket(self):
        for value in ("", "0", "-1", "1.5", "one", " 10"):
            with self.subTest(value=value):
                self.acl2.reset_mock()
                self.events.clear()
                with self.assertRaisesRegex(ValueError, "positive integer"):
                    self.run_serve(value)
                self.assertEqual(self.events, [])
                self.assert_closed()

    def test_refused_setup_fails_closed(self):
        self.response = ("ACL2 Error: refused step limit", False)
        with self.assertRaisesRegex(RuntimeError, "refused the startup prover step limit"):
            self.run_serve("1000")
        self.assert_closed()

    def test_timed_out_setup_fails_closed(self):
        self.response = ("partial setup output", True)
        with self.assertRaisesRegex(RuntimeError, "refused the startup prover step limit"):
            self.run_serve("1000")
        self.assert_closed()

    def test_start_help_explains_environment_cap(self):
        output = io.StringIO()
        with contextlib.redirect_stdout(output), self.assertRaises(SystemExit) as stopped:
            repl.main(["start", "--help"])
        self.assertEqual(stopped.exception.code, 0)
        self.assertIn("FN_REPL_STEP_LIMIT=N", output.getvalue())
        self.assertIn("before source dependencies", " ".join(output.getvalue().split()))


if __name__ == "__main__":
    unittest.main()
