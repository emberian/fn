"""Narrow evidence insertion and cut/wire controls; no native image launched."""
import importlib.util
from pathlib import Path
import unittest

HERE = Path(__file__).resolve().parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


launcher = load("capture_launcher", HERE / "native-control-launcher.py")
campaign = load("control_campaign", HERE / "native-control-death.py")


class Markers:
    def __init__(self, lines):
        self.lines = iter(lines)

    def marker(self, prefix):
        line = next(self.lines)
        assert line.startswith(prefix)
        return line


class ControlCapture(unittest.TestCase):
    def test_selected_main_is_preserved(self):
        source = (HERE.parent / "tools/image-node.lsp").read_bytes()
        hook = b'(load "tests/native-control-capture.lsp")\n'
        self.assertEqual(launcher.instrument(source).replace(hook, b""), source)
        main = b"(sb-ext:exit :code (fn2-nserve-main))"
        for bad in (source.replace(main, b""), source + main):
            with self.assertRaises(ValueError):
                launcher.instrument(bad)

    def test_complete_independent_wire_then_exact_cut(self):
        node = Markers([b"CAPTURE-SEND 8 6162", b"CAPTURE-SEND 9 6364",
                        b"CAPTURE-CUT 9 post-recorded-before-post-boundary"])
        self.assertEqual(campaign.await_recorded(node, b"abcd"), 9)

    def test_changed_wire_or_cut_refused(self):
        for lines in ([b"CAPTURE-SEND 9 6163"],
                      [b"CAPTURE-SEND 9 6162", b"CAPTURE-CUT 10 post-recorded-before-post-boundary"],
                      [b"CAPTURE-SEND 9 6162", b"CAPTURE-CUT 9 wrong-position"]):
            with self.assertRaises(AssertionError):
                campaign.await_recorded(Markers(lines), b"ab")


if __name__ == "__main__":
    unittest.main()
