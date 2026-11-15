"""Narrow evidence insertion and cut/wire controls; no native image launched."""
import importlib.util
import hashlib
import tempfile
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

    def test_device_hook_is_optional_and_preserves_selected_main(self):
        source = (HERE.parent / "tools/image-node.lsp").read_bytes()
        control = b'(load "tests/native-control-capture.lsp")\n'
        device = b'(load "tests/native-device-effects-capture.lsp")\n'
        self.assertNotIn(device, launcher.instrument(source))
        selected = launcher.instrument(source, device_effects=True)
        self.assertEqual(selected.count(device), 1)
        self.assertEqual(selected.replace(control, b"").replace(device, b""), source)
        env = campaign.captured_env(Path("/tmp/fixture.trace"), b"abc", True)
        self.assertEqual(env["FN2_TEST_DEVICE_EFFECTS"], "/tmp/fixture.effects")
        self.assertNotIn("FN2_TEST_DEVICE_EFFECTS", campaign.captured_env(Path("/tmp/fixture.trace"), b"abc"))

    def test_image_observation_retains_exact_bytes_without_overwrite(self):
        with tempfile.TemporaryDirectory() as directory:
            source, target = Path(directory) / "node.img", Path(directory) / "snapshot.img"
            data = bytes(range(256)) * 4097
            source.write_bytes(data)
            receipt = campaign.image_observation(source, target)
            self.assertEqual(source.read_bytes(), data)
            self.assertEqual(target.read_bytes(), data)
            self.assertEqual(receipt["sha256"], hashlib.sha256(data).hexdigest())
            self.assertEqual(receipt["bytes"], len(data))
            with self.assertRaises(FileExistsError):
                campaign.image_observation(source, target)

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
