"""D40 raw dispatch in a built image: every raw-dispatched entry is trapped.

`fn acl2 raw-traps' (developer images, host/native/acl2-session.lisp) calls
each raw-dispatched entry's target outside a dispatcher extent -- by its
literal symbol, by a symbol interned from its name, through its function
binding, and under a binding of a same-named slot symbol (the extent is a
per-thread slot whose symbol is uninterned: host/native/raw-trap.lisp) --
and requires the trap's fault each time; the dispatcher applies the captured
function object.  Then the mechanism's own probe: served through the
dispatcher and a callback, trapped directly, interned, forged and from a
thread started inside an extent.  Every start of every image also runs
fnn-raw-dispatch-traps-intact (fnn-main), so any native that starts an image
checks no target was redefined.  That the dispatcher's calls serve is the
native matrix (POST/ARTICLE/OVER) itself.
"""
import os
import re
import subprocess
import unittest

from tests.native_harness import ROOT, environment, executable, native_image


class RawDispatchImageTests(unittest.TestCase):
    def images(self):
        found = []
        for variable in ("FN_NATIVE_DEVELOPER_HOST", "FN_NATIVE_DTN_DEVELOPER_HOST"):
            image = native_image(variable)
            if executable(image):
                found.append(image)
        if not found:
            self.skipTest("no developer image")
        return found

    def test_every_raw_dispatched_entry_is_trapped(self):
        for image in self.images():
            with self.subTest(image=str(image)):
                run = subprocess.run([str(image), "--fn", "acl2", "raw-traps"], cwd=ROOT,
                                     env=environment({}), capture_output=True, text=True,
                                     timeout=120)
                self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
                summary = re.search(r"^FN_RAW_TRAPS (\d+) intact=(\d+) bad=(\d+)$",
                                    run.stdout, re.M)
                self.assertIsNotNone(summary, run.stdout + run.stderr)
                count, intact, bad = (int(g) for g in summary.groups())
                self.assertIn("FN_RAW_TRAP_PROBE dispatch=served callback=served direct=trapped "
                              "interned=trapped forged=trapped thread=trapped", run.stdout)
                self.assertEqual((intact, bad), (count, 0), run.stdout)
                rows = re.findall(r"^FN_RAW_TRAP (\S+) (.*)$", run.stdout, re.M)
                self.assertEqual(len(rows), count, run.stdout)
                for name, fields in rows:
                    self.assertEqual(
                        fields,
                        "direct=trapped interned=trapped binding=trapped forged=trapped "
                        "dispatch=captured", name)
                if os.environ.get("FN_RAW_DISPATCH_EXPECT"):
                    expected = set(os.environ["FN_RAW_DISPATCH_EXPECT"].split(","))
                    self.assertLessEqual(expected, {name for name, _ in rows}, run.stdout)


if __name__ == "__main__":
    unittest.main()
