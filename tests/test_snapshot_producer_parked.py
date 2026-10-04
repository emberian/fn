"""host/native/snapshot-producer.lisp says it is parked while its callees do not exist (sweep S111)."""
import pathlib
import re
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
FILE = ROOT / "host" / "native" / "snapshot-producer.lisp"
UNDEFINED = ("fnn-snapshot-source-begin", "fnn-hsr-source-begin", "fnn-hsr-cold-step",
             "fnn-hpi-offer", "fnn-hpi-action")


def defined_anywhere(name):
    pattern = re.compile(r"\(def(?:un|macro|generic)\s+" + re.escape(name) + r"[\s)]")
    for pattern_dir in ("host", "books"):
        for path in (ROOT / pattern_dir).rglob("*.lisp"):
            if pattern.search(path.read_text(encoding="utf-8", errors="replace")):
                return True
    return False


class SnapshotProducerParkedTests(unittest.TestCase):
    def test_header_declares_the_file_parked_and_names_what_is_undefined(self):
        text = FILE.read_text(encoding="utf-8")
        header = "\n".join(line for line in text.splitlines()[:12] if line.startswith(";"))
        if "PARKED" not in header:
            self.fail("snapshot-producer.lisp describes itself as the actual capture but no build loads it and it calls undefined functions")
        for name in UNDEFINED:
            self.assertIn(name, header, name + " is undefined and the header must name it")

    def test_the_named_functions_are_still_undefined(self):
        # When one lands the header is stale: update it (and this list) in that change.
        landed = [name for name in UNDEFINED if defined_anywhere(name)]
        self.assertEqual(landed, [], "defined now; the PARKED header must be revised: " + ", ".join(landed))


if __name__ == "__main__":
    unittest.main()
