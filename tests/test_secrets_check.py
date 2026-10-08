"""tools/secrets_check.py: no live credential near an invitation word.

The refused fixture is built here, not stored: stored, it would be a
secret-shaped value in tests/ and the lint would refuse the tree.  Its
sanitized twin is tests/fixtures/secrets/accepted.md.
"""
import hashlib
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import secrets_check  # noqa: E402

CODE = hashlib.md5(b"an invitation code").hexdigest()          # 32 hex, high entropy
TOKEN = hashlib.sha256(b"a bearer").hexdigest()[:40]
# Spelled in pieces so this file itself carries no secret-shaped value.
PW, AUTH = "pass" + "word", "Author" + "ization"


def refused_text() -> str:
    return "\n".join([
        "# a lane record",                                        # 1
        "The invite code for the friend node:",                  # 2
        "",                                                      # 3
        "    " + CODE,                                           # 4
        "XREDEEM " + CODE + " robin",                            # 5
        "credentials: " + PW + "=hunter2x9",                     # 6
        "curl -H '" + AUTH + ": Bearer " + TOKEN + "'",          # 7
        '{"invitation": 1, "' + PW + '": "s3cret-9"}',           # 8
        "", "", "", "", "", "", "",                              # 9-15
        "far away: " + CODE,                                     # 16
    ])


class Rules(unittest.TestCase):
    def test_the_refused_fixture_is_refused_by_line(self):
        found = secrets_check.findings_in(refused_text())
        lines = [line for line, _ in found]
        self.assertEqual(sorted(set(lines)), [4, 5, 6, 7, 8])
        for _, what in found:
            self.assertNotIn(CODE, what)                         # never printed whole
            self.assertNotIn(TOKEN, what)
        self.assertIn(CODE[:4] + "... (32 chars)", " ".join(w for _, w in found))

    def test_the_sanitized_twin_is_accepted(self):
        path = ROOT / "tests/fixtures/secrets/accepted.md"
        self.assertEqual(secrets_check.check([path], ROOT), [])

    def test_synthetic_rule(self):
        self.assertTrue(secrets_check.synthetic_hex("1" * 32))
        self.assertTrue(secrets_check.synthetic_hex("0123" * 8))
        self.assertTrue(secrets_check.synthetic_hex("000102030405060708090a0b0c0d0efa"))
        self.assertFalse(secrets_check.synthetic_hex(CODE))

    def test_a_context_word_inside_a_name_is_not_context(self):
        text = "books/native-auth-credentials.lisp\nFN_CERTIFY_SUCCESS " + CODE + " x\n"
        self.assertEqual(secrets_check.findings_in(text), [])
        self.assertTrue(secrets_check.findings_in("the credentials\n" + CODE + "\n"))

    def test_an_evidence_path_component_is_not_a_secret(self):
        # planning/repair/repair.py names its archives <item>-<uuid4 hex>.json
        # under planning/evidence/repair/, next to the item's title words.
        path = "planning/evidence/repair/S107-" + CODE + ".json"
        self.assertEqual(secrets_check.findings_in('"credentials",\n"path": "' + path + '"'), [])
        # The same token outside the path, on the same line, is still refused.
        self.assertTrue(secrets_check.findings_in("credentials " + CODE + " " + path))
        self.assertTrue(secrets_check.findings_in("credentials docs/x-" + CODE + ".json"))

    def test_the_marker_passes_its_own_line_only(self):
        self.assertEqual(secrets_check.findings_in("invite " + CODE + "  FAKE-SECRET"), [])
        self.assertTrue(secrets_check.findings_in("invite FAKE-SECRET\n" + CODE))

    def test_files_are_checked_and_named(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "record.md"
            path.write_text(refused_text())
            refused = secrets_check.check([path], Path(directory))
            self.assertTrue(refused[0].startswith("record.md:4: a 32-hex token"))


class Tree(unittest.TestCase):
    def test_the_tree_is_clean(self):
        self.assertEqual(secrets_check.check(secrets_check.tracked_files()), [])


if __name__ == "__main__":
    unittest.main()
