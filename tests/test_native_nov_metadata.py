"""D27 NOV metadata: exact saved-core scalars and real served row counts.

The scalar fixture supplies wide metadata to the actual image renderer; it
makes no claim to have allocated an article of that size. The socket fixture
checks metadata against the article actually retained by the node.
"""
import os
from pathlib import Path
import re
import shlex
import subprocess
import unittest

from tests.native_harness import EXIT, Node, article, native_image, requires

IMAGE = native_image("FN_NATIVE_HOST")
ROOT = Path(__file__).resolve().parent.parent


@requires(IMAGE)
class NativeNovMetadata(unittest.TestCase):
    def test_saved_core_wide_metadata(self):
        wrapper = Path(IMAGE).read_text()
        line = next(line for line in wrapper.splitlines() if line.startswith("exec "))
        words = shlex.split(line.replace("${SBCL_USER_ARGS}", ""))[1:]
        runtime = words[:words.index("--end-runtime-options") + 1]
        env = dict(os.environ)
        home = re.search(r"SBCL_HOME='([^']*)'", wrapper)
        if home:
            env["SBCL_HOME"] = home.group(1)
        result = subprocess.run(
            runtime + ["--no-userinit", "--disable-debugger", "--load",
                       str(ROOT / "tests/native_nov_metadata_image.lisp")],
            cwd=ROOT, env=env, capture_output=True, timeout=60, check=False)
        self.assertEqual(result.returncode, EXIT.OK, result.stdout + result.stderr)
        self.assertIn(b"NATIVE-NOV-METADATA exact wide", result.stdout)

    def test_served_metadata_matches_retained_article(self):
        node = Node(self, IMAGE)
        node.init("fn.test")
        node.start()
        msgid = "<nov-metadata@example.invalid>"
        wire = article(msgid, groups="fn.test", subject="metadata", body="one\r\ntwo\r\n")
        with node.session() as client:
            opened, committed = client.post(wire)
            self.assertTrue(opened.startswith(b"340"), opened)
            self.assertTrue(committed.startswith(b"240"), committed)
            self.assertTrue(client.command("GROUP fn.test").startswith(b"211"))
            status, retained = client.multiline("ARTICLE " + msgid)
            self.assertTrue(status.startswith(b"220"), status)
            status, overview = client.multiline("OVER 1")
            self.assertTrue(status.startswith(b"224"), status)
            fields = overview.rstrip(b"\r\n").split(b"\t")
            self.assertEqual(len(fields), 9, overview)
            self.assertTrue(fields[8].startswith(b"Xref: "), overview)
            self.assertEqual(fields[0], b"1")
            self.assertEqual(fields[1], b"metadata")
            self.assertEqual(fields[4], msgid.encode())
            # ARTICLE leads with this node's synthesized Xref (PRF-243);
            # it is not part of the retained payload counted by :bytes.
            self.assertTrue(retained.startswith(fields[8] + b"\r\n"), retained)
            retained = retained.split(b"\r\n", 1)[1]
            self.assertEqual(fields[6], str(len(retained)).encode())
            body = retained.split(b"\r\n\r\n", 1)[1]
            self.assertEqual(fields[7], str(body.count(b"\r\n")).encode())
        node.stop(EXIT.OK)
