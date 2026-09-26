"""The attach-stobj prototype in the developer image (wave 5, lane
consolidation-design, 2026-09-26; the design's section 3).

books/proto-catalog.lisp introduces `fn-pcat', an ATTACHABLE abstract stobj
whose logical side is the arena's (books/payload-arena.lisp) and whose own
foundation is a one-field list; books/proto-catalog-arena.lisp evaluates
`(attach-stobj fn-pcat fn-arena)' before including it, so in an image that
includes the arena book `fn-pcat' executes with the arena's byte array as
its foundation while every theorem about it (books/proto-catalog-fold.lisp,
certified once against the generic) is unchanged.

The witness: the developer verb `proto-catalog` (host/native/proto-catalog.lisp)
runs the fold on the image's live `fn-pcat' and prints ACL2's values with
the live foundation's field count: five is the arena's concrete stobj
(buf, off, size, count, fill), one would be the generic's own.  The
production image does not register the verb.
"""
import os
from pathlib import Path
import subprocess
import unittest

from tests import test_native_operator_verbs as verbs

ROOT = verbs.ROOT
DEVELOPER = verbs.DEVELOPER
PRODUCTION = Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host"))


def invoke(image, *words):
    return subprocess.run(
        [str(image), "--fn", *words], cwd=ROOT, env=verbs.environment(),
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120, check=False)


class ProtoCatalogSourceTests(unittest.TestCase):
    def test_the_image_attaches_the_arena_before_introducing_the_generic(self):
        arena = (ROOT / "books" / "proto-catalog-arena.lisp").read_text(encoding="ascii")
        # The events at column 0, not the comment's mention of them.
        attach = arena.index("\n(attach-stobj fn-pcat fn-arena)")
        self.assertLess(arena.index('\n(include-book "payload-arena")'), attach)
        self.assertLess(attach, arena.index('\n(include-book "proto-catalog")'))
        generic = (ROOT / "books" / "proto-catalog.lisp").read_text(encoding="ascii")
        self.assertIn(":attachable t", generic)
        build = (ROOT / "host" / "native" / "build.lisp").read_text(encoding="ascii")
        self.assertIn('(include-book "books/proto-catalog-arena")', build)
        self.assertIn('(load "host/native/proto-catalog.lisp")', build)
        host = (ROOT / "host" / "native" / "proto-catalog.lisp").read_text(encoding="ascii")
        self.assertIn('(fnn-register-developer-verb "proto-catalog"', host)
        self.assertIn("(fnn-call 'fn-pcat-smoke live)", host)


@unittest.skipUnless(verbs.executable(DEVELOPER),
                     "build the developer native image (FN_NATIVE_DEVELOPER_HOST)")
class ProtoCatalogImageTests(unittest.TestCase):
    def test_the_developer_image_runs_the_generic_over_the_arena(self):
        run = invoke(DEVELOPER, "proto-catalog", "smoke")
        self.assertEqual(run.returncode, verbs.EXIT_OK, run.stderr)
        line = run.stdout.decode("ascii").strip().splitlines()[-1]
        self.assertEqual(
            line,
            "proto-catalog count=3 total=5 payload1=(4 5) get02=3 foundation=arena fields=5")

    @unittest.skipUnless(verbs.executable(PRODUCTION),
                         "build the production native image (FN_NATIVE_HOST)")
    def test_the_production_image_does_not_register_the_verb(self):
        run = invoke(PRODUCTION, "proto-catalog", "smoke")
        self.assertNotEqual(run.returncode, verbs.EXIT_OK)
        self.assertNotIn(b"foundation=", run.stdout)
