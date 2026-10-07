"""RP-1: the developer image's `eval' is absent from a production image by construction.

Three checks, each a function that answers the violations it finds, so that the same function is
the claim on a production image and the tooth on a developer one:

* SURFACE.  IMAGE.surface, which tools/build_native_host.sh writes beside every image from the
  image it saved (host/native/build.lisp prints it): no `eval' word under `operator', no verb
  named eval, no FNCT kind of books/developer-eval.lisp among the kinds the control classifier
  answers for, no developer selector honoured.
* LIVE.  A running production node answers an eval request frame as it answers any frame of an
  unknown kind (the plain refusal), and a running developer node answers the same frame with an
  evaluation: the frame is well formed, so the production node's answer is the kind's absence.
* CORE.  The bytes of the core contain neither FN-DEVAL-ADMIT nor FNN-DEV-EVALUATE, in the two
  encodings SBCL stores a symbol's name in (base-string, UTF-32).

TEETH (the mutation, labelled).  The same three functions run on the developer image -- the image
built with the developer branch on -- and must report a violation each; the recorded run is in
build/coordinator/lanedumps/obs-dev-eval.md.  Each check skips, naming the file, when the image is
absent; the synthetic cases need no image.
"""
import mmap
import os
from pathlib import Path
import re
import socket
import subprocess
import sys
import tempfile
import unittest

from tests import native_harness
from tests.native_harness import (
    Acl2Session, Node, acl2_boolean, acl2_octets, executable, native_image, requires)

ROOT = native_harness.ROOT

# What the check looks for is read from the book that defines it, not copied.
BOOK = (ROOT / "books" / "developer-eval.lisp").read_text(encoding="utf-8")
EVAL_KIND = int(re.search(r"\(defconst \*fn-deval-request-kind\* (\d+)\)", BOOK).group(1))
CORE_NEEDLES = ("FN-DEVAL-ADMIT", "FNN-DEV-EVALUATE")

PRODUCTION = native_image("FN_NATIVE_HOST")
DEVELOPER = native_image("FN_NATIVE_DEVELOPER_HOST")


def parse_surface(text):
    """IMAGE.surface -> dict(profile, verbs, words {verb: [word]}, kinds [int], selectors [str])."""
    surface = {"profile": None, "verbs": [], "words": {}, "kinds": [], "selectors": []}
    for line in text.splitlines():
        parts = line.split()
        if not parts:
            continue
        if parts[0] == "profile":
            surface["profile"] = parts[1]
        elif parts[0] == "verb":
            surface["verbs"].append(parts[1])
        elif parts[0] == "verb-word":
            surface["words"].setdefault(parts[1], []).append(parts[2])
        elif parts[0] == "kind":
            surface["kinds"].append(int(parts[1]))
        elif parts[0] == "selector":
            surface["selectors"].append(parts[1])
        else:
            raise ValueError("IMAGE.surface line not understood: %r" % line)
    return surface


def surface_violations(text):
    """What IMAGE.surface lists that a production image must not."""
    surface = parse_surface(text)
    found = []
    if "eval" in surface["verbs"]:
        found.append("a verb named eval")
    for verb, words in surface["words"].items():
        if "eval" in words:
            found.append("the word `eval' under `%s'" % verb)
    if EVAL_KIND in surface["kinds"]:
        found.append("FNCT kind %d (books/developer-eval.lisp) among the kinds the classifier answers"
                     % EVAL_KIND)
    for name in surface["selectors"]:
        found.append("the developer selector %s" % name)
    return found


def core_violations(path):
    """The needles found in the bytes of the core at PATH (base-string and UTF-32 spellings)."""
    found = []
    with open(path, "rb") as handle, mmap.mmap(handle.fileno(), 0, access=mmap.ACCESS_READ) as data:
        for needle in CORE_NEEDLES:
            for encoding in ("ascii", "utf-32-le"):
                if data.find(needle.encode(encoding)) >= 0:
                    found.append("%s (%s) in %s" % (needle, encoding, path))
    return found


def request_frame(session):
    """ACL2's eval request frame for a small form (the developer image's own codec)."""
    return acl2_octets(session.call(
        "(fn-deval-request-encode (fn-record-string-octets \"(+ 1 2)\"))"))


def answer_is_the_plain_refusal(session, reply):
    """Whether REPLY is exactly the status frame a frame of an unknown kind is answered with."""
    return acl2_boolean(session.call(
        "(equal (fn-native-control-reply-encode :refused) '%s)" % session.literal(reply)))


def live_violations(case, image, session, request):
    """Start a node on IMAGE, send REQUEST to its control socket; what it answered that a
    production node would not."""
    from tests.test_native_control import control_exchange
    node = Node(case, image, name="surface-" + Path(image).name)
    node.init()
    node.start()
    reply = control_exchange(node.control, request)
    if answer_is_the_plain_refusal(session, reply):
        return []
    return ["the node answered the eval frame with %d octets that are not the plain refusal"
            % len(reply)]


class Synthetic(unittest.TestCase):
    """The surface check on written-out surfaces: no image needed."""

    PRODUCTION_SURFACE = ("profile production\nverb operator\nverb store\nverb owner\n"
                          "kind 4\nkind 5\nkind 19\nkind 24\n")

    def test_a_production_surface_passes(self):
        self.assertEqual(surface_violations(self.PRODUCTION_SURFACE), [])

    def test_each_part_of_the_developer_surface_is_named(self):
        for line, fragment in (("verb eval\n", "a verb named eval"),
                               ("verb-word operator eval\n", "`eval' under `operator'"),
                               ("kind %d\n" % EVAL_KIND, "FNCT kind %d" % EVAL_KIND),
                               ("selector FN_NATIVE_DEV_REPL\n", "FN_NATIVE_DEV_REPL")):
            found = surface_violations(self.PRODUCTION_SURFACE + line)
            self.assertEqual(len(found), 1, (line, found))
            self.assertIn(fragment, found[0])

    def test_a_developer_surface_fails_all_of_them(self):
        found = surface_violations(self.PRODUCTION_SURFACE + "verb-word operator eval\n"
                                   "kind %d\nselector FN_NATIVE_TEST_CLOCK\n" % EVAL_KIND)
        self.assertEqual(len(found), 3, found)

    def test_a_surface_line_not_understood_is_refused(self):
        with self.assertRaises(ValueError):
            parse_surface("profile production\nfrobnicate 1\n")

    def test_the_kind_is_the_books(self):
        self.assertIsInstance(EVAL_KIND, int)
        self.assertEqual(EVAL_KIND, 40)

    def test_the_core_search_finds_both_spellings(self):
        with tempfile.TemporaryDirectory() as d:
            clean = Path(d) / "clean.core"
            clean.write_bytes(b"\0" * 64 + b"FN-OTHER" + b"\0" * 64)
            self.assertEqual(core_violations(clean), [])
            for encoding in ("ascii", "utf-32-le"):
                dirty = Path(d) / ("dirty-" + encoding + ".core")
                dirty.write_bytes(b"\1" * 32 + CORE_NEEDLES[0].encode(encoding) + b"\1" * 32)
                found = core_violations(dirty)
                self.assertEqual(len(found), 1, found)
                self.assertIn(CORE_NEEDLES[0], found[0])


def beside(image, suffix):
    return Path(str(image) + suffix)


class ProductionImage(unittest.TestCase):
    """RP-1 on the production image."""

    @requires(PRODUCTION)
    def test_surface_lists_no_eval(self):
        surface = beside(PRODUCTION, ".surface")
        if not surface.is_file():
            self.skipTest("no %s (built before IMAGE.surface)" % surface)
        text = surface.read_text(encoding="utf-8")
        self.assertEqual(parse_surface(text)["profile"], "production")
        self.assertEqual(surface_violations(text), [])

    @requires(PRODUCTION)
    def test_core_bytes_contain_neither_symbol(self):
        core = beside(PRODUCTION, ".core")
        if not core.is_file():
            self.skipTest("no %s" % core)
        self.assertEqual(core_violations(core), [])

    @requires(PRODUCTION, DEVELOPER)
    def test_a_live_production_node_answers_the_eval_frame_as_an_unknown_kind(self):
        with Acl2Session(DEVELOPER) as session:
            request = request_frame(session)
            self.assertEqual(live_violations(self, PRODUCTION, session, request), [])
            self.assertTrue(acl2_boolean(session.call(
                "(consp (fn-deval-request-decode '%s))" % session.literal(request))),
                "the frame is a well formed eval request (else its refusal proves nothing)")


class FnCore(unittest.TestCase):
    """RP-1 on fn-core: the core extracted by tools/extract/core.sh (FN_EXTRACT_CORE names its
    .core file, or the launcher beside it)."""

    def core(self):
        named = os.environ.get("FN_EXTRACT_CORE")
        if not named:
            self.skipTest("FN_EXTRACT_CORE names no fn-core")
        path = Path(named)
        if path.suffix != ".core":
            path = beside(path, ".core")
        if not path.is_file():
            self.skipTest("no %s" % path)
        return path

    def test_core_bytes_contain_neither_symbol(self):
        self.assertEqual(core_violations(self.core()), [])

    def test_surface_when_the_core_has_one(self):
        surface = beside(self.core().with_suffix(""), ".surface")
        if not surface.is_file():
            self.skipTest("fn-core writes no IMAGE.surface")
        self.assertEqual(surface_violations(surface.read_text(encoding="utf-8")), [])


class TeethTheDeveloperImage(unittest.TestCase):
    """MUTATION (labelled): the developer image is the build with the developer branch on.  Every
    check above, run on it, finds what it looks for; a check that passed here would prove nothing
    about the production image.  The run of record is in the lane's lanedump."""

    @requires(DEVELOPER)
    def test_surface_check_fails_on_the_developer_surface(self):
        surface = beside(DEVELOPER, ".surface")
        if not surface.is_file():
            self.skipTest("no %s" % surface)
        found = surface_violations(surface.read_text(encoding="utf-8"))
        self.assertTrue(any("`eval'" in item for item in found), found)
        self.assertTrue(any("FNCT kind" in item for item in found), found)
        self.assertTrue(any("developer selector" in item for item in found), found)

    @requires(DEVELOPER)
    def test_core_check_fails_on_the_developer_core(self):
        core = beside(DEVELOPER, ".core")
        if not core.is_file():
            self.skipTest("no %s" % core)
        found = core_violations(core)
        self.assertTrue(any("FN-DEVAL-ADMIT" in item for item in found), found)
        self.assertTrue(any("FNN-DEV-EVALUATE" in item for item in found), found)

    @requires(DEVELOPER)
    def test_live_check_fails_on_a_developer_node(self):
        with Acl2Session(DEVELOPER) as session:
            request = request_frame(session)
            found = live_violations(self, DEVELOPER, session, request)
            self.assertEqual(len(found), 1, found)


if __name__ == "__main__":
    unittest.main()
