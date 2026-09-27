"""The host entry guard on the saved developer image (lane entry-guards).

Every call from the raw host into ACL2 passes through fnn-call
(host/native/io.lisp), which first checks the entry's arity and the KIND
conjuncts of the entry's own ACL2 guard (books/payload-kinds.lisp
*fn-entry-guard-kinds*) on the actual arguments.  On 2026-09-27 six defects
handed an entry an arena HANDLE (a natural) where it meant the article's
OCTETS, or the wrong number of arguments, and each surfaced as a silent
refusal downstream.  These cases hand the image's own entries exactly those
wrong values and assert the refusal is the named fault, raised before the
entry runs: "host-entry-guard: ENTRY argument N (FORMAL) must be KIND".

The subject is the image's fnn-call (the dispatcher every fnn-core* wrapper
applies), evaluated in the saved core before the image's own entry starts.
"""
import os
from pathlib import Path
import re
import shlex
import subprocess
import unittest

ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get(
    "FN_NATIVE_DEVELOPER_HOST", ROOT / "build" / "fn-host-developer"))


def image_command(forms):
    """The image's runtime and core, with FORMS evaluated in place of its entry."""
    text = IMAGE.read_text()
    line = next(l for l in text.splitlines() if l.startswith("exec "))
    words = shlex.split(line.replace("${SBCL_USER_ARGS}", ""))[1:]
    runtime = words[:words.index("--end-runtime-options") + 1]
    env = {k: v for k, v in os.environ.items() if not k.startswith(("FN_NATIVE_", "SBCL_"))}
    home = re.search(r"SBCL_HOME='([^']*)'", text)
    if home:
        env["SBCL_HOME"] = home.group(1)
    argv = runtime + ["--no-userinit", "--disable-debugger"]
    for form in forms:
        argv += ["--eval", form]
    argv += ["--eval", "(sb-ext:exit :code 0 :abort t)", "--end-toplevel-options"]
    return argv, env


# One probe: call the entry through the dispatcher and print what came back:
# the named guard fault, another condition, or the value.
PROBE = """(in-package "ACL2")
(format t "~&PROBE ~a ~a~%" {label!r}
  (handler-case (progn (fnn-core '{entry} {args}) "returned")
    (fnn-entry-guard-fault (c) (format nil "GUARD[~a]" (fnn-message c)))
    (serious-condition (c) (format nil "OTHER[~a]" c))))"""


def probe(label, entry, args):
    return PROBE.replace("{label!r}", '"' + label + '"').replace(
        "{entry}", entry).replace("{args}", args)


@unittest.skipUnless(IMAGE.is_file(), "no developer image (FN_NATIVE_DEVELOPER_HOST)")
class NativeEntryGuardTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        forms = [
            '(in-package "ACL2")',
            # the handle-for-octets defect: an arena handle where octets are meant
            probe("handle", "fn-store-record-txid", "7"),
            # an octet VECTOR (the host's own representation) where ACL2 wants a list
            probe("vector", "fn-store-record-txid",
                  "(make-array 2 :element-type '(unsigned-byte 8) :initial-element 1)"),
            # the wrong argument count
            probe("arity", "fn-store-record-txid", "'(1 2) 3"),
            # a length where a length is meant, octets where octets are: admitted
            probe("octets", "fn-store-record-txid", "'(1 2 3)"),
            # a handle in the second position of a two-kind entry
            probe("second", "fn-owner-transit-decide", "'(54 54 97) 7 *the-live-state*"),
        ]
        argv, env = image_command(forms)
        result = subprocess.run(argv, env=env, cwd=ROOT, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=300, check=False)
        cls.output = result.stdout.decode("utf-8", "replace")
        cls.code = result.returncode
        cls.answers = dict(re.findall(r"^PROBE (\S+) (.*)$", cls.output, re.M))

    def answer(self, label):
        self.assertIn(label, self.answers, self.output[-3000:])
        return self.answers[label]

    def test_a_handle_where_octets_are_meant_is_refused_by_name(self):
        self.assertEqual(
            self.answer("handle"),
            "GUARD[host-entry-guard: fn-store-record-txid argument 1 (octets) must be "
            "octets (a NIL-terminated list of bytes, not a payload handle) "
            "(fn-cbor-octet-listp); the host passed the natural 7]")

    def test_an_octet_vector_is_refused_by_name(self):
        self.assertIn("argument 1 (octets) must be octets", self.answer("vector"))
        self.assertIn("a vector of 2 elements", self.answer("vector"))

    def test_the_wrong_argument_count_is_refused_by_name(self):
        self.assertEqual(
            self.answer("arity"),
            "GUARD[host-entry-guard: fn-store-record-txid takes 1 argument (stobjs and "
            "state included); the host passed 2]")

    def test_the_right_kind_reaches_the_entry(self):
        # not the guard: the entry ran and answered (a malformed record's
        # verdict is the entry's own, whatever it is)
        self.assertFalse(self.answer("octets").startswith("GUARD["), self.answer("octets"))

    def test_the_position_is_named(self):
        self.assertTrue(self.answer("second").startswith(
            "GUARD[host-entry-guard: fn-owner-transit-decide argument 2 (subject-octets) "
            "must be octets"),
            self.answer("second"))


if __name__ == "__main__":
    unittest.main()
