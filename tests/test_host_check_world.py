"""tools/host_check.py --world: a name a raw file hands to fnn-core*/fnn-call
must be defined in the world of the image that loads it.

compression-extents-2 found books/payload-lz-record outside build.lisp's world
while host/native/extent.lisp called (fnn-core 'fn-lzr-lz-read ...): "counterpart
missing" at run time, latent until a compressed handle existed.  The fixture
reproduces that shape (a book nothing the build includes defines the name).
"""
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))

import host_check                                             # noqa: E402

FILES = {
    "host/native/build.lisp": '''
(include-book "books/a")
(ld "host/h-host.lisp" :ld-error-action :error)
(progn! (set-raw-mode t)
        (load "host/native/r.lisp"))
''',
    "books/a.lisp": '''
(in-package "ACL2")
(include-book "b")
(local (include-book "c"))
(defun fn-a (x) x)
(local (defun fn-a-local (x) x))
''',
    "books/b.lisp": '(in-package "ACL2")\n(defun fn-b (x) x)\n',
    "books/c.lisp": '(in-package "ACL2")\n(defun fn-c (x) x)\n',
    "books/d.lisp": '(in-package "ACL2")\n(defun fn-d (x) x)\n'
                    '(defstobj st (fld :type integer :initially 0))\n',
    "books/e.lisp": '(in-package "ACL2")\n(defun fn-e (x) x)\n',
    "host/h-host.lisp": '''
(include-book "../books/d")
(defun fn-h (x) (declare (xargs :mode :program)) x)
''',
    "host/native/r.lisp": '''
(defun fnn-core (name &rest args) (first (apply #'fnn-call name args)))
(defun r1 (x name)
  (list (fnn-core 'fn-a x)
        (fnn-core-state 'fn-b x)
        (fnn-call 'fn-d x)
        (fnn-core 'fn-h x)
        (fnn-core 'update-fld x)
        (fnn-core (if x 'fn-b
                    'fn-e)
                  x)
        (fnn-core 'fn-c x)
        (fnn-core 'fn-a-local x)
        (fnn-core name x)))
''',
}


class WorldFixtureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.dir = tempfile.TemporaryDirectory()
        cls.root = Path(cls.dir.name)
        for name, text in FILES.items():
            path = cls.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding="utf-8")
        cls.refused, cls.notes = host_check.world_check(("host/native/build.lisp",), cls.root)

    @classmethod
    def tearDownClass(cls):
        cls.dir.cleanup()

    def test_a_name_no_included_book_defines_is_refused_by_file_line(self):
        heads = sorted(line.split(":", 2)[0] + ":" + line.split(":", 2)[1] for line in self.refused)
        self.assertEqual(heads, ["host/native/r.lisp:10 fn-e",
                                 "host/native/r.lisp:12 fn-c",
                                 "host/native/r.lisp:13 fn-a-local"])

    def test_the_world_is_includes_non_local_closure_and_ld_files(self):
        defined, raw, problems = host_check.world_of("host/native/build.lisp", self.root)
        for name in ("fn-a", "fn-b", "fn-d", "fn-h", "update-fld", "fld"):
            self.assertIn(name, defined)
        for name in ("fn-c", "fn-a-local", "fn-e"):
            self.assertNotIn(name, defined)
        self.assertEqual(raw, ["host/native/r.lisp"])
        self.assertEqual(problems, [])

    def test_a_computed_name_is_counted_not_guessed(self):
        self.assertIn("1 computed name(s)", self.notes[0])


class GeneratedNameTests(unittest.TestCase):
    def test_a_defevent_defines_its_encoder_decoder_and_recognizer(self):
        # Lane generators G6: books/owner-time-journal.lisp's defevent names
        # fn-otm-wordp, which host/native/owner.lisp calls through fnn-core.
        with tempfile.TemporaryDirectory() as directory:
            book = Path(directory) / "b.lisp"
            book.write_text('(in-package "ACL2")\n(defevent fam :version 1 :var w '
                            ':codes ((:a 1)) :encode fam-code :decode fam-kind '
                            ':code-var c :recognizer famp)\n', encoding="utf-8")
            self.assertEqual(host_check.stobj_names(book), {"fam-code", "fam-kind", "famp"})


class TreeTests(unittest.TestCase):
    def test_the_images_worlds_define_every_named_counterpart(self):
        refused, notes = host_check.world_check()
        self.assertEqual(refused, [])

    def test_the_payload_decoder_is_in_the_default_world(self):
        # The served payload read (the pooled DEFLATE decoder; LZ4 retired)
        # and the COMPRESS inflater's stobj creator, which no `def' spells.
        defined, raw, _ = host_check.world_of("host/native/build.lisp")
        self.assertIn("host/native/deflate.lisp", raw)
        self.assertIn("fn-zpl-decode-bufs", defined)
        self.assertIn("create-fn-zin-st", defined)
        self.assertIn("create-fn-zin-st", host_check.stobj_world_names())
        sites, _ = host_check.world_sites(ROOT / "host/native/deflate.lisp")
        self.assertIn("fn-zpl-decode-bufs", [name for _, name in sites])


if __name__ == "__main__":
    unittest.main()
