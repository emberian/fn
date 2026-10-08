"""tools/host_check.py --world: a name a raw file hands to fnn-core*/fnn-call
must be defined in the world of the image that loads it.

compression-extents-2 found books/payload-lz-record outside build.lisp's world
while host/native/extent.lisp called (fnn-core 'fn-lzr-lz-read ...): "counterpart
missing" at run time, latent until a compressed handle existed.  The fixture
reproduces that shape (a book nothing the build includes defines the name).

Also --attach-order (red and green on a fixture tree) and --build-lists
(native-subsets-6c0626c5 failure 2: build-dtn.lisp lacked an `ld` io.lisp
needs; each clause of the check fails without its premise).
"""
import contextlib
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
sys.path.insert(0, str(ROOT))

import host_check                                             # noqa: E402
from tools import commit_map  # noqa: E402

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


def tree(host_includes):
    d = Path(tempfile.mkdtemp())
    (d / "books").mkdir()
    (d / "host/native").mkdir(parents=True)
    w = lambda p, s: (d / p).write_text(s)
    w("books/impl.lisp", "(in-package \"ACL2\")\n")
    w("books/gen.lisp", "(in-package \"ACL2\")\n(defabsstobj fn-x\n  :attachable t)\n")
    w("books/gen-attach.lisp", "(in-package \"ACL2\")\n(include-book \"impl\")\n"
      "(attach-stobj fn-x fn-x-impl)\n(include-book \"gen\")\n")
    w("books/above.lisp", "(in-package \"ACL2\")\n(include-book \"gen\")\n")
    w("host/native/build.lisp", "(include-book \"books/gen-attach\")\n")
    w("host/h-host.lisp", "(in-package \"ACL2\")\n" + host_includes)
    w("books/image-world.lisp", "(in-package \"ACL2\")\n(include-book \"../host/h-host\")\n")
    return d


class AttachOrder(unittest.TestCase):
    def test_red_generic_without_attach(self):
        f = host_check.attach_findings(tree('(include-book "../books/above")\n'))
        self.assertEqual(len(f), 1)
        self.assertIn("host/h-host.lisp", f[0])

    def test_red_attach_after_generic(self):
        f = host_check.attach_findings(tree('(include-book "../books/above")\n(include-book "../books/gen-attach")\n'))
        self.assertEqual(len(f), 1)

    def test_green_attach_first(self):
        self.assertEqual(host_check.attach_findings(tree('(include-book "../books/gen-attach")\n'
                                        '(include-book "../books/above")\n')), [])

    def test_green_without_generic(self):
        self.assertEqual(host_check.attach_findings(tree("")), [])

    def test_red_when_an_attachable_impl_name_extends_the_generic(self):
        # fn-cat and fn-cat-paged are both :attachable; the generic match must not
        # take fn-x-impl's defabsstobj as a second fn-x and drop the pair.
        d = tree('(include-book "../books/above")\n')
        (d / "books/impl.lisp").write_text("(in-package \"ACL2\")\n(defabsstobj fn-x-impl\n  :attachable t)\n")
        self.assertEqual(len(host_check.attach_findings(d)), 1)

    def test_ambiguous_generic_is_a_finding(self):
        # Two books both declare :attachable fn-x: the pair is reported, not dropped.
        d = tree('(include-book "../books/gen-attach")\n')
        (d / "books/gen2.lisp").write_text("(in-package \"ACL2\")\n(defabsstobj fn-x\n  :attachable t)\n")
        f = host_check.attach_findings(d)
        self.assertEqual(len(f), 1)
        self.assertIn("books/gen.lisp", f[0])
        self.assertIn("books/gen2.lisp", f[0])

    def test_attach_without_generic_is_a_finding(self):
        d = tree("")
        (d / "books/gen.lisp").write_text("(in-package \"ACL2\")\n")
        f = host_check.attach_findings(d)
        self.assertEqual(len(f), 1)
        self.assertIn("books/gen-attach.lisp", f[0])

    def test_this_tree_is_clean(self):
        self.assertEqual(host_check.attach_findings(ROOT), [])


CHECKPOINT_LD = '(ld "host/checkpoint-host.lisp" :ld-error-action :error)\n'


# The octet-buffer books host/owner-host.lisp and host/store-node-host.lisp
# use (native-drift-2026-09-25 finding 3: at 32842f50 build-dtn.lisp lacked
# them and the DTN image did not build).  The host files include them
# themselves now, so removing them from the build list is no finding.
BUFFER_BOOKS = ("octets-stobj", "poster-bytes-buffer", "store-reclaim-buffer",
                "post-identity-index", "post-retain-carried", "owner-prepare-served")


def drop_includes(text: str, books) -> str:
    """TEXT without its top-level include-book of each of BOOKS."""
    for book in books:
        text = re.sub(r'^\(include-book "books/%s"\)\n' % re.escape(book), "", text,
                      flags=re.M)
    return text


class BuildListsCheckTests(unittest.TestCase):
    def dtn_text(self):
        return (ROOT / host_check.DTN_BUILD).read_text()

    def test_tree_is_clean(self):
        self.assertEqual(host_check.build_lists_findings(), [])

    def test_missing_checkpoint_ld_is_found_twice(self):
        text = self.dtn_text()
        self.assertIn(CHECKPOINT_LD, text)
        found = host_check.build_lists_findings(dtn_text=text.replace(CHECKPOINT_LD, ""))
        self.assertTrue(any(line.startswith("omitted: host/checkpoint-host.lisp")
                            for line in found), found)
        self.assertTrue(any("host/native/io.lisp names 'fn-store-checkpoint-clone-fence-name"
                            in line for line in found), found)

    def test_allowlisted_omission_is_still_checked_for_reach(self):
        # Listing the file as omitted does not excuse io.lisp's reference.
        text = self.dtn_text().replace(CHECKPOINT_LD, "")
        omitted = dict(host_check.DTN_OMITTED)
        omitted["host/checkpoint-host.lisp"] = ("pretend", {})
        found = host_check.build_lists_findings(dtn_text=text, omitted=omitted)
        self.assertFalse(any(line.startswith("omitted:") for line in found), found)
        self.assertTrue(any("fn-store-checkpoint-clone-fence-name" in line
                            for line in found), found)

    def test_unlisted_reference_into_an_omitted_file_is_found(self):
        omitted = dict(host_check.DTN_OMITTED)
        reason, _ = omitted["host/native/reader-model-host.lisp"]
        omitted["host/native/reader-model-host.lisp"] = (reason, {})
        found = host_check.build_lists_findings(omitted=omitted)
        self.assertTrue(any("host/native/io.lisp names 'fn-reader-model-octets"
                            in line for line in found), found)

    def test_an_excuse_nothing_needs_is_stale(self):
        omitted = dict(host_check.DTN_OMITTED)
        reason, allowed = omitted["host/reader-host.lisp"]
        omitted["host/reader-host.lisp"] = (
            reason, {**allowed, "fn-reader-observe-clock": "pretend"})
        found = host_check.build_lists_findings(omitted=omitted)
        self.assertEqual(found, ["stale: DTN_OMITTED excuses fn-reader-observe-clock "
                                 "(host/reader-host.lisp), which nothing "
                                 "host/native/build-dtn.lisp loads names any more"])

    def test_unexplained_omission_is_found(self):
        omitted = dict(host_check.DTN_OMITTED)
        del omitted["host/native-auth-admin-host.lisp"]
        found = host_check.build_lists_findings(omitted=omitted)
        self.assertIn("omitted: host/native-auth-admin-host.lisp", "\n".join(found))

    def test_stale_entry_is_found(self):
        omitted = dict(host_check.DTN_OMITTED)
        omitted["host/store-host.lisp"] = ("loaded by both", {})
        found = host_check.build_lists_findings(omitted=omitted)
        self.assertIn("stale: DTN_OMITTED lists host/store-host.lisp", "\n".join(found))

    def test_raw_call_into_an_unloaded_module_is_found(self):
        # The second layer of the same failure: with checkpoint-host loaded,
        # the c7b76b59 DTN images still refused `store init`, because io.lisp
        # called fnn-checkpoint-name-result and only checkpoint.lisp, which
        # build-dtn.lisp does not load, defined it.  Restore those two files.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / "host", root / "host")
            for path in ("host/native/io.lisp", "host/native/checkpoint.lisp"):
                old = subprocess.run(["git", "show", f"{commit_map.resolve('c7b76b59')}:{path}"], cwd=ROOT,
                                     check=True, capture_output=True, text=True).stdout
                (root / path).write_text(old)
            found = host_check.build_lists_findings(root=root)
            self.assertIn("raw: host/native/io.lisp calls fnn-checkpoint-name-result, "
                          "defined only in host/native/checkpoint.lisp", "\n".join(found))

    def test_unlisted_raw_reach_is_found(self):
        # Batch AX: at 6f397c158 the DTN image's operator.lisp called the
        # live surfaces (auth-admin, control, tls-reload, ...) behind a
        # run-time flag.  Restore that operator.lisp.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            shutil.copytree(ROOT / "host", root / "host")
            old = subprocess.run(["git", "show", commit_map.resolve("6f397c158") + ":host/native/operator.lisp"],
                                 cwd=ROOT, check=True, capture_output=True,
                                 text=True).stdout
            (root / "host/native/operator.lisp").write_text(old)
            found = host_check.build_lists_findings(root=root)
        self.assertIn("raw: host/native/operator.lisp calls fnn-native-auth-admin-execute, "
                      "defined only in host/native/auth-admin.lisp, which "
                      "host/native/build-dtn.lisp does not load", found)
        self.assertIn("raw: host/native/operator.lisp calls fnn-control-live-status, "
                      "defined only in host/native/control.lisp, which "
                      "host/native/build-dtn.lisp does not load", found)

    def test_an_unused_raw_reach_excuse_is_stale(self):
        found = host_check.build_lists_findings(reach={("host/native/operator.lisp",
                                       "fnn-native-auth-admin-execute"): "pretend"})
        self.assertEqual(found, ["stale: DTN_RAW_REACH excuses host/native/operator.lisp "
                                 "calling fnn-native-auth-admin-execute, which it no longer "
                                 "does (or the DTN image now loads its definition)"])

    def test_a_missing_or_late_loader_include_is_found(self):
        # The loader must include a host file's book BEFORE the `ld`: omitted
        # or after it, the use is a finding (the 32842f50 DTN build failure).
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "books").mkdir()
            (root / "host").mkdir()
            (root / "books/a.lisp").write_text('(defun fn-a (x) x)\n')
            (root / "host/h.lisp").write_text('(defun fn-h (x) (fn-a x))\n')
            include, ld = '(include-book "books/a")\n', '(ld "host/h.lisp" :ld-error-action :error)\n'
            self.assertEqual(host_check.include_findings(root, include + ld), [])
            for loader in (ld, ld + include):
                with self.subTest(loader=loader):
                    found = host_check.include_findings(root, loader)
                    self.assertEqual(found, [
                        "included: host/h.lisp uses fn-a, defined in books/a.lisp, which "
                        "host/native/build-dtn.lisp has not included when it loads "
                        "host/h.lisp"], found)

    def test_owner_host_declares_its_own_books(self):
        # The same omission in the real tree is no finding: every loader of
        # host/owner-host.lisp gets its books from the file itself.
        text = self.dtn_text()
        bare = drop_includes(text, BUFFER_BOOKS)
        self.assertLess(len(bare), len(text))
        self.assertEqual(host_check.include_findings(ROOT, bare), [])

    def test_a_nested_ld_serves_its_loader(self):
        # host/store-node-host.lisp loads host/store-host.lisp, which includes
        # books/store-config, before it calls fn-store-group-name; a loader of
        # store-node-host.lisp alone is not short of that book.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "books").mkdir()
            (root / "host").mkdir()
            (root / "books/a.lisp").write_text('(defun fn-a (x) x)\n')
            (root / "host/inner.lisp").write_text('(include-book "../books/a")\n')
            (root / "host/outer.lisp").write_text(
                '(ld "inner.lisp" :ld-error-action :error)\n(defun fn-o (x) (fn-a x))\n')
            (root / "host/bare.lisp").write_text('(defun fn-o (x) (fn-a x))\n')
            self.assertEqual(host_check.include_findings(
                root, '(ld "host/outer.lisp" :ld-error-action :error)\n'), [])
            self.assertEqual(len(host_check.include_findings(
                root, '(ld "host/bare.lisp" :ld-error-action :error)\n')), 1)

    def test_later_host_include_cannot_justify_earlier_use(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "books").mkdir()
            (root / "host").mkdir()
            (root / "books/a.lisp").write_text('(defun fn-a (x) x)\n')
            (root / "host/inner.lisp").write_text('(include-book "../books/a")\n')
            early = '(defun fn-before (x) (fn-a x))\n'
            late = '(defun fn-after (x) (fn-a x))\n'
            for directive in ('(include-book "../books/a")\n',
                              '(ld "inner.lisp" :ld-error-action :error)\n'):
                with self.subTest(directive=directive):
                    outer = root / "host/outer.lisp"
                    outer.write_text(early + directive + late)
                    found = host_check.include_findings(root, '(ld "host/outer.lisp")\n')
                    self.assertEqual(len(found), 1, found)
                    self.assertIn('host/outer.lisp uses fn-a', found[0])
                    outer.write_text(directive + early + late)
                    self.assertEqual(host_check.include_findings(
                        root, '(ld "host/outer.lisp")\n'), [])

    def test_nested_child_order_and_earlier_sibling_include(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "books").mkdir()
            (root / "host").mkdir()
            (root / "books/a.lisp").write_text('(defun fn-a (x) x)\n')
            child = root / "host/child.lisp"
            child.write_text('(defun fn-child (x) (fn-a x))\n'
                             '(include-book "../books/a")\n')
            (root / "host/outer.lisp").write_text('(ld "child.lisp")\n')
            found = host_check.include_findings(root, '(ld "host/outer.lisp")\n')
            self.assertEqual(len(found), 1, found)
            self.assertIn('host/child.lisp uses fn-a', found[0])
            (root / "host/first.lisp").write_text('(include-book "../books/a")\n')
            child.write_text('(defun fn-child (x) (fn-a x))\n')
            (root / "host/outer.lisp").write_text(
                '(ld "first.lisp")\n(ld "child.lisp")\n')
            self.assertEqual(host_check.include_findings(
                root, '(ld "host/outer.lisp")\n'), [])

    def test_default_build_satisfies_the_include_rule(self):
        # The same rule over build.lisp: the default image already builds.
        default = (ROOT / host_check.BUILD_SCRIPT).read_text()
        self.assertEqual(host_check.include_findings(ROOT, default), [])

    def test_local_include_does_not_count(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "books").mkdir()
            (root / "host").mkdir()
            (root / "books/a.lisp").write_text('(defun fn-a (x) x)\n')
            (root / "books/b.lisp").write_text('(local (include-book "a"))\n')
            (root / "books/c.lisp").write_text('(include-book "a")\n')
            (root / "host/h.lisp").write_text('(defun fn-h (x) (fn-a x))\n')
            ld = '(ld "host/h.lisp" :ld-error-action :error)\n'
            self.assertEqual(len(host_check.include_findings(
                root, '(include-book "books/b")\n' + ld)), 1)
            self.assertEqual(host_check.include_findings(
                root, '(include-book "books/c")\n' + ld), [])

    def test_docstring_mention_is_not_a_call(self):
        text = host_check.strip_code('(defun f () "see (fnn-x y) here" (fnn-y #\\( 1)) ; (fnn-z)')
        self.assertEqual(host_check.RAW_USE.findall(text), ["fnn-y"])


class DuplicateLoadTests(unittest.TestCase):
    def test_findings_refuse_duplicate_ld_before_set_closure_hides_it(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "host").mkdir(); (root / "books").mkdir()
            (root / "host/empty.lisp").write_text('(in-package "ACL2")\n')
            text = '(ld "host/empty.lisp")\n(ld "host/empty.lisp")\n'
            found = host_check.build_lists_findings(root, default_text=text, dtn_text=text,
                                   omitted={}, reach={})
            self.assertTrue(any(row.startswith("duplicate-load:") for row in found),
                            "duplicate literal load must be refused")
            self.assertEqual(len(found), 2)

    def test_repeated_include_and_path_alias_are_refused(self):
        for kind, target in (("ld", "host/file.lisp"), ("include-book", "books/core")):
            text = f'({kind} "{target}")\n({kind} "{target.replace("/", "/./", 1)}")\n'
            found = host_check.duplicate_load_findings(text, "fixture")
            self.assertEqual(len(found), 1)
            self.assertIn("fixture:2", found[0])
            self.assertIn("line 1", found[0])

    def test_quoted_comment_and_macro_template_are_not_load_directives(self):
        text = '''
; (ld "host/a.lisp")
#| (ld "host/a.lisp") |#
(defconst *data* '((ld "host/a.lisp")))
(defmacro template () `(ld "host/a.lisp"))
'(include-book "books/a")
(ld "host/a.lisp")
(include-book "books/a")
'''
        self.assertEqual(host_check.duplicate_load_findings(text, "fixture"), [])

    def test_nested_admitted_event_and_different_options_still_repeat(self):
        text = '(progn (ld "host/a.lisp") (ld "host/a.lisp" :ld-error-action :error))'
        self.assertEqual(len(host_check.duplicate_load_findings(text, "fixture")), 1)

    def test_distinct_namespaces_and_distinct_scripts_do_not_conflict(self):
        text = '(include-book "core")\n(include-book "core" :dir :system)\n'
        self.assertEqual(host_check.duplicate_load_findings(text, "one"), [])
        self.assertEqual(host_check.duplicate_load_findings(text, "two"), [])

    def test_shared_transitive_include_is_allowed(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); (root / "books").mkdir()
            (root / "books/shared.lisp").write_text('(in-package "ACL2")')
            for book in ("a", "b"):
                (root / f"books/{book}.lisp").write_text('(include-book "shared")')
            text = '(include-book "books/a")\n(include-book "books/b")\n'
            self.assertEqual(host_check.build_lists_findings(root, default_text=text, dtn_text=text,
                                            omitted={}, reach={}), [])

    def test_unreadable_load_list_is_a_finding(self):
        self.assertIn("unreadable", host_check.duplicate_load_findings('(ld "broken"', "fixture")[0])



class KeystoneClosureTests(unittest.TestCase):
    """A definterface keystone defined in a book the image never includes:
    dcece7415 (D26) moved K1 to books/peer-catchup-spool-body and no build
    list included it; only host-ld, at convergence, refused (attach-order
    gate 3, 2026-10-07)."""

    def tree(self, temp: str, include_body: bool) -> Path:
        root = Path(temp)
        for rel, text in {
            "books/spool.lisp": '(in-package "ACL2")\n(defthm k0 t)\n',
            "books/spool-body.lisp": ('(in-package "ACL2")\n(include-book "spool")\n'
                                      '(defthm k1 t)\n(local (defthm k-local t))\n'),
            "host/interfaces.lisp": ('(in-package "ACL2")\n'
                                     '(definterface f :class :program\n'
                                     '  :keystones (k0 (k1 :via g) unknown-generated))\n'
                                     '(definterface h :class :program)\n'),
        }.items():
            (root / rel).parent.mkdir(parents=True, exist_ok=True)
            (root / rel).write_text(text)
        build = '(include-book "books/spool")\n'
        if include_body:
            build += '(include-book "books/spool-body")\n'
        build += '(ld "host/interfaces.lisp" :ld-error-action :error)\n'
        (root / "build.lisp").write_text(build)
        return root

    def run_check(self, root: Path) -> list[str]:
        text = (root / "build.lisp").read_text()
        return host_check.keystone_findings(root, text, ["host/interfaces.lisp"])

    def test_a_cited_keystone_outside_the_image_is_a_finding(self):
        with tempfile.TemporaryDirectory() as temp:
            found = self.run_check(self.tree(temp, include_body=False))
        self.assertEqual(len(found), 1)
        self.assertIn("definterface f cites k1, defined in books/spool-body.lisp", found[0])

    def test_including_the_book_closes_it_and_unknown_names_are_left_to_host_ld(self):
        with tempfile.TemporaryDirectory() as temp:
            self.assertEqual(self.run_check(self.tree(temp, include_body=True)), [])

    def test_keystone_entries_with_via_name_their_theorem(self):
        lists = host_check.keystone_lists(
            "(definterface f :keystones (a (b :via g)) :class :program)\n"
            "(definterface h :class :program)\n"
            "(definterface i :keystones (c))\n")
        self.assertEqual(lists, [("f", ["a", "b"]), ("i", ["c"])])

    def test_an_image_that_does_not_load_interfaces_is_not_checked(self):
        with tempfile.TemporaryDirectory() as temp:
            root = self.tree(temp, include_body=False)
            self.assertEqual(host_check.keystone_findings(root, "", []), [])


if __name__ == "__main__":
    unittest.main()
