"""tools/green_check.py: a book is certified only at the closure key it carries NOW.

On 2026-09-21 four books sat red on `dev` for a day, each committed by a lane
that never certified it, while every reader took `git log` for certification.
"Certified" is now one thing: the record box's cert cache holds an entry at the
book's current closure key whose toolchain identity is the record toolchain's.
These tests stand up a fake cache directory (no ssh) and pin that rule: a
changed book or a changed dependency moves the key and so uncertifies the book
and its includers, an entry from another toolchain never counts, and a
corrupt certificate never counts.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import cert_images  # noqa: E402
import certs  # noqa: E402
import green_check  # noqa: E402

RECORD = "r" * 64
LAPTOP = "l" * 64


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def book(root: Path, name: str, body: str) -> str:
    """Write `<name>.lisp` with `body` and answer its sha256."""
    path = root / f"{name}.lisp"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(body, encoding="utf-8")
    return digest(body)


def publish(cache: Path, root: Path, name: str, *, identity: str = RECORD,
            cert: bytes = b"cert", recorded: bytes | None = None,
            published_at: str = "2026-10-07T00:00:00Z") -> Path:
    """One cache entry for NAME at ROOT's current closure key, in every world
    a certificate of it may have been made in.  `recorded` is the certificate
    the meta.json hashes when it differs from the bytes on disk (corruption)."""
    made = None
    for world in cert_images.worlds(root.resolve(), name):
        key, _ = certs.closure_key(root, name, world)
        entry = cache / key / "origin-a"
        entry.mkdir(parents=True, exist_ok=True)
        (entry / "book.cert").write_bytes(cert)
        (entry / "meta.json").write_text(json.dumps({
            "book": name, "closure_key": key, "toolchain_identity": identity,
            "cert_sha256": hashlib.sha256(cert if recorded is None else recorded).hexdigest(),
            "published_at": published_at, "origin_host": "hbox"}))
        made = made or entry
    return made


def audit(root: Path, cache: Path, roots: list[str], identity: str = RECORD) -> dict:
    return green_check.audit(
        root, roots=roots, cache=green_check.Cache(local=cache, identity=identity))


class Fixture(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.root = Path(self.directory.name).resolve() / "tree"
        self.cache = Path(self.directory.name).resolve() / "cache"
        self.cache.mkdir()
        self.root.mkdir()

    def tearDown(self):
        self.directory.cleanup()

    def verdicts(self, roots: list[str]) -> dict[str, str]:
        report = audit(self.root, self.cache, roots)
        return {name: entry["verdict"]
                for name, entry in report["books_by_verdict"].items()}


class CacheVerdictTests(Fixture):
    def setUp(self):
        super().setUp()
        for name in ("green", "foreign", "corrupt", "empty"):
            book(self.root, f"books/{name}", f'(in-package "ACL2") ; {name}')
        publish(self.cache, self.root, "books/green")
        publish(self.cache, self.root, "books/foreign", identity=LAPTOP)
        publish(self.cache, self.root, "books/corrupt", recorded=b"other bytes")
        self.names = ["books/green", "books/foreign", "books/corrupt", "books/empty"]

    def test_only_a_record_toolchain_entry_with_a_good_cert_is_green(self):
        self.assertEqual(self.verdicts(self.names), {
            "books/green": "green", "books/foreign": "uncertified",
            "books/corrupt": "uncertified", "books/empty": "uncertified"})

    def test_an_edit_moves_the_key_and_uncertifies_the_book(self):
        book(self.root, "books/green", '(in-package "ACL2")\n(defun f () 1) ; green, edited')
        self.assertEqual(self.verdicts(["books/green"]), {"books/green": "uncertified"})

    def test_a_comment_only_edit_keeps_the_key(self):
        """The key hashes the read forms (certs.form_hash), not the bytes."""
        book(self.root, "books/green", '(in-package "ACL2") ; green\n; a new comment\n')
        self.assertEqual(self.verdicts(["books/green"]), {"books/green": "green"})

    def test_a_moved_dependency_uncertifies_the_includer(self):
        book(self.root, "books/dep", '(in-package "ACL2")\n(defun f () 1)\n')
        book(self.root, "books/top", '(in-package "ACL2")\n(include-book "dep")\n')
        publish(self.cache, self.root, "books/dep")
        publish(self.cache, self.root, "books/top")
        self.assertEqual(self.verdicts(["books/top"]),
                         {"books/dep": "green", "books/top": "green"})
        book(self.root, "books/dep", '(in-package "ACL2")\n(defun f () 2)\n')
        self.assertEqual(self.verdicts(["books/top"]),
                         {"books/dep": "uncertified", "books/top": "uncertified"})

    def test_the_newest_entry_is_reported(self):
        old = publish(self.cache, self.root, "books/green", published_at="2026-01-01T00:00:00Z")
        newer = old.parent / "origin-b"
        newer.mkdir()
        for name in ("book.cert", "meta.json"):
            (newer / name).write_bytes((old / name).read_bytes())
        meta = json.loads((newer / "meta.json").read_text())
        meta["published_at"] = "2026-10-01T00:00:00Z"
        (newer / "meta.json").write_text(json.dumps(meta))
        record = audit(self.root, self.cache, ["books/green"])["books_by_verdict"]["books/green"]
        self.assertEqual(record["cache_entry"]["origin"], "origin-b")

    def test_the_report_names_where_it_asked_and_counts(self):
        report = audit(self.root, self.cache, self.names)
        self.assertEqual(report["counts"], {"green": 1, "uncertified": 3, "unknown": 0})
        self.assertEqual(report["standing_counts"], {"green": 1, "uncertified": 3})
        self.assertIn(str(self.cache), report["cache"])
        self.assertEqual(report["record_identity"], RECORD)

    def test_the_table_puts_the_uncertified_books_first(self):
        report = audit(self.root, self.cache, self.names)
        rows = green_check.table(report)
        self.assertTrue(rows[1].startswith("uncertified"))
        self.assertTrue(rows[-1].startswith("green"))

    def test_the_worklist_is_everything_but_the_greens(self):
        report = audit(self.root, self.cache, self.names)
        self.assertEqual(sorted(green_check.worklist(report)),
                         ["books/corrupt", "books/empty", "books/foreign"])

    def test_the_summary_says_the_counts_and_what_is_owed(self):
        lines = green_check.summary(audit(self.root, self.cache, self.names))
        self.assertEqual(len(lines), 3)
        self.assertIn("1 certified", lines[0])
        self.assertIn("3 not", lines[0])
        self.assertIn("books/corrupt", lines[1])

    def test_a_missing_record_is_absent_never_green(self):
        self.assertEqual(green_check.standing(None), "absent")
        self.assertFalse(green_check.green_at_these_bytes(None))
        self.assertFalse(green_check.green_at_these_bytes({"verdict": "uncertified"}))
        self.assertTrue(green_check.green_at_these_bytes({"verdict": "green"}))


class ReleaseGateTests(Fixture):
    """`--strict` and `--profile --strict` are the release cut's check: every
    book must be green, and a book nothing vouches for fails (S009)."""

    def setUp(self):
        super().setUp()
        book(self.root, "books/dep", '(in-package "ACL2")')
        book(self.root, "books/top", '(in-package "ACL2")\n(include-book "dep")\n')

    def test_all_certified_passes_both_gates(self):
        publish(self.cache, self.root, "books/dep")
        publish(self.cache, self.root, "books/top")
        report = audit(self.root, self.cache, ["books/top"])
        self.assertEqual([r for r in green_check.strict_rows(report)
                          if r["verdict"] != "green"], [])
        answer = green_check.profile_gate(report, "default", root=self.root,
                                          roots=["books/top"])
        self.assertEqual(answer["not_green"], [])
        self.assertEqual(answer["books"], 2)

    def test_an_uncertified_dependency_fails_strict_and_profile(self):
        publish(self.cache, self.root, "books/top")
        report = audit(self.root, self.cache, ["books/top"])
        self.assertEqual([r["book"] for r in green_check.strict_rows(report)
                          if r["verdict"] != "green"], ["books/dep"])
        answer = green_check.profile_gate(report, "default", root=self.root,
                                          roots=["books/top"])
        self.assertEqual(answer["not_green"], ["books/dep"])
        self.assertIn("uncertified=1", green_check.profile_lines(answer)[0])

    def test_a_book_the_audit_never_saw_is_absent_and_fails(self):
        report = {"books_by_verdict": {}}
        answer = green_check.profile_gate(report, "default", root=self.root,
                                          roots=["books/top"])
        self.assertEqual({r["verdict"] for r in answer["rows"]}, {"absent"})
        self.assertTrue(answer["not_green"])


class MergeGateTests(Fixture):
    """--changed-since: a changed book merges with everything that includes it.

    Finding F4 of planning/review-2026-09-22-proof-engineering.md: on
    2026-09-21 behaviour landed under invariant books nobody recertified.  The
    gate reads the branch's changed books, the audited books whose closure
    reaches one, and each verdict at the closure key a merge would carry.
    """

    def tree(self) -> dict:
        book(self.root, "books/dep", '(in-package "ACL2")')
        book(self.root, "books/top", '(in-package "ACL2")\n(include-book "dep")\n')
        book(self.root, "books/aside", '(in-package "ACL2") ; unrelated')
        for name in ("dep", "top", "aside"):
            publish(self.cache, self.root, f"books/{name}")
        return audit(self.root, self.cache, ["books/top", "books/aside"])

    def test_a_changed_book_names_the_books_that_include_it_and_nothing_else(self):
        report = self.tree()
        self.assertEqual(green_check.dependents(self.root, report, ["books/dep"]),
                         {"books/top": ["books/dep"]})

    def test_host_include_is_a_dependency_not_an_uncertifiable_root(self):
        book(self.root, "books/dep", '(in-package "ACL2")')
        book(self.root, "host/helper", '(in-package "ACL2")\n(include-book "../books/dep")\n')
        book(self.root, "books/top", '(in-package "ACL2")\n(include-book "../host/helper")\n')
        report = audit(self.root, self.cache, ["books/top"])
        self.assertIn("host/helper", report["books_by_verdict"])
        self.assertEqual(green_check.dependents(self.root, report, ["books/dep"]),
                         {"books/top": ["books/dep"]})

    def test_the_gate_is_green_only_when_every_row_is_green(self):
        report = self.tree()
        deps = green_check.dependents(self.root, report, ["books/dep"])
        self.assertEqual(green_check.gate(report, ["books/dep"], deps)["not_green"], [])
        # The dependency's bytes move and nobody certifies: both it and its
        # includer (whose key hashes the dependency) are owed a run.
        book(self.root, "books/dep", '(in-package "ACL2") ; edited\n(defun g () 3)\n')
        report = audit(self.root, self.cache, ["books/top", "books/aside"])
        answer = green_check.gate(report, ["books/dep"],
                                  green_check.dependents(self.root, report, ["books/dep"]))
        self.assertEqual(answer["not_green"], ["books/dep", "books/top"])
        roles = {row["book"]: row["role"] for row in answer["rows"]}
        self.assertEqual(roles, {"books/dep": "changed", "books/top": "dependent"})
        self.assertNotIn("books/aside", roles)

    def test_certifying_only_the_dependency_does_not_certify_its_consumer(self):
        self.tree()
        book(self.root, "books/dep", '(in-package "ACL2")\n(defun g () 3)\n')
        publish(self.cache, self.root, "books/dep")
        report = audit(self.root, self.cache, ["books/top", "books/aside"])
        answer = green_check.gate(report, ["books/dep"],
                                  green_check.dependents(self.root, report, ["books/dep"]))
        self.assertEqual(answer["not_green"], ["books/top"])
        publish(self.cache, self.root, "books/top")
        report = audit(self.root, self.cache, ["books/top", "books/aside"])
        answer = green_check.gate(report, ["books/dep"],
                                  green_check.dependents(self.root, report, ["books/dep"]))
        self.assertEqual(answer["not_green"], [])

    def test_a_changed_book_no_root_reaches_is_unaudited_and_not_green(self):
        report = self.tree()
        answer = green_check.gate(report, ["tests/acl2/orphan-tests"], {}, unhooked_books={})
        self.assertEqual(answer["rows"][0]["verdict"], "unaudited")
        self.assertEqual(answer["not_green"], ["tests/acl2/orphan-tests"])

    def test_changed_books_reads_the_working_tree_against_the_merge_base(self):
        root = self.root
        git = self.git_repo()
        book(root, "books/dep", '(in-package "ACL2")')
        book(root, "tests/acl2/dep-tests", '(in-package "ACL2")')
        (root / "notes.md").write_text("x")
        git("add", "-A")
        git("commit", "-q", "-m", "base")
        git("checkout", "-q", "-b", "lane")
        book(root, "books/dep", '(in-package "ACL2") ; committed on the lane')
        git("commit", "-q", "-am", "lane edit")
        book(root, "tests/acl2/dep-tests", '(in-package "ACL2") ; uncommitted')
        (root / "notes.md").write_text("prose does not count")
        self.assertEqual(green_check.changed_books(root, "main"),
                         ["books/dep", "tests/acl2/dep-tests"])

    def git_repo(self):
        root = self.root
        git = lambda *words: subprocess.run(  # noqa: E731
            ["git", *words], cwd=root, check=True, capture_output=True, text=True)
        git("init", "-q", "-b", "main")
        git("config", "user.email", "t@example.invalid")
        git("config", "user.name", "t")
        # This temporary history tests diff selection, not the user's
        # signing agent or repository hooks.
        git("config", "commit.gpgsign", "false")
        hooks = root / "empty-hooks"
        hooks.mkdir()
        git("config", "core.hooksPath", str(hooks))
        return git

    def test_a_host_include_edit_and_an_untracked_book_reach_the_gate(self):
        """S056: a lane that edits only host/page-read-host.lisp (which books
        include), or creates a book without `git add`, used to see
        "no book or test book differs" and exit 0 under --strict."""
        root = self.root
        git = self.git_repo()
        book(root, "host/helper", '(in-package "ACL2")')
        book(root, "books/top", '(in-package "ACL2")\n(include-book "../host/helper")\n')
        publish(self.cache, root, "books/top")
        git("add", "-A")
        git("commit", "-q", "-m", "base")
        git("checkout", "-q", "-b", "lane")
        book(root, "host/helper", '(in-package "ACL2") ; host edit\n(defun h () 1)\n')
        book(root, "books/fresh", '(in-package "ACL2") ; never added')
        changed = green_check.changed_books(root, "main")
        self.assertEqual(changed, ["books/fresh", "host/helper"])
        report = audit(root, self.cache, ["books/top", "books/fresh"])
        answer = green_check.gate(report, green_check.certifiable(changed),
                                  green_check.dependents(root, report, changed))
        verdicts = {row["book"]: row["verdict"] for row in answer["rows"]}
        self.assertEqual(verdicts, {"books/fresh": "uncertified", "books/top": "uncertified"})
        self.assertEqual(answer["not_green"], ["books/fresh", "books/top"])

    def test_the_gate_lines_say_the_counts_and_every_row(self):
        answer = green_check.gate(
            {"books_by_verdict": {"books/a": {"verdict": "green"},
                                  "books/b": {"verdict": "uncertified"}}},
            ["books/a"], {"books/b": ["books/a"]})
        lines = green_check.gate_lines(answer)
        self.assertIn("1 changed books, 1 books include one; 1 not green", lines[0])
        self.assertTrue(any("uncertified" in line and "books/b" in line
                            and "<- books/a" in line for line in lines[1:]))


class ScopedAuditTests(Fixture):
    def test_cli_selects_affected_roots_before_audit(self):
        report = {"books_by_verdict": {"books/dep": {"verdict": "uncertified"},
                                        "books/top": {"verdict": "uncertified"}}}
        root = self.root
        book(root, "books/dep", '(in-package "ACL2")')
        book(root, "books/top", '(include-book "dep")')
        book(root, "books/aside", '(in-package "ACL2")')
        calls = []

        def scoped(*args, **kwargs):
            calls.append(kwargs.get("roots"))
            return report
        with patch.object(green_check, "ROOT", root), \
                patch.object(green_check.ledger, "makefile_roots",
                             return_value=["books/top", "books/aside"]), \
                patch.object(green_check, "changed_books", return_value=["books/dep"]), \
                patch.object(green_check, "audit", side_effect=scoped), \
                patch("builtins.print"):
            code = green_check.main(["--changed-since", "HEAD", "--strict"])
        self.assertEqual(calls, [["books/dep", "books/top"]],
                         "changed gate must select affected roots before auditing")
        self.assertEqual(code, 1)

    def test_reverse_graph_matches_existing_dependent_scope_including_host_sources(self):
        root = self.root
        book(root, "books/dep", '(in-package "ACL2")')
        book(root, "host/helper", '(include-book "../books/dep")')
        book(root, "books/mid", '(local (include-book "../host/helper"))')
        book(root, "books/top", '(include-book "mid")')
        book(root, "books/aside", '(in-package "ACL2")')
        roots = ["books/top", "books/aside"]
        full = audit(root, self.cache, roots)
        for changed in (["books/dep"], ["host/helper"], ["books/new"]):
            selected, deps = green_check.changed_scope(root, changed, roots)
            scoped = audit(root, self.cache, selected)
            self.assertEqual(deps, green_check.dependents(root, full, changed))
            self.assertEqual(green_check.gate(scoped, green_check.certifiable(changed), deps),
                             green_check.gate(full, green_check.certifiable(changed), deps))

    def test_empty_changed_query_asks_no_cache(self):
        with patch.object(green_check, "changed_books", return_value=[]), \
                patch.object(green_check.ledger, "makefile_roots", return_value=["books/top"]), \
                patch.object(green_check.certs, "include_graph",
                             side_effect=AssertionError("unneeded graph")), \
                patch.object(green_check, "audit", side_effect=AssertionError("unneeded ask")), \
                patch("builtins.print"):
            self.assertEqual(green_check.main(["--changed-since", "HEAD", "--strict"]), 0)

    def test_the_command_line_answers_from_a_local_cache(self):
        book(self.root, "books/a", '(in-package "ACL2")')
        book(self.root, "books/b", '(in-package "ACL2") ; b')
        publish(self.cache, self.root, "books/a")
        out = []
        with patch.object(green_check, "ROOT", self.root), \
                patch.object(green_check.ledger, "makefile_roots",
                             return_value=["books/a", "books/b"]), \
                patch("builtins.print", side_effect=lambda *a, **k: out.append(" ".join(map(str, a)))):
            code = green_check.main(["--json", "--strict", "--cache", str(self.cache),
                                     "--identity", RECORD])
        self.assertEqual(code, 1)
        report = json.loads(out[0])
        self.assertEqual({b: e["verdict"] for b, e in report["books_by_verdict"].items()},
                         {"books/a": "green", "books/b": "uncertified"})


class BoxTests(Fixture):
    """The ssh path, with ssh replaced: one call per process, hbox first,
    persvati when hbox cannot be reached, never a silent "uncertified"."""

    def reply(self, hits, code=0, identity="i" * 64):
        return subprocess.CompletedProcess(
            [], code, json.dumps({"identity": identity, "hits": hits}) + "\n", "unreachable")

    def test_one_call_carries_every_key_and_the_box_cache_path(self):
        calls = []

        def fake(command, **kwargs):
            calls.append((command, kwargs["input"]))
            return self.reply({})
        cache = green_check.Cache()
        with patch.object(green_check.subprocess, "run", side_effect=fake):
            cache.ask(["k1", "k2"])
            cache.ask(["k1", "k2"])        # remembered: no second call
        self.assertEqual(len(calls), 1)
        command, script = calls[0]
        self.assertEqual(command[-3:], ["hbox", "python3", "-"])
        self.assertIn("/tank/fn/certcache", script)
        self.assertIn(green_check.RECORD_LAUNCHER, script)
        compile(script, "remote", "exec")

    def test_hbox_unreachable_falls_back_to_persvati_and_says_so(self):
        asked = []

        def fake(command, **kwargs):
            asked.append(command[-3])
            return self.reply({}, code=255) if command[-3] == "hbox" else self.reply({"k1": {"x": 1}})
        cache = green_check.Cache()
        with patch.object(green_check.subprocess, "run", side_effect=fake), \
                patch("sys.stderr") as err:
            cache.ask(["k1"])
        self.assertEqual(asked, ["hbox", "persvati"])
        self.assertEqual(cache.hit("k1"), {"x": 1})
        said = "".join(call.args[0] for call in err.write.call_args_list)
        self.assertIn("answered by persvati", said)

    def test_no_box_answering_is_an_error_not_an_uncertified_verdict(self):
        cache = green_check.Cache()
        with patch.object(green_check.subprocess, "run", return_value=self.reply({}, code=255)):
            with self.assertRaises(green_check.CacheUnavailable):
                cache.ask(["k1"])
        with patch.object(green_check, "audit", side_effect=green_check.CacheUnavailable("x")), \
                patch("sys.stderr"):
            self.assertEqual(green_check.main(["--summary"]), 2)

    def test_unreachable_cache_reports_unknown_per_book_and_exits_3_in_every_mode(self):
        book(self.root, "books/a", '(in-package "ACL2")')
        with patch.object(green_check.subprocess, "run", return_value=self.reply({}, code=255)):
            report = green_check.audit(self.root, roots=["books/a"],
                                       cache=green_check.Cache(), unknown_ok=True)
        self.assertEqual(report["books_by_verdict"]["books/a"]["verdict"], "unknown")
        self.assertEqual(report["counts"]["unknown"], 1)
        self.assertFalse(green_check.green_at_these_bytes(report["books_by_verdict"]["books/a"]))
        out = []
        with patch.object(green_check, "ROOT", self.root), \
                patch.object(green_check.ledger, "makefile_roots", return_value=["books/a"]), \
                patch.object(green_check.subprocess, "run", return_value=self.reply({}, code=255)), \
                patch("builtins.print", side_effect=lambda *a, **k: out.append(" ".join(map(str, a)))):
            for mode in (["--summary"], ["--table"], ["--json"], ["--strict"]):
                self.assertEqual(green_check.main(mode), 3, mode)

    def test_a_local_mirror_without_a_launcher_requires_explicit_identity(self):
        book(self.root, "books/a", '(in-package "ACL2")')
        publish(self.cache, self.root, "books/a", identity="current-record")
        with patch.object(green_check.acl2_toolchain, "fingerprint",
                          return_value=green_check.acl2_toolchain.Fingerprint(
                              False, None, None, {}, "no launcher")):
            with self.assertRaisesRegex(green_check.CacheUnavailable, "--identity"):
                green_check.Cache(local=self.cache).local_identity()
            report = green_check.audit(self.root, roots=["books/a"],
                                       cache=green_check.Cache(local=self.cache,
                                                               identity="current-record"))
        self.assertEqual(report["books_by_verdict"]["books/a"]["verdict"], "green")

    def test_an_explicit_box_is_the_only_box_asked(self):
        asked = []

        def fake(command, **kwargs):
            asked.append(command[-3])
            return self.reply({}, code=255)
        with patch.object(green_check.subprocess, "run", side_effect=fake):
            with self.assertRaises(green_check.CacheUnavailable):
                green_check.Cache(box="persvati").ask(["k1"])
        self.assertEqual(asked, ["persvati"])

    def test_the_remote_program_scans_a_cache_it_can_read(self):
        """The shipped script, run for real against a fixture cache (its
        launcher is not a qualified one here, so its identity is null)."""
        book(self.root, "books/a", '(in-package "ACL2")')
        entry = publish(self.cache, self.root, "books/a", identity=None)
        key = entry.parent.name
        script = green_check.remote_script(str(self.cache), "/nonexistent/launcher", [key])
        done = subprocess.run([sys.executable, "-"], input=script, capture_output=True,
                              text=True, cwd=self.directory.name)
        self.assertEqual(done.returncode, 0, done.stderr)
        answer = json.loads(done.stdout)
        self.assertIsNone(answer["identity"])

    def test_the_record_launcher_is_the_farms_hbox_launcher(self):
        import farm
        self.assertEqual(green_check.RECORD_LAUNCHER, farm.HOSTS["hbox"]["acl2"])
        self.assertEqual(green_check.RECORD_LAUNCHER, farm.HOSTS["persvati"]["acl2"])


if __name__ == "__main__":
    unittest.main()
