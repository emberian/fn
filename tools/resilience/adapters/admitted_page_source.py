"""Same protected source world for actual owner/PIO Scenario trials and reduction.

Cache-only startup permits the one named owner host root from source. No missing
source cascade, image/bootstrap or native worker join is synthesized.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

from tools.proof_repl import include_graph

from .typed_window_source import SourceBackend as ProtectedBackend, ROOT
from .. import admitted_page
from ..checker import Verdict
from ..journal import Journal
from ..scenario import check

ACL2 = "/tank/fn/toolchains/w28/acl2-literal-4g-tls64k"


def completed(text, trial):
    marker = f"FN_W7_ADMITTED_COMPLETE trial={trial}"
    return re.search(r"(?m)^\s*(?:ACL2[^\n>]*>)?" + re.escape(marker) + r"\s*$", text) is not None


class SourceBackend(ProtectedBackend):
    def __init__(self, *args, source_books=(), **kwargs):
        super().__init__(*args, **kwargs)
        # Explicit finite fallback, never discover/load an arbitrary missing set.
        allowed = ("books/cold-read-layout", "books/page-read-ledger")
        if tuple(source_books) not in ((), allowed):
            raise ValueError("only the frozen two-root/five-dependent source fallback is supported")
        self.source_books = tuple(source_books)

    def __enter__(self):
        if (ROOT / "build/proof-repl" / self.session).exists():
            raise ValueError("fresh owned source session required")
        self.out.mkdir(parents=True, exist_ok=False)
        graph = include_graph(ROOT, "host/page-read-host")
        sources = sorted({"host/page-read-host.lisp"} |
                         {name + ".lisp" for name in graph})
        inventory = {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in sources}
        self.inventory = inventory
        (self.out / "source-inventory.json").write_text(json.dumps(inventory, indent=2) + "\n")
        prefix = self.out / "prefix.lisp"
        book = os.path.relpath(ROOT / "host/page-read-host", prefix.parent)
        prefix.write_text(f'(in-package "ACL2")\n(include-book "{book}")\n')
        self.live = True
        try:
            arguments = ["start", self.session, str(prefix.relative_to(ROOT).with_suffix("")),
                         "--host", self.host, "--limit", str(self.limit), "--load-limit", str(self.limit),
                         "--idle-timeout", "5", "--ld", "host/page-read-host"]
            for book in self.source_books:
                arguments += ["--ld", book]
            if self.host != "laptop":
                remote_base = "/home/ember/fn-gates" if self.host == "persvati" else "/tank/fn/gates"
                arguments += ["--acl2", ACL2, "--remote-tree",
                              f"{remote_base}/gpt61-resilience-admitted-page-repl"]
            result = self.command(*arguments)
            (self.out / "start.stdout").write_text(result.stdout)
            (self.out / "start.stderr").write_text(result.stderr)
            if result.returncode:
                raise RuntimeError("actual owner source prefix refused; retain exact frontier")
        except BaseException as error:
            def diagnostic(value):
                return value.decode(errors="backslashreplace") if isinstance(value, bytes) else value
            failure = dict(stage="start", exception=type(error).__name__, diagnostic=str(error),
                           session=self.session, host=self.host,
                           stdout=diagnostic(getattr(error, "stdout", None)),
                           stderr=diagnostic(getattr(error, "stderr", None)))
            (self.out / "start-failure.json").write_text(json.dumps(failure, indent=2) + "\n")
            self._close_preserving(error)
            raise
        return self

    def execute(self, scenario):
        if not self.live or self.failed:
            raise RuntimeError("source world not owned/live or already incomplete")
        check(scenario)
        if any(hashlib.sha256((ROOT / p).read_bytes()).hexdigest() != digest
               for p, digest in self.inventory.items()):
            self.failed = True
            raise RuntimeError("source coordinate changed during owned lifecycle session")
        trial = self.trial
        self.trial += 1
        directory = self.out / f"trial-{trial:04d}"
        directory.mkdir()
        scenario.dump(directory / "scenario.json")
        path = directory / "driver.lisp"
        path.write_text(admitted_page.driver(scenario, trial))
        marker = f"FN_W7_ADMITTED_COMPLETE trial={trial}"
        stage = "send-file"
        try:
            result = self.command("send-file", self.session, str(path.relative_to(ROOT)), "--limit", str(self.limit))
            (directory / "send.stdout").write_text(result.stdout)
            (directory / "send.stderr").write_text(result.stderr)
            stage = "fetch-log"
            self.fetch("log", directory / "log")
        except (OSError, subprocess.SubprocessError, ValueError) as error:
            self.failed = True
            def diagnostic(value):
                return value.decode(errors="backslashreplace") if isinstance(value, bytes) else value
            failure = dict(stage=stage, exception=type(error).__name__, diagnostic=str(error),
                           session=self.session, host=self.host, owned_session_requires_stop=True,
                           stdout=diagnostic(getattr(error, "stdout", None)),
                           stderr=diagnostic(getattr(error, "stderr", None)))
            (directory / "failure.json").write_text(json.dumps(failure, indent=2) + "\n")
            journal = Journal(scenario.id)
            journal.environment("admitted-source-transport-incomplete", **failure)
            verdict = Verdict("harness-failure", scenario_id=scenario.id,
                              journal_digest=journal.digest(), cause="admitted-source-transport-incomplete").sign()
        else:
            # Trial-specific anchored marker cannot be satisfied by Lisp source echo.
            complete = completed(result.stdout, trial)
            journal = admitted_page.observe(scenario, result.stdout, trial)
            if result.returncode or not complete:
                self.failed = True
                verdict = Verdict("harness-failure", scenario_id=scenario.id,
                                  journal_digest=journal.digest(), cause="admitted-source-trial-did-not-complete").sign()
            else:
                verdict = admitted_page.judge(scenario, journal)
        journal.write(directory / "journal.jsonl")
        (directory / "verdict.json").write_text(json.dumps(verdict.to_json(), indent=2) + "\n")
        return verdict
