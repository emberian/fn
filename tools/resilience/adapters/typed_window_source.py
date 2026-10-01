"""One protected exact-component ACL2 world for shared-IR execution/reduction.

All candidates use the same six source books and fresh supplied-vector states.
Only fresh constants are added per trial; no candidate adds rewrite rules.
No logical return establishes native join, certificate or image qualification.
"""
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

from ..checker import Verdict
from ..journal import Journal
from ..scenario import check
from ..typed_window_model import driver, from_scenario, judge_scenario, observe

ROOT = Path(__file__).resolve().parents[3]
# The six frozen component sources and their inventory, copied byte-for-byte
# from planning/evidence/resilience-typed-window-2026-09-30/ (lane
# evidence-out, 2026-10-02): sources a tool loads stay in the repository when
# the evidence moves to the archive; the inventory's digests still pin them.
EVIDENCE = ROOT / "tools/resilience/typed_window_frozen"


class SourceBackend:
    def __init__(self, out, session, host="hbox", *, timeout=60, limit=15):
        self.out = Path(out).resolve()
        self.out.relative_to(ROOT)
        if not re.fullmatch(r"[a-z][a-z0-9-]{0,39}", session) or host not in ("hbox", "persvati", "laptop"):
            raise ValueError("owned session and supported host required")
        if type(timeout) is not int or timeout < 1 or type(limit) is not int or limit < 1:
            raise ValueError("positive experimental timeout/form budget required")
        self.session, self.host, self.timeout, self.limit = session, host, timeout, limit
        self.trial, self.live, self.failed = 0, False, False

    def command(self, *arguments):
        return subprocess.run([sys.executable, str(ROOT / "tools/proof_repl.py"), *arguments],
                              cwd=ROOT, capture_output=True, text=True, timeout=self.timeout)

    def fetch(self, name, destination):
        if self.host == "laptop":
            shutil.copyfile(ROOT / "build/proof-repl" / self.session / name, destination)
        else:
            record = json.loads((ROOT / "build/proof-repl" / self.session / "remote.json").read_text())
            tree = record["tree"]
            if record["host"] != self.host or not re.fullmatch(r"/[A-Za-z0-9_./-]+", tree):
                raise ValueError("owned remote coordinate changed")
            subprocess.run(["scp", f"{self.host}:{tree}/build/proof-repl/{self.session}/{name}", str(destination)],
                           check=True, capture_output=True, timeout=self.timeout)

    def __enter__(self):
        if (ROOT / "build/proof-repl" / self.session).exists():
            raise ValueError("session name already has a record; choose a fresh owned name")
        self.out.mkdir(parents=True, exist_ok=False)
        inventory = json.loads((EVIDENCE / "source-inventory.json").read_text())
        for name, expected in inventory["sha256"].items():
            source = EVIDENCE / Path(name).name
            if hashlib.sha256(source.read_bytes()).hexdigest() != expected:
                raise ValueError("frozen component source bytes changed: " + name)
            shutil.copyfile(source, self.out / source.name)
        (self.out / "source-inventory.json").write_text(json.dumps(inventory, indent=2) + "\n")
        prefix = self.out / "prefix.lisp"
        prefix.write_text('(in-package "ACL2")\n(include-book "page-window-executor")\n')
        # Reserve the session before starting; any failed startup is stopped.
        self.live = True
        try:
            result = self.command("start", self.session, str(prefix.relative_to(ROOT).with_suffix("")),
                                  "--source-deps", "--host", self.host, "--limit", str(self.limit),
                                  "--idle-timeout", "5")
            (self.out / "start.stdout").write_text(result.stdout)
            (self.out / "start.stderr").write_text(result.stderr)
            if result.returncode != 0:
                raise RuntimeError("typed source prefix refused; retain startup output")
        except BaseException as error:
            self._close_preserving(error)
            raise
        return self

    def execute(self, scenario):
        if not self.live or self.failed:
            raise RuntimeError("typed source session is not owned/live or a prior trial is incomplete")
        check(scenario)
        steps = from_scenario(scenario)
        trial = self.trial
        self.trial += 1
        directory = self.out / f"trial-{trial:04d}"
        directory.mkdir()
        scenario.dump(directory / "scenario.json")
        marker = f"FN_W7_TYPED_COMPLETE trial={trial}"
        path = directory / "driver.lisp"
        path.write_text(driver(steps, trial) + f'(value-triple (cw "{marker}~%"))\n')
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
            failure = dict(stage=stage, exception=type(error).__name__, message=str(error),
                           session=self.session, host=self.host,
                           stdout=diagnostic(getattr(error, "stdout", None)),
                           stderr=diagnostic(getattr(error, "stderr", None)),
                           owned_session_requires_stop=True)
            (directory / "failure.json").write_text(json.dumps(failure, indent=2) + "\n")
            journal = Journal(scenario.id)
            journal.environment("source-transport-incomplete", **failure)
            journal.write(directory / "journal.jsonl")
            verdict = Verdict("harness-failure", scenario_id=scenario.id,
                              journal_digest=journal.digest(),
                              cause="typed-source-trial-transport-incomplete").sign()
            (directory / "verdict.json").write_text(json.dumps(verdict.__dict__, indent=2) + "\n")
            return verdict
        text = (directory / "log").read_text(errors="backslashreplace")
        journal = observe(text, trial)
        journal.write(directory / "journal.jsonl")
        # Literal completion has no CW format escapes. Exclude source echo.
        complete = re.search(r"(?m)^(?:ACL2[^\n>]*>)?" + re.escape(marker) + r"\s*$", text) is not None
        if result.returncode != 0 or not complete:
            self.failed = True
            verdict = Verdict("harness-failure", scenario_id=scenario.id,
                              journal_digest=journal.digest(), cause="typed-source-trial-did-not-complete").sign()
        else:
            verdict = judge_scenario(scenario, journal, trial)
        (directory / "verdict.json").write_text(json.dumps(verdict.__dict__, indent=2) + "\n")
        return verdict

    def close(self):
        if self.live:
            result = self.command("stop", self.session)
            (self.out / "stop.stdout").write_text(result.stdout)
            (self.out / "stop.stderr").write_text(result.stderr)
            if result.returncode != 0:
                raise RuntimeError("owned typed session stop failed; retain handle and stop explicitly")
            self.live = False
            self.fetch("state.json", self.out / "state.json")

    def _close_preserving(self, primary):
        try:
            self.close()
        except BaseException as cleanup:
            # A failed stop is still an owned handle, never an idle verdict.
            (self.out / "stop-failure.json").write_text(json.dumps(dict(
                session=self.session, host=self.host, exception=type(cleanup).__name__,
                message=str(cleanup), owned_session_requires_stop=self.live), indent=2) + "\n")
            primary.add_note("Owned typed session cleanup failed; see " + str(self.out / "stop-failure.json"))

    def __exit__(self, kind, error, traceback):
        if error is None:
            try:
                self.close()
            except BaseException as cleanup:
                (self.out / "stop-failure.json").write_text(json.dumps(dict(
                    session=self.session, host=self.host, exception=type(cleanup).__name__,
                    message=str(cleanup), owned_session_requires_stop=self.live), indent=2) + "\n")
                raise
        else:
            self._close_preserving(error)
