"""The observation journal: three histories kept apart (design §6).

client      what the client saw: a reply or its loss, bytes returned, a
            listing.  The ONLY history that establishes a promise.
internal    diagnostic events (a log line saying "durable"): never evidence.
environment which fault fired, what the image's own scan says was
            persisted, which completion was withheld.
stage       the run's stages begun and ended (a begun stage never ended is
            a killed stage, a harness failure).
binding     symbolic identity -> concrete value, for replay.

The journal lives OUTSIDE the faulted store and ends in a seal (count and
digest): a journal without its seal, or whose count disagrees, is a
truncated history, never a shorter valid one.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

KINDS = ("client", "internal", "environment", "stage", "binding")


class TruncatedHistory(AssertionError):
    pass


class Journal:
    def __init__(self, scenario_id: str):
        self.scenario_id = scenario_id
        self.records = []

    def append(self, kind: str, **fields) -> dict:
        if kind not in KINDS:
            raise ValueError(kind)
        rec = {"seq": len(self.records), "kind": kind}
        rec.update(fields)
        self.records.append(rec)
        return rec

    def client(self, event: str, **fields) -> dict:
        return self.append("client", event=event, **fields)

    def internal(self, event: str, **fields) -> dict:
        return self.append("internal", event=event, **fields)

    def environment(self, event: str, **fields) -> dict:
        return self.append("environment", event=event, **fields)

    def stage(self, name: str, event: str, **fields) -> dict:
        """A stage begun or ended; an ended healing stage carries `elapsed`
        (seconds) for the scenario's declared bound."""
        return self.append("stage", name=name, event=event, **fields)

    def bind(self, symbol: str, concrete) -> dict:
        return self.append("binding", symbol=symbol, concrete=concrete)

    def of_kind(self, kind: str) -> list:
        return [r for r in self.records if r["kind"] == kind]

    def narrowing(self) -> list:
        """The records the checker narrows on, in sequence: the client's
        history and the environment's facts.  Internal events are not here."""
        return [r for r in self.records if r["kind"] in ("client", "environment")]

    @staticmethod
    def _line(rec: dict) -> str:
        return json.dumps(rec, sort_keys=True, separators=(",", ":"))

    def digest(self) -> str:
        h = hashlib.sha256()
        for r in self.records:
            h.update(self._line(r).encode()); h.update(b"\n")
        return h.hexdigest()

    def seal(self) -> dict:
        return {"kind": "seal", "scenario": self.scenario_id,
                "count": len(self.records), "digest": self.digest()}

    def write(self, path: Path) -> Path:
        path = Path(path)
        with open(path, "w") as f:
            f.write(self._line({"kind": "head", "scenario": self.scenario_id}) + "\n")
            for r in self.records:
                f.write(self._line(r) + "\n")
            f.write(self._line(self.seal()) + "\n")
        return path

    @classmethod
    def read(cls, path: Path) -> "Journal":
        lines = [ln for ln in Path(path).read_text().splitlines() if ln.strip()]
        if not lines:
            raise TruncatedHistory("empty journal " + str(path))
        head = json.loads(lines[0])
        if head.get("kind") != "head":
            raise TruncatedHistory("journal without a head: " + str(path))
        j = cls(head["scenario"])
        last = json.loads(lines[-1])
        if last.get("kind") != "seal":
            raise TruncatedHistory("journal without its seal: " + str(path))
        for ln in lines[1:-1]:
            rec = json.loads(ln)
            if rec["seq"] != len(j.records):
                raise TruncatedHistory("journal sequence gap at {}".format(rec["seq"]))
            j.records.append(rec)
        if last["count"] != len(j.records) or last["digest"] != j.digest():
            raise TruncatedHistory("journal seal disagrees with its records")
        return j
