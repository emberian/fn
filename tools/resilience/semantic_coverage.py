"""Observed abstract situations, separate from correctness and code coverage.

Missing dimensions remain `unobserved`; model records cannot establish native
headroom, reader generations, storage evidence versions or resource release.
Only sealed journals are accepted by the command-line collector.
"""
import argparse
from collections import Counter
from dataclasses import asdict, dataclass
import json
from pathlib import Path

from .journal import Journal
from .scenario import Scenario


@dataclass(frozen=True)
class Signature:
    scope: str
    publication_phase: str
    outcome_certainty: str
    pending_effect_classes: str
    reader_generation_relation: str = "unobserved"
    hold_count_class: str = "unobserved"
    headroom_band: str = "unobserved"
    evidence_version_relation: str = "unobserved"
    recovery_attempt: str = "unobserved"


def collect(scenario, journal):
    """Project actual client model observations; never synthesize an oracle."""
    if journal.scenario_id != scenario.id:
        raise ValueError("coverage scenario/journal identity differs")
    operations = {o.id: o for o in scenario.operations}
    counts = Counter()
    recoveries = 0
    for row in journal.of_kind("client"):
        if row.get("event") not in ("model-step", "response-model-step"):
            continue
        operation = operations.get(row.get("operation"))
        if operation is None:
            raise ValueError("observed operation is absent from scenario")
        if row["event"] == "model-step":
            if row.get("f") not in ("T", "NIL") or row.get("p") not in ("A", "B", "none"):
                raise ValueError("coverage requires complete observed model view")
            if operation.op == "model-recover":
                recoveries += 1
            signature = Signature("logical-acceptance", operation.op,
                "unresolved" if row["f"] == "T" else "decided",
                "proposal" if row["p"] != "none" else "none",
                recovery_attempt="zero" if not recoveries else "one" if recoveries == 1 else "repeated")
        else:
            holds = row.get("h")
            if not isinstance(holds, str) or not holds or any(c not in "0123456789" for c in holds):
                raise ValueError("coverage requires an observed natural hold count")
            holds = holds.lstrip("0") or "0"
            signature = Signature("logical-response-holds", "unobserved", "unobserved",
                "unobserved", hold_count_class="zero" if holds == "0" else "one" if holds == "1" else "multiple")
        counts[signature] += 1
    return counts


def report(scenario, journal):
    counts = collect(scenario, journal)
    return dict(version="resilience-semantic-coverage/1", scenario=scenario.id,
                journal_digest=journal.digest(),
                scope="observed logical model states; no native resource/correctness verdict",
                distinct=len(counts), observations=sum(counts.values()),
                situations=[dict(signature=asdict(signature), count=count)
                            for signature, count in sorted(counts.items(), key=lambda item: repr(item[0]))])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scenario", type=Path, required=True)
    parser.add_argument("--journal", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    scenario = Scenario.from_json(json.loads(args.scenario.read_text()))
    journal = Journal.read(args.journal)
    args.out.write_text(json.dumps(report(scenario, journal), indent=2) + "\n")


if __name__ == "__main__":
    main()
