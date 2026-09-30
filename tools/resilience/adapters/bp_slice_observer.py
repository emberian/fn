"""Lossless SCN1046 observations; collection alone makes no native verdict.

Attach to NativeBpNodeTests.resilience_observer before running the real test.
A failed or skipped fixture must not call finish(). No diagnostic durability
marker is promoted to a client acceptance promise.
"""
from ..journal import Journal

EVENTS = (
    "post-observed", "post-observed", "fixture", "decision-cut-readback", "application-replay",
    "outbox-process-death", "receipt-contact-uncertain",
    "checkpoint-stage-cut", "receipt-contact-resumed",
    "receipt-obligation-settlement", "checkpoint-complete-readback",
    "retirement-frozen-report",
)


# Callbacks report actual client results or observed process death; durable
# stdout strings remain diagnostics inside those records, never POST promises.
OBSERVATION_KINDS = {event: "client" for event in EVENTS}
OBSERVATION_KINDS.update({"outbox-process-death": "environment",
                          "checkpoint-stage-cut": "environment"})


def encode(value):
    """Preserve bytes without decoding, normalization or opaque-ID hashing."""
    if isinstance(value, bytes):
        return {"octets_hex": value.hex()}
    if isinstance(value, (list, tuple)):
        return [encode(item) for item in value]
    if isinstance(value, dict):
        return {key: encode(item) for key, item in value.items()}
    if value is None or isinstance(value, (str, int, bool)):
        return value
    raise TypeError("unsupported observation type: " + type(value).__name__)


class SliceObserver:
    def __init__(self):
        self.journal = Journal("bp-disconnected-delivery-recovery")
        self.seen = []
        self.complete = False

    def __call__(self, event, **values):
        if self.complete or len(self.seen) >= len(EVENTS):
            raise ValueError("observation after fixture completion")
        if event != EVENTS[len(self.seen)]:
            raise ValueError("missing or reordered SCN1046 observation: " + event)
        if event == "fixture":
            source = values.get("source", "")
            if (not isinstance(source, str) or len(source) != 40 or
                    any(c not in "0123456789abcdef" for c in source)):
                raise ValueError("missing validated image source coordinate")
        self.journal.append(OBSERVATION_KINDS[event], event=event, **encode(values))
        self.seen.append(event)

    def finish(self, path):
        """Seal only after the caller independently confirms fixture success.

        This artifact is diagnostic input for the scenario adapter/checker;
        completeness does not imply a legal execution or qualification.
        """
        if tuple(self.seen) != EVENTS or self.complete:
            raise ValueError("incomplete or already sealed SCN1046 observation")
        self.journal.environment("fixture-observations-complete",
                                 semantic_verdict="pending")
        result = self.journal.write(path)
        self.complete = True
        return result


def run_fixture(output, expected_source):
    """Run the actual composed native test once; skips never seal a journal.

    Image selection remains the native harness's explicit environment. This
    function neither builds an image nor silently substitutes another fixture.
    """
    import unittest
    from pathlib import Path
    import hashlib
    import re
    from tests.test_bp_node_native import NativeBpNodeTests, PRODUCER, IMAGE
    from tests.native_image_provenance import _published_source

    if not isinstance(expected_source, str) or not re.fullmatch(r"[0-9a-f]{40}", expected_source):
        raise ValueError("expected immutable image source required")
    coordinates = []
    for image in (PRODUCER, IMAGE):
        if _published_source(image) != expected_source:
            raise ValueError("selected published image differs from expected source")
        launcher = Path(image).resolve(strict=True)
        manifest = launcher.parent / "MANIFEST.json"
        coordinates.append(dict(launcher=str(launcher), manifest=str(manifest),
                                manifest_sha256=hashlib.sha256(manifest.read_bytes()).hexdigest(),
                                source=expected_source))

    observer = SliceObserver()
    fixture = NativeBpNodeTests(
        "test_disconnected_delivery_restarts_and_releases_only_matching_obligation")
    fixture.resilience_observer = observer
    result = unittest.TestResult()
    fixture.run(result)
    if result.skipped:
        raise RuntimeError("native fixture skipped: " + result.skipped[0][1])
    if result.errors or result.failures:
        # Retain the observed prefix, but never represent it as a complete run.
        prefix = Path(output).with_suffix(".incomplete.jsonl")
        prefix.parent.mkdir(parents=True, exist_ok=True)
        prefix.write_text("\n".join(observer.journal._line(record)
                                    for record in observer.journal.records) + "\n")
        failures = result.errors + result.failures
        raise RuntimeError("native fixture failed; unsealed prefix at " +
                           str(prefix) + "\n" + failures[0][1])
    target = Path(output)
    target.parent.mkdir(parents=True, exist_ok=True)
    for image, coordinate in zip((PRODUCER, IMAGE), coordinates):
        if (_published_source(image) != expected_source or
                hashlib.sha256(Path(coordinate["manifest"]).read_bytes()).hexdigest() !=
                coordinate["manifest_sha256"]):
            raise RuntimeError("published image coordinate changed during fixture")
    observer.journal.environment("image-artifact-coordinate", images=coordinates,
                                 core_integrity_gate="runner-required")
    return observer.finish(target)


def judge_file(path, source, output):
    """Re-read the sealed observations and retain the separate checker verdict."""
    import json
    from pathlib import Path
    from ..checker import check_bp_slice_observations
    journal = Journal.read(path)
    verdict = check_bp_slice_observations(journal, expected_source=source)
    Path(output).write_text(json.dumps(verdict.to_json(), indent=2) + "\n")
    return verdict


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True)
    parser.add_argument("--journal", help="judge an existing sealed trace instead of executing")
    parser.add_argument("--source", required=True, help="expected immutable image source commit")
    parser.add_argument("--verdict", required=True)
    args = parser.parse_args()
    journal = args.journal or run_fixture(args.out, args.source)
    result = judge_file(journal, args.source, args.verdict)
    print(result.kind + ": " + str(result.cause))
    raise SystemExit(0 if result.kind == "consistent" else 1)
