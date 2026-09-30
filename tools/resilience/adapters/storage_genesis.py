"""Exact native scanner corruption fixture; no host checksum computation."""
import re
from ..journal import Journal
from ..checker import Verdict
from ..bp_slice_contract import octets, MissingObservation
from .bp_slice_observer import encode

EVENTS = ("genesis-valid-pair", "checksum-breaking-refusal", "intact-alternate-chain-refusal")


class Observer:
    def __init__(self):
        self.journal = Journal("storage-genesis-corruption")
        self.seen = []

    def __call__(self, event, **values):
        if len(self.seen) >= len(EVENTS) or event != EVENTS[len(self.seen)]:
            raise ValueError("missing or reordered native storage observation")
        self.journal.environment(event, **encode(values))
        self.seen.append(event)


def judge(journal, expected_source):
    base = dict(scenario_id=journal.scenario_id, journal_digest=journal.digest(),
                pending_rules=["storage-native-qualification", "storage-broader-mutation-corpus"])
    rows = [r for r in journal.records if r.get("event") in EVENTS]
    artifacts = [r for r in journal.of_kind("environment") if r.get("event") == "image-artifact-coordinate"]
    if (not isinstance(expected_source, str) or not re.fullmatch(r"[0-9a-f]{40}", expected_source)
            or journal.scenario_id != "storage-genesis-corruption"
            or tuple(r.get("event") for r in rows) != EVENTS
            or any(r["kind"] != "environment" for r in rows) or len(artifacts) != 1):
        return Verdict("harness-failure", cause="storage-observations-incomplete", **base).sign()
    image = artifacts[0]
    if (image.get("source") != expected_source or not image.get("launcher")
            or not image.get("manifest") or not isinstance(image.get("manifest_sha256"), str)
            or not re.fullmatch(r"[0-9a-f]{64}", image["manifest_sha256"])):
        return Verdict("harness-failure", cause="storage-image-coordinate", **base).sign()
    valid, broken, swapped = rows
    try:
        original, alternate = octets(valid, "original"), octets(valid, "alternate")
        mutated = octets(broken, "mutated")
        replacement = octets(swapped, "replacement")
        if len(original) <= 40 or original == alternate or octets(broken, "original") != original:
            raise MissingObservation("distinct complete native-generated frames missing")
        if valid.get("validation") != "both prior native digest commands succeeded":
            raise MissingObservation("prior actual native open validation missing")
        left, right = valid.get("original_digest"), valid.get("alternate_digest")
        if not isinstance(left, list) or not isinstance(right, list) or any(not isinstance(x, str) for x in left + right):
            raise MissingObservation("actual digest output missing")
        genesis = lambda lines: [s for s in lines if s.startswith("digest genesis ")]
        rest = lambda lines: [s for s in lines if not s.startswith("digest genesis ")]
        if len(genesis(left)) != 1 or len(genesis(right)) != 1 or genesis(left) == genesis(right) or rest(left) != rest(right):
            raise MissingObservation("successful equivalent native opens of distinct genesis missing")
        expected = bytearray(original)
        expected[40] ^= 1
        if broken.get("offset") != 40 or broken.get("xor") != 1 or mutated != bytes(expected) or replacement != alternate:
            raise MissingObservation("exact retained mutation bytes mismatch")
        for row in (broken, swapped):
            if type(row.get("exit_code")) is not int:
                raise MissingObservation("actual scanner returncode missing")
        diagnostic = octets(broken, "stdout") + octets(broken, "stderr")
        swapped_stdout = octets(swapped, "stdout")
        octets(swapped, "stderr")
    except MissingObservation as error:
        return Verdict("harness-failure", cause="storage-fact-missing:" + str(error), **base).sign()
    if broken["exit_code"] != 1 or b"reason=genesis-damaged" not in diagnostic:
        return Verdict("violation", cause="damaged-genesis-refused", surviving=0, **base).sign()
    if swapped["exit_code"] == 0 or b"digest state " in swapped_stdout:
        return Verdict("violation", cause="intact-alternate-chain-refused", surviving=0, **base).sign()
    return Verdict("consistent", surviving=1,
                   witnesses_observed=["checksum-breaking-frame-refused", "intact-valid-frame-chain-refused"],
                   diagnostics=["Alternate integrity comes from prior successful actual native open; host does not recompute checksum."], **base).sign()


def run_fixture(output, expected_source):
    """One existing native test; refuse source mismatch before mixed-store setup."""
    import hashlib
    import unittest
    from pathlib import Path
    from tests import native_image_provenance
    from tests import test_native_replay_determinism as fixture
    if not isinstance(expected_source, str) or not re.fullmatch(r"[0-9a-f]{40}", expected_source):
        raise ValueError("immutable expected source required")
    image = Path(fixture.IMAGE).resolve(strict=True)
    manifest = image.parent / "MANIFEST.json"
    if native_image_provenance._published_source(image) != expected_source:
        raise ValueError("native scanner image source mismatch")
    manifest_digest = hashlib.sha256(manifest.read_bytes()).hexdigest()
    observer = Observer()
    case = fixture.NativeReplayDeterminismTests("test_g_the_genesis_is_read_only_where_it_must_be")
    case.resilience_observer = observer
    result = unittest.TestResult()
    unittest.TestSuite([case]).run(result)
    if not result.wasSuccessful() or result.skipped or tuple(observer.seen) != EVENTS:
        observer.journal.write(str(output) + ".incomplete.jsonl")
        raise RuntimeError("native storage fixture failed or skipped; no complete verdict")
    if (native_image_provenance._published_source(image) != expected_source
            or hashlib.sha256(manifest.read_bytes()).hexdigest() != manifest_digest):
        raise ValueError("native storage image changed during fixture")
    observer.journal.environment("image-artifact-coordinate", source=expected_source,
                                 launcher=str(image), manifest=str(manifest),
                                 manifest_sha256=manifest_digest, core_integrity_gate="runner-required")
    observer.journal.write(output)
    return judge(observer.journal, expected_source)
