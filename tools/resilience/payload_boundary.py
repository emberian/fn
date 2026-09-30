"""Actual native POST boundary campaign, bound to persisted profile observations.

Literal reference: fn-sbud-named-profile-payload-bounds and
fn-sbud-post-boundary-refuses-exactly-past-the-profile-bound, PRF-110,
books/store-budget-naming.lisp at REFERENCE_SOURCE. This is a source fixture;
qualification of a matching image is separate. No host admission computation.
"""
import hashlib
import re
from pathlib import Path
from types import SimpleNamespace

from .payload_corpus import cases, preflight
from .scenario import Scenario, Operation, check

REFERENCE_SOURCE = "7ff69b8fc1c77c77139683e8b03589eca77b1686"
REFERENCE_BOOK_SHA256 = "3d9281d4b9b24474a4252427a4be61ab9c611fea98ee808644e13c8a7800e7d6"
NAMED_PROFILE_A = 32768
# Literal ACL2 refusal octets, an assertion reference, never emitted as a reply.
PAYLOAD_REFUSAL = b"payload exceeds the modelled bound"


def scenario(expected_image_source):
    if not isinstance(expected_image_source, str) or not re.fullmatch(r"[0-9a-f]{40}", expected_image_source):
        raise ValueError("immutable matching image source required")
    rows = cases([dict(name="fn-sbud-named-profile-payload-bounds/:development",
                       source=REFERENCE_SOURCE, octets=NAMED_PROFILE_A,
                       unit="complete-payload-octets")])
    posts = [Operation("payload-" + row["relation"], "client", "post",
                       dict(groups=["fn.letters"], payload=row["relation"], boundary_payload=row))
             for row in rows]
    reads = [Operation("read-" + op.id, "client", "read", dict(article=op.id)) for op in posts]
    recovery = Operation("recover", "client", "recover")
    return check(Scenario("native-profile-payload-boundary", "Persisted development profile A boundary",
        "local-commit-log", dict(recipe="empty-store", groups=["fn.letters"], prior=[],
            profile_flags=["--profile", "development"], payload_preparation_budget=sum(r["octets"] for r in rows),
            payload_boundary=dict(expected_image_source=expected_image_source, expected_profile_a=NAMED_PROFILE_A,
                reference_source=REFERENCE_SOURCE, reference_book_sha256=REFERENCE_BOOK_SHA256)),
        [{"name": "client", "kind": "client"}], posts + [recovery] + reads, [],
        [recovery.id] + [r.id for r in reads], ["post-accepted", "payload-bound-refused", "read-completed", "recovery-completed"],
        requirements=["STO-002"], replay="image"))


def image_preflight(scenario, image, journal):
    from tests.native_image_provenance import _published_source
    contract = scenario.initial.get("payload_boundary")
    if not isinstance(contract, dict):
        raise ValueError("boundary corpus native execution requires explicit persisted-profile contract")
    expected = contract.get("expected_image_source")
    if not isinstance(expected, str) or not re.fullmatch(r"[0-9a-f]{40}", expected):
        raise ValueError("immutable expected native image source required")
    image = Path(image).resolve(strict=True)
    if _published_source(image) != expected:
        raise ValueError("native boundary image source mismatch before Store mutation")
    manifest = image.parent / "MANIFEST.json"
    journal.environment("payload-boundary-image", source=expected, launcher=str(image),
        manifest=str(manifest), manifest_sha256=hashlib.sha256(manifest.read_bytes()).hexdigest(),
        core_integrity_gate="runner-required", qualification="unproved")


def image_unchanged(scenario, image, journal):
    from tests.native_image_provenance import _published_source
    from .adapters.native_cuts import HarnessFailure
    if "payload_boundary" not in scenario.initial:
        return
    rows = [r for r in journal.of_kind("environment") if r.get("event") == "payload-boundary-image"]
    if len(rows) != 1:
        raise HarnessFailure("boundary-image-coordinate-lost")
    try:
        row = rows[0]
        if (_published_source(image) != row["source"]
                or hashlib.sha256(Path(row["manifest"]).read_bytes()).hexdigest() != row["manifest_sha256"]):
            raise HarnessFailure("boundary-image-changed-during-execution")
    except (OSError, KeyError, TypeError, ValueError) as error:
        raise HarnessFailure("boundary-image-recheck-failed:" + str(error)) from error


def require_prepared_payload(operation, path, journal):
    from .adapters.native_cuts import HarnessFailure
    if "boundary_payload" not in operation.args:
        return
    rows = [r for r in journal.of_kind("environment")
            if r.get("event") == "boundary-payload-prepared" and r.get("operation") == operation.id]
    if len(rows) != 1:
        raise HarnessFailure("prepared-boundary-payload-missing:" + operation.id)
    digest, size = hashlib.sha256(), 0
    with Path(path).open("rb") as stream:
        while chunk := stream.read(8192):
            digest.update(chunk)
            size += len(chunk)
    if size != rows[0]["prepared_octets"] or digest.hexdigest() != rows[0]["sha256"]:
        raise HarnessFailure("prepared-boundary-payload-changed:" + operation.id)


def require_profile(scenario, result):
    from tools.outcome_codes import EXIT
    from .adapters.native_cuts import HarnessFailure
    if result.returncode != EXIT.OK:
        raise HarnessFailure("persisted-payload-profile-unobserved")
    rows = [line for line in result.stdout.splitlines() if line.startswith(b"profile ")]
    if len(rows) != 1:
        raise HarnessFailure("persisted-payload-profile-ambiguous")
    values = re.findall(rb"(?:^| )max-article-octets=([0-9]+)(?: |$)", rows[0])
    expected = scenario.initial["payload_boundary"].get("expected_profile_a")
    if type(expected) is not int or expected < 0 or len(values) != 1 or int(values[0]) != expected:
        raise HarnessFailure("persisted-payload-profile-mismatch")


def inspect(scenario, journal):
    """(kind, cause) on missing/wrong/uncertain facts; None allows full history check."""
    if "payload_boundary" not in scenario.initial:
        return None
    from .adapters.native_cuts import HarnessFailure, _reply_outcome
    try:
        preflight(scenario.posts(), scenario.initial.get("payload_preparation_budget"))
        metadata = scenario.initial["payload_boundary"]
        if (metadata.get("reference_source") != REFERENCE_SOURCE
                or metadata.get("reference_book_sha256") != REFERENCE_BOOK_SHA256
                or metadata.get("expected_profile_a") != NAMED_PROFILE_A):
            raise ValueError("unsupported literal profile reference")
        artifacts = [r for r in journal.of_kind("environment") if r.get("event") == "payload-boundary-image"]
        if len(artifacts) != 1 or artifacts[0].get("source") != metadata.get("expected_image_source"):
            raise ValueError("image coordinate missing or mismatched")
        if not re.fullmatch(r"[0-9a-f]{64}", artifacts[0].get("manifest_sha256", "")):
            raise ValueError("image manifest digest missing")
        profiles = [r for r in journal.of_kind("environment") if r.get("event") == "persisted-payload-profile"]
        if len(profiles) != 1:
            raise ValueError("persisted profile observation missing")
        require_profile(scenario, SimpleNamespace(returncode=profiles[0]["returncode"],
            stdout=bytes.fromhex(profiles[0]["stdout_hex"])))
        uncertain = []
        for op in scenario.posts():
            descriptor = op.args["boundary_payload"]
            prepared = [r for r in journal.of_kind("environment")
                        if r.get("event") == "boundary-payload-prepared" and r.get("operation") == op.id]
            replies = [r for r in journal.of_kind("client") if r.get("event") == "reply" and r.get("operation") == op.id]
            if len(prepared) != 1 or len(replies) != 1:
                raise ValueError("payload preparation/reply missing or repeated")
            if any(prepared[0].get(k) != v for k, v in descriptor.items()) or prepared[0].get("prepared_octets") != descriptor["octets"]:
                raise ValueError("prepared payload differs from retained descriptor")
            if not re.fullmatch(r"[0-9a-f]{64}", prepared[0].get("sha256", "")):
                raise ValueError("prepared payload digest missing")
            if (descriptor["boundary_octets"] != metadata["expected_profile_a"]
                    or descriptor["source"] != REFERENCE_SOURCE):
                raise ValueError("payload descriptor differs from observed profile A/reference")
            reply = replies[0]
            processes = [r for r in journal.of_kind("environment")
                         if r.get("event") == "post-process-result" and r.get("operation") == op.id]
            if len(processes) != 1 or any(processes[0].get(k) != reply.get(k)
                                          for k in ("returncode", "stdout_hex", "stderr_hex")):
                raise ValueError("client reply differs from retained native process result")
            if not (artifacts[0]["seq"] < prepared[0]["seq"] < processes[0]["seq"] < reply["seq"]
                    and profiles[0]["seq"] < processes[0]["seq"]):
                raise ValueError("image/preparation/profile/process/reply observation order differs")
            result = SimpleNamespace(returncode=reply["returncode"], stdout=bytes.fromhex(reply["stdout_hex"]),
                                     stderr=bytes.fromhex(reply["stderr_hex"]))
            outcome = _reply_outcome(result)
            if outcome != reply.get("outcome"):
                raise ValueError("reply class differs from observed native result")
            if outcome in ("uncertain", "lost"):
                uncertain.append(op.id)
                continue
            if descriptor["relation"] == "above":
                if outcome != "refused" or not named_refusal(op, reply):
                    return "violation", "above-A-not-named-payload-refusal:" + op.id
            elif outcome != "accepted":
                return "violation", "within-A-not-accepted:" + op.id
        if uncertain:
            return "inconclusive", "payload-boundary-outcome-uncertain:" + ",".join(uncertain)
    except (KeyError, TypeError, ValueError, HarnessFailure) as error:
        return "harness-failure", "payload-boundary-fact-missing:" + str(error)
    return None


def named_refusal(op, row):
    if op.args.get("boundary_payload", {}).get("relation") != "above" or row.get("outcome") != "refused":
        return False
    try:
        data = bytes.fromhex(row["stderr_hex"])
        return any(line == PAYLOAD_REFUSAL or line.endswith(b": " + PAYLOAD_REFUSAL) for line in data.splitlines())
    except (KeyError, TypeError, ValueError):
        return False


def main(argv=None):
    """Explicit one-scenario runner; preparation alone is never a native verdict."""
    import argparse
    import json
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-source", required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--image", type=Path)
    parser.add_argument("--execute", action="store_true")
    args = parser.parse_args(argv)
    if args.execute and args.image is None:
        parser.error("--execute requires the matching published --image")
    selected = scenario(args.expected_source)
    args.out.mkdir(parents=True, exist_ok=False)
    selected.dump(args.out / "scenario.json")
    if not args.execute:
        print("Prepared boundary scenario only; native admission/refusal/uncertain outcomes unobserved.")
        return 0
    from .adapters.native_cuts import run
    _, verdict = run(selected, args.image, args.out)
    print(json.dumps(dict(kind=verdict.kind, cause=verdict.cause, witnesses=verdict.witnesses_observed,
                          pending=verdict.pending_rules, scope="selected-image observations; native qualification separate")))
    return 0 if verdict.green else 1


if __name__ == "__main__":
    raise SystemExit(main())
