#!/usr/bin/env python3
"""Exercise BP's durable creation-sequence frontier in a native image.

This is deliberately a failed-connect test: reservation and durable FNBS
publication happen before TCPCL socket I/O, so it exposes the allocation cuts
without requiring a peer.  It injects a root-parent publication failure on an
existing journal, retries without the injection, restarts once, then corrupts
the durable frontier.  The report pins the image and source revision.
"""
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path


AUTHORED = re.compile(r"^BP authored creation=(\d+) sequence=(\d+) ")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def invoke(image: Path, root: Path, env: dict[str, str]) -> tuple[int, str]:
    adu = root / "adu"
    command = [str(image), "--fn", "bp", "send", "127.0.0.1", "1",
               str(adu), str(root / "journal"), "dtn://fn-a/", "dtn://fn-b/",
               "3600000", "2", "32", "1048576", "0", "100", "0"]
    result = subprocess.run(command, text=True, capture_output=True, env=env,
                            timeout=45)
    output = result.stdout + result.stderr
    return result.returncode, output


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--image", required=True)
    parser.add_argument("--work", help="retain report and native logs here")
    parser.add_argument("--source-revision", default="unknown")
    parser.add_argument("--artifact-set", default="unknown")
    args = parser.parse_args(argv)

    image = Path(args.image).resolve()
    if not image.is_file():
        raise SystemExit("missing native image: {}".format(image))
    if args.work:
        root = Path(args.work).resolve()
        if root.exists():
            shutil.rmtree(root)
        root.mkdir(parents=True)
    else:
        root = Path(tempfile.mkdtemp(prefix="fn-bp-sequence-"))
    (root / "adu").write_bytes(b"sequence durability\n")
    (root / "journal").mkdir()

    base_env = dict(os.environ)
    injected_env = dict(base_env)
    injected_env["FN_BP_TEST_FAIL_ROOT_PARENT_BARRIER"] = "1"
    injected_rc, injected = invoke(image, root, injected_env)
    first_rc, first = invoke(image, root, base_env)
    second_rc, second = invoke(image, root, base_env)
    frontier = root / "journal" / "sequence" / "frontier.fnb"
    frontier.write_bytes(b"\0")
    corrupt_rc, corrupt = invoke(image, root, base_env)

    for name, output in (("injected", injected), ("first", first),
                         ("second", second), ("corrupt", corrupt)):
        (root / (name + ".log")).write_text(output)
    first_match = AUTHORED.search(first)
    second_match = AUTHORED.search(second)
    report = {
        "scenario": "bp-sequence-root-publication-retry",
        "image": str(image), "image_sha256": digest(image),
        "source_revision": args.source_revision,
        "artifact_set": args.artifact_set,
        "exit_codes": {"injected": injected_rc, "first": first_rc,
                       "second": second_rc, "corrupt": corrupt_rc},
        "authored": {
            "first": first_match.groups() if first_match else None,
            "second": second_match.groups() if second_match else None,
        },
        "injected_output": injected.splitlines(),
        "corrupt_output": corrupt.splitlines(),
    }
    report["ok"] = (
        injected_rc == 3 and "root parent barrier failure" in injected and
        "BP authored" not in injected and first_rc == 4 and second_rc == 4 and
        first_match is not None and second_match is not None and
        first_match.group(1) == second_match.group(1) == "100" and
        first_match.group(2) == "0" and second_match.group(2) == "1" and
        corrupt_rc == 3 and "sequence frontier cannot be recovered" in corrupt and
        "BP authored" not in corrupt)
    (root / "report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
