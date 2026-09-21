#!/usr/bin/env python3
"""Exercise native authored-wire no-replace publication and recovery outcomes."""
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path


AUTHORED = re.compile(r"^BP authored creation=(\d+) sequence=(\d+) ", re.MULTILINE)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def prepare(root: Path) -> None:
    root.mkdir(parents=True)
    (root / "adu").write_bytes(b"authored wire durability\n")
    (root / "journal").mkdir()


def command(image: Path, root: Path) -> list[str]:
    return [str(image), "--fn", "bp", "send", "127.0.0.1", "1",
            str(root / "adu"), str(root / "journal"),
            "dtn://fn-a/", "dtn://fn-b/", "3600000", "2", "32",
            "1048576", "0", "100", "0"]


def invoke(image: Path, root: Path, fault: str | None = None) -> tuple[int, str]:
    env = dict(os.environ)
    if fault is not None:
        env["FN_IMMUTABLE_PUBLISH_TEST_FAIL"] = fault
    result = subprocess.run(command(image, root), text=True, capture_output=True,
                            env=env, timeout=45)
    return result.returncode, result.stdout + result.stderr


def authored_sequence(output: str) -> int | None:
    match = AUTHORED.search(output)
    return int(match.group(2)) if match else None


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--image", required=True)
    parser.add_argument("--work", help="retain report and native logs here")
    parser.add_argument("--source-revision", default="unknown")
    parser.add_argument("--artifact-set", default="unknown")
    args = parser.parse_args(argv)

    image = Path(args.image).resolve()
    if not image.is_file():
        raise SystemExit("missing native image: {}".format(image))
    work = (Path(args.work).resolve() if args.work else
            Path(tempfile.mkdtemp(prefix="fn-bp-authored-wire-")))
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)

    barrier = work / "barrier"
    prepare(barrier)
    file_rc, file_output = invoke(image, barrier, "file-barrier")
    file_final = barrier / "journal" / "authored-0.wire"
    namespace_rc, namespace_output = invoke(image, barrier, "namespace")
    namespace_final = barrier / "journal" / "authored-1.wire"
    namespace_visible = namespace_final.is_file()
    namespace_digest = digest(namespace_final) if namespace_visible else None
    restart_rc, restart_output = invoke(image, barrier)
    restart_final = barrier / "journal" / "authored-2.wire"

    template = work / "template"
    prepare(template)
    template_rc, template_output = invoke(image, template)
    template_wire = template / "journal" / "authored-0.wire"

    equal = work / "equal-collision"
    prepare(equal)
    equal_final = equal / "journal" / "authored-0.wire"
    shutil.copyfile(template_wire, equal_final)
    equal_before = digest(equal_final)
    equal_rc, equal_output = invoke(image, equal)
    equal_after = digest(equal_final)
    equal_restart_rc, equal_restart_output = invoke(image, equal)
    equal_restart_final = equal / "journal" / "authored-1.wire"

    different = work / "different-collision"
    prepare(different)
    different_final = different / "journal" / "authored-0.wire"
    different_final.write_bytes(b"contrary existing evidence\n")
    different_before = digest(different_final)
    different_rc, different_output = invoke(image, different)
    different_after = digest(different_final)
    different_restart_rc, different_restart_output = invoke(image, different)
    different_restart_final = different / "journal" / "authored-1.wire"

    outputs = {
        "file-barrier": file_output,
        "namespace-barrier": namespace_output,
        "restart": restart_output,
        "template": template_output,
        "equal-collision": equal_output,
        "equal-collision-restart": equal_restart_output,
        "different-collision": different_output,
        "different-collision-restart": different_restart_output,
    }
    for name, output in outputs.items():
        (work / (name + ".log")).write_text(output)

    report = {
        "scenario": "bp-authored-wire-immutable-publication",
        "image": str(image),
        "image_sha256": digest(image),
        "source_revision": args.source_revision,
        "artifact_set": args.artifact_set,
        "exit_codes": {
            "file_barrier": file_rc,
            "namespace_barrier": namespace_rc,
            "restart": restart_rc,
            "template": template_rc,
            "equal_collision": equal_rc,
            "equal_collision_restart": equal_restart_rc,
            "different_collision": different_rc,
            "different_collision_restart": different_restart_rc,
        },
        "sequences": {
            "file_barrier": authored_sequence(file_output),
            "namespace_barrier": authored_sequence(namespace_output),
            "restart": authored_sequence(restart_output),
            "template": authored_sequence(template_output),
            "equal_collision_restart": authored_sequence(equal_restart_output),
            "different_collision_restart": authored_sequence(
                different_restart_output),
        },
        "namespace_visible_after_error": namespace_visible,
        "namespace_visible_sha256": namespace_digest,
        "restart_final_exists": restart_final.is_file(),
        "equal_collision_unchanged": equal_before == equal_after,
        "different_collision_unchanged": different_before == different_after,
        "outputs": {name: output.splitlines() for name, output in outputs.items()},
    }
    report["ok"] = (
        file_rc == 1 and not file_final.exists() and
        "publication refused before link" in file_output and
        authored_sequence(file_output) is None and
        namespace_rc == 3 and namespace_visible and
        "publication outcome is uncertain" in namespace_output and
        authored_sequence(namespace_output) is None and
        restart_rc == 4 and authored_sequence(restart_output) == 2 and
        restart_final.is_file() and
        template_rc == 4 and authored_sequence(template_output) == 0 and
        equal_rc == 3 and "already occupied" in equal_output and
        equal_before == equal_after and
        equal_restart_rc == 4 and
        authored_sequence(equal_restart_output) == 1 and
        equal_restart_final.is_file() and
        different_rc == 3 and "already occupied" in different_output and
        different_before == different_after and
        different_restart_rc == 4 and
        authored_sequence(different_restart_output) == 1 and
        different_restart_final.is_file())
    (work / "report.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
