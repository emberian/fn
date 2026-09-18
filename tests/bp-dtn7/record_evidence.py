#!/usr/bin/env python3
"""Turn one completed harness artifact into compact reproducibility evidence."""
import argparse
import hashlib
import json
import platform
import subprocess
from datetime import datetime, timezone
from pathlib import Path


def sha256(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def line(command, cwd=None):
    return subprocess.check_output(command, cwd=cwd, text=True).strip()


def manifest(path):
    return dict(line.split("=", 1) for line in Path(path).read_text().splitlines()
                if "=" in line)


parser = argparse.ArgumentParser()
parser.add_argument("--repo", required=True)
parser.add_argument("--artifact", required=True)
parser.add_argument("--harness", required=True)
parser.add_argument("--output", required=True)
args = parser.parse_args()
repo, artifact, harness = map(Path, (args.repo, args.artifact, args.harness))
result = json.loads((artifact / "results.json").read_text())
run_manifest = manifest(artifact / "manifest.txt")
data = {
    "schema": 1,
    "created_utc": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
    "pin": {
        "upstream": "https://github.com/dtn7/dtn7-rs",
        "revision": line(["git", "rev-parse", "HEAD"], repo),
        "build_command": ["cargo", "build", "--release", "--locked"],
    },
    "versions": {
        "cargo": line(["cargo", "--version"]),
        "dtnd": line([str(repo / "target/release/dtnd"), "--version"]),
        "dtnsend": line([str(repo / "target/release/dtnsend"), "--version"]),
        "platform": platform.platform(),
    },
    "commands": [run_manifest["invocation"], "cargo build --release --locked"],
    "digests_sha256": {
        "harness": sha256(harness),
        "cargo_lock": sha256(repo / "Cargo.lock"),
        "dtnd": sha256(repo / "target/release/dtnd"),
        "dtnsend": sha256(repo / "target/release/dtnsend"),
        "dtnrecv": sha256(repo / "target/release/dtnrecv"),
        "dtnquery": sha256(repo / "target/release/dtnquery"),
    },
    "bundle_ids": run_manifest,
    "assertions": result,
    "artifact": str(artifact.resolve()),
    "limits": [
        "A dtn7-rs /insert reply is only an asynchronous submission reply, not BPA custody.",
        "Clean restart is observed; power-loss, quota, fairness, and delivery durability are unproven.",
        "Copied inbox file fsync plus renamed-inbox directory fsync stages bytes only; it is not fn validation, acceptance, receipt, or retention release.",
        "Endpoint pop is destructive and is deliberately excluded from the safe ingress branch.",
    ],
}
Path(args.output).write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
