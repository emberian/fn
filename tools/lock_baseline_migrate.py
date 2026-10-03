#!/usr/bin/env python3
"""Translate historical line-based callback keys without adding baseline debt.

  python3 tools/lock_baseline_migrate.py --source REV [--baseline PATH] [--write]

REV must contain the exact current baseline bytes. Callback identities are
derived from that revision's host and contracts, never guessed from today's line
numbers. Ambiguous/missing callback mappings and key collisions refuse migration.
"""
import argparse
import copy
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import tarfile
import tempfile

import lock_discipline_check as ldc

CALLBACK = re.compile(r"(?:lambda@|thread:[^@|]+@)[\w/.-]+\.lisp:\d+")


def git(root, *args):
    return subprocess.run(["git", *args], cwd=root, capture_output=True, check=True).stdout


def migrate_keys(data, identities, source, digest):
    result = copy.deepcopy(data)
    keys = set()
    for row in result["findings"]:
        def replace(match):
            old = match.group()
            names = identities.get(old, set())
            if len(names) != 1:
                raise ValueError(f"{old}: expected one historical callback, found {sorted(names)}")
            return next(iter(names))
        row["key"] = CALLBACK.sub(replace, row["key"])
        if row["key"] in keys:
            raise ValueError("migration would merge distinct baseline rows: " + row["key"])
        keys.add(row["key"])
    result["identity_source"] = {"revision": source, "baseline_sha256": digest}
    return result


def historical_identities(root, source):
    """Analyze only historical host syntax; no build, evaluator or current aliases."""
    archive = git(root, "archive", source, "host/native", "tools/lock_discipline_contracts.json")
    with tempfile.TemporaryDirectory(prefix="lock-baseline-") as tmp:
        historical = Path(tmp)
        with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
            tar.extractall(historical, filter="data")
        contracts = ldc.load_contracts(historical / "tools/lock_discipline_contracts.json")
        analyzer = ldc.Analyzer(ldc.collect_tree(historical), contracts, {})
        analyzer.param_sites = {}
        analyzer.analyze()
        identities = {}
        for name, info in analyzer.infos.items():
            if name.startswith("lambda@"):
                old = f"lambda@{info.path}:{info.line}"
            elif name.startswith("thread:"):
                old = name.split("@", 1)[0] + f"@{info.path}:{info.line}"
            else:
                continue
            identities.setdefault(old, set()).add(name)
        return identities


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", required=True)
    parser.add_argument("--baseline", type=Path, default=ldc.BASELINE)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    root = Path(git(Path.cwd(), "rev-parse", "--show-toplevel").decode().strip())
    source = git(root, "rev-parse", args.source).decode().strip()
    path = args.baseline.resolve()
    rel = path.relative_to(root).as_posix()
    data = path.read_bytes()
    if git(root, "show", source + ":" + rel) != data:
        parser.error("--source must contain the exact baseline being migrated")
    migrated = migrate_keys(json.loads(data), historical_identities(root, source), source,
                            hashlib.sha256(data).hexdigest())
    before = json.loads(data)["findings"]
    print(f"{len(before)} rows; weight {sum(r.get('count', 1) for r in before)} unchanged")
    if args.write:
        path.write_text(json.dumps(migrated, indent=1) + "\n")
    else:
        print("review source coordinate, then use --write")


if __name__ == "__main__":
    main()
