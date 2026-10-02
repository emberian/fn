#!/usr/bin/env python3
"""Resolve Git lookups across the 2026-10-02 rewrite; never change identities.

Usage: python3 tools/commit_map.py OLD
Use the printed object name for git show, retaining OLD in provenance.
"""
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


class RevisionError(ValueError):
    """A requested historical coordinate cannot be resolved safely."""


class AmbiguousRevision(RevisionError):
    pass


class UnmappedRevision(RevisionError):
    pass


def resolve(rev: str, root: Path = ROOT) -> str:
    """Return an existing object, or the sole old-prefix mapping to one."""
    found = subprocess.run(['git', '-C', str(root), 'rev-parse', '--verify',
                            '--end-of-options', rev + '^{object}'],
                           capture_output=True, text=True)
    if found.returncode == 0:
        return found.stdout.strip()
    matches = []
    if re.fullmatch(r'[0-9a-fA-F]{1,40}', rev):
        try:
            lines = (root / 'planning/commit-map-20261002.txt').read_text().splitlines()
        except FileNotFoundError as error:
            raise UnmappedRevision(f'unmapped historical revision: {rev} (no commit map)') from error
        for line in lines:
            old, new = line.split()
            if old.startswith(rev.lower()):
                matches.append(new)
    if len(matches) > 1:
        raise AmbiguousRevision(f'ambiguous historical revision: {rev}')
    if len(matches) != 1 or matches[0] == '0' * 40:
        raise UnmappedRevision(f'unmapped historical revision: {rev}')
    target = matches[0]
    if subprocess.run(['git', '-C', str(root), 'cat-file', '-e', target],
                      capture_output=True).returncode:
        raise UnmappedRevision(f'historical revision {rev} maps to missing object {target}')
    return target


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise SystemExit('usage: commit_map.py REVISION')
    try:
        print(resolve(sys.argv[1]))
    except (RevisionError, OSError) as error:
        raise SystemExit(f'{type(error).__name__}: {error}')
