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
    """Return the object REV names now, never guessing across the rewrite.

    A hex REV that prefixes an OLD sha in the commit map resolves through the
    map (the map wins: an old coordinate is what such a citation means); if
    the same abbreviation also names a DIFFERENT object of the rewritten
    repository, it is refused as ambiguous, never resolved silently.  A REV
    the map does not know resolves as an ordinary git revision, else refused.
    """
    current = None
    found = subprocess.run(['git', '-C', str(root), 'rev-parse', '--verify', '--quiet',
                            '--end-of-options', rev + '^{object}'],
                           capture_output=True, text=True)
    if found.returncode == 0:
        current = found.stdout.strip()
    matches = []
    if re.fullmatch(r'[0-9a-fA-F]{1,40}', rev):
        try:
            lines = (root / 'planning/commit-map-20261002.txt').read_text().splitlines()
        except FileNotFoundError:
            lines = []
        for line in lines:
            parts = line.split()
            if len(parts) == 2 and parts[0].startswith(rev.lower()):
                matches.append(parts[1])
    if not matches:
        if current is None:
            raise UnmappedRevision(f'unmapped historical revision: {rev}')
        return current
    if len(matches) > 1:
        raise AmbiguousRevision(f'ambiguous historical revision: {rev}')
    target = matches[0]
    if target == '0' * 40:
        raise UnmappedRevision(f'unmapped historical revision: {rev}')
    if current is not None and current != target:
        raise AmbiguousRevision(f'ambiguous revision: {rev} is an old sha mapped to {target} '
                                f'and also names current object {current}')
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
