#!/usr/bin/env python3
"""fn's release sequence (D37): release order is a sequence, never a number.

    python3 tools/release_sequence.py position VERSION
    python3 tools/release_sequence.py next VERSION [--final]
    python3 tools/release_sequence.py is-next PREV NEW
    python3 tools/release_sequence.py cut-check VERSION [TAG ...]

ember, 2026-09-27: the first release is 6.6.0, then 6.6.1 to 6.6.5, then the
6.7.x series (6.7.0, 6.7.1, ..., open-ended), then 6.6.6, the final release,
and after it every release appends one more .6 (6.6.6.6, 6.6.6.6.6, ...).
So 6.6.6 follows 6.7.41, and 6.6.5 precedes 6.7.0: no comparison of version
numbers says anything about release order.  The sequence is written in
planning/release-sequence.json; this module reads it and is the only place
that decides order.  `position' is (segment, index), segments in the file's
order; `next' is the successor within the sequence (6.7.N has two: 6.7.N+1,
and with --final the first entry of the next segment); `cut-check' is
tools/cut_release.sh gate 01: VERSION is the next entry after the newest
existing v* tag (by position), or the first entry when there is none, or
VERSION's own tag is the newest (the cut's own commit, re-run).
Stdlib only; nothing here reads git or the network.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SEQUENCE_FILE = ROOT / "planning" / "release-sequence.json"
_NUMERAL = re.compile(r"0|[1-9][0-9]*\Z")


class NotInSequence(ValueError):
    """A well-formed version that is not an entry of the release sequence."""


def parse(text: str) -> tuple[int, ...]:
    """Dotted decimal numerals without leading zeros, any number of components."""
    if not isinstance(text, str) or not text:
        raise ValueError(f"not a version: {text!r}")
    parts = text.split(".")
    if not all(_NUMERAL.fullmatch(p) for p in parts):
        raise ValueError(f"not a version (dotted numerals, no leading zeros): {text!r}")
    return tuple(int(p) for p in parts)


def load(path: Path | None = None) -> list[dict]:
    data = json.loads((path or SEQUENCE_FILE).read_text())
    segments = data["segments"]
    for i, seg in enumerate(segments):
        kind = seg.get("kind")
        if kind == "list":
            for v in seg["versions"]:
                parse(v)
            if not seg["versions"]:
                raise ValueError(f"segment {i} lists no versions")
        elif kind == "counter":
            parse(seg["prefix"] + str(seg["start"]))
        elif kind == "append":
            parse(seg["first"])
            parse(seg["first"] + seg["append"])
            if i != len(segments) - 1:
                raise ValueError("an append segment never ends, so it is the last")
        else:
            raise ValueError(f"segment {i}: unknown kind {kind!r}")
    return segments


def _first_of(seg: dict) -> str:
    kind = seg["kind"]
    if kind == "list":
        return seg["versions"][0]
    if kind == "counter":
        return seg["prefix"] + str(seg["start"])
    return seg["first"]


def _index_in(seg: dict, version: str) -> int | None:
    kind = seg["kind"]
    if kind == "list":
        return seg["versions"].index(version) if version in seg["versions"] else None
    if kind == "counter":
        prefix = seg["prefix"]
        if version.startswith(prefix) and _NUMERAL.fullmatch(version[len(prefix):]):
            n = int(version[len(prefix):])
            return n - seg["start"] if n >= seg["start"] else None
        return None
    first, tail = seg["first"], seg["append"]
    if not version.startswith(first):
        return None
    rest = version[len(first):]
    k, r = divmod(len(rest), len(tail))
    return k if r == 0 and rest == tail * k else None


def position(version: str, segments: list[dict] | None = None) -> tuple[int, int]:
    """(segment, index within it): the release order, compared as a pair."""
    parse(version)
    segments = segments if segments is not None else load()
    for i, seg in enumerate(segments):
        j = _index_in(seg, version)
        if j is not None:
            return (i, j)
    raise NotInSequence(f"{version} is not in the release sequence ({SEQUENCE_FILE.name})")


def _at(seg: dict, j: int) -> str | None:
    kind = seg["kind"]
    if kind == "list":
        return seg["versions"][j] if j < len(seg["versions"]) else None
    if kind == "counter":
        return seg["prefix"] + str(seg["start"] + j)
    return seg["first"] + seg["append"] * j


def successors(version: str, segments: list[dict] | None = None) -> tuple[str, ...]:
    """Every entry that may follow VERSION: one, or two at an open-ended
    counter (its next entry, then the next segment's first)."""
    segments = segments if segments is not None else load()
    i, j = position(version, segments)
    seg = segments[i]
    nxt = _at(seg, j + 1)
    out = [nxt] if nxt is not None else []
    if seg["kind"] == "counter" and i + 1 < len(segments):
        out.append(_first_of(segments[i + 1]))
    elif nxt is None and i + 1 < len(segments):
        out.append(_first_of(segments[i + 1]))
    return tuple(out)


def next(version: str, final: bool = False, segments: list[dict] | None = None) -> str:  # noqa: A001
    """The release after VERSION.  In an open-ended counter (the 6.7.x
    series) that is 6.7.N+1, or with FINAL the next segment's first entry
    (6.6.6); FINAL anywhere else is an error."""
    segments = segments if segments is not None else load()
    succ = successors(version, segments)
    i, _ = position(version, segments)
    if final:
        if segments[i]["kind"] != "counter" or len(succ) < 2:
            raise ValueError(f"--final applies only inside an open-ended series, not at {version}")
        return succ[1]
    return succ[0]


def first(segments: list[dict] | None = None) -> str:
    segments = segments if segments is not None else load()
    return _first_of(segments[0])


def is_next(prev: str | None, new: str, segments: list[dict] | None = None) -> bool:
    """NEW is a permitted successor of PREV (PREV None: NEW is the first)."""
    segments = segments if segments is not None else load()
    try:
        position(new, segments)
    except ValueError:
        return False
    if prev is None:
        return new == first(segments)
    try:
        return new in successors(prev, segments)
    except ValueError:
        return False


def newest(versions, segments: list[dict] | None = None) -> str | None:
    """The latest in sequence order of VERSIONS (all must be entries)."""
    segments = segments if segments is not None else load()
    best = None
    for v in versions:
        p = position(v, segments)
        if best is None or p > best[0]:
            best = (p, v)
    return best[1] if best else None


def cut_check(version: str, tags, segments: list[dict] | None = None) -> tuple[bool, str]:
    """Gate 01's rule over the repository's tags (git tag -l output)."""
    segments = segments if segments is not None else load()
    try:
        position(version, segments)
    except ValueError as e:
        return False, f"VERSION {version!r}: {e}"
    released = []
    for t in tags:
        if not t.startswith("v"):
            continue
        try:
            position(t[1:], segments)
        except ValueError:
            return False, f"tag {t} is not an entry of the release sequence; it cannot be ordered"
        released.append(t[1:])
    last = newest(released, segments)
    if version in released:
        if version == last:
            return True, f"v{version} is the newest tag (the cut's own)"
        return False, f"v{version} is already tagged and v{last} follows it: VERSION is stale"
    if is_next(last, version, segments):
        return True, (f"{version} is the first release" if last is None
                      else f"{version} follows v{last}, the newest tag")
    want = first(segments) if last is None else " or ".join(successors(last, segments))
    after = "no v* tag exists" if last is None else f"the newest tag is v{last}"
    return False, f"VERSION is {version}, but {after}: VERSION must be {want}"


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("position"); p.add_argument("version")
    p = sub.add_parser("next"); p.add_argument("version"); p.add_argument("--final", action="store_true")
    p = sub.add_parser("is-next"); p.add_argument("prev"); p.add_argument("new")
    p = sub.add_parser("cut-check"); p.add_argument("version"); p.add_argument("tags", nargs="*")
    a = ap.parse_args(argv)
    try:
        if a.cmd == "position":
            print("%d %d" % position(a.version))
        elif a.cmd == "next":
            print(next(a.version, final=a.final))
        elif a.cmd == "is-next":
            ok = is_next(a.prev, a.new)
            print("yes" if ok else "no")
            return 0 if ok else 1
        else:
            ok, why = cut_check(a.version, a.tags)
            print(why)
            return 0 if ok else 1
    except ValueError as e:
        print(f"release_sequence: {e}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
