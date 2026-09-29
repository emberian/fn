#!/usr/bin/env python3
"""The replay dispatcher's alphabet is the writers' alphabet, generated.

B10 (2026-09-29) was a record kind the open did not account for: the writers
of the configuration journal gained kinds (:set-limit, :withdraw-article,
...) and the open's frontier fold read article records only.  Every event
family in the tree has a WRITER side (the constructors, the encoder) and a
READER side (the decoder, the replay's dispatch); when they are one
`defevent' form (books/defevent.lisp) they agree by construction and
tools/event_emit.py keeps the codes stable.  The two families that are not
one form are the store's configuration deltas (books/config.lisp) and the
store log's events (books/store-events.lisp, books/replay.lisp,
books/replay-identity-index.lisp).  This reads their tables from the source
with tools/reach_check.py's reader, never a copy typed here, and

  FAILS when a writer produces a kind the dispatcher lacks: a
  `(fn-cfg-delta-make :K ...)' anywhere in books/ or host/ whose :K
  `fn-cfg-apply-delta' has no arm for, or whose code `fn-cfg-kind-code' /
  `fn-cfg-code-kind' do not carry; a store event predicate
  `fn-store-event-encode' encodes that `fn-store-event-decode',
  `fn-store-event-kind', `fn-replay-apply-record' or
  `fn-rii-apply-record' has no arm for;

  REPORTS (never fails) a dispatcher arm no writer reaches: a dead arm is a
  retired kind, and the retirement is event_emit's business.

The one hand-written table: the wire event predicate of each store event
predicate (`fn-record-p' is `fn-held-p' through alpha, `fn-stxa-p' is
`fn-hstxa-p': books/catalog-record.lisp fn-held-wire-of), because the
encoder sees the wire event and the replay sees the row the arena holds.

    python3 tools/alphabet_check.py             # the tables and the findings
    python3 tools/alphabet_check.py --summary   # the line `make check` prints
    python3 tools/alphabet_check.py --strict    # exit 1 on a writer kind the
                                                # dispatcher lacks
"""
from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

import reach_check  # noqa: E402

ROOT = reach_check.ROOT
CONFIG = ROOT / "books" / "config.lisp"
STORE_EVENTS = ROOT / "books" / "store-events.lisp"
REPLAY = ROOT / "books" / "replay.lisp"
RII = ROOT / "books" / "replay-identity-index.lisp"
EVENTS_JSON = ROOT / "planning" / "events.json"

# Store event predicates: (wire predicate, the row predicate the replay sees).
WIRE_TO_ROW = {"fn-record-p": "fn-held-p", "fn-stxa-p": "fn-hstxa-p"}
# The replay dispatches the composite through its held row.
ROW_ALIASES = {"fn-replay-composite-held": "fn-hstxa-p"}


def definition(path: pathlib.Path, name: str) -> str:
    text = path.read_text(encoding="utf-8", errors="replace")
    for form in reach_check.forms(text):
        if re.match(r"\(\s*(defun|defund|defconst)\s+" + re.escape(name) + r"[\s)]", form):
            return form
    raise SystemExit(f"alphabet_check: {path.relative_to(ROOT)} defines no {name}")


def kinds_in(form: str, pattern: str) -> set[str]:
    return set(re.findall(pattern, form))


def config_tables() -> dict[str, set[str]]:
    declared = kinds_in(definition(CONFIG, "*fn-cfg-delta-kinds*"), r":[a-z][a-z0-9-]*")
    kind_code = kinds_in(definition(CONFIG, "fn-cfg-kind-code"), r"\(equal kind (:[a-z][a-z0-9-]*)\)")
    code_kind = kinds_in(definition(CONFIG, "fn-cfg-code-kind"), r"\)\s*(:[a-z][a-z0-9-]*)\)")
    apply = kinds_in(definition(CONFIG, "fn-cfg-apply-delta"), r"\(equal kind (:[a-z][a-z0-9-]*)\)")
    writers: set[str] = set()
    for path in sorted(ROOT.glob("books/*.lisp")) + sorted(ROOT.glob("host/**/*.lisp")):
        text = path.read_text(encoding="utf-8", errors="replace")
        writers |= set(re.findall(r"\(fn-cfg-delta-make\s+(:[a-z][a-z0-9-]*)", text))
    return {"declared": declared, "encoder": kind_code, "decoder": code_kind,
            "dispatcher": apply, "writers": writers}


def cond_predicates(form: str) -> set[str]:
    """The predicates a `cond' dispatch tests: `((fn-x-p event) ...)'."""
    return set(re.findall(r"\(\((fn-[a-z0-9-]+(?:-p|p))\s", form))


def store_event_tables() -> dict[str, set[str]]:
    encoder = cond_predicates(definition(STORE_EVENTS, "fn-store-event-encode"))
    decoder = cond_predicates(definition(STORE_EVENTS, "fn-store-event-decode"))
    kind = cond_predicates(definition(STORE_EVENTS, "fn-store-event-kind"))
    replay = definition(REPLAY, "fn-replay-apply-record")
    rii = definition(RII, "fn-rii-apply-record")
    dispatch = set()
    for form in (replay, rii):
        for name in re.findall(r"\((fn-[a-z0-9-]+(?:-p|p|-held))\s", form):
            dispatch.add(ROW_ALIASES.get(name, name))
    # The decoder answers a decoded WIRE event; the decode arms name the
    # decoders, so read the predicates the decoder's cond tests as well.
    decoder |= {p for p in cond_predicates(definition(STORE_EVENTS, "fn-store-event-decode"))}
    as_row = lambda s: {WIRE_TO_ROW.get(p, p) for p in s}  # noqa: E731
    return {"encoder": as_row(encoder), "decoder": as_row(decoder) or as_row(encoder),
            "kind": as_row(kind), "dispatcher": dispatch & (as_row(encoder) | as_row(kind) | dispatch)}


def defevent_families() -> list[str]:
    if not EVENTS_JSON.exists():
        return []
    data = json.loads(EVENTS_JSON.read_text())
    families = data.get("families", data)
    return sorted(families) if isinstance(families, dict) else []


def findings(config: dict, store: dict) -> tuple[list[str], list[str]]:
    failures, notes = [], []
    for side in ("encoder", "decoder", "dispatcher", "declared"):
        missing = sorted(config["writers"] - config[side])
        if missing:
            failures.append(f"config delta kinds written but not in fn-cfg {side}: {', '.join(missing)}")
        dead = sorted(config[side] - config["writers"])
        if dead:
            notes.append(f"config {side} arms no writer reaches: {', '.join(dead)}")
    store_dispatch = store["dispatcher"]
    for side_name, side in (("decoder", store["decoder"]), ("kind", store["kind"]),
                            ("dispatcher", store_dispatch)):
        missing = sorted(store["encoder"] - side)
        if missing:
            failures.append(f"store event kinds encoded but without a {side_name} arm: {', '.join(missing)}")
    dead = sorted(store_dispatch - store["encoder"])
    if dead:
        notes.append(f"store event dispatcher arms no encoder produces: {', '.join(dead)}")
    return failures, notes


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--summary", action="store_true")
    parser.add_argument("--strict", action="store_true")
    arguments = parser.parse_args(argv)
    config, store = config_tables(), store_event_tables()
    failures, notes = findings(config, store)
    families = defevent_families()
    line = (f"alphabet_check: config deltas {len(config['writers'])} written / "
            f"{len(config['dispatcher'])} dispatched; store events {len(store['encoder'])} encoded / "
            f"{len(store['dispatcher'])} dispatched; {len(families)} defevent families generated; "
            f"{len(failures)} missing, {len(notes)} dead")
    if not arguments.summary:
        print("config deltas:")
        for side in ("declared", "writers", "encoder", "decoder", "dispatcher"):
            print(f"  {side:10s} {len(config[side]):3d}: {' '.join(sorted(config[side]))}")
        print("store events (row predicates):")
        for side in ("encoder", "decoder", "kind", "dispatcher"):
            print(f"  {side:10s} {len(store[side]):3d}: {' '.join(sorted(store[side]))}")
        print("defevent families (encoder = decoder by construction): " + ", ".join(families))
        for note in notes:
            print("note: " + note)
    for failure in failures:
        print("alphabet_check: " + failure)
    print(line)
    return 1 if (arguments.strict and failures) else 0


if __name__ == "__main__":
    sys.exit(main())
