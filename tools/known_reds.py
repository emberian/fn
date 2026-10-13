#!/usr/bin/env python3.12
"""Write known-red admissions, owner transfers and closed-item retirements.

Validate with train's parsers; retirement leaves append-only amendments intact.
"""
from __future__ import annotations

import argparse
import fcntl
import json
from pathlib import Path
import re
import sys
from types import SimpleNamespace

if __package__:
    from . import train
else:
    import train

ROOT = Path(__file__).resolve().parents[1]
ORIGINAL_ROW = ('original baseline row: no admission record to transfer from; '
                'an owner change for it is a train commit under a coordinator ruling')
NATIVE_ID = re.compile(r'tests\.test_native_[A-Za-z0-9_]+\.[A-Za-z_][A-Za-z0-9_]*\.[A-Za-z_][A-Za-z0-9_]*')
DECODER = json.JSONDecoder()


def commit_sha(root: Path, sha: str) -> str:
    if not re.fullmatch(r'[0-9a-fA-F]{4,40}', sha):
        raise train.TrainError(f'not a commit SHA: {sha}')
    result = train.git(root, 'rev-parse', '--verify', sha, check=False)
    resolved = result.stdout.strip()
    if result.returncode or train.git(root, 'cat-file', '-t', resolved, check=False).stdout.strip() != 'commit':
        raise train.TrainError(f'not a commit in this repo: {sha}')
    return resolved


def whitespace(text: str, offset: int) -> int:
    while offset < len(text) and text[offset].isspace():
        offset += 1
    return offset


def members(text: str, start: int = 0):
    """JSON object member value spans, so unrelated bytes need never be rendered."""
    offset = whitespace(text, start) + 1
    while True:
        offset = whitespace(text, offset)
        if text[offset] == '}':
            return
        key, offset = DECODER.raw_decode(text, offset)
        offset = whitespace(text, offset)
        if text[offset] != ':':
            raise train.TrainError('invalid JSON member')
        start_value = whitespace(text, offset + 1)
        value, end = DECODER.raw_decode(text, start_value)
        yield key, value, start_value, end
        offset = whitespace(text, end)
        if text[offset] == ',':
            offset += 1


def array_entries(text: str, key: str):
    matches = [(start, end) for name, _, start, end in members(text) if name == key]
    if len(matches) != 1:
        raise train.TrainError(f'expected exactly one {key} array')
    start, end = matches[0]
    if text[start] != '[':
        raise train.TrainError(f'{key} is not an array')
    offset = whitespace(text, start + 1)
    entries = []
    while text[offset] != ']':
        value, after = DECODER.raw_decode(text, offset)
        entries.append((value, offset, after))
        offset = whitespace(text, after)
        if text[offset] == ',':
            offset = whitespace(text, offset + 1)
    return start, end, entries


def append_entry(text: str, key: str, entry: dict) -> str:
    start, end, entries = array_entries(text, key)
    rendered = '\n'.join('  ' + line for line in json.dumps(
        entry, indent=1, ensure_ascii=False).splitlines())
    if entries:
        # Insert after the old last value, preserving all old bytes on both sides.
        offset = entries[-1][2]
        return text[:offset] + ',\n' + rendered + text[offset:]
    return text[:start + 1] + '\n' + rendered + '\n ' + text[end - 1:]


def retire_rows(text: str, item: str) -> str:
    """Delete matching value spans and separators, preserving surviving bytes."""
    start, end, entries = array_entries(text, 'rows')
    if all(value['item'] == item for value, _, _ in entries):
        return text[:start + 1] + text[end - 1:]
    spans = []
    index = 0
    while index < len(entries):
        if entries[index][0]['item'] != item:
            index += 1
            continue
        first = index
        while index < len(entries) and entries[index][0]['item'] == item:
            index += 1
        if index < len(entries):
            # Keep the indentation before this run for the next surviving row.
            spans.append((entries[first][1], entries[index][1]))
        else:
            # A trailing run takes the comma after the previous surviving row.
            spans.append((entries[first - 1][2], entries[-1][2]))
    for start, end in reversed(spans):
        text = text[:start] + text[end:]
    return text


def item_state(root: Path, item: str):
    if not item or Path(item).name != item or item in ('.', '..'):
        raise train.TrainError(f'invalid repair item: {item}')
    path = root / 'planning/repair/items' / (item + '.json')
    try:
        data = json.loads(path.read_text(encoding='utf-8'))
        if not isinstance(data, dict) or not isinstance(data.get('state'), str):
            raise ValueError('missing state')
        return data['state']
    except (OSError, ValueError) as error:
        raise train.TrainError(f'no valid repair item {path}: {error}') from error


def validate(root: Path, rows_text: str, amendments_text: str) -> tuple[list, list]:
    """Train's schema parsers and baseline ownership/append-only checks, on disk text."""
    rows = train.parse_known_reds(rows_text)
    records = train.parse_amendments(amendments_text)
    row_by_key = {(r['kind'], r['subject']): r for r in rows}
    latest = {(r['kind'], r['subject']): r for r in records}
    for row in rows:
        if item_state(root, row['item']) in train.CLOSED_ITEM_STATES:
            raise train.TrainError(f"repair item is closed: {row['item']}")
    for key, record in latest.items():
        row = row_by_key.get(key)
        if row is None:
            if item_state(root, record['item']) not in train.CLOSED_ITEM_STATES:
                raise train.TrainError(f'amendment names no row: {key}')
        elif (row['item'], row['owner']) != (record['item'], record['owner']):
            raise train.TrainError(f'amendment disagrees with row: {key}')
    context = SimpleNamespace(root=root)
    before = train.amendments_at(context, train.train_base())
    if records[:len(before)] != before:
        raise train.TrainError('amendments are append-only: a dev record was edited or dropped')
    dev_rows = train.known_reds_at(context, train.train_base())
    if dev_rows is not None:
        dev_keys = {(r['kind'], r['subject']) for r in dev_rows}
        for key in row_by_key.keys() - dev_keys - latest.keys():
            raise train.TrainError(f'known red added without amendment: {key}')
    return rows, records


def operate(root: Path, args) -> int:
    rows_path, amendments_path = root / train.KNOWN_REDS, root / train.KNOWN_RED_AMENDMENTS
    # Lock the existing row file without writing a lock file, including on refusal.
    with rows_path.open('r', encoding='utf-8', newline='') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        rows_text = lock.read()
        amendments_text = amendments_path.read_text(encoding='utf-8')
        if args.command == 'retire':
            if item_state(root, args.item) not in train.CLOSED_ITEM_STATES:
                raise train.TrainError(f'close the item first: {args.item}')
            rows = train.parse_known_reds(rows_text)
            removed = [row for row in rows if row['item'] == args.item]
            if not removed:
                raise train.TrainError(f'no rows for repair item: {args.item}')
            new_rows = retire_rows(rows_text, args.item)
            validate(root, new_rows, amendments_text)
            rows_path.write_bytes(new_rows.encode('utf-8'))
            for row in removed:
                print(f'retire: {row["kind"]} {row["subject"]}')
            return 0
        rows, records = validate(root, rows_text, amendments_text)
        if args.command == 'check':
            print(f'known reds: {len(rows)} rows, {len(records)} amendment records; valid')
            return 0
        if args.command == 'add':
            if args.kind == 'native' and not NATIVE_ID.fullmatch(args.subject):
                raise train.TrainError('native subject must be tests.test_native_*.Class.method')
            if any((r['kind'], r['subject']) == (args.kind, args.subject) for r in rows):
                raise train.TrainError(f'row already exists: {args.kind} {args.subject}')
            if item_state(root, args.item) in train.CLOSED_ITEM_STATES:
                raise train.TrainError(f'repair item is closed: {args.item}')
            commit_sha(root, args.dev_sha)
            row = {k: getattr(args, k) for k in train.KNOWN_RED_FIELDS}
            record = {k: getattr(args, k) for k in train.AMENDMENT_FIELDS}
            new_rows = append_entry(rows_text, 'rows', row)
        else:
            matches = [r for r in rows if r['subject'] == args.subject]
            if len(matches) != 1:
                raise train.TrainError('transfer subject must name exactly one row')
            row = matches[0]
            previous = [r for r in records if (r['kind'], r['subject']) == (row['kind'], row['subject'])]
            if not previous:
                raise train.TrainError(ORIGINAL_ROW)
            record = dict(previous[-1], owner=args.owner, ruling=args.ruling, transfer_from=row['owner'])
            _, _, entries = array_entries(rows_text, 'rows')
            row_start = next(start for value, start, _ in entries if value == row)
            owner_span = [(start, end) for key, _, start, end in members(rows_text, row_start) if key == 'owner']
            if len(owner_span) != 1:
                raise train.TrainError('expected exactly one row owner')
            start, end = owner_span[0]
            new_rows = rows_text[:start] + json.dumps(args.owner, ensure_ascii=False) + rows_text[end:]
        new_amendments = append_entry(amendments_text, 'amendments', record)
        validate(root, new_rows, new_amendments)
        # All refusals occur before either write. One write per destination.
        rows_path.write_bytes(new_rows.encode('utf-8'))
        amendments_path.write_bytes(new_amendments.encode('utf-8'))
        print(f'{args.command}: {row["kind"]} {row["subject"]}')
        return 0


def main(argv=None, *, root: Path = ROOT) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    add = commands.add_parser('add')
    add.add_argument('--kind', choices=('native', 'check'), required=True)
    for field in ('subject', 'item', 'owner', 'dev-sha', 'evidence', 'ruling'):
        add.add_argument('--' + field, required=True)
    transfer = commands.add_parser('transfer')
    for field in ('subject', 'owner', 'ruling'):
        transfer.add_argument('--' + field, required=True)
    retire = commands.add_parser('retire')
    retire.add_argument('--item', required=True)
    commands.add_parser('check')
    args = parser.parse_args(argv)
    try:
        return operate(root, args)
    except (train.TrainError, OSError, ValueError) as error:
        print(f'known_reds: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
