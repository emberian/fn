#!/usr/bin/env python3
"""Audit reached callback cost omissions; source findings are not work proofs.

DEFcost defaults omitted dimensions to zero. Preserve that distinction here,
report stateful boundaries reached by real :DO sites, and show explicit arm
charges separately. Charges are not presumed to cover a missing callback bound.
"""
from __future__ import annotations
import argparse
from dataclasses import asdict, dataclass
import json
from pathlib import Path
import ledger

DIMENSIONS = (':bytes', ':steps', ':descriptors')
BOUNDARIES = (':tables', ':own-writes', ':effects')


@dataclass
class Finding:
    operation: str
    declaration: str
    arm: str
    call_source: str
    missing: list[str]
    declared: dict[str, str]
    boundary: dict[str, str]
    arm_charges: list[str]
    status: str = 'unpriced-callback-bound'
    coverage: str = 'unverified; explicit charges are not an actual-work proof'


def walk(form):
    if isinstance(form, list) and ledger.head(form) not in ('quote', 'quasiquote'):
        yield form
        for child in form:
            yield from walk(child)


def nonempty(value):
    return value not in (None, [], ledger.Sym('nil'))


@dataclass
class Audit:
    findings: list[Finding]
    unknown_providers: list[dict]
    ambiguous_declarations: list[dict]


def audit_report(sources: dict[str, str]) -> Audit:
    declarations, arms = {}, []
    for source, text in sources.items():
        for form, _ in ledger.source_events(ledger.Reader(text).top_level()):
            if ledger.head(form) == 'defcost' and len(form) >= 2:
                declarations.setdefault(str(form[1]), []).append((source, ledger.keyword_plist(form[2:])))
            if ledger.head(form) == 'defmachine-arms':
                for group in (':arms', ':subarms'):
                    try:
                        rows = form[form.index(ledger.Sym(group)) + 1]
                    except (ValueError, IndexError):
                        continue
                    if isinstance(rows, list):
                        for row in rows:
                            if isinstance(row, list) and row:
                                arms.append((source, str(form[1]) + '/' + group + '/' + str(row[0]), row))
    findings, unknown, ambiguous = [], [], []
    for name, rows in sorted(declarations.items()):
        if any(row != rows[0][1] for _, row in rows[1:]):
            ambiguous.append({'operation': name,
                'declarations': [{'source': owner,
                                  'options': {k: ledger.source_text(v) for k, v in row.items()}}
                                 for owner, row in rows], 'reached_at': []})
    ambiguous_by_name = {row['operation']: row for row in ambiguous}
    for source, arm, body in arms:
        charges = [ledger.source_text(node) for node in walk(body)
                   if ledger.head(node) == ':charge']
        for node in walk(body):
            if ledger.head(node) != ':do' or len(node) < 3 or not isinstance(node[2], list) or not node[2]:
                continue
            operation = str(node[2][0])
            site = {'operation': operation, 'arm': arm, 'call_source': source,
                    'arm_charges': charges}
            if operation not in declarations:
                unknown.append({**site, 'reason': 'No DEFcost in supplied sources; may be an operation or declared elsewhere'})
                continue
            if operation in ambiguous_by_name:
                ambiguous_by_name[operation]['reached_at'].append(site)
                continue  # Never choose a declaration by source iteration order.
            owner, row = declarations[operation][0]
            boundary = {k: ledger.source_text(row[k]) for k in BOUNDARIES if nonempty(row.get(k))}
            if ':steps' in row or not boundary:
                continue  # Explicit zero and pure scalar helpers are distinct from omission.
            findings.append(Finding(operation, owner, arm, source,
                [k for k in DIMENSIONS if k not in row],
                {k: ledger.source_text(row[k]) for k in DIMENSIONS if k in row},
                boundary, charges))
    return Audit(findings, unknown, ambiguous)


def audit(sources: dict[str, str]) -> list[Finding]:
    """Compatibility view for focused finding checks; CLI always exposes partial scope."""
    return audit_report(sources).findings


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('sources', nargs='+', type=Path, help='Declaration and actual arm sources to join')
    p.add_argument('--require-explicit', action='store_true', help='Fail for reached unpriced stateful callbacks')
    args = p.parse_args()
    report = audit_report({str(path): path.read_text() for path in args.sources})
    print(json.dumps({'scope': 'supplied source ownership only; not physical-work qualification',
                      'complete_source_ownership': not (report.unknown_providers or report.ambiguous_declarations),
                      **asdict(report)}, indent=2))
    return int(args.require_explicit and bool(report.findings or report.unknown_providers
                                             or report.ambiguous_declarations))


if __name__ == '__main__':
    raise SystemExit(main())
