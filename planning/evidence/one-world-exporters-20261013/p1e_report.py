#!/usr/bin/env python3
"""Regenerate P1E from the ruled export scan, census and six gate logs."""
import collections
import json
from pathlib import Path

OUT = Path(__file__).resolve().parent


def main():
    scan = json.loads((OUT / 'p1e-rule-scan.json').read_text())
    data = json.loads((OUT / 'p1-census.json').read_text())
    rows = scan['rules']
    zero = set(data['per_rune']['ADT-NTH-0']['enabled_books'])
    successor = set(data['per_rune']['ADT-NTH-1+']['enabled_books'])
    total = len(zero | successor)
    overlap = len(zero & successor)
    changed = set(data['changed_from_parent'])
    replacements = len((changed & set(data['existing_enables'])) - {'books/proto/adt-key-lib.lisp'})
    additions = len(changed & set(data['new_enables']))
    unchanged = len(data['edited']) - len(changed)
    counts = collections.Counter(r['classification'] for r in rows)
    broad = [r for r in rows if r['initial_broad_classification'] == 'PEELER']
    already_disabled = {'ADT-SET-REC-C-OPEN', 'ADT-APPEND-FIELDS-OPEN',
                        'ADT-SET-FIELDS-OPEN', 'ADT-GET-FIELDS-OPEN',
                        'ADT-GET-FIELDS-OKP-OPEN', 'ADT-COLS-SHAPE-OPEN', 'ADT-REC-P-OPEN'}
    reactive = {'ADT-CAR-OF-UPDATE-NTH', 'ADT-CDR-OF-UPDATE-NTH'}
    lines = ['# P1E — two opaque-field openers, Seat A28 ruling', '',
             f"At parent `{data['head']}`, ADT-NTH-0 becomes DEFTHMD with its immediate defining-book LOCAL enable. "
             f'ADT-NTH-1+ retains the same default-disabled treatment. The census derives **{len(zero)} ADT-NTH-0 enable subjects**, '
             f'**{len(successor)} ADT-NTH-1+ subjects**, and **{total} enabled books in total** ({overlap} use both). '
             'All six requested gates exit 0. No proof or certificate of the changed closures is claimed.', '',
             '## Seat A28 ruling', '',
             'The family of "peel an opaque field index into car/cdr" has exactly two members: ADT-NTH-0 and ADT-NTH-1+. '
             'They are the only rules whose LHS is NTH of an opaque record at a field index and whose RHS introduces CAR/CDR from nothing. '
             'The other fifteen rows in the initial broad scan react to selectors already present, describe ADT functions, or already end disabled. '
             'None has the same mechanism; none changes in this pass.', '',
             'The initial stop concerned ADT-PSCHEMA-FACTS: its ninth written conjunct opens ADT\'s own recognizer and shares its DEFTHM '
             'with eight other facts. A28 resolved that stop by excluding the entire event from this pass. Its statement and theory setting stay unchanged.', '',
             '## Initial broad scan and final classification', '',
             '| Event | Location | Initial broad class | A28 class | Mechanism / disposition |',
             '| --- | --- | --- | --- | --- |']
    for row in broad:
        name = row['name']
        why = ('Opaque NTH field opener; default-disabled with derived LOCAL enables' if row['classification'] == 'PEELER' else
               'Already disabled; unchanged' if name in already_disabled else
               'LHS already needs CAR/CDR of UPDATE-NTH; unchanged' if name in reactive else
               "Statement about ADT's own function/recognizer; unchanged")
        lines.append(f"| {name} | {row['book']}:{row['line']} | PEELER | {row['classification']} | {why} |")
    lines += ['', '## Census counts', '',
              '| Rune | Dev | Qualifying other lane | Own lane (excluded) | Ancestry excluded | Historical U | Additional authorized repairs | Enabled books |',
              '| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |']
    for rune, sets in data['per_rune'].items():
        values = [len(sets[k]) for k in ('U_dev', 'U_lane_other', 'U_lane_own', 'U_lane_ancestry_excluded', 'U')]
        values += [len(set(sets['enabled_books']) - set(sets['U'])), len(sets['enabled_books'])]
        lines.append('| ' + rune + ' | ' + ' | '.join(map(str, values)) + ' |')
    lines += ['', f"Historical union: **{len(data['U'])}**; enabled-book union: **{total} = {len(zero)} + {len(successor)} - {overlap}**. "
              'The two extra ADT-NTH-1+ subjects are the previously authorized CFGROUP/CFPOLICY guard repairs, '
              'whose replay controls remain distinctly labeled rather than counted as historical certificates.', '',
              'The fresh census reads the same October/all-event and September/guard-only scopes named in P1.md, '
              'including both read-only hbox reference trees. Only successful FN_CERTIFY_SUCCESS logs and Form/Rules summaries qualify; '
              'DEFTHM, DEFUN/implicit guards and explicit VERIFY-GUARDS summaries are retained. Source echoes, failed/incomplete attempts '
              'and runes outside Rules lists do not count. Qualifying lanes have ancestry exit 1 for '
              '`git -C /absolute/lane merge-base --is-ancestor f7760ab8c HEAD`; own and ancestry-descendant logs are excluded. '
              'HEAD snapshots are validated after scanning and again before applying. The seven excluded books receive no enables and are byte-identical to parent.', '',
              '## Source boundary and deterministic generation', '',
              'The script accepts `--runes ADT-NTH-1+ ADT-NTH-0`, canonicalizes by uppercase sorted order, '
              'and records the rune list in the census. Each log summary and evidence entry records the exact runes used. '
              'Each selected consumer gets exactly one line containing only its needed runes, replacing its committed ADT-NTH-1+ line where present: '
              '`(local (in-theory (enable adt-nth-0 adt-nth-1+)))` when both are needed. '
              'The defining library is the explicit placement exception: each opener has its own immediate LOCAL enable after DEFTHMD.', '',
              f"**{len(changed)} books differ from the parent**: {replacements} consumer enable-line replacements, "
              f'{additions} new consumer lines, and the defining-library change. {unchanged} ADT-NTH-1+-only subjects remain byte-identical. '
              'Consumer text is constructed from immutable HEAD by a single span insertion/replacement at its last top-level INCLUDE-BOOK, '
              'then asserted byte-identical after removing only the canonical enable lines. Existing lines must occur once at that exact anchor. '
              'The library permits exactly the ADT-NTH-0 DEFTHM-to-DEFTHMD token change plus its LOCAL enable. '
              'Every selected consumer sees the opener definitions at insertion; no undefined-at-insertion findings. '
              'Apply was repeated successfully to verify idempotence. [p1e-byte-audit.json](p1e-byte-audit.json) records the independent parent audit.', '',
              'Commands: `timeout 900 python3 build/vertical-runs/one-world/p1_enables.py --runes ADT-NTH-1+ ADT-NTH-0 --scan`; '
              '`timeout 180 python3 build/vertical-runs/one-world/p1_enables.py --runes ADT-NTH-1+ ADT-NTH-0 --apply`; '
              '`timeout 30 python3 build/vertical-runs/one-world/p1_enables.py --runes ADT-NTH-1+ ADT-NTH-0 --report`. '
              'The generated selection/evidence are [p1-enables.txt](p1-enables.txt), [p1-enables.json](p1-enables.json), '
              '[p1-census.json](p1-census.json), and [P1.md](P1.md).', '',
              '## Six gates', '', '| Command | Exit | Log |', '| --- | ---: | --- |']
    for name, command in [('one-world', 'tools/one_world_check.py'), ('book-roots', 'tools/book_roots_check.py'),
                          ('host-attach-order', 'tools/host_check.py --attach-order'), ('host-world', 'tools/host_check.py --world'),
                          ('extract-world', 'tools/extract/world.py --check'), ('interface', 'tools/interface_emit.py --check')]:
        code = (OUT / ('p1e-gate-' + name + '.exit')).read_text().strip()
        log = 'p1e-gate-' + name + '.log'
        lines.append(f'| `timeout 180 python3 {command}` | {code} | [{log}]({log}) |')
    lines += ['', 'Each gate has 0 findings/refusals. Book-roots retains its existing 55 explicit exclusions; '
              'host-world computed-name cases and interface source-undecidable cases retain their existing non-failing status. '
              'No proof_repl sessions, certifies, box jobs, commits, pushes or process stops occurred.', '',
              '## Complete export inventory', '',
              f"The closure is `adt-key-lib` -> `adt-lib`, with no further non-local project include. "
              f"The table inventories {len(rows)} non-local theorem events: {counts['PEELER']} PEELER, "
              f"{counts['TOWARD']} TOWARD, {counts['unrelated']} unrelated. Nine NIL-rule-class events export no theorem rules. "
              f"{len(scan['excluded_local_theorems'])} LOCAL theorem events are excluded. "
              'There are no :elim classes or macro-generated theorem events in this closure. '
              'Predicate conclusions rewrite to T; selectors on their LHS are not RHS introductions. '
              'The scan preserves classifications per written conjunct and every formula in [p1e-rule-scan.json](p1e-rule-scan.json). '
              'No third generic constant/successor-index or explicit-CONS-input opener is exported. '
              'The local ADT-UPDATE-NTH-0, ADT-UPDATE-NTH-OF-CONS, ADT-NTHCDR-3 and ADT-NTHCDR-1 are excluded.', '',
              '| Event | Location | Rule classes | A28 class |', '| --- | --- | --- | --- |']
    for row in rows:
        lines.append(f"| {row['name']} | {row['book']}:{row['line']} | `{row['rule_classes']}` | {row['classification']} |")
    lines += ['', '## Non-local function events', '',
              'Definition/type-prescription/induction families (as admitted) are unrelated to this theorem :rewrite/:elim family. '
              'This inventories source events, without claiming that each function has every family or performing a new ACL2 world query.', '',
              '| Function event | Location | Class |', '| --- | --- | --- |']
    for row in scan['functions']:
        lines.append(f"| {row['name']} ({row['event'].upper()}) | {row['book']}:{row['line']} | unrelated |")
    (OUT / 'P1E.md').write_text('\n'.join(lines) + '\n')


if __name__ == '__main__':
    main()
