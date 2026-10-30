"""H drivers for peering and bp (README "Provisioning and driver hooks": check eligible histories, record
observation gaps, assert findings).

One hook for both: `FN2_SURFACE_HISTORY_<FAMILY>=fn2.tests.surface.history_drivers:history`. The histories
are the E natives' own observation logs (OUT/<family>/natives/observe, or FN2_SURFACE_HISTORY_DIR_<FAMILY>),
adapted by fn2.tests.history.from_observe exactly as the nntp and consumer H forms adapt theirs:

  peering   convergence.check (V1 accepted twice, V2 accepted then absent, V3 changed, V4 divergence across
            nodes) and durable.check (D1-D3) over posts, IHAVE transfers and reads
  bp        durable.check over the bp natives' posts and reads. Bundle convergence (F8: custody released only
            by a receipt or a waiver, no bundle delivered twice) needs bundle operations, and the bp natives'
            logs carry none (decoded_custody exercises the NNTP side of custody; source_corpus_bp needs
            FN_DTN7_REPO): that half is owed to the F8 simulator scenario and named in every report.

Every log's counts and unmapped evidence are kept in the case's evidence; a log with anomalies fails the
form; no mapped operation in any log is a named skip.
"""
import json
import os
from pathlib import Path
import unittest

RELEVANT = {'peering': {'post', 'transfer', 'read'}, 'bp': {'post', 'read'}}
OWED = {'bp': 'bundle convergence (F8) needs bundle operations; the bp natives observe none'}


def history(*, case, target, family, out, checkers):
    from fn2.tests.history import convergence, durable, from_observe
    from fn2.tests.history.history import pair
    if family not in RELEVANT:
        raise ValueError(f'no history driver for {family}')
    directory = Path(os.environ.get('FN2_SURFACE_HISTORY_DIR_' + family.upper(), str(Path(out) / 'natives' / 'observe')))
    checks = [('durable', durable.check)] + ([('convergence', convergence.check)] if family == 'peering' else [])
    reports = []
    for path in sorted(directory.rglob('*.jsonl')):
        adapted = from_observe.adapt(json.loads(line) for line in path.read_text().splitlines())
        ops = [o for o in pair(adapted.history) if o.f in RELEVANT[family] and not o.value.get('observed_only')]
        anomalies = [f'{name}: {a}' for name, check in checks for a in check(adapted.history)]
        reports.append(dict(source=str(path), counts=adapted.counts, unmapped=len(adapted.unmapped),
                            operations=len(ops), by_function={f: sum(o.f == f for o in ops) for f in RELEVANT[family]},
                            anomalies=anomalies))
    case.evidence['history'] = reports
    if family in OWED:
        case.evidence['history_owed'] = OWED[family]
    (Path(out) / 'history.json').write_text(json.dumps(reports, indent=1, default=str))
    bad = [r for r in reports if r['anomalies']]
    case.assertFalse(bad, json.dumps(bad[:3], default=str))
    if not any(r['operations'] for r in reports):
        raise unittest.SkipTest(f'history driver: no mapped {family} operations in {directory}')
    return reports
