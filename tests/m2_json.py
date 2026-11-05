"""M2CUT lines (tests/m2-cuts.lsp) -> OUT/m2.json for H's nightly line (tests/surface/nightly_nntp.py m2).

    tools/acl2 --timeout 1800 < tests/m2-cuts.lsp | python3 tests/m2_json.py OUT

Every cut c0..c11 must have a line; a missing one is a FAIL named as missing, never dropped."""
import json
import re
import subprocess
import sys
from pathlib import Path

CUTS = [f'c{i}' for i in range(12)]


def main(out):
    cuts = {}
    total = None
    for line in sys.stdin:
        m = re.match(r'M2CUT (c\d+) (PASS|FAIL) ?(.*)$', line.rstrip('\n'))
        if m:
            cuts[m.group(1)] = {'verdict': m.group(2), 'reasons': [r for r in m.group(3).split(' | ') if r]}
        m = re.match(r'M2 (\d+)/(\d+)$', line.strip())
        if m:
            total = (int(m.group(1)), int(m.group(2)))
    for c in CUTS:
        cuts.setdefault(c, {'verdict': 'FAIL', 'reasons': ['no M2CUT line: the driver did not report this cut']})
    passed = sum(1 for c in CUTS if cuts[c]['verdict'] == 'PASS')
    sha = subprocess.run(['git', 'rev-parse', '--short', 'HEAD'], capture_output=True, text=True).stdout.strip()
    data = {'passed': passed, 'total': len(CUTS), 'source': f'tests/m2-cuts.lsp @ {sha or "unknown"}',
            'driver_total': total, 'cuts': {c: cuts[c] for c in CUTS}}
    path = Path(out) / 'm2.json'
    path.write_text(json.dumps(data, indent=2) + '\n')
    print(f"M2 cuts {passed}/{len(CUTS)} -> {path}")
    if total is None:
        sys.exit('no M2 total line: the driver did not finish')


if __name__ == '__main__':
    main(sys.argv[1])
