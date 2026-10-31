"""INTERIM lines (tests/conn-interim-export.lsp) -> fn2/tests/surface/fn2_conn_interim.json.

The surface harness reports every interim reply as OWED with its quest, never a pass or a red;
the table empties as D4-D7 and E land (layer doc section 4.3)."""
import json, re, sys

rows = {}
for line in sys.stdin:
    m = re.search(r'INTERIM ([^|]+)\|(\d+)\|([^|]*)\|(\S+)', line)
    if m:
        rows[m.group(1)] = {'code': int(m.group(2)), 'reply': m.group(3), 'quest': m.group(4)}
if not rows:
    sys.exit('no INTERIM lines')
out = {'source': 'fn2/books/conn-answer.lisp *fn2-answer-interim*',
       'served_verbs': ['CAPABILITIES', 'HELP', 'QUIT', 'MODE', 'DATE', 'AUTHINFO', 'XREDEEM',
                        'GROUP', 'LISTGROUP', 'NEXT', 'LAST', 'STAT', 'OVER', 'XOVER'],
       'interim': dict(sorted(rows.items())),
       'notes': {'LIST': 'OVERVIEW.FMT, HEADERS and MOTD are served now; DISTRIBUTIONS and DISTRIB.PATS answer 503 data item not stored; the other variants are the interim reply',
                 'IHAVE': 'on a reader connection (every D3 connection) the 502 state refusal answers first',
                 'CHECK': 'on a reader connection the 502 state refusal answers first',
                 'TAKETHIS': 'on a reader connection the 502 state refusal; a peer TAKETHIS waits for D4 and E4'}}
with open('fn2/tests/surface/fn2_conn_interim.json', 'w') as f:
    json.dump(out, f, indent=2)
    f.write('\n')
print(f'{len(rows)} interim commands')
