"""INTERIM lines (tests/conn-interim-export.lsp) -> tests/surface/fn2_conn_interim.json.

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
out = {'source': 'books/conn-answer.lisp *fn2-answer-interim*',
       'served_verbs': ['CAPABILITIES', 'HELP', 'QUIT', 'MODE', 'DATE', 'POST', 'AUTHINFO', 'XREDEEM',
                        'GROUP', 'LISTGROUP', 'NEXT', 'LAST', 'STAT', 'ARTICLE', 'HEAD', 'BODY', 'OVER', 'XOVER',
                        'HDR', 'XHDR', 'LIST', 'NEWGROUPS', 'NEWNEWS', 'CHECK', 'IHAVE', 'TAKETHIS'],
       'interim': dict(sorted(rows.items())),
       'notes': {'LIST': 'every variant, with or without a wildmat, is the query cursor\'s where the profile serves reading (D6 2/n, 0f568f89b); DISTRIBUTIONS and DISTRIB.PATS answer 503 data item not stored',
                 'CHECK': 'served on a peer connection (the AcceptResult\'s peer family sets the peer bit, D5 3/n 21b661477); on a reader connection the 502 state refusal answers first',
                 'IHAVE': 'as CHECK; 436 where posting is off',
                 'TAKETHIS': 'as CHECK; its block is drained and answered 439 where no upload row serves it'}}
with open('tests/surface/fn2_conn_interim.json', 'w') as f:
    json.dump(out, f, indent=2)
    f.write('\n')
print(f'{len(rows)} interim commands')
