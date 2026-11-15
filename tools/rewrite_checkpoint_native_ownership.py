"""Drain live construction admissions through the native-role discriminator."""
from pathlib import Path
import lisp_rewrite as lr
FILES = ('checkpoint-teardown', 'checkpoint-tickets', 'checkpoint-lifecycle',
         'checkpoint-page-state', 'checkpoint-map-build', 'checkpoint-metadata-manifest',
         'checkpoint-installation-coordinator', 'checkpoint-map-read', 'checkpoint-plan')
def rewrite(text):
    parsed = lr.parse(text)
    edits = []
    for op in ('equal', '='):
        for m in lr.match('('+op+' (fn2-checkpoint-construction-live ?row fn2-checkpoint-construction) 1)', parsed.forms):
            row = m.captures['row']
            edits.append((m.start, m.end, '(fn2-checkpoint-construction-native-p '+text[row.start:row.end]+' fn2-checkpoint-construction)'))
    return lr.write(text, edits), len(edits)
if __name__ == '__main__':
    import argparse
    p = argparse.ArgumentParser(); p.add_argument('--write', action='store_true'); args = p.parse_args()
    for stem in FILES:
        path = Path(__file__).resolve().parents[1] / 'books' / (stem+'.lisp')
        out, count = rewrite(path.read_text())
        print(stem, count)
        if args.write: path.write_text(out)
