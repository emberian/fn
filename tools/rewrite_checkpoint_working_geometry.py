from pathlib import Path
from tools.lisp_rewrite import parse, write, Lst, Atom, Str

def walk(n):
 yield n
 if isinstance(n,Lst):
  for x in n.items: yield from walk(x)
def rewrite(s, mapping):
 return write(s,[(n.start,n.end,mapping[n.text]) for f in parse(s).forms for n in walk(f) if isinstance(n,Atom) and not isinstance(n,Str) and n.text in mapping])
# Controls: code-only substitution; quoted negative token and owner generation stay.
s='; 19 27 26\n(x 19 27 26 8 "19")'
o=rewrite(s,{'19':'ROOT','27':'ALL','26':'(- ALL 1)'})
assert o=='; 19 27 26\n(x ROOT ALL (- ALL 1) 8 "19")'
assert rewrite('(owner 4 8 1 2 3)',{'19':'ROOT'})=='(owner 4 8 1 2 3)'
for name in ['tests/checkpoint-future-resources-unit.lisp','tests/checkpoint-working-release-unit.lisp']:
 p=Path(name);p.write_text(rewrite(p.read_text(),{'19':'*fn2-checkpoint-window-count*','27':'*fn2-checkpoint-working-window-count*','26':'(- *fn2-checkpoint-working-window-count* 1)'}))
p=Path('books/checkpoint-working-reserve.lisp');s=p.read_text();s=s.replace('(defconst *fn2-checkpoint-window-count* 19)', '''; Dedicated physical-source reader windows follow the original nineteen.
; They cannot alias semantic/payload windows across iterator yields.
(defconst *fn2-checkpoint-source-page-window* 19)
(defconst *fn2-checkpoint-source-read-window* (+ 1 *fn2-checkpoint-source-page-window*))
(defconst *fn2-checkpoint-window-count* (+ 1 *fn2-checkpoint-source-read-window*))
(defconst *fn2-checkpoint-working-window-count*
 (+ *fn2-checkpoint-window-count* *fn2-checkpoint-future-window-count*))''');s=s.replace('(equal i 16)) *fn2-run-page-size*)','(equal i 16) (equal i *fn2-checkpoint-source-page-window*)) *fn2-run-page-size*)');s=rewrite(s,{'27':'*fn2-checkpoint-working-window-count*'});p.write_text(s)
p=Path('tests/checkpoint-retry-unit.lisp');s=p.read_text().replace('(cons 29 (max','(cons (+ *fn2-checkpoint-working-window-count* 2) (max');p.write_text(s)
print('2 geometry rewrite controls passed; declarations and 3 fixtures updated')
