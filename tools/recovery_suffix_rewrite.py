"""Move the actual recovery scan/replay origin to its captured base; no evaluation."""
import lisp_rewrite as lr

RULES = (
 ('(< 0 row-rc-chain)', '(< row-rc-base row-rc-chain)', 2),
 ('(fn2-recovery-commit-extent 1)', '(fn2-recovery-commit-extent (+ 1 row-rc-base))', 2),
 ('(rc-commit 1)', '(rc-commit (+ 1 row-rc-base))', 2),
 ('(rc-chain 0)', '(rc-chain row-rc-base)', 1),
)

def rewrite(source, rules=RULES):
 tree=lr.parse(source)
 scopes=lr.match('(defmachine-arms fn2-recovery-machine ?*rest)',tree.forms,deep=False)
 if len(scopes)!=1:raise ValueError('expected one actual recovery arm declaration')
 scope=scopes[0]; edits=[]
 for pattern,replacement,count in rules:
  matches=[m for m in lr.match(pattern,tree.forms) if scope.start<=m.start and m.end<=scope.end]
  if len(matches)!=count:raise ValueError(f'{pattern}: expected {count}, got {len(matches)}')
  edits.extend((m.start,m.end,replacement) for m in matches)
 return lr.write(source,edits)
