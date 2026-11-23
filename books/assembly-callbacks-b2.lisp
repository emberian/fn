; The commit kind's first section, second half: root edges, refusal, collect
; and seal (split from assembly-callbacks-b under the one-minute rule).
(in-package "ACL2")
(include-book "assembly-callbacks-bt")
(local (in-theory (disable fn2-alloc-frozenp fn2-alloc-snapshot-activep)))
(fn2-commit-events-1b)
