(in-package "ACL2")
(include-book "def-loop-fixture-dep")
(include-book "def-loop")

(def-loop fn-served-feed (conn octets fn-arena)
  :shape :thread :over octets :st conn :elt o
  :done (or (not (consp octets))
            (fn-served-closed-wirep (fn-served-conn-wire conn))
            (fn-served-haltedp conn))
  :let ((here (fn-served-feed-byte conn o fn-arena))) :row (fn-served-result-effects here)
  :next (fn-served-result-conn here)
  :make (fn-served-make-result conn dl-rows) :st-of (fn-served-result-conn dl-r)
  :rows-of (fn-served-result-effects dl-r) :rev fn-ag-rev-onto :measure (len octets)
  :guard (fn-wire-statep (fn-served-conn-wire conn)) :stobjs fn-arena
  :guard-hints (("Goal"
                 :in-theory
                 (disable fn-served-dispatch-events fn-wire-feed-byte fn-wire-statep))))

