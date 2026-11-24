; The shared Message-ID span in an NNTP overview line.
(in-package "ACL2")
(include-book "grammar")
(fn2-book-layer :d)

;; The Message-ID of an overview line at [from, to) of a slot: its fourth
;; TAB-separated field (subject, from, date, message-id, ...), as (mv code
;; start length).
(defun fn2-cursor-mid-span (slot gen from to okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (and (fn2-pool-wfp fn2-pool) (natp from) (natp to))))
  (b* ((left (nfix (- to from)))
       ((mv f1 t1) (fn2-gram-find left from 9 slot gen okind oslot ogen fn2-pool))
       ((mv f2 t2) (fn2-gram-find (nfix (- to (+ 1 t1))) (+ 1 t1) 9 slot gen okind oslot ogen fn2-pool))
       ((mv f3 t3) (fn2-gram-find (nfix (- to (+ 1 t2))) (+ 1 t2) 9 slot gen okind oslot ogen fn2-pool))
       ((mv f4 t4) (fn2-gram-find (nfix (- to (+ 1 t3))) (+ 1 t3) 9 slot gen okind oslot ogen fn2-pool)))
    (if (and f1 f2 f3 f4 (< (+ 1 t3) t4)) (mv :ok (+ 1 t3) (- t4 (+ 1 t3))) (mv :refused 0 0))))
(defthm fn2-cursor-mid-span-types
  (and (natp (mv-nth 1 (fn2-cursor-mid-span slot gen from to okind oslot ogen fn2-pool)))
       (natp (mv-nth 2 (fn2-cursor-mid-span slot gen from to okind oslot ogen fn2-pool)))))
(in-theory (disable fn2-cursor-mid-span))
