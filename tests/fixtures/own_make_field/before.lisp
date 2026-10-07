; fixture: four construction shapes, a comment that must not move, a name
; list that is not a construction, and an already converted call.
(in-package "ACL2")

(defun fn-own-configure (o config)
  (declare (xargs :guard t))
  (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o) (fn-own-next-id o)
               (fn-own-max-conns o) (fn-own-pending o) (fn-own-ledger-field o)
               (fn-own-clock o) (fn-own-facts o) config (fn-own-queue o)
               (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o)))

#|  a block comment mentioning (fn-own-make a b) is not a form |#
(defthm theorem-site
  (equal (fn-own-refused (fn-own-make store view conns next-id max-conns pending ledger clock facts config queue inflight feeds node-secret refused))
         refused))

(defun fresh (store)
  (fn-own-make store nil nil 0 4 nil nil nil nil nil nil nil nil nil nil))

(defun transit (o conn)
  (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o) (fn-own-next-id o)
               (fn-own-max-conns o) (fn-own-pending o) (fn-own-ledger-field o)
               (fn-own-clock o) (fn-own-facts o) (fn-own-config o) (fn-own-queue o)
               (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o)
               (fn-own-transit-refused o conn)))

(in-theory (disable (:d fn-own-make)))
(defconst *names* '(fn-own-make fn-own-replace-conn fn-own-remove-conn))
(defun already (o)
  (fn-own-make 1 2 3 4 5 6 7 8 9 10 11 12 13 14 (fn-own-refused o) (fn-own-proc o)))
