; State globals under guard verification.
;
; A host file keeps its adapter state in ACL2 state globals (f-put-global,
; f-get-global).  put-global's guard is the state's state-p1, so a function
; that chains puts owes state-p1 of every intermediate state.  state-p1
; constrains three keys of the global table (current-acl2-world, timer-alist,
; print-base) and the table's shape (ordered, the initial table bound); add-pair
; keeps both for any other key.  The obligation arrives with put-global and
; global-table opened and the inner table already simplified by nth-update-nth,
; so the rule is stated in that shape with the table as its own variable.
;
; Included by host files whose entries are :logic and guard-verified (row K2:
; host/reader-host.lisp first); nothing served computes with it.
(in-package "ACL2")

(defthm fn-sg-state-p1-of-put-global
  (implies (and (state-p1 st)
                (symbolp key)
                (not (equal key 'current-acl2-world))
                (not (equal key 'timer-alist))
                (not (equal key 'print-base))
                (equal gt (nth 2 st)))
           (state-p1 (update-nth 2 (add-pair key val gt) st)))
  :hints (("Goal" :in-theory (enable state-p1))))
