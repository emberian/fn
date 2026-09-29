; fn: witnesses and teeth for books/owner-reclaim-conns.lisp (Q16 (a), lane
; online-reclaim-4): the connections the installing pass re-pins have their
; history over the rebuilt Store.
(in-package "ACL2")
(include-book "../../books/owner-reclaim-conns")
(include-book "must-fail-checked")

; The rebuild (owner-checkpoint-open-tests' image: two retention events, two
; configuration records) and a live owner with one open connection on it.
(defconst *orcn-t-events*
  (list (fn-store-retention-event-make :undertake 0 0 0 "forward-orcp" "subject" "evidence" 10)
        (fn-store-retention-event-make :release 1 1 1 "forward-orcp" "subject" "evidence" 0)))
(defconst *orcn-t-configs*
  (list *fn-cfg-default-record*
        (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1)) *fn-cfg-default-stamp*)))
(defconst *orcn-t-rebuilt-oc* (cadr (fn-orcp-rebuild *orcn-t-events* *orcn-t-configs* 8 4)))
(defconst *orcn-t-live* (cdr (fn-ocfg-open *orcn-t-rebuilt-oc* nil)))
(defconst *orcn-t-next* (fn-orcp-swapped-ocfg *orcn-t-live* *orcn-t-rebuilt-oc*))

; -----------------------------------------------------------------------------
; KEYSTONE fn-orcn-swap-over-the-rebuild-keeps-conn-histories, positive
; witness (reachable: the live owner is an open on the full open's owner).
; Antecedent: the decision is :swap.  Conclusion: every connection of the
; swapped owner (one) has its history.
(assert-event (fn-ocl-relation *orcn-t-live*))
(assert-event (equal (fn-orcp-swap-decision :swap *orcn-t-live* *orcn-t-rebuilt-oc*) :swap))
(assert-event (equal (len (fn-own-conns (fn-ocfg-owner *orcn-t-next*))) 1))
(assert-event (fn-ocl-conns-historyp *orcn-t-next* (fn-own-conns (fn-ocfg-owner *orcn-t-next*))))
; The pin the swap installs is the rebuilt configuration.
(assert-event (equal (fn-ocfg-conn-config
                      *orcn-t-next*
                      (fn-own-conn-id (car (fn-own-conns (fn-ocfg-owner *orcn-t-next*)))))
                     (fn-ocfg-config *orcn-t-rebuilt-oc*)))
; Other words pass through the decision unchanged.
(assert-event (equal (fn-orcp-swap-decision :delta *orcn-t-live* *orcn-t-rebuilt-oc*) :delta))
(assert-event (equal (fn-orcp-swap-decision :readers *orcn-t-live* *orcn-t-rebuilt-oc*) :readers))

; Hypothesis removal (the only hypothesis, decision = :swap), CORRUPTED
; STATE: the live connection's session is not a session.  The rebuild still
; installed (not :fault); the decision is :unbound, not :swap; and the
; swapped owner's connection has no history.
(defconst *orcn-t-bad-live*
  (let* ((oc *orcn-t-live*) (o (fn-ocfg-owner oc)) (c (car (fn-own-conns o))))
    (fn-ocfg-make (fn-own-set-conns o (list (update-nth 4 nil c)))
                  (fn-ocfg-config oc) (fn-ocfg-pins oc) (fn-ocfg-staged oc))))
(defconst *orcn-t-bad-next* (fn-orcp-swapped-ocfg *orcn-t-bad-live* *orcn-t-rebuilt-oc*))
(assert-event (not (equal *orcn-t-rebuilt-oc* :fault)))
(assert-event (equal (fn-orcp-swap-decision :swap *orcn-t-bad-live* *orcn-t-rebuilt-oc*) :unbound))
(must-fail-checked
 (assert-event (equal (fn-orcp-swap-decision :swap *orcn-t-bad-live* *orcn-t-rebuilt-oc*) :swap)))
(assert-event (not (fn-ocl-conns-historyp *orcn-t-bad-next*
                                          (fn-own-conns (fn-ocfg-owner *orcn-t-bad-next*)))))

; The admissibility conjuncts, each refused alone.  A :fault rebuild is not
; admitted (a faulted open never swaps in).
(defconst *orcn-t-fault* (cadr (fn-orcp-rebuild *orcn-t-events* *orcn-t-configs* 8 -1)))
(assert-event (equal *orcn-t-fault* :fault))
(assert-event (equal (fn-orcp-swap-decision :swap *orcn-t-live* *orcn-t-fault*) :unbound))
; A live configuration other than the rebuilt one (CORRUPTED STATE: the live
; configuration record replaced) is not admitted.
(defconst *orcn-t-other-cfg-live*
  (fn-ocfg-make (fn-ocfg-owner *orcn-t-live*) nil (fn-ocfg-pins *orcn-t-live*)
                (fn-ocfg-staged *orcn-t-live*)))
(assert-event (equal (fn-orcp-swap-decision :swap *orcn-t-other-cfg-live* *orcn-t-rebuilt-oc*)
                     :unbound))
