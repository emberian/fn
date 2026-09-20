; Deterministic ACL2 scenarios for the fn logical core.
;
; This is a host-side scenario catalog, not an implementation of acceptance:
; every transition below calls the certified functions from books/acceptance.

(in-package "ACL2")
; The certified acceptance core every scenario below calls.  tools/
; run_simulator.py also includes it; a repeated include-book is redundant.
(include-book "../books/acceptance")

(defconst *fn-sim-groups* '("fn.letters" "fn.test"))
(defconst *fn-sim-message-id* "<simulator@example.invalid>")
(defconst *fn-sim-payload* '(72 105 13 10))

(defun fn-sim-acceptance-initial ()
  (fn-initial-state *fn-sim-groups*))

(defun fn-sim-acceptance-prepared ()
  (fn-accept-prepare (fn-sim-acceptance-initial)
                     7
                     *fn-sim-message-id*
                     *fn-sim-payload*
                     *fn-sim-groups*))

(defun fn-sim-acceptance-durable ()
  (fn-accept-complete (fn-sim-acceptance-prepared) 0 7 :durable))

(defun fn-sim-acceptance-durable-okp ()
  (let ((initial (fn-sim-acceptance-initial))
        (prepared (fn-sim-acceptance-prepared))
        (durable (fn-sim-acceptance-durable)))
    (and (fn-statep initial)
         (fn-statep prepared)
         (fn-statep durable)
         (equal (fn-state-articles initial) nil)
         (equal (fn-state-articles prepared) nil)
         (equal (len (fn-state-articles durable)) 1)
         (equal (fn-state-next-txid durable) 1)
         (equal (fn-state-fenced durable) nil)
         (equal (fn-acceptedp *fn-sim-message-id*
                              (fn-state-articles durable))
                t))))
