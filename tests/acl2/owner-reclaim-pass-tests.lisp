; fn: witnesses and teeth for books/owner-reclaim-pass.lisp (Q16 (a), lane
; online-reclaim-3): the installing pass's credit, swap word, cuts, rerun,
; rebuild and swapped owner.
(in-package "ACL2")
(include-book "../../books/owner-reclaim-pass")
(include-book "must-fail-checked")
(include-book "arena-lift")
; The owner fixture's store (*rpt-s*, its arena *rpt-payloads*, its history's
; octets rpt-events) and the expiring context over it (*xt-ctx*).
(include-book "expiry-tests")

; -----------------------------------------------------------------------------
; 1. The credit.  A ledger with 10^6 octets of budget, 1,000 held by a
; connection, 500 by the open batch.
(defconst *orcp-t-ops* (list (cons (fn-mca-conn-key 3) (cons 0 1000))
                             (cons :open (cons 0 500))))
(defconst *orcp-t-l* (fn-mcr-make 1000000 100000 0 0 0 0 *orcp-t-ops*))
(assert-event (fn-mcr-fundedp *orcp-t-l*))
(assert-event (equal (fn-orcp-estimate 1000) 64000))

; KEYSTONES fn-orcp-reserve-keeps-funded and fn-orcp-reserve-holds-the-
; estimate, positive witness: admitted, funded, the pass holds its estimate,
; the connection and the open batch hold what they held.
(defconst *orcp-t-r* (fn-orcp-reserved-credits *orcp-t-l* 1000))
(assert-event (equal (car (fn-orcp-reserve *orcp-t-l* 1000)) :ok))
(assert-event (fn-mcr-fundedp *orcp-t-r*))
(assert-event (equal (fn-mcr-credit-of :reclaim (fn-mcr-ops *orcp-t-r*)) 64000))
(assert-event (equal (fn-mcr-credit-of (fn-mca-conn-key 3) (fn-mcr-ops *orcp-t-r*)) 1000))
(assert-event (equal (fn-mcr-credit-of :open (fn-mcr-ops *orcp-t-r*)) 500))
; Mutation: a reservation that took the connection's credit is not this one.
(must-fail-checked
 (assert-event (equal (fn-mcr-credit-of (fn-mca-conn-key 3) (fn-mcr-ops *orcp-t-r*)) 0)))

; fn-orcp-reserve-refused-by-name: past the budget (a history whose copy
; needs 64 x 20,000 octets) it is refused by name and the ledger is kept.
(assert-event (equal (fn-orcp-reserve *orcp-t-l* 20000) '(:refused :memory-budget-exhausted)))
(assert-event (equal (fn-orcp-reserved-credits *orcp-t-l* 20000) *orcp-t-l*))
; The boundary: exactly the headroom is admitted, one octet more is not.
(defconst *orcp-t-room* (- 1000000 (fn-mcr-total *orcp-t-l*)))
(assert-event (equal (car (fn-mcr-resize *orcp-t-l* :reclaim *orcp-t-room*)) :ok))
(assert-event (equal (car (fn-mcr-resize *orcp-t-l* :reclaim (1+ *orcp-t-room*))) :refused))

; fn-orcp-release-frees-the-pass: nothing held after, funded.
(assert-event (equal (fn-mcr-credit-of :reclaim (fn-mcr-ops (fn-orcp-release *orcp-t-r*))) 0))
(assert-event (fn-mcr-fundedp (fn-orcp-release *orcp-t-r*)))
(assert-event (equal (fn-mcr-credit-of :open (fn-mcr-ops (fn-orcp-release *orcp-t-r*))) 500))

; -----------------------------------------------------------------------------
; 2. The swap word.  KEYSTONE fn-orcp-swap-only-over-the-capture: the
; positive witness asserts every conclusion; each hypothesis-removal
; witness fails one condition alone and is not a swap.
(assert-event (equal (fn-orcp-swap-word 7 9 *rpt-s* 7 9 *rpt-s* t 0) :swap))
(assert-event (equal (fn-orcp-swap-word 7 9 *rpt-s* 8 9 *rpt-s* t 0) :delta))
(assert-event (equal (fn-orcp-swap-word 7 9 *rpt-s* 7 10 *rpt-s* t 0) :delta))
(assert-event (equal (fn-orcp-swap-word 7 9 *rpt-s* 7 9 (fn-sn-with-topic *rpt-s* nil) t 0)
                     :delta))
(assert-event (equal (fn-orcp-swap-word 7 9 *rpt-s* 7 9 *rpt-s* nil 0) :busy))
(assert-event (equal (fn-orcp-swap-word 7 9 *rpt-s* 7 9 *rpt-s* t 1) :readers))
(must-fail-checked
 (assert-event (equal (fn-orcp-swap-word 7 9 *rpt-s* 8 9 *rpt-s* t 0) :swap)))

; fn-orcp-swapped-history-is-the-offline-rewrite on the fixture: at a swap
; the rewrite of the captured rows is the offline rewrite of the rows now.
(bpr-lift fn-orc-rows-octets 1)
(bpr-lift fn-orc-rewrite-rows 2)
(defconst *orcp-t-rows* (fn-sf-records (fn-sn-files *rpt-s*)))
(defmacro orcp-t-new () '(in-arena-fn-orc-rewrite-rows *rpt-payloads* *orcp-t-rows* *xt-ctx*))
(assert-event (equal (in-arena-fn-orc-rows-octets *rpt-payloads* (orcp-t-new))
                     (fn-rclp-events (in-arena-fn-orc-rows-octets *rpt-payloads* *orcp-t-rows*)
                                     *xt-ctx*)))
(assert-event (not (equal (in-arena-fn-orc-rows-octets *rpt-payloads* (orcp-t-new))
                          (in-arena-fn-orc-rows-octets *rpt-payloads* *orcp-t-rows*))))

; -----------------------------------------------------------------------------
; 3. The cuts, and the rerun.
(assert-event (equal (fn-orcp-cut-outcome :captured) :old))
(assert-event (equal (fn-orcp-cut-outcome :rebuilt) :old))
(assert-event (equal (fn-orcp-cut-outcome :installed) :new))
(assert-event (equal (fn-orcp-cut-outcome :released) :new))
(assert-event (equal (fn-orcp-cut-outcome :elsewhere) :unknown))
(must-fail-checked (assert-event (equal (fn-orcp-cut-outcome :staged) :new)))

; KEYSTONE fn-orcp-rerun-rewrites-nothing: three articles expire; a rerun
; over the rewritten rows has the same octets.
(assert-event (equal (len (fn-rclp-rewritten-msgids (rpt-events) *xt-ctx*)) 3))
(assert-event (equal (in-arena-fn-orc-rows-octets
                      *rpt-payloads*
                      (in-arena-fn-orc-rewrite-rows *rpt-payloads* (orcp-t-new) *xt-ctx*))
                     (in-arena-fn-orc-rows-octets *rpt-payloads* (orcp-t-new))))

; -----------------------------------------------------------------------------
; 4. The rebuild (owner-checkpoint-open-tests' image: two retention events,
; two configuration records).  KEYSTONE fn-orcp-rebuild-is-the-full-open on
; a reachable owner, not :fault.
(defconst *orcp-t-events*
  (list (fn-store-retention-event-make :undertake 0 0 0 "forward-orcp" "subject" "evidence" 10)
        (fn-store-retention-event-make :release 1 1 1 "forward-orcp" "subject" "evidence" 0)))
(defconst *orcp-t-configs*
  (list *fn-cfg-default-record*
        (fn-cfg-record-make 1 7 2 (list (fn-cfg-set-capacity 1)) *fn-cfg-default-stamp*)))
(defconst *orcp-t-rebuilt* (fn-orcp-rebuild *orcp-t-events* *orcp-t-configs* 8 4))
(assert-event (not (equal (cadr *orcp-t-rebuilt*) :fault)))
(assert-event (equal (cadr *orcp-t-rebuilt*)
                     (fn-ock-recover-full *orcp-t-configs* 8 *orcp-t-events* 4)))
(assert-event (equal (car *orcp-t-rebuilt*)
                     (fn-sco-capture *orcp-t-configs* *orcp-t-events*)))
; Mutation: the rebuild of a shorter history is not the full open's.
(must-fail-checked
 (assert-event (equal (cadr (fn-orcp-rebuild (cdr *orcp-t-events*) *orcp-t-configs* 8 4))
                      (fn-ock-recover-full *orcp-t-configs* 8 *orcp-t-events* 4))))

; KEYSTONE fn-orcp-swapped-store-is-the-full-open: the live owner is the
; open of the first event only; swapped with the rebuild, it serves the full
; open's Store and keeps the live owner's next id and (empty) connections.
(defconst *orcp-t-live*
  (fn-ocfg-owner (fn-ock-recover-full *orcp-t-configs* 8 (list (car *orcp-t-events*)) 4)))
(defconst *orcp-t-swapped*
  (fn-orcp-swapped-owner *orcp-t-live* (fn-ocfg-owner (cadr *orcp-t-rebuilt*))))
(assert-event (equal (fn-own-store *orcp-t-swapped*)
                     (fn-own-store (fn-ocfg-owner (fn-ock-recover-full *orcp-t-configs* 8
                                                                       *orcp-t-events* 4)))))
(assert-event (not (equal (fn-own-store *orcp-t-swapped*) (fn-own-store *orcp-t-live*))))
(assert-event (equal (fn-own-next-id *orcp-t-swapped*) (fn-own-next-id *orcp-t-live*)))
(assert-event (equal (fn-own-conns *orcp-t-swapped*) nil))
