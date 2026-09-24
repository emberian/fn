; Kind-7 local-delta correspondence has a reached positive application and
; an exact failed-match tooth for its one premise.  The larger outer cache
; invariant and kind-5/18/8/9 tests follow the serving wrapper checkpoint.
(in-package "ACL2")
(include-book "../../books/bp-node-debt-cache-invariants")
(include-book "../../books/codec-attach")
(include-book "bp-node-debt-tests")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bpndc-record*
  (fn-bpn-nth 4
   (fn-bpnf-issued (fn-bpnf-answer-state *bpnd-result*))))
(defconst *bpndc-applied*
  (mv-list 3 (fn-bpah-apply-delivery
              *bpndc-record* (fn-bpnf-held-list *bpnd-s2*))))

; This record was produced by the actual :deliver-result transition and is
; the kind-7 record the actual :persist-result transition applies.
(assert-event
 (and (equal (fn-bpn-nth 3
              (fn-bpnf-issued (fn-bpnf-answer-state *bpnd-result*)))
             :deliver)
      (equal (car *bpnd-kind7*) :persist-delivery)
      (car *bpndc-applied*)
      (equal (fn-bpnd-held-list-debt (cadr *bpndc-applied*) *bpnd-local*)
             (+ (fn-bpnd-held-list-debt (fn-bpnf-held-list *bpnd-s2*)
                                          *bpnd-local*)
                (fn-bpnd-held-delta
                 (fn-bpnf-find-arrival
                  (fn-bpn-nth 3 *bpndc-record*)
                  (fn-bpnf-held-list *bpnd-s2*))
                 (fn-bpah-delivered-held
                  (fn-bpnf-find-arrival
                   (fn-bpn-nth 3 *bpndc-record*)
                   (fn-bpnf-held-list *bpnd-s2*))
                  *bpndc-record*)
                 *bpnd-local*)))
      (equal (fn-bpnd-debt *bpnd-after-state* *bpnd-local*)
             (+ (fn-bpnd-debt *bpnd-s2* *bpnd-local*)
                (fn-bpnd-held-handoff-delta
                 *bpnd-new-held*
                 (fn-bpnf-find-held
                  *bpnd-new-key* (fn-bpnf-held-list *bpnd-after-state*))
                 (car (fn-bpnf-handoffs *bpnd-after-state*))
                 *bpnd-local*)))))

; Remove the matched-application premise while retaining the real kind-7
; record.  An empty held list has no matching arrival and cannot acquire the
; hypothetical delivered row/debt that the conclusion would require.
(assert-event
 (not (car (mv-list 3 (fn-bpah-apply-delivery *bpndc-record* nil)))))
(must-fail
 (assert-event
  (equal
   (fn-bpnd-held-list-debt
    (cadr (mv-list 3 (fn-bpah-apply-delivery *bpndc-record* nil)))
    *bpnd-local*)
   (+ (fn-bpnd-held-list-debt nil *bpnd-local*)
      (fn-bpnd-held-delta
       (fn-bpnf-find-arrival (fn-bpn-nth 3 *bpndc-record*) nil)
       (fn-bpah-delivered-held
        (fn-bpnf-find-arrival (fn-bpn-nth 3 *bpndc-record*) nil)
       *bpndc-record*)
       *bpnd-local*)))))

; The actual kind-5 rows above are encoded into the received namespace's
; ordered name/byte input.  The same auto-event that the native host calls
; replays those bytes and carries their physical count, even though one row
; may later cease to be live held work.
(defconst *bpndc-row0-record*
  (fn-bpnf-stored-record 0 0 *bpnd-old-held*))
(defconst *bpndc-row1-record*
  (fn-bpnf-stored-record 0 1 *bpnd-new-held*))
(make-event
 `(defconst *bpndc-rows*
    ',(list (list (fn-bpnf-stored-record-name 0 0)
                  (fn-bpnf-stored-record-frame *bpndc-row0-record*))
            (list (fn-bpnf-stored-record-name 0 1)
                  (fn-bpnf-stored-record-frame *bpndc-row1-record*)))))
(make-event
 `(defconst *bpndc-replay*
    ',(fn-bpnf-family-replay-rows *bpndc-rows* (fn-bpnf-base *bpnd-s2*))))
(make-event
 `(defconst *bpndc-recover-event*
    ',(fn-bpnf-family-recover-auto-event *bpnd-s2* nil :ready *bpndc-rows*)))
(make-event
 `(defconst *bpndc-recovered*
    ',(fn-bpnp-step *bpnd-s2* *bpndc-recover-event*)))
(assert-event
 (and (fn-bpnf-stored-recordp *bpndc-row0-record*)
      (fn-bpnf-stored-recordp *bpndc-row1-record*)
      (equal (car *bpndc-replay*) :ready)
      (equal (fn-bpn-nth 1 *bpndc-replay*)
             (fn-bpnf-held-list *bpnd-s2*))
      (equal (fn-bpn-nth 5 *bpndc-recover-event*) 2)
      (fn-bpnp-host-eventp *bpndc-recover-event*)
      (equal (car (car (fn-bpnf-answer-effects *bpndc-recovered*)))
             :restart-ready)
      (equal (fn-bpnp-used (fn-bpnf-answer-state *bpndc-recovered*)) 2)
      (equal (fn-bpnp-debt (fn-bpnf-answer-state *bpndc-recovered*))
             (fn-bpnd-debt (fn-bpnf-answer-state *bpndc-recovered*)
                           *bpnd-local*))
      (equal (fn-bpnp-debt (fn-bpnf-answer-state *bpndc-recovered*)) 7)))

; A damaged observed final still counts as an observed name, but its replay
; faults.  The failed recovery cannot replace the live cache or obligations.
(defconst *bpndc-corrupt-rows*
  (cons (list (fn-bpnf-stored-record-name 0 0)
              (cons 255
                    (cdr (cadar *bpndc-rows*))))
        (cdr *bpndc-rows*)))
(make-event
 `(defconst *bpndc-fault-event*
    ',(fn-bpnf-family-recover-auto-event
       (fn-bpnf-answer-state *bpndc-recovered*) nil :ready
       *bpndc-corrupt-rows*)))
(make-event
 `(defconst *bpndc-fault*
    ',(fn-bpnp-step (fn-bpnf-answer-state *bpndc-recovered*)
                   *bpndc-fault-event*)))
(assert-event
 (and (equal (car (fn-bpnf-family-replay-rows
                   *bpndc-corrupt-rows*
                   (fn-bpnf-base (fn-bpnf-answer-state *bpndc-recovered*))))
             :fault)
      (fn-bpnp-host-eventp *bpndc-fault-event*)
      (equal (car (car (fn-bpnf-answer-effects *bpndc-fault*)))
             :restart-fault)
      (equal (fn-bpnp-used (fn-bpnf-answer-state *bpndc-fault*)) 2)
      (equal (fn-bpnp-debt (fn-bpnf-answer-state *bpndc-fault*)) 7)
      (equal (fn-bpnf-held-list (fn-bpnf-answer-state *bpndc-fault*))
             (fn-bpnf-held-list
              (fn-bpnf-answer-state *bpndc-recovered*)))))
