; Kind-7 local-delta correspondence has a reached positive application and
; an exact failed-match tooth for its one premise.  The larger outer cache
; invariant and kind-5/18/8/9 tests follow the serving wrapper checkpoint.
(in-package "ACL2")
(include-book "../../books/bp-node-debt-cache-invariants")
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
