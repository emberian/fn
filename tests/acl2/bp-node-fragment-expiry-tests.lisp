(in-package "ACL2")
(include-book "../../books/bp-node-fragment-expiry")
(include-book "bp-node-fragment-family-tests")
(include-book "std/testing/must-fail" :dir :system)

; The existing family is complete.  An old kind-5 row without an arrival
; clock anchor is unknown and cannot authorize a new family proposal.
(defconst *bpnfe-unknown* (fn-clock-observation 1 2343 0 t))
(assert-event (equal (car (fn-bpnf-family-plan *bpnff-state* *bpnff-p3*))
                     :ready))
(assert-event (equal (fn-bpnf-family-plan-at
                      *bpnff-state* *bpnff-p3* *bpnfe-unknown*)
                     '(:blocked :expiry)))

; For a common confident wall observation, every selected row is live and
; the existing principal/coherence partition is left intact.
(defconst *bpnfe-live-state*
  (fn-bpnf-state (fn-bpnf-base *bpnff-state*)
                 (list (update-nth 9 '(:wall) *bpnff-p3*)
                       (update-nth 9 '(:wall) *bpnff-p0*))
                 nil nil nil nil nil 3 0))
(assert-event
 (equal (car (fn-bpnf-family-plan-at
              *bpnfe-live-state*
              (car (fn-bpnf-held-list *bpnfe-live-state*))
              *bpnfe-unknown*)) :ready))

; Expiring one selected source blocks the whole family.  Filtering the
; expired source out would hide its bytes and alter the family decision.
(defconst *bpnfe-expired-observation*
  (fn-clock-observation 1 60002344 0 t))
(assert-event
 (equal (fn-bpnf-family-plan-at
         *bpnfe-live-state*
         (car (fn-bpnf-held-list *bpnfe-live-state*))
         *bpnfe-expired-observation*)
        '(:blocked :expiry)))
(must-fail
 (assert-event
  (equal (car (fn-bpnf-family-plan-at
               *bpnfe-live-state*
               (car (fn-bpnf-held-list *bpnfe-live-state*))
               *bpnfe-expired-observation*)) :ready)))
