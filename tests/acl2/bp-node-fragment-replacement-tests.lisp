(in-package "ACL2")
(include-book "../../books/bp-node-fragment-replacement")
(include-book "bp-node-fragment-plan-tests")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bpnfr-record*
  (fn-bpnf-family-record 3 8 0 7 (nth 2 *bpnfp-plan*)))
(defconst *bpnfr-applied*
  (fn-bpnf-family-apply *bpnff-state* *bpnfr-record* 7))
(assert-event (equal (car *bpnfr-applied*) :ready))
(assert-event
 (and (equal (nth 3 *bpnfr-applied*) (list *bpnff-p3* *bpnff-p0*))
      (equal (nth 9 (nth 2 *bpnfr-applied*))
             (nth 9 *bpnff-p0*))
      (equal (fn-bpnf-held-wire (nth 2 *bpnfr-applied*))
             (nth 2 *bpnfp-plan*))
      (member-equal *bpnff-q3* (nth 1 *bpnfr-applied*))
      (member-equal *bpnff-pbad* (nth 1 *bpnfr-applied*))
      (not (member-equal *bpnff-p3* (nth 1 *bpnfr-applied*)))
      (not (member-equal *bpnff-p0* (nth 1 *bpnfr-applied*)))))
(assert-event
 (equal (fn-bpnf-family-apply *bpnff-state* *bpnfr-record* 8)
        '(:fault :family-anchor)))
(defconst *bpnfr-colliding-arrival-state*
  (fn-bpnf-state (fn-bpnf-base *bpnff-state*)
                 (cons *bpnff-p3* (fn-bpnf-held-list *bpnff-state*))
                 nil nil nil nil nil 3 0))
(assert-event
 (equal (fn-bpnf-family-apply
         *bpnfr-colliding-arrival-state* *bpnfr-record* 7)
        '(:fault :family-anchor)))
(assert-event
 (equal (fn-bpnf-family-apply
         *bpnff-state*
         (fn-bpnf-family-record 3 8 0 7 '(159 0)) 7)
        '(:fault :family-image)))
(must-fail
 (assert-event
  (equal (car (fn-bpnf-family-apply
               *bpnff-state*
               (fn-bpnf-family-record 3 8 0 7 '(159 0)) 7))
         :ready)))
