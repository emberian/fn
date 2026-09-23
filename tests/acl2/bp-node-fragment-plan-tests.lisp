(in-package "ACL2")
(include-book "../../books/bp-node-fragment-plan")
(include-book "bp-node-fragment-family-tests")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bpnfp-plan*
  (fn-bpnf-family-plan *bpnff-state* *bpnff-p3*))
(assert-event (equal (car *bpnfp-plan*) :ready))
(assert-event (fn-bpb-bundlep (cadr *bpnfp-plan*)))
(assert-event (equal (fn-bpb-payload (cadr *bpnfp-plan*))
                     '(10 20 30 40 50 60 70 80)))
(assert-event (not (fn-bpp-fragmentp
                    (fn-bpp-flags
                     (fn-bpb-bundle-primary (cadr *bpnfp-plan*))))))
(assert-event (equal (nth 4 *bpnfp-plan*) *bpnff-p0*))
(assert-event
 (equal (nth 3 *bpnfp-plan*)
        (list (list '(112) (fn-bpnf-held-id *bpnff-p3*) 0)
              (list '(112) (fn-bpnf-held-id *bpnff-p0*) 2))))
(assert-event (equal (fn-bpnf-family-plan *bpnff-conflict-state*
                                          *bpnff-p3*)
                     '(:conflict 4)))
(assert-event (equal (fn-bpnf-family-plan *bpnff-state* *bpnff-pbad*)
                     '(:missing 0 6)))
(assert-event (equal (fn-bpnf-family-plan *bpnff-state* *bpnff-pdeleted*)
                     '(:invalid :bounds)))
(must-fail
 (assert-event
  (equal (car (fn-bpnf-family-plan *bpnff-conflict-state*
                                   *bpnff-p3*)) :ready)))
(defconst *bpnfp-tight-state*
  (fn-bpnf-state (fn-bpn-initial-machine-state *bpnff-config* 1 1048576)
                 (fn-bpnf-held-list *bpnff-state*)
                 nil nil nil nil nil 3 0))
(assert-event (equal (fn-bpnf-family-plan *bpnfp-tight-state* *bpnff-p3*)
                     '(:capacity)))
