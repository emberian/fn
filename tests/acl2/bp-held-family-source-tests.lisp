; Real received and family constructors: complete positives and removals.
(in-package "ACL2")
(include-book "../../books/bp-held-family-source")
(include-book "bp-node-fragment-family-tests")
(include-book "bp-handoff-producer-shape-tests")
(defconst *bphgf-rows* (list *bpnff-p3* *bpnff-q3* *bpnff-pbad* *bpnff-p0*))
(defconst *bphgf-state* (fn-bpnf-state (fn-bpn-initial-machine-state *bpnff-config* 8 1048576) *bphgf-rows* nil nil nil nil nil 3 0))
(defconst *bphgf-plan* (fn-bpnf-family-plan *bphgf-state* *bpnff-p3*))
(defconst *bphgf-record* (fn-bpnf-family-record 3 8 0 7 (nth 2 *bphgf-plan*)))
(defconst *bphgf-applied* (fn-bpnf-family-apply *bphgf-state* *bphgf-record* 7))
(assert-event (and (fn-bpn-machine-statep (fn-bpnf-base *bphgf-state*)) (fn-bphs-held-sourcesp *bphgf-rows*) (fn-bphg-held-auxsp *bphgf-rows*) (equal (car *bphgf-applied*) :ready) (fn-bphg-held-auxsp (fn-bpn-nth 1 *bphgf-applied*)) (fn-bphs-held-sourcesp (fn-bpn-nth 1 *bphgf-applied*))))
(assert-event (and (fn-bphs-held-sourcesp *bphgf-rows*) (fn-bphg-consumed-rowsp (fn-bpnf-family-consumed-ids *bphgf-rows*))))
; Corrupted principal remains accepted by the old held predicate. It is not
; an actual received source: both principal and CL principal are corrupted.
(defun bphgft-corrupt-principal (h)
 (declare (xargs :guard t :verify-guards nil))
 (update-nth 1 :foreign-principal (update-nth 4 (update-nth 4 :foreign-principal (fn-bpn-nth 4 h)) h)))
(defconst *bphgf-bad-source-rows* (list (bphgft-corrupt-principal *bpnff-p3*) (bphgft-corrupt-principal *bpnff-p0*)))
(defconst *bphgf-bad-source-state* (fn-bpnf-state (fn-bpnf-base *bphgf-state*) *bphgf-bad-source-rows* nil nil nil nil nil 3 0))
(defconst *bphgf-bad-source-applied* (fn-bpnf-family-apply *bphgf-bad-source-state* *bphgf-record* 7))
(assert-event (and (not (fn-bphs-held-sourcesp *bphgf-bad-source-rows*)) (not (fn-bphg-consumed-rowsp (fn-bpnf-family-consumed-ids *bphgf-bad-source-rows*)))))
; Remove source carry from both family theorems; retain aux and ready.
(assert-event (and (not (fn-bphs-held-sourcesp *bphgf-bad-source-rows*)) (fn-bphg-held-auxsp *bphgf-bad-source-rows*) (equal (car *bphgf-bad-source-applied*) :ready) (not (fn-bphg-held-auxsp (fn-bpn-nth 1 *bphgf-bad-source-applied*))) (not (fn-bphs-held-sourcesp (fn-bpn-nth 1 *bphgf-bad-source-applied*)))))
; Remove aux carry in an unrelated retained row; retain source and ready.
(defconst *bphgf-bad-aux-rows* (list *bpnff-p3* (update-nth 5 :foreign-submission *bpnff-q3*) *bpnff-p0*))
(defconst *bphgf-bad-aux-state* (fn-bpnf-state (fn-bpnf-base *bphgf-state*) *bphgf-bad-aux-rows* nil nil nil nil nil 3 0))
(defconst *bphgf-bad-aux-applied* (fn-bpnf-family-apply *bphgf-bad-aux-state* *bphgf-record* 7))
(assert-event (and (fn-bphs-held-sourcesp *bphgf-bad-aux-rows*) (not (fn-bphg-held-auxsp *bphgf-bad-aux-rows*)) (equal (car *bphgf-bad-aux-applied*) :ready) (not (fn-bphg-held-auxsp (fn-bpn-nth 1 *bphgf-bad-aux-applied*)))))
; Remove ready for both: retained input carries do not make fault data rows.
(assert-event (let ((a (fn-bpnf-family-apply *bphgf-state* *bphgf-record* 8))) (and (fn-bphs-held-sourcesp *bphgf-rows*) (fn-bphg-held-auxsp *bphgf-rows*) (not (equal (car a) :ready)) (not (fn-bphg-held-auxsp (fn-bpn-nth 1 a))) (not (fn-bphs-held-sourcesp (fn-bpn-nth 1 a))))))
; Received constructor's four premises, and unconditional real anchor shape.
(assert-event (and (fn-bpnf-cl-ingressp *fn-bphsp-ingress*) (natp 0) (fn-bpb-bundlep *fn-bphsp-bundle*) (equal (fn-bpb-encode *fn-bphsp-bundle*) (fn-bpb-encode *fn-bphsp-bundle*)) (fn-bphs-held-sourcep (fn-bpnf-frame-held-with-anchor *fn-bphsp-ingress* 0 *fn-bphsp-bundle* (fn-bpb-encode *fn-bphsp-bundle*) '(:wall))) (fn-bphg-anchorp (fn-bpnf-received-anchor *fn-bphsp-bundle* (fn-clock-observation 1000 0 0 nil)))))
(assert-event (and (not (fn-bpnf-cl-ingressp nil)) (natp 0) (fn-bpb-bundlep *fn-bphsp-bundle*) (equal (fn-bpb-encode *fn-bphsp-bundle*) (fn-bpb-encode *fn-bphsp-bundle*)) (not (fn-bphs-held-sourcep (fn-bpnf-frame-held-with-anchor nil 0 *fn-bphsp-bundle* (fn-bpb-encode *fn-bphsp-bundle*) nil)))))
(assert-event (and (fn-bpnf-cl-ingressp *fn-bphsp-ingress*) (not (natp -1)) (fn-bpb-bundlep *fn-bphsp-bundle*) (equal (fn-bpb-encode *fn-bphsp-bundle*) (fn-bpb-encode *fn-bphsp-bundle*)) (not (fn-bphs-held-sourcep (fn-bpnf-frame-held-with-anchor *fn-bphsp-ingress* -1 *fn-bphsp-bundle* (fn-bpb-encode *fn-bphsp-bundle*) nil)))))
; Bundle omission is a logical corrupted-input witness: executable guard
; requires a real bundle, so only this expression disables guard checking.
(assert-event (with-guard-checking :none (and (fn-bpnf-cl-ingressp *fn-bphsp-ingress*) (natp 0) (not (fn-bpb-bundlep nil)) (equal (fn-bpb-encode nil) (fn-bpb-encode nil)) (not (fn-bphs-held-sourcep (fn-bpnf-frame-held-with-anchor *fn-bphsp-ingress* 0 nil (fn-bpb-encode nil) nil))))))
(assert-event (and (fn-bpnf-cl-ingressp *fn-bphsp-ingress*) (natp 0) (fn-bpb-bundlep *fn-bphsp-bundle*) (not (equal nil (fn-bpb-encode *fn-bphsp-bundle*))) (not (fn-bphs-held-sourcep (fn-bpnf-frame-held-with-anchor *fn-bphsp-ingress* 0 *fn-bphsp-bundle* nil nil)))))
