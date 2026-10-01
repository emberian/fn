; Legacy :none route: no structural/stale BIB metadata is verified authority.
; Source tests proposed, not admitted. No real crypto/provider is fabricated.
(in-package "ACL2")
(include-book "../../books/bp-node-receive-boundary")
(include-book "../../books/bpsec-operation")
(defconst *bpcrc-local* (cons :dtn '(47 47 102 110 45 97 47)))
(defconst *bpcrc-peer* (cons :dtn '(47 47 102 110 45 98 47)))
(defconst *bpcrc-config* (fn-bpn-config *bpcrc-local* 3600000 2 32 1048576))
(defconst *bpcrc-obs* (fn-clock-observation 1000 0 0 nil))
(defconst *bpcrc-valid*
 (fn-bpn-send-bundle *bpcrc-config* *bpcrc-peer* '(65 66 67) 7 *bpcrc-obs*))
(defun fn-bpcrc-zero (bundle extra)
 (declare (xargs :guard t :verify-guards nil))
 (let ((p (fn-bpb-bundle-primary bundle)))
  (fn-bpb-make-bundle
   (fn-bpp-make-block (fn-bpp-flags p) 0 (fn-bpp-destination p)
    (fn-bpp-source p) (fn-bpp-report-to p) (fn-bpp-creation-time p)
    (fn-bpp-sequence p) (fn-bpp-lifetime p) (fn-bpp-fragment-offset p)
    (fn-bpp-total-adu-length p))
   (append extra (fn-bpb-bundle-blocks bundle)) (fn-bpb-bundle-payload bundle))))
; ASB sequence: primary target0/context1/source ipn10.0/HMAC384 bytes.
; Its presence and canonical spelling are deliberately not a verification.
(defconst *bpcrc-bib-bytes*
 (append '(129 0 1 0 130 2 130 10 0 129 129 130 1 88 48)
         (make-list 48 :initial-element 65)))
(defconst *bpcrc-bare* (fn-bpcrc-zero *bpcrc-valid* nil))
(defconst *bpcrc-bib*
 (fn-bpcrc-zero *bpcrc-valid* (list (fn-bpb-make-block 11 20 0 2 *bpcrc-bib-bytes*))))
(defconst *bpcrc-malformed*
 (fn-bpcrc-zero *bpcrc-valid* (list (fn-bpb-make-block 11 20 0 2 '(255)))))
(defconst *bpcrc-ingress* (list :cl (cons 0 1) 1 *bpcrc-peer* '(112) 0))
(assert-event
 (and (fn-bpn-configp *bpcrc-config*) (fn-clock-observationp *bpcrc-obs*)
      (fn-bpnf-cl-ingressp *bpcrc-ingress*)
      (fn-bpb-bundlep *bpcrc-bare*) (fn-bpb-bundlep *bpcrc-bib*)
      (fn-bpb-bundlep *bpcrc-malformed*)
      (equal (fn-bpn-receive-carrier *bpcrc-config* (fn-bpb-encode *bpcrc-bare*) *bpcrc-obs*)
             '(:refused :block-unintelligible))
      (equal (fn-bpnf-receive-wire-event *bpcrc-config* (fn-bpb-encode *bpcrc-bib*)
               *bpcrc-obs* *bpcrc-ingress*) '(:refused :block-unintelligible))
      (equal (fn-bpnf-receive-wire-event *bpcrc-config* (fn-bpb-encode *bpcrc-malformed*)
               *bpcrc-obs* *bpcrc-ingress*) '(:refused :block-unintelligible))))
; Real current-source/key/provider provenance remains absent even when supplied
; descriptor matching metadata says verified; a stale view emits no evidence.
(defconst *bpcrc-op*
 (fn-bps-op-make :verify-bib '(:bps-ref 1 2) '(:bps-ref 10 3)
   '(:bps-ref 20 4) '(:bps-ref 30 5) 20 0 1
   '(:bps-bib-params 6 7 (:bytes-span 40 100 24))
   '(:bps-ref 50 6) '(:bytes-span 40 200 48)))
(defconst *bpcrc-stale*
 (fn-bps-op-complete (list :bps-operation :issued *bpcrc-op*)
  '(:bps-current (:bps-ref 10 3) (:bps-ref 20 5) (:bps-ref 30 5) (:bps-ref 50 6))
  (list :bps-completion *bpcrc-op* :verified nil :ok)))
(assert-event
 (and (fn-bps-opp *bpcrc-op*) (eq (fn-bps-field 1 *bpcrc-stale*) :ignored)
      (eq (fn-bps-field 2 *bpcrc-stale*) :stale-current)
      (null (fn-bps-field 4 *bpcrc-stale*))
      (equal (fn-bpnf-receive-wire-event *bpcrc-config* (fn-bpb-encode *bpcrc-bib*)
               *bpcrc-obs* *bpcrc-ingress*) '(:refused :block-unintelligible))))
(assert-event
 (and (fn-bpn-acceptedp (fn-bpn-receive-carrier *bpcrc-config*
                         (fn-bpb-encode *bpcrc-valid*) *bpcrc-obs*))
      (fn-bpnf-receive-wire-readyp
       (fn-bpnf-receive-wire-event *bpcrc-config* (fn-bpb-encode *bpcrc-valid*)
          *bpcrc-obs* *bpcrc-ingress*))))
