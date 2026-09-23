; Reachable principal/coherence partitions and offset-zero header selection.
(in-package "ACL2")
(include-book "../../books/bp-node-fragment-family")
(include-book "../../books/codec-attach")

(defconst *bpnff-local* (cons :dtn '(47 47 102 110 45 97 47)))
(defconst *bpnff-peer* (cons :dtn '(47 47 102 110 45 98 47)))
(defconst *bpnff-config*
  (fn-bpn-config *bpnff-local* 3600000 1 32 1048576))
(defconst *bpnff-base-primary*
  (fn-bpp-make-block 0 1 *bpnff-local* *bpnff-peer* *bpnff-peer*
                     2342 2 60000000 nil nil))
(defconst *bpnff-other-lifetime-primary*
  (fn-bpp-make-block 0 1 *bpnff-local* *bpnff-peer* *bpnff-peer*
                     2342 2 60000001 nil nil))

(defun fn-bpnfft-bundle (primary offset bytes total)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpb-make-bundle
   (fn-bpf-fragment-block primary offset total)
   nil (fn-bpb-payload-block 1 bytes)))

(defun fn-bpnfft-held (principal arrival bundle constraints deleted)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpnf-held principal (fn-bpb-bundle-id bundle) arrival
                 (list :cl arrival 1 *bpnff-peer* principal 0)
                 nil nil bundle (fn-bpb-encode bundle) nil nil nil
                 constraints nil deleted arrival))

(defconst *bpnff-b0*
  (fn-bpnfft-bundle *bpnff-base-primary* 0 '(10 20 30 40 50) 8))
(defconst *bpnff-b3*
  (fn-bpnfft-bundle *bpnff-base-primary* 3 '(40 50 60 70 80) 8))
(defconst *bpnff-bq*
  (fn-bpnfft-bundle *bpnff-base-primary* 3 '(40 99 60 70 80) 8))
(defconst *bpnff-bbad*
  (fn-bpnfft-bundle *bpnff-other-lifetime-primary* 6 '(99 80) 8))
(defconst *bpnff-bdeleted*
  (fn-bpnfft-bundle *bpnff-base-primary* 4 '(99 60 70 80) 8))
(defconst *bpnff-bconsumed*
  (fn-bpnfft-bundle *bpnff-base-primary* 5 '(99 70 80) 8))
(defconst *bpnff-bconflict*
  (fn-bpnfft-bundle *bpnff-base-primary* 2 '(30 40 99 60 70 80) 8))
(defconst *bpnff-p0* (fn-bpnfft-held '(112) 2 *bpnff-b0* '(:dispatch-pending) nil))
(defconst *bpnff-p3* (fn-bpnfft-held '(112) 0 *bpnff-b3* '(:dispatch-pending) nil))
(defconst *bpnff-q3* (fn-bpnfft-held '(113) 1 *bpnff-bq* '(:dispatch-pending) nil))
(defconst *bpnff-pbad* (fn-bpnfft-held '(112) 3 *bpnff-bbad* '(:dispatch-pending) nil))
(defconst *bpnff-pdeleted* (fn-bpnfft-held '(112) 4 *bpnff-bdeleted* '(:dispatch-pending) t))
(defconst *bpnff-pconsumed* (fn-bpnfft-held '(112) 5 *bpnff-bconsumed* :reassembly-consumed nil))
(defconst *bpnff-pconflict* (fn-bpnfft-held '(112) 6 *bpnff-bconflict* '(:dispatch-pending) nil))

(defconst *bpnff-state*
  (fn-bpnf-state (fn-bpn-initial-machine-state *bpnff-config* 8 1048576)
                 (list *bpnff-p3* *bpnff-q3* *bpnff-pbad* *bpnff-p0*
                       *bpnff-pdeleted* *bpnff-pconsumed*)
                 nil nil nil nil nil 3 0))

; All rows are valid A1 held records.  The nonzero-offset P fragment is first
; in arrival/list order; only the later offset-zero row supplies the header.
(assert-event (and (fn-bpp-blockp *bpnff-base-primary*)
                   (fn-bpb-bundlep *bpnff-b0*)
                   (fn-bpb-bundlep *bpnff-b3*)
                   (fn-bpb-bundlep *bpnff-bq*)
                   (fn-bpb-bundlep *bpnff-bbad*)
                   (fn-bpb-bundlep *bpnff-bconflict*)))
(assert-event (and (fn-bpnf-heldp *bpnff-p0*)
                   (fn-bpnf-heldp *bpnff-p3*)
                   (fn-bpnf-heldp *bpnff-q3*)
                   (fn-bpnf-heldp *bpnff-pbad*)
                   (fn-bpnf-heldp *bpnff-pdeleted*)
                   (fn-bpnf-heldp *bpnff-pconsumed*)
                   (fn-bpnf-heldp *bpnff-pconflict*)))
(assert-event
 (equal (fn-bpp-adu-key (fn-bpb-bundle-primary *bpnff-b3*))
        (fn-bpp-adu-key (fn-bpb-bundle-primary *bpnff-bq*))))
(assert-event
 (not (equal (fn-bpnf-fragment-coherence-key
              (fn-bpb-bundle-primary *bpnff-b3*))
             (fn-bpnf-fragment-coherence-key
              (fn-bpb-bundle-primary *bpnff-bbad*)))))
; Apart from Q's independent principal partition, every same-principal row
; has a distinct RFC bundle ID and is a fresh A1 reception decision.
(assert-event
 (and (not (equal (fn-bpb-bundle-id *bpnff-b3*)
                  (fn-bpb-bundle-id *bpnff-bbad*)))
      (not (equal (fn-bpb-bundle-id *bpnff-b3*)
                  (fn-bpb-bundle-id *bpnff-bconflict*)))
      (equal (fn-bpnf-receive-decision
              (list *bpnff-p3* *bpnff-p0*)
              (list :cl 7 1 *bpnff-peer* '(112) 0)
              *bpnff-bconflict*)
             :fresh)))
(assert-event
 (and (equal (fn-bpnf-receive-decision
              (list *bpnff-p3* *bpnff-p0*)
              (list :cl 8 1 *bpnff-peer* '(112) 0)
              *bpnff-bbad*)
             :fresh)
      (equal (fn-bpnf-receive-decision
              (list *bpnff-p3* *bpnff-p0*)
              (list :cl 9 1 *bpnff-peer* '(113) 0)
              *bpnff-bq*)
             :fresh)))
(defconst *bpnff-two-held-state*
  (fn-bpnf-state (fn-bpnf-base *bpnff-state*)
                 (list *bpnff-p3* *bpnff-p0*)
                 nil nil nil nil nil 3 0))
(assert-event
 (equal (car (car (fn-bpnf-answer-effects
                   (fn-bpnf-step
                    *bpnff-two-held-state*
                    (list :receive-bundle *bpnff-bconflict*
                          (fn-bpb-encode *bpnff-bconflict*)
                          (list :cl 7 1 *bpnff-peer* '(112) 0))))))
        :persist))
(assert-event (equal (fn-bpnf-active-set *bpnff-state* *bpnff-p3*)
                     (list *bpnff-p3* *bpnff-p0*)))
(assert-event
 (not (equal (car (fn-bpnf-active-set *bpnff-state* *bpnff-p3*))
             *bpnff-p0*)))
(assert-event (equal (fn-bpnf-fragment-query *bpnff-state* *bpnff-p3*)
                     '(:ok (10 20 30 40 50 60 70 80))))
(assert-event
 (equal (fn-bpnf-offset-zero-source
         (fn-bpnf-active-set *bpnff-state* *bpnff-p3*))
        *bpnff-p0*))
(assert-event
 (not (fn-bpnf-offset-zero-source (list *bpnff-p3*))))

; Dropping principal equality would mix Q's contradictory byte 99 at ADU
; position 4 into P's successful cover.  Dropping coherence equality would
; cause a separate conflict at position 6 with P's altered-lifetime fragment.
(assert-event
 (equal (fn-bpf-reassemble
         (fn-bpnf-fragment-cells (list *bpnff-p3* *bpnff-q3* *bpnff-p0*)) 8)
        '(:conflict 4)))
(assert-event
 (equal (fn-bpf-reassemble
         (fn-bpnf-fragment-cells (list *bpnff-p3* *bpnff-pbad* *bpnff-p0*)) 8)
        '(:conflict 6)))
(assert-event
 (equal (fn-bpf-reassemble
         (fn-bpnf-fragment-cells (list *bpnff-p3* *bpnff-pdeleted* *bpnff-p0*)) 8)
        '(:conflict 4)))
(assert-event
 (equal (fn-bpf-reassemble
         (fn-bpnf-fragment-cells (list *bpnff-p3* *bpnff-pconsumed* *bpnff-p0*)) 8)
        '(:conflict 5)))
(assert-event (not (member-equal *bpnff-q3*
                                  (fn-bpnf-active-set *bpnff-state* *bpnff-p3*))))
(assert-event (not (member-equal *bpnff-pbad*
                                  (fn-bpnf-active-set *bpnff-state* *bpnff-p3*))))
(assert-event (not (member-equal *bpnff-pdeleted*
                                  (fn-bpnf-active-set *bpnff-state* *bpnff-p3*))))
(assert-event (not (member-equal *bpnff-pconsumed*
                                  (fn-bpnf-active-set *bpnff-state* *bpnff-p3*))))

; A coherent same-principal row with one differing byte must participate and
; make conflict visible; partitioning never hides a real family conflict.
(defconst *bpnff-conflict-state*
  (fn-bpnf-state (fn-bpnf-base *bpnff-state*)
                 (cons *bpnff-pconflict* (fn-bpnf-held-list *bpnff-state*))
                 nil nil nil nil nil 3 0))
(assert-event (equal (fn-bpnf-fragment-query *bpnff-conflict-state* *bpnff-p3*)
                     '(:conflict 4)))
(assert-event (equal (fn-bpnf-fragment-query *bpnff-state* *bpnff-pbad*)
                     '(:missing 0 6)))
(assert-event (equal (fn-bpnf-fragment-query *bpnff-state* *bpnff-pdeleted*)
                     '(:invalid :bounds)))
(assert-event
 (equal (fn-bpnf-fragment-query
         *bpnff-state*
         (fn-bpnfft-held '(112) 99 *bpnff-b0* '(:dispatch-pending) nil))
        '(:invalid :bounds)))

; The actual A1 reception step proposes persistence but leaves held rows and
; the fragment query unchanged until its matching durable callback.
(defconst *bpnff-receive-proposal*
  (fn-bpnf-step *bpnff-state*
                 (list :receive-bundle *bpnff-bq* (fn-bpb-encode *bpnff-bq*)
                       (list :cl 8 1 *bpnff-peer* '(114) 0))))
(assert-event (equal (car (car (fn-bpnf-answer-effects *bpnff-receive-proposal*)))
                     :persist))
(assert-event
 (equal (fn-bpnf-fragment-query
         (fn-bpnf-answer-state *bpnff-receive-proposal*) *bpnff-p3*)
        (fn-bpnf-fragment-query *bpnff-state* *bpnff-p3*)))
