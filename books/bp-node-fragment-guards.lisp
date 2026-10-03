; Guard obligations for the exact native fragment-step call. The base-state
; invariant is maintained by the owner; no whole-held-list recognizer is
; inserted into the served event body.
(in-package "ACL2")
(include-book "bp-node-fragment-step")
(include-book "bp-node-machine-guards")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-bpnf-heldp))))

(local
 (defthm fn-bpnfg-total-nth-is-nth
   (implies (natp n)
            (equal (fn-bpn-nth n xs) (nth n xs)))
   :hints (("Goal" :induct (fn-bpn-nth n xs)
            :in-theory (enable fn-bpn-nth fn-cbor-ag-car)))))

(local
 (defthm fn-bpnfg-bundle-primary-blockp
   (implies (fn-bpb-bundlep bundle)
            (fn-bpp-blockp (fn-bpb-bundle-primary bundle)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bpb-bundlep)
                            (fn-bpp-blockp fn-bpp-eidp
                             fn-bpp-vchar-listp fn-bpp-vcharp))))))

(local
 (defthm fn-bpnfg-held-bundlep
   (implies (fn-bpnf-heldp h)
            (fn-bpb-bundlep (fn-bpnf-held-bundle h)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bpnf-heldp)
                            (fn-bpb-bundlep fn-bpb-encode))))))

(local
 (defthm fn-bpnfg-held-true-listp
   (implies (fn-bpnf-heldp h) (true-listp h))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bpnf-heldp)
                            (fn-bpb-bundlep fn-bpb-encode
                             fn-bpp-blockp fn-bpp-eidp))))))

(local
 (defthm fn-bpnfg-held-primary-guard-fields
   (implies (fn-bpnf-heldp h)
            (and (true-listp h)
                 (true-listp
                  (fn-bpb-bundle-primary (fn-bpnf-held-bundle h)))
                 (natp
                  (fn-bpp-flags
                   (fn-bpb-bundle-primary (fn-bpnf-held-bundle h))))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bpnfg-held-true-listp)
                  (:instance fn-bpnfg-held-bundlep)
                  (:instance fn-bpnfg-bundle-primary-blockp
                             (bundle (fn-bpnf-held-bundle h)))
                  (:instance fn-bpn-bundle-primary-true-list-for-guard
                             (bundle (fn-bpnf-held-bundle h)))
                  (:instance fn-bpn-report-primary-flags-natural-for-guard
                             (primary
                              (fn-bpb-bundle-primary
                               (fn-bpnf-held-bundle h)))))
            :in-theory (union-theories
                        '(fn-bpnfg-held-true-listp)
                        (theory 'minimal-theory))))))

(local
 (defthm fn-bpnfg-held-octets-natp
   (natp (fn-bpnf-held-octets held))
   :hints (("Goal" :induct (fn-bpnf-held-octets held)
            :in-theory (enable fn-bpnf-held-octets)))))

(local
 (defthm fn-bpnfg-fragment-query-true-listp
   (true-listp (fn-bpnf-fragment-query st anchor))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bpnf-fragment-query)
                            (fn-bpnf-active-set fn-bpnf-fragment-cells
                             fn-bpfw-spec fn-bpf-canvas))))))

(verify-guards fn-bpnf-arrival-count-loop)
(verify-guards fn-bpnf-arrival-count)
(verify-guards fn-bpnf-find-arrival)
(verify-guards fn-bpnf-family-retain-other-rows-loop)
(verify-guards fn-bpnf-family-retain-other-rows)
(verify-guards fn-bpnf-family-member)
(verify-guards fn-bpnf-fragment-coherence-key)
(verify-guards fn-bpnf-active-fragmentp
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnfg-held-primary-guard-fields))
           :in-theory (disable fn-bpnf-heldp fn-bpb-bundlep
                               fn-bpnfg-held-primary-guard-fields))))
(verify-guards fn-bpnf-same-fragment-family-p)
(verify-guards fn-bpnf-active-set-rows-loop)
(verify-guards fn-bpnf-active-set-rows
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnf-active-set-rows fn-ag-rev-onto
                                fn-bpnf-active-set-rows-loop-is-rev-onto)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))
(verify-guards fn-bpnf-active-set)
(verify-guards fn-bpnf-fragment-cell-exec)
(verify-guards fn-bpnf-fragment-cells-loop)
(defthm fn-bpnf-fragment-cells-loop-is-rev-onto
  (equal (fn-bpnf-fragment-cells-loop held acc)
         (fn-ag-rev-onto acc (fn-bpnf-fragment-cells held)))
  :hints (("Goal" :induct (fn-bpnf-fragment-cells-loop held acc)
                  :in-theory (enable fn-bpn-nth fn-bpb-bundle-primary
                                     fn-bpb-bundle-payload fn-bpb-block-data
                                     fn-bpb-payload))))
(verify-guards fn-bpnf-fragment-cells
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-bpn-nth fn-bpb-bundle-primary
                              fn-bpb-bundle-payload fn-bpb-block-data
                              fn-bpb-payload))))
(verify-guards fn-bpnf-fragment-query)
(verify-guards fn-bpnf-offset-zero-source
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-bpn-nth fn-bpp-fragment-offset))))
(verify-guards fn-bpnf-family-whole-bundle
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnfg-held-primary-guard-fields (h zero))
                 (:instance fn-bpnfg-held-bundlep (h zero))
                 (:instance fn-bpnfg-bundle-primary-blockp
                            (bundle (fn-bpnf-held-bundle zero))))
           :in-theory (disable fn-bpnf-heldp fn-bpb-bundlep
                               fn-bpp-blockp
                               fn-bpnfg-held-primary-guard-fields
                               fn-bpnfg-held-bundlep
                               fn-bpnfg-bundle-primary-blockp))))
(verify-guards fn-bpnf-family-plan
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpn-state-field-types-for-guard
                            (st (fn-bpnf-base st)))
                 (:instance fn-bpnfg-held-octets-natp
                            (held (fn-bpnf-held-list st)))
                 (:instance fn-bpnfg-held-octets-natp
                            (held (fn-bpnf-active-set st anchor))))
           :in-theory (disable fn-bpnf-fragment-query-is-reference
                               fn-bpnf-fragment-query fn-bpnf-active-set
                               fn-bpnf-family-whole-bundle
                               fn-bpnf-held-octets
                               fn-bpn-machine-statep
                               fn-bpn-machine-recordp
                               fn-bpb-bundlep fn-bpb-encode
                               fn-bpn-state-field-types-for-guard
                               fn-bpnfg-held-octets-natp))))
(verify-guards fn-bpnf-family-record)
(verify-guards fn-bpnf-family-recordp)
(verify-guards fn-bpnf-family-record-atp)

; The family-plan theorem is stated with car/cadr.  The executable apply
; guard uses the total selectors, so bridge just those two fields while the
; expensive plan body stays closed.
(local
 (defthm fn-bpnfg-second-is-cadr
   (equal (fn-bpn-nth 1 xs) (cadr xs))
   ; Two unfoldings and nothing else; the enabled world spent 4 s here.
   :hints (("Goal" :expand ((fn-bpn-nth 1 xs) (fn-bpn-nth 0 (cdr xs)))
            :in-theory (union-theories
                        '(fn-cbor-ag-car natp zp (natp) (zp) (binary-+)
                          (unary--) (not) default-car default-cdr)
                        (theory 'minimal-theory))))))
(local
 (defthm fn-bpnfg-car-is-car
   (equal (fn-cbor-ag-car xs) (car xs))
   :hints (("Goal" :in-theory (enable fn-cbor-ag-car)))))
(local
 (defthm fn-bpnfg-ready-plan-bundlep
   (implies (equal (fn-cbor-ag-car (fn-bpnf-family-plan st anchor)) :ready)
            (fn-bpb-bundlep
             (fn-bpn-nth 1 (fn-bpnf-family-plan st anchor))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-bpnf-family-ready-has-valid-whole))
            :in-theory (union-theories
                        '(fn-bpnfg-second-is-cadr fn-bpnfg-car-is-car)
                        (theory 'minimal-theory))))))
(verify-guards fn-bpnf-family-apply
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnfg-ready-plan-bundlep
                            (anchor (fn-bpnf-find-arrival
                                     (fn-bpn-nth 3 record)
                                     (fn-bpnf-held-list st)))))
           :in-theory (disable fn-bpnf-family-plan
                               fn-bpnf-heldp fn-bpb-bundlep
                               fn-bpn-machine-statep
                               fn-bpnfg-ready-plan-bundlep))))
(verify-guards fn-bpnf-family-rows-livep)
(verify-guards fn-bpnf-family-plan-at)
(verify-guards fn-bpnf-family-record-at)
(verify-guards fn-bpnf-family-v1-values)
(verify-guards fn-bpnf-family-v1-frame)
(verify-guards fn-bpnf-family-apply-at
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-bpn-machine-statep
                               fn-bpnf-family-record-atp
                               fn-bpnf-family-plan-at
                               fn-bpnf-family-apply))))
; Recovery calls the inherited unverified kind-5 decoder and row predicate.
; Its guard closure remains a separate A2 codec obligation.
(verify-guards fn-bpnf-family-issuedp)
(verify-guards fn-bpnf-family-propose-step
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpn-state-config-for-guard
                            (st (fn-bpnf-base st)))
                 (:instance fn-bpn-state-field-types-for-guard
                            (st (fn-bpnf-base st))))
           :in-theory (disable fn-bpn-machine-statep
                               fn-bpn-machine-recordp
                               fn-bpn-state-config-for-guard
                               fn-bpn-state-field-types-for-guard
                               fn-bpnf-family-plan fn-bpnf-family-apply
                               fn-bpnf-family-frame))))
(verify-guards fn-bpnf-family-persist-step
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-bpn-machine-statep
                               fn-bpn-machine-recordp
                               fn-bpnf-family-apply
                               fn-bpnf-family-plan))))
(verify-guards fn-bpnf-family-next-aux
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-bpn-machine-statep
                               fn-bpn-machine-recordp
                               fn-bpnf-family-plan))))
(verify-guards fn-bpnf-family-tried-p)
(verify-guards fn-bpnf-family-next-memo
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-bpn-machine-statep
                               fn-bpn-machine-recordp
                               fn-bpnf-family-plan))))
; PRF-136: the served selector reads the rows' primary blocks; it plans a
; row only when its family holds an offset-zero fragment.
(local
 (defthm fn-bpnfg-blockp-true-listp
   (implies (fn-bpp-blockp b) (true-listp b))
   :rule-classes :forward-chaining))
(verify-guards fn-bpnf-fragment-candidatep)
(local
 (defthm fn-bpnfg-candidate-primary
   (implies (fn-bpnf-fragment-candidatep h)
            (and (fn-bpp-blockp (fn-bpb-bundle-primary (fn-bpnf-held-bundle h)))
                 (true-listp (fn-bpb-bundle-primary (fn-bpnf-held-bundle h)))))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-bpnf-fragment-candidatep
                                 fn-bpnfg-blockp-true-listp)
                               (theory 'minimal-theory))))))
(verify-guards fn-bpnf-fragment-family-key
  :hints (("Goal" :in-theory (disable fn-bpp-blockp))))
(verify-guards fn-bpnf-zero-family-keys-loop
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnfg-candidate-primary)
                              (theory 'minimal-theory)))))
(verify-guards fn-bpnf-zero-family-keys
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnfg-candidate-primary fn-ag-rev-onto
                                fn-bpnf-zero-family-keys
                                fn-bpnf-zero-family-keys-loop-is-rev-onto)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))
(verify-guards fn-bpnf-family-select
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bpnfg-candidate-primary true-listp)
                       (theory 'minimal-theory)))))
(verify-guards fn-bpnf-family-next
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnf-family-select-is-aux
                            (held (fn-bpnf-held-list st)) (tried nil)
                            (zero (fn-bpnf-zero-family-keys
                                   (fn-bpnf-held-list st)))))
           :in-theory (union-theories
                       '(fn-bpnf-subsetp-equal-reflexive
                         fn-bpnf-family-keys-not-readyp-of-nil)
                       (theory 'minimal-theory)))))
;; The candidate selector the host calls (bp-service fnn-bps-fragment-effects;
;; the *1* class, Q4a item 2): it reassembles nothing, so no plan obligations.
(local
 (defthm fn-bpnfg-zero-family-keys-true-listp
   (true-listp (fn-bpnf-zero-family-keys held))
   :hints (("Goal" :induct (fn-bpnf-zero-family-keys held)
            :in-theory (e/d (fn-bpnf-zero-family-keys)
                            (fn-bpnf-fragment-candidatep
                             fn-bpnf-fragment-family-key))))))
;; The S008 coverage gate fn-bpfj-candidate calls (BM10): its helpers' guards.
;; The rows it sums are the anchor's active set, every row of which is held.
(local
 (defthm fn-bpfjg-rows-payload-octets-natp
   (implies (natp acc) (natp (fn-bpfj-rows-payload-octets rows acc)))
   :rule-classes :type-prescription))
(verify-guards fn-bpfj-rows-payload-octets
  :hints (("Goal" :in-theory (enable fn-bpnf-all-heldp))))
(local
 (defthm fn-bpfjg-active-set-rows-all-heldp
   (fn-bpnf-all-heldp (fn-bpnf-active-set-rows held anchor))
   :hints (("Goal" :induct (fn-bpnf-active-set-rows held anchor)
            :in-theory (union-theories
                        '(fn-bpnf-all-heldp fn-bpnf-active-set-rows
                          fn-bpnf-same-fragment-family-p fn-bpnf-active-fragmentp
                          car-cons cdr-cons atom)
                        (theory 'minimal-theory))))))
(local
 (defthm fn-bpfjg-active-set-all-heldp
   (fn-bpnf-all-heldp (fn-bpnf-active-set st anchor))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-bpfjg-active-set-rows-all-heldp
                                 fn-bpnf-active-set fn-bpnf-all-heldp atom)
                               (theory 'minimal-theory))))))
(verify-guards fn-bpfj-family-coveredp
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bpnfg-candidate-primary fn-bpfjg-active-set-all-heldp)
                       (theory 'minimal-theory)))))
(verify-guards fn-bpfj-candidate
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bpnfg-candidate-primary true-listp)
                       (theory 'minimal-theory)))))
(verify-guards fn-bpfj-next-candidate
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bpnfg-zero-family-keys-true-listp true-listp)
                       (theory 'minimal-theory)))))

;; Q4a increment B: the reassembly job's functions the host reaches
;; (host/native/bp-service.lisp fnn-bps-fragment-effects: fn-bpfj-start,
;; -step, -finishedp per quantum; the twins below read the finished job).
;; Their guards are the job's shape (books/bp-fragment-job-shape), checked
;; at the receive boundary, never the cells per step.
(verify-guards fn-bpfj-cells)
(verify-guards fn-bpfj-total
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnfg-held-primary-guard-fields (h anchor)))
           :in-theory (e/d (fn-bpnf-active-fragmentp)
                           (fn-bpnf-heldp fn-bpb-bundlep fn-bpp-fragmentp
                            fn-bpnfg-held-primary-guard-fields)))))
(verify-guards fn-bpfj-start
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-bpnf-active-fragmentp fn-bpfj-cells
                               fn-bpfj-total fn-bpfr-start
                               fn-bpfw-fragmentp))))
(verify-guards fn-bpfj-step
  :hints (("Goal" :in-theory (e/d (fn-bpfj-jobp fn-bpfr-statep)
                                  (fn-bpfw-fragmentp fn-bpfr-step)))))
(verify-guards fn-bpfj-finishedp
  :hints (("Goal" :in-theory (e/d (fn-bpfj-jobp fn-bpfr-statep)
                                  (fn-bpfw-fragmentp)))))
(verify-guards fn-bpfj-currentp
  :hints (("Goal" :in-theory (disable fn-bpnf-active-fragmentp fn-bpfj-cells
                                      fn-bpfj-total))))
(verify-guards fn-bpfj-wf
  :hints (("Goal" :in-theory (e/d (fn-bpfj-readable-jobp fn-bpfj-jobp
                                   fn-bpfr-statep)
                                  (fn-bpfw-fragmentp fn-bpfw-sort
                                   fn-bpfr-resume fn-bpfw-sweep-acc
                                   fn-bpnf-active-fragmentp fn-bpfj-currentp)))))
(verify-guards fn-bpfj-query
  :hints (("Goal" :in-theory (e/d (fn-bpfj-readable-jobp fn-bpfj-jobp
                                   fn-bpfr-statep)
                                  (fn-bpfw-fragmentp fn-bpfr-finish
                                   fn-bpnf-active-fragmentp fn-bpfj-currentp
                                   fn-bpnf-family-member)))))
(local
 (defthm fn-bpnfg-job-query-true-listp
   (true-listp (fn-bpfj-query st anchor job))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bpfj-query fn-bpfr-finish)
                            (fn-bpnf-active-set fn-bpnf-fragment-cells
                             fn-bpfw-spec fn-bpf-canvas fn-bpfr-resume
                             fn-bpfj-currentp fn-bpfj-finishedp
                             fn-bpnf-active-fragmentp
                             fn-bpnf-family-member))))))
(verify-guards fn-bpfj-plan
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpn-state-field-types-for-guard
                            (st (fn-bpnf-base st)))
                 (:instance fn-bpnfg-held-octets-natp
                            (held (fn-bpnf-held-list st)))
                 (:instance fn-bpnfg-held-octets-natp
                            (held (fn-bpnf-active-set st anchor))))
           :in-theory (disable fn-bpfj-query fn-bpnf-active-set
                               fn-bpnf-family-whole-bundle
                               fn-bpnf-held-octets
                               fn-bpn-machine-statep
                               fn-bpn-machine-recordp
                               fn-bpb-bundlep fn-bpb-encode
                               fn-bpn-state-field-types-for-guard
                               fn-bpnfg-held-octets-natp))))
(verify-guards fn-bpfj-plan-at)
(local
 (defthm fn-bpnfg-job-query-is-not-ready
   (not (equal (car (fn-bpfj-query st anchor job)) :ready))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bpfj-query fn-bpfr-finish fn-bpfw-outcome)
                            (fn-bpnf-active-set fn-bpnf-fragment-cells
                             fn-bpf-first-index fn-bpf-run-end
                             fn-bpfw-inputsp fn-bpfr-resume
                             fn-bpfj-currentp fn-bpfj-finishedp
                             fn-bpnf-active-fragmentp
                             fn-bpnf-family-member))))))
(local
 (defthm fn-bpnfg-ready-job-plan-bundlep
   (implies (equal (fn-cbor-ag-car (fn-bpfj-plan st anchor job limit)) :ready)
            (fn-bpb-bundlep
             (fn-bpn-nth 1 (fn-bpfj-plan st anchor job limit))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-bpfj-plan fn-bpnfg-second-is-cadr
                             fn-bpnfg-car-is-car)
                            (fn-bpnf-active-set fn-bpfj-query
                             fn-bpnf-family-whole-bundle
                             fn-bpnf-offset-zero-source fn-bpb-bundlep
                             fn-bpb-encode fn-bpnf-held-octets
                             fn-bpnf-family-consumed-ids
                             fn-cbor-octet-listp fn-bpnf-held-list
                             fn-bpn-machine-state-max-jobs
                             fn-bpn-machine-state-max-octets))))))
(verify-guards fn-bpfj-apply
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnfg-ready-job-plan-bundlep
                            (anchor (fn-bpnf-find-arrival
                                     (fn-bpn-nth 3 record)
                                     (fn-bpnf-held-list st)))))
           :in-theory (disable fn-bpfj-plan
                               fn-bpnf-heldp fn-bpb-bundlep
                               fn-bpn-machine-statep
                               fn-bpnfg-ready-job-plan-bundlep))))
(verify-guards fn-bpfj-record-anchor)
(verify-guards fn-bpfj-apply-at
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-bpn-machine-statep
                               fn-bpnf-family-record-atp
                               fn-bpfj-plan-at fn-bpfj-apply))))

;; The twins over the reassembly job have the family steps' obligations
;; (fn-bpfj-plan-at / -apply-at are guarded by the same machine-state
;; recognizer and the job's readability, both from the twins' guards).
(verify-guards fn-bpfj-propose-step
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpn-state-config-for-guard
                            (st (fn-bpnf-base st)))
                 (:instance fn-bpn-state-field-types-for-guard
                            (st (fn-bpnf-base st))))
           :in-theory (disable fn-bpn-machine-statep
                               fn-bpn-machine-recordp
                               fn-bpn-state-config-for-guard
                               fn-bpn-state-field-types-for-guard
                               fn-bpfj-plan-at fn-bpfj-apply-at
                               fn-bpfj-readable-jobp
                               fn-bpnf-family-plan fn-bpnf-family-apply
                               fn-bpnf-family-frame))))

(verify-guards fn-bpfj-persist-step
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-bpn-machine-statep
                               fn-bpn-machine-recordp
                               fn-bpfj-apply-at fn-bpfj-readable-jobp
                               fn-bpnf-family-apply
                               fn-bpnf-family-plan))))

(verify-guards fn-bpnf-fragment-step
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-bpn-machine-statep fn-bpn-machine-eventp
                               fn-bpfj-readable-jobp fn-bpnf-family-issuedp
                               fn-bpfj-propose-step fn-bpfj-persist-step
                               fn-bpnf-family-propose-step
                               fn-bpnf-family-persist-step fn-bpnf-step))))
