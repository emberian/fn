; K1 live owner retention: completed-cut invariant and host writer frames.
(in-package "ACL2")
(include-book "../host/owner-host")
(include-book "owner-retain-carried")
(include-book "owner-retain-livep")
(include-book "owner-host-relation")


(local
 (defthm fn-owner-retain-store-projection
   (equal (fn-owner-store state) (fn-sbud-oc-store (fn-owner-ocfg state)))
   :hints (("Goal" :in-theory
            '(fn-owner-store-is-configured-store-by-definition fn-sbud-oc-store)))))

(local
 (defthm fn-owner-retain-install-arena-frame
   (equal (mv-nth 2 (fn-owner-install-extended
                      oc extended key fn-arena fn-cat fn-hist state))
          fn-arena)
   :hints (("Goal" :in-theory '(fn-owner-install-extended mv-nth car-cons cdr-cons)))))

(local
 (defthm fn-owner-retain-install-store-when-recovering
   (implies (equal (mv-nth 1 (fn-owner-install-extended
                              oc extended key fn-arena fn-cat fn-hist state))
                   :recovering)
            (equal (fn-owner-store
                    (mv-nth 5 (fn-owner-install-extended
                               oc extended key fn-arena fn-cat fn-hist state)))
                   (fn-sbud-oc-store oc)))
   :hints (("Goal" :in-theory
            '(fn-owner-install-extended fn-owner-store-is-configured-store-by-definition
              fn-owner-core-is-configured-owner-by-definition fn-sbud-oc-store
              fn-owner-install-open-ocfg fn-owner-ocfg-of-install-ocfg
              fn-owner-ocfg-of-retain-carry-put fn-owner-ocfg-of-other-global-put
              fn-owner-authority-proposal-clear fn-orc-writer-enter fn-orc-writer-leave
              fn-ost-install-publication mv-nth nth endp zp car-cons cdr-cons
              (:executable-counterpart zp) (:executable-counterpart binary-+)
              (:executable-counterpart unary--))))))

(defthm fn-owner-retain-live-established-at-recovery
  (let* ((oc (fn-ock-recover-extended
              (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
              configs frontier max-conns))
         (out (fn-owner-install-extended oc extended key fn-arena fn-cat fn-hist state)))
    (implies (and (not (equal oc :fault))
                  (fn-lgoc-invariantp oc)
                  (fn-rows-handles-inp (append prefix suffix) fn-arena)
                  (fn-orcr-fold-contexts-okp (append prefix suffix)
                                             (fn-stxk-initial-context 0)
                                             (fn-arena-count fn-arena) fn-arena)
                  (equal (mv-nth 1 out) :recovering))
             (fn-owner-retain-livep (mv-nth 5 out) (mv-nth 2 out))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-owner-install-extended-establishes-when-recovering
                           (oc (fn-ock-recover-extended
                                (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
                                configs frontier max-conns)))
                 fn-owner-recovery-establishes-retained-store
                 fn-rfcl-recovery-establishes-okp)
           :in-theory '(fn-owner-retain-livep fn-owner-retain-install-arena-frame
                        fn-owner-retain-install-store-when-recovering))))

; Group C: the bounded article plan worker updates only connections.
(local
 (defthm fn-owner-retain-asto-with-conn-store-frame
   (equal (fn-sbud-oc-store (fn-asto-with-conn oc conn)) (fn-sbud-oc-store oc))
   :hints (("Goal" :in-theory
            '(fn-asto-with-conn fn-sbud-oc-store fn-ocfg-with-owner
              fn-ocfg-owner-of-fn-ocfg-make fn-own-set-conns
              fn-own-store-of-fn-own-make)))))
(local
 (defthm fn-owner-retain-asto-selection-missing-store-frame
   (equal (fn-sbud-oc-store (mv-nth 1 (fn-asto-selection-missing oc capture)))
          (fn-sbud-oc-store oc))
   :hints (("Goal" :in-theory
            '(fn-asto-selection-missing fn-owner-retain-asto-with-conn-store-frame
              mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--))))))
(local
 (defthm fn-owner-retain-asto-selection-ready-store-frame
   (equal (fn-sbud-oc-store (mv-nth 1 (fn-asto-selection-ready oc capture fuel fn-arena)))
          (fn-sbud-oc-store oc))
   :hints (("Goal" :in-theory
            '(fn-asto-selection-ready fn-asto-selection-ready-on
              fn-owner-retain-asto-selection-missing-store-frame
              mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--))))))
(local
 (defthm fn-owner-retain-asto-finish-store-frame
   (equal (fn-sbud-oc-store (mv-nth 1 (fn-asto-finish oc capture fn-arena)))
          (fn-sbud-oc-store oc))
   :hints (("Goal" :in-theory
            '(fn-asto-finish fn-owner-retain-asto-with-conn-store-frame
              mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--))))))
(local
 (defthm fn-owner-retain-asto-ready-rest-store-frame
   (equal (fn-sbud-oc-store
           (mv-nth 1 (fn-asto-ready-rest oc id rest fuel fn-arena fn-ast-ws)))
          (fn-sbud-oc-store oc))
   :hints (("Goal" :induct (fn-asto-ready-rest oc id rest fuel fn-arena fn-ast-ws)
            :in-theory
            '(fn-asto-ready-rest fn-owner-retain-asto-selection-ready-store-frame
              fn-owner-retain-asto-finish-store-frame
              mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--))))))
(defthm fn-owner-retain-ready-plan-keeps-store
  (equal (fn-sbud-oc-store (mv-nth 1 (fn-asto-ready-plan-step oc id plan fuel fn-arena fn-ast-ws)))
         (fn-sbud-oc-store oc))
  :hints (("Goal" :in-theory
           '(fn-asto-ready-plan-step fn-owner-retain-asto-ready-rest-store-frame
             mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--)))))

; Group B/C: actual durable publication and the successful capture rebuild.
(defthm fn-owner-retain-publish-keeps-retained-store
  (implies (and (fn-ocl-relation oc) (fn-osr-retainedp (fn-sbud-oc-store oc)))
    (fn-osr-retainedp (fn-sbud-oc-store (mv-nth 1 (fn-oclc-publish oc generation max-octets)))))
  :hints (("Goal"
           :use ((:instance fn-oclc-publish-is-publish)
                 (:instance fn-ocl-complete-success-install-exact-store)
                 (:instance fn-osr-configure-durable-preserves-full-retained-carry
                            (s (fn-sbud-oc-store oc)) (record (fn-ocfg-staged oc))))
           :in-theory
           '(fn-ocl-publish fn-sbud-oc-store fn-ocfg-with-owner fn-own-configure
             fn-own-store-of-fn-own-make fn-ocfg-owner-of-fn-ocfg-make
             mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--)))))

(local
 (defthm fn-owner-retain-open-kind-implies-okp
   (implies (equal (fn-sn-open-kind (fn-cpo-open-observed configs frontier records)) :ok)
            (fn-sn-open-okp (fn-cpo-open-observed configs frontier records)))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-cpo-open-observed fn-sn-open-kind fn-sn-open-state
               fn-sn-open-okp fn-sn-open-shapep fn-sn-open-ok fn-sn-open-error
               len car-cons cdr-cons))))))
(local
 (defthm fn-owner-retain-recovered-full-has-retained-fields
   (implies (not (equal (fn-ock-recover-full configs frontier records max-conns) :fault))
            (fn-osr-retainedp
             (fn-sbud-oc-store (fn-ock-recover-full configs frontier records max-conns))))
   :hints (("Goal" :use fn-osr-open-establishes-full-retained-carry
            :in-theory
            '(fn-ock-recover-full fn-ock-install fn-sbud-oc-store
              fn-own-configure fn-own-start fn-own-refresh-keeps-fields
              fn-own-store-of-fn-own-make fn-ocfg-owner-of-fn-ocfg-make
              fn-owner-retain-open-kind-implies-okp)))))
(local (defthm fn-owner-retain-nth-one-is-cadr (equal (nth 1 x) (cadr x))))
(defthm fn-owner-retain-successful-rebuild-swap-retained
  (let ((r (fn-owner-orcp-rebuild (fn-sco-capture configs rows) configs frontier max-conns)))
    (implies (and (true-listp rows) (not (equal (cadr r) :fault)))
      (fn-osr-retainedp (fn-owner-store (mv-nth 2 (fn-owner-orcp-swap r state))))))
  :hints (("Goal" :use (fn-owner-orcp-rebuild-of-capture-is-the-full-open
                        (:instance fn-owner-retain-recovered-full-has-retained-fields
                                   (records rows)))
           :in-theory '(fn-owner-orcp-swap-store-effect-by-definition fn-owner-retain-nth-one-is-cadr car-cons cdr-cons
                        (:e zp) (:e binary-+) (:e unary--)))))

; Seat-flagged history premise: statement only, deliberately not a theorem.
; (defthm fn-owner-retain-finish-submission-keeps-retained-store
;   (implies (and (fn-osr-retainedp (fn-own-store o)) (fn-apc-p carry)
;                 (fn-hist-of-storep fn-hist (fn-own-store o)))
;     (fn-osr-retainedp (fn-own-store (cdr (fn-apc-own-finish o cfg fn-arena fn-hist carry))))))

; A retained view transfers the additional fields once the successor is live.
(local
 (defthm fn-owner-retain-sn-io-keeps-retained
   (implies (and (fn-osr-retainedp s)
                 (fn-cst-relation (fn-sn-io s operation result)))
            (fn-osr-retainedp (fn-sn-io s operation result)))
   :hints (("Goal"
            :use ((:instance fn-osr-retained-view-connects-full-carry
                             (a s) (b (fn-sn-io s operation result)))
                  (:instance fn-osr-store-step-preserves-independent-live
                             (event (list :io operation result))))
            :in-theory
            '(fn-osr-retainedp fn-osr-livep fn-osr-independent-livep
              fn-snrt-step fn-snt-step fn-osr-io-keeps-retained-view
              fn-cstp-io-fields member-equal car-cons cdr-cons
              (:e equal) (:e member-equal))))) )
(local
 (defthm fn-owner-retain-rcon-io-keeps-retained
   (implies (and (fn-lgoc-invariantp oc)
                 (fn-osr-retainedp (fn-sbud-oc-store oc))
                 (fn-psrv-io-safep operation))
            (fn-osr-retainedp (fn-sbud-oc-store (fn-rcon-ocfg-io oc operation result))))
   :hints (("Goal"
            :use ((:instance fn-owner-retain-sn-io-keeps-retained (s (fn-sbud-oc-store oc)))
                  (:instance fn-lgoc-ocl-relation-cst (oc (fn-rcon-ocfg-io oc operation result)))
                  (:instance fn-psrv-rcon-io-preserves-invariant)
                  (:instance fn-rcon-ocfg-io-is-ocfg-step)
                  (:instance fn-pout-store-of-store-step (ev (list :io operation result))))
            :in-theory
            '(fn-owner-retain-sn-io-keeps-retained fn-lgoc-invariantp
              fn-lgoc-ocl-relation-cst fn-sbud-oc-store fn-snrt-step fn-snt-step
              car-cons cdr-cons)))))
(defthm fn-owner-retain-io-keeps-retained-store
  (implies (fn-owner-retain-livep state fn-arena)
    (fn-osr-retainedp (fn-owner-store (mv-nth 2 (fn-owner-io op result state)))))
  :hints (("Goal" :in-theory
           '(fn-owner-retain-livep fn-owner-retain-statep fn-owner-io fn-owner-io-safep
             fn-olr-ocfg-reserve fn-olr-ocfg-order
             fn-owner-retain-rcon-io-keeps-retained fn-psrv-rcon-io-preserves-invariant
             fn-psrv-io-safep fn-cstp-reserve-opp fn-lgoc-log-reserve-preserves-invariant
             fn-psrv-log-order-preserves-invariant
             fn-owner-retain-store-projection fn-owner-ocfg-of-install-ocfg
             member-equal mv-nth nth endp zp car-cons cdr-cons
             (:e member-equal) (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

; Group A frame: reads of the owner and the retention carry determine livep.
(defthm fn-owner-retain-livep-of-other-global-put
  (implies (and (not (equal key 'fn-owner))
                (not (equal key 'fn-owner-retain-carry)))
           (equal (fn-owner-retain-livep (f-put-global key value state) fn-arena)
                  (fn-owner-retain-livep state fn-arena)))
  :hints (("Goal" :in-theory
           '(fn-owner-retain-livep fn-orh-retain-statep-of-other-global-put
             fn-owner-retain-store-projection fn-owner-ocfg-of-other-global-put))))
(local
 (defthm fn-owner-retain-livep-of-install-frame
   (implies (and (fn-owner-retain-livep state fn-arena)
                 (fn-lgoc-invariantp oc)
                 (equal (fn-sbud-oc-store oc) (fn-owner-store state)))
            (fn-owner-retain-livep (fn-owner-install-ocfg oc state) fn-arena))
   :hints (("Goal" :in-theory
            '(fn-owner-retain-livep fn-orh-retain-statep-of-install-ocfg
              fn-owner-retain-store-projection fn-owner-ocfg-of-install-ocfg)))))

(defthm fn-owner-retain-callback-install-effects-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (fn-owner-callback-install-effects effects state) fn-arena))
  :hints (("Goal" :in-theory
           '(fn-owner-callback-install-effects fn-owner-install-served-effects fn-owner-retain-livep-of-other-global-put
             mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-install-effects-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (fn-owner-install-effects effects state) fn-arena))
  :hints (("Goal" :in-theory
           '(fn-owner-install-effects fn-owner-callback-install-effects fn-owner-install-served-effects fn-owner-retain-livep-of-other-global-put
             mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-put-credits-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (fn-owner-put-credits l state) fn-arena))
  :hints (("Goal" :in-theory
           '(fn-owner-put-credits fn-owner-retain-livep-of-other-global-put
             mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-cfg-capture-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-cfg-capture state)) fn-arena))
  :hints (("Goal" :in-theory
           '(fn-owner-cfg-capture-state-by-definition fn-owner-retain-livep-of-other-global-put
             mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-cat-may-seal-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-cat-may-seal state)) fn-arena))
  :hints (("Goal" :in-theory
           '(fn-owner-cat-may-seal fn-owner-retain-livep-of-other-global-put
             mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-cat-prepare-sealed-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-cat-prepare-sealed fn-arena fn-cat state)) fn-arena))
  :hints (("Goal" :in-theory
           '(fn-owner-cat-prepare-sealed fn-owner-cat-prepare-sealed-produced fn-owner-retain-livep-of-other-global-put
             mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--)))))

(local
 (defthm fn-owner-retain-lgoc-owner-shape
   (implies (fn-lgoc-invariantp oc) (fn-own-shapep (fn-ocfg-owner oc)))
   :hints (("Goal" :in-theory '(fn-lgoc-invariantp fn-ohr-relation-owner-shapep)))))

(defthm fn-owner-retain-install-node-secret-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep
            (mv-nth 2 (fn-owner-install-node-secret ring state)) fn-arena))
  :hints (("Goal"
           :use ((:instance fn-ohr-with-node-secret-preserves-carried-relation
                            (oc (fn-owner-ocfg state)) (secret ring)))
           :in-theory
           '(fn-owner-install-node-secret fn-owner-replace-core fn-owner-ocfg
             fn-owner-core-is-configured-owner-by-definition
             fn-owner-retain-livep fn-owner-retain-statep
             fn-owner-retain-livep-of-install-frame fn-owner-retain-store-projection
             fn-sbud-oc-store fn-ocfg-with-owner fn-own-with-node-secret
             fn-ocfg-owner-of-fn-ocfg-make fn-own-store-of-fn-own-make
             mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-apply-limit-profile-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep
            (mv-nth 2 (fn-owner-apply-limit-profile values state)) fn-arena))
  :hints (("Goal"
           :use ((:instance fn-ohr-osb-install-preserves-carried-relation
                            (oc (fn-owner-ocfg state)) (profile values)))
           :in-theory
           '(fn-owner-apply-limit-profile fn-owner-replace-core fn-owner-ocfg
             fn-owner-core-is-configured-owner-by-definition
             fn-owner-retain-livep fn-owner-retain-statep
             fn-owner-retain-livep-of-install-frame fn-owner-retain-livep-of-other-global-put
             fn-owner-retain-store-projection fn-owner-retain-lgoc-owner-shape
             fn-sbud-oc-store fn-ocfg-with-owner fn-ocfg-owner-of-fn-ocfg-make
             fn-ohr-osb-install-keeps-control
             mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-unstage-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep
            (mv-nth 2 (fn-owner-reconfigure-unstage state)) fn-arena))
  :hints (("Goal" :use ((:instance fn-psrv-unstage-preserves-invariant
                                  (oc (fn-owner-ocfg state))))
           :in-theory
           '(fn-owner-reconfigure-unstage fn-owner-authority-proposal-clear
             fn-owner-retain-livep fn-owner-retain-statep
             fn-owner-retain-livep-of-install-frame fn-owner-retain-livep-of-other-global-put
             fn-owner-ocfg-of-other-global-put fn-owner-retain-store-projection
             fn-psrv-unstage fn-sbud-oc-store fn-ocfg-owner-of-fn-ocfg-make
             mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--)))))

(local
 (defthm fn-owner-retain-step-reconfigure-store-frame
   (implies (fn-lgoc-invariantp oc)
            (equal (fn-sbud-oc-store (fn-ocfg-step oc (list :reconfigure id deltas) fn-arena))
                   (fn-sbud-oc-store oc)))
   :hints (("Goal" :in-theory
            '(fn-ocfg-step fn-sbud-oc-store fn-ohr-reconfigure-keeps-owner
              fn-owner-retain-lgoc-owner-shape car-cons cdr-cons (:e equal))))))
(defthm fn-owner-retain-step-reconfigure-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (fn-owner-step (list :reconfigure id deltas) fn-arena state) fn-arena))
  :hints (("Goal" :use ((:instance fn-ohr-step-reconfigure-preserves-carried-relation
                                  (oc (fn-owner-ocfg state))))
           :in-theory
           '(fn-owner-step fn-owner-retain-livep fn-owner-retain-statep
             fn-owner-retain-livep-of-install-frame fn-owner-retain-store-projection
             fn-owner-retain-step-reconfigure-store-frame))))

(local
 (defthm fn-owner-retain-step-take-store-frame
   (implies (fn-lgoc-invariantp oc)
            (equal (fn-sbud-oc-store (fn-ocfg-step oc (list :take) fn-arena))
                   (fn-sbud-oc-store oc)))
   :hints (("Goal" :in-theory
            '(fn-ocfg-step fn-sbud-oc-store fn-ohr-pass-take-keeps-store
              fn-owner-retain-lgoc-owner-shape car-cons cdr-cons (:e equal))))))
(defthm fn-owner-retain-step-take-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (fn-owner-step (list :take) fn-arena state) fn-arena))
  :hints (("Goal" :use ((:instance fn-ohr-step-take-preserves-carried-relation
                                  (oc (fn-owner-ocfg state))))
           :in-theory
           '(fn-owner-step fn-owner-retain-livep fn-owner-retain-statep
             fn-owner-retain-livep-of-install-frame fn-owner-retain-store-projection
             fn-owner-retain-step-take-store-frame))))

(local
 (defthm fn-owner-retain-step-control-submit-store-frame
   (implies (fn-lgoc-invariantp oc)
            (equal (fn-sbud-oc-store (fn-ocfg-step oc (list :control-submit msgid groups octets) fn-arena))
                   (fn-sbud-oc-store oc)))
   :hints (("Goal" :in-theory
            '(fn-ocfg-step fn-sbud-oc-store fn-ohr-pass-control-submit-keeps-store
              fn-owner-retain-lgoc-owner-shape car-cons cdr-cons (:e equal))))))
(defthm fn-owner-retain-step-control-submit-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (fn-owner-step (list :control-submit msgid groups octets) fn-arena state) fn-arena))
  :hints (("Goal" :use ((:instance fn-ohr-step-control-submit-preserves-carried-relation
                                  (oc (fn-owner-ocfg state))))
           :in-theory
           '(fn-owner-step fn-owner-retain-livep fn-owner-retain-statep
             fn-owner-retain-livep-of-install-frame fn-owner-retain-store-projection
             fn-owner-retain-step-control-submit-store-frame))))

(local
 (defthm fn-owner-retain-step-operator-submit-store-frame
   (implies (fn-lgoc-invariantp oc)
            (equal (fn-sbud-oc-store (fn-ocfg-step oc (list :operator-submit msgid groups octets stored) fn-arena))
                   (fn-sbud-oc-store oc)))
   :hints (("Goal" :in-theory
            '(fn-ocfg-step fn-sbud-oc-store fn-ohr-pass-operator-submit-keeps-store
              fn-owner-retain-lgoc-owner-shape car-cons cdr-cons (:e equal))))))
(defthm fn-owner-retain-step-operator-submit-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (fn-owner-step (list :operator-submit msgid groups octets stored) fn-arena state) fn-arena))
  :hints (("Goal" :use ((:instance fn-ohr-step-operator-submit-preserves-carried-relation
                                  (oc (fn-owner-ocfg state))))
           :in-theory
           '(fn-owner-step fn-owner-retain-livep fn-owner-retain-statep
             fn-owner-retain-livep-of-install-frame fn-owner-retain-store-projection
             fn-owner-retain-step-operator-submit-store-frame))))

(local
 (defthm fn-owner-retain-step-advance-store-frame
   (implies (fn-lgoc-invariantp oc)
            (equal (fn-sbud-oc-store (fn-ocfg-step oc (list :advance id) fn-arena))
                   (fn-sbud-oc-store oc)))
   :hints (("Goal" :in-theory
            '(fn-ocfg-step fn-sbud-oc-store fn-ohr-advance-keeps-store
              fn-owner-retain-lgoc-owner-shape car-cons cdr-cons (:e equal))))))
(defthm fn-owner-retain-step-advance-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (fn-owner-step (list :advance id) fn-arena state) fn-arena))
  :hints (("Goal" :use ((:instance fn-ohr-step-advance-preserves-carried-relation
                                  (oc (fn-owner-ocfg state))))
           :in-theory
           '(fn-owner-step fn-owner-retain-livep fn-owner-retain-statep
             fn-owner-retain-livep-of-install-frame fn-owner-retain-store-projection
             fn-owner-retain-step-advance-store-frame))))

(local
 (defthm fn-owner-retain-step-feed-conn-store-frame
   (implies (fn-lgoc-invariantp oc)
            (equal (fn-sbud-oc-store (fn-ocfg-step oc (list :feed-conn peer conn form) fn-arena))
                   (fn-sbud-oc-store oc)))
   :hints (("Goal" :in-theory
            '(fn-ocfg-step fn-sbud-oc-store fn-ohr-pass-feed-conn-keeps-store
              fn-owner-retain-lgoc-owner-shape car-cons cdr-cons (:e equal))))))
(defthm fn-owner-retain-step-feed-conn-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (fn-owner-step (list :feed-conn peer conn form) fn-arena state) fn-arena))
  :hints (("Goal" :use ((:instance fn-ohr-step-feed-conn-preserves-carried-relation
                                  (oc (fn-owner-ocfg state))))
           :in-theory
           '(fn-owner-step fn-owner-retain-livep fn-owner-retain-statep
             fn-owner-retain-livep-of-install-frame fn-owner-retain-store-projection
             fn-owner-retain-step-feed-conn-store-frame))))

(local
 (defthm fn-owner-retain-begin-model-frame
   (implies (fn-lgoc-invariantp oc)
            (and (fn-lgoc-invariantp (fn-ocfg-step oc (list :begin id) fn-arena))
                 (equal (fn-sbud-oc-store (fn-ocfg-step oc (list :begin id) fn-arena))
                        (fn-sbud-oc-store oc))))
   :hints (("Goal"
            :use (fn-ohr-step-begin-preserves-ocl-relation
                  (:instance fn-ohr-carried-of-same-store
                             (x (fn-ocfg-step oc (list :begin id) fn-arena))))
            :in-theory '(fn-lgoc-invariantp fn-sbud-oc-store fn-pout-begin-unfolds
                         fn-own-store-of-fn-own-make)))))
(defthm fn-owner-retain-begin-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-begin id fn-arena state)) fn-arena))
  :hints (("Goal" :in-theory
           '(fn-owner-begin fn-pout-begin fn-owner-retain-livep fn-owner-retain-statep
             fn-owner-retain-livep-of-install-frame fn-owner-retain-store-projection
             fn-owner-retain-begin-model-frame
             mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--)))))

(local
 (defthm fn-owner-retain-observe-model-frame
   (implies (fn-lgoc-invariantp oc)
            (and (fn-lgoc-invariantp (fn-ocfg-observe oc obs))
                 (equal (fn-sbud-oc-store (fn-ocfg-observe oc obs)) (fn-sbud-oc-store oc))))
   :hints (("Goal"
            :use ((:instance fn-ocl-observe-preserves-historical-relation (observation obs))
                  (:instance fn-ohr-carried-of-same-store (x (fn-ocfg-observe oc obs))))
            :in-theory
            '(fn-lgoc-invariantp fn-sbud-oc-store fn-ocfg-observe fn-ocfg-pass fn-own-step
              fn-ocfg-with-owner fn-own-observe fn-own-store-of-fn-own-make
              fn-ocfg-owner-of-fn-ocfg-make car-cons cdr-cons (:e equal))))))
(defthm fn-owner-retain-observe-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep
            (mv-nth 2 (fn-owner-observe monotonic wall wall-error has-wall state)) fn-arena))
  :hints (("Goal" :in-theory
           '(fn-owner-observe fn-owner-retain-livep fn-owner-retain-statep
             fn-owner-retain-livep-of-install-frame fn-owner-retain-store-projection
             fn-owner-retain-observe-model-frame
             mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--)))))

(local
 (defthm fn-owner-retain-step-legacy-control-submit-model-frame
   (implies (fn-lgoc-invariantp oc)
            (and (fn-lgoc-invariantp (fn-ocfg-step oc (list :legacy-control-submit msgid groups octets) fn-arena))
                 (equal (fn-sbud-oc-store (fn-ocfg-step oc (list :legacy-control-submit msgid groups octets) fn-arena))
                        (fn-sbud-oc-store oc))))
   :hints (("Goal"
            :use ((:instance fn-ohr-ocl-relation-with-owner-of-same-control-field
                             (o2 (fn-own-legacy-control-submit (fn-ocfg-owner oc) msgid groups octets)))
                  (:instance fn-ohr-carried-of-same-store (x (fn-ocfg-step oc (list :legacy-control-submit msgid groups octets) fn-arena))))
            :in-theory
            '(fn-lgoc-invariantp fn-ohr-relation-owner-shapep fn-sbud-oc-store
              fn-ocfg-step fn-ocfg-pass fn-own-step fn-ocfg-with-owner
              fn-ocfg-owner-of-fn-ocfg-make fn-own-legacy-control-submit fn-own-enqueue
              fn-own-shapep-of-fn-own-make fn-own-store-of-fn-own-make fn-own-view-of-fn-own-make fn-own-conns-of-fn-own-make fn-own-next-id-of-fn-own-make fn-own-max-conns-of-fn-own-make fn-own-ledger-field-of-fn-own-make fn-own-clock-of-fn-own-make fn-own-facts-of-fn-own-make
              car-cons cdr-cons (:e equal))))))
(defthm fn-owner-retain-step-legacy-control-submit-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (fn-owner-step (list :legacy-control-submit msgid groups octets) fn-arena state) fn-arena))
  :hints (("Goal" :in-theory
           '(fn-owner-step fn-owner-retain-livep fn-owner-retain-statep
             fn-owner-retain-livep-of-install-frame fn-owner-retain-store-projection
             fn-owner-retain-step-legacy-control-submit-model-frame))))

(local
 (defthm fn-owner-retain-step-bp-transit-submit-model-frame
   (implies (fn-lgoc-invariantp oc)
            (and (fn-lgoc-invariantp (fn-ocfg-step oc (list :bp-transit-submit cfg peer msgid octets id subject) fn-arena))
                 (equal (fn-sbud-oc-store (fn-ocfg-step oc (list :bp-transit-submit cfg peer msgid octets id subject) fn-arena))
                        (fn-sbud-oc-store oc))))
   :hints (("Goal"
            :use ((:instance fn-ohr-ocl-relation-with-owner-of-same-control-field
                             (o2 (fn-own-bp-transit-submit (fn-ocfg-owner oc) cfg peer msgid octets id subject)))
                  (:instance fn-ohr-carried-of-same-store (x (fn-ocfg-step oc (list :bp-transit-submit cfg peer msgid octets id subject) fn-arena))))
            :in-theory
            '(fn-lgoc-invariantp fn-ohr-relation-owner-shapep fn-sbud-oc-store
              fn-ocfg-step fn-ocfg-pass fn-own-step fn-ocfg-with-owner
              fn-ocfg-owner-of-fn-ocfg-make fn-own-bp-transit-submit fn-own-enqueue
              fn-own-shapep-of-fn-own-make fn-own-store-of-fn-own-make fn-own-view-of-fn-own-make fn-own-conns-of-fn-own-make fn-own-next-id-of-fn-own-make fn-own-max-conns-of-fn-own-make fn-own-ledger-field-of-fn-own-make fn-own-clock-of-fn-own-make fn-own-facts-of-fn-own-make
              car-cons cdr-cons (:e equal))))))
(defthm fn-owner-retain-step-bp-transit-submit-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (fn-owner-step (list :bp-transit-submit cfg peer msgid octets id subject) fn-arena state) fn-arena))
  :hints (("Goal" :in-theory
           '(fn-owner-step fn-owner-retain-livep fn-owner-retain-statep
             fn-owner-retain-livep-of-install-frame fn-owner-retain-store-projection
             fn-owner-retain-step-bp-transit-submit-model-frame))))

; The served publication and auxiliary exposure/log/auth writers frame the Store.
(defthm fn-owner-retain-sco-note-durable-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-sco-note-durable sequence state)) fn-arena))
  :hints (("Goal" :in-theory
           '(fn-owner-sco-note-durable fn-ost-install-publication fn-owner-retain-livep-of-other-global-put
             mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-sco-note-base-payloads-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-sco-note-base-payloads count state)) fn-arena))
  :hints (("Goal" :in-theory
           '(fn-owner-sco-note-base-payloads fn-ost-install-publication fn-owner-retain-livep-of-other-global-put
             mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-sco-publication-done-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-sco-publication-done next payloads durablep verdict state)) fn-arena))
  :hints (("Goal" :in-theory
           '(fn-owner-sco-publication-done fn-ost-install-publication fn-owner-retain-livep-of-other-global-put
             mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-sco-publication-abandoned-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-sco-publication-abandoned count serial outcome now state)) fn-arena))
  :hints (("Goal" :in-theory
           '(fn-owner-sco-publication-abandoned fn-ost-install-publication fn-owner-retain-livep-of-other-global-put
             mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-transit-log-line-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-transit-log-line id kind reason word detail verdict state)) fn-arena))
  :hints (("Goal" :in-theory
           '(fn-owner-transit-log-line fn-owner-retain-livep-of-other-global-put
             mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-login-gate-buffer-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-login-gate-buffer fn-octets state)) fn-arena))
  :hints (("Goal" :in-theory
           '(fn-owner-login-gate-buffer fn-owner-retain-livep-of-other-global-put
             mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-exposure-install-set-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-exposure-install-set projections state)) fn-arena))
  :hints (("Goal" :in-theory
           '(fn-owner-exposure-install-set fn-owner-retain-livep-of-other-global-put
             mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--)))))

; These Q1 Group A wrappers are :program-only, so have no theorem subject:
; fn-owner-install-profile, fn-owner-posting-configure,
; fn-owner-feed-install-port-result, fn-owner-feed-replay-counted,
; fn-owner-feed-configure, fn-owner-control-outcome, fn-owner-bp-transit-outcome,
; fn-owner-transit-outcome, fn-owner-outcome, fn-owner-tls-established,
; fn-owner-sasl-context, fn-owner-exposure-open, fn-owner-unavailable-line-at,
; fn-owner-resource-unavailable-line-at, fn-owner-output-refusal-line-at,
; fn-owner-declare-group. Their model transitions are not substituted subjects.

; Completed cuts: bodies fixed by CANDIDATES-2.lisp.
; Completed POST cut: approved v1b body.
(defun fn-owner-retain-post-quantum (record budget force-abort fn-arena fn-cat state)
  (declare (xargs :stobjs (fn-arena fn-cat state) :verify-guards nil))
  (let* ((s (fn-owner-store state))
         (row (fn-intern-row-at record (fn-sn-keyring s)
                                (fn-sn-keyring-generation s) (fn-arena-count fn-arena)))
         (carry (fn-prc-refresh (fn-owner-retain-carry state)
                                (fn-node-retention (fn-sn-node s)))))
    (mv-let (word oc) (fn-pout-prepare-article (fn-owner-ocfg state) row budget carry)
      (let* ((state (fn-owner-retain-carry-put carry state))
             (state (fn-owner-install-ocfg oc state)))
        (if (not (equal word :prepared))
            (mv-let (erp answer state) (fn-owner-refuse-reservation fn-arena state)
              (declare (ignore erp)) (mv answer fn-arena state))
          (let ((state (f-put-global 'fn-owner-cat-candidate (cons record row) state)))
            (mv-let (erp may state) (fn-owner-cat-may-seal state)
              (declare (ignore erp))
              (if (or force-abort (not (equal may t)))
                  (mv-let (erp answer state) (fn-owner-known-abort fn-arena state)
                    (declare (ignore erp)) (mv answer fn-arena state))
                (let ((fn-arena (fn-arena-seal-list (fn-record-payload record) fn-arena)))
                  (mv-let (erp answer state) (fn-owner-cat-prepare-sealed fn-arena fn-cat state)
                    (declare (ignore erp)) (mv answer fn-arena state)))))))))))

; Both unchanged statements passed the A22 REPL proof.
; Kept comment-only under the closing scope: no proofs admitted into any book.
#|
(defthm fn-owner-post-quantum-keeps-retain-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep
            (mv-nth 2 (fn-owner-retain-post-quantum record budget force-abort fn-arena fn-cat state))
            (mv-nth 1 (fn-owner-retain-post-quantum record budget force-abort fn-arena fn-cat state))))
  :rule-classes nil)

(defthm fn-owner-retain-quanta-keep-retained-store
  (implies (fn-owner-retain-livep state fn-arena)
    (and (fn-osr-retainedp (fn-owner-store (mv-nth 2 (fn-owner-retain-post-quantum record budget abort fn-arena fn-cat state))))
         (fn-osr-retainedp (fn-owner-store (mv-nth 2 (fn-owner-retain-identity-quantum event fn-arena fn-cat state)))))))
|#

(defun fn-owner-retain-identity-quantum (event fn-arena fn-cat state)
  (declare (xargs :stobjs (fn-arena fn-cat state) :verify-guards nil))
  (mv-let (erp word state) (fn-owner-prepare-identity event fn-arena state)
    (declare (ignore erp))
    (cond ((and (consp word) (equal (car word) :seal))
           (let ((fn-arena (fn-arena-seal-list (cadr word) fn-arena)))
             (mv-let (erp answer state) (fn-owner-cat-prepare-sealed fn-arena fn-cat state)
               (declare (ignore erp)) (mv answer fn-arena state))))
          ((equal word :prepared) (mv word fn-arena state))
          (t (mv-let (erp answer state) (fn-owner-refuse-reservation fn-arena state)
               (declare (ignore erp)) (mv answer fn-arena state))))))

(local
 (defthm fn-owner-retain-update-selectors
   (let ((b (fn-sn-update s files node)))
     (and (equal (fn-sn-keyring b) (fn-sn-keyring s))
          (equal (fn-sn-keyring-generation b) (fn-sn-keyring-generation s))
          (equal (fn-sn-keyring-snapshots b) (fn-sn-keyring-snapshots s))
          (equal (fn-sn-verdicts b) (fn-sn-verdicts s))
          (equal (fn-sn-index b) (fn-sn-index s))
          (equal (fn-sn-event-index b) (fn-sn-event-index s))
          (equal (fn-sn-identity-next b) (fn-sn-identity-next s))))
   :hints (("Goal" :in-theory
            (e/d (fn-sn-update)
                 (fn-sn-make-v6 fn-sn-keyring fn-sn-keyring-generation
                  fn-sn-keyring-snapshots fn-sn-verdicts fn-sn-index
                  fn-sn-event-index fn-sn-identity-next))))))

; The carried identity implementation stages without changing its retained view.
(local
 (defthm fn-owner-retain-ccar-identity-view-frame
   (equal (fn-osr-retained-view (fn-ccar-sn-prepare-identity s e))
          (fn-osr-retained-view s))
   :hints (("Goal" :in-theory
            '(fn-ccar-sn-prepare-identity fn-osr-retained-view
              fn-cstp-sn-update-fields fn-owner-retain-update-selectors fn-pcar-stage-record
              fn-sf-records-of-fn-sf-make-fields-kept car-cons cdr-cons)))))
(local
 (defthm fn-owner-retain-ccar-identity-keeps-retained
   (implies (and (fn-osr-retainedp s)
                 (fn-cst-relation (fn-ccar-sn-prepare-identity s e)))
            (fn-osr-retainedp (fn-ccar-sn-prepare-identity s e)))
   :hints (("Goal"
            :use ((:instance fn-osr-retained-view-connects-full-carry
                             (a s) (b (fn-ccar-sn-prepare-identity s e)))
                  (:instance fn-owner-carried-identity-prepare-preserves-cursor (event e))
                  (:instance fn-cstp-relation-is-statep (st (fn-ccar-sn-prepare-identity s e)))
                  (:instance fn-th-topic-event-is-not-stxe (event e))
                  (:instance fn-th-topic-event-is-not-stxk (event e))
                  (:instance fn-hls-retained-kind4-disjoint-from-other-store-events (event e)))
            :in-theory
            '(fn-owner-retain-ccar-identity-view-frame fn-ccar-sn-prepare-identity
              fn-osr-retainedp fn-osr-livep fn-cstp-relation-is-statep
              fn-sti-livep fn-csi-livep fn-sti-completed-prefixp
              fn-csi-completed-prefixp fn-csi-completion-lastp
              fn-osr-identity-prefixp fn-sn-identity-context
              fn-cstp-sn-update-fields fn-owner-retain-update-selectors fn-pcar-stage-record
              fn-sf-records-of-fn-sf-make-fields-kept fn-sf-scalars-of-fn-sf-make-fields
              fn-sf-completion-phasep member-equal car-cons cdr-cons
              (:e member-equal) (:e equal))))) )

(local
 (defthm fn-owner-retain-pout-identity-keeps-retained
   (implies (and (fn-lgoc-invariantp oc) (fn-osr-retainedp (fn-sbud-oc-store oc)))
            (fn-osr-retainedp
             (fn-sbud-oc-store (mv-nth 1 (fn-pout-prepare-identity oc w h)))))
   :hints (("Goal"
            :use ((:instance fn-pout-store-of-oiis-prepare-identity)
                  (:instance fn-oiis-prepare-identity-preserves-invariant)
                  (:instance fn-lgoc-ocl-relation-cst
                             (oc (fn-oiis-prepare-identity oc w h)))
                  (:instance fn-owner-retain-ccar-identity-keeps-retained
                             (s (fn-sbud-oc-store oc))
                             (e (fn-oii-identity-row w (fn-sn-keyring (fn-sbud-oc-store oc))
                                                    (fn-sn-keyring-generation (fn-sbud-oc-store oc)) h))))
            :in-theory
            '(fn-pout-prepare-identity fn-lgoc-invariantp fn-sbud-oc-store
              mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--))))))

(local
 (defthm fn-owner-retain-identity-prepare-cut
   (let* ((out (fn-owner-prepare-identity event fn-arena state))
          (next (mv-nth 2 out)) (word (mv-nth 1 out)))
     (implies (fn-owner-retain-livep state fn-arena)
              (and (fn-owner-retain-statep next)
                   (fn-osr-retainedp (fn-owner-store next))
                   (fn-rfcl-okp (fn-owner-store next)
                     (if (and (consp word) (equal (car word) :seal))
                         (fn-arena-seal-list (cadr word) fn-arena)
                       fn-arena)))))
   :hints (("Goal"
            :use ((:instance fn-pout-identity-refusal-kind-is-a-refusal (oc (fn-owner-ocfg state)) (w event) (h (fn-arena-count fn-arena)))
                  fn-owner-prepare-identity-preserves-retain-state
                  fn-owner-retain-statep-implies-lgoc fn-owner-retain-statep-implies-entry-guard
                  (:instance fn-rfcl-prepare-identity-keeps-okp
                             (oc (fn-owner-ocfg state)) (w event))
                  (:instance fn-owner-retain-pout-identity-keeps-retained
                             (oc (fn-owner-ocfg state)) (w event) (h (fn-arena-count fn-arena))))
            :in-theory
            '(fn-owner-retain-livep fn-owner-prepare-identity fn-pout-prepare-identity member-equal (:e equal)
              fn-irc-pout-prepare-identity-of-refresh-is-pout
              fn-owner-retain-store-projection fn-owner-ocfg-of-install-ocfg
              fn-owner-ocfg-of-retain-carry-put fn-owner-ocfg-of-other-global-put
              mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--))))))

(local
 (defthm fn-owner-retain-sn-refuse-keeps-retained
   (implies (and (fn-osr-retainedp s)
                 (fn-cst-relation (fn-sn-refuse-reservation s txid)))
            (fn-osr-retainedp (fn-sn-refuse-reservation s txid)))
   :hints (("Goal"
            :use ((:instance fn-osr-retained-view-connects-full-carry
                             (a s) (b (fn-sn-refuse-reservation s txid)))
                  (:instance fn-osr-store-step-preserves-independent-live
                             (event (list :refuse-reservation txid))))
            :in-theory
            '(fn-osr-retainedp fn-osr-livep fn-osr-independent-livep
              fn-snrt-step fn-osr-preparations-keep-retained-view
              fn-sn-refuse-reservation fn-cstp-sn-update-fields
              member-equal car-cons cdr-cons (:e equal) (:e member-equal))))))
(local
 (defthm fn-owner-retain-sn-refuse-rfcl-rows-frame
   (equal (fn-rfcl-rows (fn-sn-refuse-reservation s txid)) (fn-rfcl-rows s))
   :hints (("Goal" :in-theory
            '(fn-sn-refuse-reservation fn-sn-refuse-reservation-enabledp
              fn-sf-refuse-reservation fn-rfcl-rows fn-rfcl-pending-phasep
              fn-cstp-sn-update-fields fn-sf-records-of-fn-sf-make-fields-kept
              fn-sf-scalars-of-fn-sf-make-fields
              member-equal car-cons cdr-cons (:e equal) (:e member-equal))))))
(local
 (defthm fn-owner-retain-refuse-model-cut
   (let* ((out (fn-pout-refuse-reservation oc fn-arena))
          (s (fn-sbud-oc-store oc)) (next (fn-sbud-oc-store (mv-nth 1 out))))
     (implies (and (fn-lgoc-invariantp oc) (fn-osr-retainedp s) (fn-rfcl-okp s fn-arena))
              (and (fn-osr-retainedp next) (fn-rfcl-okp next fn-arena))))
   :hints (("Goal"
            :use (fn-pout-refuse-reservation-preserves-owner-invariant
                  (:instance fn-lgoc-ocl-relation-cst
                             (oc (mv-nth 1 (fn-pout-refuse-reservation oc fn-arena))))
                  (:instance fn-pout-store-of-store-step
                             (ev (list :refuse-reservation
                                       (1- (fn-sf-frontier (fn-sn-files (fn-sbud-oc-store oc)))))))
                  (:instance fn-owner-retain-sn-refuse-keeps-retained
                             (s (fn-sbud-oc-store oc))
                             (txid (1- (fn-sf-frontier (fn-sn-files (fn-sbud-oc-store oc)))))))
            :in-theory
            '(fn-pout-refuse-reservation fn-lgoc-invariantp fn-sbud-oc-store fn-snrt-step
              fn-rfcl-okp fn-owner-retain-sn-refuse-rfcl-rows-frame
              mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--))))))
(defthm fn-owner-retain-refuse-reservation-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep
            (mv-nth 2 (fn-owner-refuse-reservation fn-arena state)) fn-arena))
  :hints (("Goal"
           :use (fn-owner-refuse-reservation-preserves-retain-state
                 fn-owner-retain-statep-implies-lgoc
                 (:instance fn-owner-retain-refuse-model-cut (oc (fn-owner-ocfg state))))
           :in-theory
           '(fn-owner-retain-livep fn-owner-refuse-reservation
             fn-owner-retain-store-projection fn-owner-ocfg-of-install-ocfg
             fn-owner-ocfg-of-other-global-put
             mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-identity-quantum-keeps-retain-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep
            (mv-nth 2 (fn-owner-retain-identity-quantum event fn-arena fn-cat state))
            (mv-nth 1 (fn-owner-retain-identity-quantum event fn-arena fn-cat state))))
  :rule-classes nil
  :hints (("Goal" :use (fn-owner-retain-identity-prepare-cut)
           :in-theory
           '(fn-owner-retain-identity-quantum fn-owner-retain-livep
             fn-owner-retain-refuse-reservation-keeps-live
             fn-owner-retain-cat-prepare-sealed-keeps-live
             mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--)))))

(in-theory (disable fn-owner-retain-livep fn-owner-retain-identity-quantum))
