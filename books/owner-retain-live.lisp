; K1 live owner retention: completed-cut invariant and host writer frames.
(in-package "ACL2")
; Attachment headers precede the shared arena predicate. K1 supports the
; existing served row; there is no second retained-state carried row.
(include-book "payload-arena-attach")
(include-book "history-paged-attach")
(include-book "catalog-paged-attach")
(include-book "owner-retain-carried")
(include-book "owner-retain-livep")
(include-book "owner-retain-frame")
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

; The establishment in implication form, without the :fault case: the
; recovering install makes the retained state hold (the form premise_audit
; reads as an establishment; the row below cites the :ok form).
(defthm fn-owner-retain-install-recovering-establishes-retained-state
  (implies (and (fn-lgoc-invariantp oc)
                (fn-osr-retainedp (fn-sbud-oc-store oc))
                (equal (mv-nth 1 (fn-owner-install-extended
                                   oc extended key fn-arena fn-cat fn-hist state))
                       :recovering))
           (fn-owner-retain-retained-statep
            (mv-nth 5 (fn-owner-install-extended
                        oc extended key fn-arena fn-cat fn-hist state))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-owner-install-extended-establishes-when-recovering
                 fn-owner-install-extended-word-when-refused)
           :in-theory '(fn-owner-retain-retained-statep
                        fn-owner-retain-install-store-when-recovering))))

; Retained input of the cold installer, discharged at its existing producers.
(defthm fn-owner-retain-install-establishes-retained-state
  (implies (or (equal oc :fault)
               (and (fn-lgoc-invariantp oc)
                    (fn-osr-retainedp (fn-sbud-oc-store oc))))
           (if (equal (mv-nth 1 (fn-owner-install-extended
                                  oc extended key fn-arena fn-cat fn-hist state))
                      :recovering)
               (fn-owner-retain-retained-statep
                (mv-nth 5 (fn-owner-install-extended
                            oc extended key fn-arena fn-cat fn-hist state)))
             t))
  :hints (("Goal"
           :use (fn-owner-install-extended-establishes-when-recovering
                 fn-owner-install-extended-word-when-refused)
           :in-theory '(fn-owner-retain-retained-statep
                        fn-owner-retain-install-store-when-recovering))))

(defthm fn-owner-retain-recovery-produces-retained-input
  (implies (fn-assume-capture-extensionp extended configs)
           (let ((oc (fn-ock-recover-extended extended configs frontier max-conns)))
             (or (equal oc :fault)
                 (and (fn-lgoc-invariantp oc)
                      (fn-osr-retainedp (fn-sbud-oc-store oc))))))
  :hints (("Goal"
           :use (fn-owner-recover-extended-produces-invariant
                 (:instance fn-assume-capture-extension-is-one (e extended))
                 (:instance fn-owner-recovery-establishes-retained-store
                            (prefix (fn-assume-capture-prefix extended configs))
                            (suffix (fn-assume-capture-suffix extended configs))))
           :in-theory (theory 'minimal-theory))))

(defthm fn-owner-retain-store-open-produces-retained-input
  (implies (fn-assume-store-open-pairp replayed opened)
           (let ((oc (fn-ock-install replayed opened max-conns)))
             (or (equal oc :fault)
                 (and (fn-lgoc-invariantp oc)
                      (fn-osr-retainedp (fn-sbud-oc-store oc))))))
  :hints (("Goal"
           :use (fn-assume-store-open-pair-is-an-open
                 (:instance fn-ock-install-of-store-open-by-definition
                            (e (fn-assume-store-open-e replayed opened))
                            (configs (fn-assume-store-open-configs replayed opened))
                            (frontier (fn-assume-store-open-frontier replayed opened)))
                 (:instance fn-owner-retain-recovery-produces-retained-input
                            (extended (fn-assume-store-open-e replayed opened))
                            (configs (fn-assume-store-open-configs replayed opened))
                            (frontier (fn-assume-store-open-frontier replayed opened))))
           :in-theory (theory 'minimal-theory))))

(defthm fn-owner-retain-identity-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep
            (mv-nth 2 (fn-owner-prepare-identity event fn-arena state))))
  :hints (("Goal"
           :use (fn-owner-prepare-identity-preserves-retain-state
                 fn-owner-retain-statep-implies-lgoc
                 (:instance fn-owner-retain-pout-identity-keeps-retained
                            (oc (fn-owner-ocfg state)) (w event)
                            (h (fn-arena-count fn-arena))))
           :in-theory '(fn-owner-retain-retained-statep fn-owner-retain-statep
                        fn-owner-prepare-identity fn-pout-prepare-identity
                        fn-irc-pout-prepare-identity-of-refresh-is-pout
                        fn-owner-retain-store-projection
                        fn-owner-ocfg-of-install-ocfg
                        fn-owner-ocfg-of-retain-carry-put
                        fn-owner-ocfg-of-other-global-put
                        mv-nth nth zp endp car-cons cdr-cons (:e equal)
                        (:e zp) (:e binary-+) (:e unary--)))))

(local
 (defthm fn-owner-retain-cpe-not-topic
   (implies (fn-cpe-eventp e) (not (fn-th-topic-eventp e)))
   :hints (("Goal" :use ((:instance fn-th-topic-event-has-topic-tag (event e)))
            :in-theory '(fn-cpe-eventp fn-cp-nth nth zp car-cons cdr-cons
                         member-equal (:e member-equal) (:e equal) (:e zp)
                         (:e binary-+) (:e unary--))))))
(local
 (defthm fn-owner-retain-pdc-consumer-view-frame
   (equal (fn-osr-retained-view (fn-pdc-sn-prepare-consumer s e)) (fn-osr-retained-view s))
   :hints (("Goal" :in-theory '(fn-osr-retained-view fn-pdc-sn-prepare-consumer
              fn-cstp-sn-update-fields fn-owner-retain-update-selectors
              fn-pcar-stage-record fn-sf-records-of-fn-sf-make-fields-kept
              car-cons cdr-cons)))))
(local
 (defthm fn-owner-retain-pdc-consumer-keeps-cursor
   (implies (fn-sn-identity-sequencep s)
            (fn-sn-identity-sequencep (fn-pdc-sn-prepare-consumer s e)))
   :hints (("Goal" :in-theory
     (union-theories (theory 'minimal-theory)
       '(fn-pdc-sn-prepare-consumer fn-sn-identity-sequencep fn-pcar-stage-record
         fn-cstp-sn-update-fields fn-owner-retain-update-selectors
         fn-sf-records-of-fn-sf-make-fields-kept fn-sf-scalars-of-fn-sf-make-fields
         fn-sf-completion-phasep natp member-equal car-cons cdr-cons
         (:e member-equal) (:e equal)))))))
(local
 (defthm fn-owner-retain-pdc-consumer-keeps-retained
   (implies (and (fn-osr-retainedp s) (fn-cst-relation (fn-pdc-sn-prepare-consumer s e)))
            (fn-osr-retainedp (fn-pdc-sn-prepare-consumer s e)))
   :hints (("Goal"
            :use (fn-owner-retain-pdc-consumer-keeps-cursor
                  fn-owner-retain-cpe-not-topic
                  (:instance fn-osr-retained-view-connects-full-carry
                       (a s) (b (fn-pdc-sn-prepare-consumer s e)))
                  (:instance fn-cstp-relation-is-statep (st (fn-pdc-sn-prepare-consumer s e))))
            :in-theory '(fn-owner-retain-pdc-consumer-view-frame fn-pdc-sn-prepare-consumer
              fn-osr-retainedp fn-osr-livep fn-sti-livep fn-csi-livep
              fn-sti-completed-prefixp fn-csi-completed-prefixp fn-csi-completion-lastp
              fn-osr-identity-prefixp fn-sn-identity-context
              fn-cstp-sn-update-fields fn-owner-retain-update-selectors fn-pcar-stage-record
              fn-sf-records-of-fn-sf-make-fields-kept fn-sf-scalars-of-fn-sf-make-fields
              fn-sf-completion-phasep fn-ccar-cpe-projection-step-is-cpe-projection-step
              member-equal car-cons cdr-cons
              (:e member-equal) (:e equal))))) )
(local
 (defthm fn-owner-retain-pdc-pout-consumer-keeps-retained
   (implies (and (fn-lgoc-invariantp oc) (fn-osr-retainedp (fn-sbud-oc-store oc)))
            (fn-osr-retainedp (fn-sbud-oc-store
              (mv-nth 1 (fn-pdc-pout-prepare-consumer oc e)))))
   :hints (("Goal"
            :use ((:instance fn-pdc-store-of-owner-prepares)
                  (:instance fn-pdc-ocfg-prepare-consumer-preserves-invariant)
                  (:instance fn-lgoc-ocl-relation-cst (oc (fn-pdc-ocfg-prepare-consumer oc e)))
                  (:instance fn-owner-retain-pdc-consumer-keeps-retained
                       (s (fn-sbud-oc-store oc))))
            :in-theory '(fn-pdc-pout-prepare-consumer fn-lgoc-invariantp
              fn-sbud-oc-store mv-nth nth zp endp car-cons cdr-cons
              (:e zp) (:e binary-+) (:e unary--))))) )
(defthm fn-owner-retain-consumer-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep
            (mv-nth 2 (fn-owner-prepare-consumer event fn-arena state))))
  :hints (("Goal"
           :use (fn-owner-prepare-consumer-preserves-retain-state
                 fn-owner-retain-statep-implies-lgoc
                 (:instance fn-owner-retain-pdc-pout-consumer-keeps-retained
                      (oc (fn-owner-ocfg state)) (e event)))
           :in-theory '(fn-owner-retain-retained-statep fn-owner-prepare-consumer
             fn-owner-retain-store-projection fn-owner-ocfg-of-install-ocfg
             mv-nth nth zp endp car-cons cdr-cons
             (:e zp) (:e binary-+) (:e unary--)))))

(local
 (defthm fn-owner-retain-pdc-topic-view-frame
   (equal (fn-osr-retained-view (fn-pdc-sn-prepare-topic s e)) (fn-osr-retained-view s))
   :hints (("Goal" :in-theory '(fn-osr-retained-view fn-pdc-sn-prepare-topic
              fn-cstp-sn-update-fields fn-owner-retain-update-selectors
              fn-pcar-stage-record fn-sf-records-of-fn-sf-make-fields-kept
              car-cons cdr-cons)))))
(local
 (defthm fn-owner-retain-pdc-topic-keeps-cursor
   (implies (fn-sn-identity-sequencep s)
            (fn-sn-identity-sequencep (fn-pdc-sn-prepare-topic s e)))
   :hints (("Goal" :in-theory
     (union-theories (theory 'minimal-theory)
       '(fn-pdc-sn-prepare-topic fn-sn-identity-sequencep fn-pcar-stage-record
         fn-cstp-sn-update-fields fn-owner-retain-update-selectors
         fn-sf-records-of-fn-sf-make-fields-kept fn-sf-scalars-of-fn-sf-make-fields
         fn-sf-completion-phasep natp member-equal car-cons cdr-cons
         (:e member-equal) (:e equal)))))))
(local
 (defthm fn-owner-retain-pdc-topic-keeps-retained
   (implies (and (fn-osr-retainedp s) (fn-cst-relation (fn-pdc-sn-prepare-topic s e)))
            (fn-osr-retainedp (fn-pdc-sn-prepare-topic s e)))
   :hints (("Goal"
            :use (fn-owner-retain-pdc-topic-keeps-cursor
                  fn-owner-retain-cpe-not-topic
                  (:instance fn-osr-retained-view-connects-full-carry
                       (a s) (b (fn-pdc-sn-prepare-topic s e)))
                  (:instance fn-cstp-relation-is-statep (st (fn-pdc-sn-prepare-topic s e))))
            :in-theory '(fn-owner-retain-pdc-topic-view-frame fn-pdc-sn-prepare-topic
              fn-osr-retainedp fn-osr-livep fn-sti-livep fn-csi-livep
              fn-sti-completed-prefixp fn-csi-completed-prefixp fn-csi-completion-lastp
              fn-osr-identity-prefixp fn-sn-identity-context
              fn-cstp-sn-update-fields fn-owner-retain-update-selectors fn-pcar-stage-record
              fn-sf-records-of-fn-sf-make-fields-kept fn-sf-scalars-of-fn-sf-make-fields
              fn-sf-completion-phasep fn-ccar-cpe-projection-step-is-cpe-projection-step
              member-equal car-cons cdr-cons
              (:e member-equal) (:e equal))))) )
(local
 (defthm fn-owner-retain-pdc-pout-topic-keeps-retained
   (implies (and (fn-lgoc-invariantp oc) (fn-osr-retainedp (fn-sbud-oc-store oc)))
            (fn-osr-retainedp (fn-sbud-oc-store
              (mv-nth 1 (fn-pdc-pout-prepare-topic oc e)))))
   :hints (("Goal"
            :use ((:instance fn-pdc-store-of-owner-prepares)
                  (:instance fn-pdc-psrv-prepare-topic-preserves-invariant)
                  (:instance fn-lgoc-ocl-relation-cst (oc (fn-pdc-psrv-prepare-topic oc e)))
                  (:instance fn-owner-retain-pdc-topic-keeps-retained
                       (s (fn-sbud-oc-store oc))))
            :in-theory '(fn-pdc-pout-prepare-topic fn-lgoc-invariantp
              fn-sbud-oc-store mv-nth nth zp endp car-cons cdr-cons
              (:e zp) (:e binary-+) (:e unary--))))) )
(defthm fn-owner-retain-topic-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep
            (mv-nth 2 (fn-owner-prepare-topic event fn-arena state))))
  :hints (("Goal"
           :use (fn-owner-prepare-topic-preserves-retain-state
                 fn-owner-retain-statep-implies-lgoc
                 (:instance fn-owner-retain-pdc-pout-topic-keeps-retained
                      (oc (fn-owner-ocfg state)) (e event)))
           :in-theory '(fn-owner-retain-retained-statep fn-owner-prepare-topic
             fn-owner-retain-store-projection fn-owner-ocfg-of-install-ocfg
             mv-nth nth zp endp car-cons cdr-cons
             (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-retained-statep-implies-entry-guard
  (implies (fn-owner-retain-retained-statep state)
           (and (boundp-global 'fn-owner state)
                (fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg state)))
                (fn-prc-carryp (fn-owner-retain-carry state))))
  :hints (("Goal" :use fn-owner-retain-statep-implies-entry-guard
           :in-theory '(fn-owner-retain-retained-statep))))

; As in the existing pilot, the installer input premise is discharged at
; both actual recovery producers under their existing named assumptions.
; This model-world row is followed by host-world owed enumeration below.



(defthm fn-owner-retain-retained-statep-of-other-global-put
  (implies (and (not (equal key 'fn-owner))
                (not (equal key 'fn-owner-retain-carry)))
           (equal (fn-owner-retain-retained-statep (f-put-global key value state))
                  (fn-owner-retain-retained-statep state)))
  :hints (("Goal" :in-theory '(fn-owner-retain-retained-statep
              fn-orh-retain-statep-of-other-global-put fn-owner-store-is-configured-store-by-definition fn-sbud-oc-store
              fn-owner-ocfg-of-other-global-put))))
(defthm fn-owner-retain-retained-statep-of-install-ocfg
  (implies (and (fn-owner-retain-retained-statep state)
                (fn-lgoc-invariantp oc) (fn-osr-retainedp (fn-sbud-oc-store oc)))
           (fn-owner-retain-retained-statep (fn-owner-install-ocfg oc state)))
  :hints (("Goal" :in-theory '(fn-owner-retain-retained-statep
              fn-orh-retain-statep-of-install-ocfg fn-owner-store-is-configured-store-by-definition fn-sbud-oc-store
              fn-owner-ocfg-of-install-ocfg))))




(include-book "../host/owner-host")
(include-book "../host/owner-retain-host")










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



; The carried identity implementation stages without changing its retained view.







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

; POST completed-cut support, replayed from a22-accepted-post-events.log.
; Retain the complete recorded support, including implicit rewrite dependencies.
(local
 (DEFTHM RFCL-LV0
  (IMPLIES (AND (FN-RFCL-OKP S FN-ARENA)
                (NOT (FN-RFCL-PENDING-PHASEP (FN-SF-PHASE (FN-SN-FILES S)))))
           (FN-ORCR-FOLD-CONTEXTS-OKP (FN-SF-RECORDS (FN-SN-FILES S))
                                      (FN-STXK-INITIAL-CONTEXT 0)
                                      (FN-ARENA-COUNT FN-ARENA)
                                      FN-ARENA))
  :HINTS (("Goal" :IN-THEORY '(FN-RFCL-OKP FN-RFCL-ROWS)))))

(local
 (DEFTHM RFCL-LV1
   (FN-RFCL-OKP (FN-SN-INITIAL GROUPS CAPACITY)
                FN-ARENA)
   :HINTS (("Goal" :IN-THEORY (ENABLE FN-RFCL-OKP
                                      FN-RFCL-ROWS FN-RFCL-PENDING-PHASEP
                                      FN-SN-INITIAL FN-SN-MAKE-V2
                                      FN-SN-FILES FN-STORE-EVENT-NTH
                                      FN-SF-INITIAL-STATE)))))

(local
 (DEFTHM RFCL-HANDLES-APPEND
   (EQUAL (FN-ROWS-HANDLES-INP (APPEND A B)
                               FN-ARENA)
          (AND (FN-ROWS-HANDLES-INP A FN-ARENA)
               (FN-ROWS-HANDLES-INP B FN-ARENA)))
   :HINTS
   (("Goal" :INDUCT (APPEND A B)
            :IN-THEORY (E/D (FN-ROWS-HANDLES-INP APPEND)
                            (FN-HELD-P FN-HSTXA-P FN-ROW-HANDLE-INP))))))

(local
 (DEFUN RFCL-AFTER (ROWS ID H)
   (DECLARE (XARGS :VERIFY-GUARDS NIL))
   (IF (ATOM ROWS)
       (MV ID H)
     (LET* ((W (CAR ROWS))
            (SEED (FN-SSR-SEED ID))
            (ROW (IF (FN-RECORD-P W)
                     (FN-INTERN-ROW-AT W (FN-SSR-AT 1 SEED)
                                       (FN-SSR-AT 2 SEED)
                                       H)
                   W)))
       (RFCL-AFTER (CDR ROWS)
                   (FN-REPLAY-IDENTITY-LOOP (LIST ROW) ID)
                   (IF (FN-RECORD-P W) (+ 1 H) H))))))

(local
 (DEFTHM RFCL-FOLD-APPEND
   (EQUAL (FN-ORCR-FOLD-CONTEXTS-OKP (APPEND A B)
                                     ID H FN-ARENA)
          (AND (FN-ORCR-FOLD-CONTEXTS-OKP A ID H FN-ARENA)
               (FN-ORCR-FOLD-CONTEXTS-OKP B (MV-NTH 0 (RFCL-AFTER A ID H))
                                          (MV-NTH 1 (RFCL-AFTER A ID H))
                                          FN-ARENA)))
   :HINTS
   (("Goal"
         :INDUCT (RFCL-AFTER A ID H)
         :IN-THEORY
         (UNION-THEORIES '(RFCL-AFTER FN-ORCR-FOLD-CONTEXTS-OKP
                                      APPEND (:INDUCTION RFCL-AFTER)
                                      NATP
                                      NOT CAR-CONS CDR-CONS CONS-EQUAL MV-NTH
                                      NTH ZP (:EXECUTABLE-COUNTERPART ZP)
                                      (:EXECUTABLE-COUNTERPART BINARY-+)
                                      (:EXECUTABLE-COUNTERPART UNARY--)
                                      (:EXECUTABLE-COUNTERPART MEMBER-EQUAL)
                                      MEMBER-EQUAL)
                         (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM RFCL-HANDLES-SEAL
  (IMPLIES (FN-ROWS-HANDLES-INP ROWS FN-ARENA)
           (FN-ROWS-HANDLES-INP ROWS (FN-ARENA-SEAL-LIST P FN-ARENA)))
  :HINTS
  (("Goal" :INDUCT (FN-ROWS-HANDLES-INP ROWS FN-ARENA)
           :IN-THEORY (E/D (FN-ROWS-HANDLES-INP FN-ROW-HANDLE-INP)
                           (FN-HELD-P FN-HSTXA-P FN-ARENA-SEAL-LIST-IS-APPEND
                                      FN-ARENA-COUNT-IS-LEN))))))

(local
 (DEFTHM RFCL-FOLD-SEAL
  (IMPLIES (AND (FN-ROWS-HANDLES-INP ROWS FN-ARENA)
                (FN-ORCR-FOLD-CONTEXTS-OKP ROWS ID H FN-ARENA))
           (FN-ORCR-FOLD-CONTEXTS-OKP ROWS
                                      ID H (FN-ARENA-SEAL-LIST P FN-ARENA)))
  :HINTS
  (("Goal"
     :INDUCT (FN-ORCR-FOLD-CONTEXTS-OKP ROWS ID H FN-ARENA)
     :IN-THEORY
     (UNION-THEORIES
          '(FN-ORCR-FOLD-CONTEXTS-OKP FN-ROWS-HANDLES-INP
                                      FN-ROW-HANDLE-INP FN-ROW-BYTES
                                      FN-ORCR-RETAINED-P FN-ORCR-HELD-PART
                                      FN-ARENA-SEAL-KEEPS-SEALED
                                      FN-ARENA-SEAL-COUNT
                                      (:TYPE-PRESCRIPTION FN-ARENA-COUNT)
                                      FN-CSTP-HELD-KIND-FACTS
                                      FN-HSTXA-IS-NOT-HELD NATP
                                      NOT CAR-CONS CDR-CONS CONS-EQUAL MV-NTH
                                      NTH ZP (:EXECUTABLE-COUNTERPART ZP)
                                      (:EXECUTABLE-COUNTERPART BINARY-+)
                                      (:EXECUTABLE-COUNTERPART UNARY--)
                                      (:EXECUTABLE-COUNTERPART MEMBER-EQUAL)
                                      MEMBER-EQUAL)
          (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM RFCL-LV5
  (IMPLIES (FN-RFCL-OKP S FN-ARENA)
           (FN-RFCL-OKP S (FN-ARENA-SEAL-LIST P FN-ARENA)))
  :HINTS
  (("Goal"
       :IN-THEORY (E/D (FN-RFCL-OKP)
                       (FN-RFCL-ROWS FN-ORCR-FOLD-CONTEXTS-OKP
                                     FN-ROWS-HANDLES-INP))
       :USE ((:INSTANCE FN-RFC-FOLD-CONTEXTS-OKP-ANY-HANDLE
                        (ROWS (FN-RFCL-ROWS S))
                        (ID (FN-STXK-INITIAL-CONTEXT 0))
                        (H1 (FN-ARENA-COUNT (FN-ARENA-SEAL-LIST P FN-ARENA)))
                        (H2 (FN-ARENA-COUNT FN-ARENA))
                        (FN-ARENA (FN-ARENA-SEAL-LIST P FN-ARENA))))))))

(local
 (DEFTHM RFCL-EVENT-NONHELD
   (IMPLIES (OR (FN-STORE-RETENTION-EVENT-P EVENT)
                (FN-CPE-EVENTP EVENT)
                (FN-TH-TOPIC-EVENTP EVENT))
            (NOT (FN-ORCR-RETAINED-P EVENT)))
   :HINTS
   (("Goal" :USE ((:INSTANCE FN-HELD-IS-NO-WIRE-EVENT (X EVENT))
                  FN-HLS-RETAINED-KIND4-DISJOINT-FROM-OTHER-STORE-EVENTS)
            :IN-THEORY '(FN-ORCR-RETAINED-P)))))

(local
 (DEFTHM RFCL-NONHELD-APPEND
  (IMPLIES (AND (NOT (FN-ORCR-RETAINED-P EVENT))
                (FN-ROWS-HANDLES-INP ROWS FN-ARENA)
                (FN-ORCR-FOLD-CONTEXTS-OKP ROWS ID H FN-ARENA))
           (AND (FN-ROWS-HANDLES-INP (APPEND ROWS (LIST EVENT))
                                     FN-ARENA)
                (FN-ORCR-FOLD-CONTEXTS-OKP (APPEND ROWS (LIST EVENT))
                                           ID H FN-ARENA)))
  :HINTS
  (("Goal"
      :IN-THEORY (E/D (FN-ROWS-HANDLES-INP FN-ORCR-RETAINED-P)
                      (FN-HELD-P FN-HSTXA-P FN-RECORD-P
                                 FN-INTERN-ROW-AT FN-SSR-SEED FN-SSR-AT
                                 FN-ROW-BYTES FN-HELD-CONTEXT-OF
                                 FN-REPLAY-IDENTITY-LOOP))
      :EXPAND ((:FREE (CTX COUNT)
                      (FN-ORCR-FOLD-CONTEXTS-OKP (LIST EVENT)
                                                 CTX COUNT FN-ARENA))
               (:FREE (CTX COUNT)
                      (FN-ORCR-FOLD-CONTEXTS-OKP NIL CTX COUNT FN-ARENA)))))))

(local
 (DEFTHM RFCL-STAGE-NONHELD
  (IMPLIES (AND (FN-RFCL-OKP S FN-ARENA)
                (EQUAL (FN-SF-PHASE (FN-SN-FILES S))
                       :RESERVED)
                (NOT (FN-ORCR-RETAINED-P EVENT)))
           (FN-RFCL-OKP (FN-SN-UPDATE S
                                      (FN-PCAR-STAGE-RECORD (FN-SN-FILES S)
                                                            EVENT)
                                      NODE)
                        FN-ARENA))
  :HINTS
  (("Goal"
        :IN-THEORY
        (UNION-THEORIES '(FN-RFCL-OKP FN-RFCL-ROWS FN-RFCL-PENDING-PHASEP
                                      FN-PCAR-STAGE-RECORD
                                      FN-SN-FILES-OF-FN-SN-UPDATE
                                      FN-SF-SCALARS-OF-FN-SF-MAKE-FIELDS
                                      FN-SF-RECORDS-OF-FN-SF-MAKE-FIELDS-KEPT
                                      RFCL-NONHELD-APPEND
                                      RFCL-HANDLES-APPEND RFCL-FOLD-APPEND
                                      (:E FN-RFCL-PENDING-PHASEP)
                                      (:E MEMBER-EQUAL))
                        (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM RFCL-LV4-RETENTION
  (IMPLIES (FN-RFCL-OKP S FN-ARENA)
           (FN-RFCL-OKP (FN-PDC-SN-PREPARE-RETENTION S EVENT)
                        FN-ARENA))
  :HINTS
  (("Goal"
    :IN-THEORY
    (UNION-THEORIES
         '(FN-PDC-SN-PREPARE-RETENTION RFCL-STAGE-NONHELD RFCL-EVENT-NONHELD)
         (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM RFCL-LV4-CONSUMER
  (IMPLIES (FN-RFCL-OKP S FN-ARENA)
           (FN-RFCL-OKP (FN-PDC-SN-PREPARE-CONSUMER S EVENT)
                        FN-ARENA))
  :HINTS
  (("Goal"
     :IN-THEORY
     (UNION-THEORIES
          '(FN-PDC-SN-PREPARE-CONSUMER RFCL-STAGE-NONHELD RFCL-EVENT-NONHELD)
          (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM RFCL-LV4-TOPIC
  (IMPLIES (FN-RFCL-OKP S FN-ARENA)
           (FN-RFCL-OKP (FN-PDC-SN-PREPARE-TOPIC S EVENT)
                        FN-ARENA))
  :HINTS
  (("Goal"
        :IN-THEORY
        (UNION-THEORIES
             '(FN-PDC-SN-PREPARE-TOPIC RFCL-STAGE-NONHELD RFCL-EVENT-NONHELD)
             (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFUN RFCL-FILE-ROWS (F)
   (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
   (IF (FN-RFCL-PENDING-PHASEP (FN-SF-PHASE F))
       (APPEND (FN-SF-RECORDS F)
               (LIST (FN-SF-RECORD-CANDIDATE F)))
     (FN-SF-RECORDS F))))

(local
 (DEFUN RFCL-FOK (F H FN-ARENA)
   (DECLARE (XARGS :STOBJS FN-ARENA
                   :VERIFY-GUARDS NIL))
   (AND (FN-ROWS-HANDLES-INP (RFCL-FILE-ROWS F)
                             FN-ARENA)
        (FN-ORCR-FOLD-CONTEXTS-OKP (RFCL-FILE-ROWS F)
                                   (FN-STXK-INITIAL-CONTEXT 0)
                                   H FN-ARENA))))

(local
 (DEFTHM RFCL-OKP-IS-FOK
   (EQUAL (FN-RFCL-OKP S FN-ARENA)
          (RFCL-FOK (FN-SN-FILES S)
                    (FN-ARENA-COUNT FN-ARENA)
                    FN-ARENA))
   :HINTS
   (("Goal" :IN-THEORY '(FN-RFCL-OKP RFCL-FOK FN-RFCL-ROWS RFCL-FILE-ROWS)))))

(local
 (DEFTHM RFCL-FOK-HAS-RECORDS
   (IMPLIES (RFCL-FOK F H FN-ARENA)
            (AND (FN-ROWS-HANDLES-INP (FN-SF-RECORDS F)
                                      FN-ARENA)
                 (FN-ORCR-FOLD-CONTEXTS-OKP (FN-SF-RECORDS F)
                                            (FN-STXK-INITIAL-CONTEXT 0)
                                            H FN-ARENA)))
   :HINTS
   (("Goal"
         :IN-THEORY (E/D (RFCL-FOK RFCL-FILE-ROWS)
                         (FN-ROWS-HANDLES-INP FN-ORCR-FOLD-CONTEXTS-OKP))))))

(local
 (DEFTHM RFCL-FOK-FILE-STEP
  (IMPLIES (RFCL-FOK F H FN-ARENA)
           (RFCL-FOK (FN-SN-FILE-STEP F OPERATION RESULT)
                     H FN-ARENA))
  :HINTS
  (("Goal" :IN-THEORY
           (UNION-THEORIES '(RFCL-FOK RFCL-FILE-ROWS FN-RFCL-PENDING-PHASEP
                                      FN-SN-FILE-STEP FN-SF-START-FRONTIER
                                      FN-SF-FRONTIER-FILE-RESULT
                                      FN-SF-FRONTIER-REPLACE-RESULT
                                      FN-SF-FRONTIER-DIR-RESULT
                                      FN-SF-RECORD-FILE-RESULT
                                      FN-SF-RECORD-LINK-RESULT
                                      FN-SF-RECORD-DIR-RESULT
                                      FN-SF-RECOVERY-BARRIER
                                      FN-SF-SCALARS-OF-FN-SF-MAKE-FIELDS
                                      FN-SF-RECORDS-OF-FN-SF-MAKE-FIELDS-KEPT
                                      FN-SF-RECORDS-OF-FN-SF-MAKE-FIELDS-SNOC
                                      RFCL-HANDLES-APPEND RFCL-FOLD-APPEND
                                      RFCL-FOK-HAS-RECORDS NATP
                                      NOT CAR-CONS CDR-CONS CONS-EQUAL MV-NTH
                                      NTH ZP (:EXECUTABLE-COUNTERPART ZP)
                                      (:EXECUTABLE-COUNTERPART BINARY-+)
                                      (:EXECUTABLE-COUNTERPART UNARY--)
                                      (:EXECUTABLE-COUNTERPART MEMBER-EQUAL)
                                      MEMBER-EQUAL)
                           (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM RFCL-LV4-IO
  (IMPLIES (AND (FN-SN-STATEP S)
                (FN-RFCL-OKP S FN-ARENA))
           (FN-RFCL-OKP (FN-SN-IO S OPERATION RESULT)
                        FN-ARENA))
  :HINTS
  (("Goal"
       :IN-THEORY
       (UNION-THEORIES '(RFCL-OKP-IS-FOK FN-SN-IO FN-SN-FILES-OF-FN-SN-UPDATE
                                         RFCL-FOK-FILE-STEP)
                       (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM RFCL-FOK-CRASH
  (IMPLIES (RFCL-FOK F H FN-ARENA)
           (RFCL-FOK (FN-SF-CRASH F FC RC)
                     H FN-ARENA))
  :HINTS
  (("Goal" :IN-THEORY
           (UNION-THEORIES '(RFCL-FOK RFCL-FILE-ROWS
                                      FN-RFCL-PENDING-PHASEP FN-SF-CRASH
                                      FN-SF-RECORD-PRESENT-VISIBLEP
                                      FN-SF-PHASE-OF-FN-SF-MAKE
                                      FN-SF-RECORDS-OF-FN-SF-MAKE
                                      FN-SF-RECORD-CANDIDATE-OF-FN-SF-MAKE
                                      RFCL-HANDLES-APPEND RFCL-FOLD-APPEND
                                      RFCL-FOK-HAS-RECORDS NATP
                                      NOT CAR-CONS CDR-CONS CONS-EQUAL MV-NTH
                                      NTH ZP (:EXECUTABLE-COUNTERPART ZP)
                                      (:EXECUTABLE-COUNTERPART BINARY-+)
                                      (:EXECUTABLE-COUNTERPART UNARY--)
                                      (:EXECUTABLE-COUNTERPART MEMBER-EQUAL)
                                      MEMBER-EQUAL)
                           (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM RFCL-LV6
  (IMPLIES (FN-RFCL-OKP S FN-ARENA)
           (FN-RFCL-OKP (FN-SN-CRASH S FRONTIER-CHOICE RECORD-CHOICE)
                        FN-ARENA))
  :HINTS
  (("Goal"
      :IN-THEORY
      (UNION-THEORIES '(RFCL-OKP-IS-FOK FN-SN-CRASH FN-SN-UPDATE-INDEXED
                                        FN-SN-WITH-CONSUMER FN-SN-WITH-TOPIC
                                        FN-SN-FILES-OF-FN-SN-WITH-EVENT-INDEX
                                        FN-SN-FIELDS-OF-FN-SN-MAKE-V6
                                        RFCL-FOK-CRASH)
                      (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM RFCL-FOK-COMPLETE
  (IMPLIES (RFCL-FOK F H FN-ARENA)
           (RFCL-FOK (FN-SF-CORE-COMPLETION F SEQ TX)
                     H FN-ARENA))
  :HINTS
  (("Goal" :IN-THEORY
           (UNION-THEORIES '(RFCL-FOK RFCL-FILE-ROWS FN-RFCL-PENDING-PHASEP
                                      FN-SF-CORE-COMPLETION
                                      FN-SF-SCALARS-OF-FN-SF-MAKE-FIELDS
                                      FN-SF-RECORDS-OF-FN-SF-MAKE-FIELDS-KEPT
                                      NATP
                                      NOT CAR-CONS CDR-CONS CONS-EQUAL MV-NTH
                                      NTH ZP (:EXECUTABLE-COUNTERPART ZP)
                                      (:EXECUTABLE-COUNTERPART BINARY-+)
                                      (:EXECUTABLE-COUNTERPART UNARY--)
                                      (:EXECUTABLE-COUNTERPART MEMBER-EQUAL)
                                      MEMBER-EQUAL)
                           (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM RFCL-FOK-EMIT
  (IMPLIES (RFCL-FOK F H FN-ARENA)
           (RFCL-FOK (FN-SF-EMIT-SUCCESS F SEQ TX)
                     H FN-ARENA))
  :HINTS
  (("Goal" :IN-THEORY
           (UNION-THEORIES '(RFCL-FOK RFCL-FILE-ROWS FN-RFCL-PENDING-PHASEP
                                      FN-SF-EMIT-SUCCESS
                                      FN-SF-SCALARS-OF-FN-SF-MAKE-FIELDS
                                      FN-SF-RECORDS-OF-FN-SF-MAKE-FIELDS-KEPT
                                      NATP
                                      NOT CAR-CONS CDR-CONS CONS-EQUAL MV-NTH
                                      NTH ZP (:EXECUTABLE-COUNTERPART ZP)
                                      (:EXECUTABLE-COUNTERPART BINARY-+)
                                      (:EXECUTABLE-COUNTERPART UNARY--)
                                      (:EXECUTABLE-COUNTERPART MEMBER-EQUAL)
                                      MEMBER-EQUAL)
                           (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM RFCL-FINISH-FILES
  (IMPLIES
       (FN-SN-COMPLETION-ENABLEDP S)
       (EQUAL (FN-SN-FILES (FN-SN-FINISH S))
              (FN-SF-EMIT-SUCCESS
                   (FN-SF-CORE-COMPLETION
                        (FN-SN-FILES S)
                        (FN-STORE-EVENT-SEQUENCE (FN-SN-COMPLETION-RECORD S))
                        (FN-STORE-EVENT-TXID (FN-SN-COMPLETION-RECORD S)))
                   (FN-STORE-EVENT-SEQUENCE (FN-SN-COMPLETION-RECORD S))
                   (FN-STORE-EVENT-TXID (FN-SN-COMPLETION-RECORD S)))))
  :HINTS
  (("Goal"
        :IN-THEORY
        (UNION-THEORIES '(FN-SN-FINISH FN-SN-FINISH-IDENTITY
                                       FN-SN-UPDATE-ACCEPTED
                                       FN-SN-UPDATE-INDEXED
                                       FN-SN-ADVANCE-IDENTITY-NEXT
                                       FN-SN-WITH-CONSUMER FN-SN-WITH-TOPIC
                                       FN-SN-FIELDS-OF-FN-SN-MAKE-V6
                                       FN-SN-FILES-OF-FN-SN-UPDATE
                                       FN-SN-FILES-OF-FN-SN-WITH-EVENT-INDEX)
                        (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM RFCL-LV4-FINISH
  (IMPLIES (FN-RFCL-OKP S FN-ARENA)
           (FN-RFCL-OKP (FN-SN-FINISH S) FN-ARENA))
  :HINTS
  (("Goal" :CASES ((FN-SN-COMPLETION-ENABLEDP S))
           :IN-THEORY
           (UNION-THEORIES '(RFCL-OKP-IS-FOK RFCL-FINISH-FILES
                                             RFCL-FOK-EMIT RFCL-FOK-COMPLETE)
                           (THEORY 'MINIMAL-THEORY)))
   ("Subgoal 2" :IN-THEORY (UNION-THEORIES '(FN-SN-FINISH)
                                           (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM RFCL-STORE-EVENT-NOT-RECORD
   (IMPLIES (FN-STORE-EVENT-P X)
            (NOT (FN-RECORD-P X)))
   :HINTS
   (("Goal" :USE (FN-HELD-IS-NO-WIRE-EVENT FN-HSTXA-IS-NO-WIRE-EVENT
                                           FN-RECORD-IS-NO-OTHER-WIRE-EVENT)
            :IN-THEORY '(FN-STORE-EVENT-P)))))

(local
 (DEFTHM RFCL-AFTER-IS-REPLAY
  (IMPLIES (FN-SF-RECORD-VALUESP ROWS)
           (EQUAL (RFCL-AFTER ROWS ID H)
                  (MV (FN-REPLAY-IDENTITY-LOOP ROWS ID)
                      H)))
  :HINTS
  (("Goal"
        :INDUCT (RFCL-AFTER ROWS ID H)
        :IN-THEORY (E/D (RFCL-AFTER FN-SF-RECORD-VALUESP
                                    FN-REPLAY-IDENTITY-LOOP)
                        (FN-STORE-EVENT-P FN-RECORD-P FN-REPLAY-IDENTITY-STEP
                                          FN-STXK-FAULT FN-INTERN-ROW-AT
                                          FN-SSR-SEED FN-SSR-AT))))))

(local
 (DEFTHM RFCL-RECORD-LIST-VALUES
   (IMPLIES (FN-SF-RECORD-LISTP ROWS SEQ LOW FRONTIER)
            (FN-SF-RECORD-VALUESP ROWS))
   :HINTS
   (("Goal" :INDUCT (FN-SF-RECORD-LISTP ROWS SEQ LOW FRONTIER)
            :IN-THEORY (E/D (FN-SF-RECORD-LISTP FN-SF-RECORD-VALUESP)
                            (FN-STORE-EVENT-P FN-STORE-EVENT-SEQUENCE
                                              FN-STORE-EVENT-TXID
                                              FN-STORE-EVENT-GENERATION))))))

(local
 (DEFTHM RFCL-STATE-RECORD-VALUES
  (IMPLIES (FN-SN-STATEP S)
           (FN-SF-RECORD-VALUESP (FN-SF-RECORDS (FN-SN-FILES S))))
  :HINTS
  (("Goal" :USE ((:INSTANCE FN-CSTP-SN-STATEP-FILES (ST S)))
           :IN-THEORY (UNION-THEORIES '(FN-SF-STATEP RFCL-RECORD-LIST-VALUES)
                                      (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM RFCL-RETAINED-PARTS
  (IMPLIES (FN-OSR-RETAINEDP S)
           (AND (FN-SN-STATEP S)
                (FN-SF-STATEP (FN-SN-FILES S))
                (FN-SN-IDENTITY-SEQUENCEP S)
                (FN-OSR-IDENTITY-PREFIXP S)
                (FN-SKP-RESOLVEDP S)
                (FN-SF-RECORD-VALUESP (FN-SF-RECORDS (FN-SN-FILES S)))))
  :HINTS
  (("Goal"
      :IN-THEORY
      (UNION-THEORIES '(FN-OSR-RETAINEDP FN-OSR-LIVEP FN-STI-LIVEP
                                         FN-CSI-LIVEP FN-CSTP-SN-STATEP-FILES
                                         RFCL-STATE-RECORD-VALUES)
                      (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM RFCL-RESERVED-SNAPSHOT-EXACT
  (IMPLIES (AND (FN-OSR-RETAINEDP S)
                (EQUAL (FN-SF-PHASE (FN-SN-FILES S))
                       :RESERVED))
           (EQUAL (FN-STXK-CONTEXT-SNAPSHOTS
                       (FN-REPLAY-IDENTITY (FN-SF-RECORDS (FN-SN-FILES S))))
                  (FN-SN-KEYRING-SNAPSHOTS S)))
  :HINTS
  (("Goal"
      :USE
      (RFCL-RETAINED-PARTS (:INSTANCE FN-SF-STATE-RECORDS-ARE-TRUE-LIST
                                      (S (FN-SN-FILES S)))
                           (:INSTANCE FN-CBOR-TAKE-WHOLE-LIST
                                      (XS (FN-SF-RECORDS (FN-SN-FILES S)))))
      :IN-THEORY
      (UNION-THEORIES
           '(FN-SN-IDENTITY-SEQUENCEP FN-OSR-IDENTITY-PREFIXP
                                      FN-OSR-CONTEXT-VIEW
                                      FN-SN-IDENTITY-CONTEXT
                                      FN-STXK-CONTEXT-SNAPSHOTS
                                      FN-STXK-CONTEXT FN-SF-COMPLETION-PHASEP
                                      FN-STORE-EVENT-NTH
                                      FN-CSTP-SN-STATEP-FILES
                                      FN-SF-STATE-RECORDS-ARE-TRUE-LIST
                                      MEMBER-EQUAL
                                      (:EXECUTABLE-COUNTERPART MEMBER-EQUAL)
                                      NATP NOT CAR-CONS CDR-CONS CONS-EQUAL)
           (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM RFCL-RESERVED-SEED-EXACT
  (IMPLIES
   (AND (FN-OSR-RETAINEDP S)
        (EQUAL (FN-SF-PHASE (FN-SN-FILES S))
               :RESERVED))
   (AND
    (EQUAL
     (FN-SSR-AT
          1
          (FN-SSR-SEED (FN-REPLAY-IDENTITY (FN-SF-RECORDS (FN-SN-FILES S)))))
     (FN-SN-KEYRING S))
    (EQUAL
     (FN-SSR-AT
          2
          (FN-SSR-SEED (FN-REPLAY-IDENTITY (FN-SF-RECORDS (FN-SN-FILES S)))))
     (FN-SN-KEYRING-GENERATION S))))
  :HINTS
  (("Goal"
    :USE (RFCL-RETAINED-PARTS RFCL-RESERVED-SNAPSHOT-EXACT)
    :IN-THEORY
    (UNION-THEORIES '(FN-SKP-RESOLVEDP FN-SSR-SEED FN-SSR-STATE
                                       FN-SSR-AT FN-AG-CAR FN-AG-CDR
                                       ZP (:EXECUTABLE-COUNTERPART ZP)
                                       (:EXECUTABLE-COUNTERPART BINARY-+)
                                       (:EXECUTABLE-COUNTERPART UNARY--)
                                       NATP NOT CAR-CONS CDR-CONS CONS-EQUAL)
                    (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM RFCL-INTERN-IS-HELD
   (IMPLIES (AND (FN-RECORD-P W) (NATP G) (NATP H))
            (FN-HELD-P (FN-INTERN-ROW-AT W K G H)))
   :HINTS (("Goal" :IN-THEORY (ENABLE FN-INTERN-ROW-AT FN-RECORD-P
                                      FN-HELD-P FN-RECORD-INTERNALS
                                      FN-HELD-INTERNALS FN-HF-P
                                      FN-HC-P FN-HF-STARTP FN-HC-VERDICTP)))))

(local
 (DEFTHM RFCL-INTERN-FIELDS
   (AND (EQUAL (FN-HELD-CONTEXT (FN-INTERN-ROW-AT W K G H))
               (FN-HELD-CONTEXT-OF (FN-RECORD-PAYLOAD W)
                                   K G))
        (EQUAL (FN-RECORD-PAYLOAD (FN-INTERN-ROW-AT W K G H))
               H))
   :HINTS (("Goal" :IN-THEORY (ENABLE FN-INTERN-ROW-AT)))))

(local
 (DEFTHM RFCL-ONE-INTERN
  (IMPLIES
       (AND (FN-HELD-P (FN-INTERN-ROW-AT W K G (FN-ARENA-COUNT FN-ARENA)))
            (NATP G)
            (EQUAL K (FN-SSR-AT 1 (FN-SSR-SEED ID)))
            (EQUAL G (FN-SSR-AT 2 (FN-SSR-SEED ID))))
       (AND (FN-ROWS-HANDLES-INP
                 (LIST (FN-INTERN-ROW-AT W K G (FN-ARENA-COUNT FN-ARENA)))
                 (FN-ARENA-SEAL-LIST (FN-RECORD-PAYLOAD W)
                                     FN-ARENA))
            (FN-ORCR-FOLD-CONTEXTS-OKP
                 (LIST (FN-INTERN-ROW-AT W K G (FN-ARENA-COUNT FN-ARENA)))
                 ID HH
                 (FN-ARENA-SEAL-LIST (FN-RECORD-PAYLOAD W)
                                     FN-ARENA))))
  :HINTS
  (("Goal"
       :IN-THEORY
       (E/D (FN-ROWS-HANDLES-INP FN-ROW-HANDLE-INP FN-ORCR-RETAINED-P
                                 FN-ORCR-HELD-PART FN-ROW-BYTES)
            (FN-HELD-CONTEXT-OF FN-SSR-SEED FN-SSR-AT
                                FN-INTERN-ROW-AT FN-REPLAY-IDENTITY-LOOP
                                FN-HELD-P FN-HSTXA-P
                                FN-RECORD-P FN-ARENA-COUNT-IS-LEN
                                FN-ARENA-PAYLOAD-IS-NTH
                                FN-ARENA-SEAL-LIST-IS-APPEND))
       :EXPAND
       ((:FREE (ROWS H A)
               (FN-ORCR-FOLD-CONTEXTS-OKP NIL ROWS H A))
        (:FREE (A)
               (FN-ORCR-FOLD-CONTEXTS-OKP
                    (LIST (FN-INTERN-ROW-AT W K G (FN-ARENA-COUNT FN-ARENA)))
                    ID HH A)))))))

(local
 (DEFTHM RFCL-AFTER-STORE
  (IMPLIES (FN-OSR-RETAINEDP S)
           (EQUAL (RFCL-AFTER (FN-SF-RECORDS (FN-SN-FILES S))
                              (FN-STXK-INITIAL-CONTEXT 0)
                              H)
                  (MV (FN-REPLAY-IDENTITY (FN-SF-RECORDS (FN-SN-FILES S)))
                      H)))
  :HINTS
  (("Goal"
        :USE (RFCL-RETAINED-PARTS)
        :IN-THEORY (UNION-THEORIES '(RFCL-AFTER-IS-REPLAY FN-REPLAY-IDENTITY)
                                   (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM RFCL-FOLD-SEAL-ANY-HANDLE
  (IMPLIES (AND (FN-ROWS-HANDLES-INP ROWS FN-ARENA)
                (FN-ORCR-FOLD-CONTEXTS-OKP ROWS ID H FN-ARENA)
                (NATP H)
                (NATP HH))
           (FN-ORCR-FOLD-CONTEXTS-OKP ROWS
                                      ID HH (FN-ARENA-SEAL-LIST P FN-ARENA)))
  :HINTS
  (("Goal" :USE ((:INSTANCE FN-RFC-FOLD-CONTEXTS-OKP-ANY-HANDLE
                            (H1 HH)
                            (H2 H)
                            (FN-ARENA (FN-ARENA-SEAL-LIST P FN-ARENA))))
           :IN-THEORY (UNION-THEORIES '(RFCL-FOLD-SEAL)
                                      (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM RFCL-STATE-GENERATION
   (IMPLIES (FN-SN-STATEP S)
            (NATP (FN-SN-KEYRING-GENERATION S)))
   :HINTS (("Goal" :IN-THEORY '(FN-SN-STATEP NATP)))))

(local
 (DEFTHM RFCL-APPEND-INTERN
  (IMPLIES
   (AND (FN-OSR-RETAINEDP S)
        (FN-RFCL-OKP S FN-ARENA)
        (EQUAL (FN-SF-PHASE (FN-SN-FILES S))
               :RESERVED)
        (FN-HELD-P (FN-INTERN-ROW-AT W (FN-SN-KEYRING S)
                                     (FN-SN-KEYRING-GENERATION S)
                                     (FN-ARENA-COUNT FN-ARENA))))
   (LET ((ROWS (APPEND (FN-SF-RECORDS (FN-SN-FILES S))
                       (LIST (FN-INTERN-ROW-AT W (FN-SN-KEYRING S)
                                               (FN-SN-KEYRING-GENERATION S)
                                               (FN-ARENA-COUNT FN-ARENA))))))
     (AND (FN-ROWS-HANDLES-INP ROWS
                               (FN-ARENA-SEAL-LIST (FN-RECORD-PAYLOAD W)
                                                   FN-ARENA))
          (FN-ORCR-FOLD-CONTEXTS-OKP
               ROWS (FN-STXK-INITIAL-CONTEXT 0)
               (FN-ARENA-COUNT (FN-ARENA-SEAL-LIST (FN-RECORD-PAYLOAD W)
                                                   FN-ARENA))
               (FN-ARENA-SEAL-LIST (FN-RECORD-PAYLOAD W)
                                   FN-ARENA)))))
  :HINTS
  (("Goal"
    :USE
    (RFCL-RETAINED-PARTS
     RFCL-RESERVED-SEED-EXACT
     (:INSTANCE RFCL-ONE-INTERN (K (FN-SN-KEYRING S))
                (G (FN-SN-KEYRING-GENERATION S))
                (ID (FN-REPLAY-IDENTITY (FN-SF-RECORDS (FN-SN-FILES S))))
                (HH (FN-ARENA-COUNT (FN-ARENA-SEAL-LIST (FN-RECORD-PAYLOAD W)
                                                        FN-ARENA))))
     (:INSTANCE RFCL-STATE-GENERATION))
    :IN-THEORY
    (UNION-THEORIES
         '(FN-RFCL-OKP FN-RFCL-ROWS FN-RFCL-PENDING-PHASEP
                       RFCL-HANDLES-APPEND RFCL-FOLD-APPEND
                       RFCL-AFTER-STORE RFCL-HANDLES-SEAL
                       RFCL-FOLD-SEAL-ANY-HANDLE
                       FN-ARENA-SEAL-COUNT
                       (:TYPE-PRESCRIPTION FN-ARENA-COUNT)
                       NATP MV-NTH NTH ZP CAR-CONS
                       CDR-CONS (:EXECUTABLE-COUNTERPART ZP)
                       (:EXECUTABLE-COUNTERPART BINARY-+)
                       (:EXECUTABLE-COUNTERPART UNARY--)
                       (:EXECUTABLE-COUNTERPART FN-RFCL-PENDING-PHASEP))
         (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM RFCL-STAGE-INTERN
  (IMPLIES
   (AND (FN-OSR-RETAINEDP S)
        (FN-RFCL-OKP S FN-ARENA)
        (EQUAL (FN-SF-PHASE (FN-SN-FILES S))
               :RESERVED)
        (FN-HELD-P (FN-INTERN-ROW-AT W (FN-SN-KEYRING S)
                                     (FN-SN-KEYRING-GENERATION S)
                                     (FN-ARENA-COUNT FN-ARENA))))
   (FN-RFCL-OKP
       (FN-SN-UPDATE
            S
            (FN-SF-MAKE-FIELDS :RECORD-STAGED FRONTIER NIL
                               (FN-SF-RECORDS-FIELD (FN-SN-FILES S))
                               (FN-INTERN-ROW-AT W (FN-SN-KEYRING S)
                                                 (FN-SN-KEYRING-GENERATION S)
                                                 (FN-ARENA-COUNT FN-ARENA))
                               NIL SF BARRIERS)
            NODE)
       (FN-ARENA-SEAL-LIST (FN-RECORD-PAYLOAD W)
                           FN-ARENA)))
  :HINTS
  (("Goal"
        :USE (RFCL-APPEND-INTERN)
        :IN-THEORY
        (UNION-THEORIES
             '(FN-RFCL-OKP FN-RFCL-ROWS FN-RFCL-PENDING-PHASEP
                           FN-SN-FILES-OF-FN-SN-UPDATE
                           FN-SF-SCALARS-OF-FN-SF-MAKE-FIELDS
                           FN-SF-RECORDS-OF-FN-SF-MAKE-FIELDS-KEPT
                           (:EXECUTABLE-COUNTERPART FN-RFCL-PENDING-PHASEP))
             (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM RFCL-LV2
  (IMPLIES (AND (FN-OSR-RETAINEDP S)
                (FN-RFCL-OKP S FN-ARENA))
           (FN-RFCL-OKP (MV-NTH 0
                                (FN-STORE-PREPARE-INTERNED S W FN-ARENA))
                        (MV-NTH 1
                                (FN-STORE-PREPARE-INTERNED S W FN-ARENA))))
  :HINTS
  (("Goal"
    :IN-THEORY
    (UNION-THEORIES
         '(FN-STORE-PREPARE-INTERNED FN-SN-PREPARE FN-SF-PREPARE-RECORD
                                     RFCL-STAGE-INTERN MV-NTH NTH ZP CAR-CONS
                                     CDR-CONS (:EXECUTABLE-COUNTERPART ZP)
                                     (:EXECUTABLE-COUNTERPART BINARY-+)
                                     (:EXECUTABLE-COUNTERPART UNARY--))
         (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM RFCL-PRC-PREPARE-INTERN
  (IMPLIES
      (AND (FN-OSR-RETAINEDP S)
           (FN-RFCL-OKP S FN-ARENA))
      (FN-RFCL-OKP
           (FN-PRC-SPC-PREPARE S
                               (FN-INTERN-ROW-AT W (FN-SN-KEYRING S)
                                                 (FN-SN-KEYRING-GENERATION S)
                                                 (FN-ARENA-COUNT FN-ARENA))
                               VIEW CARRY)
           (FN-ARENA-SEAL-LIST (FN-RECORD-PAYLOAD W)
                               FN-ARENA)))
  :HINTS
  (("Goal" :IN-THEORY
           (UNION-THEORIES '(FN-PRC-SPC-PREPARE FN-PCAR-STAGE-RECORD
                                                RFCL-STAGE-INTERN RFCL-LV5)
                           (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM RFCL-LV2H
  (LET* ((S (FN-SBUD-OC-STORE OC))
         (ROW (FN-INTERN-ROW-AT RECORD (FN-SN-KEYRING S)
                                (FN-SN-KEYRING-GENERATION S)
                                (FN-ARENA-COUNT FN-ARENA)))
         (OUT (FN-POUT-PREPARE-ARTICLE OC ROW BUDGET CARRY))
         (S2 (FN-SBUD-OC-STORE (MV-NTH 1 OUT))))
    (IMPLIES (AND (FN-OSR-RETAINEDP S)
                  (FN-RFCL-OKP S FN-ARENA))
             (FN-RFCL-OKP S2
                          (IF (EQUAL (MV-NTH 0 OUT) :PREPARED)
                              (FN-ARENA-SEAL-LIST (FN-RECORD-PAYLOAD RECORD)
                                                  FN-ARENA)
                            FN-ARENA))))
  :HINTS
  (("Goal"
    :USE
    ((:INSTANCE
      FN-POUT-STORE-OF-PSRV-PREPARE
      (RECORD
           (FN-INTERN-ROW-AT RECORD
                             (FN-SN-KEYRING (FN-SBUD-OC-STORE OC))
                             (FN-SN-KEYRING-GENERATION (FN-SBUD-OC-STORE OC))
                             (FN-ARENA-COUNT FN-ARENA))))
     (:INSTANCE RFCL-PRC-PREPARE-INTERN
                (S (FN-SBUD-OC-STORE OC))
                (W RECORD)
                (VIEW (FN-OWN-VIEW (FN-OCFG-OWNER OC)))))
    :IN-THEORY
    (UNION-THEORIES
         '(FN-POUT-PREPARE-ARTICLE-ANSWERS-THE-STORE-CHANGE RFCL-LV5)
         (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM RFCL-BINDSP-IS-NODE-STATEP
   (IMPLIES (FN-RCON-SN-RECORD-BINDSP NODE ROW)
            (FN-NODE-STATEP NODE))
   :RULE-CLASSES NIL
   :HINTS
   (("Goal"
         :IN-THEORY
         (UNION-THEORIES '(FN-RCON-SN-RECORD-BINDSP FN-SN-RECORD-BINDSP
                                                    FN-NODE-PENDING-MATCHESP)
                         (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM RFCL-UPDATE-STATEP
  (IMPLIES (AND (FN-SN-STATEP S)
                (FN-SF-STATEP FILES)
                (FN-NODE-STATEP NODE))
           (FN-SN-STATEP (FN-SN-UPDATE S FILES NODE)))
  :HINTS
  (("Goal"
     :IN-THEORY (UNION-THEORIES '(FN-SN-STATEP FN-SN-UPDATE
                                               FN-SN-FIELDS-OF-FN-SN-MAKE-V6)
                                (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM RFCL-STAGE-FILES-FACTS
  (IMPLIES
   (FN-SF-STATEP FILES)
   (AND
    (FN-SF-STATEP (FN-PCAR-STAGE-RECORD FILES ROW))
    (EQUAL (FN-SF-RECORDS (FN-PCAR-STAGE-RECORD FILES ROW))
           (FN-SF-RECORDS FILES))
    (IMPLIES (EQUAL (FN-SF-PHASE FILES) :RESERVED)
             (EQUAL (FN-SF-RECORD-CANDIDATE (FN-PCAR-STAGE-RECORD FILES ROW))
                    (IF (FN-PCAR-FILES-CANDIDATEP ROW FILES)
                        ROW
                      (FN-SF-RECORD-CANDIDATE FILES))))))
  :HINTS
  (("Goal"
        :IN-THEORY
        (UNION-THEORIES
             '(FN-PCAR-STAGE-RECORD FN-PCAR-FILES-CANDIDATEP-IS-CANDIDATEP
                                    FN-SF-STATEP
                                    FN-SF-SHAPE-FIELDS-CANONICAL
                                    FN-SF-PHASE-SHAPEP
                                    FN-PCAR-CANDIDATEP-IS-CANDIDATEP
                                    FN-SF-SHAPEP-OF-FN-SF-MAKE-FIELDS
                                    FN-SF-SUCCESSES-OF-FN-SF-MAKE-FIELDS-KEPT
                                    (:E FN-SF-PHASEP)
                                    (:E FN-SF-FRONTIER-PHASEP)
                                    (:E FN-SF-RECORD-PHASEP)
                                    (:E FN-SF-COMPLETION-PHASEP)
                                    FN-SF-SCALARS-OF-FN-SF-MAKE-FIELDS
                                    FN-SF-RECORDS-OF-FN-SF-MAKE-FIELDS-KEPT)
             (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM RFCL-STAGE-NONCANDIDATE-IS-NO-OP
   (IMPLIES (NOT (FN-PCAR-FILES-CANDIDATEP ROW FILES))
            (EQUAL (FN-PCAR-STAGE-RECORD FILES ROW)
                   FILES))
   :HINTS (("Goal" :IN-THEORY (UNION-THEORIES '(FN-PCAR-STAGE-RECORD)
                                              (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM RFCL-PRC-PREPARED-FACTS
  (LET ((NEXT (FN-PRC-SPC-PREPARE S ROW VIEW CARRY)))
    (IMPLIES (NOT (EQUAL NEXT S))
             (AND (FN-SN-STATEP NEXT)
                  (FN-SN-KNOWN-ABORT-ENABLEDP NEXT)
                  (EQUAL (FN-SF-RECORDS (FN-SN-FILES NEXT))
                         (FN-SF-RECORDS (FN-SN-FILES S))))))
  :HINTS
  (("Goal"
      :USE ((:INSTANCE RFCL-BINDSP-IS-NODE-STATEP
                       (NODE (FN-PRC-SN-PREPARE-NODE (FN-SN-NODE S)
                                                     ROW VIEW CARRY))))
      :IN-THEORY
      (UNION-THEORIES
           '(FN-PRC-SPC-PREPARE FN-SN-KNOWN-ABORT-ENABLEDP
                                FN-CSTP-SN-UPDATE-FIELDS
                                RFCL-UPDATE-STATEP
                                RFCL-STAGE-FILES-FACTS
                                RFCL-STAGE-NONCANDIDATE-IS-NO-OP
                                FN-CSTP-SN-STATEP-FILES
                                FN-RCON-SN-RECORD-BINDSP-IS-SN-RECORD-BINDSP)
           (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM RFCL-POUT-PREPARED-FACTS
   (LET* ((OUT (FN-POUT-PREPARE-ARTICLE OC ROW BUDGET CARRY))
          (S (FN-SBUD-OC-STORE OC))
          (NEXT (FN-SBUD-OC-STORE (MV-NTH 1 OUT))))
     (IMPLIES (EQUAL (MV-NTH 0 OUT) :PREPARED)
              (AND (FN-SN-KNOWN-ABORT-ENABLEDP NEXT)
                   (EQUAL (FN-SF-RECORDS (FN-SN-FILES NEXT))
                          (FN-SF-RECORDS (FN-SN-FILES S))))))
   :HINTS
   (("Goal"
         :USE ((:INSTANCE FN-POUT-STORE-OF-PSRV-PREPARE
                          (RECORD ROW))
               (:INSTANCE RFCL-PRC-PREPARED-FACTS
                          (S (FN-SBUD-OC-STORE OC))
                          (VIEW (FN-OWN-VIEW (FN-OCFG-OWNER OC)))))
         :IN-THEORY
         (UNION-THEORIES
              '(FN-POUT-PREPARE-ARTICLE FN-POUT-STAGEDP FN-PSRV-REFUSAL-KIND
                                        FN-SBUD-REFUSAL-KIND
                                        MV-NTH CAR-CONS CDR-CONS (:E ZP)
                                        (:E BINARY-+)
                                        (:E UNARY--))
              (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM RFCL-ABORT-RESTORES-RECORDS-OKP
  (IMPLIES (AND (FN-RFCL-OKP S FN-ARENA)
                (FN-SN-KNOWN-ABORT-ENABLEDP NEXT)
                (EQUAL (FN-SF-RECORDS (FN-SN-FILES NEXT))
                       (FN-SF-RECORDS (FN-SN-FILES S))))
           (FN-RFCL-OKP (FN-SN-KNOWN-ABORT NEXT)
                        FN-ARENA))
  :HINTS
  (("Goal"
    :USE ((:INSTANCE RFCL-FOK-HAS-RECORDS (F (FN-SN-FILES S))
                     (H (FN-ARENA-COUNT FN-ARENA)))
          (:INSTANCE FN-POUT-KNOWN-ABORT-REACHES-READY
                     (S NEXT))
          (:INSTANCE FN-SNRT-KNOWN-ABORT-KEEPS-RECORDS
                     (S NEXT)))
    :IN-THEORY (UNION-THEORIES '(RFCL-OKP-IS-FOK RFCL-FOK RFCL-FILE-ROWS
                                                 (:E FN-RFCL-PENDING-PHASEP))
                               (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM RFCL-POUT-PREPARE-THEN-ABORT
  (LET* ((OUT (FN-POUT-PREPARE-ARTICLE OC ROW BUDGET CARRY))
         (AB (FN-POUT-KNOWN-ABORT (MV-NTH 1 OUT)
                                  FN-ARENA)))
    (IMPLIES (AND (FN-RFCL-OKP (FN-SBUD-OC-STORE OC)
                               FN-ARENA)
                  (EQUAL (MV-NTH 0 OUT) :PREPARED))
             (FN-RFCL-OKP (FN-SBUD-OC-STORE (MV-NTH 1 AB))
                          FN-ARENA)))
  :HINTS
  (("Goal"
    :USE
    ((:INSTANCE RFCL-POUT-PREPARED-FACTS)
     (:INSTANCE
        RFCL-ABORT-RESTORES-RECORDS-OKP
        (S (FN-SBUD-OC-STORE OC))
        (NEXT (FN-SBUD-OC-STORE
                   (MV-NTH 1
                           (FN-POUT-PREPARE-ARTICLE OC ROW BUDGET CARRY))))))
    :IN-THEORY
    (UNION-THEORIES
         '(FN-POUT-KNOWN-ABORT FN-POUT-STORE-OF-STORE-STEP FN-SNRT-STEP
                               MV-NTH CAR-CONS CDR-CONS (:E ZP)
                               (:E BINARY-+)
                               (:E UNARY--))
         (THEORY 'MINIMAL-THEORY))))))

(local
 (DEFTHM FN-OWNER-RETAIN-PRC-ARTICLE-VIEW-FRAME
  (EQUAL (FN-OSR-RETAINED-VIEW (FN-PRC-SPC-PREPARE S E VIEW CARRY))
         (FN-OSR-RETAINED-VIEW S))
  :HINTS
  (("Goal"
      :IN-THEORY '(FN-PRC-SPC-PREPARE FN-OSR-RETAINED-VIEW
                                      FN-CSTP-SN-UPDATE-FIELDS
                                      FN-OWNER-RETAIN-UPDATE-SELECTORS
                                      FN-PCAR-STAGE-RECORD
                                      FN-SF-RECORDS-OF-FN-SF-MAKE-FIELDS-KEPT
                                      CAR-CONS CDR-CONS)))))

(local
 (DEFTHM FN-OWNER-RETAIN-PRC-ARTICLE-LIVE-MODEL
  (IMPLIES (AND (FN-OSR-LIVEP S)
                (FN-CST-RELATION (FN-PRC-SPC-PREPARE S E VIEW CARRY)))
           (FN-OSR-LIVEP (FN-PRC-SPC-PREPARE S E VIEW CARRY)))
  :HINTS
  (("Goal" :USE ((:INSTANCE FN-OWNER-CARRIED-ARTICLE-PREPARE-PRESERVES-CURSOR
                            (RECORD E))
                 (:INSTANCE FN-CSTP-RELATION-IS-STATEP
                            (ST (FN-PRC-SPC-PREPARE S E VIEW CARRY)))
                 (:INSTANCE FN-HELD-IS-NO-WIRE-EVENT (X E)))
           :IN-THEORY '(FN-OWNER-RETAIN-PRC-ARTICLE-VIEW-FRAME
                            FN-PRC-SPC-PREPARE FN-OSR-LIVEP
                            FN-CSTP-RELATION-IS-STATEP FN-STI-LIVEP
                            FN-CSI-LIVEP FN-STI-COMPLETED-PREFIXP
                            FN-CSI-COMPLETED-PREFIXP
                            FN-CSI-COMPLETION-LASTP
                            FN-OSR-IDENTITY-PREFIXP
                            FN-SN-IDENTITY-CONTEXT
                            FN-CSTP-SN-UPDATE-FIELDS
                            FN-OWNER-RETAIN-UPDATE-SELECTORS
                            FN-PCAR-STAGE-RECORD
                            FN-SF-RECORDS-OF-FN-SF-MAKE-FIELDS-KEPT
                            FN-SF-SCALARS-OF-FN-SF-MAKE-FIELDS
                            FN-SF-COMPLETION-PHASEP MEMBER-EQUAL
                            CAR-CONS CDR-CONS (:E MEMBER-EQUAL)
                            (:E EQUAL))))))

(local
 (DEFTHM FN-OWNER-RETAIN-PRC-ARTICLE-KEEPS-RETAINED
  (IMPLIES (AND (FN-OSR-RETAINEDP S)
                (FN-CST-RELATION (FN-PRC-SPC-PREPARE S E VIEW CARRY)))
           (FN-OSR-RETAINEDP (FN-PRC-SPC-PREPARE S E VIEW CARRY)))
  :HINTS
  (("Goal"
     :USE ((:INSTANCE FN-OSR-RETAINED-VIEW-CONNECTS-FULL-CARRY
                      (A S)
                      (B (FN-PRC-SPC-PREPARE S E VIEW CARRY)))
           FN-OWNER-RETAIN-PRC-ARTICLE-LIVE-MODEL)
     :IN-THEORY '(FN-OSR-RETAINEDP FN-OWNER-RETAIN-PRC-ARTICLE-VIEW-FRAME)))))

(local
 (DEFTHM FN-OWNER-RETAIN-POUT-ARTICLE-KEEPS-RETAINED
  (IMPLIES
       (AND (FN-LGOC-INVARIANTP OC)
            (FN-PRC-CARRYP CARRY)
            (FN-OSR-RETAINEDP (FN-SBUD-OC-STORE OC)))
       (FN-OSR-RETAINEDP
            (FN-SBUD-OC-STORE
                 (MV-NTH 1
                         (FN-POUT-PREPARE-ARTICLE OC RECORD BUDGET CARRY)))))
  :HINTS
  (("Goal"
        :USE (FN-POUT-STORE-OF-PSRV-PREPARE
                  FN-PSRV-PREPARE-PRESERVES-INVARIANT
                  (:INSTANCE FN-LGOC-OCL-RELATION-CST
                             (OC (FN-PSRV-PREPARE OC RECORD BUDGET CARRY)))
                  (:INSTANCE FN-OWNER-RETAIN-PRC-ARTICLE-KEEPS-RETAINED
                             (S (FN-SBUD-OC-STORE OC))
                             (E RECORD)
                             (VIEW (FN-OWN-VIEW (FN-OCFG-OWNER OC)))))
        :IN-THEORY
        '(FN-POUT-PREPARE-ARTICLE FN-LGOC-INVARIANTP
                                  FN-SBUD-OC-STORE MV-NTH
                                  NTH ENDP ZP CAR-CONS CDR-CONS (:E ZP)
                                  (:E BINARY-+)
                                  (:E UNARY--))))))

(local
 (DEFTHM FN-OWNER-RETAIN-ARTICLE-PREPARE-CUT
  (LET*
    ((S (FN-OWNER-STORE STATE))
     (ROW (FN-INTERN-ROW-AT RECORD (FN-SN-KEYRING S)
                            (FN-SN-KEYRING-GENERATION S)
                            (FN-ARENA-COUNT FN-ARENA)))
     (CARRY (FN-PRC-REFRESH (FN-OWNER-RETAIN-CARRY STATE)
                            (FN-NODE-RETENTION (FN-SN-NODE S))))
     (OUT (FN-POUT-PREPARE-ARTICLE (FN-OWNER-OCFG STATE)
                                   ROW BUDGET CARRY))
     (NEXT (FN-OWNER-INSTALL-OCFG (MV-NTH 1 OUT)
                                  (FN-OWNER-RETAIN-CARRY-PUT CARRY STATE))))
    (IMPLIES
         (FN-OWNER-RETAIN-LIVEP STATE FN-ARENA)
         (AND (FN-OWNER-RETAIN-STATEP NEXT)
              (FN-OSR-RETAINEDP (FN-OWNER-STORE NEXT))
              (FN-RFCL-OKP (FN-OWNER-STORE NEXT)
                           (IF (EQUAL (MV-NTH 0 OUT) :PREPARED)
                               (FN-ARENA-SEAL-LIST (FN-RECORD-PAYLOAD RECORD)
                                                   FN-ARENA)
                             FN-ARENA)))))
  :HINTS
  (("Goal"
    :USE
    (FN-OWNER-RETAIN-STATEP-IMPLIES-LGOC
     (:INSTANCE
          FN-PRC-CARRYP-OF-REFRESH
          (CARRY (FN-OWNER-RETAIN-CARRY STATE))
          (LEDGER (FN-NODE-RETENTION (FN-SN-NODE (FN-OWNER-STORE STATE)))))
     (:INSTANCE
      FN-PSRV-PREPARE-PRESERVES-INVARIANT
      (OC (FN-OWNER-OCFG STATE))
      (RECORD
          (FN-INTERN-ROW-AT RECORD
                            (FN-SN-KEYRING (FN-OWNER-STORE STATE))
                            (FN-SN-KEYRING-GENERATION (FN-OWNER-STORE STATE))
                            (FN-ARENA-COUNT FN-ARENA)))
      (CARRY (FN-PRC-REFRESH
                  (FN-OWNER-RETAIN-CARRY STATE)
                  (FN-NODE-RETENTION (FN-SN-NODE (FN-OWNER-STORE STATE))))))
     (:INSTANCE
       RFCL-LV2H (OC (FN-OWNER-OCFG STATE))
       (CARRY (FN-PRC-REFRESH
                   (FN-OWNER-RETAIN-CARRY STATE)
                   (FN-NODE-RETENTION (FN-SN-NODE (FN-OWNER-STORE STATE))))))
     (:INSTANCE
      FN-OWNER-RETAIN-POUT-ARTICLE-KEEPS-RETAINED
      (OC (FN-OWNER-OCFG STATE))
      (RECORD
          (FN-INTERN-ROW-AT RECORD
                            (FN-SN-KEYRING (FN-OWNER-STORE STATE))
                            (FN-SN-KEYRING-GENERATION (FN-OWNER-STORE STATE))
                            (FN-ARENA-COUNT FN-ARENA)))
      (CARRY (FN-PRC-REFRESH
                  (FN-OWNER-RETAIN-CARRY STATE)
                  (FN-NODE-RETENTION (FN-SN-NODE (FN-OWNER-STORE STATE)))))))
    :IN-THEORY
    '(FN-OWNER-RETAIN-LIVEP FN-OWNER-RETAIN-STATEP
                            FN-POUT-PREPARE-ARTICLE
                            FN-ORH-RETAIN-STATEP-OF-RETAIN-CARRY-PUT
                            FN-ORH-RETAIN-STATEP-OF-INSTALL-OCFG
                            FN-OWNER-BOUND-OF-RETAIN-CARRY-PUT
                            FN-OWNER-BOUND-OF-INSTALL-OCFG
                            FN-OWNER-RETAIN-CARRY-OF-INSTALL-OCFG
                            FN-OWNER-RETAIN-CARRY-OF-PUT
                            FN-OWNER-RETAIN-STORE-PROJECTION
                            FN-OWNER-STORE-IS-CONFIGURED-STORE-BY-DEFINITION
                            FN-OWNER-OCFG-OF-INSTALL-OCFG
                            FN-OWNER-OCFG-OF-RETAIN-CARRY-PUT
                            FN-OWNER-OCFG-OF-OTHER-GLOBAL-PUT MV-NTH
                            NTH ENDP ZP CAR-CONS CDR-CONS (:E ZP)
                            (:E BINARY-+)
                            (:E UNARY--))))))

(local
 (DEFTHM FN-OWNER-RETAIN-SN-ABORT-KEEPS-RETAINED
   (IMPLIES (AND (FN-OSR-RETAINEDP S)
                 (FN-CST-RELATION (FN-SN-KNOWN-ABORT S)))
            (FN-OSR-RETAINEDP (FN-SN-KNOWN-ABORT S)))
   :HINTS
   (("Goal"
         :USE ((:INSTANCE FN-OSR-RETAINED-VIEW-CONNECTS-FULL-CARRY
                          (A S)
                          (B (FN-SN-KNOWN-ABORT S)))
               (:INSTANCE FN-OSR-STORE-STEP-PRESERVES-INDEPENDENT-LIVE
                          (EVENT (LIST :KNOWN-ABORT))))
         :IN-THEORY '(FN-OSR-RETAINEDP FN-OSR-LIVEP
                                       FN-OSR-INDEPENDENT-LIVEP FN-SNRT-STEP
                                       FN-OSR-PREPARATIONS-KEEP-RETAINED-VIEW
                                       FN-SN-KNOWN-ABORT
                                       FN-CSTP-SN-UPDATE-FIELDS MEMBER-EQUAL
                                       CAR-CONS CDR-CONS (:E EQUAL)
                                       (:E MEMBER-EQUAL))))))

(local
 (DEFTHM FN-OWNER-RETAIN-KNOWN-ABORT-RETAINED
  (IMPLIES
       (AND (FN-OWNER-RETAIN-STATEP STATE)
            (FN-OSR-RETAINEDP (FN-OWNER-STORE STATE)))
       (FN-OSR-RETAINEDP
            (FN-OWNER-STORE (MV-NTH 2
                                    (FN-OWNER-KNOWN-ABORT FN-ARENA STATE)))))
  :HINTS
  (("Goal"
     :USE
     (FN-OWNER-RETAIN-STATEP-IMPLIES-LGOC
          (:INSTANCE FN-POUT-KNOWN-ABORT-PRESERVES-OWNER-INVARIANT
                     (OC (FN-OWNER-OCFG STATE)))
          (:INSTANCE FN-LGOC-OCL-RELATION-CST
                     (OC (MV-NTH 1
                                 (FN-POUT-KNOWN-ABORT (FN-OWNER-OCFG STATE)
                                                      FN-ARENA))))
          (:INSTANCE FN-POUT-STORE-OF-STORE-STEP
                     (OC (FN-OWNER-OCFG STATE))
                     (EV (LIST :KNOWN-ABORT)))
          (:INSTANCE FN-OWNER-RETAIN-SN-ABORT-KEEPS-RETAINED
                     (S (FN-OWNER-STORE STATE))))
     :IN-THEORY '(FN-OWNER-KNOWN-ABORT FN-POUT-KNOWN-ABORT FN-LGOC-INVARIANTP
                                       FN-OWNER-RETAIN-STORE-PROJECTION
                                       FN-OWNER-OCFG-OF-INSTALL-OCFG
                                       FN-OWNER-OCFG-OF-OTHER-GLOBAL-PUT
                                       FN-SNRT-STEP FN-SBUD-OC-STORE MV-NTH
                                       NTH ENDP ZP CAR-CONS CDR-CONS (:E ZP)
                                       (:E BINARY-+)
                                       (:E UNARY--))))))

(local
 (DEFTHM FN-OWNER-RETAIN-KNOWN-ABORT-CUT
  (IMPLIES
   (AND
    (FN-OWNER-RETAIN-STATEP STATE)
    (FN-OSR-RETAINEDP (FN-OWNER-STORE STATE))
    (FN-RFCL-OKP
         (FN-SBUD-OC-STORE (MV-NTH 1
                                   (FN-POUT-KNOWN-ABORT (FN-OWNER-OCFG STATE)
                                                        FN-ARENA)))
         FN-ARENA))
   (FN-OWNER-RETAIN-LIVEP (MV-NTH 2 (FN-OWNER-KNOWN-ABORT FN-ARENA STATE))
                          FN-ARENA))
  :HINTS
  (("Goal" :USE (FN-OWNER-KNOWN-ABORT-PRESERVES-RETAIN-STATE
                     FN-OWNER-RETAIN-KNOWN-ABORT-RETAINED)
           :IN-THEORY
           '(FN-OWNER-RETAIN-LIVEP FN-OWNER-KNOWN-ABORT-EXACT-EFFECTS
                                   FN-OWNER-RETAIN-STORE-PROJECTION
                                   MV-NTH NTH ZP CAR-CONS CDR-CONS (:E ZP)
                                   (:E BINARY-+)
                                   (:E UNARY--))))))

(defthm fn-owner-post-quantum-keeps-retain-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep
            (mv-nth 2 (fn-owner-retain-post-quantum record budget force-abort fn-arena fn-cat state))
            (mv-nth 1 (fn-owner-retain-post-quantum record budget force-abort fn-arena fn-cat state))))
  :rule-classes nil
  :hints (("Goal"
    :USE
    (FN-OWNER-RETAIN-ARTICLE-PREPARE-CUT
     (:INSTANCE
      RFCL-POUT-PREPARE-THEN-ABORT
      (OC (FN-OWNER-OCFG STATE))
      (ROW
          (FN-INTERN-ROW-AT RECORD
                            (FN-SN-KEYRING (FN-OWNER-STORE STATE))
                            (FN-SN-KEYRING-GENERATION (FN-OWNER-STORE STATE))
                            (FN-ARENA-COUNT FN-ARENA)))
      (CARRY (FN-PRC-REFRESH
                  (FN-OWNER-RETAIN-CARRY STATE)
                  (FN-NODE-RETENTION (FN-SN-NODE (FN-OWNER-STORE STATE))))))
     (:INSTANCE
      FN-OWNER-RETAIN-KNOWN-ABORT-CUT
      (STATE
       (F-PUT-GLOBAL
        'FN-OWNER-CAT-CANDIDATE
        (CONS
          RECORD
          (FN-INTERN-ROW-AT RECORD
                            (FN-SN-KEYRING (FN-OWNER-STORE STATE))
                            (FN-SN-KEYRING-GENERATION (FN-OWNER-STORE STATE))
                            (FN-ARENA-COUNT FN-ARENA)))
        (FN-OWNER-INSTALL-OCFG
         (MV-NTH
          1
          (FN-POUT-PREPARE-ARTICLE
              (FN-OWNER-OCFG STATE)
              (FN-INTERN-ROW-AT
                   RECORD
                   (FN-SN-KEYRING (FN-OWNER-STORE STATE))
                   (FN-SN-KEYRING-GENERATION (FN-OWNER-STORE STATE))
                   (FN-ARENA-COUNT FN-ARENA))
              BUDGET
              (FN-PRC-REFRESH
                   (FN-OWNER-RETAIN-CARRY STATE)
                   (FN-NODE-RETENTION (FN-SN-NODE (FN-OWNER-STORE STATE))))))
         (FN-OWNER-RETAIN-CARRY-PUT
              (FN-PRC-REFRESH
                   (FN-OWNER-RETAIN-CARRY STATE)
                   (FN-NODE-RETENTION (FN-SN-NODE (FN-OWNER-STORE STATE))))
              STATE)))))
     (:INSTANCE
      FN-OWNER-RETAIN-REFUSE-RESERVATION-KEEPS-LIVE
      (STATE
       (FN-OWNER-INSTALL-OCFG
        (MV-NTH
         1
         (FN-POUT-PREPARE-ARTICLE
          (FN-OWNER-OCFG STATE)
          (FN-INTERN-ROW-AT RECORD
                            (FN-SN-KEYRING (FN-OWNER-STORE STATE))
                            (FN-SN-KEYRING-GENERATION (FN-OWNER-STORE STATE))
                            (FN-ARENA-COUNT FN-ARENA))
          BUDGET
          (FN-PRC-REFRESH
               (FN-OWNER-RETAIN-CARRY STATE)
               (FN-NODE-RETENTION (FN-SN-NODE (FN-OWNER-STORE STATE))))))
        (FN-OWNER-RETAIN-CARRY-PUT
             (FN-PRC-REFRESH
                  (FN-OWNER-RETAIN-CARRY STATE)
                  (FN-NODE-RETENTION (FN-SN-NODE (FN-OWNER-STORE STATE))))
             STATE))))
     (:INSTANCE
      FN-OWNER-RETAIN-CAT-PREPARE-SEALED-KEEPS-LIVE
      (STATE
       (F-PUT-GLOBAL
        'FN-OWNER-CAT-CANDIDATE
        (CONS
          RECORD
          (FN-INTERN-ROW-AT RECORD
                            (FN-SN-KEYRING (FN-OWNER-STORE STATE))
                            (FN-SN-KEYRING-GENERATION (FN-OWNER-STORE STATE))
                            (FN-ARENA-COUNT FN-ARENA)))
        (FN-OWNER-INSTALL-OCFG
         (MV-NTH
          1
          (FN-POUT-PREPARE-ARTICLE
              (FN-OWNER-OCFG STATE)
              (FN-INTERN-ROW-AT
                   RECORD
                   (FN-SN-KEYRING (FN-OWNER-STORE STATE))
                   (FN-SN-KEYRING-GENERATION (FN-OWNER-STORE STATE))
                   (FN-ARENA-COUNT FN-ARENA))
              BUDGET
              (FN-PRC-REFRESH
                   (FN-OWNER-RETAIN-CARRY STATE)
                   (FN-NODE-RETENTION (FN-SN-NODE (FN-OWNER-STORE STATE))))))
         (FN-OWNER-RETAIN-CARRY-PUT
              (FN-PRC-REFRESH
                   (FN-OWNER-RETAIN-CARRY STATE)
                   (FN-NODE-RETENTION (FN-SN-NODE (FN-OWNER-STORE STATE))))
              STATE))))
      (FN-ARENA (FN-ARENA-SEAL-LIST (FN-RECORD-PAYLOAD RECORD)
                                    FN-ARENA))))
    :IN-THEORY '(FN-OWNER-RETAIN-POST-QUANTUM
                     FN-OWNER-RETAIN-LIVEP
                     FN-POUT-PREPARE-ARTICLE
                     FN-OWNER-CAT-MAY-SEAL-REFINES-CAT-BY-DEFINITION
                     FN-OWNER-RETAIN-STORE-PROJECTION
                     FN-OWNER-OCFG-OF-INSTALL-OCFG
                     FN-OWNER-OCFG-OF-RETAIN-CARRY-PUT
                     FN-OWNER-OCFG-OF-OTHER-GLOBAL-PUT
                     FN-ORH-RETAIN-STATEP-OF-OTHER-GLOBAL-PUT
                     MV-NTH
                     NTH ENDP ZP CAR-CONS CDR-CONS (:E ZP)
                     (:E EQUAL)
                     (:E BINARY-+)
                     (:E UNARY--)))))

(defthm fn-owner-retain-quanta-keep-retained-store
  (implies (fn-owner-retain-livep state fn-arena)
    (and (fn-osr-retainedp (fn-owner-store (mv-nth 2 (fn-owner-retain-post-quantum record budget abort fn-arena fn-cat state))))
         (fn-osr-retainedp (fn-owner-store (mv-nth 2 (fn-owner-retain-identity-quantum event fn-arena fn-cat state))))))
  :hints (("Goal" :USE ((:INSTANCE FN-OWNER-POST-QUANTUM-KEEPS-RETAIN-LIVE
                            (FORCE-ABORT ABORT))
                 (:INSTANCE FN-OWNER-IDENTITY-QUANTUM-KEEPS-RETAIN-LIVE))
           :IN-THEORY '(FN-OWNER-RETAIN-LIVEP))))

; v1c finish: the host calls fn-apc-own-finish, whose existing keystone
; fn-apc-own-finish-is-own-finish supplies the pre-existing parse/history
; premises at the host boundary. This pure finish statement needs neither.
(defthm fn-owner-retain-finish-submission-keeps-retained-store
  (implies (fn-osr-retainedp (fn-own-store o))
           (fn-osr-retainedp (fn-own-store (cdr (fn-own-finish o cfg fn-arena)))))
  :hints (("Goal"
           :use ((:instance fn-osr-finish-preserves-full-retained-carry
                            (s (fn-own-store o))))
           :in-theory '(fn-own-finish fn-own-complete fn-own-refresh-keeps-fields
                        fn-own-store-of-fn-own-make car-cons cdr-cons))))

; Host POST map: host/owner-host.lisp:2516-2650 prepares the catalog row,
; installs next ocfg, and applies fn-adm-article-word to the prepare word.
; host/native/owner.lisp:3683-3728 maps :seal-buffer to seal + catalog prepare;
; a staged refusal uses known-abort; an unstaged refusal consumes reservation.
; R-POST-1 hypotheses are copied from existing keystones
; fn-ppc-pout-prepare-article-cat-of-live-owner and
; fn-apc-intern-row-at-is-reference (CARRY here is the parse carry;
; RETAIN-CARRY is the separate refreshed retention carry).
(defthm fn-owner-retain-host-prepare-is-the-quantum-prepare
  (let ((oc (fn-owner-ocfg state)))
    (implies (and (fn-ocl-relation oc)
                  (fn-scj-invp (fn-ocfg-owner oc) fn-arena fn-cat)
                  (fn-apc-p carry))
             (and
              (equal (mv-nth 0
                       (fn-ppc-pout-prepare-article-cat oc
                         (fn-apc-intern-row-at record kr gen n carry)
                         budget retain-carry fn-arena fn-cat))
                     (mv-nth 0 (fn-pout-prepare-article oc
                                 (fn-intern-row-at record kr gen n)
                                 budget retain-carry)))
              (equal (mv-nth 1
                       (fn-ppc-pout-prepare-article-cat oc
                         (fn-apc-intern-row-at record kr gen n carry)
                         budget retain-carry fn-arena fn-cat))
                     (mv-nth 1 (fn-pout-prepare-article oc
                                 (fn-intern-row-at record kr gen n)
                                 budget retain-carry))))))
  :hints (("Goal"
           :use ((:instance fn-ppc-pout-prepare-article-cat-of-live-owner
                            (oc (fn-owner-ocfg state))
                            (record (fn-intern-row-at record kr gen n))
                            (carry retain-carry))
                 (:instance fn-apc-intern-row-at-is-reference
                            (w record) (keyring kr) (generation gen) (h n)))
           :in-theory '(fn-apc-intern-row-at-is-reference))))

; R-POST-2: no hypotheses are needed. Existing keystones:
; fn-adm-article-word-passes-other-words, and the refusal cases named by
; fn-adm-article-word-under-the-budget-names-the-resource.
; The memory refusal is passed budget zero before the prepare, not after
; an accepted prepare; neither refusal naming function creates :prepared.
(defthm fn-owner-retain-admitted-word-is-prepared-iff
  (iff (equal (fn-adm-article-word word profile img cfg limit used bytes-used
                                 record debt tot row) :prepared)
       (equal word :prepared))
  :hints (("Goal" :cases ((equal word :unaffordable))
           :use fn-adm-article-word-passes-other-words
           :in-theory '(fn-adm-article-word fn-cvec-article-refusal-word
                        (:e equal)))))

; Identity map: host/native/owner.lisp:4200-4222 calls prepare-identity;
; (:seal payload) causes one seal and cat-prepare-sealed, :prepared passes,
; and every refusal calls refuse-reservation. Those are the quantum's arms.
; R-IDENTITY's only hypothesis is copied verbatim from the existing keystone
; fn-irc-pout-prepare-identity-of-refresh-is-pout, with CARRY bound to the
; actual owner's retention carry. The invalid-event branch remains explicit.
(defthm fn-owner-retain-host-identity-is-the-quantum-prepare
  (let* ((carry (fn-owner-retain-carry state))
         (oc (fn-owner-ocfg state))
         (out (fn-pout-prepare-identity oc event (fn-arena-count fn-arena))))
    (implies (fn-prc-carryp carry)
             (and
              (equal (mv-nth 1 (fn-owner-prepare-identity event fn-arena state))
                     (if (not (or (fn-stxk-p event) (fn-stxa-p event)))
                         :invalid
                       (if (and (equal (mv-nth 0 out) :prepared)
                                (fn-oii-identity-sealsp event))
                           (list :seal (fn-oii-identity-payload event))
                         (mv-nth 0 out))))
              (equal (fn-owner-ocfg
                       (mv-nth 2 (fn-owner-prepare-identity event fn-arena state)))
                     (if (not (or (fn-stxk-p event) (fn-stxa-p event)))
                         oc
                       (mv-nth 1 out))))))
  :hints (("Goal"
           :use ((:instance fn-irc-pout-prepare-identity-of-refresh-is-pout
                            (oc (fn-owner-ocfg state)) (w event)
                            (h (fn-arena-count fn-arena))
                            (carry (fn-owner-retain-carry state))
                            (ledger (fn-node-retention (fn-sn-node (fn-owner-store state))))))
           :in-theory '(fn-owner-prepare-identity fn-pout-prepare-identity
                        fn-owner-ocfg-of-install-ocfg
                        fn-owner-ocfg-of-retain-carry-put
                        fn-owner-ocfg-of-other-global-put
                        mv-nth nth endp zp car-cons cdr-cons (:e zp)
                        (:e equal) (:e binary-+) (:e unary--)))))

; The preparation interval does not seal. Its completed-cut keeper names
; exactly the seal performed by the already proved identity quantum.
(defthm fn-owner-retain-identity-prepare-keeps-live-after-seal
  (let* ((out (fn-owner-prepare-identity event fn-arena state))
         (word (mv-nth 1 out)))
    (implies (fn-owner-retain-livep state fn-arena)
             (fn-owner-retain-livep (mv-nth 2 out)
               (if (and (consp word) (equal (car word) :seal))
                   (fn-arena-seal-list (cadr word) fn-arena)
                 fn-arena))))
  :hints (("Goal" :use fn-owner-retain-identity-prepare-cut
           :in-theory '(fn-owner-retain-livep))))
(defthm fn-owner-retain-consumer-prepare-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep
            (mv-nth 2 (fn-owner-prepare-consumer event fn-arena state)) fn-arena))
  :hints (("Goal"
           :use (fn-owner-retain-consumer-keeps-retained-state
                 (:instance fn-rfcl-pdc-pout-prepare-consumer-keeps-okp
                      (oc (fn-owner-ocfg state)) (e event)))
           :in-theory '(fn-owner-retain-livep fn-owner-retain-retained-statep
                        fn-owner-prepare-consumer fn-owner-retain-store-projection
                        fn-owner-ocfg-of-install-ocfg
                        mv-nth nth zp endp car-cons cdr-cons (:e zp)
                        (:e binary-+) (:e unary--)))))
(defthm fn-owner-retain-topic-prepare-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep
            (mv-nth 2 (fn-owner-prepare-topic event fn-arena state)) fn-arena))
  :hints (("Goal"
           :use (fn-owner-retain-topic-keeps-retained-state
                 (:instance fn-rfcl-pdc-pout-prepare-topic-keeps-okp
                      (oc (fn-owner-ocfg state)) (e event)))
           :in-theory '(fn-owner-retain-livep fn-owner-retain-retained-statep
                        fn-owner-prepare-topic fn-owner-retain-store-projection
                        fn-owner-ocfg-of-install-ocfg
                        mv-nth nth zp endp car-cons cdr-cons (:e zp)
                        (:e binary-+) (:e unary--)))))

; A23: world-derived returning writers. Deletion debt is explicit below.
(defthm fn-owner-retain-barrier-limits-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-barrier-limits state))))
 :hints (("Goal" :in-theory '(fn-owner-barrier-limits fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-barrier-limits-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-barrier-limits state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-barrier-limits fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-bound-commit-gate-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-bound-commit-gate received group-octets state))))
 :hints (("Goal" :in-theory '(fn-owner-bound-commit-gate fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-bound-commit-gate-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-bound-commit-gate received group-octets state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-bound-commit-gate fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-bp-transit-raw-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-bp-transit-raw state))))
 :hints (("Goal" :in-theory '(fn-owner-bp-transit-raw fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-bp-transit-raw-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-bp-transit-raw state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-bp-transit-raw fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-cat-may-seal-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-cat-may-seal state))))
 :hints (("Goal" :in-theory '(fn-owner-cat-may-seal fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-cat-prepare-sealed-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-cat-prepare-sealed fn-arena fn-cat state))))
 :hints (("Goal" :in-theory '(fn-owner-cat-prepare-sealed fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--) fn-owner-cat-prepare-sealed-produced))))

(defthm fn-owner-retain-catchup-plans-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-catchup-plans state))))
 :hints (("Goal" :in-theory '(fn-owner-catchup-plans fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-catchup-plans-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-catchup-plans state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-catchup-plans fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-cfg-capture-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-cfg-capture state))))
 :hints (("Goal" :in-theory '(fn-owner-cfg-capture fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-checkpoint-clone-phase-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-checkpoint-clone-phase marker-octets state))))
 :hints (("Goal" :in-theory '(fn-owner-checkpoint-clone-phase fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-checkpoint-clone-phase-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-checkpoint-clone-phase marker-octets state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-checkpoint-clone-phase fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-clock-observation-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-clock-observation state))))
 :hints (("Goal" :in-theory '(fn-owner-clock-observation fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-clock-observation-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-clock-observation state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-clock-observation fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-compress-min-octets-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-compress-min-octets state))))
 :hints (("Goal" :in-theory '(fn-owner-compress-min-octets fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-compress-min-octets-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-compress-min-octets state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-compress-min-octets fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-config-generation-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-config-generation state))))
 :hints (("Goal" :in-theory '(fn-owner-config-generation fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-config-generation-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-config-generation state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-config-generation fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-consumer-local-ack-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-consumer-local-ack cursor-octets state))))
 :hints (("Goal" :in-theory '(fn-owner-consumer-local-ack fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-consumer-local-ack-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-consumer-local-ack cursor-octets state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-consumer-local-ack fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-consumer-local-bootstrap-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-consumer-local-bootstrap history incarnation state))))
 :hints (("Goal" :in-theory '(fn-owner-consumer-local-bootstrap fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-consumer-local-bootstrap-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-consumer-local-bootstrap history incarnation state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-consumer-local-bootstrap fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-consumer-local-position-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-consumer-local-position consumer state))))
 :hints (("Goal" :in-theory '(fn-owner-consumer-local-position fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-consumer-local-position-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-consumer-local-position consumer state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-consumer-local-position fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-consumer-local-status-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-consumer-local-status consumer state))))
 :hints (("Goal" :in-theory '(fn-owner-consumer-local-status fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-consumer-local-status-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-consumer-local-status consumer state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-consumer-local-status fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-consumer-local-unregister-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-consumer-local-unregister consumer state))))
 :hints (("Goal" :in-theory '(fn-owner-consumer-local-unregister fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-consumer-local-unregister-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-consumer-local-unregister consumer state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-consumer-local-unregister fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-consumer-local-wait-admit-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-consumer-local-wait-admit waiters state))))
 :hints (("Goal" :in-theory '(fn-owner-consumer-local-wait-admit fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-consumer-local-wait-admit-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-consumer-local-wait-admit waiters state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-consumer-local-wait-admit fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-control-filing-buffer-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-control-filing-buffer group-octets fn-octets state))))
 :hints (("Goal" :in-theory '(fn-owner-control-filing-buffer fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-control-filing-buffer-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-control-filing-buffer group-octets fn-octets state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-control-filing-buffer fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-exposure-install-set-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-exposure-install-set projections state))))
 :hints (("Goal" :in-theory '(fn-owner-exposure-install-set fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-hybrid-current-enrollment-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-hybrid-current-enrollment generation state))))
 :hints (("Goal" :in-theory '(fn-owner-hybrid-current-enrollment fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-hybrid-current-enrollment-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-hybrid-current-enrollment generation state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-hybrid-current-enrollment fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-hybrid-snapshots-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-hybrid-snapshots state))))
 :hints (("Goal" :in-theory '(fn-owner-hybrid-snapshots fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-hybrid-snapshots-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-hybrid-snapshots state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-hybrid-snapshots fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-key-statement-log-line-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-key-statement-log-line plan outcome at-open state))))
 :hints (("Goal" :in-theory '(fn-owner-key-statement-log-line fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-key-statement-log-line-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-key-statement-log-line plan outcome at-open state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-key-statement-log-line fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-key-statement-redecide-log-line-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-key-statement-redecide-log-line plan outcome state))))
 :hints (("Goal" :in-theory '(fn-owner-key-statement-redecide-log-line fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-key-statement-redecide-log-line-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-key-statement-redecide-log-line plan outcome state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-key-statement-redecide-log-line fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-key-statement-request-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-key-statement-request event state))))
 :hints (("Goal" :in-theory '(fn-owner-key-statement-request fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-key-statement-request-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-key-statement-request event state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-key-statement-request fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-live-post-config-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-live-post-config state))))
 :hints (("Goal" :in-theory '(fn-owner-live-post-config fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-live-post-config-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-live-post-config state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-live-post-config fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-log-bounds-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-log-bounds state))))
 :hints (("Goal" :in-theory '(fn-owner-log-bounds fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-log-bounds-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-log-bounds state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-log-bounds fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-log-reopen-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-log-reopen configured handled requested state))))
 :hints (("Goal" :in-theory '(fn-owner-log-reopen fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-log-reopen-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-log-reopen configured handled requested state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-log-reopen fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-login-bindings-plan-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-login-bindings-plan bindings state))))
 :hints (("Goal" :in-theory '(fn-owner-login-bindings-plan fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-login-bindings-plan-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-login-bindings-plan bindings state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-login-bindings-plan fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-login-gate-buffer-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-login-gate-buffer fn-octets state))))
 :hints (("Goal" :in-theory '(fn-owner-login-gate-buffer fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-moderation-plan-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-moderation-plan op login id reason fn-arena state))))
 :hints (("Goal" :in-theory '(fn-owner-moderation-plan fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-moderation-plan-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-moderation-plan op login id reason fn-arena state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-moderation-plan fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-next-store-coordinates-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-next-store-coordinates state))))
 :hints (("Goal" :in-theory '(fn-owner-next-store-coordinates fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-next-store-coordinates-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-next-store-coordinates state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-next-store-coordinates fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-next-txid-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-next-txid state))))
 :hints (("Goal" :in-theory '(fn-owner-next-txid fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-next-txid-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-next-txid state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-next-txid fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-operator-refusal-reason-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-operator-refusal-reason msgid-octets group-octets payload fn-arena state))))
 :hints (("Goal" :in-theory '(fn-owner-operator-refusal-reason fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-operator-refusal-reason-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-operator-refusal-reason msgid-octets group-octets payload fn-arena state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-operator-refusal-reason fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-peer-carrier-form-buffer-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-peer-carrier-form-buffer fn-octets state))))
 :hints (("Goal" :in-theory '(fn-owner-peer-carrier-form-buffer fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-peer-carrier-form-buffer-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-peer-carrier-form-buffer fn-octets state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-peer-carrier-form-buffer fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-pending-sequence-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-pending-sequence state))))
 :hints (("Goal" :in-theory '(fn-owner-pending-sequence fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-pending-sequence-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-pending-sequence state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-pending-sequence fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-prov-post-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-prov-post state))))
 :hints (("Goal" :in-theory '(fn-owner-prov-post fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-prov-post-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-prov-post state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-prov-post fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-pull-plans-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-pull-plans state))))
 :hints (("Goal" :in-theory '(fn-owner-pull-plans fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-pull-plans-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-pull-plans state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-pull-plans fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-queue-head-served-p-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-queue-head-served-p state))))
 :hints (("Goal" :in-theory '(fn-owner-queue-head-served-p fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-queue-head-served-p-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-queue-head-served-p state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-queue-head-served-p fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-served-carried-word-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-served-carried-word word detail state))))
 :hints (("Goal" :in-theory '(fn-owner-served-carried-word fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-served-carried-word-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-served-carried-word word detail state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-served-carried-word fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-served-post-word-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-served-post-word word detail state))))
 :hints (("Goal" :in-theory '(fn-owner-served-post-word fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-served-post-word-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-served-post-word word detail state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-served-post-word fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-set-auth-config-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-set-auth-config acfg state))))
 :hints (("Goal" :in-theory '(fn-owner-set-auth-config fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-set-auth-config-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-set-auth-config acfg state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-set-auth-config fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-snapshot-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-snapshot state))))
 :hints (("Goal" :in-theory '(fn-owner-snapshot fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-snapshot-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-snapshot state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-snapshot fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-space-need-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-space-need state))))
 :hints (("Goal" :in-theory '(fn-owner-space-need fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-space-need-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-space-need state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-space-need fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-stamp-status-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-stamp-status state))))
 :hints (("Goal" :in-theory '(fn-owner-stamp-status fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-stamp-status-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-stamp-status state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-stamp-status fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-statement-fence-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-statement-fence event state))))
 :hints (("Goal" :in-theory '(fn-owner-statement-fence fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-statement-fence-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-statement-fence event state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-statement-fence fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-topic-propose-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-topic-propose operation source-sequence observed-uid entropy-id quota state))))
 :hints (("Goal" :in-theory '(fn-owner-topic-propose fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-topic-propose-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-topic-propose operation source-sequence observed-uid entropy-id quota state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-topic-propose fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-transit-evidence-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-transit-evidence state))))
 :hints (("Goal" :in-theory '(fn-owner-transit-evidence fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-transit-evidence-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-transit-evidence state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-transit-evidence fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-transit-log-line-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-transit-log-line id kind reason word detail verdict state))))
 :hints (("Goal" :in-theory '(fn-owner-transit-log-line fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-transit-reason-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-transit-reason state))))
 :hints (("Goal" :in-theory '(fn-owner-transit-reason fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-transit-reason-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-transit-reason state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-transit-reason fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-transit-verdict-buffer-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-transit-verdict-buffer transitp ed ml fn-octets state))))
 :hints (("Goal" :in-theory '(fn-owner-transit-verdict-buffer fn-owner-retain-retained-statep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-transit-verdict-buffer-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-transit-verdict-buffer transitp ed ml fn-octets state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-transit-verdict-buffer fn-owner-retain-livep-of-other-global-put
                  mv-nth nth car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-apply-limit-profile-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-apply-limit-profile values state))))
:hints (("Goal"
           :use ((:instance fn-ohr-osb-install-preserves-carried-relation
                            (oc (fn-owner-ocfg state)) (profile values)))
           :in-theory
           '(fn-owner-apply-limit-profile fn-owner-replace-core fn-owner-ocfg
             fn-owner-core-is-configured-owner-by-definition
             fn-owner-retain-retained-statep fn-owner-retain-statep
             fn-owner-retain-retained-statep-of-install-ocfg fn-owner-retain-retained-statep-of-other-global-put
             fn-owner-retain-store-projection fn-owner-retain-lgoc-owner-shape
             fn-sbud-oc-store fn-ocfg-with-owner fn-ocfg-owner-of-fn-ocfg-make
             fn-ohr-osb-install-keeps-control
             mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-close-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-close id fn-arena state))))
 :hints (("Goal" :use (fn-owner-retain-statep-implies-lgoc (:instance fn-ohr-step-close-preserves-carried-relation (oc (fn-owner-ocfg state))) (:instance fn-ohr-close-keeps-store (oc (fn-owner-ocfg state))) (:instance fn-owner-callback-close-branch-unfolds (oc (fn-owner-ocfg state)))) :in-theory '(fn-owner-close fn-owner-callback-close fn-owner-callback-install-effects fn-owner-install-served-effects fn-owner-put-credits fn-owner-retain-retained-statep fn-owner-retain-statep fn-owner-retain-store-projection fn-owner-retain-retained-statep-of-other-global-put fn-owner-retain-retained-statep-of-install-ocfg fn-sbud-oc-store fn-owner-ocfg-of-other-global-put mv-nth nth zp car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-close-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-close id fn-arena state)) fn-arena))
 :hints (("Goal" :use (fn-owner-retain-statep-implies-lgoc (:instance fn-ohr-step-close-preserves-carried-relation (oc (fn-owner-ocfg state))) (:instance fn-ohr-close-keeps-store (oc (fn-owner-ocfg state))) (:instance fn-owner-callback-close-branch-unfolds (oc (fn-owner-ocfg state)))) :in-theory '(fn-owner-close fn-owner-callback-close fn-owner-callback-install-effects fn-owner-install-served-effects fn-owner-put-credits fn-owner-retain-livep fn-owner-retain-statep fn-owner-retain-store-projection fn-owner-retain-livep-of-other-global-put fn-owner-retain-livep-of-install-frame fn-sbud-oc-store fn-owner-ocfg-of-other-global-put mv-nth nth zp car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-fault-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-fault id state))))
 :hints (("Goal" :use (fn-owner-retain-statep-implies-lgoc (:instance fn-ohr-fault-preserves-carried-relation (oc (fn-owner-ocfg state))) (:instance fn-ohr-fault-keeps-store (oc (fn-owner-ocfg state)))) :in-theory '(fn-owner-fault fn-owner-callback-fault fn-owner-callback-install-effects fn-owner-install-served-effects fn-owner-put-credits fn-owner-retain-retained-statep fn-owner-retain-statep fn-owner-retain-store-projection fn-owner-retain-retained-statep-of-other-global-put fn-owner-retain-retained-statep-of-install-ocfg fn-sbud-oc-store fn-owner-ocfg-of-other-global-put mv-nth nth zp car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-fault-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-fault id state)) fn-arena))
 :hints (("Goal" :use (fn-owner-retain-statep-implies-lgoc (:instance fn-ohr-fault-preserves-carried-relation (oc (fn-owner-ocfg state))) (:instance fn-ohr-fault-keeps-store (oc (fn-owner-ocfg state)))) :in-theory '(fn-owner-fault fn-owner-callback-fault fn-owner-callback-install-effects fn-owner-install-served-effects fn-owner-put-credits fn-owner-retain-livep fn-owner-retain-statep fn-owner-retain-store-projection fn-owner-retain-livep-of-other-global-put fn-owner-retain-livep-of-install-frame fn-sbud-oc-store fn-owner-ocfg-of-other-global-put mv-nth nth zp car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-install-node-secret-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-install-node-secret ring state))))
:hints (("Goal"
           :use ((:instance fn-ohr-with-node-secret-preserves-carried-relation
                            (oc (fn-owner-ocfg state)) (secret ring)))
           :in-theory
           '(fn-owner-install-node-secret fn-owner-replace-core fn-owner-ocfg
             fn-owner-core-is-configured-owner-by-definition
             fn-owner-retain-retained-statep fn-owner-retain-statep
             fn-owner-retain-retained-statep-of-install-ocfg fn-owner-retain-store-projection
             fn-sbud-oc-store fn-ocfg-with-owner fn-own-with-node-secret
             fn-ocfg-owner-of-fn-ocfg-make fn-own-store-of-fn-own-make
             mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-observe-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-observe monotonic wall wall-error has-wall state))))
:hints (("Goal" :in-theory
           '(fn-owner-observe fn-owner-retain-retained-statep fn-owner-retain-statep
             fn-owner-retain-retained-statep-of-install-ocfg fn-owner-retain-store-projection
             fn-owner-retain-observe-model-frame
             mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-open-peer-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-open-peer peer-octets state))))
 :hints (("Goal" :use (fn-owner-retain-statep-implies-lgoc (:instance fn-ohr-open-peer-preserves-carried-relation (oc (fn-owner-ocfg state)) (peer (fn-store-octets->string peer-octets)) (acfg (fn-owner-auth state))) (:instance fn-ohr-open-peer-keeps-store-and-view (oc (fn-owner-ocfg state)) (peer (fn-store-octets->string peer-octets)) (acfg (fn-owner-auth state)))) :in-theory '(fn-owner-open-peer fn-owner-callback-open-peer fn-owner-callback-install-effects fn-owner-install-served-effects fn-owner-put-credits fn-owner-retain-retained-statep fn-owner-retain-statep fn-owner-retain-store-projection fn-owner-retain-retained-statep-of-other-global-put fn-owner-retain-retained-statep-of-install-ocfg fn-sbud-oc-store fn-owner-ocfg-of-other-global-put mv-nth nth zp car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-open-peer-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-open-peer peer-octets state)) fn-arena))
 :hints (("Goal" :use (fn-owner-retain-statep-implies-lgoc (:instance fn-ohr-open-peer-preserves-carried-relation (oc (fn-owner-ocfg state)) (peer (fn-store-octets->string peer-octets)) (acfg (fn-owner-auth state))) (:instance fn-ohr-open-peer-keeps-store-and-view (oc (fn-owner-ocfg state)) (peer (fn-store-octets->string peer-octets)) (acfg (fn-owner-auth state)))) :in-theory '(fn-owner-open-peer fn-owner-callback-open-peer fn-owner-callback-install-effects fn-owner-install-served-effects fn-owner-put-credits fn-owner-retain-livep fn-owner-retain-statep fn-owner-retain-store-projection fn-owner-retain-livep-of-other-global-put fn-owner-retain-livep-of-install-frame fn-sbud-oc-store fn-owner-ocfg-of-other-global-put mv-nth nth zp car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-reconfigure-unstage-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-reconfigure-unstage state))))
:hints (("Goal" :use ((:instance fn-psrv-unstage-preserves-invariant
                                  (oc (fn-owner-ocfg state))))
           :in-theory
           '(fn-owner-reconfigure-unstage fn-owner-authority-proposal-clear
             fn-owner-retain-retained-statep fn-owner-retain-statep
             fn-owner-retain-retained-statep-of-install-ocfg fn-owner-retain-retained-statep-of-other-global-put
             fn-owner-ocfg-of-other-global-put fn-owner-retain-store-projection
             fn-psrv-unstage fn-sbud-oc-store fn-ocfg-owner-of-fn-ocfg-make
             mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-reconfigure-unstage-keeps-live
  (implies (fn-owner-retain-livep state fn-arena)
           (fn-owner-retain-livep (mv-nth 2 (fn-owner-reconfigure-unstage state)) fn-arena))
:hints (("Goal" :use ((:instance fn-psrv-unstage-preserves-invariant
                                  (oc (fn-owner-ocfg state))))
           :in-theory
           '(fn-owner-reconfigure-unstage fn-owner-authority-proposal-clear
             fn-owner-retain-livep fn-owner-retain-statep
             fn-owner-retain-livep-of-install-frame fn-owner-retain-livep-of-other-global-put
             fn-owner-ocfg-of-other-global-put fn-owner-retain-store-projection
             fn-psrv-unstage fn-sbud-oc-store fn-ocfg-owner-of-fn-ocfg-make
             mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--)))))







; Strengthened preservation for the existing served row, with the same writers.
(local
 (defthm fn-owner-retain-refuse-model-retained
   (let* ((out (fn-pout-refuse-reservation oc fn-arena))
          (s (fn-sbud-oc-store oc)) (next (fn-sbud-oc-store (mv-nth 1 out))))
     (implies (and (fn-lgoc-invariantp oc) (fn-osr-retainedp s))
              (fn-osr-retainedp next)))
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

(local (defthm fn-owner-retain-io-retained-without-arena
  (implies (fn-owner-retain-retained-statep state)
    (fn-osr-retainedp (fn-owner-store (mv-nth 2 (fn-owner-io op result state)))))
  :hints (("Goal" :in-theory
           '(fn-owner-retain-retained-statep fn-owner-retain-statep fn-owner-io fn-owner-io-safep
             fn-olr-ocfg-reserve fn-olr-ocfg-order
             fn-owner-retain-rcon-io-keeps-retained fn-psrv-rcon-io-preserves-invariant
             fn-psrv-io-safep fn-cstp-reserve-opp fn-lgoc-log-reserve-preserves-invariant
             fn-psrv-log-order-preserves-invariant
             fn-owner-retain-store-projection fn-owner-ocfg-of-install-ocfg
             member-equal mv-nth nth endp zp car-cons cdr-cons
             (:e member-equal) (:e equal) (:e zp) (:e binary-+) (:e unary--))))))

(defthm fn-owner-retain-refuse-reservation-keeps-retained-state
 (implies (fn-owner-retain-retained-statep state)
          (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-refuse-reservation fn-arena state))))
 :hints (("Goal" :use (fn-owner-refuse-reservation-preserves-retain-state (:instance fn-owner-retain-refuse-model-retained (oc (fn-owner-ocfg state))) fn-owner-retain-statep-implies-lgoc)
 :in-theory '(fn-owner-retain-retained-statep fn-owner-retain-statep fn-owner-refuse-reservation
  fn-owner-retain-store-projection fn-owner-ocfg-of-install-ocfg fn-owner-ocfg-of-other-global-put
  mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e equal) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-known-abort-keeps-retained-state
 (implies (fn-owner-retain-retained-statep state)
          (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-known-abort fn-arena state))))
 :hints (("Goal" :use (fn-owner-known-abort-preserves-retain-state fn-owner-retain-known-abort-retained fn-owner-retain-statep-implies-lgoc)
 :in-theory '(fn-owner-retain-retained-statep fn-owner-retain-statep fn-owner-known-abort
  fn-owner-retain-store-projection fn-owner-ocfg-of-install-ocfg fn-owner-ocfg-of-other-global-put
  mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e equal) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-io-keeps-retained-state
 (implies (fn-owner-retain-retained-statep state)
          (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-io op result state))))
 :hints (("Goal" :use ((:instance fn-owner-io-preserves-retain-state (operation op)) fn-owner-retain-io-retained-without-arena fn-owner-retain-statep-implies-lgoc)
 :in-theory '(fn-owner-retain-retained-statep fn-owner-retain-statep fn-owner-io
  fn-owner-retain-store-projection fn-owner-ocfg-of-install-ocfg fn-owner-ocfg-of-other-global-put
  mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e equal) (:e binary-+) (:e unary--)))))

(local
 (defthm fn-owner-retain-rcon-io-keeps-rfcl
  (implies (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc))) (fn-rfcl-okp (fn-own-store (fn-ocfg-owner oc)) fn-arena))
           (fn-rfcl-okp (fn-own-store (fn-ocfg-owner (fn-rcon-ocfg-io oc operation result))) fn-arena))
  :hints (("Goal" :use ((:instance fn-rfcl-io-keeps-okp (s (fn-own-store (fn-ocfg-owner oc)))))
           :in-theory '(fn-sbud-oc-store fn-lgoc-store-of-rcon-io)))))

(defthm fn-owner-retain-io-keeps-live
 (implies (fn-owner-retain-livep state fn-arena)
          (fn-owner-retain-livep (mv-nth 2 (fn-owner-io op result state)) fn-arena))
 :hints (("Goal" :use ((:instance fn-owner-io-preserves-retain-state (operation op)) fn-owner-retain-io-keeps-retained-store fn-owner-retain-statep-implies-entry-guard)
 :in-theory '(fn-owner-retain-livep fn-owner-io fn-owner-io-safep fn-olr-ocfg-reserve fn-olr-ocfg-order
  fn-owner-retain-rcon-io-keeps-rfcl fn-rcon-ocfg-io-keeps-the-store-a-state
  fn-sbud-oc-store fn-owner-retain-store-projection fn-owner-ocfg-of-install-ocfg
  member-equal mv-nth nth endp zp car-cons cdr-cons (:e member-equal) (:e zp) (:e equal) (:e binary-+) (:e unary--)))))

(local (defthm fn-owner-retain-step-take-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (fn-owner-step (list :take) fn-arena state)))
  :hints (("Goal" :use ((:instance fn-ohr-step-take-preserves-carried-relation
                                  (oc (fn-owner-ocfg state))))
           :in-theory
           '(fn-owner-step fn-owner-retain-retained-statep fn-owner-retain-statep
             fn-owner-retain-retained-statep-of-install-ocfg fn-owner-retain-store-projection
             fn-owner-retain-step-take-store-frame)))))

(defthm fn-owner-retain-take-keeps-retained-state
 (implies (fn-owner-retain-retained-statep state) (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-take fn-arena state))))
 :hints (("Goal" :in-theory '(fn-owner-take fn-owner-put-credits fn-owner-retain-retained-statep-of-other-global-put
   fn-owner-retain-step-take-keeps-retained-state mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e equal) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-take-keeps-live
 (implies (fn-owner-retain-livep state fn-arena) (fn-owner-retain-livep (mv-nth 2 (fn-owner-take fn-arena state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-take fn-owner-put-credits fn-owner-retain-livep-of-other-global-put
   fn-owner-retain-step-take-keeps-live mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e equal) (:e binary-+) (:e unary--)))))

(local (defthm fn-owner-retain-step-control-submit-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (fn-owner-step (list :control-submit msgid groups octets) fn-arena state)))
  :hints (("Goal" :use ((:instance fn-ohr-step-control-submit-preserves-carried-relation
                                  (oc (fn-owner-ocfg state))))
           :in-theory
           '(fn-owner-step fn-owner-retain-retained-statep fn-owner-retain-statep
             fn-owner-retain-retained-statep-of-install-ocfg fn-owner-retain-store-projection
             fn-owner-retain-step-control-submit-store-frame)))))

(defthm fn-owner-retain-control-submit-keeps-retained-state
 (implies (fn-owner-retain-retained-statep state) (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-control-submit msgid-octets group-octets payload fn-arena state))))
 :hints (("Goal" :in-theory '(fn-owner-control-submit fn-owner-put-credits fn-owner-retain-retained-statep-of-other-global-put
   fn-owner-retain-step-control-submit-keeps-retained-state mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e equal) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-control-submit-keeps-live
 (implies (fn-owner-retain-livep state fn-arena) (fn-owner-retain-livep (mv-nth 2 (fn-owner-control-submit msgid-octets group-octets payload fn-arena state)) fn-arena))
 :hints (("Goal" :in-theory '(fn-owner-control-submit fn-owner-put-credits fn-owner-retain-livep-of-other-global-put
   fn-owner-retain-step-control-submit-keeps-live mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e equal) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-install-effects-keeps-retained-state
  (implies (fn-owner-retain-retained-statep state)
           (fn-owner-retain-retained-statep (fn-owner-install-effects effects state)))
  :hints (("Goal" :in-theory
           '(fn-owner-install-effects fn-owner-callback-install-effects fn-owner-install-served-effects fn-owner-retain-retained-statep-of-other-global-put
             mv-nth nth endp zp car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--)))))

(local
 (defthm fn-owner-retain-retention-not-topic
   (implies (fn-store-retention-event-p e) (not (fn-th-topic-eventp e)))
   :hints (("Goal" :use ((:instance fn-th-topic-event-has-topic-tag (event e)))
            :in-theory '(fn-store-retention-event-p fn-store-event-nth nth zp car-cons cdr-cons
                         member-equal (:e member-equal) (:e equal) (:e zp)
                         (:e binary-+) (:e unary--))))))

(local
 (defthm fn-owner-retain-pdc-retention-view-frame
   (equal (fn-osr-retained-view (fn-pdc-sn-prepare-retention s e)) (fn-osr-retained-view s))
   :hints (("Goal" :in-theory '(fn-osr-retained-view fn-pdc-sn-prepare-retention
              fn-cstp-sn-update-fields fn-owner-retain-update-selectors
              fn-pcar-stage-record fn-sf-records-of-fn-sf-make-fields-kept
              car-cons cdr-cons)))))

(local
 (defthm fn-owner-retain-pdc-retention-keeps-cursor
   (implies (fn-sn-identity-sequencep s)
            (fn-sn-identity-sequencep (fn-pdc-sn-prepare-retention s e)))
   :hints (("Goal" :in-theory
     (union-theories (theory 'minimal-theory)
       '(fn-pdc-sn-prepare-retention fn-sn-identity-sequencep fn-pcar-stage-record
         fn-cstp-sn-update-fields fn-owner-retain-update-selectors
         fn-sf-records-of-fn-sf-make-fields-kept fn-sf-scalars-of-fn-sf-make-fields
         fn-sf-completion-phasep natp member-equal car-cons cdr-cons
         (:e member-equal) (:e equal)))))))

(local
 (defthm fn-owner-retain-pdc-retention-keeps-retained
   (implies (and (fn-osr-retainedp s) (fn-cst-relation (fn-pdc-sn-prepare-retention s e)))
            (fn-osr-retainedp (fn-pdc-sn-prepare-retention s e)))
   :hints (("Goal"
            :use (fn-owner-retain-pdc-retention-keeps-cursor
                  fn-owner-retain-retention-not-topic
                  (:instance fn-osr-retained-view-connects-full-carry
                       (a s) (b (fn-pdc-sn-prepare-retention s e)))
                  (:instance fn-cstp-relation-is-statep (st (fn-pdc-sn-prepare-retention s e))))
            :in-theory '(fn-owner-retain-pdc-retention-view-frame fn-pdc-sn-prepare-retention
              fn-osr-retainedp fn-osr-livep fn-sti-livep fn-csi-livep
              fn-sti-completed-prefixp fn-csi-completed-prefixp fn-csi-completion-lastp
              fn-osr-identity-prefixp fn-sn-identity-context
              fn-cstp-sn-update-fields fn-owner-retain-update-selectors fn-pcar-stage-record
              fn-sf-records-of-fn-sf-make-fields-kept fn-sf-scalars-of-fn-sf-make-fields
              fn-sf-completion-phasep fn-ccar-cpe-projection-step-is-cpe-projection-step
              member-equal car-cons cdr-cons
              (:e member-equal) (:e equal))))) )

(local
 (defthm fn-owner-retain-pdc-pout-retention-keeps-retained
   (implies (and (fn-lgoc-invariantp oc) (fn-osr-retainedp (fn-sbud-oc-store oc)))
            (fn-osr-retainedp (fn-sbud-oc-store
              (mv-nth 1 (fn-pdc-pout-prepare-retention oc e)))))
   :hints (("Goal"
            :use ((:instance fn-pdc-store-of-owner-prepares)
                  (:instance fn-pdc-ocfg-prepare-retention-preserves-invariant)
                  (:instance fn-lgoc-ocl-relation-cst (oc (fn-pdc-ocfg-prepare-retention oc e)))
                  (:instance fn-owner-retain-pdc-retention-keeps-retained
                       (s (fn-sbud-oc-store oc))))
            :in-theory '(fn-pdc-pout-prepare-retention fn-lgoc-invariantp
              fn-sbud-oc-store mv-nth nth zp endp car-cons cdr-cons
              (:e zp) (:e binary-+) (:e unary--))))) )

(local
 (defthm fn-owner-retain-idrp-keeps-retained
  (implies (and (fn-lgoc-invariantp oc) (fn-osr-retainedp (fn-sbud-oc-store oc)))
           (fn-osr-retainedp (fn-sbud-oc-store (mv-nth 1 (fn-idrp-prepare-retention oc event grant fn-arena)))))
  :hints (("Goal" :use ((:instance fn-owner-retain-pdc-pout-retention-keeps-retained (e event)))
           :in-theory '(fn-idrp-prepare-retention mv-nth nth endp zp car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--))))))

(defthm fn-owner-retain-prepare-retention-keeps-retained-state
 (implies (fn-owner-retain-retained-statep state) (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-prepare-retention kind id-octets subject-octets evidence-octets charge fn-arena state))))
 :hints (("Goal" :use (fn-owner-prepare-retention-preserves-retain-state fn-owner-retain-statep-implies-lgoc)
 :in-theory '(fn-owner-retain-retained-statep fn-owner-retain-statep fn-owner-prepare-retention fn-owner-retain-idrp-keeps-retained fn-owner-idrp-install-preserves-lgoc
  fn-owner-retain-store-projection fn-owner-ocfg-of-install-ocfg fn-owner-ocfg-of-other-global-put
  fn-owner-retain-retained-statep-of-other-global-put fn-owner-retain-livep-of-other-global-put
  fn-rfcl-idrp-prepare-retention-keeps-okp mv-nth nth endp zp car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(defthm fn-owner-retain-prepare-retention-keeps-live
 (implies (fn-owner-retain-livep state fn-arena) (fn-owner-retain-livep (mv-nth 2 (fn-owner-prepare-retention kind id-octets subject-octets evidence-octets charge fn-arena state)) fn-arena))
 :hints (("Goal" :use (fn-owner-prepare-retention-preserves-retain-state fn-owner-retain-statep-implies-lgoc (:instance fn-rfcl-idrp-prepare-retention-keeps-okp (oc (fn-owner-ocfg state)) (event (fn-store-retention-event-make kind (fn-sn-identity-next (fn-owner-store state)) (fn-state-next-txid (fn-node-acceptance (fn-sn-node (fn-owner-store state)))) (fn-state-next-txid (fn-node-acceptance (fn-sn-node (fn-owner-store state)))) (fn-store-octets->string id-octets) (fn-store-octets->string subject-octets) (fn-store-octets->string evidence-octets) charge))))
 :in-theory '(fn-owner-retain-livep fn-owner-retain-statep fn-owner-prepare-retention fn-owner-retain-idrp-keeps-retained fn-owner-idrp-install-preserves-lgoc
  fn-owner-retain-store-projection fn-owner-ocfg-of-install-ocfg fn-owner-ocfg-of-other-global-put
  fn-owner-retain-retained-statep-of-other-global-put fn-owner-retain-livep-of-other-global-put
  fn-rfcl-idrp-prepare-retention-keeps-okp mv-nth nth endp zp car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

(local
 (defthm fn-owner-retain-sn-known-abort-keeps-rfcl
  (implies (fn-rfcl-okp s fn-arena)
           (fn-rfcl-okp (fn-sn-known-abort s) fn-arena))
  :hints (("Goal" :cases ((fn-sn-known-abort-enabledp s))
    :use ((:instance rfcl-abort-restores-records-okp (next s)))
    :in-theory '(fn-sn-known-abort)))))

(defthm fn-owner-retain-known-abort-keeps-live
 (implies (fn-owner-retain-livep state fn-arena)
          (fn-owner-retain-livep (mv-nth 2 (fn-owner-known-abort fn-arena state)) fn-arena))
 :hints (("Goal"
  :use (fn-owner-known-abort-preserves-retain-state fn-owner-retain-known-abort-retained
        fn-owner-retain-statep-implies-lgoc
        (:instance fn-owner-retain-sn-known-abort-keeps-rfcl (s (fn-owner-store state)))
        (:instance fn-pout-store-of-store-step (oc (fn-owner-ocfg state)) (ev (list :known-abort))))
  :in-theory '(fn-owner-retain-livep fn-owner-retain-statep fn-owner-known-abort fn-pout-known-abort
     fn-owner-retain-store-projection fn-owner-ocfg-of-install-ocfg fn-owner-ocfg-of-other-global-put
     fn-snrt-step fn-sbud-oc-store fn-lgoc-invariantp
     mv-nth nth endp zp car-cons cdr-cons (:e equal) (:e zp) (:e binary-+) (:e unary--)))))

; DEF-CARRIED instantiates by the writer's actual formal names.
(defthm fn-owner-retain-io-preserves-retained-state
 (implies (fn-owner-retain-retained-statep state)
          (fn-owner-retain-retained-statep (mv-nth 2 (fn-owner-io operation result state))))
 :hints (("Goal" :use ((:instance fn-owner-retain-io-keeps-retained-state (op operation)))
          :in-theory nil)))

(in-theory (disable fn-owner-retain-livep fn-owner-retain-identity-quantum))
