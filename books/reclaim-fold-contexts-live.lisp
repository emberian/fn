; Carry the open's reclaim fold-context premise through live reference entries
; and their atomic payload seals to the reclaim capture (Builder L14).
; The served POST is host/owner-host.lisp fn-owner-prepare-buffer: its row is
; fn-apc-intern-row-at (fn-intern-row-at under fn-apc-p,
; fn-apc-intern-row-at-is-reference) and its prepare
; fn-ppc-pout-prepare-article-cat, equal to fn-pout-prepare-article under
; fn-ocl-relation and fn-scj-invp (fn-ppc-pout-prepare-article-cat-of-live-
; owner, books/post-prepare-catalog.lisp).  The host then either seals the
; payload once (LV-2h) or, when the catalog's may-seal gate refuses, aborts
; the staged row unsealed (host/native/owner.lisp:3562, LV-2k).
; LV-4 and LV-4e cover the served carried deferred prepares and their
; grant/outcome entries. LV-2c/LV-3c restore the invariant after a valid-
; choice fn-sn-crash in the unsealed prepare interval, before seal or abort.
; LV-6 covers fn-sn-crash's choices only, not the separate rollback
; constructors.  fn-sn-set-keyring is outside the native composition
; (books/catalog-commit.lisp:751).
; The lift into fn-owner-retain-statep's carry is the named adapter
; RFCL-OWNER-RETAIN-LIFT (owner builder-L), retired by A's
; owner-retain-state transition-preservation landing.
(in-package "ACL2")
(include-book "reclaim-fold-contexts")
(include-book "owner-cursor-domain")
(include-book "owner-identity-prepare")

(local (in-theory (disable (tau-system))))


(defun fn-rfcl-pending-phasep (p)
  (declare (xargs :guard t))
  (and (member-equal p '(:record-staged :record-data-durable :record-attempted :fenced-record)) t))

(defun fn-rfcl-rows (s)
  (declare (xargs :guard t :verify-guards nil))
  (let ((f (fn-sn-files s)))
    (if (fn-rfcl-pending-phasep (fn-sf-phase f))
        (append (fn-sf-records f) (list (fn-sf-record-candidate f)))
      (fn-sf-records f))))

(defun fn-rfcl-okp (s fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (and (fn-rows-handles-inp (fn-rfcl-rows s) fn-arena)
       (fn-orcr-fold-contexts-okp (fn-rfcl-rows s) (fn-stxk-initial-context 0)
                                  (fn-arena-count fn-arena) fn-arena)))

(local
 (defthm rfcl-lv0
  (implies (and (fn-rfcl-okp s fn-arena)
                (not (fn-rfcl-pending-phasep (fn-sf-phase (fn-sn-files s)))))
           (fn-orcr-fold-contexts-okp (fn-sf-records (fn-sn-files s))
                                      (fn-stxk-initial-context 0)
                                      (fn-arena-count fn-arena) fn-arena))
  :hints (("Goal" :in-theory '(fn-rfcl-okp fn-rfcl-rows)))))

(local
 (defthm rfcl-lv1
  (fn-rfcl-okp (fn-sn-initial groups capacity) fn-arena)
  :hints (("Goal" :in-theory (enable fn-rfcl-okp fn-rfcl-rows fn-rfcl-pending-phasep
                                    fn-sn-initial fn-sn-make-v2 fn-sn-files fn-store-event-nth
                                    fn-sf-initial-state)))))

(local
 (defthm rfcl-handles-append
  (equal (fn-rows-handles-inp (append a b) fn-arena)
         (and (fn-rows-handles-inp a fn-arena) (fn-rows-handles-inp b fn-arena)))
  :hints (("Goal" :induct (append a b)
           :in-theory (e/d (fn-rows-handles-inp append)
                            (fn-held-p fn-hstxa-p fn-row-handle-inp))))))

(local
 (defun rfcl-after (rows id h)
  (declare (xargs :verify-guards nil))
  (if (atom rows) (mv id h)
    (let* ((w (car rows)) (seed (fn-ssr-seed id))
           (row (if (fn-record-p w) (fn-intern-row-at w (fn-ssr-at 1 seed) (fn-ssr-at 2 seed) h) w)))
      (rfcl-after (cdr rows) (fn-replay-identity-loop (list row) id)
                  (if (fn-record-p w) (+ 1 h) h))))))

(local
 (defthm rfcl-fold-append
  (equal (fn-orcr-fold-contexts-okp (append a b) id h fn-arena)
         (and (fn-orcr-fold-contexts-okp a id h fn-arena)
              (fn-orcr-fold-contexts-okp b (mv-nth 0 (rfcl-after a id h))
                                         (mv-nth 1 (rfcl-after a id h)) fn-arena)))
  :hints (("Goal" :induct (rfcl-after a id h)
           :in-theory (union-theories
              '(rfcl-after fn-orcr-fold-contexts-okp append (:induction rfcl-after) natp not car-cons cdr-cons cons-equal mv-nth nth zp (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart unary--) (:executable-counterpart member-equal) member-equal)
              (theory 'minimal-theory))))))

(local
 (defthm rfcl-handles-seal
  (implies (fn-rows-handles-inp rows fn-arena)
           (fn-rows-handles-inp rows (fn-arena-seal-list p fn-arena)))
  :hints (("Goal" :induct (fn-rows-handles-inp rows fn-arena)
           :in-theory (e/d (fn-rows-handles-inp fn-row-handle-inp)
                            (fn-held-p fn-hstxa-p fn-arena-seal-list-is-append
                             fn-arena-count-is-len))))))

(local
 (defthm rfcl-fold-seal
  (implies (and (fn-rows-handles-inp rows fn-arena)
                (fn-orcr-fold-contexts-okp rows id h fn-arena))
           (fn-orcr-fold-contexts-okp rows id h (fn-arena-seal-list p fn-arena)))
  :hints (("Goal" :induct (fn-orcr-fold-contexts-okp rows id h fn-arena)
           :in-theory (union-theories
              '(fn-orcr-fold-contexts-okp fn-rows-handles-inp fn-row-handle-inp fn-row-bytes fn-orcr-retained-p fn-orcr-held-part fn-arena-seal-keeps-sealed fn-arena-seal-count (:type-prescription fn-arena-count) fn-cstp-held-kind-facts fn-hstxa-is-not-held natp not car-cons cdr-cons cons-equal mv-nth nth zp (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart unary--) (:executable-counterpart member-equal) member-equal)
              (theory 'minimal-theory))))))

(local
 (defthm rfcl-lv5
  (implies (fn-rfcl-okp s fn-arena)
           (fn-rfcl-okp s (fn-arena-seal-list p fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-rfcl-okp)
                               (fn-rfcl-rows fn-orcr-fold-contexts-okp fn-rows-handles-inp))
           :use ((:instance fn-rfc-fold-contexts-okp-any-handle
                            (rows (fn-rfcl-rows s)) (id (fn-stxk-initial-context 0))
                            (h1 (fn-arena-count (fn-arena-seal-list p fn-arena)))
                            (h2 (fn-arena-count fn-arena))
                            (fn-arena (fn-arena-seal-list p fn-arena))))))))

(local
 (defthm rfcl-event-nonheld
  (implies (or (fn-store-retention-event-p event) (fn-cpe-eventp event) (fn-th-topic-eventp event))
           (not (fn-orcr-retained-p event)))
  :hints (("Goal" :use ((:instance fn-held-is-no-wire-event (x event))
                         fn-hls-retained-kind4-disjoint-from-other-store-events)
           :in-theory '(fn-orcr-retained-p)))))

(local
 (defthm rfcl-nonheld-append
  (implies (and (not (fn-orcr-retained-p event))
                (fn-rows-handles-inp rows fn-arena)
                (fn-orcr-fold-contexts-okp rows id h fn-arena))
           (and (fn-rows-handles-inp (append rows (list event)) fn-arena)
                (fn-orcr-fold-contexts-okp (append rows (list event)) id h fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-rows-handles-inp fn-orcr-retained-p)
                                 (fn-held-p fn-hstxa-p fn-record-p fn-intern-row-at
                                  fn-ssr-seed fn-ssr-at fn-row-bytes fn-held-context-of
                                  fn-replay-identity-loop))
           :expand ((:free (ctx count) (fn-orcr-fold-contexts-okp (list event) ctx count fn-arena))
                    (:free (ctx count) (fn-orcr-fold-contexts-okp nil ctx count fn-arena)))))))

(local
 (defthm rfcl-stage-nonheld
  (implies (and (fn-rfcl-okp s fn-arena)
                (equal (fn-sf-phase (fn-sn-files s)) :reserved)
                (not (fn-orcr-retained-p event)))
           (fn-rfcl-okp
            (fn-sn-update s (fn-pcar-stage-record (fn-sn-files s) event) node)
            fn-arena))
  :hints (("Goal" :in-theory (union-theories
    '(fn-rfcl-okp fn-rfcl-rows fn-rfcl-pending-phasep fn-pcar-stage-record
      fn-sn-files-of-fn-sn-update fn-sf-scalars-of-fn-sf-make-fields
      fn-sf-records-of-fn-sf-make-fields-kept rfcl-nonheld-append
      rfcl-handles-append rfcl-fold-append
      (:e fn-rfcl-pending-phasep) (:e member-equal))
    (theory 'minimal-theory))))))

(local
 (defthm rfcl-lv4-retention
  (implies (fn-rfcl-okp s fn-arena)
           (fn-rfcl-okp (fn-pdc-sn-prepare-retention s event) fn-arena))
  :hints (("Goal" :in-theory (union-theories
    '(fn-pdc-sn-prepare-retention rfcl-stage-nonheld rfcl-event-nonheld)
    (theory 'minimal-theory))))))

(local
 (defthm rfcl-lv4-consumer
  (implies (fn-rfcl-okp s fn-arena)
           (fn-rfcl-okp (fn-pdc-sn-prepare-consumer s event) fn-arena))
  :hints (("Goal" :in-theory (union-theories
    '(fn-pdc-sn-prepare-consumer rfcl-stage-nonheld rfcl-event-nonheld)
    (theory 'minimal-theory))))))

(local
 (defthm rfcl-lv4-topic
  (implies (fn-rfcl-okp s fn-arena)
           (fn-rfcl-okp (fn-pdc-sn-prepare-topic s event) fn-arena))
  :hints (("Goal" :in-theory (union-theories
    '(fn-pdc-sn-prepare-topic rfcl-stage-nonheld rfcl-event-nonheld)
    (theory 'minimal-theory))))))

(local
 (defun rfcl-file-rows (f)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-rfcl-pending-phasep (fn-sf-phase f))
      (append (fn-sf-records f) (list (fn-sf-record-candidate f)))
    (fn-sf-records f))))

(local
 (defun rfcl-fok (f h fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (and (fn-rows-handles-inp (rfcl-file-rows f) fn-arena)
       (fn-orcr-fold-contexts-okp (rfcl-file-rows f) (fn-stxk-initial-context 0) h fn-arena))))

(local
 (defthm rfcl-okp-is-fok
  (equal (fn-rfcl-okp s fn-arena) (rfcl-fok (fn-sn-files s) (fn-arena-count fn-arena) fn-arena))
  :hints (("Goal" :in-theory '(fn-rfcl-okp rfcl-fok fn-rfcl-rows rfcl-file-rows)))))

(local
 (defthm rfcl-fok-has-records
  (implies (rfcl-fok f h fn-arena)
           (and (fn-rows-handles-inp (fn-sf-records f) fn-arena)
                (fn-orcr-fold-contexts-okp (fn-sf-records f) (fn-stxk-initial-context 0) h fn-arena)))
  :hints (("Goal" :in-theory (e/d (rfcl-fok rfcl-file-rows)
                           (fn-rows-handles-inp fn-orcr-fold-contexts-okp))))))

(local
 (defthm rfcl-fok-file-step
  (implies (rfcl-fok f h fn-arena)
           (rfcl-fok (fn-sn-file-step f operation result) h fn-arena))
  :hints (("Goal" :in-theory (union-theories
              '(rfcl-fok rfcl-file-rows fn-rfcl-pending-phasep fn-sn-file-step fn-sf-start-frontier fn-sf-frontier-file-result fn-sf-frontier-replace-result fn-sf-frontier-dir-result fn-sf-record-file-result fn-sf-record-link-result fn-sf-record-dir-result fn-sf-recovery-barrier fn-sf-scalars-of-fn-sf-make-fields fn-sf-records-of-fn-sf-make-fields-kept fn-sf-records-of-fn-sf-make-fields-snoc rfcl-handles-append rfcl-fold-append rfcl-fok-has-records natp not car-cons cdr-cons cons-equal mv-nth nth zp (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart unary--) (:executable-counterpart member-equal) member-equal)
              (theory 'minimal-theory))))))

(local
 (defthm rfcl-lv4-io
  (implies (and (fn-sn-statep s) (fn-rfcl-okp s fn-arena))
           (fn-rfcl-okp (fn-sn-io s operation result) fn-arena))
  :hints (("Goal" :in-theory (union-theories '(rfcl-okp-is-fok fn-sn-io
                          fn-sn-files-of-fn-sn-update rfcl-fok-file-step)
                          (theory 'minimal-theory))))))

(local
 (defthm rfcl-fok-crash
  (implies (rfcl-fok f h fn-arena)
           (rfcl-fok (fn-sf-crash f fc rc) h fn-arena))
  :hints (("Goal" :in-theory (union-theories
              '(rfcl-fok rfcl-file-rows fn-rfcl-pending-phasep fn-sf-crash fn-sf-record-present-visiblep fn-sf-phase-of-fn-sf-make fn-sf-records-of-fn-sf-make fn-sf-record-candidate-of-fn-sf-make rfcl-handles-append rfcl-fold-append rfcl-fok-has-records natp not car-cons cdr-cons cons-equal mv-nth nth zp (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart unary--) (:executable-counterpart member-equal) member-equal)
              (theory 'minimal-theory))))))

(local
 (defthm rfcl-lv6
  (implies (fn-rfcl-okp s fn-arena)
           (fn-rfcl-okp (fn-sn-crash s frontier-choice record-choice) fn-arena))
  :hints (("Goal" :in-theory (union-theories '(rfcl-okp-is-fok fn-sn-crash
                          fn-sn-update-indexed fn-sn-with-consumer fn-sn-with-topic
                          fn-sn-files-of-fn-sn-with-event-index fn-sn-fields-of-fn-sn-make-v6
                          rfcl-fok-crash)
                          (theory 'minimal-theory))))))

(local
 (defthm rfcl-fok-complete
  (implies (rfcl-fok f h fn-arena)
           (rfcl-fok (fn-sf-core-completion f seq tx) h fn-arena))
  :hints (("Goal" :in-theory (union-theories
              '(rfcl-fok rfcl-file-rows fn-rfcl-pending-phasep fn-sf-core-completion fn-sf-scalars-of-fn-sf-make-fields fn-sf-records-of-fn-sf-make-fields-kept natp not car-cons cdr-cons cons-equal mv-nth nth zp (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart unary--) (:executable-counterpart member-equal) member-equal)
              (theory 'minimal-theory))))))

(local
 (defthm rfcl-fok-emit
  (implies (rfcl-fok f h fn-arena)
           (rfcl-fok (fn-sf-emit-success f seq tx) h fn-arena))
  :hints (("Goal" :in-theory (union-theories
              '(rfcl-fok rfcl-file-rows fn-rfcl-pending-phasep fn-sf-emit-success fn-sf-scalars-of-fn-sf-make-fields fn-sf-records-of-fn-sf-make-fields-kept natp not car-cons cdr-cons cons-equal mv-nth nth zp (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart unary--) (:executable-counterpart member-equal) member-equal)
              (theory 'minimal-theory))))))

(local
 (defthm rfcl-finish-files
  (implies (fn-sn-completion-enabledp s)
           (equal (fn-sn-files (fn-sn-finish s))
                  (fn-sf-emit-success
                   (fn-sf-core-completion (fn-sn-files s)
                                          (fn-store-event-sequence (fn-sn-completion-record s))
                                          (fn-store-event-txid (fn-sn-completion-record s)))
                   (fn-store-event-sequence (fn-sn-completion-record s))
                   (fn-store-event-txid (fn-sn-completion-record s)))))
  :hints (("Goal" :in-theory (union-theories
             '(fn-sn-finish fn-sn-finish-identity fn-sn-update-accepted fn-sn-update-indexed
               fn-sn-advance-identity-next fn-sn-with-consumer fn-sn-with-topic
               fn-sn-fields-of-fn-sn-make-v6 fn-sn-files-of-fn-sn-update
               fn-sn-files-of-fn-sn-with-event-index)
             (theory 'minimal-theory))))))

(local
 (defthm rfcl-lv4-finish
  (implies (fn-rfcl-okp s fn-arena)
           (fn-rfcl-okp (fn-sn-finish s) fn-arena))
  :hints (("Goal" :cases ((fn-sn-completion-enabledp s))
           :in-theory (union-theories '(rfcl-okp-is-fok rfcl-finish-files rfcl-fok-emit
                                        rfcl-fok-complete)
                                      (theory 'minimal-theory)))
          ("Subgoal 2" :in-theory (union-theories '(fn-sn-finish) (theory 'minimal-theory))))))

(local
 (defthm rfcl-store-event-not-record
  (implies (fn-store-event-p x) (not (fn-record-p x)))
  :hints (("Goal" :use (fn-held-is-no-wire-event fn-hstxa-is-no-wire-event fn-record-is-no-other-wire-event)
           :in-theory '(fn-store-event-p)))))

(local
 (defthm rfcl-after-is-replay
  (implies (fn-sf-record-valuesp rows)
           (equal (rfcl-after rows id h) (mv (fn-replay-identity-loop rows id) h)))
  :hints (("Goal" :induct (rfcl-after rows id h)
           :in-theory (e/d (rfcl-after fn-sf-record-valuesp fn-replay-identity-loop)
                            (fn-store-event-p fn-record-p fn-replay-identity-step
                             fn-stxk-fault fn-intern-row-at fn-ssr-seed fn-ssr-at))))))

(local
 (defthm rfcl-record-list-values
  (implies (fn-sf-record-listp rows seq low frontier) (fn-sf-record-valuesp rows))
  :hints (("Goal" :induct (fn-sf-record-listp rows seq low frontier)
           :in-theory (e/d (fn-sf-record-listp fn-sf-record-valuesp)
                            (fn-store-event-p fn-store-event-sequence fn-store-event-txid
                             fn-store-event-generation))))))

(local
 (defthm rfcl-state-record-values
  (implies (fn-sn-statep s)
           (fn-sf-record-valuesp (fn-sf-records (fn-sn-files s))))
  :hints (("Goal" :use ((:instance fn-cstp-sn-statep-files (st s)))
           :in-theory (union-theories '(fn-sf-statep rfcl-record-list-values)
                                      (theory 'minimal-theory))))))

(local
 (defthm rfcl-retained-parts
  (implies (fn-osr-retainedp s)
           (and (fn-sn-statep s) (fn-sf-statep (fn-sn-files s))
                (fn-sn-identity-sequencep s) (fn-osr-identity-prefixp s) (fn-skp-resolvedp s)
                (fn-sf-record-valuesp (fn-sf-records (fn-sn-files s)))))
  :hints (("Goal" :in-theory (union-theories
            '(fn-osr-retainedp fn-osr-livep fn-sti-livep fn-csi-livep
              fn-cstp-sn-statep-files rfcl-state-record-values)
            (theory 'minimal-theory))))))

(local
 (defthm rfcl-reserved-snapshot-exact
  (implies (and (fn-osr-retainedp s) (equal (fn-sf-phase (fn-sn-files s)) :reserved))
           (equal (fn-stxk-context-snapshots (fn-replay-identity (fn-sf-records (fn-sn-files s))))
                  (fn-sn-keyring-snapshots s)))
  :hints (("Goal"
           :use (rfcl-retained-parts (:instance fn-sf-state-records-are-true-list (s (fn-sn-files s)))
                 (:instance fn-cbor-take-whole-list (xs (fn-sf-records (fn-sn-files s)))))
           :in-theory (union-theories
            '(fn-sn-identity-sequencep fn-osr-identity-prefixp
              fn-osr-context-view fn-sn-identity-context fn-stxk-context-snapshots
              fn-stxk-context fn-sf-completion-phasep fn-store-event-nth
              fn-cstp-sn-statep-files fn-sf-state-records-are-true-list
              member-equal (:executable-counterpart member-equal)
              natp not car-cons cdr-cons cons-equal)
            (theory 'minimal-theory))))))

(local
 (defthm rfcl-reserved-seed-exact
  (implies (and (fn-osr-retainedp s) (equal (fn-sf-phase (fn-sn-files s)) :reserved))
           (and (equal (fn-ssr-at 1 (fn-ssr-seed (fn-replay-identity (fn-sf-records (fn-sn-files s)))) )
                       (fn-sn-keyring s))
                (equal (fn-ssr-at 2 (fn-ssr-seed (fn-replay-identity (fn-sf-records (fn-sn-files s)))) )
                       (fn-sn-keyring-generation s))))
  :hints (("Goal" :use (rfcl-retained-parts rfcl-reserved-snapshot-exact)
           :in-theory (union-theories
              '(fn-skp-resolvedp
                fn-ssr-seed fn-ssr-state fn-ssr-at fn-ag-car fn-ag-cdr
                zp (:executable-counterpart zp) (:executable-counterpart binary-+)
                (:executable-counterpart unary--)
                natp not car-cons cdr-cons cons-equal)
              (theory 'minimal-theory))))))

(local
 (defthm rfcl-intern-is-held
  (implies (and (fn-record-p w) (natp g) (natp h)) (fn-held-p (fn-intern-row-at w k g h)))
  :hints (("Goal" :in-theory (enable fn-intern-row-at fn-record-p fn-held-p fn-record-internals
                                    fn-held-internals fn-hf-p fn-hc-p fn-hf-startp fn-hc-verdictp)))))

(local
 (defthm rfcl-intern-fields
  (and (equal (fn-held-context (fn-intern-row-at w k g h)) (fn-held-context-of (fn-record-payload w) k g))
       (equal (fn-record-payload (fn-intern-row-at w k g h)) h))
  :hints (("Goal" :in-theory (enable fn-intern-row-at)))))

(local
 (defthm rfcl-one-intern
  (implies (and (fn-record-p w) (natp g)
                (equal k (fn-ssr-at 1 (fn-ssr-seed id)))
                (equal g (fn-ssr-at 2 (fn-ssr-seed id))))
           (and
            (fn-rows-handles-inp (list (fn-intern-row-at w k g (fn-arena-count fn-arena)))
                                 (fn-arena-seal-list (fn-record-payload w) fn-arena))
            (fn-orcr-fold-contexts-okp (list (fn-intern-row-at w k g (fn-arena-count fn-arena)))
                                       id hh (fn-arena-seal-list (fn-record-payload w) fn-arena))))
  :hints (("Goal" :in-theory
            (e/d (fn-rows-handles-inp fn-row-handle-inp fn-orcr-retained-p fn-orcr-held-part fn-row-bytes)
                 (fn-held-context-of fn-ssr-seed fn-ssr-at fn-intern-row-at fn-replay-identity-loop
                  fn-held-p fn-hstxa-p fn-record-p fn-arena-count-is-len fn-arena-payload-is-nth
                  fn-arena-seal-list-is-append))
           :expand ((:free (rows h a) (fn-orcr-fold-contexts-okp nil rows h a))
                    (:free (a) (fn-orcr-fold-contexts-okp
                      (list (fn-intern-row-at w k g (fn-arena-count fn-arena))) id hh a)))))))

(local
 (defthm rfcl-after-store
  (implies (fn-osr-retainedp s)
           (equal (rfcl-after (fn-sf-records (fn-sn-files s)) (fn-stxk-initial-context 0) h)
                  (mv (fn-replay-identity (fn-sf-records (fn-sn-files s))) h)))
  :hints (("Goal" :use (rfcl-retained-parts)
           :in-theory (union-theories '(rfcl-after-is-replay fn-replay-identity)
                                      (theory 'minimal-theory))))))

(local
 (defthm rfcl-fold-seal-any-handle
  (implies (and (fn-rows-handles-inp rows fn-arena)
                (fn-orcr-fold-contexts-okp rows id h fn-arena) (natp h) (natp hh))
           (fn-orcr-fold-contexts-okp rows id hh (fn-arena-seal-list p fn-arena)))
  :hints (("Goal" :use ((:instance fn-rfc-fold-contexts-okp-any-handle
                                   (h1 hh) (h2 h) (fn-arena (fn-arena-seal-list p fn-arena))))
           :in-theory (union-theories '(rfcl-fold-seal) (theory 'minimal-theory))))))

(local
 (defthm rfcl-state-generation
  (implies (fn-sn-statep s) (natp (fn-sn-keyring-generation s)))
  :hints (("Goal" :in-theory '(fn-sn-statep natp)))))

(local
 (defthm rfcl-append-intern
  (implies (and (fn-osr-retainedp s) (fn-rfcl-okp s fn-arena)
                (equal (fn-sf-phase (fn-sn-files s)) :reserved) (fn-record-p w))
           (let ((rows (append (fn-sf-records (fn-sn-files s))
                         (list (fn-intern-row-at w (fn-sn-keyring s) (fn-sn-keyring-generation s)
                                                (fn-arena-count fn-arena))))))
             (and (fn-rows-handles-inp rows (fn-arena-seal-list (fn-record-payload w) fn-arena))
                  (fn-orcr-fold-contexts-okp rows (fn-stxk-initial-context 0)
                   (fn-arena-count (fn-arena-seal-list (fn-record-payload w) fn-arena))
                   (fn-arena-seal-list (fn-record-payload w) fn-arena)))))
  :hints (("Goal"
           :use (rfcl-retained-parts rfcl-reserved-seed-exact
                 (:instance rfcl-one-intern
                   (k (fn-sn-keyring s)) (g (fn-sn-keyring-generation s))
                   (id (fn-replay-identity (fn-sf-records (fn-sn-files s))))
                   (hh (fn-arena-count (fn-arena-seal-list (fn-record-payload w) fn-arena))))
                 (:instance rfcl-state-generation))
           :in-theory (union-theories
              '(fn-rfcl-okp fn-rfcl-rows fn-rfcl-pending-phasep
                rfcl-handles-append rfcl-fold-append rfcl-after-store
                rfcl-handles-seal rfcl-fold-seal-any-handle
                fn-arena-seal-count (:type-prescription fn-arena-count)
                natp mv-nth nth zp car-cons cdr-cons
                (:executable-counterpart zp) (:executable-counterpart binary-+)
                (:executable-counterpart unary--) 
                (:executable-counterpart fn-rfcl-pending-phasep))
              (theory 'minimal-theory))))))

(local
 (defthm rfcl-stage-intern
  (implies (and (fn-osr-retainedp s) (fn-rfcl-okp s fn-arena)
                (equal (fn-sf-phase (fn-sn-files s)) :reserved) (fn-record-p w))
           (fn-rfcl-okp
             (fn-sn-update s
              (fn-sf-make-fields :record-staged frontier nil (fn-sf-records-field (fn-sn-files s))
                (fn-intern-row-at w (fn-sn-keyring s) (fn-sn-keyring-generation s) (fn-arena-count fn-arena))
                nil sf barriers) node)
             (fn-arena-seal-list (fn-record-payload w) fn-arena)))
  :hints (("Goal" :use (rfcl-append-intern)
           :in-theory (union-theories
             '(fn-rfcl-okp fn-rfcl-rows fn-rfcl-pending-phasep
               fn-sn-files-of-fn-sn-update fn-sf-scalars-of-fn-sf-make-fields
               fn-sf-records-of-fn-sf-make-fields-kept
               (:executable-counterpart fn-rfcl-pending-phasep))
             (theory 'minimal-theory))))))

(local
 (defthm rfcl-lv2
  (implies (and (fn-osr-retainedp s) (fn-rfcl-okp s fn-arena))
           (fn-rfcl-okp (mv-nth 0 (fn-store-prepare-interned s w fn-arena))
                        (mv-nth 1 (fn-store-prepare-interned s w fn-arena))))
  :hints (("Goal" :in-theory (union-theories
             '(fn-store-prepare-interned fn-sn-prepare fn-sf-prepare-record rfcl-stage-intern
               mv-nth nth zp car-cons cdr-cons
               (:executable-counterpart zp) (:executable-counterpart binary-+)
               (:executable-counterpart unary--))
             (theory 'minimal-theory))))))

(local
 (defthm rfcl-prc-prepare-intern
  (implies (and (fn-osr-retainedp s) (fn-rfcl-okp s fn-arena) (fn-record-p w))
           (fn-rfcl-okp
            (fn-prc-spc-prepare s
              (fn-intern-row-at w (fn-sn-keyring s) (fn-sn-keyring-generation s) (fn-arena-count fn-arena))
              view carry)
            (fn-arena-seal-list (fn-record-payload w) fn-arena)))
  :hints (("Goal" :in-theory (union-theories
             '(fn-prc-spc-prepare fn-pcar-stage-record rfcl-stage-intern rfcl-lv5)
             (theory 'minimal-theory))))))

(local
 (defthm rfcl-lv2h
  (let* ((s (fn-sbud-oc-store oc))
         (row (fn-intern-row-at record (fn-sn-keyring s) (fn-sn-keyring-generation s)
                                (fn-arena-count fn-arena)))
         (out (fn-pout-prepare-article oc row budget carry))
         (s2 (fn-sbud-oc-store (mv-nth 1 out))))
    (implies (and (fn-osr-retainedp s)
                  (fn-record-p record)
                  (fn-rfcl-okp s fn-arena))
             (fn-rfcl-okp s2 (if (equal (mv-nth 0 out) :prepared)
                                 (fn-arena-seal-list (fn-record-payload record) fn-arena)
                               fn-arena))))
  :hints (("Goal"
           :use ((:instance fn-pout-store-of-psrv-prepare
                  (record (fn-intern-row-at record (fn-sn-keyring (fn-sbud-oc-store oc))
                             (fn-sn-keyring-generation (fn-sbud-oc-store oc)) (fn-arena-count fn-arena))))
                 (:instance rfcl-prc-prepare-intern (s (fn-sbud-oc-store oc)) (w record)
                            (view (fn-own-view (fn-ocfg-owner oc)))))
           :in-theory (union-theories
              '(fn-pout-prepare-article-answers-the-store-change rfcl-lv5)
              (theory 'minimal-theory))))))

(local
 (defthm rfcl-open-files
  (implies (equal (fn-sn-open-kind (fn-cpo-open-observed configs frontier rows)) :ok)
           (equal (fn-sn-files (fn-sn-open-state (fn-cpo-open-observed configs frontier rows)))
                  (fn-sf-make :recovering frontier nil rows nil nil nil 0)))
  :hints (("Goal" :in-theory (union-theories
            '(fn-cpo-open-observed fn-sn-open-error fn-sn-open-ok fn-sn-open-kind fn-sn-open-state
              fn-sn-with-event-index fn-sn-files-of-fn-sn-with-event-index
              fn-sn-with-topic fn-sn-with-consumer fn-cpo-install
              fn-sn-files-of-fn-sn-update-replayed
              fn-sn-fields-of-fn-sn-make-v6 fn-sn-files-of-fn-sn-make-v6
              fn-sn-files-of-fn-sn-with-configuration
              car-cons cdr-cons cons-equal)
            (theory 'minimal-theory))))))

(local
 (defthm rfcl-install-store
  (implies (not (equal (fn-ock-install replayed opened max-conns) :fault))
           (and (equal (fn-sbud-oc-store (fn-ock-install replayed opened max-conns))
                       (fn-sn-open-state opened))
                (equal (fn-sn-open-kind opened) :ok)))
  :hints (("Goal" :in-theory (union-theories
            '(fn-ock-install fn-sbud-oc-store fn-own-start fn-own-configure
              fn-own-store-of-fn-own-make fn-own-refresh-keeps-fields fn-ocfg-owner-of-fn-ocfg-make)
            (theory 'minimal-theory))))))

(local
 (defthm rfcl-lv1b
  (let ((oc (fn-ock-recover-extended
             (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
             configs frontier max-conns)))
    (implies (and (not (equal oc :fault))
                  (fn-rows-handles-inp (append prefix suffix) fn-arena)
                  (fn-orcr-fold-contexts-okp (append prefix suffix)
                                             (fn-stxk-initial-context 0)
                                             (fn-arena-count fn-arena) fn-arena))
             (fn-rfcl-okp (fn-sbud-oc-store oc) fn-arena)))
  :hints (("Goal" :use ((:instance rfcl-install-store
                         (replayed (fn-cpr-replay configs (append prefix suffix)))
                         (opened (fn-cpo-open-observed configs frontier (append prefix suffix)))))
           :in-theory (union-theories
             '(fn-owner-recover-from-checkpoint-equals-full-recover fn-ock-recover-full
               rfcl-open-files fn-rfcl-okp fn-rfcl-rows fn-rfcl-pending-phasep
               fn-sf-phase-of-fn-sf-make fn-sf-records-of-fn-sf-make
               (:executable-counterpart fn-rfcl-pending-phasep))
             (theory 'minimal-theory))))))

(local
 (defthm rfcl-wire-nonheld
  (implies (fn-wire-event-p x) (not (fn-orcr-retained-p x)))
  :hints (("Goal" :use (fn-held-is-no-wire-event fn-hstxa-is-no-wire-event)
           :in-theory '(fn-wire-event-p fn-orcr-retained-p)))))

(local
 (defthm rfcl-wire-parts
  (implies (fn-wire-event-p x) (and (not (fn-held-p x)) (not (fn-hstxa-p x))))
  :hints (("Goal" :use (rfcl-wire-nonheld) :in-theory '(fn-orcr-retained-p)))))

(local
 (defthm rfcl-one-identity
  (implies (and (natp g) (equal k (fn-ssr-at 1 (fn-ssr-seed id)))
                (equal g (fn-ssr-at 2 (fn-ssr-seed id))))
           (let ((a (if (fn-oii-identity-sealsp w)
                        (fn-arena-seal-list (fn-oii-identity-payload w) fn-arena) fn-arena))
                 (row (fn-oii-identity-row w k g (fn-arena-count fn-arena))))
             (and (fn-rows-handles-inp (list row) a)
                  (fn-orcr-fold-contexts-okp (list row) id hh a))))
  :hints (("Goal" :in-theory (union-theories
              '(fn-oii-identity-row fn-oii-identity-sealsp fn-oii-identity-payload fn-rows-handles-inp fn-row-handle-inp fn-orcr-retained-p fn-orcr-held-part fn-row-bytes fn-hstxa-p-of-make fn-hstxa-accessors-of-make fn-hstxa-is-not-held fn-cstp-held-kind-facts fn-held-is-no-wire-event rfcl-intern-is-held rfcl-intern-fields rfcl-wire-parts fn-arena-seal-new-handle fn-arena-seal-count (:type-prescription fn-arena-count) (:executable-counterpart fn-held-p) (:executable-counterpart fn-hstxa-p) (:executable-counterpart fn-orcr-retained-p) (:executable-counterpart fn-record-p) natp not car-cons cdr-cons cons-equal mv-nth nth zp (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart unary--) (:executable-counterpart member-equal) member-equal)
              (theory 'minimal-theory))
           :expand ((:free (rows h a) (fn-orcr-fold-contexts-okp nil rows h a))
                    (:free (a row) (fn-orcr-fold-contexts-okp (list row) id hh a)))))))

(local
 (defthm rfcl-append-identity
  (implies (and (fn-osr-retainedp s) (fn-rfcl-okp s fn-arena)
                (equal (fn-sf-phase (fn-sn-files s)) :reserved))
           (let ((rows (append (fn-sf-records (fn-sn-files s))
                         (list (fn-oii-identity-row w (fn-sn-keyring s) (fn-sn-keyring-generation s)
                                                (fn-arena-count fn-arena))))))
             (and (fn-rows-handles-inp rows (if (fn-oii-identity-sealsp w) (fn-arena-seal-list (fn-oii-identity-payload w) fn-arena) fn-arena))
                  (fn-orcr-fold-contexts-okp rows (fn-stxk-initial-context 0)
                   (fn-arena-count (if (fn-oii-identity-sealsp w) (fn-arena-seal-list (fn-oii-identity-payload w) fn-arena) fn-arena))
                   (if (fn-oii-identity-sealsp w) (fn-arena-seal-list (fn-oii-identity-payload w) fn-arena) fn-arena)))))
  :hints (("Goal"
           :cases ((fn-oii-identity-sealsp w))
           :use (rfcl-retained-parts rfcl-reserved-seed-exact
                 (:instance rfcl-one-identity
                   (k (fn-sn-keyring s)) (g (fn-sn-keyring-generation s))
                   (id (fn-replay-identity (fn-sf-records (fn-sn-files s))))
                   (hh (fn-arena-count (if (fn-oii-identity-sealsp w) (fn-arena-seal-list (fn-oii-identity-payload w) fn-arena) fn-arena))))
                 (:instance rfcl-state-generation))
           :in-theory (union-theories
              '(fn-rfcl-okp fn-rfcl-rows fn-rfcl-pending-phasep
                rfcl-handles-append rfcl-fold-append rfcl-after-store
                rfcl-handles-seal rfcl-fold-seal-any-handle
                fn-arena-seal-count (:type-prescription fn-arena-count)
                natp mv-nth nth zp car-cons cdr-cons
                (:executable-counterpart zp) (:executable-counterpart binary-+)
                (:executable-counterpart unary--) 
                (:executable-counterpart fn-rfcl-pending-phasep))
              (theory 'minimal-theory))))))

(local
 (defthm rfcl-stage-identity
  (implies (and (fn-osr-retainedp s) (fn-rfcl-okp s fn-arena)
                (equal (fn-sf-phase (fn-sn-files s)) :reserved))
           (fn-rfcl-okp
             (fn-sn-update s
              (fn-sf-make-fields :record-staged frontier nil (fn-sf-records-field (fn-sn-files s))
                (fn-oii-identity-row w (fn-sn-keyring s) (fn-sn-keyring-generation s) (fn-arena-count fn-arena))
                nil sf barriers) node)
             (if (fn-oii-identity-sealsp w)
                 (fn-arena-seal-list (fn-oii-identity-payload w) fn-arena) fn-arena)))
  :hints (("Goal" :use (rfcl-append-identity)
           :in-theory (union-theories
             '(fn-rfcl-okp fn-rfcl-rows fn-rfcl-pending-phasep
               fn-sn-files-of-fn-sn-update fn-sf-scalars-of-fn-sf-make-fields
               fn-sf-records-of-fn-sf-make-fields-kept
               (:executable-counterpart fn-rfcl-pending-phasep))
             (theory 'minimal-theory))))))

(local
 (defthm rfcl-ccar-prepare-identity
  (implies (and (fn-osr-retainedp s) (fn-rfcl-okp s fn-arena))
           (fn-rfcl-okp
            (fn-ccar-sn-prepare-identity s
             (fn-oii-identity-row w (fn-sn-keyring s) (fn-sn-keyring-generation s) (fn-arena-count fn-arena)))
            (if (fn-oii-identity-sealsp w)
                (fn-arena-seal-list (fn-oii-identity-payload w) fn-arena) fn-arena)))
   :hints (("Goal" :use ((:instance rfcl-stage-identity
                            (frontier (fn-sf-frontier (fn-sn-files s)))
                            (sf (fn-sf-successes-field (fn-sn-files s)))
                            (barriers (fn-sf-barriers (fn-sn-files s))) (node (fn-sn-node s))))
           :in-theory (union-theories
             '(fn-ccar-sn-prepare-identity fn-pcar-stage-record rfcl-stage-identity rfcl-lv5)
             (theory 'minimal-theory))))))

(local
 (defthm rfcl-lv3
  (let* ((s (fn-sbud-oc-store oc))
         (out (fn-pout-prepare-identity oc w (fn-arena-count fn-arena)))
         (s2 (fn-sbud-oc-store (mv-nth 1 out))))
    (implies (and (fn-osr-retainedp s)
                  (fn-rfcl-okp s fn-arena))
             (fn-rfcl-okp s2 (if (and (equal (mv-nth 0 out) :prepared)
                                      (fn-oii-identity-sealsp w))
                                 (fn-arena-seal-list (fn-oii-identity-payload w) fn-arena)
                               fn-arena))))
  :hints (("Goal"
           :use ((:instance fn-pout-store-of-oiis-prepare-identity (h (fn-arena-count fn-arena)))
                 (:instance rfcl-ccar-prepare-identity (s (fn-sbud-oc-store oc))))
           :in-theory (union-theories
              '(fn-pout-prepare-identity-answers-the-store-change rfcl-lv5)
              (theory 'minimal-theory))))))

(local (in-theory (union-theories '(rfcl-lv0) (theory 'minimal-theory))))

(defthm fn-rfcl-okp-is-the-capture-premise-by-definition
  (implies (and (fn-rfcl-okp s fn-arena)
                (not (fn-rfcl-pending-phasep (fn-sf-phase (fn-sn-files s)))))
           (fn-orcr-fold-contexts-okp (fn-sf-records (fn-sn-files s))
                                      (fn-stxk-initial-context 0)
                                      (fn-arena-count fn-arena) fn-arena)))

(local (in-theory (union-theories '(rfcl-lv1) (theory 'minimal-theory))))

(defthm fn-rfcl-initial-okp
  (fn-rfcl-okp (fn-sn-initial groups capacity) fn-arena))

(local (in-theory (union-theories '(rfcl-lv1b) (theory 'minimal-theory))))

(defthm fn-rfcl-recovery-establishes-okp
  (let ((oc (fn-ock-recover-extended
             (fn-sco-extend (fn-sco-capture configs prefix) configs suffix)
             configs frontier max-conns)))
    (implies (and (not (equal oc :fault))
                  (fn-rows-handles-inp (append prefix suffix) fn-arena)
                  (fn-orcr-fold-contexts-okp (append prefix suffix)
                                             (fn-stxk-initial-context 0)
                                             (fn-arena-count fn-arena) fn-arena))
             (fn-rfcl-okp (fn-sbud-oc-store oc) fn-arena))))

(local (in-theory (union-theories '(rfcl-lv2) (theory 'minimal-theory))))

(defthm fn-rfcl-prepare-interned-keeps-okp
  (implies (and (fn-osr-retainedp s)
                (fn-rfcl-okp s fn-arena))
           (fn-rfcl-okp (mv-nth 0 (fn-store-prepare-interned s w fn-arena))
                        (mv-nth 1 (fn-store-prepare-interned s w fn-arena)))))

(local (in-theory (union-theories '(rfcl-lv2h) (theory 'minimal-theory))))

(defthm fn-rfcl-owner-prepare-article-keeps-okp
  (let* ((s (fn-sbud-oc-store oc))
         (row (fn-intern-row-at record (fn-sn-keyring s) (fn-sn-keyring-generation s)
                                (fn-arena-count fn-arena)))
         (out (fn-pout-prepare-article oc row budget carry))
         (s2 (fn-sbud-oc-store (mv-nth 1 out))))
    (implies (and (fn-osr-retainedp s)
                  (fn-record-p record)
                  (fn-rfcl-okp s fn-arena))
             (fn-rfcl-okp s2 (if (equal (mv-nth 0 out) :prepared)
                                 (fn-arena-seal-list (fn-record-payload record) fn-arena)
                               fn-arena)))))

(local (in-theory (union-theories '(rfcl-lv3) (theory 'minimal-theory))))

(defthm fn-rfcl-prepare-identity-keeps-okp
  (let* ((s (fn-sbud-oc-store oc))
         (out (fn-pout-prepare-identity oc w (fn-arena-count fn-arena)))
         (s2 (fn-sbud-oc-store (mv-nth 1 out))))
    (implies (and (fn-osr-retainedp s)
                  (fn-rfcl-okp s fn-arena))
             (fn-rfcl-okp s2 (if (and (equal (mv-nth 0 out) :prepared)
                                      (fn-oii-identity-sealsp w))
                                 (fn-arena-seal-list (fn-oii-identity-payload w) fn-arena)
                               fn-arena)))))

(local (in-theory (union-theories '(rfcl-lv4-retention) (theory 'minimal-theory))))

(defthm fn-rfcl-prepare-retention-keeps-okp
  (implies (fn-rfcl-okp s fn-arena)
           (fn-rfcl-okp (fn-pdc-sn-prepare-retention s event) fn-arena)))

(local (in-theory (union-theories '(rfcl-lv4-consumer) (theory 'minimal-theory))))

(defthm fn-rfcl-prepare-consumer-keeps-okp
  (implies (fn-rfcl-okp s fn-arena)
           (fn-rfcl-okp (fn-pdc-sn-prepare-consumer s event) fn-arena)))

(local (in-theory (union-theories '(rfcl-lv4-topic) (theory 'minimal-theory))))

(defthm fn-rfcl-prepare-topic-keeps-okp
  (implies (fn-rfcl-okp s fn-arena)
           (fn-rfcl-okp (fn-pdc-sn-prepare-topic s event) fn-arena)))

(local (in-theory (union-theories '(rfcl-lv4-io) (theory 'minimal-theory))))

(defthm fn-rfcl-io-keeps-okp
  (implies (and (fn-sn-statep s) (fn-rfcl-okp s fn-arena))
           (fn-rfcl-okp (fn-sn-io s operation result) fn-arena)))

(local (in-theory (union-theories '(rfcl-lv4-finish) (theory 'minimal-theory))))

(defthm fn-rfcl-finish-keeps-okp
  (implies (fn-rfcl-okp s fn-arena)
           (fn-rfcl-okp (fn-sn-finish s) fn-arena)))

(local (in-theory (union-theories '(rfcl-lv5) (theory 'minimal-theory))))

(defthm fn-rfcl-seal-keeps-okp
  (implies (fn-rfcl-okp s fn-arena)
           (fn-rfcl-okp s (fn-arena-seal-list p fn-arena))))

(local (in-theory (union-theories '(rfcl-lv6) (theory 'minimal-theory))))

(defthm fn-rfcl-crash-keeps-okp
  (implies (fn-rfcl-okp s fn-arena)
           (fn-rfcl-okp (fn-sn-crash s frontier-choice record-choice) fn-arena)))

; A staged POST refused before its seal drops the candidate, retaining
; exactly the prior records. Binding establishes the node state needed by
; known-abort, even without a hypothesis about the supplied retention carry.
(local
 (defthm rfcl-bindsp-is-node-statep
  (implies (fn-rcon-sn-record-bindsp node row) (fn-node-statep node))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories
     '(fn-rcon-sn-record-bindsp fn-sn-record-bindsp fn-node-pending-matchesp)
     (theory 'minimal-theory))))))

(local
 (defthm rfcl-update-statep
  (implies (and (fn-sn-statep s) (fn-sf-statep files) (fn-node-statep node))
           (fn-sn-statep (fn-sn-update s files node)))
  :hints (("Goal" :in-theory (union-theories
     '(fn-sn-statep fn-sn-update fn-sn-fields-of-fn-sn-make-v6)
     (theory 'minimal-theory))))))

(local
 (defthm rfcl-stage-files-facts
  (implies (fn-sf-statep files)
           (and (fn-sf-statep (fn-pcar-stage-record files row))
                (equal (fn-sf-records (fn-pcar-stage-record files row))
                       (fn-sf-records files))
                (implies (equal (fn-sf-phase files) :reserved)
                         (equal (fn-sf-record-candidate (fn-pcar-stage-record files row))
                                (if (fn-pcar-files-candidatep row files) row
                                  (fn-sf-record-candidate files))))))
  :hints (("Goal" :in-theory (union-theories
    '(fn-pcar-stage-record fn-pcar-files-candidatep-is-candidatep
      fn-sf-statep fn-sf-shape-fields-canonical fn-sf-phase-shapep fn-pcar-candidatep-is-candidatep
      fn-sf-shapep-of-fn-sf-make-fields fn-sf-successes-of-fn-sf-make-fields-kept
      (:e fn-sf-phasep) (:e fn-sf-frontier-phasep) (:e fn-sf-record-phasep)
      (:e fn-sf-completion-phasep) fn-sf-scalars-of-fn-sf-make-fields
      fn-sf-records-of-fn-sf-make-fields-kept)
    (theory 'minimal-theory))))))

(local
 (defthm rfcl-stage-noncandidate-is-no-op
  (implies (not (fn-pcar-files-candidatep row files))
           (equal (fn-pcar-stage-record files row) files))
  :hints (("Goal" :in-theory (union-theories '(fn-pcar-stage-record)
                                           (theory 'minimal-theory))))))

(local
 (defthm rfcl-prc-prepared-facts
  (let ((next (fn-prc-spc-prepare s row view carry)))
    (implies (not (equal next s))
             (and (fn-sn-statep next)
                  (fn-sn-known-abort-enabledp next)
                  (equal (fn-sf-records (fn-sn-files next))
                         (fn-sf-records (fn-sn-files s))))))
  :hints (("Goal"
    :use ((:instance rfcl-bindsp-is-node-statep
           (node (fn-prc-sn-prepare-node (fn-sn-node s) row view carry))))
    :in-theory (union-theories
     '(fn-prc-spc-prepare fn-sn-known-abort-enabledp
       fn-cstp-sn-update-fields rfcl-update-statep
       rfcl-stage-files-facts rfcl-stage-noncandidate-is-no-op fn-cstp-sn-statep-files
       fn-rcon-sn-record-bindsp-is-sn-record-bindsp)
     (theory 'minimal-theory))))))

(local
 (defthm rfcl-pout-prepared-facts
  (let* ((out (fn-pout-prepare-article oc row budget carry))
         (s (fn-sbud-oc-store oc))
         (next (fn-sbud-oc-store (mv-nth 1 out))))
    (implies (equal (mv-nth 0 out) :prepared)
             (and (fn-sn-known-abort-enabledp next)
                  (equal (fn-sf-records (fn-sn-files next))
                         (fn-sf-records (fn-sn-files s))))))
  :hints (("Goal"
    :use ((:instance fn-pout-store-of-psrv-prepare (record row))
          (:instance rfcl-prc-prepared-facts (s (fn-sbud-oc-store oc))
                     (view (fn-own-view (fn-ocfg-owner oc)))))
    :in-theory (union-theories
      '(fn-pout-prepare-article fn-pout-stagedp fn-psrv-refusal-kind fn-sbud-refusal-kind mv-nth car-cons cdr-cons
        (:e zp) (:e binary-+) (:e unary--))
      (theory 'minimal-theory))))))

(local
 (defthm rfcl-abort-restores-records-okp
  (implies (and (fn-rfcl-okp s fn-arena)
                (fn-sn-known-abort-enabledp next)
                (equal (fn-sf-records (fn-sn-files next))
                       (fn-sf-records (fn-sn-files s))))
           (fn-rfcl-okp (fn-sn-known-abort next) fn-arena))
  :hints (("Goal"
    :use ((:instance rfcl-fok-has-records (f (fn-sn-files s)) (h (fn-arena-count fn-arena)))
          (:instance fn-pout-known-abort-reaches-ready (s next))
          (:instance fn-snrt-known-abort-keeps-records (s next)))
    :in-theory (union-theories
      '(rfcl-okp-is-fok rfcl-fok rfcl-file-rows (:e fn-rfcl-pending-phasep))
      (theory 'minimal-theory))))))

(local
 (defthm rfcl-pout-prepare-then-abort
  (let* ((out (fn-pout-prepare-article oc row budget carry))
         (ab (fn-pout-known-abort (mv-nth 1 out) fn-arena)))
    (implies (and (fn-rfcl-okp (fn-sbud-oc-store oc) fn-arena)
                  (equal (mv-nth 0 out) :prepared))
             (fn-rfcl-okp (fn-sbud-oc-store (mv-nth 1 ab)) fn-arena)))
  :hints (("Goal"
    :use ((:instance rfcl-pout-prepared-facts)
          (:instance rfcl-abort-restores-records-okp
            (s (fn-sbud-oc-store oc))
            (next (fn-sbud-oc-store (mv-nth 1 (fn-pout-prepare-article oc row budget carry))))))
    :in-theory (union-theories
      '(fn-pout-known-abort fn-pout-store-of-store-step fn-snrt-step
        mv-nth car-cons cdr-cons (:e zp) (:e binary-+) (:e unary--))
      (theory 'minimal-theory))))))

(local (in-theory (union-theories '(rfcl-pout-prepare-then-abort) (theory 'minimal-theory))))
(defthm fn-rfcl-known-abort-after-prepare-keeps-okp
  (let* ((s (fn-sbud-oc-store oc))
         (row (fn-intern-row-at record (fn-sn-keyring s) (fn-sn-keyring-generation s)
                                (fn-arena-count fn-arena)))
         (out (fn-pout-prepare-article oc row budget carry))
         (ab (fn-pout-known-abort (mv-nth 1 out) fn-arena)))
    (implies (and (fn-osr-retainedp s)
                  (fn-record-p record)
                  (equal (mv-nth 0 out) :prepared)
                  (fn-rfcl-okp s fn-arena))
             (fn-rfcl-okp (fn-sbud-oc-store (mv-nth 1 ab)) fn-arena))))

(local
 (defthm rfcl-idrp
  (implies (fn-rfcl-okp (fn-sbud-oc-store oc) fn-arena)
           (fn-rfcl-okp (fn-sbud-oc-store (mv-nth 1 (fn-idrp-prepare-retention oc event grant fn-arena)))
                        fn-arena))
  :hints (("Goal"
    :use ((:instance fn-idrp-retention-preparation-consumes-exact-current-grant)
          (:instance fn-pdc-store-of-owner-prepares (e event)))
    :in-theory (union-theories '(rfcl-lv4-retention) (theory 'minimal-theory))))))
(local
 (defthm rfcl-pdc-consumer
  (implies (fn-rfcl-okp (fn-sbud-oc-store oc) fn-arena)
           (fn-rfcl-okp (fn-sbud-oc-store (mv-nth 1 (fn-pdc-pout-prepare-consumer oc e))) fn-arena))
  :hints (("Goal" :use ((:instance fn-pdc-store-of-owner-prepares))
    :in-theory (union-theories
      '(fn-pdc-pout-prepares-answer-the-store-change rfcl-lv4-consumer)
      (theory 'minimal-theory))))))
(local
 (defthm rfcl-pdc-topic
  (implies (fn-rfcl-okp (fn-sbud-oc-store oc) fn-arena)
           (fn-rfcl-okp (fn-sbud-oc-store (mv-nth 1 (fn-pdc-pout-prepare-topic oc e))) fn-arena))
  :hints (("Goal" :use ((:instance fn-pdc-store-of-owner-prepares))
    :in-theory (union-theories
      '(fn-pdc-pout-prepares-answer-the-store-change rfcl-lv4-topic)
      (theory 'minimal-theory))))))

(local (in-theory (union-theories '(rfcl-idrp) (theory 'minimal-theory))))
(defthm fn-rfcl-idrp-prepare-retention-keeps-okp
  (implies (fn-rfcl-okp (fn-sbud-oc-store oc) fn-arena)
           (fn-rfcl-okp (fn-sbud-oc-store (mv-nth 1 (fn-idrp-prepare-retention oc event grant fn-arena)))
                        fn-arena)))

(local (in-theory (union-theories '(rfcl-pdc-consumer) (theory 'minimal-theory))))
(defthm fn-rfcl-pdc-pout-prepare-consumer-keeps-okp
  (implies (fn-rfcl-okp (fn-sbud-oc-store oc) fn-arena)
           (fn-rfcl-okp (fn-sbud-oc-store (mv-nth 1 (fn-pdc-pout-prepare-consumer oc e))) fn-arena)))

(local (in-theory (union-theories '(rfcl-pdc-topic) (theory 'minimal-theory))))
(defthm fn-rfcl-pdc-pout-prepare-topic-keeps-okp
  (implies (fn-rfcl-okp (fn-sbud-oc-store oc) fn-arena)
           (fn-rfcl-okp (fn-sbud-oc-store (mv-nth 1 (fn-pdc-pout-prepare-topic oc e))) fn-arena)))

; Valid-choice crashes drop the record-staged candidate. The prepare itself
; establishes Store validity whenever it changes the Store.
(local
 (defthm rfcl-crash-staged-restores-records
  (implies (and (fn-rfcl-okp s fn-arena)
                (fn-sn-statep next)
                (equal (fn-sf-phase (fn-sn-files next)) :record-staged)
                (equal (fn-sf-records (fn-sn-files next))
                       (fn-sf-records (fn-sn-files s)))
                (fn-sf-crash-choicep frontier-choice record-choice))
           (fn-rfcl-okp (fn-sn-crash next frontier-choice record-choice) fn-arena))
  :hints (("Goal"
    :use ((:instance rfcl-fok-has-records (f (fn-sn-files s)) (h (fn-arena-count fn-arena)))
          (:instance fn-cstp-sn-statep-files (st next)))
    :in-theory (union-theories
      '(rfcl-okp-is-fok rfcl-fok rfcl-file-rows fn-sn-crash
        fn-sn-update-indexed fn-sn-with-consumer fn-sn-with-topic
        fn-sn-files-of-fn-sn-with-event-index fn-sn-fields-of-fn-sn-make-v6
        fn-sf-crash fn-sf-record-present-visiblep fn-sf-frontier-new-visiblep
        fn-sf-phase-of-fn-sf-make fn-sf-records-of-fn-sf-make
        (:e fn-rfcl-pending-phasep) (:e member-equal))
      (theory 'minimal-theory))))))

(local
 (defthm rfcl-prc-change-is-staged
  (implies (not (equal (fn-prc-spc-prepare s row view carry) s))
           (equal (fn-sf-phase (fn-sn-files (fn-prc-spc-prepare s row view carry)))
                  :record-staged))
  :hints (("Goal" :in-theory (union-theories
    '(fn-prc-spc-prepare fn-cstp-sn-update-fields)
    (theory 'minimal-theory))))))

(local
 (defthm rfcl-ccar-identity-change-facts
  (let ((next (fn-ccar-sn-prepare-identity s event)))
    (implies (not (equal next s))
             (and (fn-sn-statep next)
                  (equal (fn-sf-phase (fn-sn-files next)) :record-staged)
                  (equal (fn-sf-records (fn-sn-files next))
                         (fn-sf-records (fn-sn-files s))))))
  :hints (("Goal" :in-theory (union-theories
    '(fn-ccar-sn-prepare-identity rfcl-update-statep rfcl-stage-files-facts
      fn-cstp-sn-update-fields fn-sn-statep)
    (theory 'minimal-theory))))))

(local
 (defthm rfcl-article-prepare-crash
  (implies (and (fn-rfcl-okp (fn-sbud-oc-store oc) fn-arena)
                (fn-sf-crash-choicep frontier-choice record-choice))
           (fn-rfcl-okp (fn-sn-crash
                         (fn-sbud-oc-store (mv-nth 1 (fn-pout-prepare-article oc row budget carry)))
                         frontier-choice record-choice) fn-arena))
  :hints (("Goal"
    :use ((:instance fn-pout-store-of-psrv-prepare (record row))
          (:instance rfcl-prc-prepared-facts (s (fn-sbud-oc-store oc))
                     (view (fn-own-view (fn-ocfg-owner oc))))
          (:instance rfcl-prc-change-is-staged (s (fn-sbud-oc-store oc))
                     (view (fn-own-view (fn-ocfg-owner oc))))
          (:instance rfcl-crash-staged-restores-records (s (fn-sbud-oc-store oc))
            (next (fn-prc-spc-prepare (fn-sbud-oc-store oc) row (fn-own-view (fn-ocfg-owner oc)) carry))))
    :in-theory (union-theories
      '(fn-pout-prepare-article-answers-the-store-change rfcl-lv6)
      (theory 'minimal-theory))))))

(local
 (defthm rfcl-identity-prepare-crash
  (implies (and (fn-rfcl-okp (fn-sbud-oc-store oc) fn-arena)
                (fn-sf-crash-choicep frontier-choice record-choice))
           (fn-rfcl-okp (fn-sn-crash
                         (fn-sbud-oc-store (mv-nth 1 (fn-pout-prepare-identity oc w h)))
                         frontier-choice record-choice) fn-arena))
  :hints (("Goal"
    :use ((:instance fn-pout-store-of-oiis-prepare-identity)
          (:instance rfcl-ccar-identity-change-facts (s (fn-sbud-oc-store oc))
            (event (fn-oii-identity-row w (fn-sn-keyring (fn-sbud-oc-store oc))
                                        (fn-sn-keyring-generation (fn-sbud-oc-store oc)) h)))
          (:instance rfcl-crash-staged-restores-records (s (fn-sbud-oc-store oc))
            (next (fn-ccar-sn-prepare-identity (fn-sbud-oc-store oc)
                    (fn-oii-identity-row w (fn-sn-keyring (fn-sbud-oc-store oc))
                                        (fn-sn-keyring-generation (fn-sbud-oc-store oc)) h)))))
    :in-theory (union-theories
      '(fn-pout-prepare-identity-answers-the-store-change rfcl-lv6)
      (theory 'minimal-theory))))))

(local (in-theory (union-theories '(rfcl-article-prepare-crash) (theory 'minimal-theory))))
(defthm fn-rfcl-crash-after-prepare-article-keeps-okp
  (let* ((s (fn-sbud-oc-store oc))
         (row (fn-intern-row-at record (fn-sn-keyring s) (fn-sn-keyring-generation s)
                                (fn-arena-count fn-arena)))
         (out (fn-pout-prepare-article oc row budget carry)))
    (implies (and (fn-rfcl-okp s fn-arena)
                  (fn-sf-crash-choicep frontier-choice record-choice))
             (fn-rfcl-okp (fn-sn-crash (fn-sbud-oc-store (mv-nth 1 out))
                                       frontier-choice record-choice)
                          fn-arena))))

(local (in-theory (union-theories '(rfcl-identity-prepare-crash) (theory 'minimal-theory))))
(defthm fn-rfcl-crash-after-prepare-identity-keeps-okp
  (let* ((s (fn-sbud-oc-store oc))
         (out (fn-pout-prepare-identity oc w (fn-arena-count fn-arena))))
    (implies (and (fn-rfcl-okp s fn-arena)
                  (fn-sf-crash-choicep frontier-choice record-choice))
             (fn-rfcl-okp (fn-sn-crash (fn-sbud-oc-store (mv-nth 1 out))
                                       frontier-choice record-choice)
                          fn-arena))))
