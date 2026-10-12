; Ground witnesses and teeth for reclaim-fold-contexts-live's live entries.
; Enrollment is recovered and reserved before either entry; the arena is a
; fresh real local stobj.  Equality of the complete diagnostic results checks
; every antecedent, actual staging (:prepared), a retained candidate, one
; seal, and the conclusion for LV-2h/LV-3. LV-2k prepares and aborts without
; sealing. Signature observations in the fixture remain
; within the fixture's documented crypto trust boundary.
(in-package "ACL2")
(include-book "../../books/reclaim-fold-contexts-live")
(include-book "store-identity-traces-tests")



(with-guard-checking-event
 :none
 (defconst *rfcllive-wire*
   (fn-record-make 1 1 1 "<rfcllive@example.invalid>" '(76 13 10) *sit-groups*
                   "rfcllive-obligation" "rfcllive-subject" "rfcllive-release" 2 841000000)))

(defun rfcllive-check (s fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv (list :okp (fn-rfcl-okp s fn-arena)
            :phase (fn-sf-phase (fn-sn-files s))
            :records (len (fn-sf-records (fn-sn-files s)))
            :rows (len (fn-rfcl-rows s))
            :count (fn-arena-count fn-arena)) fn-arena))

(with-guard-checking-event
 :none
 (defconst *rfcllive-configs2*
   (list *fn-cfg-default-record*
         (fn-cfg-record-make 1 0 2
            (list (fn-cfg-create-group "example" *fn-cfg-default-policy-id*))
            *fn-cfg-default-stamp*))))

(make-event `(defconst *rfcllive-open* ',(fn-cpo-open-observed *rfcllive-configs2* 1 (list *sit-enrollment*))))

(make-event `(defconst *rfcllive-good* ',(fn-sit-barriers (fn-sn-open-state *rfcllive-open*) *fn-sf-recovery-barrier-count*)))

(defun rfcllive-run-stale-composite2 ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (answer fn-arena)
      (let ((fn-arena (fn-arena-seal-list *sit-source* fn-arena)))
        (rfcllive-check *sit-after-composite* fn-arena))
      answer)))

(defun rfcllive-resolution-teeth2 (fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let* ((good (fn-sit-reserve *rfcllive-good*))
         (bad (update-nth 6 0 good))
         (before (list :good-retained (fn-osr-retainedp good)
                       :good-csi (fn-csi-livep good)
                       :before-ok (fn-rfcl-okp bad fn-arena)
                       :bad-retained (fn-osr-retainedp bad)
                       :live (fn-osr-livep bad) :resolved (fn-skp-resolvedp bad)
                       :verdict (fn-osr-verdict-prefixp bad)
                       :index (fn-osr-frozen-index-prefixp bad)
                       :event-index-empty (equal (fn-sn-event-index bad) nil)
                       :csi (fn-csi-livep bad))))
    (mv-let (after fn-arena) (fn-store-prepare-interned bad *rfcllive-wire* fn-arena)
      (mv (list before :changed (not (equal after bad))
                :after-ok (fn-rfcl-okp after fn-arena)
                :phase (fn-sf-phase (fn-sn-files after))
                :row-generation (fn-hc-generation
                        (fn-held-context (fn-sf-record-candidate (fn-sn-files after)))))
          fn-arena))))

(defun rfcllive-run-resolution-teeth2 ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (answer fn-arena) (rfcllive-resolution-teeth2 fn-arena) answer)))

(defun rfcllive-identity-mutation (fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let* ((s (fn-sit-reserve *rfcllive-good*))
         (before (list :retained (fn-osr-retainedp s)
                       :okp (fn-rfcl-okp s fn-arena)
                       :generation (fn-sn-keyring-generation s)))
         (row (fn-oii-identity-row *sit-composite-wire* (fn-sn-keyring s)
                                  0 (fn-arena-count fn-arena)))
         (s2 (fn-sn-prepare-identity s row))
         (fn-arena (if (not (equal s2 s))
                       (fn-arena-seal-list (fn-oii-identity-payload *sit-composite-wire*) fn-arena)
                     fn-arena)))
    (mv (list :before before :composite (fn-hstxa-p row)
              :row-generation (fn-hc-generation (fn-held-context (fn-hstxa-held row)))
              :changed (not (equal s2 s))
              :phase (fn-sf-phase (fn-sn-files s2))
              :after-okp (fn-rfcl-okp s2 fn-arena)
              :published-finished-okp (fn-rfcl-okp (fn-sn-finish (fn-sit-publish s2)) fn-arena))
        fn-arena)))

(defun rfcllive-run-identity-mutation ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (answer fn-arena) (rfcllive-identity-mutation fn-arena) answer)))

(defun rfcllive-ready-owner (fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-ocfg-run
   (fn-ock-recover-extended
    (fn-sco-capture *rfcllive-configs2* (list *sit-enrollment*)) *rfcllive-configs2* 1 2)
   '((:store (:io :recovery-barrier :ok))
     (:store (:io :recovery-barrier :ok))
     (:store (:io :recovery-barrier :ok))
     (:store (:io :start-frontier nil))
     (:store (:io :frontier-file :ok))
     (:store (:io :frontier-replace :ok))
     (:store (:io :frontier-directory :ok))) fn-arena))

(defun rfcllive-entry (identityp fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let* ((oc (rfcllive-ready-owner fn-arena))
         (s (fn-sbud-oc-store oc))
         (row (fn-intern-row-at *rfcllive-wire* (fn-sn-keyring s)
                               (fn-sn-keyring-generation s) (fn-arena-count fn-arena)))
         (before (list :owner (fn-own-relation (fn-ocfg-owner oc))
                       :retained (fn-osr-retainedp s) :record (fn-record-p *rfcllive-wire*)
                       :okp (fn-rfcl-okp s fn-arena)
                       :arena (fn-arena-p fn-arena) :count (fn-arena-count fn-arena))))
    (mv-let (word oc2)
      (if identityp (fn-pout-prepare-identity oc *sit-composite-wire* (fn-arena-count fn-arena))
        (fn-pout-prepare-article oc row 100
          (fn-prc-refresh nil (fn-node-retention (fn-sn-node s)))))
      (let* ((s2 (fn-sbud-oc-store oc2))
             (sealsp (and (equal word :prepared)
                          (or (not identityp) (fn-oii-identity-sealsp *sit-composite-wire*))))
             (fn-arena (if sealsp
                           (fn-arena-seal-list
                            (if identityp (fn-oii-identity-payload *sit-composite-wire*)
                              (fn-record-payload *rfcllive-wire*)) fn-arena)
                         fn-arena)))
        (mv (list :before before :word word :changed (not (equal s s2))
                  :sealed sealsp :after-okp (fn-rfcl-okp s2 fn-arena)
                  :count (fn-arena-count fn-arena)
                  :candidate (fn-orcr-retained-p (fn-sf-record-candidate (fn-sn-files s2))))
            fn-arena)))))

(defun rfcllive-run-entry (identityp)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (answer fn-arena) (rfcllive-entry identityp fn-arena) answer)))

(defun rfcllive-reference (fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let* ((s (fn-sit-reserve *rfcllive-good*))
         (before (and (fn-osr-retainedp s) (fn-rfcl-okp s fn-arena))))
    (mv-let (s2 fn-arena) (fn-store-prepare-interned s *rfcllive-wire* fn-arena)
      (mv (and before (not (equal s2 s))
               (equal (fn-sf-phase (fn-sn-files s2)) :record-staged)
               (fn-held-p (fn-sf-record-candidate (fn-sn-files s2)))
               (equal (fn-arena-count fn-arena) 1)
               (fn-rfcl-okp s2 fn-arena)) fn-arena))))
(defun rfcllive-run-reference ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (answer fn-arena) (rfcllive-reference fn-arena) answer)))
(with-guard-checking-event
 :none
 (assert-event (rfcllive-run-reference)))

(with-guard-checking-event
 :none
 (assert-event (equal (rfcllive-run-entry nil)
                      '(:before (:owner t :retained t :record t :okp t :arena t :count 0) :word :prepared :changed t :sealed t :after-okp t :count 1 :candidate t))))

(with-guard-checking-event
 :none
 (assert-event (equal (rfcllive-run-entry t)
                      '(:before (:owner t :retained t :record t :okp t :arena t :count 0) :word :prepared :changed t :sealed t :after-okp t :count 1 :candidate t))))

; Invariant teeth: the historical stale composite has payloads in-range,
; but carries generation 0 after the generation-1 enrollment.
(with-guard-checking-event
 :none
 (assert-event (equal (rfcllive-run-stale-composite2)
                      '(:okp nil :phase :ready :records 2 :rows 2 :count 1))))
; LV-2 removal: all retainedness conjuncts except resolution remain true;
; the entry really stages a generation-0 row and its conclusion is NIL.
(with-guard-checking-event
 :none
 (assert-event
  (equal (rfcllive-run-resolution-teeth2)
         '((:good-retained t :good-csi t :before-ok t :bad-retained nil
            :live t :resolved nil :verdict t :index t :event-index-empty t :csi t)
           :changed t :after-ok nil :phase :record-staged :row-generation 0))))
; LV-3 mutation: replacing the outcome entry with raw fn-sn-prepare-identity
; accepts a composite interned at a stale generation, despite retainedness
; and the invariant both being T before.  The exact seal leaves NIL.
(with-guard-checking-event
 :none
 (assert-event
  (equal (rfcllive-run-identity-mutation)
         '(:before (:retained t :okp t :generation 1) :composite t
           :row-generation 0 :changed t :phase :record-staged :after-okp nil
           :published-finished-okp nil))))

(defun rfcllive-known-abort (fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let* ((oc (rfcllive-ready-owner fn-arena))
         (s (fn-sbud-oc-store oc))
         (row (fn-intern-row-at *rfcllive-wire* (fn-sn-keyring s)
                               (fn-sn-keyring-generation s) (fn-arena-count fn-arena)))
         (before (list :owner (fn-own-relation (fn-ocfg-owner oc))
                       :retained (fn-osr-retainedp s) :record (fn-record-p *rfcllive-wire*)
                       :okp (fn-rfcl-okp s fn-arena)
                       :arena (fn-arena-p fn-arena) :count (fn-arena-count fn-arena))))
    (mv-let (word oc2)
      (fn-pout-prepare-article oc row 100
        (fn-prc-refresh nil (fn-node-retention (fn-sn-node s))))
      (mv-let (abort-word oc3) (fn-pout-known-abort oc2 fn-arena)
        (mv (list :before before :word word
                  :staged-phase (fn-sf-phase (fn-sn-files (fn-sbud-oc-store oc2)))
                  :unsealed-okp (fn-rfcl-okp (fn-sbud-oc-store oc2) fn-arena)
                  :abort-word abort-word
                  :after-phase (fn-sf-phase (fn-sn-files (fn-sbud-oc-store oc3)))
                  :after-okp (fn-rfcl-okp (fn-sbud-oc-store oc3) fn-arena)
                  :count (fn-arena-count fn-arena))
            fn-arena)))))

(defun rfcllive-run-known-abort ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (answer fn-arena) (rfcllive-known-abort fn-arena) answer)))

; LV-2k: all antecedents hold; the staged candidate has no sealed payload.
; Known abort restores the invariant and leaves the real arena empty.
(with-guard-checking-event
 :none
 (assert-event
  (equal (rfcllive-run-known-abort)
         '(:before (:owner t :retained t :record t :okp t :arena t :count 0)
           :word :prepared :staged-phase :record-staged :unsealed-okp nil
           :abort-word :aborted :after-phase :ready :after-okp t :count 0))))

; v5: actual carried deferred prepares and the grant/outcome entries.
(with-guard-checking-event :none
 (defconst *rfclv5-retention*
  (fn-store-retention-event-make :undertake 1 1 1 "rfclv5-obligation"
                               "rfclv5-subject" "rfclv5-evidence" 5)))

(with-guard-checking-event :none
 (defconst *rfclv5-consumer* (fn-cpe-make 1 1 1 '(:bootstrap (1) (2)))))

(with-guard-checking-event :none
 (defconst *rfclv5-topic*
  (fn-stmt-value (fn-th-local-admin-install 1 1 1 501 (make-list 32 :initial-element 61) nil))))

(defun rfclv5-staging (kind entryp badp fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let* ((ready (rfcllive-ready-owner fn-arena))
         (oc (if badp (fn-ocfg-with-owner ready (fn-ocl-owner-with-store (fn-ocfg-owner ready) *sit-after-composite*)) ready))
         (s (fn-sbud-oc-store oc))
         (e (cond ((equal kind :retention) *rfclv5-retention*)
                  ((equal kind :consumer) *rfclv5-consumer*)
                  (t *rfclv5-topic*)))
         (grant (list :identity-grant (1- (fn-sf-frontier (fn-sn-files s))) e))
         (out (cond ((equal kind :retention) (mv-list 4 (fn-idrp-prepare-retention oc e grant fn-arena)))
                    ((equal kind :consumer) (mv-list 2 (fn-pdc-pout-prepare-consumer oc e)))
                    (t (mv-list 2 (fn-pdc-pout-prepare-topic oc e)))))
         (next (if entryp (fn-sbud-oc-store (mv-nth 1 out))
                 (cond ((equal kind :retention) (fn-pdc-sn-prepare-retention s e))
                       ((equal kind :consumer) (fn-pdc-sn-prepare-consumer s e))
                       (t (fn-pdc-sn-prepare-topic s e))))))
    (mv (list :before-okp (fn-rfcl-okp s fn-arena)
              :before-phase (fn-sf-phase (fn-sn-files s))
              :entry-word (mv-nth 0 out)
              :changed (not (equal next s))
              :after-phase (fn-sf-phase (fn-sn-files next))
              :candidate (equal (fn-sf-record-candidate (fn-sn-files next)) e)
              :after-okp (fn-rfcl-okp next fn-arena)
              :count (fn-arena-count fn-arena)) fn-arena)))

(defun rfclv5-run-staging (kind entryp badp)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (answer fn-arena) (rfclv5-staging kind entryp badp fn-arena) answer)))

; Whole antecedent and real staging.
(with-guard-checking-event :none
 (assert-event (equal (rfclv5-run-staging :retention nil nil)
                      '(:before-okp t :before-phase :reserved :entry-word :prepared :changed t :after-phase :record-staged :candidate t :after-okp t :count 0))))
(with-guard-checking-event :none
 (assert-event (equal (rfclv5-run-staging :consumer nil nil)
                      '(:before-okp t :before-phase :reserved :entry-word :prepared :changed t :after-phase :record-staged :candidate t :after-okp t :count 0))))
(with-guard-checking-event :none
 (assert-event (equal (rfclv5-run-staging :topic nil nil)
                      '(:before-okp t :before-phase :reserved :entry-word :prepared :changed t :after-phase :record-staged :candidate t :after-okp t :count 0))))
(with-guard-checking-event :none
 (assert-event (equal (rfclv5-run-staging :retention t nil)
                      '(:before-okp t :before-phase :reserved :entry-word :prepared :changed t :after-phase :record-staged :candidate t :after-okp t :count 0))))
(with-guard-checking-event :none
 (assert-event (equal (rfclv5-run-staging :consumer t nil)
                      '(:before-okp t :before-phase :reserved :entry-word :prepared :changed t :after-phase :record-staged :candidate t :after-okp t :count 0))))
(with-guard-checking-event :none
 (assert-event (equal (rfclv5-run-staging :topic t nil)
                      '(:before-okp t :before-phase :reserved :entry-word :prepared :changed t :after-phase :record-staged :candidate t :after-okp t :count 0))))

; Removal of the sole input-invariant hypothesis; refused no-op control.
(with-guard-checking-event :none
 (assert-event (equal (rfclv5-run-staging :retention nil t)
                      '(:before-okp nil :before-phase :ready :entry-word :refused :changed nil :after-phase :ready :candidate nil :after-okp nil :count 0))))
(with-guard-checking-event :none
 (assert-event (equal (rfclv5-run-staging :consumer nil t)
                      '(:before-okp nil :before-phase :ready :entry-word :refused :changed nil :after-phase :ready :candidate nil :after-okp nil :count 0))))
(with-guard-checking-event :none
 (assert-event (equal (rfclv5-run-staging :topic nil t)
                      '(:before-okp nil :before-phase :ready :entry-word :refused :changed nil :after-phase :ready :candidate nil :after-okp nil :count 0))))
(with-guard-checking-event :none
 (assert-event (equal (rfclv5-run-staging :retention t t)
                      '(:before-okp nil :before-phase :ready :entry-word :refused :changed nil :after-phase :ready :candidate nil :after-okp nil :count 0))))
(with-guard-checking-event :none
 (assert-event (equal (rfclv5-run-staging :consumer t t)
                      '(:before-okp nil :before-phase :ready :entry-word :refused :changed nil :after-phase :ready :candidate nil :after-okp nil :count 0))))
(with-guard-checking-event :none
 (assert-event (equal (rfclv5-run-staging :topic t t)
                      '(:before-okp nil :before-phase :ready :entry-word :refused :changed nil :after-phase :ready :candidate nil :after-okp nil :count 0))))

; LV-2c/LV-3c v6: positive valid-choice controls and choice-removal teeth.
; The invalid choices refuted the seat's v5 forms and falsify v6 without
; its new choice recognizer.
(defun rfclv5-crash-entry (identityp frontier-choice record-choice fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let* ((oc (rfcllive-ready-owner fn-arena))
         (s (fn-sbud-oc-store oc))
         (row (fn-intern-row-at *rfcllive-wire* (fn-sn-keyring s)
                               (fn-sn-keyring-generation s) (fn-arena-count fn-arena)))
         (before (list :retained (fn-osr-retainedp s)
                       :record (fn-record-p *rfcllive-wire*)
                       :okp (fn-rfcl-okp s fn-arena))))
    (mv-let (word next)
      (if identityp (fn-pout-prepare-identity oc *sit-composite-wire* (fn-arena-count fn-arena))
        (fn-pout-prepare-article oc row 100
          (fn-prc-refresh nil (fn-node-retention (fn-sn-node s)))))
      (let* ((staged (fn-sbud-oc-store next))
             (crashed (fn-sn-crash staged frontier-choice record-choice)))
        (mv (list :before before :word word
                  :staged-phase (fn-sf-phase (fn-sn-files staged))
                  :unsealed-okp (fn-rfcl-okp staged fn-arena)
                  :choicep (fn-sf-crash-choicep frontier-choice record-choice)
                  :unchanged (equal crashed staged)
                  :crash-phase (fn-sf-phase (fn-sn-files crashed))
                  :after-okp (fn-rfcl-okp crashed fn-arena)
                  :count (fn-arena-count fn-arena)) fn-arena)))))

(defun rfclv5-run-crash-entry (identityp frontier-choice record-choice)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (answer fn-arena)
      (rfclv5-crash-entry identityp frontier-choice record-choice fn-arena) answer)))
(with-guard-checking-event :none
 (assert-event (equal (rfclv5-run-crash-entry nil :old :present)
                      '(:before (:retained t :record t :okp t) :word :prepared :staged-phase :record-staged :unsealed-okp nil :choicep t :unchanged nil :crash-phase :replaying :after-okp t :count 0))))
(with-guard-checking-event :none
 (assert-event (equal (rfclv5-run-crash-entry t :old :present)
                      '(:before (:retained t :record t :okp t) :word :prepared :staged-phase :record-staged :unsealed-okp nil :choicep t :unchanged nil :crash-phase :replaying :after-okp t :count 0))))
(with-guard-checking-event :none
 (assert-event (equal (rfclv5-run-crash-entry nil :invalid :present)
                      '(:before (:retained t :record t :okp t) :word :prepared :staged-phase :record-staged :unsealed-okp nil :choicep nil :unchanged t :crash-phase :record-staged :after-okp nil :count 0))))
(with-guard-checking-event :none
 (assert-event (equal (rfclv5-run-crash-entry t :invalid :present)
                      '(:before (:retained t :record t :okp t) :word :prepared :staged-phase :record-staged :unsealed-okp nil :choicep nil :unchanged t :crash-phase :record-staged :after-okp nil :count 0))))

; LV-2c/LV-3c v6: input-invariant removal while every other hypothesis holds.
(defun rfclv6-invariant-removal (identityp fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let* ((oc (rfcllive-ready-owner fn-arena))
         (s (fn-sbud-oc-store oc))
         (row (fn-intern-row-at *rfcllive-wire* (fn-sn-keyring s)
                               (fn-sn-keyring-generation s) (fn-arena-count fn-arena))))
    (mv-let (word staged)
      (fn-pout-prepare-article oc row 100
        (fn-prc-refresh nil (fn-node-retention (fn-sn-node s))))
      (let* ((durable (fn-sn-finish (fn-sit-publish (fn-sbud-oc-store staged))))
             (oc2 (fn-ocfg-with-owner oc
                    (fn-ocl-owner-with-store (fn-ocfg-owner oc) durable)))
             (before (list :retained (fn-osr-retainedp durable)
                           :record (fn-record-p *rfcllive-wire*)
                           :okp (fn-rfcl-okp durable fn-arena)
                           :statep (fn-sn-statep durable))))
        (mv-let (word2 next)
          (if identityp (fn-pout-prepare-identity oc2 *sit-composite-wire* (fn-arena-count fn-arena))
            (fn-pout-prepare-article oc2 row 100 nil))
          (let ((crashed (fn-sn-crash (fn-sbud-oc-store next) :old :present)))
            (mv (list :first-word word :before before :word word2
                      :choicep (fn-sf-crash-choicep :old :present)
                      :crash-phase (fn-sf-phase (fn-sn-files crashed))
                      :after-okp (fn-rfcl-okp crashed fn-arena)
                      :count (fn-arena-count fn-arena)) fn-arena)))))))

(defun rfclv6-run-invariant-removal (identityp)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (answer fn-arena) (rfclv6-invariant-removal identityp fn-arena) answer)))
(with-guard-checking-event :none
 (assert-event (equal (rfclv6-run-invariant-removal nil)
   '(:first-word :prepared :before (:retained t :record t :okp nil :statep t)
     :word :refused :choicep t :crash-phase :replaying :after-okp nil :count 0))))
(with-guard-checking-event :none
 (assert-event (equal (rfclv6-run-invariant-removal t)
   '(:first-word :prepared :before (:retained t :record t :okp nil :statep t)
     :word :refused :choicep t :crash-phase :replaying :after-okp nil :count 0))))
