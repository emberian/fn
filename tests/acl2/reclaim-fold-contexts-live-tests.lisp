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


(set-guard-checking :none)

(defconst *rfcllive-wire*
  (fn-record-make 1 1 1 "<rfcllive@example.invalid>" '(76 13 10) *sit-groups*
                  "rfcllive-obligation" "rfcllive-subject" "rfcllive-release" 2 841000000))

(defun rfcllive-check (s fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv (list :okp (fn-rfcl-okp s fn-arena)
            :phase (fn-sf-phase (fn-sn-files s))
            :records (len (fn-sf-records (fn-sn-files s)))
            :rows (len (fn-rfcl-rows s))
            :count (fn-arena-count fn-arena)) fn-arena))

(defconst *rfcllive-configs2*
  (list *fn-cfg-default-record*
        (fn-cfg-record-make 1 0 2
           (list (fn-cfg-create-group "example" *fn-cfg-default-policy-id*))
           *fn-cfg-default-stamp*)))

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
(assert-event (rfcllive-run-reference))

(assert-event (equal (rfcllive-run-entry nil)
                     '(:before (:owner t :retained t :record t :okp t :arena t :count 0) :word :prepared :changed t :sealed t :after-okp t :count 1 :candidate t)))

(assert-event (equal (rfcllive-run-entry t)
                     '(:before (:owner t :retained t :record t :okp t :arena t :count 0) :word :prepared :changed t :sealed t :after-okp t :count 1 :candidate t)))

; Invariant teeth: the historical stale composite has payloads in-range,
; but carries generation 0 after the generation-1 enrollment.
(assert-event (equal (rfcllive-run-stale-composite2)
                     '(:okp nil :phase :ready :records 2 :rows 2 :count 1)))
; LV-2 removal: all retainedness conjuncts except resolution remain true;
; the entry really stages a generation-0 row and its conclusion is NIL.
(assert-event
 (equal (rfcllive-run-resolution-teeth2)
        '((:good-retained t :good-csi t :before-ok t :bad-retained nil
           :live t :resolved nil :verdict t :index t :event-index-empty t :csi t)
          :changed t :after-ok nil :phase :record-staged :row-generation 0)))
; LV-3 mutation: replacing the outcome entry with raw fn-sn-prepare-identity
; accepts a composite interned at a stale generation, despite retainedness
; and the invariant both being T before.  The exact seal leaves NIL.
(assert-event
 (equal (rfcllive-run-identity-mutation)
        '(:before (:retained t :okp t :generation 1) :composite t
          :row-generation 0 :changed t :phase :record-staged :after-okp nil
          :published-finished-okp nil)))

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
(assert-event
 (equal (rfcllive-run-known-abort)
        '(:before (:owner t :retained t :record t :okp t :arena t :count 0)
          :word :prepared :staged-phase :record-staged :unsealed-okp nil
          :abort-word :aborted :after-phase :ready :after-okp t :count 0)))
