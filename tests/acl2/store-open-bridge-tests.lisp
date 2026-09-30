; Teeth for books/store-open-bridge.lisp.  The witness is the host's open
; (fn-cpo-open-observed, host/store-node-host.lisp:159) of a crash image of
; the K5 fixture's second publication: the linked cut, kept, so the scanned
; journal holds two acknowledged-shape records at frontier 2.
(in-package "ACL2")
(include-book "../../books/store-open-bridge")
(include-book "byte-store-stable-prefix-tests")
(include-book "must-fail-checked")

(defconst *sobt-configs* (list *fn-cfg-default-record*))
; Two configuration records, both at sequence 0: the second replays to
; (:fault ... :config-sequence).  A non-empty journal, so the open reaches
; the replay rather than its (null configs) refusal.
(defconst *sobt-fault-configs* (list *fn-cfg-default-record* *fn-cfg-default-record*))

(defun sobt-image ()
  (let ((pair (bsk5-linked-2)))
    (fn-bs-crash (car pair)
                 (fn-bs-view-choices (fn-bs-pending (car pair)) (fn-bs-unit (car pair))))))
(defun sobt-f () (fn-bs-scan-frontier (fn-bs-scan-store (sobt-image))))
; The host opens over the retained rows whose alpha is the scan (the intern
; of the scanned frames): the dying process's own rows at the crash pair.
(defun sobt-r () (fn-bs-scanned-rows (cdr (bsk5-linked-2)) (sobt-image) *bsk5-arena*))
(defun sobt-host (configs) (fn-cpo-open-observed configs (sobt-f) (sobt-r)))
(defun sobt-model (groups capacity)
  (fn-sn-open-observed groups capacity (sobt-f) (sobt-r)))
(defun sobt-files (opened) (fn-sn-files (fn-sn-open-state opened)))

; The image is non-trivial: two records, frontier 2.
(assert-event (and (equal (len (sobt-r)) 2) (equal (sobt-f) 2)))

; Witness for fn-cpo-open-observed-is-sn-open-observed-on-the-kernel: both
; hypotheses hold, the host opens, and the kernels agree.
(assert-event
 (and (fn-sn-open-okp (sobt-model *bsk5-groups* *bsk5-capacity*))
      (fn-sob-configured-openp *sobt-configs* (sobt-f) (sobt-r))
      (fn-sn-open-okp (sobt-host *sobt-configs*))
      (equal (sobt-files (sobt-host *sobt-configs*))
             (sobt-files (sobt-model *bsk5-groups* *bsk5-capacity*)))
      (equal (sobt-files (sobt-host *sobt-configs*))
             (fn-bs-recovered-kernel (sobt-f) (sobt-r) 0))))

; Witness for fn-cpo-open-observed-succeeds-exactly: every conjunct.
(assert-event
 (and (fn-sn-observed-historyp (sobt-f) (sobt-r))
      (fn-sn-observed-identity-okp (sobt-r))
      (fn-sn-observed-consumer-okp (sobt-r))
      (fn-sn-observed-topic-okp (sobt-r))
      (fn-sob-identity-typedp (sobt-r))))

; The corollaries' conclusions at the witness.
(assert-event
 (let ((st (fn-sn-open-state (sobt-host *sobt-configs*))))
   (and (equal (fn-sf-records (fn-sn-files st)) (sobt-r))
        (equal (fn-sf-phase (fn-sn-files (fn-sn-observed-rebarrier st 2))) :recovering)
        (equal (fn-sf-phase (fn-sn-files (fn-sn-observed-rebarrier st 3))) :ready)
        (fn-cpo-history-relation st))))

; Drop fn-sob-configured-openp: a configuration journal that replays :fault.
; The store-only open still succeeds on the same image; the host's refuses.
(assert-event
 (and (equal (fn-replay-result-kind (fn-cpr-replay *sobt-fault-configs* (sobt-r))) :fault)
      (not (fn-sob-configured-openp *sobt-fault-configs* (sobt-f) (sobt-r)))
      (fn-sn-open-okp (sobt-model *bsk5-groups* *bsk5-capacity*))))
(must-fail-checked
 (assert-event (fn-sn-open-okp (sobt-host *sobt-fault-configs*))))

; Drop the store-only open's success: with no groups the fixed-table replay
; refuses the journal.  The host still opens, but the kernels differ, so the
; second conclusion needs the first hypothesis.
(assert-event
 (and (not (fn-sn-open-okp (sobt-model nil *bsk5-capacity*)))
      (fn-sn-open-okp (sobt-host *sobt-configs*))))
(must-fail-checked
 (assert-event
  (equal (sobt-files (sobt-host *sobt-configs*))
         (sobt-files (sobt-model nil *bsk5-capacity*)))))

; Observed, not proved: with one configuration record the host's opened
; state is the store-only one opened under that configuration's own table
; and capacity, with the configuration history installed.  A theorem of this
; form needs a node correspondence between fn-cpr-replay and fn-replay; it
; would carry fn-snt-relation, and so the two theorems that do not transfer.
(assert-event
 (let* ((cn (fn-replay-result-node (fn-cpr-replay *sobt-configs* (sobt-r))))
        (m (sobt-model (fn-cnode-domain-of (fn-cnode-config cn))
                       (fn-cfg-capacity (fn-cfg-value (fn-cnode-config cn))))))
   (and (fn-sn-open-okp m)
        (equal (fn-cpo-install (fn-sn-open-state m) cn *sobt-configs*)
               (fn-sn-open-state (sobt-host *sobt-configs*)))
        (fn-snt-relation (fn-sn-open-state (sobt-host *sobt-configs*))))))

;;; KEYSTONE fn-bs-store-recovery-is-a-kernel-crash (PRF-041, row B25 of planning/evidence/vacuity-audit-2026-09-29.md)
;;; Recovering a model crash image of a related pair is the kernel's image
;;; crash at the scanned frontier and rows: same frontier, same rows, whose
;;; wire is the scanned records, in phase :replaying.
(defun sobt-crashed (ks image)
  (fn-sf-image-crash ks (fn-bs-scan-frontier (fn-bs-scan-store image))
                     (fn-bs-scanned-rows ks image *bsk5-arena*)))
(defun sobt-crash-okp (ks image)
  (let ((scan (fn-bs-scan-store image))
        (rows (fn-bs-scanned-rows ks image *bsk5-arena*))
        (crashed (sobt-crashed ks image)))
    (and (equal (fn-sf-frontier crashed) (fn-bs-scan-frontier scan))
         (equal (fn-sf-records crashed) rows)
         (equal (fn-bs-rows-wire (fn-sf-records crashed) *bsk5-arena*)
                (fn-bs-scan-records scan))
         (equal (fn-sf-phase crashed) :replaying))))
;; fn-bs-crash-imagep is a defun-sk: the image is admitted by its choices.
(defun sobt-choices ()
  (let ((bs (car (bsk5-linked-2))))
    (fn-bs-view-choices (fn-bs-pending bs) (fn-bs-unit bs))))
(assert-event
 (let ((bs (car (bsk5-linked-2))))
   (and (fn-bs-crash-choicesp (sobt-choices) (fn-bs-pending bs) (fn-bs-unit bs))
        (equal (sobt-image) (fn-bs-crash bs (sobt-choices))))))
(defthm sobt-image-is-a-crash-image
  (fn-bs-crash-imagep (car (bsk5-linked-2)) (sobt-image))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bs-crash-imagep-suff
                                   (s (car (bsk5-linked-2))) (image (sobt-image))
                                   (choices (sobt-choices))))
           :in-theory (disable fn-bs-crash-imagep))))
(assert-event
 (let ((bs (car (bsk5-linked-2))) (ks (cdr (bsk5-linked-2))) (image (sobt-image)))
   (and (fn-bs-store-relation bs ks *bsk5-arena*)
        (consp (fn-sf-records ks))
        (equal (len (fn-bs-scan-records (fn-bs-scan-store image))) 2)
        (sobt-crash-okp ks image)
        (equal (sobt-crashed ks image)
               (fn-sf-image-crash (cdr (bsk5-linked-2)) (sobt-f) (sobt-r))))))
; Drop the relation: the quiet bytes after the first finish have a legal
; all-empty choice list, whose crash image they are; they do not relate to
; the second publication's linked kernel, and the recovered rows are not the
; scanned ones.
(defthm sobt-legal-choice-constructs-crash-image
  (implies (fn-bs-crash-choicesp choices (fn-bs-pending bs) (fn-bs-unit bs))
           (fn-bs-crash-imagep bs (fn-bs-crash bs choices)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bs-crash-imagep-suff
                                   (s bs) (image (fn-bs-crash bs choices)))))))
(defun sobt-quiet () (car (bsk5-finished)))
(assert-event
 (and (not (fn-bs-store-relation (sobt-quiet) (cdr (bsk5-linked-2)) *bsk5-arena*))
      (fn-bs-crash-choicesp nil (fn-bs-pending (sobt-quiet)) (fn-bs-unit (sobt-quiet)))
      (equal (fn-bs-crash (sobt-quiet) nil) (sobt-quiet))))
(must-fail-checked
 (assert-event (sobt-crash-okp (cdr (bsk5-linked-2)) (fn-bs-crash (sobt-quiet) nil))))
