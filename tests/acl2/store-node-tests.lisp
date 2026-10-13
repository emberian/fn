; Executable live-node/file-kernel composition and spoofed-completion checks.
(in-package "ACL2")
(include-book "../../books/store-node-invariants")
(include-book "../../books/codec-attach")

(defconst *sn-groups* '("fn.letters" "fn.test"))
(defconst *sn-record*
  (fn-record-make 0 0 0 "<sn@example>" '(65 66) *sn-groups*
                  "sn-pin" "sn-content" "sn-release" 2 841000000))
; The store retains held rows (records-flip, books/held-record.lisp): the
; wire record's eleven positions with a payload handle in the arena.  No
; check below reads the bytes, so the row is the plain held row at handle 0.
(defconst *sn-row* (fn-held-plain *sn-record* 0))
(assert-event (fn-held-p *sn-row*))
(defun fn-sn-test-reserve (s)
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil)
                                :frontier-file :ok)
                      :frontier-replace :ok)
            :frontier-directory :ok))
(defun fn-sn-test-publish (s)
  (fn-sn-io (fn-sn-io (fn-sn-io s :record-file :ok)
                      :record-link :ok)
            :record-directory :ok))
(defun fn-sn-test-barriers (s n)
  (if (zp n) s
    (fn-sn-test-barriers (fn-sn-io s :recovery-barrier :ok) (1- n))))
(defconst *sn-initial* (fn-sn-initial *sn-groups* 10))
(defconst *sn-reserved* (fn-sn-test-reserve *sn-initial*))
(defconst *sn-prepared* (fn-sn-prepare *sn-reserved* *sn-row*))
(assert-event (fn-sn-statep *sn-prepared*))
(assert-event (equal (fn-sf-phase (fn-sn-files *sn-prepared*)) :record-staged))
(assert-event (fn-sn-record-bindsp (fn-sn-node *sn-prepared*) *sn-row*))
(assert-event (not (fn-state-articles (fn-node-acceptance (fn-sn-node *sn-prepared*)))))
(assert-event (not (fn-retain-pins (fn-node-retention (fn-sn-node *sn-prepared*)))))
(assert-event (equal (fn-sn-finish *sn-prepared*) *sn-prepared*))
; Host words cannot bypass the real completion operation.
(assert-event (equal (fn-sn-io *sn-prepared* :core-completion :matching) *sn-prepared*))
(assert-event (equal (fn-sn-io *sn-prepared* :emit-success :matching) *sn-prepared*))

(defconst *sn-completing* (fn-sn-test-publish *sn-prepared*))
(assert-event (equal (fn-sf-phase (fn-sn-files *sn-completing*)) :completing))
(assert-event (not (fn-sf-successes (fn-sn-files *sn-completing*))))
(defconst *sn-finished* (fn-sn-finish *sn-completing*))
(assert-event (fn-sn-statep *sn-finished*))
(assert-event (equal (fn-sf-successes (fn-sn-files *sn-finished*)) '((0 . 0))))
(assert-event (fn-sn-committed-recordp (fn-sn-node *sn-finished*) *sn-row*))
(assert-event (equal (fn-sn-node *sn-finished*)
                     (fn-sf-replay-node *sn-groups* 10 (list *sn-row*) 1)))
(assert-event (equal (fn-sn-finish *sn-finished*) *sn-finished*))

; A real but different pending node with the same sequence/txid/generation is
; insufficient: payload, groups, archive ID, subject, evidence and charge bind.
; The pending's payload is the row's handle (0); a different handle is a
; different payload.
(defun fn-sn-test-mismatched-pending (payload groups id subject evidence charge)
  (fn-sn-update *sn-completing* (fn-sn-files *sn-completing*)
    (fn-node-prepare (fn-sn-node *sn-initial*) 0 "<sn@example>" payload groups
                     id subject evidence charge 841000000)))
(assert-event (let ((s (fn-sn-test-mismatched-pending
                        1 *sn-groups* "sn-pin" "sn-content" "sn-release" 2)))
                (and (fn-sn-statep s) (equal (fn-sn-finish s) s))))
(assert-event (let ((s (fn-sn-test-mismatched-pending
                        0 '("fn.letters") "sn-pin" "sn-content" "sn-release" 2)))
                (and (fn-sn-statep s) (equal (fn-sn-finish s) s))))
(assert-event (let ((s (fn-sn-test-mismatched-pending
                        0 *sn-groups* "other-pin" "sn-content" "sn-release" 2)))
                (and (fn-sn-statep s) (equal (fn-sn-finish s) s))))
(assert-event (let ((s (fn-sn-test-mismatched-pending
                        0 *sn-groups* "sn-pin" "other-content" "sn-release" 2)))
                (and (fn-sn-statep s) (equal (fn-sn-finish s) s))))
(assert-event (let ((s (fn-sn-test-mismatched-pending
                        0 *sn-groups* "sn-pin" "sn-content" "other-release" 2)))
                (and (fn-sn-statep s) (equal (fn-sn-finish s) s))))
(assert-event (let ((s (fn-sn-test-mismatched-pending
                        0 *sn-groups* "sn-pin" "sn-content" "sn-release" 3)))
                (and (fn-sn-statep s) (equal (fn-sn-finish s) s))))

; Acknowledged content survives crash/replay and all three recovery barriers.
(defconst *sn-recovered*
  (fn-sn-test-barriers (fn-sn-recover (fn-sn-crash *sn-finished* :old :absent))
                       *fn-sf-recovery-barrier-count*))
(assert-event (fn-sn-statep *sn-recovered*))
(assert-event (equal (fn-sf-phase (fn-sn-files *sn-recovered*)) :ready))
(assert-event (equal (fn-sn-node *sn-recovered*) (fn-sn-node *sn-finished*)))
(assert-event (equal (fn-sf-successes (fn-sn-files *sn-recovered*)) '((0 . 0))))

; An uncertain link can recover the exact article without inventing an ACK;
; its absent outcome burns the allocated txid and leaves no partial article.
(defconst *sn-link-error*
  (fn-sn-io (fn-sn-io *sn-prepared* :record-file :ok) :record-link :error))
(defconst *sn-present*
  (fn-sn-recover (fn-sn-crash *sn-link-error* :old :present)))
(defconst *sn-absent*
  (fn-sn-recover (fn-sn-crash *sn-link-error* :old :absent)))

; Process death after os.link returned but before the link result was
; observed (the final-link cut) leaves the composition in :record-data-durable
; with the same two outcomes; both replay to the same nodes as the fenced
; link above, and neither invents an acknowledgement.
(defconst *sn-data-durable* (fn-sn-io *sn-prepared* :record-file :ok))
(assert-event (equal (fn-sf-phase (fn-sn-files *sn-data-durable*)) :record-data-durable))
(assert-event (equal (fn-sn-node (fn-sn-recover (fn-sn-crash *sn-data-durable* :old :present)))
                     (fn-sn-node *sn-present*)))
(assert-event (equal (fn-sn-node (fn-sn-recover (fn-sn-crash *sn-data-durable* :old :absent)))
                     (fn-sn-node *sn-absent*)))
(assert-event (not (fn-sf-successes
                    (fn-sn-files (fn-sn-recover (fn-sn-crash *sn-data-durable* :old :present))))))
; Death after the record file barrier returned but before it was observed
; (the staged-data-barrier cut) is in :record-staged: no link was issued, so
; the present choice selects nothing.
(assert-event (equal (fn-sf-records (fn-sn-files (fn-sn-crash *sn-prepared* :old :present)))
                     nil))
(assert-event (fn-sn-committed-recordp (fn-sn-node *sn-present*) *sn-row*))
(assert-event (not (fn-sf-successes (fn-sn-files *sn-present*))))
(assert-event (not (fn-state-articles (fn-node-acceptance (fn-sn-node *sn-absent*)))))
(assert-event (equal (fn-state-next-txid (fn-node-acceptance (fn-sn-node *sn-absent*))) 1))
(assert-event (equal (fn-sn-finish *sn-present*) *sn-present*))
; unreachable-in-composition: fn-sn-fence-node/fn-sn-resolve-node have no host
; caller; these two checks document the in-process correspondence only.
(assert-event (equal (fn-sn-node *sn-present*)
                     (fn-sn-resolve-node
                      (fn-sn-fence-node (fn-sn-node *sn-prepared*) *sn-row*)
                      *sn-row* t)))
(assert-event (equal (fn-sn-node *sn-absent*)
                     (fn-sn-resolve-node
                      (fn-sn-fence-node (fn-sn-node *sn-prepared*) *sn-row*)
                      *sn-row* nil)))

; Article constructor: reachable SAT, exact u64 teeth, and hypothesis removals.
(defun fn-sn-article-test-state (sequence txid)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((s (fn-sn-initial '("fn.test") 10))
         (node (fn-sn-node s))
         (a (fn-node-acceptance node)))
    (update-nth 9 sequence
      (fn-sn-update s (fn-sn-files s)
        (fn-node-make-state
          (fn-make-state (fn-state-groups a) (fn-state-nexts a)
                         (fn-state-articles a) txid nil nil)
          (fn-node-retention node) nil (fn-node-bindings node))))))
(defconst *sn-article-test-clock* (fn-clock-observation 0 1000 0 t))
(defconst *sn-article-test-fields*
  '("<seq@example>" (65) ("fn.test") "id" "subject" "evidence" 1))
(defun fn-sn-article-test-hypotheses (fields)
  (declare (xargs :guard t :verify-guards nil))
  (list (fn-record-msgidp (nth 0 fields))
        (fn-record-payloadp (nth 1 fields))
        (fn-record-groups-validp (nth 2 fields))
        (fn-record-metadata-bytes-p (nth 3 fields))
        (fn-record-metadata-bytes-p (nth 4 fields))
        (fn-record-metadata-bytes-p (nth 5 fields))
        (fn-record-uint64p (nth 6 fields))))
(defun fn-sn-article-test-result (fields)
  (declare (xargs :guard t :verify-guards nil))
  (fn-sn-article-record (fn-sn-article-test-state 0 0) *sn-article-test-clock*
    (nth 0 fields) (nth 1 fields) (nth 2 fields) (nth 3 fields)
    (nth 4 fields) (nth 5 fields) (nth 6 fields)))
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs *sn-article-test-clock*)
         (r (fn-sn-article-test-result *sn-article-test-fields*)))
   (and (fn-sn-statep (fn-sn-article-test-state 0 0))
        (equal (fn-sn-article-test-hypotheses *sn-article-test-fields*)
               '(t t t t t t t))
        (natp (fn-record-stamp-of-observation obs))
        (fn-record-uint64p (fn-sn-identity-next s))
        (fn-record-uint64p (fn-state-next-txid (fn-node-acceptance (fn-sn-node s))))
        (fn-record-p r)
        (equal r (fn-record-make 0 0 0 "<seq@example>" '(65) '("fn.test")
                                 "id" "subject" "evidence" 1 1))))))
(with-guard-checking-event :none
 (assert-event (equal (fn-sn-article-record (fn-sn-article-test-state (expt 2 64) 0) *sn-article-test-clock* "<seq@example>" '(65) '("fn.test") "id" "subject" "evidence" 1) :sequence-exhausted)))
(with-guard-checking-event :none
 (assert-event (equal (fn-sn-article-record (fn-sn-article-test-state 0 (expt 2 64)) *sn-article-test-clock* "<seq@example>" '(65) '("fn.test") "id" "subject" "evidence" 1) :txid-exhausted)))
(with-guard-checking-event :none
 (assert-event (fn-record-p (fn-sn-article-record (fn-sn-article-test-state (1- (expt 2 64)) (1- (expt 2 64))) *sn-article-test-clock* "<seq@example>" '(65) '("fn.test") "id" "subject" "evidence" 1))))
; Widening refusal 1: only copied field 1 is invalid.
(with-guard-checking-event :none
 (assert-event
  (let* ((fields (update-nth 0 "" *sn-article-test-fields*))
         (r (fn-sn-article-test-result fields)))
   (and (equal (fn-sn-article-test-hypotheses fields) '(nil t t t t t t))
        (not (fn-record-p r))
        (equal r :msgid-invalid)))))
; Widening refusal 2: only copied field 2 is invalid.
(with-guard-checking-event :none
 (assert-event
  (let* ((fields (update-nth 1 '(256) *sn-article-test-fields*))
         (r (fn-sn-article-test-result fields)))
   (and (equal (fn-sn-article-test-hypotheses fields) '(t nil t t t t t))
        (not (fn-record-p r))
        (equal r :payload-invalid)))))
; Widening refusal 3: only copied field 3 is invalid.
(with-guard-checking-event :none
 (assert-event
  (let* ((fields (update-nth 2 '("bad group") *sn-article-test-fields*))
         (r (fn-sn-article-test-result fields)))
   (and (equal (fn-sn-article-test-hypotheses fields) '(t t nil t t t t))
        (not (fn-record-p r))
        (equal r :groups-invalid)))))
; Widening refusal 4: only copied field 4 is invalid.
(with-guard-checking-event :none
 (assert-event
  (let* ((fields (update-nth 3 "" *sn-article-test-fields*))
         (r (fn-sn-article-test-result fields)))
   (and (equal (fn-sn-article-test-hypotheses fields) '(t t t nil t t t))
        (not (fn-record-p r))
        (equal r :obligation-id-invalid)))))
; Widening refusal 5: only copied field 5 is invalid.
(with-guard-checking-event :none
 (assert-event
  (let* ((fields (update-nth 4 "" *sn-article-test-fields*))
         (r (fn-sn-article-test-result fields)))
   (and (equal (fn-sn-article-test-hypotheses fields) '(t t t t nil t t))
        (not (fn-record-p r))
        (equal r :subject-invalid)))))
; Widening refusal 6: only copied field 6 is invalid.
(with-guard-checking-event :none
 (assert-event
  (let* ((fields (update-nth 5 "" *sn-article-test-fields*))
         (r (fn-sn-article-test-result fields)))
   (and (equal (fn-sn-article-test-hypotheses fields) '(t t t t t nil t))
        (not (fn-record-p r))
        (equal r :evidence-invalid)))))
; Widening refusal 7: only copied field 7 is invalid.
(with-guard-checking-event :none
 (assert-event
  (let* ((fields (update-nth 6 (expt 2 64) *sn-article-test-fields*))
         (r (fn-sn-article-test-result fields)))
   (and (equal (fn-sn-article-test-hypotheses fields) '(t t t t t t nil))
        (not (fn-record-p r))
        (equal r :charge-invalid)))))

; MUTATION: the old constructor falsifies S1 with all hypotheses true.
; Non-local: the defteeth mutation below calls it in certify-book pass 2.
(defun fn-sn-article-record-old-for-teeth (s obs msgid payload groups
                             obligation-id subject evidence charge)
 (declare (xargs :guard t))
 (let ((stamp (fn-record-stamp-of-observation obs))
       (txid (fn-state-next-txid (fn-node-acceptance (fn-sn-node s)))))
   (if (not (natp stamp))
       :clock-unusable
     (fn-record-make (fn-sn-identity-next s) txid txid msgid payload groups
                     obligation-id subject evidence charge stamp))))

(with-guard-checking-event :none
 (assert-event
  (let ((r (fn-sn-article-record-old-for-teeth
             (fn-sn-article-test-state (expt 2 64) 0) *sn-article-test-clock*
             "<seq@example>" '(65) '("fn.test") "id" "subject" "evidence" 1)))
   (and (fn-sn-statep (fn-sn-article-test-state 0 0))
        (equal (fn-sn-article-test-hypotheses *sn-article-test-fields*)
               '(t t t t t t t))
        (not (fn-record-p r))
        (not (member-equal r *fn-sn-article-record-refusals*))))))

; Clock refusal retains precedence when both allocation counters are exhausted.
(with-guard-checking-event :none
 (assert-event
  (equal (fn-sn-article-record
           (fn-sn-article-test-state (expt 2 64) (expt 2 64))
           (fn-clock-observation 0 1000 0 nil)
           "<seq@example>" '(65) '("fn.test") "id" "subject" "evidence" 1)
         :clock-unusable)))

; MUTATION: 74083e9a6 has no group codec bound at construction.
(local (defun fn-sn-article-record-u64-only-for-teeth (s obs msgid payload groups
                              obligation-id subject evidence charge)
  (declare (xargs :guard t))
  (let ((stamp (fn-record-stamp-of-observation obs))
        (txid (fn-state-next-txid (fn-node-acceptance (fn-sn-node s)))))
    (cond ((not (natp stamp)) :clock-unusable)
          ((not (fn-record-uint64p (fn-sn-identity-next s)))
           :sequence-exhausted)
          ((not (fn-record-uint64p txid)) :txid-exhausted)
          (t (fn-record-make (fn-sn-identity-next s) txid txid msgid payload groups
                             obligation-id subject evidence charge stamp))))))
(with-guard-checking-event :none
 (assert-event
  (let* ((g256 (coerce (make-list 256 :initial-element #\a) 'string))
         (g257 (coerce (make-list 257 :initial-element #\a) 'string))
         (valid (update-nth 2 (list g256) *sn-article-test-fields*))
         (invalid (update-nth 2 (list g257) *sn-article-test-fields*))
         (old (fn-sn-article-record-u64-only-for-teeth
               (fn-sn-article-test-state 0 0) *sn-article-test-clock*
               "<seq@example>" '(65) (list g257) "id" "subject" "evidence" 1)))
   (and (fn-record-p (fn-sn-article-test-result valid))
        (equal (fn-sn-article-test-result invalid) :groups-invalid)
        (not (fn-record-p old))
        (not (member-equal old *fn-sn-article-record-refusals*))))))
(with-guard-checking-event :none
 (assert-event
  (fn-record-p
   (fn-sn-article-test-result
    (update-nth 6 (1- (expt 2 64)) *sn-article-test-fields*)))))

; F1..F7 removal witnesses: dropped clock, sequence, txid, each earlier
; field, and the current invalidity. All other antecedent conjuncts hold.
(defun fn-sn-field-tooth-hypotheses (target s obs fields)
 (declare (xargs :guard t :verify-guards nil))
 (append (list (natp (fn-record-stamp-of-observation obs))
               (fn-record-uint64p (fn-sn-identity-next s))
               (fn-record-uint64p
                (fn-state-next-txid (fn-node-acceptance (fn-sn-node s)))))
         (append (take target (fn-sn-article-test-hypotheses fields))
                 (list (not (nth target (fn-sn-article-test-hypotheses fields)))))))

; F1, removed hypothesis 1.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs (fn-clock-observation 0 1000 0 nil)) (fields (update-nth 0 "" *sn-article-test-fields*))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 0 s obs fields) '(nil t t t))
        (not (equal r :msgid-invalid))))))

; F1, removed hypothesis 2.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state (expt 2 64) 0))
         (obs *sn-article-test-clock*) (fields (update-nth 0 "" *sn-article-test-fields*))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 0 s obs fields) '(t nil t t))
        (not (equal r :msgid-invalid))))))

; F1, removed hypothesis 3.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 (expt 2 64)))
         (obs *sn-article-test-clock*) (fields (update-nth 0 "" *sn-article-test-fields*))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 0 s obs fields) '(t t nil t))
        (not (equal r :msgid-invalid))))))

; F1, removed hypothesis 4.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs *sn-article-test-clock*) (fields *sn-article-test-fields*)
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 0 s obs fields) '(t t t nil))
        (not (equal r :msgid-invalid))))))

; F2, removed hypothesis 1.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs (fn-clock-observation 0 1000 0 nil)) (fields (update-nth 1 '(256) *sn-article-test-fields*))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 1 s obs fields) '(nil t t t t))
        (not (equal r :payload-invalid))))))

; F2, removed hypothesis 2.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state (expt 2 64) 0))
         (obs *sn-article-test-clock*) (fields (update-nth 1 '(256) *sn-article-test-fields*))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 1 s obs fields) '(t nil t t t))
        (not (equal r :payload-invalid))))))

; F2, removed hypothesis 3.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 (expt 2 64)))
         (obs *sn-article-test-clock*) (fields (update-nth 1 '(256) *sn-article-test-fields*))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 1 s obs fields) '(t t nil t t))
        (not (equal r :payload-invalid))))))

; F2, removed hypothesis 4.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs *sn-article-test-clock*) (fields (update-nth 0 "" (update-nth 1 '(256) *sn-article-test-fields*)))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 1 s obs fields) '(t t t nil t))
        (not (equal r :payload-invalid))))))

; F2, removed hypothesis 5.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs *sn-article-test-clock*) (fields *sn-article-test-fields*)
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 1 s obs fields) '(t t t t nil))
        (not (equal r :payload-invalid))))))

; F3, removed hypothesis 1.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs (fn-clock-observation 0 1000 0 nil)) (fields (update-nth 2 '("bad group") *sn-article-test-fields*))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 2 s obs fields) '(nil t t t t t))
        (not (equal r :groups-invalid))))))

; F3, removed hypothesis 2.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state (expt 2 64) 0))
         (obs *sn-article-test-clock*) (fields (update-nth 2 '("bad group") *sn-article-test-fields*))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 2 s obs fields) '(t nil t t t t))
        (not (equal r :groups-invalid))))))

; F3, removed hypothesis 3.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 (expt 2 64)))
         (obs *sn-article-test-clock*) (fields (update-nth 2 '("bad group") *sn-article-test-fields*))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 2 s obs fields) '(t t nil t t t))
        (not (equal r :groups-invalid))))))

; F3, removed hypothesis 4.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs *sn-article-test-clock*) (fields (update-nth 0 "" (update-nth 2 '("bad group") *sn-article-test-fields*)))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 2 s obs fields) '(t t t nil t t))
        (not (equal r :groups-invalid))))))

; F3, removed hypothesis 5.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs *sn-article-test-clock*) (fields (update-nth 1 '(256) (update-nth 2 '("bad group") *sn-article-test-fields*)))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 2 s obs fields) '(t t t t nil t))
        (not (equal r :groups-invalid))))))

; F3, removed hypothesis 6.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs *sn-article-test-clock*) (fields *sn-article-test-fields*)
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 2 s obs fields) '(t t t t t nil))
        (not (equal r :groups-invalid))))))

; F4, removed hypothesis 1.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs (fn-clock-observation 0 1000 0 nil)) (fields (update-nth 3 "" *sn-article-test-fields*))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 3 s obs fields) '(nil t t t t t t))
        (not (equal r :obligation-id-invalid))))))

; F4, removed hypothesis 2.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state (expt 2 64) 0))
         (obs *sn-article-test-clock*) (fields (update-nth 3 "" *sn-article-test-fields*))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 3 s obs fields) '(t nil t t t t t))
        (not (equal r :obligation-id-invalid))))))

; F4, removed hypothesis 3.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 (expt 2 64)))
         (obs *sn-article-test-clock*) (fields (update-nth 3 "" *sn-article-test-fields*))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 3 s obs fields) '(t t nil t t t t))
        (not (equal r :obligation-id-invalid))))))

; F4, removed hypothesis 4.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs *sn-article-test-clock*) (fields (update-nth 0 "" (update-nth 3 "" *sn-article-test-fields*)))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 3 s obs fields) '(t t t nil t t t))
        (not (equal r :obligation-id-invalid))))))

; F4, removed hypothesis 5.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs *sn-article-test-clock*) (fields (update-nth 1 '(256) (update-nth 3 "" *sn-article-test-fields*)))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 3 s obs fields) '(t t t t nil t t))
        (not (equal r :obligation-id-invalid))))))

; F4, removed hypothesis 6.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs *sn-article-test-clock*) (fields (update-nth 2 '("bad group") (update-nth 3 "" *sn-article-test-fields*)))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 3 s obs fields) '(t t t t t nil t))
        (not (equal r :obligation-id-invalid))))))

; F4, removed hypothesis 7.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs *sn-article-test-clock*) (fields *sn-article-test-fields*)
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 3 s obs fields) '(t t t t t t nil))
        (not (equal r :obligation-id-invalid))))))

; F5, removed hypothesis 1.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs (fn-clock-observation 0 1000 0 nil)) (fields (update-nth 4 "" *sn-article-test-fields*))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 4 s obs fields) '(nil t t t t t t t))
        (not (equal r :subject-invalid))))))

; F5, removed hypothesis 2.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state (expt 2 64) 0))
         (obs *sn-article-test-clock*) (fields (update-nth 4 "" *sn-article-test-fields*))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 4 s obs fields) '(t nil t t t t t t))
        (not (equal r :subject-invalid))))))

; F5, removed hypothesis 3.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 (expt 2 64)))
         (obs *sn-article-test-clock*) (fields (update-nth 4 "" *sn-article-test-fields*))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 4 s obs fields) '(t t nil t t t t t))
        (not (equal r :subject-invalid))))))

; F5, removed hypothesis 4.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs *sn-article-test-clock*) (fields (update-nth 0 "" (update-nth 4 "" *sn-article-test-fields*)))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 4 s obs fields) '(t t t nil t t t t))
        (not (equal r :subject-invalid))))))

; F5, removed hypothesis 5.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs *sn-article-test-clock*) (fields (update-nth 1 '(256) (update-nth 4 "" *sn-article-test-fields*)))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 4 s obs fields) '(t t t t nil t t t))
        (not (equal r :subject-invalid))))))

; F5, removed hypothesis 6.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs *sn-article-test-clock*) (fields (update-nth 2 '("bad group") (update-nth 4 "" *sn-article-test-fields*)))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 4 s obs fields) '(t t t t t nil t t))
        (not (equal r :subject-invalid))))))

; F5, removed hypothesis 7.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs *sn-article-test-clock*) (fields (update-nth 3 "" (update-nth 4 "" *sn-article-test-fields*)))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 4 s obs fields) '(t t t t t t nil t))
        (not (equal r :subject-invalid))))))

; F5, removed hypothesis 8.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs *sn-article-test-clock*) (fields *sn-article-test-fields*)
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 4 s obs fields) '(t t t t t t t nil))
        (not (equal r :subject-invalid))))))

; F6, removed hypothesis 1.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs (fn-clock-observation 0 1000 0 nil)) (fields (update-nth 5 "" *sn-article-test-fields*))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 5 s obs fields) '(nil t t t t t t t t))
        (not (equal r :evidence-invalid))))))

; F6, removed hypothesis 2.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state (expt 2 64) 0))
         (obs *sn-article-test-clock*) (fields (update-nth 5 "" *sn-article-test-fields*))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 5 s obs fields) '(t nil t t t t t t t))
        (not (equal r :evidence-invalid))))))

; F6, removed hypothesis 3.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 (expt 2 64)))
         (obs *sn-article-test-clock*) (fields (update-nth 5 "" *sn-article-test-fields*))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 5 s obs fields) '(t t nil t t t t t t))
        (not (equal r :evidence-invalid))))))

; F6, removed hypothesis 4.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs *sn-article-test-clock*) (fields (update-nth 0 "" (update-nth 5 "" *sn-article-test-fields*)))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 5 s obs fields) '(t t t nil t t t t t))
        (not (equal r :evidence-invalid))))))

; F6, removed hypothesis 5.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs *sn-article-test-clock*) (fields (update-nth 1 '(256) (update-nth 5 "" *sn-article-test-fields*)))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 5 s obs fields) '(t t t t nil t t t t))
        (not (equal r :evidence-invalid))))))

; F6, removed hypothesis 6.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs *sn-article-test-clock*) (fields (update-nth 2 '("bad group") (update-nth 5 "" *sn-article-test-fields*)))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 5 s obs fields) '(t t t t t nil t t t))
        (not (equal r :evidence-invalid))))))

; F6, removed hypothesis 7.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs *sn-article-test-clock*) (fields (update-nth 3 "" (update-nth 5 "" *sn-article-test-fields*)))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 5 s obs fields) '(t t t t t t nil t t))
        (not (equal r :evidence-invalid))))))

; F6, removed hypothesis 8.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs *sn-article-test-clock*) (fields (update-nth 4 "" (update-nth 5 "" *sn-article-test-fields*)))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 5 s obs fields) '(t t t t t t t nil t))
        (not (equal r :evidence-invalid))))))

; F6, removed hypothesis 9.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs *sn-article-test-clock*) (fields *sn-article-test-fields*)
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 5 s obs fields) '(t t t t t t t t nil))
        (not (equal r :evidence-invalid))))))

; F7, removed hypothesis 1.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs (fn-clock-observation 0 1000 0 nil)) (fields (update-nth 6 (expt 2 64) *sn-article-test-fields*))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 6 s obs fields) '(nil t t t t t t t t t))
        (not (equal r :charge-invalid))))))

; F7, removed hypothesis 2.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state (expt 2 64) 0))
         (obs *sn-article-test-clock*) (fields (update-nth 6 (expt 2 64) *sn-article-test-fields*))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 6 s obs fields) '(t nil t t t t t t t t))
        (not (equal r :charge-invalid))))))

; F7, removed hypothesis 3.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 (expt 2 64)))
         (obs *sn-article-test-clock*) (fields (update-nth 6 (expt 2 64) *sn-article-test-fields*))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 6 s obs fields) '(t t nil t t t t t t t))
        (not (equal r :charge-invalid))))))

; F7, removed hypothesis 4.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs *sn-article-test-clock*) (fields (update-nth 0 "" (update-nth 6 (expt 2 64) *sn-article-test-fields*)))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 6 s obs fields) '(t t t nil t t t t t t))
        (not (equal r :charge-invalid))))))

; F7, removed hypothesis 5.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs *sn-article-test-clock*) (fields (update-nth 1 '(256) (update-nth 6 (expt 2 64) *sn-article-test-fields*)))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 6 s obs fields) '(t t t t nil t t t t t))
        (not (equal r :charge-invalid))))))

; F7, removed hypothesis 6.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs *sn-article-test-clock*) (fields (update-nth 2 '("bad group") (update-nth 6 (expt 2 64) *sn-article-test-fields*)))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 6 s obs fields) '(t t t t t nil t t t t))
        (not (equal r :charge-invalid))))))

; F7, removed hypothesis 7.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs *sn-article-test-clock*) (fields (update-nth 3 "" (update-nth 6 (expt 2 64) *sn-article-test-fields*)))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 6 s obs fields) '(t t t t t t nil t t t))
        (not (equal r :charge-invalid))))))

; F7, removed hypothesis 8.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs *sn-article-test-clock*) (fields (update-nth 4 "" (update-nth 6 (expt 2 64) *sn-article-test-fields*)))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 6 s obs fields) '(t t t t t t t nil t t))
        (not (equal r :charge-invalid))))))

; F7, removed hypothesis 9.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs *sn-article-test-clock*) (fields (update-nth 5 "" (update-nth 6 (expt 2 64) *sn-article-test-fields*)))
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 6 s obs fields) '(t t t t t t t t nil t))
        (not (equal r :charge-invalid))))))

; F7, removed hypothesis 10.
(with-guard-checking-event :none
 (assert-event
  (let* ((s (fn-sn-article-test-state 0 0))
         (obs *sn-article-test-clock*) (fields *sn-article-test-fields*)
         (r (fn-sn-article-record s obs (nth 0 fields) (nth 1 fields)
              (nth 2 fields) (nth 3 fields) (nth 4 fields) (nth 5 fields) (nth 6 fields))))
   (and (equal (fn-sn-field-tooth-hypotheses 6 s obs fields) '(t t t t t t t t t nil))
        (not (equal r :charge-invalid))))))


; PRF-126: the claim has no hypotheses, hence no removal witnesses.
; The positive fixture is a record, and the old subject fails at u64 exhaustion.
(include-book "../../books/defkeystone")

(defteeth fn-sn-article-record-is-a-record-or-a-named-refusal
  :claim
  (let ((r (fn-sn-article-record s obs msgid payload groups
                                 obligation-id subject evidence charge)))
    (() (or (fn-record-p r)
            (member-equal r *fn-sn-article-record-refusals*))))
  :subject fn-sn-article-record
  :witness ((s (fn-sn-article-test-state 0 0))
            (obs *sn-article-test-clock*)
            (msgid "<seq@example>") (payload '(65)) (groups '("fn.test"))
            (obligation-id "id") (subject "subject")
            (evidence "evidence") (charge 1))
  :breaks nil
  :mutations
  ((old-constructor-at-u64-exhaustion
    (:conclusion
     (let ((old (fn-sn-article-record-old-for-teeth
                 s obs msgid payload groups
                 obligation-id subject evidence charge)))
       (or (fn-record-p old)
           (member-equal old *fn-sn-article-record-refusals*))))
    ((s (fn-sn-article-test-state (expt 2 64) 0)))
    :fault "the old constructor copies 2^64 into the sequence and returns a malformed record instead of :sequence-exhausted")))

(defteeth-check (fn-sn-article-record-is-a-record-or-a-named-refusal))
