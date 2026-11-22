; Shared actual journal authentication/member engine; source wrappers retain
; their own concrete provenance and expected-seal derivation.
(in-package "ACL2")
(include-book "event-read-state")
(include-book "journal-members")
(include-book "recovery")
(fn2-book-layer :c)
(local (in-theory (disable fn2-event-readp fn2-event-read-wfp fn2-event-read-rows
 fn2-fcp fn2-fc-wfp fn2-fc-rows
 fn2-fc-contextp fn2-fc-context-wfp fn2-fc-context-rows
 fn2-fieldsp fn2-fields-wfp fn2-fields-rows
 fn2-poolp fn2-pool-wfp fn2-pool-rows
 fn2-b3p fn2-b3-wfp fn2-b3-rows
 fn2-digestsp fn2-digests-wfp fn2-digests-rows
 fn2-journal-membersp fn2-journal-members-wfp fn2-journal-members-rows)))


(local (in-theory (disable fn2-event-read-allocation
 fn2-event-read-body-len
 fn2-event-read-body-off
 fn2-event-read-checker
 fn2-event-read-commit
 fn2-event-read-epoch
 fn2-event-read-extent
 fn2-event-read-field-base
 fn2-event-read-first
 fn2-event-read-gen
 fn2-event-read-journal-history
 fn2-event-read-journal-incarnation
 fn2-event-read-members
 fn2-event-read-owner-gen
 fn2-event-read-owner-kind
 fn2-event-read-owner-slot
 fn2-event-read-pending
 fn2-event-read-phase
 fn2-event-read-record-fetch-acc
 fn2-event-read-record-fetch-next
 fn2-event-read-record-fetch-off
 fn2-event-read-seal-span-length
 fn2-event-read-seal-span-next
 fn2-event-read-seal-span-started
 fn2-event-read-slot
 fn2-fc-phase
 fn2-fields-ref-gen
 fn2-fields-ref-len
 fn2-fields-ref-off
 fn2-fields-ref-slot
 fn2-fields-value
 nth update-nth fn2-layout-range-code fn2-journal-members-begin)))

; Decode only a bounded namespace hint from the retained seal-frame header.
; This accepts no authentication flag and grants no records/member transition.
(defun fn2-event-read-namespace (fn2-event-read fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-event-read fn2-fields fn2-pool) :verify-guards nil
  :guard (and (fn2-event-read-wfp fn2-event-read) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (mbt (and (fn2-event-readp fn2-event-read) (fn2-event-read-wfp fn2-event-read)
                                (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)))
                     (< 0 (fn2-event-read-rows fn2-event-read))
                     (equal (fn2-event-read-phase 0 fn2-event-read) *fn2-event-read-phase-frame-seal*)
                     (equal (fn2-event-read-pending 0 fn2-event-read) 0)))
       (mv :state fn2-event-read fn2-fields))
      (base (fn2-event-read-field-base 0 fn2-event-read))
      (slot (fn2-event-read-slot 0 fn2-event-read)) (gen (fn2-event-read-gen 0 fn2-event-read))
      (kind (fn2-event-read-owner-kind 0 fn2-event-read)) (owner (fn2-event-read-owner-slot 0 fn2-event-read))
      (generation (fn2-event-read-owner-gen 0 fn2-event-read))
      ((unless (<= (+ base *fn2-format-frame-header-num-fields*) (fn2-fields-rows fn2-fields)))
       (mv :fields fn2-event-read fn2-fields))
      ((mv frame off fn2-fields) (fn2-format-frame-header-decode base slot gen 0 4096 kind owner generation fn2-fields fn2-pool))
      (payload (fn2-fields-value (+ base *fn2-format-frame-header-field-payload-length*) fn2-fields))
      ((unless (and (eq frame :ok) (natp off) (posp payload) (<= (+ off payload) 4096)
                     (equal (fn2-fields-value (+ base *fn2-format-frame-header-field-frame-kind*) fn2-fields) *frame-kind-seal*)
                     (equal (fn2-fields-value (+ base *fn2-format-frame-header-field-ordinal*) fn2-fields) 1)
                     (equal (fn2-fields-value (+ base *fn2-format-frame-header-field-fragment-offset*) fn2-fields) 0)))
       (mv :frame fn2-event-read fn2-fields))
      (history (fn2-fields-value (+ base *fn2-format-frame-header-field-history*) fn2-fields))
      (incarnation (fn2-fields-value (+ base *fn2-format-frame-header-field-incarnation*) fn2-fields))
      ((unless (fn2-origin-physicalp history incarnation))
       (mv :namespace fn2-event-read fn2-fields))
      (fn2-event-read (fn2-event-read-put 0 (journal-history history) (journal-incarnation incarnation))))
  (mv :ok fn2-event-read fn2-fields)))

(fn2-event-read-preserves fn2-event-read-namespace
 (fn2-event-read fn2-fields fn2-pool)
 :hyps ((fn2-event-readp fn2-event-read) (fn2-event-read-wfp fn2-event-read) (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields) (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
 :specs (("-EVENT-READ-DOMAIN-TYPE" fn2-event-readp 1)
         ("-EVENT-READ-DOMAIN-WFP" fn2-event-read-wfp 1)
         ("-EVENT-READ-DOMAIN-ROWS" fn2-event-read-rows 1 :frame fn2-event-read)
         ("-FIELDS-DOMAIN-TYPE" fn2-fieldsp 2)
         ("-FIELDS-DOMAIN-WFP" fn2-fields-wfp 2)
         ("-FIELDS-DOMAIN-ROWS" fn2-fields-rows 2 :frame fn2-fields)))

(verify-guards fn2-event-read-namespace
 :hints (("Goal" :in-theory (enable fn2-origin-physicalp))))
(in-theory (disable fn2-event-read-namespace))

; The generated decoder owns its ordinary fields continuation. Padding
; resumes separately, using the same tail checker over at most BUDGET bytes.
; BODY-OFF/LEN retain the authenticated payload until its whole tail is checked.
(defun fn2-event-read-seal-span-step (budget fn2-event-read fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-event-read fn2-fields fn2-pool) :verify-guards nil
  :guard (and (fn2-event-read-wfp fn2-event-read) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (mbt (and (fn2-event-readp fn2-event-read) (fn2-event-read-wfp fn2-event-read)
                                 (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)))
                     (< 0 (fn2-event-read-rows fn2-event-read)))) (mv :state fn2-event-read fn2-fields))
      (phase (fn2-event-read-phase 0 fn2-event-read))
      (base (fn2-event-read-field-base 0 fn2-event-read))
      (off (fn2-event-read-body-off 0 fn2-event-read)) (payload (fn2-event-read-body-len 0 fn2-event-read))
      (slot (fn2-event-read-slot 0 fn2-event-read)) (gen (fn2-event-read-gen 0 fn2-event-read))
      (kind (fn2-event-read-owner-kind 0 fn2-event-read)) (owner (fn2-event-read-owner-slot 0 fn2-event-read))
      (generation (fn2-event-read-owner-gen 0 fn2-event-read))
      ((unless (and (member-equal phase (list *fn2-event-read-phase-seal-span* *fn2-event-read-phase-seal-tail*))
                    (<= (+ base *fn2-format-sealed-batch-num-fields*) (fn2-fields-rows fn2-fields))
                    (posp payload) (<= (+ off payload) *fn2-commit-unit-bytes*)
                    (natp budget) (<= budget *fn2-commit-unit-bytes*)))
       (mv :bounds fn2-event-read fn2-fields))
      ((when (zp budget)) (mv :more fn2-event-read fn2-fields))
      ((when (equal phase *fn2-event-read-phase-seal-tail*))
       (b* ((next (fn2-event-read-seal-span-next 0 fn2-event-read))
            (length (fn2-event-read-seal-span-length 0 fn2-event-read))
            ((unless (and (posp length) (<= length *fn2-format-sealed-batch-max-size*)
                          (<= (+ off length) next) (<= next (+ off payload))))
             (mv :state fn2-event-read fn2-fields))
            (count (min budget (- (+ off payload) next)))
            (code (if (eq :end (fn2-journal-record-marker slot gen next (+ next count)
                                    kind owner generation fn2-pool)) :ok :padding))
            (next (+ next count))
            (complete (equal next (+ off payload)))
            (fn2-event-read (fn2-event-read-put 0
             (phase (if (eq code :ok) (if complete *fn2-event-read-phase-semantic-seal* phase)
                       *fn2-event-read-phase-uncertain*))
             (seal-span-next next) (body-len (if (and (eq code :ok) complete) length payload)))))
        (mv (if (eq code :ok) :more code) fn2-event-read fn2-fields)))
      (fn2-fields (if (equal (fn2-event-read-seal-span-started 0 fn2-event-read) 0)
                      (fn2-format-sealed-batch-start base fn2-fields) fn2-fields))
      ((mv code next fn2-fields)
       (fn2-format-sealed-batch-decode-step base slot gen off (+ off payload)
        kind owner generation budget fn2-fields fn2-pool))
      (valid (and (eq code :ok) (natp next) (< off next) (<= next (+ off payload))
                  (<= (- next off) *fn2-format-sealed-batch-max-size*)))
      (fn2-event-read (fn2-event-read-put 0 (seal-span-started 1)
       (phase (cond ((eq code :more) phase) (valid *fn2-event-read-phase-seal-tail*)
                    (t *fn2-event-read-phase-uncertain*)))
       (seal-span-next (if valid next 0)) (seal-span-length (if valid (- next off) 0)))))
  (mv (cond ((or (eq code :more) valid) :more) ((eq code :ok) :format) (t code)) fn2-event-read fn2-fields)))
(fn2-event-read-preserves fn2-event-read-seal-span-step
 (budget fn2-event-read fn2-fields fn2-pool) :position 1)
(fn2-fields-preserves fn2-event-read-seal-span-step
 (budget fn2-event-read fn2-fields fn2-pool) :position 2 :prefix "-FIELDS-PRESERVES" :raw-rows t
 :hints (("Goal" :in-theory (enable fn2-event-read-seal-span-step))))

(verify-guards fn2-event-read-seal-span-step)
(in-theory (disable fn2-event-read-seal-span-step))

; Only actual semantic-verifier success enters RECORD-DIGEST. Source identity
; stays in the existing reader row; each byte visit rechecks its decoded Ref,
; authenticated result/window and the public wrapper's external source owner.
(defun fn2-event-read-record-digest-current-p (expected fn2-event-read fn2-fc fn2-fields fn2-digests)
 (declare (xargs :stobjs (fn2-event-read fn2-fc fn2-fields fn2-digests) :verify-guards nil
  :guard (and (fn2-event-read-wfp fn2-event-read) (fn2-fc-wfp fn2-fc)
              (fn2-fields-wfp fn2-fields) (fn2-digests-wfp fn2-digests))))
 (and (< 0 (fn2-event-read-rows fn2-event-read))
  (let* ((row (fn2-event-read-checker 0 fn2-event-read))
         (base (fn2-event-read-field-base 0 fn2-event-read))
         (field (+ base *fn2-format-sealed-batch-field-record-stream*))
         (off (fn2-event-read-record-fetch-off 0 fn2-event-read)))
   (and (equal (fn2-event-read-phase 0 fn2-event-read) *fn2-event-read-phase-record-digest*)
        (< row (fn2-fc-rows fn2-fc))
        (equal (fn2-fc-phase row fn2-fc) *fn2-fc-phase-idle*)
        (<= (+ base *fn2-format-sealed-batch-num-fields*) (fn2-fields-rows fn2-fields))
        (fn2-digest-rowp expected fn2-digests)
        (fn2-digest-rowp (fn2-digest-slot row *fn2-fc-result*) fn2-digests)
        (fn2-digest-equal (fn2-digest-slot row *fn2-fc-result*) expected fn2-digests)
        (fn2-rec-fetch-state-p (fn2-event-read-record-fetch-next 0 fn2-event-read)
                              (fn2-event-read-record-fetch-acc 0 fn2-event-read))
        (equal (fn2-fields-ref-slot field fn2-fields) (fn2-event-read-slot 0 fn2-event-read))
        (equal (fn2-fields-ref-gen field fn2-fields) (fn2-event-read-gen 0 fn2-event-read))
        (equal (fn2-fields-ref-off field fn2-fields) off)
        (equal (fn2-fields-ref-len field fn2-fields) 32)
        (<= (fn2-event-read-body-off 0 fn2-event-read) off)
        (<= (+ off 32) (+ (fn2-event-read-body-off 0 fn2-event-read) (fn2-event-read-body-len 0 fn2-event-read)))
))))

; Consumer-facing consequences of the public bounded loader contracts.  Keep
; its worker opaque: the reader stores NEXT in :u8 and ACC in :u32.
(local (defthm fn2-event-read-fetch-result-widths
 (implies (and (natp budget) (natp off) (fn2-rec-fetch-state-p next acc))
  (and (unsigned-byte-p 8
        (mv-nth 1 (fn2-rec-fetch-step budget next acc dst slot gen off kind owner generation fn2-pool fn2-digests)))
       (unsigned-byte-p 32
        (mv-nth 2 (fn2-rec-fetch-step budget next acc dst slot gen off kind owner generation fn2-pool fn2-digests)))))
 :hints (("Goal"
  :use ((:instance fn2-rec-fetch-step-result-state
         (okind kind) (oslot owner) (ogen generation)))
  :in-theory (e/d (fn2-rec-fetch-state-p unsigned-byte-p)
                  (fn2-rec-fetch-step fn2-rec-fetch-bytes))))))

(local (defthm fn2-event-read-fetch-result-carrier
 (implies (and (fn2-digestsp fn2-digests) (fn2-digest-rowp dst fn2-digests))
  (and (fn2-digestsp
        (mv-nth 3 (fn2-rec-fetch-step budget next acc dst slot gen off kind owner generation fn2-pool fn2-digests)))
       (fn2-digests-wfp
        (mv-nth 3 (fn2-rec-fetch-step budget next acc dst slot gen off kind owner generation fn2-pool fn2-digests)))
       (equal (fn2-digests-rows
        (mv-nth 3 (fn2-rec-fetch-step budget next acc dst slot gen off kind owner generation fn2-pool fn2-digests)))
        (fn2-digests-rows fn2-digests))))
 :hints (("Goal"
  :use ((:instance fn2-rec-fetch-step-shape
         (okind kind) (oslot owner) (ogen generation)))
  :in-theory (disable fn2-rec-fetch-step fn2-rec-fetch-bytes
                     fn2-digestsp fn2-digests-wfp fn2-digests-rows)))))

(verify-guards fn2-event-read-record-digest-current-p
 :hints (("Goal" :in-theory (disable fn2-digest-equal fn2-rec-fetch-state-p))))

(defun fn2-event-read-record-digest-step (budget expected fn2-event-read fn2-fc fn2-fields fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-event-read fn2-fc fn2-fields fn2-pool fn2-digests) :verify-guards nil
  :guard (and (fn2-event-read-wfp fn2-event-read) (fn2-fc-wfp fn2-fc)
              (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (fn2-digests-wfp fn2-digests))))
 (b* (((unless (fn2-event-read-record-digest-current-p expected fn2-event-read fn2-fc fn2-fields fn2-digests))
       (mv :source fn2-event-read fn2-digests))
      ((unless (and (natp budget) (<= budget *fn2-commit-unit-bytes*)))
       (mv :bounds fn2-event-read fn2-digests))
      ((when (zp budget)) (mv :more fn2-event-read fn2-digests))
      (row (fn2-event-read-checker 0 fn2-event-read))
      (hash (fn2-digest-slot row *fn2-fc-hash*))
      ((unless (fn2-digest-rowp hash fn2-digests)) (mv :bounds fn2-event-read fn2-digests))
      ((mv code next acc fn2-digests)
       (fn2-rec-fetch-step budget (fn2-event-read-record-fetch-next 0 fn2-event-read)
        (fn2-event-read-record-fetch-acc 0 fn2-event-read) hash
        (fn2-event-read-slot 0 fn2-event-read) (fn2-event-read-gen 0 fn2-event-read)
        (fn2-event-read-record-fetch-off 0 fn2-event-read)
        (fn2-event-read-owner-kind 0 fn2-event-read) (fn2-event-read-owner-slot 0 fn2-event-read)
        (fn2-event-read-owner-gen 0 fn2-event-read) fn2-pool fn2-digests))
      (complete (and (eq code :ok) (equal next 32) (equal acc 0)))

      (fn2-event-read (fn2-event-read-put 0
       (record-fetch-next next) (record-fetch-acc acc)
       (phase (cond (complete *fn2-event-read-phase-read-records*)
                    ((eq code :more) *fn2-event-read-phase-record-digest*)
                    (t *fn2-event-read-phase-uncertain*))))))
  (mv (if (and (eq code :ok) (not complete)) :invariant code) fn2-event-read fn2-digests)))
(fn2-event-read-preserves fn2-event-read-record-digest-step
 (budget expected fn2-event-read fn2-fc fn2-fields fn2-pool fn2-digests) :position 1)

; The format core returns this digest carrier at position 8.  Export the
; actual child result here, alongside the reader preservation above.
(fn2-digests-preserves fn2-event-read-record-digest-step
 (budget expected fn2-event-read fn2-fc fn2-fields fn2-pool fn2-digests)
 :position 2 :prefix "-DIGESTS-PRESERVES" :rows nil
 :hints (("Goal" :in-theory (e/d (fn2-event-read-record-digest-step)
  (fn2-rec-fetch-step fn2-rec-fetch-bytes fn2-digestsp fn2-digests-wfp fn2-digests-rows)))))

(defthm fn2-event-read-record-digest-step-digests-preserves-rows
 (implies (and (fn2-digestsp fn2-digests) (fn2-digests-wfp fn2-digests))
  (equal (fn2-digests-rows (mv-nth 2
           (fn2-event-read-record-digest-step budget expected fn2-event-read fn2-fc fn2-fields fn2-pool fn2-digests)))
         (fn2-digests-rows fn2-digests)))
 :hints (("Goal" :in-theory (e/d (fn2-event-read-record-digest-step)
  (fn2-rec-fetch-step fn2-rec-fetch-bytes fn2-digestsp fn2-digests-wfp fn2-digests-rows)))))

(verify-guards fn2-event-read-record-digest-step
 :hints (("Goal" :in-theory (e/d (fn2-event-read-record-digest-current-p)
  (fn2-rec-fetch-step fn2-rec-fetch-bytes fn2-digest-equal
   fn2-event-readp fn2-event-read-wfp fn2-digestsp fn2-digests-wfp)))))

(in-theory (disable fn2-event-read-record-digest-step))

; Interpret the completed verifier's concrete fields and digest receipt while
; the reader still owns the source buffer and the reserved checker stripe.
(defun fn2-event-read-checked-unit (expected fn2-event-read fn2-journal-members fn2-fields fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-event-read fn2-journal-members fn2-fields fn2-pool fn2-digests)
  :guard (and (fn2-event-read-wfp fn2-event-read) (fn2-journal-members-wfp fn2-journal-members)
              (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (fn2-digests-wfp fn2-digests))))
 (b* (((unless (< 0 (fn2-event-read-rows fn2-event-read)))
       (mv :state fn2-event-read fn2-journal-members fn2-fields))
      (phase (fn2-event-read-phase 0 fn2-event-read))
      (semantic (equal phase *fn2-event-read-phase-semantic-seal*))
      (sealframe (equal phase *fn2-event-read-phase-frame-seal*))
      (row (fn2-event-read-checker 0 fn2-event-read)) (base (fn2-event-read-field-base 0 fn2-event-read))
      (slot (fn2-event-read-slot 0 fn2-event-read)) (gen (fn2-event-read-gen 0 fn2-event-read))
      (kind (fn2-event-read-owner-kind 0 fn2-event-read)) (owner (fn2-event-read-owner-slot 0 fn2-event-read))
      (generation (fn2-event-read-owner-gen 0 fn2-event-read))
      (hash (fn2-digest-slot row *fn2-fc-hash*))
      ((unless (and (or semantic sealframe (equal phase *fn2-event-read-phase-frame-records*))
                    (<= (+ base *fn2-format-sealed-batch-num-fields*) (fn2-fields-rows fn2-fields))
                    (fn2-digest-rowp expected fn2-digests) (fn2-digest-rowp hash fn2-digests)
                    (fn2-digest-rowp (fn2-digest-slot row *fn2-fc-result*) fn2-digests)))
       (mv :state fn2-event-read fn2-journal-members fn2-fields))
      ((when semantic)
       (b* ((first (fn2-event-read-first 0 fn2-event-read))
            (members (fn2-event-read-members 0 fn2-event-read))
            (field (+ base *fn2-format-sealed-batch-field-record-stream*))
            (off (fn2-fields-ref-off field fn2-fields))
            (valid (and (fn2-digest-equal (fn2-digest-slot row *fn2-fc-result*) expected fn2-digests)
                        (unsigned-byte-p 32 off) (posp first) (posp members)
                        (equal (fn2-fields-value (+ base *fn2-format-sealed-batch-field-event-first*) fn2-fields) first)
                        (equal (fn2-fields-value (+ base *fn2-format-sealed-batch-field-event-last*) fn2-fields) (+ first members -1))
                        (equal (fn2-fields-ref-slot field fn2-fields) slot)
                        (equal (fn2-fields-ref-gen field fn2-fields) gen)
                        (equal (fn2-fields-ref-len field fn2-fields) 32)
                        (<= (fn2-event-read-body-off 0 fn2-event-read) off)
                        (<= (+ off 32) (+ (fn2-event-read-body-off 0 fn2-event-read) (fn2-event-read-body-len 0 fn2-event-read)))))
            (fn2-event-read (if valid (fn2-event-read-put 0
             (phase *fn2-event-read-phase-record-digest*)
             (record-fetch-next 0) (record-fetch-acc 0) (record-fetch-off off))
             (fn2-event-read-set-phase 0 *fn2-event-read-phase-uncertain* fn2-event-read))))
        (mv (if valid :more :seal) fn2-event-read fn2-journal-members fn2-fields)))
      ; The physical verifier resets its own continuation at success. Decode
      ; the already authenticated header to recover exact body boundaries.
      ((mv decoded off fn2-fields) (fn2-format-frame-header-decode base slot gen 0 4096 kind owner generation fn2-fields fn2-pool))
      (payload (fn2-fields-value (+ base *fn2-format-frame-header-field-payload-length*) fn2-fields))
      (valid (and (eq decoded :ok) (natp off) (posp payload) (<= (+ off payload) 4096)
                  (equal (fn2-fields-value (+ base *fn2-format-frame-header-field-frame-kind*) fn2-fields)
                         (if sealframe *frame-kind-seal* *frame-kind-records*))
                  (equal (fn2-fields-value (+ base *fn2-format-frame-header-field-ordinal*) fn2-fields) (if sealframe 1 0))
                  (equal (fn2-fields-value (+ base *fn2-format-frame-header-field-fragment-offset*) fn2-fields) 0)))
      (matches (or sealframe (fn2-digest-equal (fn2-digest-slot row *fn2-fc-result*) hash fn2-digests)))
      ((mv begun fn2-journal-members)
       (if (and valid matches (not sealframe))
           (fn2-journal-members-begin (fn2-event-read-first 0 fn2-event-read) (fn2-event-read-members 0 fn2-event-read)
             off (+ off payload) slot gen kind owner generation fn2-journal-members)
         (mv (cond ((not valid) :frame) ((not matches) :record-stream) (t :ok)) fn2-journal-members)))
      (fn2-event-read (fn2-event-read-put 0 (body-off (if valid off 0)) (body-len (if valid payload 0))
       (seal-span-started 0) (seal-span-next 0) (seal-span-length 0)
       (phase (if (eq begun :ok) (if sealframe *fn2-event-read-phase-seal-span* *fn2-event-read-phase-members*)
                *fn2-event-read-phase-uncertain*)))))
  (mv begun fn2-event-read fn2-journal-members fn2-fields)))
(in-theory (disable fn2-event-read-checked-unit))

(defun fn2-event-read-format-core (budget expected previous fn2-event-read
                                  fn2-journal-members fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-event-read fn2-journal-members
                          fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
  :verify-guards nil
  :guard (and (fn2-event-read-wfp fn2-event-read)
              (fn2-journal-members-wfp fn2-journal-members) (fn2-fc-wfp fn2-fc) (fn2-fc-context-wfp fn2-fc-context)
              (fn2-b3-wfp fn2-b3) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (fn2-digests-wfp fn2-digests))))
 (b* (((unless (< 0 (fn2-event-read-rows fn2-event-read)))
       (mv :state fn2-event-read fn2-journal-members fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
      (phase (fn2-event-read-phase 0 fn2-event-read))
      (semantic (equal phase *fn2-event-read-phase-semantic-seal*))
      (sealframe (equal phase *fn2-event-read-phase-frame-seal*))
      (row (fn2-event-read-checker 0 fn2-event-read)) (base (fn2-event-read-field-base 0 fn2-event-read))
      (slot (fn2-event-read-slot 0 fn2-event-read)) (gen (fn2-event-read-gen 0 fn2-event-read))
      (kind (fn2-event-read-owner-kind 0 fn2-event-read)) (owner (fn2-event-read-owner-slot 0 fn2-event-read))
      (generation (fn2-event-read-owner-gen 0 fn2-event-read))
      (commit (fn2-event-read-commit 0 fn2-event-read))
      (hash (fn2-digest-slot row *fn2-fc-hash*)) (geometry (fn2-digest-slot row *fn2-fc-geometry*))
      ((unless (and (fn2-event-read-format-phase-p phase)
                     (equal (fn2-event-read-pending 0 fn2-event-read) 0)
                     (equal row (fn2-b-event-row (fn2-fc-rows fn2-fc)))
                     (< row (fn2-fc-rows fn2-fc)) (< row (fn2-fc-context-rows fn2-fc-context))
                     (unsigned-byte-p 32 hash) (unsigned-byte-p 32 geometry)
                     (equal base (* 128 row))
                     (fn2-b3-ready row fn2-b3 fn2-digests)
                     (posp commit)
                     (fn2-digest-rowp expected fn2-digests) (unsigned-byte-p 32 expected)
                     (fn2-digest-rowp previous fn2-digests) (unsigned-byte-p 32 previous)
                     (not (equal expected previous))
                     (<= (* *fn2-digest-stride* (fn2-fc-rows fn2-fc)) expected)
                     (<= (* *fn2-digest-stride* (fn2-fc-rows fn2-fc)) previous)
                     (fn2-digest-rowp hash fn2-digests) (fn2-digest-rowp geometry fn2-digests)
                     (<= (+ base *fn2-format-sealed-batch-num-fields*) (fn2-fields-rows fn2-fields))
                     (natp budget) (<= budget 4096)))
       (mv :state fn2-event-read fn2-journal-members fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
      ((when (zp budget))
       (mv :more fn2-event-read fn2-journal-members fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
      ((unless (eq :ok (fn2-layout-range-code slot gen 0 *fn2-commit-unit-bytes*
                nil kind owner generation fn2-pool)))
       (let ((fn2-event-read (fn2-event-read-set-phase 0 *fn2-event-read-phase-uncertain* fn2-event-read)))
        (mv :source fn2-event-read fn2-journal-members fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
      ((when (equal phase *fn2-event-read-phase-record-digest*))
       (mv-let (code fn2-event-read fn2-digests)
        (fn2-event-read-record-digest-step budget expected fn2-event-read fn2-fc fn2-fields fn2-pool fn2-digests)
        (mv code fn2-event-read fn2-journal-members fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
      ((when (member-equal phase (list *fn2-event-read-phase-seal-span* *fn2-event-read-phase-seal-tail*)))
       (mv-let (code fn2-event-read fn2-fields)
        (fn2-event-read-seal-span-step budget fn2-event-read fn2-fields fn2-pool)
        (mv code fn2-event-read fn2-journal-members fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
      ((when (and sealframe (equal (fn2-event-read-journal-history 0 fn2-event-read) 0)
                   (equal (fn2-event-read-journal-incarnation 0 fn2-event-read) 0)
                   (equal (fn2-fc-phase row fn2-fc) *fn2-fc-phase-idle*)))
       (mv-let (code fn2-event-read fn2-fields) (fn2-event-read-namespace fn2-event-read fn2-fields fn2-pool)
        (mv (if (eq code :ok) :more code) fn2-event-read fn2-journal-members fn2-fc fn2-fc-context
            fn2-b3 fn2-fields fn2-pool fn2-digests)))
      ((unless (fn2-origin-physicalp (fn2-event-read-journal-history 0 fn2-event-read)
                                     (fn2-event-read-journal-incarnation 0 fn2-event-read)))
       (mv :namespace fn2-event-read fn2-journal-members fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
      ; The header-derived namespace is a hint until the expected semantic seal
      ; authenticates its matching body. Records become readable only afterward.
      (fn2-fc-context (fn2-rec-context row (fn2-event-read-extent 0 fn2-event-read)
        (if (or semantic sealframe) 2 1) (fn2-event-read-epoch 0 fn2-event-read)
        (fn2-event-read-allocation 0 fn2-event-read) commit hash previous geometry
        (fn2-event-read-journal-history 0 fn2-event-read) (fn2-event-read-journal-incarnation 0 fn2-event-read) fn2-fc-context))
      ((mv code fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests)
       (fn2-format-run (if semantic :seal :frame) nil row slot gen
         (if semantic (fn2-event-read-body-off 0 fn2-event-read) 0)
         (if semantic (fn2-event-read-body-len 0 fn2-event-read) 4096)
         base kind owner generation budget fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
      ((when (eq code :more))
       (mv code fn2-event-read fn2-journal-members fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
      ((unless (eq code :ok))
       (let ((fn2-event-read (fn2-event-read-set-phase 0 *fn2-event-read-phase-uncertain* fn2-event-read)))
        (mv code fn2-event-read fn2-journal-members fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
      ((mv receipt fn2-event-read fn2-journal-members fn2-fields)
       (fn2-event-read-checked-unit expected fn2-event-read fn2-journal-members fn2-fields fn2-pool fn2-digests)))
  (mv receipt fn2-event-read fn2-journal-members fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))

(verify-guards fn2-event-read-format-core
 :hints (("Goal" :in-theory (disable fn2-digest-equal fn2-layout-range-code fn2-fc-context-geometry
   fn2-fc-context-hash fn2-fc-context-previous-seal fn2-b-event-row fn2-b3-ready))))
