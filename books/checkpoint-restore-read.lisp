; Concrete linked checkpoint readers. These decode bytes, never allocator
; authority: the composing restore transition authenticates the page first.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "checkpoint-map-format")
(include-book "alloc")
(fn2-book-layer :b)

; Each invocation checks at most one format slot/header gap (less than a
; sector). The cursor for an unbounded chain belongs to the restore carrier.
(defun fn2-checkpoint-restore-zero-range (left at slot gen okind oslot ogen fn2-pool)
 (declare (xargs :stobjs fn2-pool :measure (nfix left)
  :guard (and (fn2-pool-wfp fn2-pool) (natp left)
              (<= left *fn2-format-sector-size*) (natp at))))
 (if (zp left) :ok
  (mv-let (code byte) (fn2-pool-read slot gen at okind oslot ogen fn2-pool)
   (cond ((not (eq code :ok)) code)
         ((not (equal byte 0)) :padding)
         (t (fn2-checkpoint-restore-zero-range (- left 1) (+ at 1)
                slot gen okind oslot ogen fn2-pool))))))

(defun fn2-checkpoint-restore-header (role cut-commit cut-event total ordinal base slot gen okind oslot ogen fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-fields fn2-pool)
  :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (member-equal role '(2 5)) (natp base)
                     (<= (+ base *fn2-checkpoint-map-header-num-fields*) (fn2-fields-rows fn2-fields))))
       (mv :bounds fn2-fields))
      ((mv code end fn2-fields)
       (fn2-checkpoint-map-header-decode base slot gen *fn2-checkpoint-map-body-start*
         *fn2-checkpoint-map-entries-start* okind oslot ogen fn2-fields fn2-pool))
      ((unless (and (eq code :ok) (natp end)
                     (<= *fn2-checkpoint-map-body-start* end)
                     (<= end *fn2-checkpoint-map-entries-start*))) (mv :format fn2-fields))
      (code (fn2-checkpoint-restore-zero-range (- *fn2-checkpoint-map-entries-start* end)
              end slot gen okind oslot ogen fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-fields))
      (slots (if (equal role 2) *fn2-checkpoint-map-slots* *fn2-checkpoint-arena-slots*))
      (has-next (fn2-fields-value (+ base *fn2-checkpoint-map-header-field-has-next*) fn2-fields))
      ((unless (and
        (equal (fn2-fields-value (+ base *fn2-checkpoint-map-header-field-kind*) fn2-fields)
               (if (equal role 2) *checkpoint-map-body-kind-allocation-map* *checkpoint-map-body-kind-recovery-arena*))
        (equal (fn2-fields-value (+ base *fn2-checkpoint-map-header-field-version*) fn2-fields) *fn2-format-version*)
        (equal (fn2-fields-value (+ base *fn2-checkpoint-map-header-field-cut-commit*) fn2-fields) cut-commit)
        (equal (fn2-fields-value (+ base *fn2-checkpoint-map-header-field-cut-event*) fn2-fields) cut-event)
        (equal (fn2-fields-value (+ base *fn2-checkpoint-map-header-field-total-entries*) fn2-fields) total)
        (equal (fn2-fields-value (+ base *fn2-checkpoint-map-header-field-page-ordinal*) fn2-fields) ordinal)
        (fn2-checkpoint-map-page-shapep total ordinal
          (fn2-fields-value (+ base *fn2-checkpoint-map-header-field-first-ordinal*) fn2-fields)
          (fn2-fields-value (+ base *fn2-checkpoint-map-header-field-entry-count*) fn2-fields) has-next slots)))
       (mv :coverage fn2-fields))
      (retired-head (fn2-fields-value (+ base *fn2-checkpoint-map-header-field-retired-head*) fn2-fields))
      (retired-count (fn2-fields-value (+ base *fn2-checkpoint-map-header-field-retired-count*) fn2-fields))
      ((unless (if (equal role 2)
        (and (<= retired-count total)
             (if (zp retired-count) (equal retired-head *fn2-alloc-none*)
               (and (natp retired-head) (< retired-head total))))
        (and (equal retired-head *fn2-alloc-none*) (equal retired-count 0))))
       (mv :retirement fn2-fields))
      (f (+ base *fn2-checkpoint-map-header-field-next-storage-domain*))
      ((unless (and
        (equal (fn2-fields-value f fn2-fields) 0)
        (equal (fn2-fields-value (+ f 6) fn2-fields) 1)
        (if (equal has-next 1)
         (and (equal (fn2-fields-value (+ f 4) fn2-fields)
                     (if (equal role 2) *page-kind-allocation-map* *page-kind-recovery-arena*))
              (equal (fn2-fields-value (+ f 5) fn2-fields) *fn2-format-page-size*)
              (equal (mod (fn2-fields-value (+ f 1) fn2-fields) *fn2-storage-extent-units*) 0))
         (and (equal (fn2-fields-value (+ f 1) fn2-fields) 0)
              (equal (fn2-fields-value (+ f 2) fn2-fields) 0)
              (equal (fn2-fields-value (+ f 3) fn2-fields) 0)
              (equal (fn2-fields-value (+ f 4) fn2-fields) 0)
              (equal (fn2-fields-value (+ f 5) fn2-fields) 0)
              (eq (fn2-checkpoint-restore-zero-range 32
                    (fn2-fields-ref-off (+ f 6) fn2-fields) slot gen okind oslot ogen fn2-pool) :ok)))))
       (mv :link fn2-fields)))
  (mv :ok fn2-fields)))

(defun fn2-checkpoint-restore-allocation-rowp (base fn2-fields)
 (declare (xargs :stobjs fn2-fields
  :guard (and (fn2-fields-wfp fn2-fields) (natp base)
              (<= (+ base *fn2-format-allocation-map-entry-num-fields*) (fn2-fields-rows fn2-fields)))))
 (let ((state (fn2-fields-value (+ base *fn2-format-allocation-map-entry-field-state*) fn2-fields))
       (owner-kind (fn2-fields-value (+ base *fn2-format-allocation-map-entry-field-owner-kind*) fn2-fields))
       (owner (fn2-fields-value (+ base *fn2-format-allocation-map-entry-field-owner*) fn2-fields))
       (epoch (fn2-fields-value (+ base *fn2-format-allocation-map-entry-field-writer-epoch*) fn2-fields))
       (allocation (fn2-fields-value (+ base *fn2-format-allocation-map-entry-field-allocation*) fn2-fields))
       (retirement (fn2-fields-value (+ base *fn2-format-allocation-map-entry-field-retirement-commit*) fn2-fields))
       (next (fn2-fields-value (+ base *fn2-format-allocation-map-entry-field-next-retired*) fn2-fields)))
  (and (unsigned-byte-p 32 next)
       (if (equal state *fn2-extent-state-retire-pending*) (posp retirement)
        (and (equal next *fn2-alloc-none*) (equal retirement 0)))
       (case state
        (0 (and (equal owner-kind 0) (equal owner 0) (equal epoch 0) (equal allocation 0)))
        (1 (and (equal owner-kind 0) (equal owner 0)))
        ((2 3) t)
        (otherwise nil)))))

; Exactly one fixed-width entry. All eight allocation fields survive unchanged
; in FN2-FIELDS, including foreign RESERVED owners and retirement commits.
; The consumer must copy/install the row before reusing the field workspace.
(defun fn2-checkpoint-restore-entry (role ordinal base slot gen okind oslot ogen fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-fields fn2-pool)
  :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (member-equal role '(2 5)) (natp ordinal) (natp base)
          (<= (+ base (if (equal role 2) *fn2-format-allocation-map-entry-num-fields*
                        *fn2-format-recovery-arena-entry-num-fields*)) (fn2-fields-rows fn2-fields))))
       (mv :bounds fn2-fields))
      (width (if (equal role 2) *fn2-checkpoint-map-entry-width* *fn2-checkpoint-arena-entry-width*))
      (slots (if (equal role 2) *fn2-checkpoint-map-slots* *fn2-checkpoint-arena-slots*))
      (off (+ *fn2-checkpoint-map-entries-start* (* (mod ordinal slots) width)))
      ((mv code end fn2-fields)
       (if (equal role 2)
        (fn2-format-allocation-map-entry-decode base slot gen off (+ off width) okind oslot ogen fn2-fields fn2-pool)
        (fn2-format-recovery-arena-entry-decode base slot gen off (+ off width) okind oslot ogen fn2-fields fn2-pool)))
      ((unless (and (eq code :ok) (natp end) (<= off end) (<= end (+ off width)))) (mv :format fn2-fields))
      (code (fn2-checkpoint-restore-zero-range (- (+ off width) end) end slot gen okind oslot ogen fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-fields))
      ((unless (or (not (equal role 2)) (fn2-checkpoint-restore-allocation-rowp base fn2-fields)))
       (mv :state fn2-fields))
      ((unless (if (equal role 2)
        (equal (fn2-fields-value (+ base *fn2-format-allocation-map-entry-field-extent*) fn2-fields) ordinal)
        (equal (mod (fn2-fields-value (+ base *fn2-format-recovery-arena-entry-field-extent-physical-unit*) fn2-fields)
                    *fn2-storage-extent-units*) 0))) (mv :identity fn2-fields)))
  (mv :entry fn2-fields)))

; Pool is a readonly source of these decoders and belongs to their actual
; type/guard domain. No runtime whole-pool validation is added. The broader
; destination-shape claims and unconditional row effects remain available.
(fn2-fields-preserves fn2-checkpoint-restore-header
 (role cut-commit
      cut-event
      total
      ordinal
      base
      slot
      gen
      okind
      oslot
      ogen
      fn2-fields
      fn2-pool)
 :hyps ((fn2-fieldsp fn2-fields) (fn2-poolp fn2-pool) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))
 :specs (("-GUARD-DOMAIN-TYPE" fn2-fieldsp 1) ("-GUARD-DOMAIN-WFP" fn2-fields-wfp 1) ("-PRESERVES-WFP" fn2-fields-wfp 1 :hyps ((fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields))) ("-PRESERVES-ROWS" fn2-fields-rows 1 :frame fn2-fields)))
(fn2-fields-preserves fn2-checkpoint-restore-entry
 (role ordinal base slot gen okind oslot ogen fn2-fields fn2-pool)
 :hyps ((fn2-fieldsp fn2-fields) (fn2-poolp fn2-pool) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))
 :specs (("-GUARD-DOMAIN-TYPE" fn2-fieldsp 1) ("-GUARD-DOMAIN-WFP" fn2-fields-wfp 1) ("-PRESERVES-WFP" fn2-fields-wfp 1 :hyps ((fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields))) ("-PRESERVES-ROWS" fn2-fields-rows 1 :frame fn2-fields)))
