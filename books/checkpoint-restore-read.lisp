; Concrete linked checkpoint readers. These decode bytes, never allocator
; authority: the composing restore transition authenticates the page first.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "event-proof-format")
(include-book "checkpoint-zero-range")
(include-book "alloc")
(fn2-book-layer :b)

; Actual metadata for the three linked checkpoint body formats. Role3 is
; the existing retained-event codec, not an alternate event representation.
(defun fn2-checkpoint-restore-linked-shape (role)
 (declare (xargs :guard t))
 (case role
  (2 (mv :ok *page-kind-allocation-map* *checkpoint-map-body-kind-allocation-map* *fn2-checkpoint-map-slots* *fn2-checkpoint-map-entry-width* *fn2-format-allocation-map-entry-num-fields*))
  (3 (mv :ok *page-kind-manifest* *checkpoint-map-body-kind-event-proof-directory* *fn2-event-proof-slots* *fn2-event-proof-entry-width* *fn2-event-proof-entry-num-fields*))
  (4 (mv :frontier *page-kind-merkle-node* 0 60 32 *fn2-event-frontier-header-num-fields*))
  (5 (mv :ok *page-kind-recovery-arena* *checkpoint-map-body-kind-recovery-arena* *fn2-checkpoint-arena-slots* *fn2-checkpoint-arena-entry-width* *fn2-format-recovery-arena-entry-num-fields*))
  (otherwise (mv :role 0 0 1 0 0))))

; Each invocation checks at most one format slot/header gap (less than a
; sector). The cursor for an unbounded chain belongs to the restore carrier.


(defun fn2-checkpoint-restore-header (role cut-commit cut-event total ordinal base slot gen okind oslot ogen fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-fields fn2-pool)
  :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))
   :guard-hints (("Goal"
    :use ((:instance fn2-fields-value-natp
           (i (+ base *fn2-checkpoint-map-header-field-total-entries*))
           (fn2-fields (mv-nth 2 (fn2-checkpoint-map-header-decode base slot gen
            *fn2-checkpoint-map-body-start* *fn2-checkpoint-map-entries-start* okind oslot ogen fn2-fields fn2-pool))))
          (:instance fn2-fields-value-natp
           (i (+ base *fn2-checkpoint-map-header-field-retired-head*))
           (fn2-fields (mv-nth 2 (fn2-checkpoint-map-header-decode base slot gen
            *fn2-checkpoint-map-body-start* *fn2-checkpoint-map-entries-start* okind oslot ogen fn2-fields fn2-pool))))
          (:instance fn2-fields-value-natp
           (i (+ base *fn2-checkpoint-map-header-field-retired-count*))
           (fn2-fields (mv-nth 2 (fn2-checkpoint-map-header-decode base slot gen
            *fn2-checkpoint-map-body-start* *fn2-checkpoint-map-entries-start* okind oslot ogen fn2-fields fn2-pool))))
          (:instance fn2-fields-value-natp
           (i (+ base *fn2-checkpoint-map-header-field-next-physical-unit*))
           (fn2-fields (mv-nth 2 (fn2-checkpoint-map-header-decode base slot gen
            *fn2-checkpoint-map-body-start* *fn2-checkpoint-map-entries-start* okind oslot ogen fn2-fields fn2-pool))))
          (:instance fn2-fields-ref-off-natp
           (i (+ base *fn2-checkpoint-map-header-field-next-expected-hash*))
           (fn2-fields (mv-nth 2 (fn2-checkpoint-map-header-decode base slot gen
            *fn2-checkpoint-map-body-start* *fn2-checkpoint-map-entries-start* okind oslot ogen fn2-fields fn2-pool)))))
    :in-theory (disable fn2-fields-rows fn2-fields-value fn2-fields-ref-off fn2-checkpoint-map-page-shapep)))))
 (b* (((mv shape pagekind bodykind slots & &) (fn2-checkpoint-restore-linked-shape role))
      ((unless (and (eq shape :ok) (natp base)
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
      (has-next (fn2-fields-value (+ base *fn2-checkpoint-map-header-field-has-next*) fn2-fields))
      ((unless (and
        (equal (fn2-fields-value (+ base *fn2-checkpoint-map-header-field-kind*) fn2-fields)
               bodykind)
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
                     pagekind)
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
  :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))
   :guard-hints (("Goal"
    :use ((:instance fn2-fields-value-natp (i base)
           (fn2-fields (mv-nth 2 (fn2-format-recovery-arena-entry-decode base slot gen
            (+ *fn2-checkpoint-map-entries-start* (* (mod ordinal *fn2-checkpoint-arena-slots*) *fn2-checkpoint-arena-entry-width*)) (+ (+ *fn2-checkpoint-map-entries-start* (* (mod ordinal *fn2-checkpoint-arena-slots*) *fn2-checkpoint-arena-entry-width*)) *fn2-checkpoint-arena-entry-width*) okind oslot ogen fn2-fields fn2-pool)))))
    :in-theory (disable fn2-fields-rows fn2-fields-value fn2-checkpoint-map-page-shapep)))))
 (b* (((mv shape & & slots width nfields) (fn2-checkpoint-restore-linked-shape role))
      ((unless (and (eq shape :ok) (natp ordinal) (natp base)
          (<= (+ base nfields) (fn2-fields-rows fn2-fields))))
       (mv :bounds fn2-fields))
      (off (+ *fn2-checkpoint-map-entries-start* (* (mod ordinal slots) width)))
      ((mv code end fn2-fields)
       (case role
        (2 (fn2-format-allocation-map-entry-decode base slot gen off (+ off width) okind oslot ogen fn2-fields fn2-pool))
        (3 (fn2-event-proof-entry-decode base slot gen off (+ off width) okind oslot ogen fn2-fields fn2-pool))
        (otherwise (fn2-format-recovery-arena-entry-decode base slot gen off (+ off width) okind oslot ogen fn2-fields fn2-pool))))
      ((unless (and (eq code :ok) (natp end) (<= off end) (<= end (+ off width)))) (mv :format fn2-fields))
      (code (fn2-checkpoint-restore-zero-range (- (+ off width) end) end slot gen okind oslot ogen fn2-pool))
      ((unless (eq code :ok)) (mv code fn2-fields))
      ((unless (or (not (equal role 2)) (fn2-checkpoint-restore-allocation-rowp base fn2-fields)))
       (mv :state fn2-fields))
      ((unless (case role
        (2 (equal (fn2-fields-value (+ base *fn2-format-allocation-map-entry-field-extent*) fn2-fields) ordinal))
        (3 (and (equal (fn2-fields-value (+ base *fn2-event-proof-entry-field-commit*) fn2-fields) (+ 1 ordinal))
                (equal (fn2-fields-value (+ base *fn2-event-proof-entry-field-semantic-seal*) fn2-fields) 1)
                (equal (fn2-fields-ref-len (+ base *fn2-event-proof-entry-field-semantic-seal*) fn2-fields) 32)))
        (otherwise (equal (mod (fn2-fields-value (+ base *fn2-format-recovery-arena-entry-field-extent-physical-unit*) fn2-fields)
                    *fn2-storage-extent-units*) 0)))) (mv :identity fn2-fields)))
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
 :hints (("Goal" :in-theory (disable fn2-fields-rows fn2-fields-value fn2-fields-ref-off
                   fn2-checkpoint-map-page-shapep fn2-checkpoint-restore-zero-range
                   fn2-checkpoint-restore-allocation-rowp)))
 :hyps ((fn2-fieldsp fn2-fields) (fn2-poolp fn2-pool) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))
 :specs (("-GUARD-DOMAIN-TYPE" fn2-fieldsp 1) ("-GUARD-DOMAIN-WFP" fn2-fields-wfp 1) ("-PRESERVES-WFP" fn2-fields-wfp 1 :hyps ((fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields))) ("-PRESERVES-ROWS" fn2-fields-rows 1 :frame fn2-fields :hints (("Goal" :in-theory (disable fn2-fields-rows fn2-checkpoint-map-page-shapep fn2-checkpoint-restore-zero-range fn2-checkpoint-restore-allocation-rowp))))))
(fn2-fields-preserves fn2-checkpoint-restore-entry
 (role ordinal base slot gen okind oslot ogen fn2-fields fn2-pool)
 :hints (("Goal" :in-theory (disable fn2-fields-rows fn2-fields-value fn2-fields-ref-off
                   fn2-checkpoint-map-page-shapep fn2-checkpoint-restore-zero-range
                   fn2-checkpoint-restore-allocation-rowp)))
 :hyps ((fn2-fieldsp fn2-fields) (fn2-poolp fn2-pool) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))
 :specs (("-GUARD-DOMAIN-TYPE" fn2-fieldsp 1) ("-GUARD-DOMAIN-WFP" fn2-fields-wfp 1) ("-PRESERVES-WFP" fn2-fields-wfp 1 :hyps ((fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields))) ("-PRESERVES-ROWS" fn2-fields-rows 1 :frame fn2-fields :hints (("Goal" :in-theory (disable fn2-fields-rows fn2-checkpoint-map-page-shapep fn2-checkpoint-restore-zero-range fn2-checkpoint-restore-allocation-rowp))))))
