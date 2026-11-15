; One exact frozen allocator row per call. Gate authority is retained on the
; allocator itself by the C-held construction lifecycle, not a reader flag.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "checkpoint-map-format")
(include-book "checkpoint-construction")
(fn2-book-layer :b)

(defun fn2-checkpoint-frozen-map-entry (extent base token okind oslot ogen fn2-extents fn2-fields)
 (declare (xargs :stobjs (fn2-extents fn2-fields)
  :guard (and (fn2-extents-wfp fn2-extents) (fn2-fields-wfp fn2-fields))))
 (b* (((unless (fn2-alloc-copy-ownerp token okind oslot ogen fn2-extents)) (mv :owner fn2-fields))
      ((unless (and (fn2-alloc-slotp extent fn2-extents) (natp base)
                     (<= (+ base *fn2-format-allocation-map-entry-num-fields*) (fn2-fields-rows fn2-fields))))
       (mv :bounds fn2-fields))
      ; All four states are serialized. Unrelated RESERVED rows are never
      ; silently converted to Free or omitted from the recovery map.
      (fn2-fields (fn2-fields-set-value (+ base *fn2-format-allocation-map-entry-field-extent*) extent fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-format-allocation-map-entry-field-state*) (fn2-extents-state extent fn2-extents) fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-format-allocation-map-entry-field-owner-kind*) (fn2-extents-owner-kind extent fn2-extents) fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-format-allocation-map-entry-field-owner*) (fn2-extents-owner-id extent fn2-extents) fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-format-allocation-map-entry-field-writer-epoch*) (fn2-extents-epoch extent fn2-extents) fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-format-allocation-map-entry-field-allocation*) (fn2-extents-counter extent fn2-extents) fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-format-allocation-map-entry-field-retirement-commit*) (fn2-extents-retirement extent fn2-extents) fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-format-allocation-map-entry-field-next-retired*)
        (if (equal (fn2-extents-state extent fn2-extents) *fn2-extent-state-retire-pending*)
            (fn2-extents-next-retired extent fn2-extents) *fn2-alloc-none*) fn2-fields)))
  (mv :entry fn2-fields)))
; The TYPE contract is over the actual stobj/guard domain, including readonly
; source carriers. The former destination-only TYPE formula was false for
; malformed logical sources (ground controls live in the roundtrip fixture).
; Destination-only WFP and unconditional row effects are retained separately.
(fn2-fields-preserves fn2-checkpoint-frozen-map-entry
 (extent base token okind oslot ogen fn2-extents fn2-fields)
 :hyps ((fn2-extentsp fn2-extents) (fn2-fieldsp fn2-fields) (fn2-extents-wfp fn2-extents) (fn2-fields-wfp fn2-fields))
 :specs (("-GUARD-DOMAIN-TYPE" fn2-fieldsp 1) ("-GUARD-DOMAIN-WFP" fn2-fields-wfp 1) ("-PRESERVES-WFP" fn2-fields-wfp 1 :hyps ((fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields))) ("-PRESERVES-ROWS" fn2-fields-rows 1 :frame fn2-fields)))

; The caller advances one extent per step. :skip is explicit and cannot count
; as a ticket. Other ordinals are skipped: physical free-list order need not
; match journal order. A requested ticket with changed identity is a conflict.
(defun fn2-checkpoint-frozen-arena-entry (extent ordinal base token okind oslot ogen
                                        fn2-checkpoint-construction fn2-extents fn2-fields)
 (declare (xargs :stobjs (fn2-checkpoint-construction fn2-extents fn2-fields)
  :guard (and (fn2-checkpoint-construction-wfp fn2-checkpoint-construction)
              (fn2-extents-wfp fn2-extents) (fn2-fields-wfp fn2-fields))))
 (b* (((unless (fn2-alloc-copy-ownerp token okind oslot ogen fn2-extents)) (mv :owner fn2-fields))
      ((unless (and (fn2-alloc-slotp extent fn2-extents)
                     (equal (fn2-checkpoint-construction-rows fn2-checkpoint-construction) (fn2-extents-rows fn2-extents))
                     (natp base) (<= (+ base *fn2-format-recovery-arena-entry-num-fields*) (fn2-fields-rows fn2-fields))))
       (mv :bounds fn2-fields))
      ((unless (and (fn2-checkpoint-construction-native-p extent fn2-checkpoint-construction)
                     (equal (fn2-checkpoint-construction-token extent fn2-checkpoint-construction) token)
                     (equal (fn2-checkpoint-construction-role extent fn2-checkpoint-construction) 6)
                     (equal (fn2-checkpoint-construction-ordinal extent fn2-checkpoint-construction) ordinal)))
       (mv :skip fn2-fields))
      (epoch (fn2-checkpoint-construction-epoch extent fn2-checkpoint-construction))
      (counter (fn2-checkpoint-construction-counter extent fn2-checkpoint-construction))
      ((unless (and (equal (fn2-checkpoint-construction-owner-kind extent fn2-checkpoint-construction) okind)
                     (equal (fn2-checkpoint-construction-owner-slot extent fn2-checkpoint-construction) oslot)
                     (equal (fn2-checkpoint-construction-owner-gen extent fn2-checkpoint-construction) ogen)
                     (eq (fn2-alloc-handle-code extent epoch counter fn2-extents) :ok)
                     (equal (fn2-extents-state extent fn2-extents) *fn2-extent-state-reserved*)))
       (mv :conflict fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-format-recovery-arena-entry-field-extent-physical-unit*)
                                      (* extent *fn2-storage-extent-units*) fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-format-recovery-arena-entry-field-writer-epoch*) epoch fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-format-recovery-arena-entry-field-allocation*) counter fn2-fields)))
  (mv :entry fn2-fields)))
(fn2-fields-preserves fn2-checkpoint-frozen-arena-entry
 (extent ordinal
        base
        token
        okind
        oslot
        ogen
        fn2-checkpoint-construction
        fn2-extents
        fn2-fields)
 :hyps ((fn2-checkpoint-constructionp fn2-checkpoint-construction) (fn2-extentsp fn2-extents) (fn2-fieldsp fn2-fields) (fn2-checkpoint-construction-wfp fn2-checkpoint-construction) (fn2-extents-wfp fn2-extents) (fn2-fields-wfp fn2-fields))
 :specs (("-GUARD-DOMAIN-TYPE" fn2-fieldsp 1) ("-GUARD-DOMAIN-WFP" fn2-fields-wfp 1) ("-PRESERVES-WFP" fn2-fields-wfp 1 :hyps ((fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields))) ("-PRESERVES-ROWS" fn2-fields-rows 1 :frame fn2-fields)))
