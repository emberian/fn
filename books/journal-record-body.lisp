; The served journal body dispatch, shared by replay and retained-event
; extraction. The generated kind codecs own every boundary; unknown kinds
; are explicit, never skipped by a second parser.
(in-package "ACL2")
(include-book "runs-served")
(include-book "format-check")
(fn2-book-layer :c)

(defconst *fn2-journal-record-fields*
 (max *fn2-run-entry-rows*
      (max *fn2-format-record-header-num-fields*
           (max *fn2-format-keyed-mutation-num-fields* *fn2-format-article-acceptance-num-fields*))))

(defun fn2-journal-body-decode (kind base slot gen off end okind oslot ogen fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-fields fn2-pool)
                 :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
 (cond ((not (and (natp base) (<= (+ base *fn2-journal-record-fields*) (fn2-fields-rows fn2-fields))
                  (unsigned-byte-p 32 off) (unsigned-byte-p 32 end)
                  (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)))
        (mv :bounds 0 fn2-fields))
       ((equal kind *record-kind-keyed-mutation*)
        (fn2-format-keyed-mutation-decode base slot gen off end okind oslot ogen fn2-fields fn2-pool))
       ((equal kind *record-kind-article-acceptance*)
        (fn2-format-article-acceptance-decode base slot gen off end okind oslot ogen fn2-fields fn2-pool))
       ((and (natp kind) (<= *record-kind-identity-evidence* kind)
             (<= kind *fn2-commit-txn-schema-record-kind-last*))
        (fn2-run-layout-decode (- kind *fn2-commit-txn-schema-record-kind-base*) 0 base slot gen off end
                               okind oslot ogen fn2-fields fn2-pool))
       (t (mv :kind 0 fn2-fields))))
(fn2-fields-preserves fn2-journal-body-decode
 (kind base slot gen off end okind oslot ogen fn2-fields fn2-pool) :position 2)

; Zero padding belongs to the record stream commitment, but not to a member
; leaf. Check it rather than silently discarding a nonzero suffix.
(defun fn2-journal-record-marker (slot gen off end okind oslot ogen fn2-pool)
 (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
 (b* (((unless (and (natp off) (natp end) (<= off end) (<= end 4096))) :invalid)
      ((when (= off end)) :end)
      ((mv code version)
       (fn2-pool-read slot gen (if (< (+ off 1) end) (+ off 1) off) okind oslot ogen fn2-pool))
      ((unless (eq code :ok)) :invalid)
      ((unless (= version 0)) :record)
      ((unless (and (natp slot) (< slot (fn2-pool-rows fn2-pool))
                    (eq (fn2-layout-range-code slot gen off end nil okind oslot ogen fn2-pool) :ok)))
       :invalid)
      (base (+ (nfix (fn2-pool-slot-base slot fn2-pool)) off))
      (n (- end off)))
  (if (and (<= (+ base n) (fn2-pool-data-length fn2-pool))
           (= (fn2-fc-zero-prefix base n fn2-pool) n))
      :end :invalid)))
(in-theory (disable fn2-journal-record-marker fn2-journal-body-decode))

; One actual canonical record, from an already frame-verified record stream.
; Returns its exclusive end, event, and kind. Framing/seal verification is a
; separate precondition owned by the physical journal reader, never inferred
; merely because these bytes decode.
(defun fn2-journal-record-next (base slot gen off end okind oslot ogen fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-fields fn2-pool)
                 :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (natp base) (<= (+ base *fn2-journal-record-fields*) (fn2-fields-rows fn2-fields))
                    (unsigned-byte-p 32 off) (unsigned-byte-p 32 end) (<= off end) (<= end 4096)
                    (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)))
       (mv :bounds 0 0 0 fn2-fields))
      (marker (fn2-journal-record-marker slot gen off end okind oslot ogen fn2-pool))
      ((when (eq marker :end)) (mv :end off 0 0 fn2-fields))
      ((unless (eq marker :record)) (mv :invalid 0 0 0 fn2-fields))
      ((mv code body fn2-fields)
       (fn2-format-record-header-decode base slot gen off end okind oslot ogen fn2-fields fn2-pool))
      ((unless (and (eq code :ok) (natp body) (< off body) (<= body end)
                    (= (fn2-fields-value (+ base *fn2-format-record-header-field-schema-version*) fn2-fields) 1)))
       (mv :invalid 0 0 0 fn2-fields))
      (kind (fn2-fields-value (+ base *fn2-format-record-header-field-record-kind*) fn2-fields))
      (event (fn2-fields-value (+ base *fn2-format-record-header-field-event*) fn2-fields))
      ((mv code next fn2-fields)
       (fn2-journal-body-decode kind base slot gen body end okind oslot ogen fn2-fields fn2-pool)))
  (if (and (eq code :ok) (natp next) (< body next) (<= next end) (posp event))
      (mv :record next event kind fn2-fields)
    (mv :invalid 0 0 0 fn2-fields))))
(fn2-fields-preserves fn2-journal-record-next
 (base slot gen off end okind oslot ogen fn2-fields fn2-pool) :position 4)
