; The served journal body dispatch, shared by replay and retained-event
; extraction. The generated kind codecs own every boundary; unknown kinds
; are explicit, never skipped by a second parser.
(in-package "ACL2")
(include-book "runs-served")
(fn2-book-layer :c)

(defconst *fn2-journal-record-fields*
 (max *fn2-format-release-allocation-num-fields* (max *fn2-format-allocation-num-fields* (max *fn2-run-entry-rows*
  (max *fn2-format-record-header-num-fields*
   (max *fn2-format-keyed-mutation-num-fields*
    (max *fn2-format-article-acceptance-num-fields*
     (max *fn2-format-retirement-num-fields* *fn2-format-checkpoint-installation-num-fields*))))))))

(defun fn2-journal-body-decode (kind base slot gen off end okind oslot ogen fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-fields fn2-pool)
                 :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool))))
 (cond ((not (and (natp base) (<= (+ base *fn2-journal-record-fields*) (fn2-fields-rows fn2-fields))
                  (unsigned-byte-p 32 off) (unsigned-byte-p 32 end)
                  (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)))
        (mv :bounds 0 fn2-fields))
       ((equal kind *record-kind-keyed-mutation*)
        (fn2-format-keyed-mutation-decode base slot gen off end okind oslot ogen fn2-fields fn2-pool))
       ((equal kind *record-kind-allocation*)
        (fn2-format-allocation-decode base slot gen off end okind oslot ogen fn2-fields fn2-pool))
       ((equal kind *record-kind-article-acceptance*)
        (fn2-format-article-acceptance-decode base slot gen off end okind oslot ogen fn2-fields fn2-pool))
       ((equal kind *record-kind-release-allocation*)
        (fn2-format-release-allocation-decode base slot gen off end okind oslot ogen fn2-fields fn2-pool))
       ((equal kind *record-kind-retirement*)
        (fn2-format-retirement-decode base slot gen off end okind oslot ogen fn2-fields fn2-pool))
       ((equal kind *record-kind-checkpoint-installation*)
        (fn2-format-checkpoint-installation-decode base slot gen off end okind oslot ogen fn2-fields fn2-pool))
       ((and (natp kind) (<= *record-kind-identity-evidence* kind)
             (<= kind *fn2-commit-txn-schema-record-kind-last*))
        (fn2-run-layout-decode (- kind *fn2-commit-txn-schema-record-kind-base*) 0 base slot gen off end
                               okind oslot ogen fn2-fields fn2-pool))
       (t (mv :kind 0 fn2-fields))))
(fn2-fields-preserves fn2-journal-body-decode
 (kind base slot gen off end okind oslot ogen fn2-fields fn2-pool) :position 2)

; Zero padding belongs to the record stream commitment, but not to a member
; leaf. Check it rather than silently discarding a nonzero suffix.
(defun fn2-journal-zero-tail (left off slot gen okind oslot ogen fn2-pool)
 (declare (xargs :stobjs fn2-pool :measure (nfix left)
                 :guard (and (fn2-pool-wfp fn2-pool) (natp left) (natp off))))
 (if (zp left) :ok
  (mv-let (code byte) (fn2-pool-read slot gen off okind oslot ogen fn2-pool)
   (if (and (eq code :ok) (equal byte 0))
       (fn2-journal-zero-tail (- left 1) (+ 1 off) slot gen okind oslot ogen fn2-pool)
     :padding))))

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
      ((when (= off end)) (mv :end off 0 0 fn2-fields))
      ((mv byte-code version) (fn2-pool-read slot gen (if (< (+ off 1) end) (+ off 1) off)
                                               okind oslot ogen fn2-pool))
      ((unless (eq byte-code :ok)) (mv :invalid 0 0 0 fn2-fields))
      ((when (= version 0))
       (mv (if (eq (fn2-journal-zero-tail (- end off) off slot gen okind oslot ogen fn2-pool) :ok) :end :invalid)
           off 0 0 fn2-fields))
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
