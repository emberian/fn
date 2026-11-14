; Shared typed page observations after the caller authenticates its retained
; window with FN2-FORMAT-RUN. These grant no candidate or allocator authority.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "runs-page")
(fn2-book-layer :c)

(defun fn2-checkpoint-semantic-page-header-p (base schema run level fn2-fields)
 (declare (xargs :stobjs fn2-fields
  :guard (and (fn2-fields-wfp fn2-fields) (fn2-run-readerp base fn2-fields))))
 (and (equal (fn2-run-hdr base schema) schema)
      (equal (fn2-run-hdr base schema-version) 1)
      (equal (fn2-run-hdr base run) run)
      (equal (fn2-run-hdr base level) level)
      (unsigned-byte-p 32 (fn2-run-hdr base entries))))

; PAGE-KIND is derived by the caller from its authenticated parent schema
; and level through the generated dispatcher. Expected digest bytes stay in the held
; pool window until the composing caller copies them with FN2-REC-FETCH.
(defun fn2-checkpoint-semantic-page-child-p (base page-kind length fn2-fields)
 (declare (xargs :stobjs fn2-fields
  :guard (and (fn2-fields-wfp fn2-fields) (natp base)
              (<= (+ base *fn2-format-ref-num-fields*) (fn2-fields-rows fn2-fields))
              (unsigned-byte-p 8 page-kind))))
 (and (equal (fn2-fields-value (+ base *fn2-format-ref-field-storage-domain*) fn2-fields) 0)
      (equal (fn2-fields-value (+ base *fn2-format-ref-field-page-kind*) fn2-fields)
             page-kind)
      (equal (fn2-fields-value (+ base *fn2-format-ref-field-encoded-length*) fn2-fields) length)
      (equal (fn2-fields-ref-len (+ base *fn2-format-ref-field-expected-hash*) fn2-fields) 32)))

; Decode the actual concrete window through the generated run codecs. The
; caller retains physical authentication and cursor ownership across this call.
(defun fn2-checkpoint-semantic-page-read-header (slot gen base schema run level kind owner generation fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-fields fn2-pool)
  :guard (and (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool)
              (fn2-run-readerp base fn2-fields))))
 (b* (((mv code fn2-fields)
       (fn2-run-read-header slot gen base kind owner generation fn2-fields fn2-pool)))
  (mv (if (and (eq code :ok)
               (fn2-checkpoint-semantic-page-header-p base schema run level fn2-fields))
          :ok :source-header) fn2-fields)))

; Operation-domain frames: the decoder changes field contents, never the
; carrier's type, dimensions, or the caller's reader stripe admission.
(fn2-fields-preserves fn2-checkpoint-semantic-page-read-header
 (slot gen base schema run level kind owner generation fn2-fields fn2-pool)
 :position 1
 :hints (("Goal" :in-theory (disable fn2-fields-rows fn2-checkpoint-semantic-page-header-p)))
 :hyps ((fn2-fieldsp fn2-fields) (fn2-run-readerp base fn2-fields)))

(defthm fn2-checkpoint-semantic-page-read-header-reader-context
 (implies (and (fn2-fieldsp fn2-fields) (fn2-run-readerp base fn2-fields))
  (fn2-run-readerp base
   (mv-nth 1 (fn2-checkpoint-semantic-page-read-header
    slot gen base schema run level kind owner generation fn2-fields fn2-pool))))
 :hints (("Goal" :in-theory (e/d (fn2-run-readerp)
                                (fn2-checkpoint-semantic-page-read-header)))))

; Observations refine the actual generated decoder. All raw decoder errors
; and semantic header mismatches normalize to SOURCE-HEADER; field output is
; exactly the decoder's output even on refusal.
(defthm fn2-checkpoint-semantic-page-read-header-fields-refinement
 (equal
  (mv-nth 1 (fn2-checkpoint-semantic-page-read-header
   slot gen base schema run level kind owner generation fn2-fields fn2-pool))
  (mv-nth 1 (fn2-run-read-header slot gen base kind owner generation fn2-fields fn2-pool)))
 :hints (("Goal" :in-theory (enable fn2-checkpoint-semantic-page-read-header))))

(defthm fn2-checkpoint-semantic-page-read-header-code-refinement
 (equal
  (mv-nth 0 (fn2-checkpoint-semantic-page-read-header
   slot gen base schema run level kind owner generation fn2-fields fn2-pool))
  (if (and (eq (mv-nth 0 (fn2-run-read-header slot gen base kind owner generation fn2-fields fn2-pool)) :ok)
           (fn2-checkpoint-semantic-page-header-p base schema run level
            (mv-nth 1 (fn2-run-read-header slot gen base kind owner generation fn2-fields fn2-pool))))
      :ok :source-header))
 :hints (("Goal" :in-theory (enable fn2-checkpoint-semantic-page-read-header))))

; The entry branch additionally compares the retained u32 entry count. This
; implies the shared header's count bound, so extraction does not add refusal.
(defthm fn2-checkpoint-semantic-page-entry-count-bound
 (implies (and (unsigned-byte-p 32 expected)
               (equal (fn2-run-hdr base entries) expected))
          (unsigned-byte-p 32 (fn2-run-hdr base entries))))

; The caller supplies its generated schema dispatch result, never a stored
; field as expected kind. This theorem exposes exactly the former live check.
(defthm fn2-checkpoint-semantic-page-child-p-by-definition
 (equal (fn2-checkpoint-semantic-page-child-p base page-kind length fn2-fields)
  (and (equal (fn2-fields-value (+ base *fn2-format-ref-field-storage-domain*) fn2-fields) 0)
       (equal (fn2-fields-value (+ base *fn2-format-ref-field-page-kind*) fn2-fields) page-kind)
       (equal (fn2-fields-value (+ base *fn2-format-ref-field-encoded-length*) fn2-fields) length)
       (equal (fn2-fields-ref-len (+ base *fn2-format-ref-field-expected-hash*) fn2-fields) 32)))
 :hints (("Goal" :in-theory (enable fn2-checkpoint-semantic-page-child-p))))
