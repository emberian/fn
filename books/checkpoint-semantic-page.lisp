; Shared typed page observations after the caller authenticates its retained
; window with FN2-FORMAT-RUN. These grant no candidate or allocator authority.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "checkpoint-metadata-retention")
(fn2-book-layer :c)

(defun fn2-checkpoint-semantic-page-header-p (base schema run level fn2-fields)
 (declare (xargs :stobjs fn2-fields
  :guard (and (fn2-fields-wfp fn2-fields) (fn2-run-readerp base fn2-fields))))
 (and (equal (fn2-run-hdr base schema) schema)
      (equal (fn2-run-hdr base schema-version) 1)
      (equal (fn2-run-hdr base run) run)
      (equal (fn2-run-hdr base level) level)
      (unsigned-byte-p 32 (fn2-run-hdr base entries))))

; LEVEL is the authenticated parent's positive level. The generated schema
; determines its child's page kind; expected digest bytes stay in the held
; pool window until the composing caller copies them with FN2-REC-FETCH.
(defun fn2-checkpoint-semantic-page-child-p (base schema level length fn2-fields)
 (declare (xargs :stobjs fn2-fields
  :guard (and (fn2-fields-wfp fn2-fields) (natp base)
              (<= (+ base *fn2-format-ref-num-fields*) (fn2-fields-rows fn2-fields))
              (posp level))))
 (and (equal (fn2-fields-value (+ base *fn2-format-ref-field-storage-domain*) fn2-fields) 0)
      (equal (fn2-fields-value (+ base *fn2-format-ref-field-page-kind*) fn2-fields)
             (fn2-run-layout-page-kind schema (- level 1)))
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
