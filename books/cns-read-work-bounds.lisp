; Source-derived pool-byte work bounds for fixed-schema, budget-1 callbacks.
; Arithmetic controls below are NOT actual-count or refinement theorems.
; The counting connection to served callees remains a separate obligation.
(in-package "ACL2")
(include-book "ordered")
; READ-SOURCES currently lives here, not in a standalone geometry leaf.
; Reuse the actual constant instead of copying its value into this book.
(include-book "machines-c-read")
(fn2-book-layer :c)

; Each successful generated decode reads at most layout-max-size octets.
; A failed/partial decode reads at most CODEC-DECODE-FUEL octets and returns
; immediately. Numeric ARTICLE/ADDR key comparisons read no pool octets.
; XL selects ONE phase per call; these are maxima, not sums of phases.
; Scope: actual ARTICLE/ADDR schema dispatch, lookup/next budget exactly1,
; and a range created through READ-RANGE (at most READ-SOURCES sources).
; Raw arbitrary WFP rows with fabricated SCOUNT are outside this count.
; ADDR DELIVER records the winning head as OUT; successor copies field rows
; only (RUN-COPY-ROW), not pool bytes. PICK/PAST/CONSUME compare numeric keys.
; No claim about normal sealer construction or full CNS control flow follows.
(defun fn2-cns-lookup-1-pool-bound (entry index)
 (declare (xargs :guard (and (natp entry) (natp index))))
 (max (+ (* (+ *fn2-ov-search-steps* 1) entry) *fn2-codec-decode-fuel*)
  (max (+ (* (- *fn2-run-restart-interval* 1) index)
          *fn2-codec-decode-fuel* *fn2-run-restart-bytes*)
   (max (+ *fn2-format-page-header-max-size* *fn2-codec-decode-fuel*)
        (+ *fn2-codec-decode-fuel* *fn2-run-restart-bytes*)))))

; A preceding source can finish with an overlay lower bound+order+entry,
; or a run leaf's at-most-16 decodes and its restart offset. The first
; unfinished/failed source returns immediately from ADVANCE-ALL, so only
; ONE source contributes the larger malformed-last/child/header/seek term.
(defun fn2-cns-range-source-complete-pool-bound (entry)
 (declare (xargs :guard (natp entry)))
 (max (* (+ *fn2-ov-search-steps* 2) entry)
      (+ (* *fn2-run-restart-interval* entry) *fn2-run-restart-bytes*)))
(defun fn2-cns-next-1-pool-bound (entry index sources)
 (declare (xargs :guard (and (natp entry) (natp index) (posp sources))))
 (let ((complete (fn2-cns-range-source-complete-pool-bound entry))
       (last (max (fn2-cns-lookup-1-pool-bound entry index)
                  (+ (* (- *fn2-run-restart-interval* 1) entry)
                     *fn2-codec-decode-fuel* *fn2-run-restart-bytes*))))
  (max (* sources complete) (+ (* (- sources 1) complete) last))))

(defconst *fn2-cns-article-lookup-1-pool-read-bound*
 (fn2-cns-lookup-1-pool-bound (fn2-layout-max-size *fn2-article-entry*)
                             (fn2-layout-max-size *fn2-article-index*)))
(defconst *fn2-cns-addr-next-1-pool-read-bound*
 (fn2-cns-next-1-pool-bound (fn2-layout-max-size *fn2-addr-entry*)
                           (fn2-layout-max-size *fn2-addr-index*) *fn2-read-sources*))
; The already bounded atomic capture tail handles the two 32-byte digests
; and location-hash vector: at most three pool byte operations per octet.
(defconst *fn2-cns-article-capture-pool-work-bound*
 (* 3 (+ 64 *fn2-article-location-hashes-max*)))
(defconst *fn2-cns-article-next-pool-work-bound*
 (+ *fn2-cns-article-lookup-1-pool-read-bound* *fn2-cns-article-capture-pool-work-bound*))

; Static arithmetic controls, including malformed-last rather than only
; successful-decode bounds. These do not claim composed callback traces.
(assert-event (equal (fn2-layout-max-size *fn2-article-entry*) 237))
(assert-event (equal (fn2-layout-max-size *fn2-article-index*) 97))
(assert-event (equal (fn2-layout-max-size *fn2-addr-entry*) 46))
(assert-event (equal (fn2-layout-max-size *fn2-addr-index*) 106))
(assert-event (equal *fn2-cns-article-lookup-1-pool-read-bound* 13813))
(assert-event (equal *fn2-cns-addr-next-1-pool-read-bound* 19506))
(assert-event (equal *fn2-cns-article-capture-pool-work-bound* 480))
(assert-event (> *fn2-cns-article-lookup-1-pool-read-bound*
                 (* (+ *fn2-ov-search-steps* 2) (fn2-layout-max-size *fn2-article-entry*))))
(assert-event (<= *fn2-cns-article-next-pool-work-bound* 32768))
(assert-event (<= *fn2-cns-addr-next-1-pool-read-bound* 32768))
