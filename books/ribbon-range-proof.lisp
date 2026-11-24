; Proofs for the range adapter.
(in-package "ACL2")

(include-book "ribbon-mutation-discharge-proof")
(include-book "range-resume-order-proof")
(include-book "range-head-delivery-proof")
(include-book "range-overlay-head-proof")
(include-book "range-seek-step-proof")
(include-book "range-stored-leaf-row-proof")
(include-book "range-page-resume-proof")
(include-book "range-installed-cursor-proof")
(include-book "runs-overview-builder-cursor-proof")
(include-book "runs-build-close-proof")
(include-book "runs-build-sealed-page-proof")
(include-book "runs-build-root-proof")

; FN2-RIBBON-NO-FALSE-NEGATIVE is not discharged here and has no known
; counterexample. Evaluated, it holds for one empty key; 256 distinct keys
; of 250 octets, each probed; 256 copies of one key; and 2,000 generated key
; sets of 1 to 256 keys with 256 queries each. Its proof follows the build,
; B's checker on the sealed page and every probe through the pool, both
; header codecs, the page writer and sealer and the incremental BLAKE3, and
; this book's closure holds only typing, well-formedness and frame lemmas
; for those. The facts it needs are the ones about this adapter's pages, not
; the general owed squares (FN2-POOL-BYTE-FILL, FN2-LAYOUT-ROUNDTRIP,
; FN2-FORMAT-PAGE-HEADER-ROUNDTRIP, FN2-RIBBON-HEADER-ROUNDTRIP,
; FN2-B3-INCREMENTAL-IS-BLAKE3). The ribbon-false-neg book chain, ending in
; books/ribbon-false-neg-discharge-proof.lisp, proves those page facts and
; discharges this square. A square takes one discharge, so this book does
; not repeat it.

; The checker uses its parent-held digest for solution bytes. These controls
; distinguish a structural refusal, a digest refusal and an unchanged page.
(local
 (assert-event
  (let ((keys '((1 2 3))))
    (and (equal (cadr (fn2-ribbon-image keys nil nil nil)) :ok)
         (equal (cadr (fn2-ribbon-image keys nil nil (cons 0 1))) :bad-magic)
         (equal (cadr (fn2-ribbon-image keys nil nil (cons *fn2-ribbon-base* 1))) :bad-hash)))))
