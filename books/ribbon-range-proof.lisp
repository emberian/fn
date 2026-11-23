; Proofs for the range adapter.
(in-package "ACL2")

(include-book "ribbon")
(include-book "range-resume-order-proof")
(include-book "range-seek-step-proof")
(include-book "runs-built-cache-proof")
(include-book "runs-overview-builder-proof")
(include-book "runs-overview-cursor-id-proof")

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

; FN2-RIBBON-MUTATION-REFUSED remains owed. The
; check after the mutation is B's checker, which compares the page's BLAKE3
; digest with the parent-held words. Evaluated at KEYS = ((1 2 3)) (65 slots,
; so the payload ends at offset 209) and X = 1 for every OFF below 65536,
; the refusal is structural at offsets 0-3 (:BAD-MAGIC), 4 (:VERSION),
; 5 (:WRONG-KIND), 6 (:WRONG-HISTORY), 7 (:WRONG-INCARNATION),
; 8 (:WRONG-LOCATION), 9-10 (:WRONG-ALLOCATION), 12 and 209-65535
; (:NONZERO-PADDING). At 11 and at 13-208 the only refusal is :BAD-HASH.
; Those offsets are the rest of B's header, the filter header at
; *fn2-run-header-area* (96), the bytes up to *fn2-ribbon-base* (144) and
; the solution bytes. At those offsets the statement says that no filter
; page of up to 256 keys collides under BLAKE3 with a one-byte change of
; itself, and it carries no collision-freedom premise (compare
; FN2-FC-COLLISION-FREE-PAIRP in FN2-FORMAT-FRAME-BINDS-LOCATION).
; On a successfully sealed and checked page, this branch would need a theorem
; that the specific one-byte change alters the digest. These controls exercise
; the unchanged page, a header refusal, and a hash-only refusal.
(local
 (assert-event
  (let ((keys '((1 2 3))))
    (and (equal (cadr (fn2-ribbon-image keys nil nil nil)) :ok)
         (equal (cadr (fn2-ribbon-image keys nil nil (cons 0 1))) :bad-magic)
         (equal (cadr (fn2-ribbon-image keys nil nil (cons *fn2-ribbon-base* 1))) :bad-hash)))))
