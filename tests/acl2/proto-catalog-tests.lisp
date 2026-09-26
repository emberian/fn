; fn: teeth for books/proto-catalog.lisp and books/proto-catalog-fold.lisp
; (wave 5, lane consolidation-design, 2026-09-26).
;
; What this book is evidence FOR.  The generic's exports execute, over its
; own list-backed foundation, as the list operations the arena's logical
; side names (the {correspondence} obligations), so the fold book's
; theorems hold on the executable path; `fn-pcat-seal-many-keeps-sealed'
; (a reader that pinned h before the fold reads the same octets after it)
; and `fn-pcat-total-of-seal-is-delta' (the scalar total after a seal is the
; total before plus the sealed length: a total advanced from a delta, never
; re-walked) each get a ground positive witness asserting the complete
; antecedent and conclusion, and one witness per hypothesis on which every
; retained hypothesis holds, the omitted one fails and the conclusion fails.
; The delta theorem has no hypothesis, so it has none to remove.  The
; attachment's evidence is books/proto-catalog-arena.lisp (the same fold on
; the arena's foundation at certification time) and the native smoke
; (tests/test_native_proto_catalog.py: the image's live foundation).

(in-package "ACL2")
(include-book "../../books/proto-catalog-fold")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; The host runs compiled code: every function it may reach is guard-verified.

(assert-event
 (and (eq (symbol-class 'fn-pcat$c-wfp (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pcat$c-count (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pcat$c-payload-len (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pcat$c-get (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pcat$c-payload (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pcat$c-seal-list (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pcat$c-seal-buffer (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pcat$c-clear (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pcat-seal-many (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-pcat-total (w state)) :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; The executable path on a live local generic (its own foundation here):
; three seals, one from the octet buffer, the total, the reads, a clear.

(defun pct-exec-run (fn-pcat)
  (declare (xargs :stobjs fn-pcat))
  (let* ((fn-pcat (fn-pcat-clear fn-pcat))
         (fn-pcat (fn-pcat-seal-many '((1 2 3) (4 5)) fn-pcat))
         (fn-pcat (with-local-stobj fn-octets
                    (mv-let (fn-pcat fn-octets)
                      (let* ((fn-octets (fn-octets-from-list '(6) fn-octets))
                             (fn-pcat (fn-pcat-seal-buffer fn-octets fn-pcat)))
                        (mv fn-pcat fn-octets))
                      fn-pcat)))
         (result (list (fn-pcat-count fn-pcat)
                       (fn-pcat-total 3 fn-pcat)
                       (fn-pcat-total 2 fn-pcat)
                       (fn-pcat-payload-len 0 fn-pcat)
                       (fn-pcat-get 0 2 fn-pcat)
                       (fn-pcat-payload 1 fn-pcat)
                       (fn-pcat-payload 2 fn-pcat)))
         (fn-pcat (fn-pcat-clear fn-pcat)))
    (mv (list result (fn-pcat-count fn-pcat)) fn-pcat)))

(defun pct-exec ()
  (with-local-stobj fn-pcat
    (mv-let (result fn-pcat) (pct-exec-run fn-pcat) result)))

(assert-event (equal (pct-exec) '((3 6 5 3 3 (4 5) (6)) 0)))

; -----------------------------------------------------------------------------
; fn-pcat-seal-many-keeps-sealed:
;   (implies (and (natp h) (< h (fn-pcat-count fn-pcat)))
;            (equal (fn-pcat-payload h (fn-pcat-seal-many payloads fn-pcat))
;                   (fn-pcat-payload h fn-pcat)))

; The positive witness: a two-payload value, handle 1, two more sealed.
(defthm pct-keeps-positive
  (let ((fn-pcat '((1 2 3) (4 5))) (h 1) (payloads '((7) (8 9))))
    (and (natp h) (< h (fn-pcat-count fn-pcat))
         (equal (fn-pcat-payload h (fn-pcat-seal-many payloads fn-pcat))
                (fn-pcat-payload h fn-pcat))
         (equal (fn-pcat-payload h fn-pcat) '(4 5))))
  :rule-classes nil)

; Without (natp h): on the empty value a negative handle reads the sealed
; payload (nth of a negative is car), so the hypothesis is not redundant.
(defthm pct-keeps-without-natp-h
  (let ((fn-pcat nil) (h -1) (payloads '((7))))
    (and (not (natp h)) (< h (fn-pcat-count fn-pcat))
         (not (equal (fn-pcat-payload h (fn-pcat-seal-many payloads fn-pcat))
                     (fn-pcat-payload h fn-pcat)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pcat-payload fn-pcat-count fn-pcat-seal-list))))

(must-fail
 (defthm pct-keeps-w-natp-h
   (implies (< h (fn-pcat-count fn-pcat))
            (equal (fn-pcat-payload h (fn-pcat-seal-many payloads fn-pcat))
                   (fn-pcat-payload h fn-pcat)))
   :hints (("Goal" :do-not-induct t))))

; Without the bound: the handle at the count is the first sealed payload.
(defthm pct-keeps-without-bound
  (let ((fn-pcat '((1 2 3))) (h 1) (payloads '((7))))
    (and (natp h) (not (< h (fn-pcat-count fn-pcat)))
         (not (equal (fn-pcat-payload h (fn-pcat-seal-many payloads fn-pcat))
                     (fn-pcat-payload h fn-pcat)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pcat-payload fn-pcat-count fn-pcat-seal-list))))

(must-fail
 (defthm pct-keeps-w-bound
   (implies (natp h)
            (equal (fn-pcat-payload h (fn-pcat-seal-many payloads fn-pcat))
                   (fn-pcat-payload h fn-pcat)))
   :hints (("Goal" :do-not-induct t))))

; -----------------------------------------------------------------------------
; fn-pcat-total-of-seal-is-delta (no hypothesis):
;   (equal (fn-pcat-total (+ 1 (fn-pcat-count fn-pcat)) (fn-pcat-seal-list xs fn-pcat))
;          (+ (len xs) (fn-pcat-total (fn-pcat-count fn-pcat) fn-pcat)))

(defthm pct-delta-positive
  (let ((fn-pcat '((1 2 3) (4 5))) (xs '(6 7 8 9)))
    (and (equal (fn-pcat-total (+ 1 (fn-pcat-count fn-pcat)) (fn-pcat-seal-list xs fn-pcat))
                (+ (len xs) (fn-pcat-total (fn-pcat-count fn-pcat) fn-pcat)))
         (equal (fn-pcat-total (fn-pcat-count fn-pcat) fn-pcat) 5)
         (equal (fn-pcat-total (+ 1 (fn-pcat-count fn-pcat)) (fn-pcat-seal-list xs fn-pcat)) 9)))
  :rule-classes nil)

; The theorem holds on an improper value too (the seal walks conses): the
; record that no recognizer hypothesis was needed, as a ground instance.
(defthm pct-delta-on-improper-value
  (let ((fn-pcat '((1 2 3) . 4)) (xs '(6 7)))
    (equal (fn-pcat-total (+ 1 (fn-pcat-count fn-pcat)) (fn-pcat-seal-list xs fn-pcat))
           (+ (len xs) (fn-pcat-total (fn-pcat-count fn-pcat) fn-pcat))))
  :rule-classes nil)
