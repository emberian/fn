; Exact completion comparison: executable witnesses and five focused mutants.
(in-package "ACL2")
(include-book "../../books/owner-parse-carried")

(defun phei-held (h)
 (declare (xargs :guard t))
 (fn-held-make 0 1 0 "<a@x>" h '("fn.test") "o" "s" "e" 1 5
   (fn-hf-make 3 0 1 nil)
   (fn-hc-make (fn-stx-make-verdict :unverified nil 0) nil 0) nil nil))

; Mutants deliberately lack verified guards: (a) uses a dotted expected list,
; and (b) permits a scalar index past the payload. Production is guard verified.
(defun phei-without-true-list (h x fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil))
 (and (equal (len x) (fn-arena-payload-len h fn-arena))
      (fn-arx-arena-prefixp h 0 (len x) x fn-arena)))
(defun phei-without-length (h x fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil))
 (and (true-listp x) (fn-arx-arena-prefixp h 0 (len x) x fn-arena)))
(defun phei-scan-at-one (h x fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil))
 (and (true-listp x) (equal (len x) (fn-arena-payload-len h fn-arena))
      (fn-arx-arena-prefixp h 1 (len x) (cdr x) fn-arena)))
(defun phei-without-msgid (record expected fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil))
 (let ((h (fn-record-payload record)))
  (if (and (natp h) (< h (fn-arena-count fn-arena)))
   (fn-arena-payload-equal-p h expected fn-arena) (equal expected nil))))
(defun phei-invalid-is-true (record msgid expected fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil))
 (and (equal (fn-record-msgid record) msgid)
  (let ((h (fn-record-payload record)))
   (if (and (natp h) (< h (fn-arena-count fn-arena)))
    (fn-arena-payload-equal-p h expected fn-arena) t))))

(assert-event
 (and (eq (symbol-class 'fn-arena-payload-equal-p (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-apc-completion-row-names-p (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-apc-completion-names-submission-p (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-apc-own-finish (w state)) :common-lisp-compliant)))

; Positive witnesses assert the complete antecedents and conclusions on
; handle 1 of a two-handle concrete arena, plus exact expected truth.
(with-guard-checking-event
 :none
 (assert-event
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-arena (fn-arena-seal-list '(9 8) fn-arena))
         (fn-arena (fn-arena-seal-list '(0 255 17) fn-arena))
         (record (phei-held 1)) (bad (phei-held 2))
         (w (fn-row-wire-of record fn-arena)))
   (mv
    (and (fn-arena-p fn-arena) (equal (fn-arena-count fn-arena) 2)
         (fn-arena-payload-equal-p 1 '(0 255 17) fn-arena)
         (equal (fn-arena-payload-equal-p 1 '(0 255 17) fn-arena)
                (equal (fn-arena-payload 1 fn-arena) '(0 255 17)))
         (fn-held-p record)
         (fn-apc-completion-row-names-p record "<a@x>" '(0 255 17) fn-arena)
         (equal (fn-apc-completion-row-names-p record "<a@x>" '(0 255 17) fn-arena)
                (and (equal (fn-record-msgid w) "<a@x>")
                     (equal (fn-record-payload w) '(0 255 17))))
         ; (a) Dotted tail: exact equality refuses, mutant accepts.
         (not (fn-arena-payload-equal-p 1 '(0 255 17 . 7) fn-arena))
         (phei-without-true-list 1 '(0 255 17 . 7) fn-arena)
         ; (c) Only byte zero differs: mutant skips it.
         (not (fn-arena-payload-equal-p 1 '(1 255 17) fn-arena))
         (phei-scan-at-one 1 '(1 255 17) fn-arena)
         ; (d) Exact bytes under a different Message-ID.
         (not (fn-apc-completion-row-names-p record "<b@x>" '(0 255 17) fn-arena))
         (phei-without-msgid record '(0 255 17) fn-arena)
         ; (e) A held row's invalid handle represents nil bytes, not anything.
         (fn-held-p bad)
         (not (fn-apc-completion-row-names-p bad "<a@x>" '(0) fn-arena))
         (phei-invalid-is-true bad "<a@x>" '(0) fn-arena))
    fn-arena))
  :stobjs-out '(nil fn-arena)))

; The requested (b) zero extension does NOT distinguish the mutant in the
; logic: the out-of-bounds scalar is nil. A live call violates its guard.
(defthm phei-length-zero-is-nondiscriminating
 (let ((fn-arena '((9 8) (0 255 17))))
  (and (not (fn-arena-payload-equal-p 1 '(0 255 17 0) fn-arena))
       (not (phei-without-length 1 '(0 255 17 0) fn-arena))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-arena-payload-equal-p phei-without-length
                                    fn-arx-arena-prefixp)
                                   ((:e fn-arx-arena-prefixp) (:e fn-arena-get))))))

; Additional (b) witness, required by K-I1's arbitrary-X scope. A trailing
; nil matches the out-of-bounds logical scalar, while exact equality refuses.
(defthm phei-length-nil-counterexample
 (let ((fn-arena '((9 8) (0 255 17))) (x '(0 255 17 nil)))
  (and (fn-arena-p fn-arena) (true-listp x)
       (not (fn-arena-payload-equal-p 1 x fn-arena))
       (phei-without-length 1 x fn-arena)))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-arena-payload-equal-p phei-without-length
                                    fn-arx-arena-prefixp)
                                   ((:e fn-arx-arena-prefixp) (:e fn-arena-get))))))

; Hypothesis-removal witnesses: K-I1 needs the arena recognizer (a payload
; can otherwise be improper); K-I2 needs the held-row recognizer (a wire row
; retains its literal payload instead of interpreting it as a handle).
(defthm phei-arena-recognizer-counterexample
 (let ((fn-arena '((0 255 17 . 7))) (x '(0 255 17 . 7)))
  (and (not (fn-arena-p fn-arena))
       (not (equal (fn-arena-payload-equal-p 0 x fn-arena)
                   (equal (fn-arena-payload 0 fn-arena) x)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-arena-payload-equal-p))))

(defthm phei-held-recognizer-counterexample
 (let* ((fn-arena '((9 8) (0 255 17)))
        (record (fn-record-make 0 1 0 "<a@x>" '(0 255 17) '("fn.test")
                                "o" "s" "e" 1 5))
        (w (fn-row-wire-of record fn-arena)))
  (and (fn-arena-p fn-arena) (not (fn-held-p record))
       (not (equal (fn-apc-completion-row-names-p record "<a@x>" '(0 255 17) fn-arena)
                   (and (equal (fn-record-msgid w) "<a@x>")
                        (equal (fn-record-payload w) '(0 255 17)))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-apc-completion-row-names-p fn-row-wire-of))))
