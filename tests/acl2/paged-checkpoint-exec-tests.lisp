; Teeth and a ground check for books/paged-checkpoint-exec.lisp.
;
;   1. a word reader that takes the pack index to be J (not J - 2) is not the
;      row: the same statement fails, witness a 17-octet record;
;   2. a reader that treats the length word as part of the pack (J - 1) fails;
;   3. the ground check: the executable reader over the real stobj gives the
;      words of the model's row for a record that is a cons tree with an octets
;      leaf (a payload of 17 octets, so the last word is padded).

(in-package "ACL2")
(include-book "../../books/paged-checkpoint-exec")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

(defun pckxt-word-at (j off fn-octets)
  ; the reader with the pack's first word at row index OFF
  (declare (xargs :stobjs fn-octets :verify-guards nil))
  (let ((n (fn-octets-len fn-octets)))
    (cond ((eql j 0) 1)
          ((eql j 1) n)
          (t (let ((o (* 8 (- j off))))
               (if (< o n) (fn-octets-get-word o (min 8 (- n o)) fn-octets) 0))))))

(must-fail-checked
 (defthm pckxt-pack-index-is-j
   (implies (and (fn-sccb-treep x) (natp j) (<= 2 j) (< j (fn-pck-x-row-words (len (fn-scc-program x)))))
            (equal (pckxt-word-at j 0 (fn-pck-x-encode x fn-octets))
                   (nth j (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row x)))))))

(must-fail-checked
 (defthm pckxt-length-word-in-the-pack
   (implies (and (fn-sccb-treep x) (natp j) (<= 2 j) (< j (fn-pck-x-row-words (len (fn-scc-program x)))))
            (equal (pckxt-word-at j 1 (fn-pck-x-encode x fn-octets))
                   (nth j (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row x)))))))

(defconst *pckxt-record*
  (cons '(1 . 2) '(1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17)))

(defun pckxt-collect (j n which fn-octets)
  (declare (xargs :stobjs fn-octets :verify-guards nil :measure (nfix (- n j))))
  (if (and (natp j) (natp n) (< j n))
      (cons (pckxt-word-at j which fn-octets) (pckxt-collect (1+ j) n which fn-octets))
    nil))

(defun pckxt-words (x which)
  ; the reader's words for X, for WHICH = 2 (the row's), 0 or 1 (the wrong ones)
  (declare (xargs :guard (natp which) :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (ws fn-octets)
      (let* ((fn-octets (fn-pck-x-encode x fn-octets))
             (n (fn-pck-x-row-words (fn-octets-len fn-octets))))
        (mv (pckxt-collect 0 n which fn-octets) fn-octets))
      ws)))

(assert-event
 (and (fn-sccb-treep *pckxt-record*)
      (equal (pckxt-words *pckxt-record* 2)
             (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row *pckxt-record*)))
      (not (equal (pckxt-words *pckxt-record* 0)
                  (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row *pckxt-record*))))
      (not (equal (pckxt-words *pckxt-record* 1)
                  (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row *pckxt-record*))))))
