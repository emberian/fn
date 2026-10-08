; Teeth and a ground check for books/paged-checkpoint-exec.lisp.
;
;   1. a word reader that takes the pack index to be J (not J - 2) is not the
;      row: the same statement fails;
;   2. a reader that treats the length word as part of the pack (J - 1) fails;
;   3. a reader that swaps the offset and length words fails;
;   4. a reader that encodes the whole event (payload included) instead of its
;      metadata is not the row;
;   5. a reader that reverses the trailer words fails;
;   6. the ground check: the executable reader over the real stobj gives the
;      words of the model's row for a record with a 17-octet payload (the
;      metadata program is a few words, the payload is not in the row), at a
;      nonzero payload offset, with the frame trailer's four words in the row.

(in-package "ACL2")
(include-book "../../books/paged-checkpoint-exec")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

;; The constrained seam, attached: the frame trailer's words (distinct per word).
(defun pckxt-trailer (p) (declare (xargs :guard t) (ignore p)) (list 11 22 33 44))

(defun pckxt-word-at (j off plen tw pack-at swap fn-octets)
  ; the reader with the pack's first word at row index PACK-AT; SWAP puts the
  ; length where the offset goes
  (declare (xargs :stobjs fn-octets :verify-guards nil))
  (let* ((n (fn-octets-len fn-octets))
         (k (adt-tp-npk n)))
    (cond ((eql j 0) 1)
          ((eql j 1) n)
          ((< j (+ 2 k))
           (let ((o (* 8 (- j pack-at))))
             (if (< o n) (fn-octets-get-word o (min 8 (- n o)) fn-octets) 0)))
          (t (nth (- j (+ 2 k)) (if swap (list* plen off tw) (list* off plen tw)))))))

(must-fail-checked
 (defthm pckxt-pack-index-is-j
   (implies (and (fn-sccb-treep (fn-pck-meta w st)) (natp j) (<= 2 j)
                 (< j (fn-pck-x-row-words (len (fn-scc-program (fn-pck-meta w st))))))
            (equal (pckxt-word-at j (+ 37 off) (len (fn-pck-payload w)) (fn-cpl-trailer-words-impl (fn-pck-payload w)) 0 nil
                                  (fn-pck-x-encode (fn-pck-meta w st) fn-octets))
                   (nth j (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row w off st)))))))

(must-fail-checked
 (defthm pckxt-length-word-in-the-pack
   (implies (and (fn-sccb-treep (fn-pck-meta w st)) (natp j) (<= 2 j)
                 (< j (fn-pck-x-row-words (len (fn-scc-program (fn-pck-meta w st))))))
            (equal (pckxt-word-at j (+ 37 off) (len (fn-pck-payload w)) (fn-cpl-trailer-words-impl (fn-pck-payload w)) 1 nil
                                  (fn-pck-x-encode (fn-pck-meta w st) fn-octets))
                   (nth j (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row w off st)))))))

(must-fail-checked
 (defthm pckxt-offset-and-length-swapped
   (implies (and (fn-sccb-treep (fn-pck-meta w st)) (natp j)
                 (< j (fn-pck-x-row-words (len (fn-scc-program (fn-pck-meta w st))))))
            (equal (pckxt-word-at j (+ 37 off) (len (fn-pck-payload w)) (fn-cpl-trailer-words-impl (fn-pck-payload w)) 2 t
                                  (fn-pck-x-encode (fn-pck-meta w st) fn-octets))
                   (nth j (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row w off st)))))))

(must-fail-checked
 (defthm pckxt-trailer-reversed
   (implies (and (fn-sccb-treep (fn-pck-meta w st)) (natp j)
                 (< j (fn-pck-x-row-words (len (fn-scc-program (fn-pck-meta w st))))))
            (equal (pckxt-word-at j (+ 37 off) (len (fn-pck-payload w))
                                  (reverse (fn-cpl-trailer-words-impl (fn-pck-payload w))) 2 nil
                                  (fn-pck-x-encode (fn-pck-meta w st) fn-octets))
                   (nth j (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row w off st)))))))

(must-fail-checked
 (defthm pckxt-encodes-the-payload-too
   ; the buffer holds the whole event's program: the word count and the words
   ; are not the row's
   (implies (and (fn-sccb-treep w) (fn-sccb-treep (fn-pck-meta w st)) (natp j)
                 (< j (fn-pck-x-row-words (len (fn-scc-program (fn-pck-meta w st))))))
            (equal (fn-pck-x-row-word j (+ 37 off) (len (fn-pck-payload w))
                                      (car (fn-cpl-trailer-words-impl (fn-pck-payload w)))
                                      (cadr (fn-cpl-trailer-words-impl (fn-pck-payload w)))
                                      (caddr (fn-cpl-trailer-words-impl (fn-pck-payload w)))
                                      (cadddr (fn-cpl-trailer-words-impl (fn-pck-payload w)))
                                      (fn-pck-x-encode w fn-octets))
                   (nth j (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row w off st)))))))

(defconst *pckxt-record*
  (fn-record-make 0 0 0 "<cp3@example.invalid>" '(1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17)
                  '("fn.test") "cp-pin-3" "cp-content-3" "cp-release-3" 3 841000000))

(defconst *pckxt-off* 4096)

(defun pckxt-collect (j n off plen tw pack-at swap fn-octets)
  (declare (xargs :stobjs fn-octets :verify-guards nil :measure (nfix (- n j))))
  (if (and (natp j) (natp n) (< j n))
      (cons (pckxt-word-at j off plen tw pack-at swap fn-octets)
            (pckxt-collect (1+ j) n off plen tw pack-at swap fn-octets))
    nil))

(defun pckxt-words (w off pack-at swap)
  ; the reader's words for event W, for PACK-AT = 2 and SWAP nil (the row's) or the wrong ones
  (declare (xargs :guard (natp pack-at) :verify-guards nil))
  (with-local-stobj fn-octets
    (mv-let (ws fn-octets)
      (let* ((fn-octets (fn-pck-x-encode (fn-pck-meta w (fn-pck-seed)) fn-octets))
             (n (fn-pck-x-row-words (fn-octets-len fn-octets))))
        (mv (pckxt-collect 0 n (+ 37 off) (len (fn-pck-payload w))
                                    (fn-cpl-trailer-words-impl (fn-pck-payload w)) pack-at swap fn-octets) fn-octets))
      ws)))

(assert-event
 (and (fn-sccb-treep (fn-pck-meta *pckxt-record* (fn-pck-seed)))
      (equal (len (fn-pck-payload *pckxt-record*)) 17)
      (equal (pckxt-words *pckxt-record* *pckxt-off* 2 nil)
             (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row *pckxt-record* *pckxt-off* (fn-pck-seed))))
      ; the last six words are the ref (offset 37 into the frame, length) and the trailer, no payload octets
      (let ((ws (pckxt-words *pckxt-record* *pckxt-off* 2 nil)))
        (equal (nthcdr (- (len ws) 6) ws) (list 4133 17 11 22 33 44)))
      (not (equal (pckxt-words *pckxt-record* *pckxt-off* 0 nil)
                  (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row *pckxt-record* *pckxt-off* (fn-pck-seed)))))
      (not (equal (pckxt-words *pckxt-record* *pckxt-off* 1 nil)
                  (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row *pckxt-record* *pckxt-off* (fn-pck-seed)))))
      (not (equal (pckxt-words *pckxt-record* *pckxt-off* 2 t)
                  (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row *pckxt-record* *pckxt-off* (fn-pck-seed)))))))
