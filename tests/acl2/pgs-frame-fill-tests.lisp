; The in-place page fill's ACL2 half (books/assumptions-pgs-host-io.lisp):
; `fn-pgb-frame-put', what the host runs over its page buffer after one pread.
;
; 1. Executed witness.  A 16384-octet page whose first word is 2^64-1 and whose
;    second is a distinct little-endian pattern is put into the image array of
;    a local pgs-mem at word 2048; the words read back are the little-endian
;    words of the octets (the one at 2^64-1 exercises the unboxed top of the
;    u64 range), words outside the frame are untouched.
; 2. The word-wise constraint the consumers use, `fn-pgs-fill-frame-word', is
;    a theorem about the fill: its statement is instantiated at a concrete
;    page, so the derived theorem is exercised and not only admitted.
; 3. Teeth: the keystone with the byte order reversed (big-endian words) is
;    refused, and the executed page reads a different word big-endian.
(in-package "ACL2")
(include-book "../../books/assumptions-pgs-host-io")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

(defun pft-fill (j n)
  (declare (xargs :measure (nfix (- n j)) :guard t))
  (if (and (natp j) (natp n) (< j n))
      (cons (+ 1 (mod j 251)) (pft-fill (+ 1 j) n))
    nil))

(defun pft-page ()
  ; octets 0..7 = 255 (word 0 = 2^64-1); octet j = 1 + (j mod 251) after, so word 1 = 0x0908070605040302 + ...
  (declare (xargs :guard t))
  (append (make-list 8 :initial-element 255)
          (pft-fill 8 16384)))

(defun pft-o (j) (declare (xargs :guard t)) (+ 1 (mod (nfix j) 251)))

(defun pft-run ()
  ; (mv page-words-read-back word-at-2047 word-at-4096-untouched)
  (with-local-stobj pgs-mem
    (mv-let (r pgs-mem)
      (let* ((pgs-mem (resize-pgs-w 6144 pgs-mem)))
        (with-local-stobj fn-pgb
          (mv-let (r2 fn-pgb pgs-mem)
            (let* ((fn-pgb (fn-pgb-from-list (pft-page) fn-pgb))
                   (pgs-mem (fn-pgb-frame-put 0 2048 fn-pgb pgs-mem)))
              (mv (list (pgs-wi 2048 pgs-mem) (pgs-wi 2049 pgs-mem) (pgs-wi 4095 pgs-mem)
                        (pgs-wi 2047 pgs-mem) (pgs-wi 4096 pgs-mem) (pgs-wi 6143 pgs-mem))
                  fn-pgb pgs-mem))
            (mv r2 pgs-mem))))
      r)))

(assert! (equal (pft-run)
                (list 18446744073709551615
                      ;; octets 8..15 are 9,10,..,16 little-endian
                      (+ 9 (* 256 10) (* 65536 11) (* 16777216 12) (* 4294967296 13)
                         (* 1099511627776 14) (* 281474976710656 15) (* 72057594037927936 16))
                      ;; word 2047 of the page: octets 16376..16383, octet j = 1 + (j mod 251)
                      (+ (pft-o 16376) (* 256 (pft-o 16377)) (* 65536 (pft-o 16378))
                         (* 16777216 (pft-o 16379)) (* 4294967296 (pft-o 16380))
                         (* 1099511627776 (pft-o 16381)) (* 281474976710656 (pft-o 16382))
                         (* 72057594037927936 (pft-o 16383)))
                      0 0 0)))

; the derived word-wise fact at a concrete instance (any fill, any page)
(defthm pft-word-0
  (implies (and (fn-pgs-frame-sel-p sel) (natp base)
                (<= (+ base 2048) (fn-pgs-frame-len sel pgs-mem)))
           (equal (fn-pgs-frame-word sel base (fn-pgs-fill-frame file addr sel base pgs-mem))
                  (car (fn-pgs-page-words file addr))))
  :hints (("Goal" :use ((:instance fn-pgs-fill-frame-word (i 0))
                        (:instance fn-pgs-page-words-shape))
           :in-theory (disable fn-pgs-fill-frame-word))))

; teeth: big-endian words
(defun pft-word-be (i k oct)
  (declare (xargs :guard (and (natp i) (true-listp oct)) :measure (nfix k)))
  (if (posp k)
      (+ (nfix (nth (+ (nfix i) (1- k)) oct)) (* 256 (pft-word-be i (1- k) oct)))
    0))

(defun pft-words-be (i m oct)
  (declare (xargs :guard (and (natp i) (natp m) (true-listp oct)) :measure (nfix m)))
  (if (zp m) nil (cons (pft-word-be i 8 oct) (pft-words-be (+ i 8) (1- m) oct))))

(must-fail-checked
 (defthm pft-frame-put-is-big-endian
   (implies (and (fn-pgs-frame-sel-p sel) (natp base)
                 (equal (len fn-pgb) 16384)
                 (<= (+ base 2048) (fn-pgs-frame-len sel pgs-mem)))
            (equal (fn-pgb-frame-put sel base fn-pgb pgs-mem)
                   (fn-pgs-frame-put sel base (pft-words-be 0 2048 fn-pgb) pgs-mem)))
   :hints (("Goal" :use ((:instance fn-pgb-frame-put-is-frame-put-of-words))
            :in-theory (disable fn-pgb-frame-put-is-frame-put-of-words)))))

(assert! (not (equal (pft-word-be 8 8 (pft-page)) (fn-oct-word-at 8 8 (pft-page)))))
