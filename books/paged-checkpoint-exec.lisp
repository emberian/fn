; fn: the host's executable side of the paged checkpoint's events tape (lane
; s-pck-host, 2026-10-07; STORAGE-PROGRAM-20261006.md section 3.3, 2a layer 1).
;
; A row of `fn-pck-row' is (1 LEN PACK(program) OFF PLEN): the tag, the octet
; count of the METADATA tree's program, its octets eight to a word, little-endian,
; the last word zero padded, then the payload offset and length (adt-tp-rw).  The
; payload octets are not in the row: they go to the payload file.  The model
; builds the row as a list.  The host holds the metadata program in the octet
; buffer `fn-octets' (written once by `fn-sccb-renc',
; books/store-checkpoint-buffer.lisp) and reads the row's words one at a time
; with `fn-octets-get-word': no octet list, no word list.
;
;   fn-pck-x-encode           the record tree's program into a cleared buffer
;   fn-pck-x-row-word         word J of the row the buffer's program makes
;   fn-pck-x-row-words        the row's word count, from the program's length
;
;   fn-pck-x-encode-is-the-program   the buffer holds fn-scc-program of the tree
;   fn-pck-x-row-words-is-the-row-length
;   fn-pck-x-row-word-is-the-row     word J is word J of the model's row
;
; Scope, named.  Equations over the logic of `fn-octets' (the list); the
; stobj's exec is its correspondence proof (books/octets-stobj.lisp).  The words
; being below 2^64 is the generator's premise (adt-tp-u64s-seq-words), not
; restated here.

(in-package "ACL2")
(include-book "paged-checkpoint")
(include-book "store-checkpoint-buffer")
(include-book "store-intern")
(local (include-book "arithmetic/top" :dir :system))

(defun fn-pck-x-row-words (n)
  ; The row's words: the tag, the META program's octet count N, its packed
  ; octets, then the payload offset and length.
  (declare (xargs :guard (natp n) :verify-guards nil))
  (+ 8 (adt-tp-npk n)))

(defun fn-pck-x-row-word (j off plen d0 d1 d2 d3 fn-octets)
  ; Word J of the row whose META program is in the buffer: after the program,
  ; the ref's offset OFF (the payload's, 37 octets into its frame) and length
  ; PLEN, then the frame trailer's four words D0..D3.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp j) (< j (fn-pck-x-row-words (fn-octets-len fn-octets))))
                  :verify-guards nil))
  (let* ((n (fn-octets-len fn-octets))
         (k (adt-tp-npk n)))
    (cond ((eql j 0) 1)
          ((eql j 1) n)
          ((< j (+ 2 k))
           (let ((o (* 8 (- j 2))))
             (fn-octets-get-word o (min 8 (- n o)) fn-octets)))
          (t (let ((m (- j (+ 2 k))))
               (cond ((eql m 0) off)
                     ((eql m 1) plen)
                     ((eql m 2) d0)
                     ((eql m 3) d1)
                     ((eql m 4) d2)
                     (t d3)))))))

(defun fn-pck-x-encode (x fn-octets)
  (declare (xargs :stobjs fn-octets :guard (fn-sccb-treep x) :verify-guards nil))
  (let ((fn-octets (fn-octets-clear fn-octets)))
    (fn-sccb-renc x 0 fn-octets)))

(defthm fn-pck-x-encode-is-the-program
  (implies (fn-sccb-treep x)
           (equal (fn-octets-list (fn-pck-x-encode x fn-octets))
                  (fn-scc-program x)))
  :hints (("Goal" :in-theory (enable fn-pck-x-encode))))

; -----------------------------------------------------------------------------
; The row's words are the buffer's words.

(defthm pckx-oct-nth-is-car-nthcdr
  (implies (natp i) (equal (fn-oct-nth i xs) (car (nthcdr i xs))))
  :hints (("Goal" :in-theory (enable fn-oct-nth))))


(defun pckx-ind (i k) (if (posp k) (pckx-ind (1+ (nfix i)) (1- k)) i))
(defthm pckx-word-at-is-wd
  (implies (and (natp i) (natp k) (true-listp xs))
           (equal (fn-oct-word-at i k xs) (adt-tp-wd (nthcdr i xs) k)))
  :hints (("Goal" :induct (pckx-ind i k)
           :in-theory (e/d (fn-oct-word-at adt-tp-wd pckx-oct-nth-is-car-nthcdr) (nth nthcdr)))))
(defthm pckx-wd-min
  (implies (natp k) (equal (adt-tp-wd l (min k (len l))) (adt-tp-wd l k)))
  :hints (("Goal" :in-theory (enable adt-tp-wd) :induct (adt-tp-wd l k))))

(defun pckx-ind8 (m o) (if (zp m) o (pckx-ind8 (1- m) (nthcdr 8 o))))
(defthm pckx-npk-step
  (implies (posp n) (equal (adt-tp-npk n) (+ 1 (adt-tp-npk (nfix (- n 8))))))
  :hints (("Goal" :expand ((adt-tp-npk n)))))
(defthm pckx-nth-of-pack
  (implies (and (natp m) (< m (adt-tp-npk (len o))) (true-listp o))
           (equal (nth m (adt-tp-pack o)) (adt-tp-wd (nthcdr (* 8 m) o) 8)))
  :hints (("Goal" :induct (pckx-ind8 m o) :in-theory (disable adt-tp-wd adt-tp-npk))
          ("Subgoal *1/2" :expand ((adt-tp-pack o)) :use ((:instance pckx-npk-step (n (len o)))
                                       (:instance adt-tp-len-nthcdr-x (n 8) (w o))))
          ("Subgoal *1/1" :expand ((adt-tp-pack o) (adt-tp-npk (len o))))))

(defun pckx-ind8n (m n) (if (zp m) n (pckx-ind8n (1- m) (nfix (- n 8)))))
(defthm pckx-npk-bound
  (implies (and (natp m) (natp n) (< m (adt-tp-npk n))) (< (* 8 m) n))
  :hints (("Goal" :induct (pckx-ind8n m n) :in-theory (disable adt-tp-npk))
          ("Subgoal *1/2" :use ((:instance pckx-npk-step (n n))))
          ("Subgoal *1/1" :expand ((adt-tp-npk n)))))

(defthm pckx-row-word-of-list
  (implies (and (true-listp prog) (equal fn-octets prog) (natp j) (<= 2 j)
                (< j (+ 2 (adt-tp-npk (len prog)))))
           (equal (fn-pck-x-row-word j off plen d0 d1 d2 d3 fn-octets)
                  (nth (- j 2) (adt-tp-pack prog))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pck-x-row-word) (adt-tp-wd adt-tp-npk adt-tp-pack fn-oct-word-at))
           :use ((:instance pckx-npk-bound (m (- j 2)) (n (len prog))) (:instance pckx-nth-of-pack (m (- j 2)) (o prog))
                 (:instance pckx-wd-min (k 8) (l (nthcdr (* 8 (- j 2)) prog)))))))

(defthm pckx-program-true-listp (true-listp (fn-scc-program x))
  :hints (("Goal" :in-theory (enable fn-scc-program))))

(defthm pckx-row-of-program
  (equal (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row w off st))
         (cons 1 (cons (len (fn-scc-program (fn-pck-meta w st)))
                       (append (adt-tp-pack (fn-scc-program (fn-pck-meta w st)))
                               (list (+ *fn-cpl-header-octets* off) (len (fn-pck-payload w))
                                     (car (fn-cpl-trailer-words-impl (fn-pck-payload w)))
                                     (cadr (fn-cpl-trailer-words-impl (fn-pck-payload w)))
                                     (caddr (fn-cpl-trailer-words-impl (fn-pck-payload w)))
                                     (cadddr (fn-cpl-trailer-words-impl (fn-pck-payload w))))))))
  :hints (("Goal" :in-theory (e/d (fn-pck-enc-row adt-tp-rw adt-tp-fw adt-enc) (fn-pck-meta fn-pck-payload)))))

(defthm fn-pck-x-row-words-is-the-row-length
  (equal (len (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row w off st)))
         (fn-pck-x-row-words (len (fn-scc-program (fn-pck-meta w st)))))
  :hints (("Goal" :in-theory (e/d (fn-pck-x-row-words) (adt-tp-rw adt-tp-npk adt-tp-pack fn-pck-meta fn-pck-payload fn-pck-enc-row))
           :use ((:instance adt-tp-len-pack (o (fn-scc-program (fn-pck-meta w st))))
                 pckx-row-of-program))))

(defthm pckx-nth-append-split
  (implies (and (natp i) (true-listp x))
           (equal (nth i (append x y))
                  (if (< i (len x)) (nth i x) (nth (- i (len x)) y)))))

(defthm pckx-nth-rest
  (implies (and (natp j) (<= 2 j))
           (equal (nth j (cons a (cons b c))) (nth (- j 2) c))))

(defthm pckx-word-low
  ; A pack word.
  (implies (and (true-listp prog) (equal fn-octets prog) (natp j) (<= 2 j)
                (< j (+ 2 (adt-tp-npk (len prog)))))
           (equal (fn-pck-x-row-word j off plen d0 d1 d2 d3 fn-octets)
                  (nth j (cons 1 (cons (len prog) (append (adt-tp-pack prog) (list off plen d0 d1 d2 d3)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-pck-x-row-word adt-tp-pack adt-tp-npk pckx-nth-append-split)
           :use ((:instance adt-tp-len-pack (o prog))
                 (:instance pckx-row-word-of-list)
                 (:instance pckx-nth-append-split (i (+ -2 j)) (x (adt-tp-pack prog)) (y (list off plen d0 d1 d2 d3)))))))

(defthm pckx-word-tail
  ; The offset and length words.
  (implies (and (true-listp prog) (equal fn-octets prog) (natp j)
                (<= (+ 2 (adt-tp-npk (len prog))) j) (< j (+ 8 (adt-tp-npk (len prog)))))
           (equal (fn-pck-x-row-word j off plen d0 d1 d2 d3 fn-octets)
                  (nth j (cons 1 (cons (len prog) (append (adt-tp-pack prog) (list off plen d0 d1 d2 d3)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pck-x-row-word fn-octets-len) (adt-tp-pack adt-tp-npk pckx-nth-append-split))
           :use ((:instance adt-tp-len-pack (o prog))
                 (:instance pckx-nth-append-split (i (+ -2 j)) (x (adt-tp-pack prog)) (y (list off plen d0 d1 d2 d3)))))))

(defthm pckx-word-head
  ; The tag and the length words.
  (implies (and (true-listp prog) (equal fn-octets prog) (natp j) (< j 2))
           (equal (fn-pck-x-row-word j off plen d0 d1 d2 d3 fn-octets)
                  (nth j (cons 1 (cons (len prog) (append (adt-tp-pack prog) (list off plen d0 d1 d2 d3)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pck-x-row-word fn-octets-len) (adt-tp-pack adt-tp-npk))
           :cases ((equal j 0) (equal j 1)))))

(defthm pckx-word-of-list
  ; The reader over a buffer that is the list PROG: word J of the row
  ; (1 N PACK(PROG) OFF PLEN).
  (implies (and (true-listp prog) (equal fn-octets prog) (natp j)
                (< j (fn-pck-x-row-words (len prog))))
           (equal (fn-pck-x-row-word j off plen d0 d1 d2 d3 fn-octets)
                  (nth j (cons 1 (cons (len prog) (append (adt-tp-pack prog) (list off plen d0 d1 d2 d3)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pck-x-row-words) (fn-pck-x-row-word adt-tp-pack adt-tp-npk pckx-nth-append-split))
           :cases ((< j 2) (< j (+ 2 (adt-tp-npk (len prog)))))
           :use ((:instance pckx-word-head) (:instance pckx-word-low) (:instance pckx-word-tail)))))

(defthm fn-pck-x-row-word-is-the-row
  ; Word J of the row of event W (payload frame at OFF) is the buffer's word
  ; after the META tree of W is encoded; the payload contributes its length
  ; and its frame trailer's words.
  (implies (and (fn-sccb-treep (fn-pck-meta w st)) (natp j)
                (< j (fn-pck-x-row-words (len (fn-scc-program (fn-pck-meta w st))))))
           (equal (fn-pck-x-row-word j (+ *fn-cpl-header-octets* off) (len (fn-pck-payload w))
                                     (car (fn-cpl-trailer-words-impl (fn-pck-payload w)))
                                     (cadr (fn-cpl-trailer-words-impl (fn-pck-payload w)))
                                     (caddr (fn-cpl-trailer-words-impl (fn-pck-payload w)))
                                     (cadddr (fn-cpl-trailer-words-impl (fn-pck-payload w)))
                                     (fn-pck-x-encode (fn-pck-meta w st) fn-octets))
                  (nth j (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row w off st)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-pck-x-encode fn-pck-x-row-word fn-pck-x-row-words adt-tp-pack adt-tp-rw adt-tp-npk
                               fn-pck-meta fn-pck-payload fn-pck-enc-row)
           :use ((:instance pckx-word-of-list (prog (fn-scc-program (fn-pck-meta w st)))
                            (fn-octets (fn-pck-x-encode (fn-pck-meta w st) fn-octets))
                            (off (+ *fn-cpl-header-octets* off))
                            (plen (len (fn-pck-payload w)))
                            (d0 (car (fn-cpl-trailer-words-impl (fn-pck-payload w))))
                            (d1 (cadr (fn-cpl-trailer-words-impl (fn-pck-payload w))))
                            (d2 (caddr (fn-cpl-trailer-words-impl (fn-pck-payload w))))
                            (d3 (cadddr (fn-cpl-trailer-words-impl (fn-pck-payload w)))))
                 (:instance fn-pck-x-encode-is-the-program (x (fn-pck-meta w st)))
                 pckx-row-of-program))))

; -----------------------------------------------------------------------------
; From the host's row.  The host holds interned rows and the payload arena; the
; record a row denotes is `fn-row-wire-of' (books/store-intern.lisp).  The
; encoder takes the row and builds that record's tree for one record only (its
; own payload), as the schema-3 writer's `fn-scka-append-src' does; nothing
; the size of the store is a list.  Residual: the payload is read as one list
; (`fn-arena-payload'); a copy from the arena into the buffer without it needs
; a primitive `fn-arena' does not export.

(defun fn-pck-x-encode-row (row fn-arena st fn-octets)
  ; The METADATA tree of the record ROW denotes, at the fold state ST, into the buffer; the payload
  ; is not encoded here (it goes to the payload file, books/checkpoint-payloads.lisp).
  (declare (xargs :stobjs (fn-arena fn-octets) :guard t :verify-guards nil))
  (fn-pck-x-encode (fn-pck-meta (fn-row-wire-of row fn-arena) st) fn-octets))

(defthm fn-pck-x-encode-row-is-the-meta-program
  (implies (fn-sccb-treep (fn-pck-meta (fn-row-wire-of row fn-arena) st))
           (equal (fn-octets-list (fn-pck-x-encode-row row fn-arena st fn-octets))
                  (fn-scc-program (fn-pck-meta (fn-row-wire-of row fn-arena) st))))
  :hints (("Goal" :in-theory (disable fn-pck-x-encode-is-the-program)
           :use ((:instance fn-pck-x-encode-is-the-program
                            (x (fn-pck-meta (fn-row-wire-of row fn-arena) st)))))))

(defthm fn-pck-x-row-word-of-row-is-the-row
  ; The host's call: word J of the row of the record ROW denotes, whose
  ; payload frame starts at FRAME in the payload file.  The row's offset
  ; word is the payload's (37 octets into the frame); PLEN is the payload's
  ; length and D0..D3 the trailer words the payload writer produced.
  (implies (and (fn-sccb-treep (fn-pck-meta (fn-row-wire-of row fn-arena) st)) (natp j)
                (equal off (+ *fn-cpl-header-octets* frame))
                (equal plen (len (fn-pck-payload (fn-row-wire-of row fn-arena))))
                (equal d0 (car (fn-cpl-trailer-words-impl (fn-pck-payload (fn-row-wire-of row fn-arena)))))
                (equal d1 (cadr (fn-cpl-trailer-words-impl (fn-pck-payload (fn-row-wire-of row fn-arena)))))
                (equal d2 (caddr (fn-cpl-trailer-words-impl (fn-pck-payload (fn-row-wire-of row fn-arena)))))
                (equal d3 (cadddr (fn-cpl-trailer-words-impl (fn-pck-payload (fn-row-wire-of row fn-arena)))))
                (< j (fn-pck-x-row-words
                      (len (fn-scc-program (fn-pck-meta (fn-row-wire-of row fn-arena) st))))))
           (equal (fn-pck-x-row-word j off plen d0 d1 d2 d3 (fn-pck-x-encode-row row fn-arena st fn-octets))
                  (nth j (adt-tp-rw *fn-pck-row-schema*
                                    (fn-pck-enc-row (fn-row-wire-of row fn-arena) frame st)))))
  :hints (("Goal" :in-theory (disable fn-pck-x-row-word-is-the-row fn-pck-x-encode)
           :use ((:instance fn-pck-x-row-word-is-the-row (w (fn-row-wire-of row fn-arena)) (off frame))))))
