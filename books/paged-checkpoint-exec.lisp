; fn: the host's executable side of the paged checkpoint's events tape (lane
; s-pck-host, 2026-10-07; STORAGE-PROGRAM-20261006.md section 3.3, 2a layer 1).
;
; A row of `fn-pck-row' is (1 LEN PACK(program)): the tag, the program's octet
; count, then the program's octets eight to a word, little-endian, the last word
; zero padded (adt-tp-rw).  The model builds that as a list.  The host holds
; the program in the octet buffer `fn-octets' (written once by `fn-sccb-renc',
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
  (declare (xargs :guard (natp n) :verify-guards nil))
  (+ 2 (adt-tp-npk n)))

(defun fn-pck-x-row-word (j fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp j) (< j (fn-pck-x-row-words (fn-octets-len fn-octets))))
                  :verify-guards nil))
  (let ((n (fn-octets-len fn-octets)))
    (cond ((eql j 0) 1)
          ((eql j 1) n)
          (t (let ((o (* 8 (- j 2))))
               (fn-octets-get-word o (min 8 (- n o)) fn-octets))))))

(defun fn-pck-x-encode (x fn-octets)
  (declare (xargs :stobjs fn-octets :guard (fn-sccb-treep x) :verify-guards nil))
  (let ((fn-octets (fn-octets-clear fn-octets)))
    (fn-sccb-renc x 0 fn-octets)))

(defthm fn-pck-x-encode-is-the-program
  (implies (fn-sccb-treep x)
           (equal (fn-octets-list (fn-pck-x-encode x fn-octets))
                  (fn-scc-program x)))
  :hints (("Goal" :in-theory (enable fn-pck-x-encode))))

(defthm fn-pck-x-row-words-is-the-row-length
  (equal (len (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row x)))
         (fn-pck-x-row-words (len (fn-scc-program x))))
  :hints (("Goal" :in-theory (enable fn-pck-enc-row adt-tp-rw adt-tp-fw))))

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
                (< j (fn-pck-x-row-words (len prog))))
           (equal (fn-pck-x-row-word j fn-octets)
                  (nth (- j 2) (adt-tp-pack prog))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pck-x-row-word fn-pck-x-row-words) (adt-tp-wd adt-tp-npk adt-tp-pack fn-oct-word-at))
           :use ((:instance pckx-npk-bound (m (- j 2)) (n (len prog))) (:instance pckx-nth-of-pack (m (- j 2)) (o prog))
                 (:instance pckx-wd-min (k 8) (l (nthcdr (* 8 (- j 2)) prog)))))))

(defthm pckx-program-true-listp (true-listp (fn-scc-program x))
  :hints (("Goal" :in-theory (enable fn-scc-program))))
(defthm pckx-nth-cons2
  (implies (and (natp j) (<= 2 j)) (equal (nth j (list* a b c)) (nth (- j 2) c))))
(defthm pckx-row-of-program
  (equal (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row x))
         (cons 1 (cons (len (fn-scc-program x)) (adt-tp-pack (fn-scc-program x)))))
  :hints (("Goal" :in-theory (enable fn-pck-enc-row adt-tp-rw adt-tp-fw))))
(defthm fn-pck-x-row-word-is-the-row
  (implies (and (fn-sccb-treep x) (natp j) (< j (fn-pck-x-row-words (len (fn-scc-program x)))))
           (equal (fn-pck-x-row-word j (fn-pck-x-encode x fn-octets))
                  (nth j (adt-tp-rw *fn-pck-row-schema* (fn-pck-enc-row x)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-pck-x-encode fn-pck-x-row-word fn-pck-x-row-words adt-tp-pack adt-tp-rw)
           :cases ((equal j 0) (equal j 1)))
          ("Subgoal 3" :use ((:instance pckx-row-word-of-list (prog (fn-scc-program x))
                                        (fn-octets (fn-scc-program x)))
                             (:instance fn-pck-x-encode-is-the-program))
                       :in-theory (e/d (fn-octets-list) (fn-pck-x-encode fn-pck-x-row-word fn-pck-x-row-words adt-tp-pack adt-tp-rw)))
          ("Subgoal 2" :in-theory (e/d (fn-pck-x-row-word) (fn-pck-x-encode)))
          ("Subgoal 1" :use ((:instance fn-pck-x-encode-is-the-program))
                       :in-theory (e/d (fn-pck-x-row-word fn-octets-list fn-octets-len) (fn-pck-x-encode adt-tp-pack adt-tp-rw)))))

; -----------------------------------------------------------------------------
; From the host's row.  The host holds interned rows and the payload arena; the
; record a row denotes is `fn-row-wire-of' (books/store-intern.lisp).  The
; encoder takes the row and builds that record's tree for one record only (its
; own payload), as the schema-3 writer's `fn-scka-append-src' does; nothing
; the size of the store is a list.  Residual: the payload is read as one list
; (`fn-arena-payload'); a copy from the arena into the buffer without it needs
; a primitive `fn-arena' does not export.

(defun fn-pck-x-encode-row (row fn-arena fn-octets)
  (declare (xargs :stobjs (fn-arena fn-octets) :guard t :verify-guards nil))
  (fn-pck-x-encode (fn-row-wire-of row fn-arena) fn-octets))

(defthm fn-pck-x-encode-row-is-the-record-program
  (implies (fn-sccb-treep (fn-row-wire-of row fn-arena))
           (equal (fn-octets-list (fn-pck-x-encode-row row fn-arena fn-octets))
                  (fn-scc-program (fn-row-wire-of row fn-arena)))))
  
(defthm fn-pck-x-row-word-of-row-is-the-row
  ; The host's call: word J of the row of the record ROW denotes.
  (implies (and (fn-sccb-treep (fn-row-wire-of row fn-arena)) (natp j)
                (< j (fn-pck-x-row-words (len (fn-scc-program (fn-row-wire-of row fn-arena))))))
           (equal (fn-pck-x-row-word j (fn-pck-x-encode-row row fn-arena fn-octets))
                  (nth j (adt-tp-rw *fn-pck-row-schema*
                                    (fn-pck-enc-row (fn-row-wire-of row fn-arena))))))
  :hints (("Goal" :in-theory (disable fn-pck-x-row-word-is-the-row fn-pck-x-encode)
           :use ((:instance fn-pck-x-row-word-is-the-row (x (fn-row-wire-of row fn-arena)))))))
