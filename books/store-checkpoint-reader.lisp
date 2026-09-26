; fn: the state checkpoint read from the octet buffer (D27, representation
; wave D-3; planning/evidence/rep-wave-d-3-2026-09-26.md).
;
; `fn-scc-decode-segments' (books/store-checkpoint-codec.lisp) is the P3
; checkpoint's reader: each FNSC segment as an octet list, joined into one
; list of the postfix program, run by `fn-scc-run', each payload leaf `take'n
; from it.  On the host that was the whole file as conses twice (sixteen
; bytes per octet, 10.7 GB each for a 670 MB file) beside the value it
; built, and at N = 10,000 x 32 KiB the owner died by heap exhaustion
; reading the checkpoint `store checkpoint' had just published
; (rep-wave-d-2 record, section 5).
;
; This book reads the file from the octet buffer (books/octets-stobj.lisp;
; one byte per octet) in the shape the writer produced it
; (books/store-checkpoint-buffer.lisp `fn-sccb-plan'): a PLAN of frames
; (HEADER A B TRAILER), the header and the trailer as short octet lists (37
; and 32 octets), the chunk as the buffer's cells A..B, the chunks
; contiguous (each frame begins where the previous ended).  The host reads
; the file one segment at a time (host/native/io.lisp
; `fnn-state-checkpoint-plan'), appends each chunk's bytes into the buffer
; and hands the plan to `fn-store-sco-decode' (host/store-node-host.lisp),
; which calls `fn-sccr-decode-plan' here:
;
;   * `fn-sccr-planp': the shape above, checked; a mis-shaped plan is
;     refused as :layout, a verdict the list decoder never gives;
;   * `fn-sccr-join': per frame the header is parsed from its list, the
;     index, count and sequence are the chain's, LENGTH is B - A, and the
;     seal over the previous trailer, the header and the chunk equals the
;     trailer.  The chunk is read for its seal as a list of at most one
;     segment (`fn-sccb-slice-acc', garbage before the next), exactly as
;     the writer seals it: `fn-scc-seal' is `fn-frame-trailer', the
;     constrained digest, which has no buffer-range twin in the logic.
;     Nothing joins the chunks: the program is the buffer's cells from the
;     first frame's A to the last frame's B;
;   * `fn-sccr-run' and `fn-sccr-step': the stack machine by index.  A
;     payload leaf is `fn-sccb-slice-acc' of its range, the record's own
;     octet list (the retained representation until PKT-293), built once;
;     a natural's digits and a string's characters are short slices;
;   * `fn-sccr-decode-plan': `fn-scc-decode-segments' mirrored, with the
;     same verdicts (:header, :segment, :truncated, :tree, :value).
;
; What is proved.  `fn-sccr-run-is-run': the index machine over the cells
; [i, end) is `fn-scc-run' over that slice.  The twin
; `fn-sccr-decode-plan-is-decode-segments': for a well-shaped plan, the
; buffer decode is the list decode of the frames' octets
; (`fn-sccb-frame-octets', which is what the host's file bytes are), on any
; buffer contents, corrupt ones included, with the same verdict.  The
; KEYSTONE `fn-sccr-decode-of-plan' (PRF-135): the buffer decode of the
; writer's plan over the buffer it leaves is (:ok c), the inverse of
; `fn-sccb-plan-is-file-octets'.  `fn-sccr-admit-segment' is the decision
; the host takes per segment before reading it (the segment bound and the
; file bound, both from the profile); `fn-sccr-admitted-within-bounds' says
; what an admission means.

(in-package "ACL2")
(include-book "store-checkpoint-buffer")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; List facts, local.

(local
 (defthm fn-sccr-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-sccr-append-nil
   (implies (true-listp x) (equal (append x nil) x))))

(local
 (defthm fn-sccr-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn-sccr-long-enoughp-is-len
   (implies (natp n)
            (equal (fn-scc-long-enoughp n xs) (<= n (len xs))))))

(local
 (defthm fn-sccr-take-of-append-short
   (implies (and (natp k) (<= k (len a)))
            (equal (take k (append a b)) (take k a)))))

(local
 (defthm fn-sccr-nthcdr-of-append-short
   (implies (and (natp k) (<= k (len a)))
            (equal (nthcdr k (append a b)) (append (nthcdr k a) b)))))

(local
 (defthm fn-sccr-nth-of-append-short
   (implies (and (natp k) (< k (len a)))
            (equal (nth k (append a b)) (nth k a)))))

(local
 (defthm fn-sccr-take-all
   (implies (and (true-listp x) (equal k (len x)))
            (equal (take k x) x))))

(local
 (defthm fn-sccr-nthcdr-all
   (implies (and (true-listp x) (equal k (len x)))
            (equal (nthcdr k x) nil))))

(local
 (defthm fn-sccr-len-nthcdr
   (implies (and (natp k) (<= k (len x)))
            (equal (len (nthcdr k x)) (- (len x) k)))))

(local
 (defthm fn-sccr-len-take
   (equal (len (take k x)) (nfix k))))

(local
 (defthm fn-sccr-true-listp-nthcdr
   (implies (true-listp x) (true-listp (nthcdr k x)))))

(local
 (defthm fn-sccr-nthcdr-nthcdr
   (implies (and (natp a) (natp b))
            (equal (nthcdr b (nthcdr a x)) (nthcdr (+ a b) x)))))

(local
 (defthm fn-sccr-true-listp-take
   (true-listp (take k x))))

(local
 (defthm fn-sccr-revappend-revappend
   (equal (revappend (revappend a b) c) (revappend b (append a c)))))

(local
 (defthm fn-sccr-true-list-fix-of-true-list
   (implies (true-listp x) (equal (true-list-fix x) x))))

(local
 (defthm fn-sccr-unequal-lens
   (implies (not (equal (len x) (len y)))
            (not (equal x y)))))

; The two octet-list recognizers are one predicate (stated as two
; backchaining rules: an equality would rewrite every codec fact away).
(defthm fn-sccr-cbor-octet-listp-is-scc-octet-listp
  (implies (fn-cbor-octet-listp x) (fn-scc-octet-listp x))
  :hints (("Goal" :in-theory (enable fn-scc-octet-listp fn-cbor-octet-listp
                                     fn-cbor-octetp))))

(defthm fn-sccr-scc-octet-listp-is-cbor-octet-listp
  (implies (fn-scc-octet-listp x) (fn-cbor-octet-listp x))
  :hints (("Goal" :in-theory (enable fn-scc-octet-listp fn-cbor-octet-listp
                                     fn-cbor-octetp))))

(local
 (defthm fn-sccr-octet-listp-append
   (implies (and (fn-scc-octet-listp a) (fn-scc-octet-listp b))
            (fn-scc-octet-listp (append a b)))))

(local
 (defthm fn-sccr-octet-listp-nthcdr
   (implies (fn-scc-octet-listp x)
            (fn-scc-octet-listp (nthcdr k x)))))

; -----------------------------------------------------------------------------
; The slice, opened once: `fn-oct-slice-list' (octets-stobj) is closed with
; its `take'/`nthcdr' equation; the index machine's correspondence wants its
; car, cdr, length, take, nthcdr and the join of two adjacent slices.

(local
 (defthm fn-sccr-slice-consp
   (equal (consp (fn-oct-slice-list i n fn-octets))
          (and (natp i) (natp n) (< i n)))
   :hints (("Goal" :expand ((fn-oct-slice-list i n fn-octets))))))

(local
 (defthm fn-sccr-slice-car
   (implies (and (natp i) (natp n) (< i n))
            (equal (car (fn-oct-slice-list i n fn-octets)) (nth i fn-octets)))
   :hints (("Goal" :expand ((fn-oct-slice-list i n fn-octets))
            :in-theory (enable fn-octets-get)))))

(local
 (defthm fn-sccr-slice-cdr
   (implies (and (natp i) (natp n))
            (equal (cdr (fn-oct-slice-list i n fn-octets))
                   (fn-oct-slice-list (1+ i) n fn-octets)))
   :hints (("Goal" :expand ((fn-oct-slice-list i n fn-octets)
                            (fn-oct-slice-list (1+ i) n fn-octets))))))

; Stated over <=, so that a slice's length is its bounds' difference with
; no case split (the empty case is octets-stobj's fn-oct-slice-list-empty).
(local
 (defthm fn-sccr-slice-len
   (implies (and (natp i) (natp n) (<= i n))
            (equal (len (fn-oct-slice-list i n fn-octets)) (- n i)))
   :hints (("Goal" :induct (fn-oct-slice-list i n fn-octets)
            :in-theory (enable fn-oct-slice-list)))))

(local
 (defthm fn-sccr-slice-true-listp
   (true-listp (fn-oct-slice-list i n fn-octets))
   :hints (("Goal" :induct (fn-oct-slice-list i n fn-octets)
            :in-theory (enable fn-oct-slice-list)))))

(local
 (defun fn-sccr-slice-ind (k i n fn-octets)
   (declare (xargs :stobjs fn-octets :verify-guards nil
                   :measure (nfix (- n i))))
   (if (or (not (natp i)) (not (natp n)) (<= n i) (zp k))
       (list k i n)
     (fn-sccr-slice-ind (1- k) (1+ i) n fn-octets))))

(local
 (defthm fn-sccr-slice-take
   (implies (and (natp i) (natp n) (natp k) (<= (+ i k) n))
            (equal (take k (fn-oct-slice-list i n fn-octets))
                   (fn-oct-slice-list i (+ i k) fn-octets)))
   :hints (("Goal" :induct (fn-sccr-slice-ind k i n fn-octets)
            :in-theory (enable fn-oct-slice-list)))))

(local
 (defthm fn-sccr-slice-nthcdr
   (implies (and (natp i) (natp n) (natp k) (<= (+ i k) n))
            (equal (nthcdr k (fn-oct-slice-list i n fn-octets))
                   (fn-oct-slice-list (+ i k) n fn-octets)))
   :hints (("Goal" :induct (fn-sccr-slice-ind k i n fn-octets)
            :in-theory (enable fn-oct-slice-list)))))

(local
 (defthm fn-sccr-slice-append
   (implies (and (natp a) (natp b) (natp c) (<= a b) (<= b c))
            (equal (append (fn-oct-slice-list a b fn-octets)
                           (fn-oct-slice-list b c fn-octets))
                   (fn-oct-slice-list a c fn-octets)))
   :hints (("Goal" :induct (fn-oct-slice-list a b fn-octets)
            :in-theory (enable fn-oct-slice-list)))))

(local
 (defthm fn-sccr-slice-octets
   (implies (and (fn-cbor-octet-listp fn-octets) (natp n) (<= n (len fn-octets)))
            (fn-scc-octet-listp (fn-oct-slice-list i n fn-octets)))
   :hints (("Goal" :induct (fn-oct-slice-list i n fn-octets)
            :in-theory (enable fn-oct-slice-list fn-octets-get)))))

; The accumulator reader with an empty accumulator is the slice.
(local
 (defthm fn-sccr-slice-acc-nil-is-slice
   (implies (and (natp i) (natp n) (<= i n))
            (equal (fn-sccb-slice-acc i n nil fn-octets)
                   (fn-oct-slice-list i n fn-octets)))))

(local (in-theory (disable fn-oct-slice-list-is-take-nthcdr)))

; One cell, read as the natural it is.  The export's logical value is
; `nth', about which type reasoning knows nothing inside a sum; the
; `mbe' makes the reader a natural by type prescription, and on an octet
; buffer it is the cell (`fn-sccr-cell-is-nth').
(defun fn-sccr-cell (i fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (< i (fn-octets-len fn-octets)))
                  :guard-hints (("Goal" :use ((:instance fn-oct-nth-of-octet-listp-is-octet
                                                         (xs fn-octets) (k i)))))))
  (mbe :logic (nfix (fn-octets-get i fn-octets))
       :exec (fn-octets-get i fn-octets)))

(defthm fn-sccr-cell-natp
  (natp (fn-sccr-cell i fn-octets))
  :rule-classes :type-prescription)

(defthm fn-sccr-cell-is-nth
  (implies (and (fn-octets-p fn-octets) (natp i) (< i (len fn-octets)))
           (equal (fn-sccr-cell i fn-octets) (nth i fn-octets)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-oct-nth-of-octet-listp-is-octet
                                   (xs fn-octets) (k i))))))

(in-theory (disable fn-sccr-cell))

; The rewrite runs the other way: a cell of an octet buffer read by `nth'
; (the list machine's `car') becomes the reader, which type reasoning
; knows to be a natural; the reader itself stays closed.
(defthm fn-sccr-nth-is-cell
  (implies (and (fn-octets-p fn-octets) (natp i) (< i (len fn-octets)))
           (equal (nth i fn-octets) (fn-sccr-cell i fn-octets)))
  :hints (("Goal" :use fn-sccr-cell-is-nth)))

(defthm fn-sccr-cell-below-256
  (implies (and (fn-octets-p fn-octets) (natp i) (< i (len fn-octets)))
           (< (fn-sccr-cell i fn-octets) 256))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use (fn-sccr-cell-is-nth
                        (:instance fn-oct-nth-of-octet-listp-is-octet
                                   (xs fn-octets) (k i))))))

; -----------------------------------------------------------------------------
; The stack machine by index.  Each reader mirrors its list twin in
; store-checkpoint-codec: (VALUE . NEXT) where the twin gives (VALUE . REST),
; nil where it gives nil.

(defun fn-sccr-read-nat (i end fn-octets)
  ; A natural at I: a digit count, then the digits little-endian.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets)))))
  (if (< i end)
      (let* ((l (fn-sccr-cell i fn-octets))
             (next (+ 1 i l)))
        (if (<= next end)
            (cons (fn-scc-le-value (fn-sccb-slice-acc (+ 1 i) next nil fn-octets))
                  next)
          nil))
    nil))

(defthm fn-sccr-read-nat-is-read-nat
  (implies (and (fn-octets-p fn-octets) (natp i) (natp end) (<= i end)
                (<= end (len fn-octets)))
           (equal (fn-scc-read-nat (fn-oct-slice-list i end fn-octets))
                  (let ((r (fn-sccr-read-nat i end fn-octets)))
                    (and r (cons (car r) (fn-oct-slice-list (cdr r) end fn-octets))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-scc-read-nat) (fn-scc-le-value)))))

(defthm fn-sccr-read-nat-facts
  (implies (and (natp i) (natp end) (<= i end) (fn-octets-p fn-octets)
                (<= end (len fn-octets))
                (fn-sccr-read-nat i end fn-octets))
           (and (natp (car (fn-sccr-read-nat i end fn-octets)))
                (natp (cdr (fn-sccr-read-nat i end fn-octets)))
                (< i (cdr (fn-sccr-read-nat i end fn-octets)))
                (<= (cdr (fn-sccr-read-nat i end fn-octets)) end)))
  :hints (("Goal" :do-not-induct t :in-theory (disable fn-scc-le-value))))

(in-theory (disable fn-sccr-read-nat))

(defun fn-sccr-read-string (i end fn-octets)
  ; A string at I: its length as a natural, then its character codes.
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets)))
                  :guard-hints (("Goal" :use ((:instance fn-sccr-read-nat-facts))
                                 :in-theory (disable fn-sccr-read-nat-facts)))))
  (let ((n (fn-sccr-read-nat i end fn-octets)))
    (if (and n (<= (+ (cdr n) (car n)) end))
        (cons (coerce (fn-scc-octets-chars
                       (fn-sccb-slice-acc (cdr n) (+ (cdr n) (car n)) nil fn-octets))
                      'string)
              (+ (cdr n) (car n)))
      nil)))

(defthm fn-sccr-read-string-is-read-string
  (implies (and (fn-octets-p fn-octets) (natp i) (natp end) (<= i end)
                (<= end (len fn-octets)))
           (equal (fn-scc-read-string (fn-oct-slice-list i end fn-octets))
                  (let ((r (fn-sccr-read-string i end fn-octets)))
                    (and r (cons (car r) (fn-oct-slice-list (cdr r) end fn-octets))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sccr-read-nat-facts))
           :in-theory (e/d (fn-scc-read-string)
                           (fn-scc-le-value fn-scc-octets-chars fn-sccr-read-nat-facts)))))

(defthm fn-sccr-read-string-facts
  (implies (and (natp i) (natp end) (<= i end) (fn-octets-p fn-octets)
                (<= end (len fn-octets))
                (fn-sccr-read-string i end fn-octets))
           (and (stringp (car (fn-sccr-read-string i end fn-octets)))
                (natp (cdr (fn-sccr-read-string i end fn-octets)))
                (< i (cdr (fn-sccr-read-string i end fn-octets)))
                (<= (cdr (fn-sccr-read-string i end fn-octets)) end)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sccr-read-nat-facts))
           :in-theory (disable fn-sccr-read-nat-facts fn-scc-octets-chars))))

(in-theory (disable fn-sccr-read-string))

; One instruction at I: (STACK . NEXT) or nil, as `fn-scc-step' gives
; (STACK . REST) or nil.
(defun fn-sccr-step (i end stack fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp end) (< i end)
                              (<= end (fn-octets-len fn-octets)))
                  :guard-hints (("Goal" :use ((:instance fn-sccr-read-nat-facts (i (+ 1 i)))
                                              (:instance fn-sccr-read-string-facts (i (+ 1 i)))
                                              (:instance fn-sccr-read-string-facts (i (+ 2 i))))
                                 :in-theory (disable fn-sccr-read-nat-facts
                                                     fn-sccr-read-string-facts)))))
  (let ((op (fn-sccr-cell i fn-octets)) (i (+ 1 i)))
    (cond ((equal op *fn-scc-op-nil*) (cons (cons nil stack) i))
          ((equal op *fn-scc-op-nat*)
           (let ((n (fn-sccr-read-nat i end fn-octets)))
             (and n (cons (cons (car n) stack) (cdr n)))))
          ((equal op *fn-scc-op-neg*)
           (let ((n (fn-sccr-read-nat i end fn-octets)))
             (and n (cons (cons (- -1 (car n)) stack) (cdr n)))))
          ((equal op *fn-scc-op-char*)
           (and (< i end)
                (cons (cons (code-char (fn-sccr-cell i fn-octets)) stack) (+ 1 i))))
          ((equal op *fn-scc-op-string*)
           (let ((s (fn-sccr-read-string i end fn-octets)))
             (and s (cons (cons (car s) stack) (cdr s)))))
          ((equal op *fn-scc-op-symbol*)
           (and (< i end)
                (let ((s (fn-sccr-read-string (+ 1 i) end fn-octets))
                      (pk (fn-sccr-cell i fn-octets)))
                  (and s (fn-scc-package-index (nth pk *fn-scc-packages*))
                       (cons (cons (fn-scc-intern pk (car s)) stack) (cdr s))))))
          ((equal op *fn-scc-op-cons*)
           (and (consp stack) (consp (cdr stack))
                (cons (cons (cons (cadr stack) (car stack)) (cddr stack)) i)))
          ((equal op *fn-scc-op-octets*)
           (let ((n (fn-sccr-read-nat i end fn-octets)))
             (and n (<= (+ (cdr n) (car n)) end)
                  (cons (cons (fn-sccb-slice-acc (cdr n) (+ (cdr n) (car n)) nil fn-octets)
                              stack)
                        (+ (cdr n) (car n))))))
          (t nil))))

(defthm fn-sccr-step-is-step
  (implies (and (fn-octets-p fn-octets) (natp i) (natp end) (< i end)
                (<= end (len fn-octets)))
           (equal (fn-scc-step (fn-oct-slice-list i end fn-octets) stack)
                  (let ((r (fn-sccr-step i end stack fn-octets)))
                    (and r (cons (car r) (fn-oct-slice-list (cdr r) end fn-octets))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sccr-read-nat-facts (i (+ 1 i)))
                 (:instance fn-sccr-read-string-facts (i (+ 1 i)))
                 (:instance fn-sccr-read-string-facts (i (+ 2 i))))
           :in-theory (e/d (fn-scc-step)
                           (nth fn-scc-read-nat fn-scc-read-string fn-scc-intern
                            fn-scc-le-value fn-scc-package-index
                            fn-sccr-read-nat-facts fn-sccr-read-string-facts)))))

(defthm fn-sccr-step-advances
  (implies (and (fn-octets-p fn-octets) (natp i) (natp end) (< i end)
                (<= end (len fn-octets))
                (fn-sccr-step i end stack fn-octets))
           (and (natp (cdr (fn-sccr-step i end stack fn-octets)))
                (< i (cdr (fn-sccr-step i end stack fn-octets)))
                (<= (cdr (fn-sccr-step i end stack fn-octets)) end)))
  ; Linear too: the list machine's measure needs i < next as arithmetic.
  :rule-classes ((:rewrite)
                 (:linear :corollary
                  (implies (and (fn-octets-p fn-octets) (natp i) (natp end) (< i end)
                                (<= end (len fn-octets))
                                (fn-sccr-step i end stack fn-octets))
                           (and (< i (cdr (fn-sccr-step i end stack fn-octets)))
                                (<= (cdr (fn-sccr-step i end stack fn-octets)) end)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sccr-read-nat-facts (i (+ 1 i)))
                 (:instance fn-sccr-read-string-facts (i (+ 1 i)))
                 (:instance fn-sccr-read-string-facts (i (+ 2 i))))
           :in-theory (e/d () (nth fn-scc-intern fn-scc-le-value fn-scc-package-index
                               fn-sccr-read-nat-facts fn-sccr-read-string-facts)))))

(in-theory (disable fn-sccr-step))

(defun fn-sccr-run (i end stack fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets)))
                  :measure (nfix (- end i))
                  :guard-hints (("Goal" :use ((:instance fn-sccr-step-advances))
                                 :in-theory (disable fn-sccr-step-advances)))))
  (if (or (not (natp i)) (not (natp end)) (>= i end))
      stack
    (let ((next (fn-sccr-step i end stack fn-octets)))
      (if (and next
               (mbt (and (natp (cdr next)) (< i (cdr next)) (<= (cdr next) end))))
          (fn-sccr-run (cdr next) end (car next) fn-octets)
        :refused))))

(defthm fn-sccr-run-is-run
  (implies (and (fn-octets-p fn-octets) (natp i) (natp end) (<= i end)
                (<= end (len fn-octets)))
           (equal (fn-sccr-run i end stack fn-octets)
                  (fn-scc-run (fn-oct-slice-list i end fn-octets) stack)))
  :hints (("Goal" :induct (fn-sccr-run i end stack fn-octets)
           :in-theory (e/d (fn-scc-run) (fn-scc-step floor mod nth)))))

(defun fn-sccr-decode-tree (start end fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp start) (natp end) (<= start end)
                              (<= end (fn-octets-len fn-octets)))))
  (let ((stack (fn-sccr-run start end nil fn-octets)))
    (if (and (consp stack) (null (cdr stack)))
        (list :ok (car stack))
      (list :refused :tree))))

(defthm fn-sccr-decode-tree-is-decode-tree
  (implies (and (fn-octets-p fn-octets) (natp start) (natp end) (<= start end)
                (<= end (len fn-octets)))
           (equal (fn-sccr-decode-tree start end fn-octets)
                  (fn-scc-decode-tree (fn-oct-slice-list start end fn-octets))))
  :hints (("Goal" :in-theory (e/d (fn-scc-decode-tree) (fn-scc-run)))))

(in-theory (disable fn-sccr-run fn-sccr-decode-tree))

; -----------------------------------------------------------------------------
; The plan: frames (HEADER A B TRAILER) over the buffer, contiguous from
; a position.  `fn-sccr-at' reads a slot of any object.

(defun fn-sccr-at (n x)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      (if (consp x) (car x) nil)
    (fn-sccr-at (1- n) (if (consp x) (cdr x) nil))))

(defthm fn-sccr-at-is-nth
  (implies (true-listp x) (equal (fn-sccr-at n x) (nth n x))))

(defun fn-sccr-framep (frame fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (and (true-listp frame) (equal (len frame) 4)
       (fn-scc-octet-listp (nth 0 frame))
       (equal (len (nth 0 frame)) *fn-scc-segment-header-octets*)
       (natp (nth 1 frame)) (natp (nth 2 frame))
       (<= (nth 1 frame) (nth 2 frame))
       (<= (nth 2 frame) (fn-octets-len fn-octets))
       (fn-scc-octet-listp (nth 3 frame))
       (equal (len (nth 3 frame)) *fn-frame-trailer-octets*)))

(defun fn-sccr-planp (plan pos fn-octets)
  ; Every frame well-formed, the first beginning at POS, each next where
  ; the previous ended.
  (declare (xargs :stobjs fn-octets :guard t))
  (if (consp plan)
      (and (fn-sccr-framep (car plan) fn-octets)
           (equal (fn-sccr-at 1 (car plan)) pos)
           (fn-sccr-planp (cdr plan) (fn-sccr-at 2 (car plan)) fn-octets))
    (and (null plan) (natp pos) (<= pos (fn-octets-len fn-octets)))))

; The frames' octets: what the host's file bytes are, per frame
; (`fn-sccb-frame-octets', the writer's specification of one frame).
(defun fn-sccr-plan-segments (plan fn-octets)
  (declare (xargs :stobjs fn-octets :guard (true-list-listp plan)))
  (if (consp plan)
      (cons (fn-sccb-frame-octets (car plan) fn-octets)
            (fn-sccr-plan-segments (cdr plan) fn-octets))
    nil))

(defthm fn-sccr-planp-true-list-listp
  (implies (fn-sccr-planp plan pos fn-octets)
           (true-list-listp plan))
  :hints (("Goal" :induct (fn-sccr-planp plan pos fn-octets))))

(defthm fn-sccr-planp-pos
  (implies (fn-sccr-planp plan pos fn-octets)
           (and (natp pos) (<= pos (len fn-octets))))
  :rule-classes :forward-chaining
  :hints (("Goal" :expand ((fn-sccr-planp plan pos fn-octets))
           :in-theory (enable fn-octets-len))))

; One frame against the chain: the trailer (the next PREV), or nil.
(defun fn-sccr-open-frame (frame index count sequence prev fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (fn-sccr-framep frame fn-octets) (true-listp prev))))
  (let* ((header (nth 0 frame)) (a (nth 1 frame)) (b (nth 2 frame))
         (trailer (nth 3 frame))
         (h (fn-scc-parse-header header)))
    (and h
         (equal (nth 0 h) index)
         (equal (nth 1 h) count)
         (equal (nth 3 h) sequence)
         (equal (nth 2 h) (- b a))
         (equal trailer
                (fn-scc-seal prev header (fn-sccb-slice-acc a b nil fn-octets)))
         trailer)))

; The chain over the plan: (:ok END) with END the last frame's B, or the
; list decoder's refusal.
(defun fn-sccr-join (plan pos index count sequence prev fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (fn-sccr-planp plan pos fn-octets) (true-listp prev)
                              (natp index))))
  (if (consp plan)
      (let ((o (fn-sccr-open-frame (car plan) index count sequence prev fn-octets)))
        (if o
            (fn-sccr-join (cdr plan) (fn-sccr-at 2 (car plan)) (+ 1 index) count
                          sequence o fn-octets)
          (list :refused :segment)))
    (if (and (equal index count) (null plan))
        (list :ok pos)
      (list :refused :truncated))))

(defthm fn-sccr-join-ok-end
  (implies (and (fn-sccr-planp plan pos fn-octets)
                (equal (car (fn-sccr-join plan pos index count sequence prev fn-octets))
                       :ok))
           (and (natp (nth 1 (fn-sccr-join plan pos index count sequence prev fn-octets)))
                (<= pos (nth 1 (fn-sccr-join plan pos index count sequence prev fn-octets)))
                (<= (nth 1 (fn-sccr-join plan pos index count sequence prev fn-octets))
                    (len fn-octets))))
  :rule-classes ((:rewrite)
                 (:linear :corollary
                  (implies (and (fn-sccr-planp plan pos fn-octets)
                                (equal (car (fn-sccr-join plan pos index count sequence prev
                                                          fn-octets))
                                       :ok))
                           (and (<= pos (nth 1 (fn-sccr-join plan pos index count sequence prev
                                                             fn-octets)))
                                (<= (nth 1 (fn-sccr-join plan pos index count sequence prev
                                                         fn-octets))
                                    (len fn-octets))))))
  :hints (("Goal" :induct (fn-sccr-join plan pos index count sequence prev fn-octets)
           :in-theory (e/d (fn-octets-len) (fn-sccr-open-frame floor mod)))))

; The reader over a plan: `fn-scc-decode-segments' mirrored.
(defun fn-sccr-decode-plan (plan fn-octets)
  (declare (xargs :stobjs fn-octets :guard t
                  :guard-hints (("Goal" :use ((:instance fn-sccr-join-ok-end
                                                         (pos (if (consp plan)
                                                                  (fn-sccr-at 1 (car plan))
                                                                0))
                                                         (index 0)
                                                         (count (nth 1 (fn-scc-parse-header
                                                                        (fn-sccr-at 0 (car plan)))))
                                                         (sequence (nth 3 (fn-scc-parse-header
                                                                           (fn-sccr-at 0 (car plan)))))
                                                         (prev *fn-scc-genesis*)))
                                 :in-theory (disable fn-sccr-join-ok-end fn-sccr-join
                                                     fn-scc-parse-header)))))
  (let ((start (if (consp plan) (fn-sccr-at 1 (car plan)) 0)))
    (if (not (fn-sccr-planp plan start fn-octets))
        (list :refused :layout)
      (let ((h (and (consp plan) (fn-scc-parse-header (fn-sccr-at 0 (car plan))))))
        (if (not h)
            (list :refused :header)
          (let ((j (fn-sccr-join plan start 0 (nth 1 h) (nth 3 h) *fn-scc-genesis*
                                 fn-octets)))
            (if (not (eq (car j) :ok))
                j
              (let ((tree (fn-sccr-decode-tree start (nth 1 j) fn-octets)))
                (if (and (eq (car tree) :ok)
                         (equal (fn-scc-value-sequence (nth 1 tree)) (nth 3 h)))
                    tree
                  (list :refused :value))))))))))

; -----------------------------------------------------------------------------
; The twin: the buffer reader is the list reader on the frames' octets.

; A 37-octet header list in front of anything parses as itself with the
; rest behind it.
(local
 (defthm fn-sccr-parse-header-of-append
   (implies (and (fn-scc-octet-listp header)
                 (equal (len header) *fn-scc-segment-header-octets*))
            (equal (fn-scc-parse-header (append header rest))
                   (and (fn-scc-parse-header header)
                        (list (nth 0 (fn-scc-parse-header header))
                              (nth 1 (fn-scc-parse-header header))
                              (nth 2 (fn-scc-parse-header header))
                              (nth 3 (fn-scc-parse-header header))
                              rest))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-scc-parse-header fn-scc-u64-at)
                            (fn-scc-le-value))))))

(local
 (defthm fn-sccr-parse-header-facts
   (implies (and (fn-scc-octet-listp header)
                 (equal (len header) *fn-scc-segment-header-octets*)
                 (fn-scc-parse-header header))
            (and (natp (nth 2 (fn-scc-parse-header header)))
                 (equal (nth 4 (fn-scc-parse-header header)) nil)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-scc-parse-header fn-scc-u64-at) (fn-scc-le-value))))))

; The seal of an octet chain is a 32-octet digest.
(local
 (defthm fn-sccr-seal-is-digest
   (implies (and (fn-scc-octet-listp prev) (fn-scc-octet-listp header)
                 (fn-scc-octet-listp chunk))
            (and (fn-scc-octet-listp (fn-scc-seal prev header chunk))
                 (equal (len (fn-scc-seal prev header chunk)) *fn-frame-trailer-octets*)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-frame-trailer-is-a-digest
                             (octets (append prev header chunk))))
            :in-theory (e/d (fn-scc-seal fn-frame-digestp)
                            (fn-frame-trailer-is-a-digest))))))

; A header whose LENGTH is not the chunk's length cannot verify on the
; list side either: the trailer it cuts from the chunk and the 32-octet
; trailer is not 32 octets long, and a seal is.
(local
 (defthm fn-sccr-list-refuses-length-mismatch
   (implies (and (fn-scc-octet-listp prev) (fn-scc-octet-listp header)
                 (fn-scc-octet-listp chunk) (fn-scc-octet-listp trailer)
                 (equal (len trailer) *fn-frame-trailer-octets*)
                 (natp l) (<= l (+ (len chunk) (len trailer)))
                 (not (equal l (len chunk))))
            (not (equal (nthcdr l (append chunk trailer))
                        (fn-scc-seal prev header (take l (append chunk trailer))))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-sccr-seal-is-digest
                             (chunk (take l (append chunk trailer))))
                  (:instance fn-sccr-unequal-lens
                             (x (nthcdr l (append chunk trailer)))
                             (y (fn-scc-seal prev header (take l (append chunk trailer))))))
            :in-theory (e/d () (fn-scc-seal fn-sccr-seal-is-digest fn-sccr-unequal-lens))))))

(local
 (defthm fn-sccr-open-segment-of-frame
   (implies (and (fn-octets-p fn-octets) (fn-sccr-framep frame fn-octets)
                 (fn-scc-octet-listp prev))
            (equal (fn-scc-open-segment (fn-sccb-frame-octets frame fn-octets)
                                        index count sequence prev)
                   (let ((o (fn-sccr-open-frame frame index count sequence prev fn-octets)))
                     (and o (list (fn-oct-slice-list (nth 1 frame) (nth 2 frame) fn-octets)
                                  o)))))
   :hints (("Goal" :do-not-induct t
            :cases ((equal (nth 2 (fn-scc-parse-header (nth 0 frame)))
                           (- (nth 2 frame) (nth 1 frame))))
            :in-theory (e/d (fn-scc-open-segment fn-sccb-frame-octets fn-sccr-open-frame)
                            (fn-scc-parse-header fn-scc-seal fn-scc-le-value))))))

; What a plan says of its first frame, forward, so that the frame lemma
; fires under the induction without the recursive recognizer opening.
(local
 (defthm fn-sccr-planp-cons-facts
   (implies (and (fn-sccr-planp plan pos fn-octets) (consp plan))
            (and (fn-sccr-framep (car plan) fn-octets)
                 (true-listp (car plan))
                 (equal (nth 1 (car plan)) pos)
                 (fn-sccr-planp (cdr plan) (nth 2 (car plan)) fn-octets)))
   :rule-classes (:forward-chaining :rewrite)
   :hints (("Goal" :expand ((fn-sccr-planp plan pos fn-octets))
            :in-theory (enable fn-sccr-framep)))))

(local
 (defthm fn-sccr-planp-atom-facts
   (implies (and (fn-sccr-planp plan pos fn-octets) (not (consp plan)))
            (and (equal plan nil) (natp pos) (<= pos (len fn-octets))))
   :rule-classes :forward-chaining
   :hints (("Goal" :expand ((fn-sccr-planp plan pos fn-octets))))))

; A frame's facts, forward, for the same reason.
(local
 (defthm fn-sccr-framep-facts
   (implies (fn-sccr-framep frame fn-octets)
            (and (true-listp frame)
                 (fn-scc-octet-listp (nth 0 frame))
                 (equal (len (nth 0 frame)) *fn-scc-segment-header-octets*)
                 (natp (nth 1 frame)) (natp (nth 2 frame))
                 (<= (nth 1 frame) (nth 2 frame))
                 (<= (nth 2 frame) (len fn-octets))
                 (fn-scc-octet-listp (nth 3 frame))
                 (equal (len (nth 3 frame)) *fn-frame-trailer-octets*)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-sccr-framep)))))

; The chain's next PREV is the frame's trailer, an octet list.
(local
 (defthm fn-sccr-open-frame-octets
   (implies (fn-sccr-framep frame fn-octets)
            (fn-scc-octet-listp
             (fn-sccr-open-frame frame index count sequence prev fn-octets)))
   :hints (("Goal" :in-theory (e/d (fn-sccr-open-frame fn-sccr-framep)
                                   (fn-scc-parse-header fn-scc-seal))))))

; The list join's accumulator grows by each chunk reversed; the induction
; follows the plan with that accumulator.
(local
 (defun fn-sccr-join-ind (plan pos index count sequence prev racc fn-octets)
   (declare (xargs :stobjs fn-octets :verify-guards nil :measure (len plan)))
   (if (consp plan)
       (let ((o (fn-sccr-open-frame (car plan) index count sequence prev fn-octets)))
         (if o
             (fn-sccr-join-ind (cdr plan) (fn-sccr-at 2 (car plan)) (+ 1 index) count
                               sequence o
                               (revappend (fn-oct-slice-list (fn-sccr-at 1 (car plan))
                                                             (fn-sccr-at 2 (car plan))
                                                             fn-octets)
                                          racc)
                               fn-octets)
           (list pos racc)))
     (list pos racc))))

; The empty plan, as rewrites: the induction's base case sees `nil' where
; the expand hints name the plan.
(local
 (defthm fn-sccr-plan-segments-nil
   (equal (fn-sccr-plan-segments nil fn-octets) nil)
   :hints (("Goal" :in-theory (enable fn-sccr-plan-segments)))))

(local
 (defthm fn-sccr-join-nil
   (equal (fn-sccr-join nil pos index count sequence prev fn-octets)
          (if (equal index count) (list :ok pos) (list :refused :truncated)))
   :hints (("Goal" :in-theory (enable fn-sccr-join)))))

(local
 (defthm fn-sccr-join-is-join
   (implies (and (fn-octets-p fn-octets) (fn-sccr-planp plan pos fn-octets)
                 (fn-scc-octet-listp prev) (true-listp racc) (natp index))
            (equal (fn-scc-join (fn-sccr-plan-segments plan fn-octets)
                                index count sequence prev racc)
                   (let ((j (fn-sccr-join plan pos index count sequence prev fn-octets)))
                     (if (eq (car j) :ok)
                         (list :ok (revappend racc (fn-oct-slice-list pos (nth 1 j) fn-octets)))
                       j))))
   :hints (("Goal" :induct (fn-sccr-join-ind plan pos index count sequence prev racc
                                             fn-octets)
            :expand ((fn-sccr-plan-segments plan fn-octets)
                     (fn-sccr-join plan pos index count sequence prev fn-octets)
                     (:free (segs) (fn-scc-join segs index count sequence prev racc)))
            :in-theory (e/d ()
                            (fn-scc-join fn-sccr-join fn-sccr-plan-segments
                             fn-scc-open-segment fn-sccr-open-frame
                             fn-sccr-planp fn-sccb-frame-octets floor mod nth))))))

(local
 (defthm fn-sccr-genesis-octets
   (fn-scc-octet-listp *fn-scc-genesis*)))

; The first segment's header, parsed from the frame's octets, is the frame's
; header list parsed, with the chunk and the trailer behind it.
(local
 (defthm fn-sccr-parse-header-of-frame-octets
   (implies (and (fn-octets-p fn-octets) (fn-sccr-framep frame fn-octets))
            (equal (fn-scc-parse-header (fn-sccb-frame-octets frame fn-octets))
                   (and (fn-scc-parse-header (nth 0 frame))
                        (list (nth 0 (fn-scc-parse-header (nth 0 frame)))
                              (nth 1 (fn-scc-parse-header (nth 0 frame)))
                              (nth 2 (fn-scc-parse-header (nth 0 frame)))
                              (nth 3 (fn-scc-parse-header (nth 0 frame)))
                              (append (fn-oct-slice-list (nth 1 frame) (nth 2 frame)
                                                         fn-octets)
                                      (nth 3 frame))))))
   :hints (("Goal" :in-theory (e/d (fn-sccb-frame-octets) (fn-scc-parse-header))))))

; The twin.
(defthm fn-sccr-decode-plan-is-decode-segments
  (implies (and (fn-octets-p fn-octets)
                (fn-sccr-planp plan (if (consp plan) (fn-sccr-at 1 (car plan)) 0) fn-octets))
           (equal (fn-sccr-decode-plan plan fn-octets)
                  (fn-scc-decode-segments (fn-sccr-plan-segments plan fn-octets))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sccr-join-ok-end
                            (pos (fn-sccr-at 1 (car plan))) (index 0)
                            (count (nth 1 (fn-scc-parse-header (fn-sccr-at 0 (car plan)))))
                            (sequence (nth 3 (fn-scc-parse-header (fn-sccr-at 0 (car plan)))))
                            (prev *fn-scc-genesis*)))
           :in-theory (e/d (fn-scc-decode-segments fn-sccr-decode-plan
                            fn-sccr-plan-segments)
                           (fn-scc-join fn-sccr-join fn-scc-parse-header fn-scc-decode-tree
                            fn-sccr-join-ok-end fn-scc-value-sequence
                            fn-sccb-frame-octets)))))

; Where the shape fails, the reader refuses by name.
(defthm fn-sccr-decode-plan-refuses-layout-by-definition
  (implies (not (fn-sccr-planp plan (if (consp plan) (fn-sccr-at 1 (car plan)) 0) fn-octets))
           (equal (fn-sccr-decode-plan plan fn-octets) (list :refused :layout)))
  :hints (("Goal" :in-theory (enable fn-sccr-decode-plan))))

; -----------------------------------------------------------------------------
; The writer's plan is a reader's plan, and its frames' octets are the
; codec's segments.

(local
 (defthm fn-sccr-header-shape
   (and (fn-scc-octet-listp (fn-scc-header index count length sequence))
        (equal (len (fn-scc-header index count length sequence))
               *fn-scc-segment-header-octets*))
   :hints (("Goal" :in-theory (enable fn-scc-header)))))

(local
 (defthm fn-sccr-chunks-short
   (implies (or (zp seg) (<= (len p) seg))
            (equal (fn-scc-chunks p seg) (list p)))))

(local
 (defthm fn-sccr-chunks-long
   (implies (and (not (zp seg)) (< seg (len p)))
            (equal (fn-scc-chunks p seg)
                   (cons (take seg p) (fn-scc-chunks (nthcdr seg p) seg))))))

(local
 (defthm fn-sccr-planp-of-frames
   (implies (and (fn-octets-p fn-octets) (natp a) (<= a (len fn-octets))
                 (fn-scc-octet-listp prev))
            (fn-sccr-planp (fn-sccb-frames a index count sequence prev seg fn-octets)
                           a fn-octets))
   :hints (("Goal" :induct (fn-sccb-frames a index count sequence prev seg fn-octets)
            :in-theory (e/d (fn-sccb-frames fn-octets-len)
                            (fn-scc-header fn-scc-seal fn-scc-u64 floor mod
                             fn-oct-slice-list))))))

(local
 (defthm fn-sccr-plan-segments-of-frames
   (implies (and (fn-octets-p fn-octets) (natp a) (<= a (len fn-octets))
                 (fn-scc-octet-listp prev))
            (equal (fn-sccr-plan-segments
                    (fn-sccb-frames a index count sequence prev seg fn-octets)
                    fn-octets)
                   (fn-scc-frames (fn-scc-chunks (nthcdr a fn-octets) seg)
                                  index count sequence prev)))
   :hints (("Goal" :induct (fn-sccb-frames a index count sequence prev seg fn-octets)
            :in-theory (e/d (fn-sccb-frames fn-oct-slice-list-is-take-nthcdr)
                            (fn-scc-header fn-scc-seal fn-scc-u64 floor mod
                             fn-scc-chunks))))))

(local
 (defthm fn-sccr-value-sequence-natp
   (natp (fn-scc-value-sequence c))
   :rule-classes :type-prescription))

; The program of an encodable value is an octet buffer value.
(local
 (defthm fn-sccr-octets-p-of-program
   (implies (fn-sccb-treep c)
            (fn-octets-p (fn-scc-program c)))
   :hints (("Goal" :use fn-sccb-treep-encodes-octets
            :in-theory (e/d (fn-oct-octets-p-is-octet-listp)
                            (fn-scc-program fn-sccb-treep fn-sccb-treep-encodes-octets))))))

; The frames from A are nonempty and begin at A.
(local
 (defthm fn-sccr-frames-first
   (and (consp (fn-sccb-frames a index count sequence prev seg fn-octets))
        (equal (fn-sccr-at 1 (car (fn-sccb-frames a index count sequence prev seg fn-octets)))
               a))
   :hints (("Goal" :expand ((fn-sccb-frames a index count sequence prev seg fn-octets))
            :in-theory (disable fn-scc-header fn-scc-seal fn-oct-slice-list)))))

; The writer's plan, as the reader takes it: contiguous from 0 over the
; encoding, and its frames' octets are `fn-scc-segments'.
(defthm fn-sccr-writer-plan-is-a-plan
  (implies (fn-sccb-treep c)
           (and (fn-sccr-planp (mv-nth 0 (fn-sccb-plan c seg fn-octets)) 0
                               (mv-nth 1 (fn-sccb-plan c seg fn-octets)))
                (equal (fn-sccr-plan-segments (mv-nth 0 (fn-sccb-plan c seg fn-octets))
                                              (mv-nth 1 (fn-sccb-plan c seg fn-octets)))
                       (fn-scc-segments c seg))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-sccb-plan fn-scc-segments)
                           (fn-sccb-frames fn-scc-frames fn-scc-chunks fn-scc-program
                            fn-scc-treep fn-sccb-treep fn-scc-value-sequence
                            fn-sccb-chunk-count fn-scc-encode fn-sccb-renc)))))

(local
 (defthm fn-sccr-writer-plan-first
   (implies (fn-sccb-treep c)
            (and (consp (mv-nth 0 (fn-sccb-plan c seg fn-octets)))
                 (equal (fn-sccr-at 1 (car (mv-nth 0 (fn-sccb-plan c seg fn-octets)))) 0)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-sccb-plan)
                            (fn-sccb-frames fn-scc-frames fn-scc-chunks fn-scc-program
                             fn-scc-header fn-scc-seal fn-scc-treep fn-sccb-treep
                             fn-scc-value-sequence fn-sccb-chunk-count fn-sccb-renc
                             fn-oct-slice-list))))))

; KEYSTONE (PRF-135): the buffer decode of the writer's plan, over the
; buffer the writer leaves, is the value.  The two width hypotheses are the
; codec's u64 header fields (fn-scc-decode-segments-of-segments).
(defthm fn-sccr-decode-of-plan
  (implies (and (fn-sccb-treep c)
                (< (+ 1 (len (fn-scc-encode c))) *fn-scc-u64-bound*)
                (< (fn-scc-value-sequence c) *fn-scc-u64-bound*))
           (equal (fn-sccr-decode-plan (mv-nth 0 (fn-sccb-plan c seg fn-octets))
                                       (mv-nth 1 (fn-sccb-plan c seg fn-octets)))
                  (list :ok c)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sccr-decode-plan-is-decode-segments
                            (plan (mv-nth 0 (fn-sccb-plan c seg fn-octets)))
                            (fn-octets (mv-nth 1 (fn-sccb-plan c seg fn-octets))))
                 (:instance fn-sccr-writer-plan-is-a-plan)
                 (:instance fn-sccr-writer-plan-first)
                 (:instance fn-sccb-plan-buffer-is-encode)
                 (:instance fn-sccr-octets-p-of-program)
                 (:instance fn-scc-decode-segments-of-segments (segment-octets seg)))
           :in-theory (e/d ()
                           (fn-sccr-decode-plan-is-decode-segments fn-sccr-writer-plan-is-a-plan
                            fn-sccr-writer-plan-first
                            fn-scc-decode-segments-of-segments fn-sccb-plan fn-sccr-decode-plan
                            fn-sccr-planp fn-sccr-plan-segments fn-scc-decode-segments
                            fn-scc-segments fn-scc-program fn-sccb-treep fn-scc-value-sequence
                            fn-sccb-plan-buffer-is-encode fn-sccb-plan-is-file-octets)))))

; -----------------------------------------------------------------------------
; The admission of one segment before it is read: the host holds the
; header (37 octets) and the running total of the file so far; ACL2 says
; whether the segment is read.  SEGMENT-BOUND is the profile's
; `fn-store-sco-segment-read-bound', FILE-BOUND `fn-store-sco-file-read-bound'
; (host/store-node-host.lisp), both decided here.

; The file bound: three times the profile's history bound (the checkpoint
; value carries the history's records twice, in the replayed store and in
; the event index, and the derived tables beside them), plus one segment's
; framing.  The reader then holds at most this many octets in the buffer
; and the value decoded from them; a file past it is refused by name and
; the journal replays, which is slower, never wrong.
(defun fn-sccr-file-read-bound (max-history-octets max-record-octets)
  (declare (xargs :guard t))
  (+ (* 3 (nfix max-history-octets))
     (fn-scc-segment-max-octets (nfix max-record-octets))))

(defun fn-sccr-admit-segment (header total segment-bound file-bound)
  ; (:ok EXTENT CHUNK-OCTETS), (:refused :header) or (:refused :exceeds-bound).
  (declare (xargs :guard t))
  (let ((h (and (fn-scc-octet-listp header) (fn-scc-parse-header header))))
    (if (not h)
        (list :refused :header)
      (let* ((chunk (nth 2 h))
             (extent (+ *fn-scc-segment-header-octets* chunk *fn-frame-trailer-octets*)))
        (if (and (natp segment-bound) (<= extent segment-bound)
                 (natp total) (natp file-bound) (<= (+ total extent) file-bound))
            (list :ok extent chunk)
          (list :refused :exceeds-bound))))))

(defthm fn-sccr-admitted-within-bounds
  (implies (equal (car (fn-sccr-admit-segment header total segment-bound file-bound)) :ok)
           (let ((extent (nth 1 (fn-sccr-admit-segment header total segment-bound file-bound))))
             (and (natp extent)
                  (equal extent (fn-scc-segment-extent header))
                  (<= extent segment-bound)
                  (<= (+ total extent) file-bound))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scc-parse-header-facts (seg header)))
           :in-theory (e/d (fn-scc-segment-extent)
                           (fn-scc-parse-header fn-scc-parse-header-facts floor mod)))))

(in-theory (disable fn-sccr-framep fn-sccr-planp fn-sccr-plan-segments
                    fn-sccr-open-frame fn-sccr-join fn-sccr-decode-plan
                    fn-sccr-admit-segment fn-sccr-file-read-bound))
