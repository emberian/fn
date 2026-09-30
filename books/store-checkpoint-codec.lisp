; fn: the byte encoding of a Store checkpoint (P3; magic FNSC; schema 3 since
; lane checkpoint-pipeline, 2026-09-26: the file is four TABLES, each a run
; of these segments, books/store-checkpoint-tables.lisp; schema 2 (one
; postfix program over the whole checkpoint value) is refused by name at the
; open, D34).
;
; A checkpoint value (books/store-checkpoint-open.lisp) is an ACL2 tree: the
; record list and each replay fold's accumulator.  The existing TREE codec
; (checkpoint-codec.lisp) admits naturals below 2^32 and four symbols, which
; the Store state exceeds, so this book gives a second tree codec:
;
;   * a postfix program for a stack machine.  An atom is one instruction
;     that pushes it; a cons is its car's program, its cdr's program, then
;     CONS.  A list of n elements is therefore its elements' programs and n
;     CONS octets.  The decoder is a tail-recursive loop with an explicit
;     value stack, so its depth does not grow with the data; the encoder
;     recurses on car only and loops along each list spine.
;   * atoms: NIL, naturals (a length octet L then L little-endian octets, so
;     below 2^2040), negative integers, characters, strings, symbols of the
;     KEYWORD, ACL2 and COMMON-LISP packages (by name, never through the
;     reader), and non-empty octet lists as one instruction.
;
; The payload is then cut into segments of at most SEG octets, each an
; FN-style frame: header (magic, schema, index, count, length, sequence), the
; chunk, and a trailer `fn-frame-trailer' over the previous trailer, the
; header and the chunk.  The host reads the file one segment at a time
; (books/byte-store-range-read.lisp), and each segment is one bounded read.
; `fn-scc-decode-segments' refuses reorder (index), truncation (count),
; splice (sequence and the trailer chain) and a corrupt octet (trailer).
(in-package "ACL2")
(include-book "store-tree-codec")
(include-book "frame-trailer")
(local (include-book "arithmetic/top" :dir :system))
(local
 (defthm fn-scc-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn-scc-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

;; The list lemmas the tree codec (books/store-tree-codec.lisp) proves
;; locally; the segments below were proved with them in one book.
(local
 (defthm fn-scc-long-enoughp-is-len
   (implies (natp n)
            (equal (fn-scc-long-enoughp n xs) (<= n (len xs))))))

(local
 (defthm fn-scc-take-of-append-len
   (implies (and (true-listp a) (equal n (len a)))
            (equal (take n (append a b)) a))))

(local
 (defthm fn-scc-nthcdr-of-append-len
   (implies (equal n (len a))
            (equal (nthcdr n (append a b)) b))))

(local
 (defthm fn-scc-len-nthcdr
   (implies (and (natp n) (<= n (len xs)))
            (equal (len (nthcdr n xs)) (- (len xs) n)))))

(local
 (defthm fn-scc-revappend-of-append
   (equal (revappend (append a b) r) (revappend b (revappend a r)))))

(local
 (defthm fn-scc-revappend-revappend-gen
   (equal (revappend (revappend a b) c) (revappend b (append a c)))))

(local
 (defthm fn-scc-append-nil-true-list
   (implies (true-listp a) (equal (append a nil) a))))

(local
 (defthm fn-scc-revappend-revappend
   (implies (true-listp a)
            (equal (revappend (revappend a nil) nil) a))
   :hints (("Goal" :use ((:instance fn-scc-revappend-revappend-gen (b nil) (c nil)))
            :in-theory (disable fn-scc-revappend-revappend-gen)))))

(local
 (defthm fn-scc-le-value-of-u64
   (implies (and (natp n) (natp k) (< n (expt 256 k)))
            (equal (fn-scc-le-value (fn-scc-u64 n k)) n))
   :hints (("Goal" :induct (fn-scc-u64 n k)))))

; -----------------------------------------------------------------------------
; Segments

(defconst *fn-scc-u64-bound* 18446744073709551616)
(defconst *fn-scc-genesis* '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))

(defun fn-scc-header (index count length sequence)
  (declare (xargs :guard (and (natp index) (natp count) (natp length)
                              (natp sequence))))
  (append *fn-scc-magic*
          (list *fn-scc-schema*)
          (fn-scc-u64 index 8) (fn-scc-u64 count 8)
          (fn-scc-u64 length 8) (fn-scc-u64 sequence 8)))

(defun fn-scc-seal (prev header chunk)
  (declare (xargs :guard t))
  (fn-frame-trailer (append (true-list-fix prev) (true-list-fix header) chunk)))

; The chunks of a payload, each at most SEG octets (one chunk when SEG is 0).
(defun fn-scc-chunks (payload seg)
  (declare (xargs :guard (and (true-listp payload) (natp seg)) :measure (len payload)))
  (if (or (zp seg) (not (fn-scc-long-enoughp (+ 1 seg) payload)))
      (list payload)
    (cons (take seg payload) (fn-scc-chunks (nthcdr seg payload) seg))))

(defun fn-scc-frames (chunks index count sequence prev)
  (declare (xargs :guard (and (true-list-listp chunks)
                              (natp index) (natp count) (natp sequence))
                  :verify-guards nil))
  (if (consp chunks)
      (let* ((chunk (car chunks))
             (header (fn-scc-header index count (len chunk) sequence))
             (trailer (fn-scc-seal prev header chunk)))
        (cons (append header chunk trailer)
              (fn-scc-frames (cdr chunks) (+ 1 index) count sequence trailer)))
    nil))

(defun fn-scc-concat (segments)
  (declare (xargs :guard t))
  (if (consp segments)
      (append (true-list-fix (car segments)) (fn-scc-concat (cdr segments)))
    nil))

; The record count a checkpoint value covers: its second element, which is
; the count itself when the file carries the count instead of the record
; list (fn-sco-freeze, books/store-checkpoint-open.lisp), else the list's
; length.
(defun fn-scc-value-sequence (c)
  (declare (xargs :guard t))
  (let ((slot (and (consp c) (consp (cdr c)) (cadr c))))
    (if (natp slot) slot (len slot))))

(defun fn-scc-segments (c segment-octets)
  (declare (xargs :guard (natp segment-octets) :verify-guards nil))
  (if (not (fn-scc-treep c))
      :unencodable
    (let ((chunks (fn-scc-chunks (fn-scc-encode c) segment-octets)))
      (fn-scc-frames chunks 0 (len chunks) (fn-scc-value-sequence c)
                     *fn-scc-genesis*))))

; What the host writes through fn-bs-scp-program.
(defun fn-scc-file-octets (c segment-octets)
  (declare (xargs :guard (natp segment-octets) :verify-guards nil))
  (let ((segments (fn-scc-segments c segment-octets)))
    (if (eq segments :unencodable) :unencodable (fn-scc-concat segments))))

(defun fn-scc-segment-max-octets (segment-octets)
  (declare (xargs :guard (natp segment-octets)))
  (+ *fn-scc-segment-header-octets* segment-octets *fn-frame-trailer-octets*))

; -----------------------------------------------------------------------------
; Reading a segment

(defun fn-scc-u64-at (xs)
  (declare (xargs :guard (fn-scc-octet-listp xs) :verify-guards nil))
  (fn-scc-le-value (take 8 xs)))

(defun fn-scc-parse-header (seg)
  ; (list index count length sequence rest) or nil; rest follows the header.
  (declare (xargs :guard (fn-scc-octet-listp seg) :verify-guards nil))
  (if (and (fn-scc-long-enoughp *fn-scc-segment-header-octets* seg)
           (equal (take 4 seg) *fn-scc-magic*)
           (equal (nth 4 seg) *fn-scc-schema*))
      (let* ((r1 (nthcdr 5 seg)) (r2 (nthcdr 8 r1)) (r3 (nthcdr 8 r2))
             (r4 (nthcdr 8 r3)))
        (list (fn-scc-u64-at r1) (fn-scc-u64-at r2) (fn-scc-u64-at r3)
              (fn-scc-u64-at r4) (nthcdr 8 r4)))
    nil))

; The host reads a header of *fn-scc-segment-header-octets*, asks this for
; the whole segment's length, and reads the rest.
(defun fn-scc-segment-extent (header)
  (declare (xargs :guard (fn-scc-octet-listp header) :verify-guards nil))
  (let ((h (fn-scc-parse-header header)))
    (and h (+ *fn-scc-segment-header-octets* (nth 2 h) *fn-frame-trailer-octets*))))

; (list chunk trailer) when SEG is one well-formed segment at INDEX of COUNT
; with SEQUENCE, chained to PREV; otherwise nil.
(defun fn-scc-open-segment (seg index count sequence prev)
  (declare (xargs :guard (and (fn-scc-octet-listp seg) (true-listp prev))
                  :verify-guards nil))
  (let ((h (fn-scc-parse-header seg)))
    (and h
         (equal (nth 0 h) index)
         (equal (nth 1 h) count)
         (equal (nth 3 h) sequence)
         (let* ((body (nth 4 h))
                (chunk (take (nth 2 h) body))
                (trailer (nthcdr (nth 2 h) body)))
           (and (fn-scc-long-enoughp (nth 2 h) body)
                (equal trailer
                       (fn-scc-seal prev (take *fn-scc-segment-header-octets* seg)
                                    chunk))
                (list chunk trailer))))))

(defun fn-scc-segment-listp (segs)
  (declare (xargs :guard t))
  (if (consp segs)
      (and (fn-scc-octet-listp (car segs)) (fn-scc-segment-listp (cdr segs)))
    (null segs)))

(defun fn-scc-join (segs index count sequence prev racc)
  (declare (xargs :guard (and (fn-scc-segment-listp segs) (true-listp prev)
                              (true-listp racc))
                  :verify-guards nil))
  (if (consp segs)
      (let ((o (fn-scc-open-segment (car segs) index count sequence prev)))
        (if o
            (fn-scc-join (cdr segs) (+ 1 (nfix index)) count sequence (cadr o)
                         (revappend (car o) racc))
          (list :refused :segment)))
    (if (and (equal index count) (null segs))
        (list :ok (revappend racc nil))
      (list :refused :truncated))))

(defun fn-scc-decode-segments (segs)
  (declare (xargs :guard (fn-scc-segment-listp segs) :verify-guards nil))
  (let ((h (and (consp segs) (fn-scc-parse-header (car segs)))))
    (if (not h)
        (list :refused :header)
      (let ((payload (fn-scc-join segs 0 (nth 1 h) (nth 3 h) *fn-scc-genesis* nil)))
        (if (not (eq (car payload) :ok))
            payload
          (let ((tree (fn-scc-decode-tree (nth 1 payload))))
            (if (and (eq (car tree) :ok)
                     (equal (fn-scc-value-sequence (nth 1 tree)) (nth 3 h)))
                tree
              (list :refused :value))))))))

; -----------------------------------------------------------------------------
; The segment round trip

(local
 (defthm fn-scc-u64-true-listp
   (true-listp (fn-scc-u64 n k))))

(local
 (defthm fn-scc-header-shape
   (and (true-listp (fn-scc-header i n l q))
        (equal (len (fn-scc-header i n l q)) 37))))

(local
 (defthm fn-scc-long-enoughp-append
   (implies (and (natp k) (<= k (len a)))
            (fn-scc-long-enoughp k (append a b)))))

(local
 (defthm fn-scc-take-of-append-short
   (implies (and (true-listp a) (natp k) (<= k (len a)))
            (equal (take k (append a b)) (take k a)))))

(local
 (defthm fn-scc-take-all
   (implies (and (true-listp x) (equal k (len x)))
            (equal (take k x) x))))

(local
 (defthm fn-scc-u64-read
   (implies (and (natp n) (< n *fn-scc-u64-bound*))
            (equal (fn-scc-u64-at (append (fn-scc-u64 n 8) rest)) n))
   :hints (("Goal" :in-theory (disable fn-scc-u64)))))

(local
 (defthm fn-scc-parse-header-of-segment
   (implies (and (natp i) (< i *fn-scc-u64-bound*)
                 (natp n) (< n *fn-scc-u64-bound*)
                 (natp l) (< l *fn-scc-u64-bound*)
                 (natp q) (< q *fn-scc-u64-bound*))
            (equal (fn-scc-parse-header (append (fn-scc-header i n l q) rest))
                   (list i n l q rest)))
   :hints (("Goal" :in-theory (e/d (fn-scc-header) (fn-scc-u64 fn-scc-u64-at))))))

(local
 (defthm fn-scc-open-segment-of-frame
   (implies (and (natp i) (< i *fn-scc-u64-bound*)
                 (natp n) (< n *fn-scc-u64-bound*)
                 (true-listp chunk) (< (len chunk) *fn-scc-u64-bound*)
                 (natp q) (< q *fn-scc-u64-bound*))
            (equal (fn-scc-open-segment
                    (append (fn-scc-header i n (len chunk) q)
                            (append chunk
                                    (fn-scc-seal prev (fn-scc-header i n (len chunk) q)
                                                 chunk)))
                    i n q prev)
                   (list chunk (fn-scc-seal prev (fn-scc-header i n (len chunk) q)
                                            chunk))))
   :hints (("Goal" :in-theory (e/d () (fn-scc-header fn-scc-seal fn-scc-parse-header))))))

(defun fn-scc-chunk-listp (chunks)
  (declare (xargs :guard t))
  (if (consp chunks)
      (and (true-listp (car chunks))
           (< (len (car chunks)) *fn-scc-u64-bound*)
           (fn-scc-chunk-listp (cdr chunks)))
    t))

(local
 (defun fn-scc-join-ind (chunks i n q prev racc)
   (declare (xargs :verify-guards nil))
   (if (consp chunks)
       (let* ((h (fn-scc-header i n (len (car chunks)) q))
              (tr (fn-scc-seal prev h (car chunks))))
         (fn-scc-join-ind (cdr chunks) (+ 1 i) n q tr
                          (revappend (car chunks) racc)))
     (list i n q prev racc))))

(local
 (defthm fn-scc-true-list-fix-id
   (implies (true-listp x) (equal (true-list-fix x) x))))

(local
 (defthm fn-scc-join-of-frames
   (implies (and (fn-scc-chunk-listp chunks)
                 (natp i) (natp n) (<= (+ i (len chunks)) n)
                 (< n *fn-scc-u64-bound*)
                 (natp q) (< q *fn-scc-u64-bound*))
            (equal (fn-scc-join (fn-scc-frames chunks i n q prev) i n q prev racc)
                   (if (equal (+ i (len chunks)) n)
                       (list :ok (revappend (revappend (fn-scc-concat chunks) racc) nil))
                     (list :refused :truncated))))
   :hints (("Goal" :induct (fn-scc-join-ind chunks i n q prev racc)
            :in-theory (e/d () (fn-scc-header fn-scc-seal fn-scc-open-segment))))))

(local
 (defthm fn-scc-append-take-nthcdr
   (implies (and (natp k) (<= k (len x)))
            (equal (append (take k x) (nthcdr k x)) x))))

(local
 (defthm fn-scc-concat-of-chunks
   (implies (true-listp payload)
            (equal (fn-scc-concat (fn-scc-chunks payload seg)) payload))))

(local
 (defthm fn-scc-len-take
   (equal (len (take k x)) (nfix k))))

(defthm fn-scc-chunks-shape
  (implies (and (true-listp payload) (< (len payload) *fn-scc-u64-bound*))
           (and (fn-scc-chunk-listp (fn-scc-chunks payload seg))
                (<= (len (fn-scc-chunks payload seg)) (+ 1 (len payload)))
                (consp (fn-scc-chunks payload seg)))))

(local
 (defthm fn-scc-concat-true-listp
   (true-listp (fn-scc-concat x))))

(defthm fn-scc-join-of-chunks
  (implies (and (true-listp p) (< (+ 1 (len p)) *fn-scc-u64-bound*)
                (natp q) (< q *fn-scc-u64-bound*))
           (equal (fn-scc-join (fn-scc-frames (fn-scc-chunks p seg) 0
                                              (len (fn-scc-chunks p seg)) q prev)
                               0 (len (fn-scc-chunks p seg)) q prev nil)
                  (list :ok p)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scc-chunks-shape (payload p))
                 (:instance fn-scc-join-of-frames (chunks (fn-scc-chunks p seg))
                            (i 0) (n (len (fn-scc-chunks p seg))) (racc nil)))
           :in-theory (e/d () (fn-scc-chunks-shape fn-scc-join-of-frames
                               fn-scc-chunks fn-scc-frames fn-scc-join)))))

(defthm fn-scc-parse-header-of-first-frame
  (implies (and (consp chunks) (fn-scc-chunk-listp chunks)
                (natp n) (< n *fn-scc-u64-bound*)
                (natp q) (< q *fn-scc-u64-bound*))
           (equal (nth 1 (fn-scc-parse-header (car (fn-scc-frames chunks 0 n q prev))))
                  n))
  :hints (("Goal" :expand ((fn-scc-frames chunks 0 n q prev))
           :in-theory (e/d () (fn-scc-header fn-scc-seal)))))

(defthm fn-scc-parse-header-of-first-frame-sequence
  (implies (and (consp chunks) (fn-scc-chunk-listp chunks)
                (natp n) (< n *fn-scc-u64-bound*)
                (natp q) (< q *fn-scc-u64-bound*))
           (and (fn-scc-parse-header (car (fn-scc-frames chunks 0 n q prev)))
                (equal (nth 3 (fn-scc-parse-header
                               (car (fn-scc-frames chunks 0 n q prev))))
                       q)))
  :hints (("Goal" :expand ((fn-scc-frames chunks 0 n q prev))
           :in-theory (e/d () (fn-scc-header fn-scc-seal)))))

(defthm fn-scc-frames-consp
  (equal (consp (fn-scc-frames chunks i n q prev)) (consp chunks)))

(local
 (defthm fn-scc-decode-tree-of-program
   (implies (fn-scc-treep x)
            (equal (fn-scc-decode-tree (fn-scc-program x)) (list :ok x)))
   :hints (("Goal" :use fn-scc-decode-tree-of-encode
            :in-theory (disable fn-scc-decode-tree-of-encode fn-scc-decode-tree)))))

; The codec round trip: the segments the writer produces decode to the value.
; The two width hypotheses are the u64 header fields' codec width.
(defthm fn-scc-decode-segments-of-segments
  (implies (and (fn-scc-treep c)
                (< (+ 1 (len (fn-scc-encode c))) *fn-scc-u64-bound*)
                (< (fn-scc-value-sequence c) *fn-scc-u64-bound*))
           (equal (fn-scc-decode-segments (fn-scc-segments c segment-octets))
                  (list :ok c)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scc-chunks-shape (payload (fn-scc-program c))
                            (seg segment-octets)))
           :in-theory (e/d (fn-scc-decode-segments fn-scc-segments)
                           (fn-scc-chunks-shape fn-scc-program
                            fn-scc-header fn-scc-seal fn-scc-chunks fn-scc-frames
                            fn-scc-decode-tree fn-scc-join fn-scc-treep
                            fn-scc-parse-header fn-scc-value-sequence)))))

; -----------------------------------------------------------------------------
; Guards: the host runs the encoder and the decoder compiled.

(defthm fn-scc-octet-listp-true
  (implies (fn-scc-octet-listp x) (true-listp x)))

(defthm fn-scc-parse-header-facts
  (implies (and (fn-scc-octet-listp seg) (fn-scc-parse-header seg))
           (and (natp (nth 2 (fn-scc-parse-header seg)))
                (fn-scc-octet-listp (nth 4 (fn-scc-parse-header seg)))))
  :hints (("Goal" :in-theory (enable fn-scc-parse-header fn-scc-u64-at))))

(defthm fn-scc-open-segment-facts
  (implies (and (fn-scc-octet-listp seg)
                (fn-scc-open-segment seg index count sequence prev))
           (and (true-listp (car (fn-scc-open-segment seg index count sequence prev)))
                (true-listp (cadr (fn-scc-open-segment seg index count sequence prev)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scc-parse-header-facts)
                 (:instance fn-scc-octet-listp-true
                            (x (nthcdr (nth 2 (fn-scc-parse-header seg))
                                       (nth 4 (fn-scc-parse-header seg))))))
           :in-theory (e/d (fn-scc-open-segment)
                           (fn-scc-parse-header fn-scc-seal fn-scc-parse-header-facts
                            fn-scc-octet-listp-true)))))

(defthm fn-scc-open-segment-chunk-octets
  (implies (and (fn-scc-octet-listp seg)
                (fn-scc-open-segment seg index count sequence prev))
           (fn-scc-octet-listp (car (fn-scc-open-segment seg index count sequence prev))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scc-parse-header-facts))
           :in-theory (e/d (fn-scc-open-segment)
                           (fn-scc-parse-header fn-scc-seal fn-scc-parse-header-facts)))))

(defthm fn-scc-revappend-octets
  (implies (and (fn-scc-octet-listp a) (fn-scc-octet-listp b))
           (fn-scc-octet-listp (revappend a b))))

(defthm fn-scc-join-octets
  (implies (and (fn-scc-segment-listp segs) (fn-scc-octet-listp racc)
                (equal (car (fn-scc-join segs index count sequence prev racc)) :ok))
           (fn-scc-octet-listp (nth 1 (fn-scc-join segs index count sequence prev racc))))
  :hints (("Goal" :induct (fn-scc-join segs index count sequence prev racc)
           :in-theory
           (union-theories
            '(fn-scc-join fn-scc-segment-listp fn-scc-octet-listp
              fn-scc-octetp fn-scc-octet-listp-facts
              fn-scc-open-segment-chunk-octets fn-scc-revappend-octets
              car-cons nth-0-cons nth-add1)
            (theory 'minimal-theory)))))

(verify-guards fn-scc-u64-at)
(verify-guards fn-scc-parse-header)
(verify-guards fn-scc-segment-extent)
(verify-guards fn-scc-open-segment
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scc-parse-header-facts))
           :in-theory (disable fn-scc-parse-header fn-scc-parse-header-facts))))
(verify-guards fn-scc-join
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scc-open-segment-facts (seg (car segs))))
           :in-theory (disable fn-scc-open-segment fn-scc-open-segment-facts))))
(verify-guards fn-scc-run)
(verify-guards fn-scc-decode-tree)
(verify-guards fn-scc-decode-segments
  :hints (("Goal" :in-theory (disable fn-scc-parse-header fn-scc-join fn-scc-decode-tree))))
(verify-guards fn-scc-program)
(verify-guards fn-scc-renc)
(verify-guards fn-scc-encode)
(defthm fn-scc-chunks-true-list-listp
  (implies (true-listp payload)
           (true-list-listp (fn-scc-chunks payload seg))))
(verify-guards fn-scc-frames)
(verify-guards fn-scc-segments)
(verify-guards fn-scc-file-octets)

;; Withdrawn from includers (lane rule-hygiene, tools/rule_cost.py).
;; Each is tried in includers' proofs and pays for its frames in
;; almost none (planning/evidence/rule-cost-*.json has the counts;
;; docs/proof-style.md section 8).  An includer that needs one
;; enables it where it is used.
(in-theory (disable (:definition fn-scc-atom-octets)
                    (:definition fn-scc-atomp)
                    (:definition fn-scc-frames)
                    (:definition fn-scc-nat-encodablep)
                    (:definition fn-scc-nat-octets)
                    (:definition fn-scc-octet-listp)
                    (:definition fn-scc-program)
                    (:definition fn-scc-seal)
                    (:definition fn-scc-step)
                    (:definition fn-scc-string-octets)
                    (:definition fn-scc-treep)
                    (:rewrite fn-scc-octet-listp-facts . 1)
                    (:rewrite fn-scc-octet-listp-facts . 2)
                    (:rewrite fn-scc-octet-listp-true)))
