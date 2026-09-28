; fn: a canonical digest of an ACL2 value, for replay determinism
; (lane proto-determinism, 2026-09-27).
;
; The record log is the truth and the owner's state is a fold over it.  If
; the fold is deterministic, the state after a log prefix is a function of
; that prefix, and anyone holding the log (a peer catching up, a bisect for
; the event that broke an invariant, a bug report replayed) can check a
; snapshot by recomputing it.  This book gives the comparison a precise
; subject: `fn-sdg-canon' writes any ACL2 object as octets, injectively and
; independently of how the object happens to be laid out in memory (sharing,
; addresses, hash-table order play no part: only the object's value), and
; `fn-sdg-digest' is the store's digest (`fn-digest', books/crypto-seam.lisp:
; SHA-256 under books/crypto-attach.lisp until lane blake3-digest's
; attachment makes it BLAKE3; format 10, lane format-bump-10) of that.  It is a comparison tool, not a codec:
; nothing reads these octets back, and no format depends on them.
;
; The encoding (every octet is a tag or a field of the atom it follows):
;   a cons chain  76 ('L'), each element in turn, 69 ('E'), the chain's
;                 terminating atom (NIL for a true list);
;   an integer    73 ('I'), 0 or 1 (the sign), LEB128 of its magnitude;
;   a ratio       81 ('Q'), numerator, denominator (each as an integer);
;   a complex     90 ('Z'), real part, imaginary part (each as a rational);
;   a character   67 ('C'), its code;
;   a string      83 ('S'), LEB128 of its length, its codes;
;   a symbol      89 ('Y'), its package name, its name (each as a string).
; A cons chain is walked along its cdrs iteratively, so a long list costs
; no stack depth; only nesting through cars recurses.
;
; `fn-sdg-arena-pool' digests the payload arena's LOGICAL value (the list of
; sealed payloads, books/payload-arena.lisp), a payload at a time, so an
; extent handle (a payload held in a log segment) and a heap handle with the
; same octets digest alike.  `fn-sdg-rows-history' digests a history's rows as
; their wire events (books/store-intern.lisp fn-row-wire-of: the payload
; read through the arena), a record at a time: the history in log order,
; independent of which handle holds which payload.

(in-package "ACL2")
(include-book "crypto-seam")
(include-book "store-intern")

(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "tools/flag" :dir :system))
(local (include-book "std/lists/revappend" :dir :system))
(local (include-book "std/lists/append" :dir :system))

;; revappend without its guard: the digest reads any object.
(defun fn-sdg-rev (x acc)
  (declare (xargs :guard t))
  (if (consp x) (fn-sdg-rev (cdr x) (cons (car x) acc)) acc))

(defun fn-sdg-leb (n acc)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (or (zp n) (< n 128))
      (cons (nfix n) acc)
    (fn-sdg-leb (floor n 128) (cons (+ 128 (mod n 128)) acc))))

(defun fn-sdg-string (s i n acc)
  (declare (xargs :guard (and (stringp s) (natp i) (natp n) (<= n (length s)))
                  :measure (nfix (- (nfix n) (nfix i)))))
  (if (or (not (natp i)) (not (natp n)) (>= i n))
      acc
    (fn-sdg-string s (1+ i) n (cons (char-code (char s i)) acc))))

(defun fn-sdg-str (s acc)
  (declare (xargs :guard (stringp s)))
  (fn-sdg-string s 0 (length s) (fn-sdg-leb (length s) (cons 83 acc))))

(defun fn-sdg-int (x acc)
  (declare (xargs :guard (integerp x)))
  (if (< x 0)
      (fn-sdg-leb (- x) (list* 1 73 acc))
    (fn-sdg-leb x (list* 0 73 acc))))

(defun fn-sdg-rat (x acc)
  (declare (xargs :guard (rationalp x)))
  (if (integerp x)
      (fn-sdg-int x acc)
    (fn-sdg-int (denominator x) (fn-sdg-int (numerator x) (cons 81 acc)))))

(defun fn-sdg-atom (x acc)
  (declare (xargs :guard t))
  (cond ((rationalp x) (fn-sdg-rat x acc))
        ((complex-rationalp x)
         (fn-sdg-rat (imagpart x) (fn-sdg-rat (realpart x) (cons 90 acc))))
        ((characterp x) (list* (char-code x) 67 acc))
        ((stringp x) (fn-sdg-str x acc))
        ((symbolp x)
         (fn-sdg-str (symbol-name x) (fn-sdg-str (symbol-package-name x) (cons 89 acc))))
        ; ACL2 has no other atoms; a raw-Lisp object cannot reach a logic
        ; value.
        (t (cons 63 acc))))

(mutual-recursion
 (defun fn-sdg-canon-rev (x acc)
   (declare (xargs :guard t :measure (+ 1 (* 2 (acl2-count x)))))
   (if (consp x)
       (fn-sdg-canon-list x (cons 76 acc))
     (fn-sdg-atom x acc)))
 (defun fn-sdg-canon-list (x acc)
   (declare (xargs :guard t :measure (* 2 (acl2-count x))))
   (if (consp x)
       (fn-sdg-canon-list (cdr x) (fn-sdg-canon-rev (car x) acc))
     (fn-sdg-atom x (cons 69 acc)))))

(defun fn-sdg-canon (x)
  (declare (xargs :guard t))
  (fn-sdg-rev (fn-sdg-canon-rev x nil) nil))

;; ---------------------------------------------------------------------------
;; The digest of a canonical octet stream, in blocks (lane format10-import,
;; 2026-09-28).  `fn-digest' takes its whole preimage as one list, so the
;; digest of a whole field of a 1,000,000-record store materialized its
;; canonical octets first (three list cells per octet with the reversal):
;; `store digest' exhausted a 32 GB heap on the format-10 syn1m-2k.  The
;; digest is now the CHAIN of the stream in blocks of *fn-sdg-block-octets*:
;; a stream of at most one block digests as before (`fn-digest' of its
;; octets, `fn-sdg-chain-of-one-block'); a longer one digests each full
;; block into a running digest, the first as `fn-digest' of its octets and
;; each later one as `fn-digest' of 66 ('B'), the running digest and the
;; block, and ends with `fn-digest' of 66, the running digest and the last
;; (nonempty) block.  The logical subject is `fn-sdg-chain' of `fn-sdg-canon'
;; (the encoding is unchanged); the executable one pushes each octet into a
;; bounded sink as `fn-sdg-canon' would cons it (`fn-sdg-canon-rev-sink'),
;; so the memory is one block and the object being read, and
;; `fn-sdg-canon-rev-sink-is-the-chain-of-the-canon' is the boundary
;; theorem between them.  The value changes only for a value whose canonical
;; stream exceeds one block, which no format and no reader depends on (a
;; comparison tool: format 10 is not deployed, and `store digest' compares
;; two opens of one image's history).

(defconst *fn-sdg-block-octets* 65536)

;; The sink: (RUNNING N . BLOCK), BLOCK the pending octets newest first and
;; N its length, RUNNING nil until the first block is digested.
(defun fn-sdg-sink-init ()
  (declare (xargs :guard t))
  (list* nil 0 nil))

(defun fn-sdg-sink-block-digest (running block)
  ; BLOCK newest first.
  (declare (xargs :guard t))
  (if running
      (fn-digest (cons 66 (fn-sdg-rev (fn-sdg-rev running nil) (fn-sdg-rev block nil))))
    (fn-digest (fn-sdg-rev block nil))))

(defun fn-sdg-sink-running (sink)
  (declare (xargs :guard t))
  (if (consp sink) (car sink) nil))

(defun fn-sdg-sink-n (sink)
  (declare (xargs :guard t))
  (if (and (consp sink) (consp (cdr sink))) (nfix (cadr sink)) 0))

(defun fn-sdg-sink-block (sink)
  (declare (xargs :guard t))
  (if (and (consp sink) (consp (cdr sink))) (cddr sink) nil))

(defun fn-sdg-sink-push (o sink)
  (declare (xargs :guard t))
  (let ((running (fn-sdg-sink-running sink))
        (n (fn-sdg-sink-n sink))
        (block (fn-sdg-sink-block sink)))
    (if (< n *fn-sdg-block-octets*)
        (list* running (1+ n) (cons o block))
      (list* (fn-sdg-sink-block-digest running block) 1 (list o)))))

(defun fn-sdg-sink-final (sink)
  (declare (xargs :guard t))
  (fn-sdg-sink-block-digest (fn-sdg-sink-running sink) (fn-sdg-sink-block sink)))

;; The sink after the octets L, in order.
(defun fn-sdg-push-list (l sink)
  (declare (xargs :guard t))
  (if (consp l)
      (fn-sdg-push-list (cdr l) (fn-sdg-sink-push (car l) sink))
    sink))

;; The logical digest of an octet stream.
(defun fn-sdg-chain (l)
  (declare (xargs :guard t))
  (fn-sdg-sink-final (fn-sdg-push-list l (fn-sdg-sink-init))))

;; The executable canonical stream: `fn-sdg-canon-rev''s traversal, each
;; octet pushed where that function conses it.  An atom's octets are its
;; own (`fn-sdg-atom'), bounded by the atom.
(mutual-recursion
 (defun fn-sdg-canon-rev-sink (x sink)
   (declare (xargs :guard t :measure (+ 1 (* 2 (acl2-count x)))))
   (if (consp x)
       (fn-sdg-canon-list-sink x (fn-sdg-sink-push 76 sink))
     (fn-sdg-push-list (fn-sdg-rev (fn-sdg-atom x nil) nil) sink)))
 (defun fn-sdg-canon-list-sink (x sink)
   (declare (xargs :guard t :measure (* 2 (acl2-count x))))
   (if (consp x)
       (fn-sdg-canon-list-sink (cdr x) (fn-sdg-canon-rev-sink (car x) sink))
     (fn-sdg-push-list (fn-sdg-rev (fn-sdg-atom x nil) nil)
                       (fn-sdg-sink-push 69 sink)))))

;; --- the boundary theorem -------------------------------------------------

(local
 (defthm fn-sdg-rev-is-revappend
   (equal (fn-sdg-rev x acc) (revappend x acc))))

(local
 (defthm fn-sdg-push-list-of-append
   (equal (fn-sdg-push-list (append a b) sink)
          (fn-sdg-push-list b (fn-sdg-push-list a sink)))))

(local
 (defthm fn-sdg-revappend-is-append
   (implies (syntaxp (not (equal b ''nil)))
            (equal (revappend a b) (append (revappend a nil) b)))))

;; Every emitter conses its octets onto ACC: its result is its own octets
;; (newest first) followed by ACC.
(local
 (defthm fn-sdg-leb-append
   (equal (fn-sdg-leb n (append x acc)) (append (fn-sdg-leb n x) acc))
   :hints (("Goal" :induct (fn-sdg-leb n x)
            :in-theory (disable floor mod)))))

(local
 (defthm fn-sdg-leb-acc
   (implies (syntaxp (not (equal acc ''nil)))
            (equal (fn-sdg-leb n acc) (append (fn-sdg-leb n nil) acc)))
   :hints (("Goal" :use ((:instance fn-sdg-leb-append (x nil)))
            :in-theory (disable fn-sdg-leb-append)))))

(local
 (defthm fn-sdg-string-append
   (equal (fn-sdg-string s i n (append x acc))
          (append (fn-sdg-string s i n x) acc))
   :hints (("Goal" :induct (fn-sdg-string s i n x)))))

(local
 (defthm fn-sdg-string-acc
   (implies (syntaxp (not (equal acc ''nil)))
            (equal (fn-sdg-string s i n acc)
                   (append (fn-sdg-string s i n nil) acc)))
   :hints (("Goal" :use ((:instance fn-sdg-string-append (x nil)))
            :in-theory (disable fn-sdg-string-append)))))

(local
 (defthm fn-sdg-str-acc
   (implies (syntaxp (not (equal acc ''nil)))
            (equal (fn-sdg-str s acc) (append (fn-sdg-str s nil) acc)))
   :hints (("Goal" :in-theory (enable fn-sdg-str)))))

(local
 (defthm fn-sdg-int-acc
   (implies (syntaxp (not (equal acc ''nil)))
            (equal (fn-sdg-int x acc) (append (fn-sdg-int x nil) acc)))))

(local
 (defthm fn-sdg-rat-acc
   (implies (syntaxp (not (equal acc ''nil)))
            (equal (fn-sdg-rat x acc) (append (fn-sdg-rat x nil) acc)))))

(local
 (defthm fn-sdg-atom-acc
   (implies (syntaxp (not (equal acc ''nil)))
            (equal (fn-sdg-atom x acc) (append (fn-sdg-atom x nil) acc)))))

(local (in-theory (disable fn-sdg-sink-push)))

(local (in-theory (disable fn-sdg-leb fn-sdg-string fn-sdg-str fn-sdg-int
                           fn-sdg-rat fn-sdg-atom fn-sdg-sink-push)))

(local
 (make-flag fn-sdg-canon-flag fn-sdg-canon-rev
            :flag-mapping ((fn-sdg-canon-rev rev) (fn-sdg-canon-list list))))

(local
 (defthm-fn-sdg-canon-flag
   (defthm fn-sdg-canon-rev-append
     (equal (fn-sdg-canon-rev x (append acc tail))
            (append (fn-sdg-canon-rev x acc) tail))
     :flag rev)
   (defthm fn-sdg-canon-list-append
     (equal (fn-sdg-canon-list x (append acc tail))
            (append (fn-sdg-canon-list x acc) tail))
     :flag list)
   :hints (("Goal" :expand ((fn-sdg-canon-rev x (append acc tail)) (fn-sdg-canon-rev x acc)
                            (fn-sdg-canon-list x (append acc tail)) (fn-sdg-canon-list x acc))))))

(local
 (defthm fn-sdg-canon-rev-acc
   (implies (syntaxp (not (equal acc ''nil)))
            (equal (fn-sdg-canon-rev x acc)
                   (append (fn-sdg-canon-rev x nil) acc)))
   :hints (("Goal" :use ((:instance fn-sdg-canon-rev-append (tail acc) (acc nil)))
            :in-theory (disable fn-sdg-canon-rev-append)))))

(local
 (defthm fn-sdg-canon-list-acc
   (implies (syntaxp (not (equal acc ''nil)))
            (equal (fn-sdg-canon-list x acc)
                   (append (fn-sdg-canon-list x nil) acc)))
   :hints (("Goal" :use ((:instance fn-sdg-canon-list-append (tail acc) (acc nil)))
            :in-theory (disable fn-sdg-canon-list-append)))))

(local
 (make-flag fn-sdg-sink-flag fn-sdg-canon-rev-sink
            :flag-mapping ((fn-sdg-canon-rev-sink rev) (fn-sdg-canon-list-sink list))))

(local
 (defthm-fn-sdg-sink-flag
   (defthm fn-sdg-canon-rev-sink-is-push
     (equal (fn-sdg-canon-rev-sink x sink)
            (fn-sdg-push-list (revappend (fn-sdg-canon-rev x nil) nil) sink))
     :flag rev)
   (defthm fn-sdg-canon-list-sink-is-push
     (equal (fn-sdg-canon-list-sink x sink)
            (fn-sdg-push-list (revappend (fn-sdg-canon-list x nil) nil) sink))
     :flag list)
   :hints (("Goal" :expand ((fn-sdg-canon-rev-sink x sink)
                            (fn-sdg-canon-list-sink x sink)
                            (fn-sdg-canon-rev x nil)
                            (fn-sdg-canon-list x nil))))))

;; KEYSTONE (the D27 boundary: the stream the host runs is the chain of the
;; canonical encoding).  `fn-sdg-digest' executes this.
(defthm fn-sdg-canon-rev-sink-is-the-chain-of-the-canon
  (equal (fn-sdg-sink-final (fn-sdg-canon-rev-sink x (fn-sdg-sink-init)))
         (fn-sdg-chain (fn-sdg-canon x)))
  :hints (("Goal" :in-theory (enable fn-sdg-canon))))

;; KEYSTONE (the value is unchanged below one block).  A stream of at most
;; one block chains to `fn-digest' of its octets, the digest this book
;; defined before format10-import.
(local
 (defun fn-sdg-block-induct (l n block)
   (if (consp l)
       (fn-sdg-block-induct (cdr l) (1+ n) (cons (car l) block))
     (list n block))))

(local
 (defthm fn-sdg-push-list-within-a-block
   (implies (and (natp n) (equal n (len block))
                 (<= (+ n (len l)) *fn-sdg-block-octets*))
            (equal (fn-sdg-push-list l (list* nil n block))
                   (list* nil (+ n (len l)) (revappend l block))))
   :hints (("Goal" :induct (fn-sdg-block-induct l n block)
            :in-theory (enable fn-sdg-sink-push)))))

(defthm fn-sdg-chain-of-one-block
  (implies (and (true-listp l) (<= (len l) *fn-sdg-block-octets*))
           (equal (fn-sdg-chain l) (fn-digest l)))
  :hints (("Goal" :in-theory (e/d (fn-sdg-chain fn-sdg-sink-final fn-sdg-sink-init)
                                  (fn-sdg-push-list-within-a-block))
           :use ((:instance fn-sdg-push-list-within-a-block
                            (n 0) (block nil))))))

(defun fn-sdg-digest (x)
  (declare (xargs :guard t))
  (mbe :logic (fn-sdg-chain (fn-sdg-canon x))
       :exec (fn-sdg-sink-final (fn-sdg-canon-rev-sink x (fn-sdg-sink-init)))))

; The arena's payloads H .. N-1, each digested, the digests accumulated
; newest first.
(defun fn-sdg-arena-loop (h n acc fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (natp h) (natp n) (<= n (fn-arena-count fn-arena)))
                  :measure (nfix (- (nfix n) (nfix h)))))
  (if (or (not (natp h)) (not (natp n)) (>= h n))
      acc
    (fn-sdg-arena-loop (1+ h) n
                       (fn-sdg-rev (fn-digest (fn-arena-payload h fn-arena)) acc)
                       fn-arena)))

; The same payload digests pushed into the sink, oldest first.
(defun fn-sdg-arena-sink (h n sink fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (natp h) (natp n) (<= n (fn-arena-count fn-arena)))
                  :measure (nfix (- (nfix n) (nfix h)))))
  (if (or (not (natp h)) (not (natp n)) (>= h n))
      sink
    (fn-sdg-arena-sink (1+ h) n
                       (fn-sdg-push-list (fn-digest (fn-arena-payload h fn-arena)) sink)
                       fn-arena)))

(local
 (defthm fn-sdg-arena-sink-is-push
   (equal (fn-sdg-arena-sink h n (fn-sdg-push-list (revappend acc nil) sink) fn-arena)
          (fn-sdg-push-list (revappend (fn-sdg-arena-loop h n acc fn-arena) nil) sink))
   :hints (("Goal" :induct (fn-sdg-arena-loop h n acc fn-arena)))))

; The pool: the chain of the payload count (LEB128) and each payload's
; digest, oldest first.  Executed as a sink (a 1,000,000-payload pool is 32
; MB of digests, never listed).
(defun fn-sdg-arena-pool (fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard-hints (("Goal" :use ((:instance fn-sdg-arena-sink-is-push
                                                         (h 0) (n (fn-arena-count fn-arena))
                                                         (acc (fn-sdg-leb (fn-arena-count fn-arena) nil))
                                                         (sink (fn-sdg-sink-init))))
                                 :in-theory (e/d (fn-sdg-chain) (fn-sdg-arena-sink-is-push))))))
  (let ((n (fn-arena-count fn-arena)))
    (mbe :logic (fn-sdg-chain
                 (fn-sdg-rev (fn-sdg-arena-loop 0 n (fn-sdg-leb n nil) fn-arena) nil))
         :exec (fn-sdg-sink-final
                (fn-sdg-arena-sink 0 n (fn-sdg-push-list (fn-sdg-rev (fn-sdg-leb n nil) nil)
                                                         (fn-sdg-sink-init))
                                   fn-arena)))))

(defun fn-sdg-rows-loop (rows acc fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (atom rows)
      acc
    (fn-sdg-rows-loop (cdr rows)
                      (fn-sdg-rev (fn-sdg-digest (fn-row-wire-of (car rows) fn-arena)) acc)
                      fn-arena)))

(defun fn-sdg-rows-sink (rows sink fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (atom rows)
      sink
    (fn-sdg-rows-sink (cdr rows)
                      (fn-sdg-push-list (fn-sdg-digest (fn-row-wire-of (car rows) fn-arena)) sink)
                      fn-arena)))

(local
 (defthm fn-sdg-rows-sink-is-push
   (equal (fn-sdg-rows-sink rows (fn-sdg-push-list (revappend acc nil) sink) fn-arena)
          (fn-sdg-push-list (revappend (fn-sdg-rows-loop rows acc fn-arena) nil) sink))
   :hints (("Goal" :induct (fn-sdg-rows-loop rows acc fn-arena)))))

; The history: the chain of the record count and each record's wire event's
; digest, in log order, executed as a sink (fn-sdg-rows-sink).
(defun fn-sdg-rows-history (rows fn-arena)
  (declare (xargs :stobjs fn-arena :guard t
                  :guard-hints (("Goal" :use ((:instance fn-sdg-rows-sink-is-push
                                                         (acc (fn-sdg-leb (len rows) nil))
                                                         (sink (fn-sdg-sink-init))))
                                 :in-theory (e/d (fn-sdg-chain) (fn-sdg-rows-sink-is-push))))))
  (mbe :logic (fn-sdg-chain
               (fn-sdg-rev (fn-sdg-rows-loop rows (fn-sdg-leb (len rows) nil) fn-arena) nil))
       :exec (fn-sdg-sink-final
              (fn-sdg-rows-sink rows (fn-sdg-push-list (fn-sdg-rev (fn-sdg-leb (len rows) nil) nil)
                                                       (fn-sdg-sink-init))
                                fn-arena))))

; Lowercase hex of an octet list, as characters.
(defun fn-sdg-hex-digit (d)
  (declare (xargs :guard t))
  (let ((d (if (natp d) (mod d 16) 0)))
    (if (< d 10) (+ 48 d) (+ 87 d))))

(defun fn-sdg-hex (octets)
  (declare (xargs :guard t))
  (if (atom octets)
      nil
    (let ((b (if (natp (car octets)) (mod (car octets) 256) 0)))
      (list* (fn-sdg-hex-digit (floor b 16)) (fn-sdg-hex-digit b)
             (fn-sdg-hex (cdr octets))))))
