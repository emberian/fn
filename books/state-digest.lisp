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

(defun fn-sdg-digest (x)
  (declare (xargs :guard t))
  (fn-digest (fn-sdg-canon x)))

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

; The pool: the digest of the payload count (LEB128) and each payload's
; digest, oldest first.
(defun fn-sdg-arena-pool (fn-arena)
  (declare (xargs :stobjs fn-arena))
  (let ((n (fn-arena-count fn-arena)))
    (fn-digest
     (fn-sdg-rev (fn-sdg-arena-loop 0 n (fn-sdg-leb n nil) fn-arena) nil))))

(defun fn-sdg-rows-loop (rows acc fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (atom rows)
      acc
    (fn-sdg-rows-loop (cdr rows)
                      (fn-sdg-rev (fn-sdg-digest (fn-row-wire-of (car rows) fn-arena)) acc)
                      fn-arena)))

; The history: the digest of the record count and each record's wire event's
; digest, in log order.
(defun fn-sdg-rows-history (rows fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (fn-digest
   (fn-sdg-rev (fn-sdg-rows-loop rows (fn-sdg-leb (len rows) nil) fn-arena) nil)))

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
