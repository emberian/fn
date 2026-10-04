; fn: exported wire grammars -- one grammar language, one interpreter, and
; its two round trips proved once for every well-formed grammar (lane
; mini-contract; Mini's M5, redregg/designs/MINI-FN-660-REQUIREMENTS-20261004.md;
; the decision is planning/design/wire-grammar-2026-10-04.md).
;
; A grammar is DATA: a tree of the nodes below.  A family's grammar is a
; `defconst'; `books/wire-grammar-export.lisp' renders the family table as
; the JSON text of specs/wire-grammar.json, and the other side (Mini, in
; Lean) runs its own interpreter of the same language over that file.
;
;   (:const OCTETS)                 exactly OCTETS; value nil
;   (:uint W LO HI)                 W octets big-endian, LO <= n <= HI
;   (:bytes W LO HI CLASS)          W-octet length L (LO..HI), L octets of CLASS
;   (:rest LO HI CLASS)             every remaining octet (tail only)
;   (:line LO HI CLASS)             L octets of CLASS (LO..HI), then CR LF;
;                                   CLASS excludes CR
;   (:base64-lines WIDTH LO HI)     fn-ot-b64-encode of the value in lines of
;                                   WIDTH characters, each then CR LF (tail)
;   (:enum W BASE NAMES)            W octets: BASE + the name's position
;   (:seq G ...)                    the elements in order; value a list
;   (:tag W (CODE NAME G) ...)      W-octet code, then that arm; value (NAME V)
;   (:maybe G)                      nothing (value nil) or G (value (V)) (tail)
;   (:where G CHECK ...)            G, accepted when every CHECK holds
;   (:frame MAGIC VERSION KIND MAX G)
;                                   MAGIC(4) VERSION KIND LENGTH(u32 <= MAX)
;                                   PAYLOAD TRAILER(32): the payload is G's
;                                   octets, all of them; the trailer is
;                                   `fn-frame-digest' of everything before it
;
; W is 1, 2, 4 or 8.  CLASS is :any, :utf8 (RFC 3629, the `utf8' book's
; decoder, as a frame :text field) or :header (HTAB, SP, VCHAR: an RFC 5322
; field body; it excludes CR, so a :line ends at its first CR).  A CHECK is
; (:le I J), (:eq I J) or (:diff K J I) over the naturals at those 0-based
; positions of the :seq value.
;
; THE TWO THEOREMS, for every grammar `fn-wg-grammarp' accepts:
;   fn-wg-decode-of-encode   decode (encode V ++ R) = (:ok V R), for a value V
;                            and octets R, when G is delimited or R is empty;
;   fn-wg-encode-of-decode   decode B = (:ok V R)  implies  V is a value and
;                            encode V ++ R = B.
; The second is CANONICITY: an accepted octet string is the encoding of its
; value, so each value has exactly one accepted encoding.  The language has
; no optional whitespace, no line-ending variants, fixed-width integers and
; canonical padded base64 (`fn-ot-b64-accepted-is-canonical'), and a
; tail-only node stands only last.
;
; Refusals: (:refused :trailer) for a frame whose trailer is not the digest
; of its protected prefix, (:refused :malformed) for every other refusal.
;
; This book owns the prefix `fn-wg-' (docs/prefixes.md).

(in-package "ACL2")
(include-book "frame-octets")
(include-book "utf8")
(include-book "octet-text")

; -----------------------------------------------------------------------------
; Total list helpers

(defun fn-wg-take (n xs)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil
    (cons (if (consp xs) (car xs) nil)
          (fn-wg-take (1- n) (if (consp xs) (cdr xs) nil)))))

(defun fn-wg-drop (n xs)
  (declare (xargs :guard (natp n)))
  (if (zp n) xs
    (fn-wg-drop (1- n) (if (consp xs) (cdr xs) nil))))

(defun fn-wg-prefixp (p xs)
  (declare (xargs :guard t))
  (if (consp p)
      (and (consp xs) (equal (car p) (car xs))
           (fn-wg-prefixp (cdr p) (cdr xs)))
    t))

(defun fn-wg-app (xs ys)
  (declare (xargs :guard t))
  (if (consp xs) (cons (car xs) (fn-wg-app (cdr xs) ys)) ys))

;; Their algebra.
(defthm fn-wg-len-of-drop
  (equal (len (fn-wg-drop n xs)) (nfix (- (len xs) (nfix n)))))
(defthm fn-wg-len-of-take
  (equal (len (fn-wg-take n xs)) (nfix n)))
(defthm fn-wg-len-of-app
  (equal (len (fn-wg-app xs ys)) (+ (len xs) (len ys))))
(defthm fn-wg-app-is-append
  (implies (true-listp xs) (equal (fn-wg-app xs ys) (append xs ys))))
(in-theory (disable fn-wg-app-is-append))
(defthm fn-wg-app-assoc
  (equal (fn-wg-app (fn-wg-app xs ys) zs) (fn-wg-app xs (fn-wg-app ys zs))))
(defthm fn-wg-take-of-app
  (implies (equal (nfix n) (len xs))
           (equal (fn-wg-take n (fn-wg-app xs ys)) (true-list-fix xs)))
  :hints (("Goal" :induct (fn-wg-take n xs))))
(defthm fn-wg-drop-of-app
  (implies (equal (nfix n) (len xs))
           (equal (fn-wg-drop n (fn-wg-app xs ys)) ys))
  :hints (("Goal" :induct (fn-wg-drop n xs))))
(defthm fn-wg-prefixp-of-app
  (implies (true-listp p) (fn-wg-prefixp p (fn-wg-app p ys))))
(defthm fn-wg-app-take-drop
  (implies (<= (nfix n) (len xs))
           (equal (fn-wg-app (fn-wg-take n xs) (fn-wg-drop n xs)) xs))
  :hints (("Goal" :induct (fn-wg-drop n xs))))
(defthm fn-wg-prefixp-app-drop
  (implies (and (fn-wg-prefixp p xs) (true-listp p))
           (equal (fn-wg-app p (fn-wg-drop (len p) xs)) xs)))
(defthm fn-wg-prefixp-len
  (implies (fn-wg-prefixp p xs) (<= (len p) (len xs)))
  :rule-classes :linear)
(defthm fn-wg-true-listp-of-take
  (true-listp (fn-wg-take n xs)))
(defthm fn-wg-take-of-len
  (implies (equal (nfix n) (len xs)) (equal (fn-wg-take n xs) (true-list-fix xs)))
  :hints (("Goal" :induct (fn-wg-take n xs))))

; -----------------------------------------------------------------------------
; Big-endian naturals of a fixed width

(defun fn-wg-widthp (w)
  (declare (xargs :guard t))
  (or (equal w 1) (equal w 2) (equal w 4) (equal w 8)))

(defun fn-wg-limit (w)
  ; 256^w: the first natural W octets cannot carry.
  (declare (xargs :guard t))
  (expt 256 (nfix w)))

; Little-endian first (the arithmetic is one floor and one mod by 256 a
; step), then reversed.
(defun fn-wg-le-bytes (w n)
  (declare (xargs :guard (and (natp w) (natp n))))
  (if (zp w) nil
    (cons (mod (nfix n) 256) (fn-wg-le-bytes (1- w) (floor (nfix n) 256)))))

(defun fn-wg-le-value (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (+ (nfix (car xs)) (* 256 (fn-wg-le-value (cdr xs))))
    0))

(encapsulate ()
(local (include-book "arithmetic-5/top" :dir :system))
(defthm fn-wg-le-bytes-shape
  (and (true-listp (fn-wg-le-bytes w n))
       (equal (len (fn-wg-le-bytes w n)) (nfix w))
       (fn-cbor-octet-listp (fn-wg-le-bytes w n))))
(defthm fn-wg-le-value-natp
  (natp (fn-wg-le-value xs))
  :rule-classes :type-prescription)
(defthm fn-wg-le-value-of-bytes
  (implies (and (natp n) (< n (expt 256 (nfix w))))
           (equal (fn-wg-le-value (fn-wg-le-bytes w n)) n)))
(defthm fn-wg-le-value-bound
  (implies (fn-cbor-octet-listp xs)
           (< (fn-wg-le-value xs) (expt 256 (len xs))))
  :hints (("Subgoal *1/2''" :nonlinearp t))
  :rule-classes :linear)
(defthm fn-wg-le-bytes-of-value
  (implies (fn-cbor-octet-listp xs)
           (equal (fn-wg-le-bytes (len xs) (fn-wg-le-value xs)) xs)))
(defun fn-wg-rev (xs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp xs) (append (fn-wg-rev (cdr xs)) (list (car xs))) nil))
(defthm fn-wg-true-listp-of-rev (true-listp (fn-wg-rev xs)))
(verify-guards fn-wg-rev)
(defthm fn-wg-len-of-rev (equal (len (fn-wg-rev xs)) (len xs)))
(defthm fn-wg-rev-of-append
  (equal (fn-wg-rev (append xs ys)) (append (fn-wg-rev ys) (fn-wg-rev xs))))
(defthm fn-wg-rev-of-rev
  (equal (fn-wg-rev (fn-wg-rev xs)) (true-list-fix xs)))
(defthm fn-wg-octet-listp-of-rev
  (implies (fn-cbor-octet-listp xs) (fn-cbor-octet-listp (fn-wg-rev xs))))
(defthm fn-wg-octet-listp-of-append
  (equal (fn-cbor-octet-listp (append xs ys))
         (and (fn-cbor-octet-listp (true-list-fix xs)) (fn-cbor-octet-listp ys))))
(defthm fn-wg-octet-listp-true-listp
  (implies (fn-cbor-octet-listp xs) (true-listp xs))
  :rule-classes :forward-chaining)
(defthm fn-wg-true-list-fix-of-octets
  (implies (fn-cbor-octet-listp xs) (equal (true-list-fix xs) xs)))

)

(defun fn-wg-be-bytes (w n)
  (declare (xargs :guard (and (natp w) (natp n))))
  (fn-wg-rev (fn-wg-le-bytes w n)))

(defun fn-wg-be-value (xs)
  (declare (xargs :guard t))
  (fn-wg-le-value (fn-wg-rev xs)))

(encapsulate ()
(local (include-book "arithmetic-5/top" :dir :system))
(defthm fn-wg-be-bytes-shape
  (and (true-listp (fn-wg-be-bytes w n))
       (equal (len (fn-wg-be-bytes w n)) (nfix w))
       (fn-cbor-octet-listp (fn-wg-be-bytes w n))))
(defthm fn-wg-be-value-natp
  (natp (fn-wg-be-value xs))
  :rule-classes :type-prescription)
(defthm fn-wg-be-value-of-bytes
  (implies (and (natp n) (< n (fn-wg-limit w)))
           (equal (fn-wg-be-value (fn-wg-be-bytes w n)) n)))
(defthm fn-wg-be-value-bound
  (implies (fn-cbor-octet-listp xs)
           (< (fn-wg-be-value xs) (fn-wg-limit (len xs))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wg-le-value-bound (xs (fn-wg-rev xs))))
           :in-theory (e/d (fn-wg-be-value) (fn-wg-le-value-bound fn-wg-le-value))))
  :rule-classes :linear)
(defthm fn-wg-be-bytes-of-value
  (implies (fn-cbor-octet-listp xs)
           (equal (fn-wg-be-bytes (len xs) (fn-wg-be-value xs)) xs))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-wg-le-bytes-of-value (xs (fn-wg-rev xs))))
           :in-theory (e/d (fn-wg-be-bytes fn-wg-be-value)
                           (fn-wg-le-bytes-of-value fn-wg-le-bytes fn-wg-le-value)))))
)
(in-theory (disable fn-wg-be-bytes fn-wg-be-value))

; -----------------------------------------------------------------------------
; Octet classes

(defun fn-wg-header-octetp (x)
  (declare (xargs :guard t))
  (and (natp x) (or (equal x 9) (and (<= 32 x) (<= x 126)))))

(defun fn-wg-header-octetsp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-wg-header-octetp (car xs)) (fn-wg-header-octetsp (cdr xs)))
    (null xs)))

(defun fn-wg-utf8p (xs)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp xs)
       (fn-wildmat-result-okp (fn-wildmat-decode-aux xs nil))))

(defun fn-wg-classp (class)
  (declare (xargs :guard t))
  (or (equal class :any) (equal class :utf8) (equal class :header)))

(defun fn-wg-class-okp (class xs)
  (declare (xargs :guard t))
  (cond ((equal class :any) (fn-cbor-octet-listp xs))
        ((equal class :utf8) (fn-wg-utf8p xs))
        ((equal class :header) (fn-wg-header-octetsp xs))
        (t nil)))

; The octets before the first CR.
(defun fn-wg-upto-cr (xs)
  (declare (xargs :guard t))
  (if (and (consp xs) (not (equal (car xs) 13)))
      (cons (car xs) (fn-wg-upto-cr (cdr xs)))
    nil))

; -----------------------------------------------------------------------------
; Base64 lines: the text cut into lines of WIDTH, each then CR LF.

(defun fn-wg-lines (w text)
  (declare (xargs :guard (natp w) :measure (len text)))
  (if (or (not (consp text)) (zp w)) nil
    (if (<= (len text) w)
        (fn-wg-app text (list 13 10))
      (fn-wg-app (fn-wg-take w text)
                 (cons 13 (cons 10 (fn-wg-lines w (fn-wg-drop w text))))))))

(defun fn-wg-unlines (w xs)
  (declare (xargs :guard (natp w) :measure (len xs)))
  (if (or (not (consp xs)) (zp w)) nil
    (if (<= (len xs) (+ w 2))
        (fn-wg-take (nfix (- (len xs) 2)) xs)
      (fn-wg-app (fn-wg-take w xs)
                 (fn-wg-unlines w (fn-wg-drop (+ w 2) xs))))))

; -----------------------------------------------------------------------------
; Checks over a :seq value

(defun fn-wg-check-okp (check v)
  (declare (xargs :guard t))
  (let ((op (if (consp check) (car check) nil))
        (a (nth (nfix (nth 1 (true-list-fix check))) (true-list-fix v)))
        (b (nth (nfix (nth 2 (true-list-fix check))) (true-list-fix v)))
        (c (nth (nfix (nth 3 (true-list-fix check))) (true-list-fix v))))
    (cond ((equal op :le) (and (natp a) (natp b) (<= a b)))
          ((equal op :eq) (and (natp a) (natp b) (equal a b)))
          ((equal op :diff) (and (natp a) (natp b) (natp c) (<= c b)
                                 (equal a (- b c))))
          (t nil))))

(defun fn-wg-checks-okp (checks v)
  (declare (xargs :guard t))
  (if (consp checks)
      (and (fn-wg-check-okp (car checks) v) (fn-wg-checks-okp (cdr checks) v))
    t))

; A :where node's checks.
(defun fn-wg-where-checks (g)
  (declare (xargs :guard t))
  (if (and (consp g) (consp (cdr g))) (cddr g) nil))

(defun fn-wg-checkp (check)
  (declare (xargs :guard t))
  (and (true-listp check)
       (or (and (member-equal (car check) '(:le :eq)) (equal (len check) 3)
                (natp (nth 1 check)) (natp (nth 2 check)))
           (and (equal (car check) :diff) (equal (len check) 4)
                (natp (nth 1 check)) (natp (nth 2 check)) (natp (nth 3 check))))))

(defun fn-wg-check-listp (checks)
  (declare (xargs :guard t))
  (if (consp checks)
      (and (fn-wg-checkp (car checks)) (fn-wg-check-listp (cdr checks)))
    (null checks)))

; -----------------------------------------------------------------------------
; Enumerations

(defun fn-wg-position (x names)
  (declare (xargs :guard t))
  (if (consp names)
      (if (equal x (car names)) 0
        (+ 1 (fn-wg-position x (cdr names))))
    0))

; -----------------------------------------------------------------------------
; The node accessors.  Nodes are read through these and `fn-wg-op' only.

(defun fn-wg-op (g) (declare (xargs :guard t)) (if (consp g) (car g) nil))
(defun fn-wg-arg (n g)
  (declare (xargs :guard (natp n)))
  (if (zp n) (if (consp g) (car g) nil)
    (fn-wg-arg (1- n) (if (consp g) (cdr g) nil))))

; A :seq or :tag node with its first element or arm removed.
(defun fn-wg-next (g)
  (declare (xargs :guard t))
  (if (and (consp g) (consp (cdr g)))
      (cons (car g) (cddr g))
    nil))
(defun fn-wg-tag-next (g)
  (declare (xargs :guard t))
  (if (and (consp g) (consp (cdr g)) (consp (cddr g)))
      (list* (car g) (cadr g) (cdddr g))
    nil))

(defthm fn-wg-next-smaller
  (implies (and (consp g) (consp (cdr g)))
           (< (acl2-count (fn-wg-next g)) (acl2-count g)))
  :rule-classes :linear)
(defthm fn-wg-tag-next-smaller
  (implies (and (consp g) (consp (cdr g)) (consp (cddr g)))
           (< (acl2-count (fn-wg-tag-next g)) (acl2-count g)))
  :rule-classes :linear)
(defthm fn-wg-count-of-arg
  (<= (acl2-count (fn-wg-arg n g)) (acl2-count g))
  :rule-classes :linear)
(defthm fn-wg-arg-smaller
  (implies (and (consp g) (posp n))
           (< (acl2-count (fn-wg-arg n g)) (acl2-count g)))
  :hints (("Goal" :expand ((fn-wg-arg n g))
           :use ((:instance fn-wg-count-of-arg (n (1- n)) (g (cdr g))))
           :in-theory (disable fn-wg-count-of-arg)))
  :rule-classes :linear)
(in-theory (disable fn-wg-next fn-wg-tag-next fn-wg-arg))

(defthm fn-wg-arm-grammar-of-arg-smaller
  (implies (consp g)
           (< (acl2-count (fn-wg-arg 2 (fn-wg-arg 2 g))) (acl2-count g)))
  :hints (("Goal" :cases ((consp (fn-wg-arg 2 g)))
           :use ((:instance fn-wg-arg-smaller (n 2) (g (fn-wg-arg 2 g)))
                 (:instance fn-wg-arg-smaller (n 2)))
           :in-theory (disable fn-wg-arg-smaller)))
  :rule-classes :linear)

; -----------------------------------------------------------------------------
; The static rules

; Every encoding of a value of G is followed by nothing G's decoder reads:
; the decoder stops at the end of the encoding whatever follows.
(defun fn-wg-delimitedp (g)
  (declare (xargs :guard t :measure (acl2-count g)))
  (let ((op (fn-wg-op g)))
    (cond ((member-equal op '(:const :uint :bytes :line :enum :frame)) t)
          ((equal op :seq)
           (if (and (consp g) (consp (cdr g)))
               (and (fn-wg-delimitedp (fn-wg-arg 1 g))
                    (fn-wg-delimitedp (fn-wg-next g)))
             t))
          ((equal op :tag)
           (if (and (consp g) (consp (cdr g)) (consp (cddr g)))
               (and (fn-wg-delimitedp (fn-wg-arg 2 (fn-wg-arg 2 g)))
                    (fn-wg-delimitedp (fn-wg-tag-next g)))
             t))
          ((equal op :where) (fn-wg-delimitedp (fn-wg-arg 1 g)))
          (t nil))))

; No value of G encodes to no octets.
(defun fn-wg-nonemptyp (g)
  (declare (xargs :guard t :measure (acl2-count g)))
  (let ((op (fn-wg-op g)))
    (cond ((equal op :const) (consp (fn-wg-arg 1 g)))
          ((member-equal op '(:uint :bytes :line :enum :frame :tag)) t)
          ((member-equal op '(:rest :base64-lines))
           (posp (fn-wg-arg (if (equal op :rest) 1 2) g)))
          ((equal op :seq)
           (if (and (consp g) (consp (cdr g)))
               (or (fn-wg-nonemptyp (fn-wg-arg 1 g))
                   (fn-wg-nonemptyp (fn-wg-next g)))
             nil))
          ((equal op :where) (fn-wg-nonemptyp (fn-wg-arg 1 g)))
          (t nil))))

(defun fn-wg-tag-codes (g)
  (declare (xargs :guard t :measure (acl2-count g)))
  (if (and (consp g) (consp (cdr g)) (consp (cddr g)))
      (cons (fn-wg-arg 0 (fn-wg-arg 2 g)) (fn-wg-tag-codes (fn-wg-tag-next g)))
    nil))

(defun fn-wg-tag-names (g)
  (declare (xargs :guard t :measure (acl2-count g)))
  (if (and (consp g) (consp (cdr g)) (consp (cddr g)))
      (cons (fn-wg-arg 1 (fn-wg-arg 2 g)) (fn-wg-tag-names (fn-wg-tag-next g)))
    nil))

(defun fn-wg-armp (arm w)
  (declare (xargs :guard t))
  (and (true-listp arm) (equal (len arm) 3)
       (natp (fn-wg-arg 0 arm)) (< (fn-wg-arg 0 arm) (fn-wg-limit w))
       (symbolp (fn-wg-arg 1 arm))))

(defun fn-wg-grammarp (g)
  (declare (xargs :guard t :measure (acl2-count g)))
  (let ((op (fn-wg-op g)))
    (and
     (true-listp g)
     (cond
      ((equal op :const) (and (equal (len g) 2) (fn-cbor-octet-listp (fn-wg-arg 1 g))))
      ((equal op :uint)
       (and (equal (len g) 4) (fn-wg-widthp (fn-wg-arg 1 g))
            (natp (fn-wg-arg 2 g)) (natp (fn-wg-arg 3 g))
            (<= (fn-wg-arg 2 g) (fn-wg-arg 3 g))
            (< (fn-wg-arg 3 g) (fn-wg-limit (fn-wg-arg 1 g)))))
      ((equal op :bytes)
       (and (equal (len g) 5) (fn-wg-widthp (fn-wg-arg 1 g))
            (natp (fn-wg-arg 2 g)) (natp (fn-wg-arg 3 g))
            (<= (fn-wg-arg 2 g) (fn-wg-arg 3 g))
            (< (fn-wg-arg 3 g) (fn-wg-limit (fn-wg-arg 1 g)))
            (fn-wg-classp (fn-wg-arg 4 g))))
      ((equal op :rest)
       (and (equal (len g) 4) (natp (fn-wg-arg 1 g)) (natp (fn-wg-arg 2 g))
            (<= (fn-wg-arg 1 g) (fn-wg-arg 2 g)) (fn-wg-classp (fn-wg-arg 3 g))))
      ((equal op :line)
       (and (equal (len g) 4) (natp (fn-wg-arg 1 g)) (natp (fn-wg-arg 2 g))
            (<= (fn-wg-arg 1 g) (fn-wg-arg 2 g)) (equal (fn-wg-arg 3 g) :header)))
      ((equal op :base64-lines)
       (and (equal (len g) 4) (posp (fn-wg-arg 1 g)) (natp (fn-wg-arg 2 g))
            (natp (fn-wg-arg 3 g)) (<= (fn-wg-arg 2 g) (fn-wg-arg 3 g))))
      ((equal op :enum)
       (and (equal (len g) 4) (fn-wg-widthp (fn-wg-arg 1 g)) (natp (fn-wg-arg 2 g))
            (symbol-listp (fn-wg-arg 3 g)) (consp (fn-wg-arg 3 g))
            (no-duplicatesp-equal (fn-wg-arg 3 g))
            (<= (+ (fn-wg-arg 2 g) (len (fn-wg-arg 3 g))) (fn-wg-limit (fn-wg-arg 1 g)))))
      ((equal op :seq)
       (if (consp (cdr g))
           (and (fn-wg-grammarp (fn-wg-arg 1 g))
                (or (not (consp (cddr g))) (fn-wg-delimitedp (fn-wg-arg 1 g)))
                (fn-wg-grammarp (fn-wg-next g)))
         t))
      ((equal op :tag)
       (and (consp (cdr g)) (fn-wg-widthp (fn-wg-arg 1 g))
            (if (consp (cddr g))
                (and (fn-wg-armp (fn-wg-arg 2 g) (fn-wg-arg 1 g))
                     (fn-wg-grammarp (fn-wg-arg 2 (fn-wg-arg 2 g)))
                     (not (member-equal (fn-wg-arg 0 (fn-wg-arg 2 g))
                                        (fn-wg-tag-codes (fn-wg-tag-next g))))
                     (not (member-equal (fn-wg-arg 1 (fn-wg-arg 2 g))
                                        (fn-wg-tag-names (fn-wg-tag-next g))))
                     (fn-wg-grammarp (fn-wg-tag-next g)))
              t)))
      ((equal op :maybe)
       (and (equal (len g) 2) (fn-wg-grammarp (fn-wg-arg 1 g))
            (fn-wg-nonemptyp (fn-wg-arg 1 g))))
      ((equal op :where)
       (and (consp (cdr g)) (fn-wg-grammarp (fn-wg-arg 1 g))
            (equal (fn-wg-op (fn-wg-arg 1 g)) :seq)
            (fn-wg-check-listp (cddr g))))
      ((equal op :frame)
       (and (equal (len g) 6)
            (fn-cbor-octet-listp (fn-wg-arg 1 g)) (equal (len (fn-wg-arg 1 g)) 4)
            (fn-cbor-octetp (fn-wg-arg 2 g)) (fn-cbor-octetp (fn-wg-arg 3 g))
            (natp (fn-wg-arg 4 g)) (< (fn-wg-arg 4 g) (fn-wg-limit 4))
            (fn-wg-grammarp (fn-wg-arg 5 g))))
      (t nil)))))

; -----------------------------------------------------------------------------
; The encoder

(defun fn-wg-frame-protected (magic version kind payload)
  (declare (xargs :guard t))
  (fn-wg-app magic (cons version (cons kind (fn-wg-app (fn-wg-be-bytes 4 (len payload))
                                                       payload)))))

(defun fn-wg-encode (g v)
  (declare (xargs :guard t :measure (acl2-count g) :verify-guards nil))
  (let ((op (fn-wg-op g)))
    (cond
     ((equal op :const) (fn-wg-arg 1 g))
     ((equal op :uint) (fn-wg-be-bytes (nfix (fn-wg-arg 1 g)) (nfix v)))
     ((equal op :bytes) (fn-wg-app (fn-wg-be-bytes (nfix (fn-wg-arg 1 g)) (len v)) v))
     ((equal op :rest) v)
     ((equal op :line) (fn-wg-app v (list 13 10)))
     ((equal op :base64-lines)
      (fn-wg-lines (nfix (fn-wg-arg 1 g)) (fn-ot-b64-encode v)))
     ((equal op :enum)
      (fn-wg-be-bytes (nfix (fn-wg-arg 1 g))
                      (+ (nfix (fn-wg-arg 2 g)) (fn-wg-position v (fn-wg-arg 3 g)))))
     ((equal op :seq)
      (if (and (consp g) (consp (cdr g)))
          (fn-wg-app (fn-wg-encode (fn-wg-arg 1 g) (if (consp v) (car v) nil))
                     (fn-wg-encode (fn-wg-next g) (if (consp v) (cdr v) nil)))
        nil))
     ((equal op :tag)
      (if (and (consp g) (consp (cdr g)) (consp (cddr g)))
          (if (equal (if (consp v) (car v) nil) (fn-wg-arg 1 (fn-wg-arg 2 g)))
              (fn-wg-app (fn-wg-be-bytes (nfix (fn-wg-arg 1 g))
                                         (nfix (fn-wg-arg 0 (fn-wg-arg 2 g))))
                         (fn-wg-encode (fn-wg-arg 2 (fn-wg-arg 2 g))
                                       (if (and (consp v) (consp (cdr v))) (cadr v) nil)))
            (fn-wg-encode (fn-wg-tag-next g) v))
        nil))
     ((equal op :maybe)
      (if (consp v) (fn-wg-encode (fn-wg-arg 1 g) (car v)) nil))
     ((equal op :where) (fn-wg-encode (fn-wg-arg 1 g) v))
     ((equal op :frame)
      (let ((prot (fn-wg-frame-protected (fn-wg-arg 1 g) (fn-wg-arg 2 g) (fn-wg-arg 3 g)
                                         (fn-wg-encode (fn-wg-arg 5 g) v))))
        (fn-wg-app prot (fn-frame-digest prot))))
     (t nil))))

; -----------------------------------------------------------------------------
; Values

(defun fn-wg-valuep (g v)
  (declare (xargs :guard t :measure (acl2-count g) :verify-guards nil))
  (let ((op (fn-wg-op g)))
    (cond
     ((equal op :const) (null v))
     ((equal op :uint) (and (natp v) (<= (nfix (fn-wg-arg 2 g)) v) (<= v (nfix (fn-wg-arg 3 g)))))
     ((member-equal op '(:bytes :line))
      (let ((class (fn-wg-arg (if (equal op :bytes) 4 3) g))
            (lo (fn-wg-arg (if (equal op :bytes) 2 1) g))
            (hi (fn-wg-arg (if (equal op :bytes) 3 2) g)))
        (and (fn-cbor-octet-listp v) (fn-wg-class-okp class v)
             (<= (nfix lo) (len v)) (<= (len v) (nfix hi)))))
     ((equal op :rest)
      (and (fn-cbor-octet-listp v) (fn-wg-class-okp (fn-wg-arg 3 g) v)
           (<= (nfix (fn-wg-arg 1 g)) (len v)) (<= (len v) (nfix (fn-wg-arg 2 g)))))
     ((equal op :base64-lines)
      (and (fn-cbor-octet-listp v)
           (<= (nfix (fn-wg-arg 2 g)) (len v)) (<= (len v) (nfix (fn-wg-arg 3 g)))))
     ((equal op :enum)
      (and (true-listp (fn-wg-arg 3 g)) (member-equal v (fn-wg-arg 3 g))))
     ((equal op :seq)
      (if (and (consp g) (consp (cdr g)))
          (and (consp v)
               (fn-wg-valuep (fn-wg-arg 1 g) (car v))
               (fn-wg-valuep (fn-wg-next g) (cdr v)))
        (null v)))
     ((equal op :tag)
      (if (and (consp g) (consp (cdr g)) (consp (cddr g)))
          (and (true-listp v) (equal (len v) 2)
               (if (equal (car v) (fn-wg-arg 1 (fn-wg-arg 2 g)))
                   (fn-wg-valuep (fn-wg-arg 2 (fn-wg-arg 2 g)) (cadr v))
                 (fn-wg-valuep (fn-wg-tag-next g) v)))
        nil))
     ((equal op :maybe)
      (or (null v)
          (and (consp v) (null (cdr v)) (fn-wg-valuep (fn-wg-arg 1 g) (car v)))))
     ((equal op :where)
      (and (fn-wg-valuep (fn-wg-arg 1 g) v) (fn-wg-checks-okp (fn-wg-where-checks g) v)))
     ((equal op :frame)
      (and (fn-wg-valuep (fn-wg-arg 5 g) v)
           (<= (len (fn-wg-encode (fn-wg-arg 5 g) v)) (nfix (fn-wg-arg 4 g)))))
     (t nil))))

; -----------------------------------------------------------------------------
; The decoder

(defun fn-wg-ok (v rest) (declare (xargs :guard t)) (list :ok v rest))
(defun fn-wg-refused (reason) (declare (xargs :guard t)) (list :refused reason))
(defun fn-wg-okp (r) (declare (xargs :guard t)) (and (consp r) (equal (car r) :ok)))
(defun fn-wg-value (r) (declare (xargs :guard t)) (if (and (consp r) (consp (cdr r))) (cadr r) nil))
(defun fn-wg-rest (r) (declare (xargs :guard t)) (if (and (consp r) (consp (cdr r)) (consp (cddr r))) (caddr r) nil))
(defun fn-wg-malformed () (declare (xargs :guard t)) (fn-wg-refused :malformed))

(defun fn-wg-decode (g xs)
  (declare (xargs :guard t :measure (acl2-count g) :verify-guards nil))
  (let ((op (fn-wg-op g)))
    (cond
     ((equal op :const)
      (if (fn-wg-prefixp (fn-wg-arg 1 g) xs)
          (fn-wg-ok nil (fn-wg-drop (len (fn-wg-arg 1 g)) xs))
        (fn-wg-malformed)))
     ((equal op :uint)
      (let* ((w (nfix (fn-wg-arg 1 g)))
             (n (fn-wg-be-value (fn-wg-take w xs))))
        (if (and (<= w (len xs))
                 (fn-cbor-octet-listp (fn-wg-take w xs))
                 (<= (nfix (fn-wg-arg 2 g)) n) (<= n (nfix (fn-wg-arg 3 g))))
            (fn-wg-ok n (fn-wg-drop w xs))
          (fn-wg-malformed))))
     ((equal op :bytes)
      (let* ((w (nfix (fn-wg-arg 1 g)))
             (n (fn-wg-be-value (fn-wg-take w xs)))
             (body (fn-wg-drop w xs))
             (v (fn-wg-take n body)))
        (if (and (<= w (len xs))
                 (fn-cbor-octet-listp (fn-wg-take w xs))
                 (<= (nfix (fn-wg-arg 2 g)) n) (<= n (nfix (fn-wg-arg 3 g)))
                 (<= n (len body))
                 (fn-wg-class-okp (fn-wg-arg 4 g) v))
            (fn-wg-ok v (fn-wg-drop n body))
          (fn-wg-malformed))))
     ((equal op :rest)
      (if (and (fn-wg-class-okp (fn-wg-arg 3 g) xs)
               (fn-cbor-octet-listp xs)
               (<= (nfix (fn-wg-arg 1 g)) (len xs))
               (<= (len xs) (nfix (fn-wg-arg 2 g))))
          (fn-wg-ok xs nil)
        (fn-wg-malformed)))
     ((equal op :line)
      (let* ((v (fn-wg-upto-cr xs))
             (after (fn-wg-drop (len v) xs)))
        (if (and (fn-wg-prefixp (list 13 10) after)
                 (fn-wg-class-okp (fn-wg-arg 3 g) v)
                 (<= (nfix (fn-wg-arg 1 g)) (len v))
                 (<= (len v) (nfix (fn-wg-arg 2 g))))
            (fn-wg-ok v (fn-wg-drop 2 after))
          (fn-wg-malformed))))
     ((equal op :base64-lines)
      (let* ((w (nfix (fn-wg-arg 1 g)))
             (text (fn-wg-unlines w xs)))
        (if (equal (fn-wg-lines w text) xs)
            (mv-let (err v) (fn-ot-b64-decode text)
              (if (and (not err)
                       (<= (nfix (fn-wg-arg 2 g)) (len v))
                       (<= (len v) (nfix (fn-wg-arg 3 g))))
                  (fn-wg-ok v nil)
                (fn-wg-malformed)))
          (fn-wg-malformed))))
     ((equal op :enum)
      (let* ((w (nfix (fn-wg-arg 1 g)))
             (n (fn-wg-be-value (fn-wg-take w xs)))
             (base (nfix (fn-wg-arg 2 g)))
             (names (fn-wg-arg 3 g)))
        (if (and (<= w (len xs))
                 (fn-cbor-octet-listp (fn-wg-take w xs))
                 (<= base n) (< n (+ base (len names))))
            (fn-wg-ok (nth (- n base) (true-list-fix names)) (fn-wg-drop w xs))
          (fn-wg-malformed))))
     ((equal op :seq)
      (if (and (consp g) (consp (cdr g)))
          (let ((r1 (fn-wg-decode (fn-wg-arg 1 g) xs)))
            (if (fn-wg-okp r1)
                (let ((r2 (fn-wg-decode (fn-wg-next g) (fn-wg-rest r1))))
                  (if (fn-wg-okp r2)
                      (fn-wg-ok (cons (fn-wg-value r1) (fn-wg-value r2)) (fn-wg-rest r2))
                    r2))
              r1))
        (fn-wg-ok nil xs)))
     ((equal op :tag)
      (if (and (consp g) (consp (cdr g)) (consp (cddr g)))
          (let ((w (nfix (fn-wg-arg 1 g))))
            (if (and (<= w (len xs))
                     (fn-cbor-octet-listp (fn-wg-take w xs))
                     (equal (fn-wg-be-value (fn-wg-take w xs))
                            (fn-wg-arg 0 (fn-wg-arg 2 g))))
                (let ((r (fn-wg-decode (fn-wg-arg 2 (fn-wg-arg 2 g)) (fn-wg-drop w xs))))
                  (if (fn-wg-okp r)
                      (fn-wg-ok (list (fn-wg-arg 1 (fn-wg-arg 2 g)) (fn-wg-value r))
                                (fn-wg-rest r))
                    r))
              (fn-wg-decode (fn-wg-tag-next g) xs)))
        (fn-wg-malformed)))
     ((equal op :maybe)
      (if (consp xs)
          (let ((r (fn-wg-decode (fn-wg-arg 1 g) xs)))
            (if (fn-wg-okp r)
                (fn-wg-ok (list (fn-wg-value r)) (fn-wg-rest r))
              r))
        (fn-wg-ok nil xs)))
     ((equal op :where)
      (let ((r (fn-wg-decode (fn-wg-arg 1 g) xs)))
        (if (and (fn-wg-okp r) (not (fn-wg-checks-okp (fn-wg-where-checks g) (fn-wg-value r))))
            (fn-wg-malformed)
          r)))
     ((equal op :frame)
      ; Split in order: MAGIC(4) VERSION KIND LENGTH(4) PAYLOAD TRAILER(32).
      (let* ((m (fn-wg-take 4 xs))
             (x1 (fn-wg-drop 4 xs))
             (version (if (consp x1) (car x1) nil))
             (kind (if (and (consp x1) (consp (cdr x1))) (cadr x1) nil))
             (x2 (if (and (consp x1) (consp (cdr x1))) (cddr x1) nil))
             (lenb (fn-wg-take 4 x2))
             (x3 (fn-wg-drop 4 x2))
             (n (fn-wg-be-value lenb))
             (payload (fn-wg-take n x3))
             (x4 (fn-wg-drop n x3))
             (trailer (fn-wg-take 32 x4)))
        (if (not (and (<= 4 (len xs))
                      (equal m (fn-wg-arg 1 g))
                      (consp x1) (consp (cdr x1))
                      (equal version (fn-wg-arg 2 g))
                      (equal kind (fn-wg-arg 3 g))
                      (<= 4 (len x2))
                      (fn-cbor-octet-listp lenb)
                      (<= n (nfix (fn-wg-arg 4 g)))
                      (<= (+ n 32) (len x3))
                      (fn-cbor-octet-listp payload)
                      (fn-cbor-octet-listp trailer)))
            (fn-wg-malformed)
          (if (not (equal trailer
                          (fn-frame-digest (fn-wg-frame-protected m version kind payload))))
              (fn-wg-refused :trailer)
            (let ((r (fn-wg-decode (fn-wg-arg 5 g) payload)))
              (cond ((not (fn-wg-okp r)) r)
                    ((consp (fn-wg-rest r)) (fn-wg-malformed))
                    (t (fn-wg-ok (fn-wg-value r) (fn-wg-drop 32 x4)))))))))
     (t (fn-wg-malformed)))))

; -----------------------------------------------------------------------------
; The round trips: lemmas

(defthm fn-wg-true-listp-of-app
  (equal (true-listp (fn-wg-app xs ys)) (true-listp ys)))
(defthm fn-wg-octets-of-app
  (implies (and (fn-cbor-octet-listp xs) (fn-cbor-octet-listp ys))
           (fn-cbor-octet-listp (fn-wg-app xs ys))))
(defthm fn-wg-app-nil
  (implies (true-listp xs) (equal (fn-wg-app xs nil) xs)))
(defthm fn-wg-consp-of-app
  (equal (consp (fn-wg-app xs ys)) (or (consp xs) (consp ys))))
(defthm fn-wg-b64-encode-octets
  (fn-cbor-octet-listp (fn-ot-b64-encode xs))
  :hints (("Goal" :in-theory (enable fn-ot-b64-c0 fn-ot-b64-c1 fn-ot-b64-c2 fn-ot-b64-c3
                                     fn-ot-b64-c1-last fn-ot-b64-c2-last))))
(defthm fn-wg-b64-encode-nonempty
  (implies (consp xs) (consp (fn-ot-b64-encode xs))))
(defthm fn-wg-octets-of-take
  (implies (and (fn-cbor-octet-listp xs) (<= (nfix n) (len xs)))
           (fn-cbor-octet-listp (fn-wg-take n xs))))
(defthm fn-wg-octets-of-drop
  (implies (fn-cbor-octet-listp xs)
           (fn-cbor-octet-listp (fn-wg-drop n xs))))
(defthm fn-wg-true-listp-of-drop
  (implies (true-listp xs) (true-listp (fn-wg-drop n xs))))
(defthm fn-wg-drop-of-app-longer
  (implies (<= (len xs) (nfix n))
           (equal (fn-wg-drop n (fn-wg-app xs ys)) (fn-wg-drop (- (nfix n) (len xs)) ys)))
  :hints (("Goal" :induct (fn-wg-drop n xs))))
(defthm fn-wg-true-list-fix-of-take
  (equal (true-list-fix (fn-wg-take n xs)) (fn-wg-take n xs)))
(defthm fn-wg-consp-of-drop
  (implies (< (nfix n) (len xs)) (consp (fn-wg-drop n xs))))
(defthm fn-wg-consp-when-len-positive
  (implies (< 0 (len x)) (consp x)))

(defthm fn-wg-lines-octets
  (implies (fn-cbor-octet-listp text)
           (fn-cbor-octet-listp (fn-wg-lines w text))))
(defthm fn-wg-lines-consp
  (implies (and (consp text) (posp w)) (consp (fn-wg-lines w text))))
(defthm fn-wg-lines-len-positive
  (implies (and (consp text) (posp w)) (< 0 (len (fn-wg-lines w text))))
  :rule-classes :linear)
(defthm fn-wg-unlines-of-lines
  (implies (and (posp w) (true-listp text))
           (equal (fn-wg-unlines w (fn-wg-lines w text)) text))
  :hints (("Goal" :induct (fn-wg-lines w text))
          ("Subgoal *1/3" :expand ((fn-wg-unlines w (fn-wg-app (fn-wg-take w text)
                                       (list* 13 10 (fn-wg-lines w (fn-wg-drop w text)))))))
          ("Subgoal *1/2" :expand ((fn-wg-unlines w (fn-wg-app text '(13 10)))))))

(defthm fn-wg-upto-cr-of-header-line
  (implies (fn-wg-header-octetsp v)
           (equal (fn-wg-upto-cr (fn-wg-app v (cons 13 rest))) v)))
(defthm fn-wg-header-octets-true-listp
  (implies (fn-wg-header-octetsp v) (true-listp v))
  :rule-classes :forward-chaining)
(defthm fn-wg-position-of-member
  (implies (member-equal v names)
           (and (< (fn-wg-position v names) (len names))
                (equal (nth (fn-wg-position v names) (true-list-fix names)) v))))

(defthm fn-wg-frame-protected-octets
  (implies (and (fn-cbor-octet-listp magic) (fn-cbor-octetp version) (fn-cbor-octetp kind)
                (fn-cbor-octet-listp payload))
           (fn-cbor-octet-listp (fn-wg-frame-protected magic version kind payload))))
(defthm fn-wg-class-ok-octets
  (implies (fn-wg-class-okp class xs) (fn-cbor-octet-listp xs))
  :hints (("Goal" :in-theory (enable fn-wg-class-okp fn-wg-utf8p)))
  :rule-classes :forward-chaining)
(defthm fn-wg-widthp-forward
  (implies (fn-wg-widthp w) (and (posp w) (<= w 8)))
  :rule-classes :forward-chaining)
(defthm fn-wg-op-consp
  (implies (fn-wg-op g) (consp g))
  :rule-classes :forward-chaining)
(defthm fn-wg-op-of-cons
  (equal (fn-wg-op (cons a b)) a))
(defthm fn-wg-limit-positive
  (< 0 (fn-wg-limit w))
  :rule-classes :linear)
(defthm fn-wg-tag-grammar-width
  (implies (and (fn-wg-grammarp g) (equal (fn-wg-op g) :tag))
           (fn-wg-widthp (fn-wg-arg 1 g)))
  :rule-classes :forward-chaining)

; The structure the recursions walk, with `fn-wg-next' and `fn-wg-tag-next'
; closed.
(defthm fn-wg-next-structure
  (implies (and (consp g) (consp (cdr g)))
           (and (equal (fn-wg-op (fn-wg-next g)) (fn-wg-op g))
                (consp (fn-wg-next g))
                (equal (consp (cdr (fn-wg-next g))) (consp (cddr g)))))
  :hints (("Goal" :in-theory (enable fn-wg-next))))
(defthm fn-wg-tag-next-structure
  (implies (and (consp g) (consp (cdr g)) (consp (cddr g)))
           (and (equal (fn-wg-op (fn-wg-tag-next g)) (fn-wg-op g))
                (equal (fn-wg-arg 1 (fn-wg-tag-next g)) (fn-wg-arg 1 g))
                (consp (fn-wg-tag-next g))
                (consp (cdr (fn-wg-tag-next g)))
                (equal (consp (cddr (fn-wg-tag-next g))) (consp (cdddr g)))))
  :hints (("Goal" :in-theory (enable fn-wg-tag-next fn-wg-arg))))

(defthm fn-wg-armp-forward
  (implies (fn-wg-armp arm w)
           (and (natp (fn-wg-arg 0 arm))
                (< (fn-wg-arg 0 arm) (fn-wg-limit w))
                (symbolp (fn-wg-arg 1 arm))))
  :rule-classes :forward-chaining)

(in-theory (disable fn-wg-op fn-wg-armp fn-wg-widthp fn-wg-limit))

; Openers: each definition below at one node kind, so a proof about one kind
; never sees the others (generated from the definitions' arms).
;; BEGIN GENERATED OPENERS
(defthm fn-wg-decode-opener-const
  (implies (equal (fn-wg-op g) :const)
           (equal (fn-wg-decode g xs)
                  (if (fn-wg-prefixp (fn-wg-arg 1 g) xs)
          (fn-wg-ok nil (fn-wg-drop (len (fn-wg-arg 1 g)) xs))
        (fn-wg-malformed))))
  :hints (("Goal" :expand ((fn-wg-decode g xs)))))

(defthm fn-wg-decode-opener-uint
  (implies (equal (fn-wg-op g) :uint)
           (equal (fn-wg-decode g xs)
                  (let* ((w (nfix (fn-wg-arg 1 g)))
             (n (fn-wg-be-value (fn-wg-take w xs))))
        (if (and (<= w (len xs))
                 (fn-cbor-octet-listp (fn-wg-take w xs))
                 (<= (nfix (fn-wg-arg 2 g)) n) (<= n (nfix (fn-wg-arg 3 g))))
            (fn-wg-ok n (fn-wg-drop w xs))
          (fn-wg-malformed)))))
  :hints (("Goal" :expand ((fn-wg-decode g xs)))))

(defthm fn-wg-decode-opener-bytes
  (implies (equal (fn-wg-op g) :bytes)
           (equal (fn-wg-decode g xs)
                  (let* ((w (nfix (fn-wg-arg 1 g)))
             (n (fn-wg-be-value (fn-wg-take w xs)))
             (body (fn-wg-drop w xs))
             (v (fn-wg-take n body)))
        (if (and (<= w (len xs))
                 (fn-cbor-octet-listp (fn-wg-take w xs))
                 (<= (nfix (fn-wg-arg 2 g)) n) (<= n (nfix (fn-wg-arg 3 g)))
                 (<= n (len body))
                 (fn-wg-class-okp (fn-wg-arg 4 g) v))
            (fn-wg-ok v (fn-wg-drop n body))
          (fn-wg-malformed)))))
  :hints (("Goal" :expand ((fn-wg-decode g xs)))))

(defthm fn-wg-decode-opener-rest
  (implies (equal (fn-wg-op g) :rest)
           (equal (fn-wg-decode g xs)
                  (if (and (fn-wg-class-okp (fn-wg-arg 3 g) xs)
               (fn-cbor-octet-listp xs)
               (<= (nfix (fn-wg-arg 1 g)) (len xs))
               (<= (len xs) (nfix (fn-wg-arg 2 g))))
          (fn-wg-ok xs nil)
        (fn-wg-malformed))))
  :hints (("Goal" :expand ((fn-wg-decode g xs)))))

(defthm fn-wg-decode-opener-line
  (implies (equal (fn-wg-op g) :line)
           (equal (fn-wg-decode g xs)
                  (let* ((v (fn-wg-upto-cr xs))
             (after (fn-wg-drop (len v) xs)))
        (if (and (fn-wg-prefixp (list 13 10) after)
                 (fn-wg-class-okp (fn-wg-arg 3 g) v)
                 (<= (nfix (fn-wg-arg 1 g)) (len v))
                 (<= (len v) (nfix (fn-wg-arg 2 g))))
            (fn-wg-ok v (fn-wg-drop 2 after))
          (fn-wg-malformed)))))
  :hints (("Goal" :expand ((fn-wg-decode g xs)))))

(defthm fn-wg-decode-opener-base64-lines
  (implies (equal (fn-wg-op g) :base64-lines)
           (equal (fn-wg-decode g xs)
                  (let* ((w (nfix (fn-wg-arg 1 g)))
             (text (fn-wg-unlines w xs)))
        (if (equal (fn-wg-lines w text) xs)
            (mv-let (err v) (fn-ot-b64-decode text)
              (if (and (not err)
                       (<= (nfix (fn-wg-arg 2 g)) (len v))
                       (<= (len v) (nfix (fn-wg-arg 3 g))))
                  (fn-wg-ok v nil)
                (fn-wg-malformed)))
          (fn-wg-malformed)))))
  :hints (("Goal" :expand ((fn-wg-decode g xs)))))

(defthm fn-wg-decode-opener-enum
  (implies (equal (fn-wg-op g) :enum)
           (equal (fn-wg-decode g xs)
                  (let* ((w (nfix (fn-wg-arg 1 g)))
             (n (fn-wg-be-value (fn-wg-take w xs)))
             (base (nfix (fn-wg-arg 2 g)))
             (names (fn-wg-arg 3 g)))
        (if (and (<= w (len xs))
                 (fn-cbor-octet-listp (fn-wg-take w xs))
                 (<= base n) (< n (+ base (len names))))
            (fn-wg-ok (nth (- n base) (true-list-fix names)) (fn-wg-drop w xs))
          (fn-wg-malformed)))))
  :hints (("Goal" :expand ((fn-wg-decode g xs)))))

(defthm fn-wg-decode-opener-seq
  (implies (equal (fn-wg-op g) :seq)
           (equal (fn-wg-decode g xs)
                  (if (and (consp g) (consp (cdr g)))
          (let ((r1 (fn-wg-decode (fn-wg-arg 1 g) xs)))
            (if (fn-wg-okp r1)
                (let ((r2 (fn-wg-decode (fn-wg-next g) (fn-wg-rest r1))))
                  (if (fn-wg-okp r2)
                      (fn-wg-ok (cons (fn-wg-value r1) (fn-wg-value r2)) (fn-wg-rest r2))
                    r2))
              r1))
        (fn-wg-ok nil xs))))
  :hints (("Goal" :expand ((fn-wg-decode g xs)))))

(defthm fn-wg-decode-opener-tag
  (implies (equal (fn-wg-op g) :tag)
           (equal (fn-wg-decode g xs)
                  (if (and (consp g) (consp (cdr g)) (consp (cddr g)))
          (let ((w (nfix (fn-wg-arg 1 g))))
            (if (and (<= w (len xs))
                     (fn-cbor-octet-listp (fn-wg-take w xs))
                     (equal (fn-wg-be-value (fn-wg-take w xs))
                            (fn-wg-arg 0 (fn-wg-arg 2 g))))
                (let ((r (fn-wg-decode (fn-wg-arg 2 (fn-wg-arg 2 g)) (fn-wg-drop w xs))))
                  (if (fn-wg-okp r)
                      (fn-wg-ok (list (fn-wg-arg 1 (fn-wg-arg 2 g)) (fn-wg-value r))
                                (fn-wg-rest r))
                    r))
              (fn-wg-decode (fn-wg-tag-next g) xs)))
        (fn-wg-malformed))))
  :hints (("Goal" :expand ((fn-wg-decode g xs)))))

(defthm fn-wg-decode-opener-maybe
  (implies (equal (fn-wg-op g) :maybe)
           (equal (fn-wg-decode g xs)
                  (if (consp xs)
          (let ((r (fn-wg-decode (fn-wg-arg 1 g) xs)))
            (if (fn-wg-okp r)
                (fn-wg-ok (list (fn-wg-value r)) (fn-wg-rest r))
              r))
        (fn-wg-ok nil xs))))
  :hints (("Goal" :expand ((fn-wg-decode g xs)))))

(defthm fn-wg-decode-opener-where
  (implies (equal (fn-wg-op g) :where)
           (equal (fn-wg-decode g xs)
                  (let ((r (fn-wg-decode (fn-wg-arg 1 g) xs)))
        (if (and (fn-wg-okp r) (not (fn-wg-checks-okp (fn-wg-where-checks g) (fn-wg-value r))))
            (fn-wg-malformed)
          r))))
  :hints (("Goal" :expand ((fn-wg-decode g xs)))))

(defthm fn-wg-decode-opener-frame
  (implies (equal (fn-wg-op g) :frame)
           (equal (fn-wg-decode g xs)
                  (let* ((m (fn-wg-take 4 xs))
             (x1 (fn-wg-drop 4 xs))
             (version (if (consp x1) (car x1) nil))
             (kind (if (and (consp x1) (consp (cdr x1))) (cadr x1) nil))
             (x2 (if (and (consp x1) (consp (cdr x1))) (cddr x1) nil))
             (lenb (fn-wg-take 4 x2))
             (x3 (fn-wg-drop 4 x2))
             (n (fn-wg-be-value lenb))
             (payload (fn-wg-take n x3))
             (x4 (fn-wg-drop n x3))
             (trailer (fn-wg-take 32 x4)))
        (if (not (and (<= 4 (len xs))
                      (equal m (fn-wg-arg 1 g))
                      (consp x1) (consp (cdr x1))
                      (equal version (fn-wg-arg 2 g))
                      (equal kind (fn-wg-arg 3 g))
                      (<= 4 (len x2))
                      (fn-cbor-octet-listp lenb)
                      (<= n (nfix (fn-wg-arg 4 g)))
                      (<= (+ n 32) (len x3))
                      (fn-cbor-octet-listp payload)
                      (fn-cbor-octet-listp trailer)))
            (fn-wg-malformed)
          (if (not (equal trailer
                          (fn-frame-digest (fn-wg-frame-protected m version kind payload))))
              (fn-wg-refused :trailer)
            (let ((r (fn-wg-decode (fn-wg-arg 5 g) payload)))
              (cond ((not (fn-wg-okp r)) r)
                    ((consp (fn-wg-rest r)) (fn-wg-malformed))
                    (t (fn-wg-ok (fn-wg-value r) (fn-wg-drop 32 x4))))))))))
  :hints (("Goal" :expand ((fn-wg-decode g xs)))))

(defthm fn-wg-encode-opener-const
  (implies (equal (fn-wg-op g) :const)
           (equal (fn-wg-encode g v)
                  (fn-wg-arg 1 g)))
  :hints (("Goal" :expand ((fn-wg-encode g v)))))

(defthm fn-wg-encode-opener-uint
  (implies (equal (fn-wg-op g) :uint)
           (equal (fn-wg-encode g v)
                  (fn-wg-be-bytes (nfix (fn-wg-arg 1 g)) (nfix v))))
  :hints (("Goal" :expand ((fn-wg-encode g v)))))

(defthm fn-wg-encode-opener-bytes
  (implies (equal (fn-wg-op g) :bytes)
           (equal (fn-wg-encode g v)
                  (fn-wg-app (fn-wg-be-bytes (nfix (fn-wg-arg 1 g)) (len v)) v)))
  :hints (("Goal" :expand ((fn-wg-encode g v)))))

(defthm fn-wg-encode-opener-rest
  (implies (equal (fn-wg-op g) :rest)
           (equal (fn-wg-encode g v)
                  v))
  :hints (("Goal" :expand ((fn-wg-encode g v)))))

(defthm fn-wg-encode-opener-line
  (implies (equal (fn-wg-op g) :line)
           (equal (fn-wg-encode g v)
                  (fn-wg-app v (list 13 10))))
  :hints (("Goal" :expand ((fn-wg-encode g v)))))

(defthm fn-wg-encode-opener-base64-lines
  (implies (equal (fn-wg-op g) :base64-lines)
           (equal (fn-wg-encode g v)
                  (fn-wg-lines (nfix (fn-wg-arg 1 g)) (fn-ot-b64-encode v))))
  :hints (("Goal" :expand ((fn-wg-encode g v)))))

(defthm fn-wg-encode-opener-enum
  (implies (equal (fn-wg-op g) :enum)
           (equal (fn-wg-encode g v)
                  (fn-wg-be-bytes (nfix (fn-wg-arg 1 g))
                      (+ (nfix (fn-wg-arg 2 g)) (fn-wg-position v (fn-wg-arg 3 g))))))
  :hints (("Goal" :expand ((fn-wg-encode g v)))))

(defthm fn-wg-encode-opener-seq
  (implies (equal (fn-wg-op g) :seq)
           (equal (fn-wg-encode g v)
                  (if (and (consp g) (consp (cdr g)))
          (fn-wg-app (fn-wg-encode (fn-wg-arg 1 g) (if (consp v) (car v) nil))
                     (fn-wg-encode (fn-wg-next g) (if (consp v) (cdr v) nil)))
        nil)))
  :hints (("Goal" :expand ((fn-wg-encode g v)))))

(defthm fn-wg-encode-opener-tag
  (implies (equal (fn-wg-op g) :tag)
           (equal (fn-wg-encode g v)
                  (if (and (consp g) (consp (cdr g)) (consp (cddr g)))
          (if (equal (if (consp v) (car v) nil) (fn-wg-arg 1 (fn-wg-arg 2 g)))
              (fn-wg-app (fn-wg-be-bytes (nfix (fn-wg-arg 1 g))
                                         (nfix (fn-wg-arg 0 (fn-wg-arg 2 g))))
                         (fn-wg-encode (fn-wg-arg 2 (fn-wg-arg 2 g))
                                       (if (and (consp v) (consp (cdr v))) (cadr v) nil)))
            (fn-wg-encode (fn-wg-tag-next g) v))
        nil)))
  :hints (("Goal" :expand ((fn-wg-encode g v)))))

(defthm fn-wg-encode-opener-maybe
  (implies (equal (fn-wg-op g) :maybe)
           (equal (fn-wg-encode g v)
                  (if (consp v) (fn-wg-encode (fn-wg-arg 1 g) (car v)) nil)))
  :hints (("Goal" :expand ((fn-wg-encode g v)))))

(defthm fn-wg-encode-opener-where
  (implies (equal (fn-wg-op g) :where)
           (equal (fn-wg-encode g v)
                  (fn-wg-encode (fn-wg-arg 1 g) v)))
  :hints (("Goal" :expand ((fn-wg-encode g v)))))

(defthm fn-wg-encode-opener-frame
  (implies (equal (fn-wg-op g) :frame)
           (equal (fn-wg-encode g v)
                  (let ((prot (fn-wg-frame-protected (fn-wg-arg 1 g) (fn-wg-arg 2 g) (fn-wg-arg 3 g)
                                         (fn-wg-encode (fn-wg-arg 5 g) v))))
        (fn-wg-app prot (fn-frame-digest prot)))))
  :hints (("Goal" :expand ((fn-wg-encode g v)))))

(defthm fn-wg-valuep-opener-const
  (implies (equal (fn-wg-op g) :const)
           (equal (fn-wg-valuep g v)
                  (null v)))
  :hints (("Goal" :expand ((fn-wg-valuep g v)))))

(defthm fn-wg-valuep-opener-uint
  (implies (equal (fn-wg-op g) :uint)
           (equal (fn-wg-valuep g v)
                  (and (natp v) (<= (nfix (fn-wg-arg 2 g)) v) (<= v (nfix (fn-wg-arg 3 g))))))
  :hints (("Goal" :expand ((fn-wg-valuep g v)))))

(defthm fn-wg-valuep-opener-bytes
  (implies (equal (fn-wg-op g) :bytes)
           (equal (fn-wg-valuep g v)
                  (let ((class (fn-wg-arg (if t 4 3) g))
            (lo (fn-wg-arg (if t 2 1) g))
            (hi (fn-wg-arg (if t 3 2) g)))
        (and (fn-cbor-octet-listp v) (fn-wg-class-okp class v)
             (<= (nfix lo) (len v)) (<= (len v) (nfix hi))))))
  :hints (("Goal" :expand ((fn-wg-valuep g v)))))

(defthm fn-wg-valuep-opener-line
  (implies (equal (fn-wg-op g) :line)
           (equal (fn-wg-valuep g v)
                  (let ((class (fn-wg-arg (if nil 4 3) g))
            (lo (fn-wg-arg (if nil 2 1) g))
            (hi (fn-wg-arg (if nil 3 2) g)))
        (and (fn-cbor-octet-listp v) (fn-wg-class-okp class v)
             (<= (nfix lo) (len v)) (<= (len v) (nfix hi))))))
  :hints (("Goal" :expand ((fn-wg-valuep g v)))))

(defthm fn-wg-valuep-opener-rest
  (implies (equal (fn-wg-op g) :rest)
           (equal (fn-wg-valuep g v)
                  (and (fn-cbor-octet-listp v) (fn-wg-class-okp (fn-wg-arg 3 g) v)
           (<= (nfix (fn-wg-arg 1 g)) (len v)) (<= (len v) (nfix (fn-wg-arg 2 g))))))
  :hints (("Goal" :expand ((fn-wg-valuep g v)))))

(defthm fn-wg-valuep-opener-base64-lines
  (implies (equal (fn-wg-op g) :base64-lines)
           (equal (fn-wg-valuep g v)
                  (and (fn-cbor-octet-listp v)
           (<= (nfix (fn-wg-arg 2 g)) (len v)) (<= (len v) (nfix (fn-wg-arg 3 g))))))
  :hints (("Goal" :expand ((fn-wg-valuep g v)))))

(defthm fn-wg-valuep-opener-enum
  (implies (equal (fn-wg-op g) :enum)
           (equal (fn-wg-valuep g v)
                  (and (true-listp (fn-wg-arg 3 g)) (member-equal v (fn-wg-arg 3 g)))))
  :hints (("Goal" :expand ((fn-wg-valuep g v)))))

(defthm fn-wg-valuep-opener-seq
  (implies (equal (fn-wg-op g) :seq)
           (equal (fn-wg-valuep g v)
                  (if (and (consp g) (consp (cdr g)))
          (and (consp v)
               (fn-wg-valuep (fn-wg-arg 1 g) (car v))
               (fn-wg-valuep (fn-wg-next g) (cdr v)))
        (null v))))
  :hints (("Goal" :expand ((fn-wg-valuep g v)))))

(defthm fn-wg-valuep-opener-tag
  (implies (equal (fn-wg-op g) :tag)
           (equal (fn-wg-valuep g v)
                  (if (and (consp g) (consp (cdr g)) (consp (cddr g)))
          (and (true-listp v) (equal (len v) 2)
               (if (equal (car v) (fn-wg-arg 1 (fn-wg-arg 2 g)))
                   (fn-wg-valuep (fn-wg-arg 2 (fn-wg-arg 2 g)) (cadr v))
                 (fn-wg-valuep (fn-wg-tag-next g) v)))
        nil)))
  :hints (("Goal" :expand ((fn-wg-valuep g v)))))

(defthm fn-wg-valuep-opener-maybe
  (implies (equal (fn-wg-op g) :maybe)
           (equal (fn-wg-valuep g v)
                  (or (null v)
          (and (consp v) (null (cdr v)) (fn-wg-valuep (fn-wg-arg 1 g) (car v))))))
  :hints (("Goal" :expand ((fn-wg-valuep g v)))))

(defthm fn-wg-valuep-opener-where
  (implies (equal (fn-wg-op g) :where)
           (equal (fn-wg-valuep g v)
                  (and (fn-wg-valuep (fn-wg-arg 1 g) v) (fn-wg-checks-okp (fn-wg-where-checks g) v))))
  :hints (("Goal" :expand ((fn-wg-valuep g v)))))

(defthm fn-wg-valuep-opener-frame
  (implies (equal (fn-wg-op g) :frame)
           (equal (fn-wg-valuep g v)
                  (and (fn-wg-valuep (fn-wg-arg 5 g) v)
           (<= (len (fn-wg-encode (fn-wg-arg 5 g) v)) (nfix (fn-wg-arg 4 g))))))
  :hints (("Goal" :expand ((fn-wg-valuep g v)))))

(defthm fn-wg-delimitedp-opener-const
  (implies (equal (fn-wg-op g) :const)
           (equal (fn-wg-delimitedp g)
                  t))
  :hints (("Goal" :expand ((fn-wg-delimitedp g)))))

(defthm fn-wg-delimitedp-opener-uint
  (implies (equal (fn-wg-op g) :uint)
           (equal (fn-wg-delimitedp g)
                  t))
  :hints (("Goal" :expand ((fn-wg-delimitedp g)))))

(defthm fn-wg-delimitedp-opener-bytes
  (implies (equal (fn-wg-op g) :bytes)
           (equal (fn-wg-delimitedp g)
                  t))
  :hints (("Goal" :expand ((fn-wg-delimitedp g)))))

(defthm fn-wg-delimitedp-opener-line
  (implies (equal (fn-wg-op g) :line)
           (equal (fn-wg-delimitedp g)
                  t))
  :hints (("Goal" :expand ((fn-wg-delimitedp g)))))

(defthm fn-wg-delimitedp-opener-enum
  (implies (equal (fn-wg-op g) :enum)
           (equal (fn-wg-delimitedp g)
                  t))
  :hints (("Goal" :expand ((fn-wg-delimitedp g)))))

(defthm fn-wg-delimitedp-opener-frame
  (implies (equal (fn-wg-op g) :frame)
           (equal (fn-wg-delimitedp g)
                  t))
  :hints (("Goal" :expand ((fn-wg-delimitedp g)))))

(defthm fn-wg-delimitedp-opener-seq
  (implies (equal (fn-wg-op g) :seq)
           (equal (fn-wg-delimitedp g)
                  (if (and (consp g) (consp (cdr g)))
               (and (fn-wg-delimitedp (fn-wg-arg 1 g))
                    (fn-wg-delimitedp (fn-wg-next g)))
             t)))
  :hints (("Goal" :expand ((fn-wg-delimitedp g)))))

(defthm fn-wg-delimitedp-opener-tag
  (implies (equal (fn-wg-op g) :tag)
           (equal (fn-wg-delimitedp g)
                  (if (and (consp g) (consp (cdr g)) (consp (cddr g)))
               (and (fn-wg-delimitedp (fn-wg-arg 2 (fn-wg-arg 2 g)))
                    (fn-wg-delimitedp (fn-wg-tag-next g)))
             t)))
  :hints (("Goal" :expand ((fn-wg-delimitedp g)))))

(defthm fn-wg-delimitedp-opener-where
  (implies (equal (fn-wg-op g) :where)
           (equal (fn-wg-delimitedp g)
                  (fn-wg-delimitedp (fn-wg-arg 1 g))))
  :hints (("Goal" :expand ((fn-wg-delimitedp g)))))

(defthm fn-wg-nonemptyp-opener-const
  (implies (equal (fn-wg-op g) :const)
           (equal (fn-wg-nonemptyp g)
                  (consp (fn-wg-arg 1 g))))
  :hints (("Goal" :expand ((fn-wg-nonemptyp g)))))

(defthm fn-wg-nonemptyp-opener-uint
  (implies (equal (fn-wg-op g) :uint)
           (equal (fn-wg-nonemptyp g)
                  t))
  :hints (("Goal" :expand ((fn-wg-nonemptyp g)))))

(defthm fn-wg-nonemptyp-opener-bytes
  (implies (equal (fn-wg-op g) :bytes)
           (equal (fn-wg-nonemptyp g)
                  t))
  :hints (("Goal" :expand ((fn-wg-nonemptyp g)))))

(defthm fn-wg-nonemptyp-opener-line
  (implies (equal (fn-wg-op g) :line)
           (equal (fn-wg-nonemptyp g)
                  t))
  :hints (("Goal" :expand ((fn-wg-nonemptyp g)))))

(defthm fn-wg-nonemptyp-opener-enum
  (implies (equal (fn-wg-op g) :enum)
           (equal (fn-wg-nonemptyp g)
                  t))
  :hints (("Goal" :expand ((fn-wg-nonemptyp g)))))

(defthm fn-wg-nonemptyp-opener-frame
  (implies (equal (fn-wg-op g) :frame)
           (equal (fn-wg-nonemptyp g)
                  t))
  :hints (("Goal" :expand ((fn-wg-nonemptyp g)))))

(defthm fn-wg-nonemptyp-opener-tag
  (implies (equal (fn-wg-op g) :tag)
           (equal (fn-wg-nonemptyp g)
                  t))
  :hints (("Goal" :expand ((fn-wg-nonemptyp g)))))

(defthm fn-wg-nonemptyp-opener-rest
  (implies (equal (fn-wg-op g) :rest)
           (equal (fn-wg-nonemptyp g)
                  (posp (fn-wg-arg (if t 1 2) g))))
  :hints (("Goal" :expand ((fn-wg-nonemptyp g)))))

(defthm fn-wg-nonemptyp-opener-base64-lines
  (implies (equal (fn-wg-op g) :base64-lines)
           (equal (fn-wg-nonemptyp g)
                  (posp (fn-wg-arg (if nil 1 2) g))))
  :hints (("Goal" :expand ((fn-wg-nonemptyp g)))))

(defthm fn-wg-nonemptyp-opener-seq
  (implies (equal (fn-wg-op g) :seq)
           (equal (fn-wg-nonemptyp g)
                  (if (and (consp g) (consp (cdr g)))
               (or (fn-wg-nonemptyp (fn-wg-arg 1 g))
                   (fn-wg-nonemptyp (fn-wg-next g)))
             nil)))
  :hints (("Goal" :expand ((fn-wg-nonemptyp g)))))

(defthm fn-wg-nonemptyp-opener-where
  (implies (equal (fn-wg-op g) :where)
           (equal (fn-wg-nonemptyp g)
                  (fn-wg-nonemptyp (fn-wg-arg 1 g))))
  :hints (("Goal" :expand ((fn-wg-nonemptyp g)))))

(defthm fn-wg-grammarp-opener-const
  (implies (equal (fn-wg-op g) :const)
           (equal (fn-wg-grammarp g)
                  (and (true-listp g) (and (equal (len g) 2) (fn-cbor-octet-listp (fn-wg-arg 1 g))))))
  :hints (("Goal" :expand ((fn-wg-grammarp g)))))

(defthm fn-wg-grammarp-opener-uint
  (implies (equal (fn-wg-op g) :uint)
           (equal (fn-wg-grammarp g)
                  (and (true-listp g) (and (equal (len g) 4) (fn-wg-widthp (fn-wg-arg 1 g))
            (natp (fn-wg-arg 2 g)) (natp (fn-wg-arg 3 g))
            (<= (fn-wg-arg 2 g) (fn-wg-arg 3 g))
            (< (fn-wg-arg 3 g) (fn-wg-limit (fn-wg-arg 1 g)))))))
  :hints (("Goal" :expand ((fn-wg-grammarp g)))))

(defthm fn-wg-grammarp-opener-bytes
  (implies (equal (fn-wg-op g) :bytes)
           (equal (fn-wg-grammarp g)
                  (and (true-listp g) (and (equal (len g) 5) (fn-wg-widthp (fn-wg-arg 1 g))
            (natp (fn-wg-arg 2 g)) (natp (fn-wg-arg 3 g))
            (<= (fn-wg-arg 2 g) (fn-wg-arg 3 g))
            (< (fn-wg-arg 3 g) (fn-wg-limit (fn-wg-arg 1 g)))
            (fn-wg-classp (fn-wg-arg 4 g))))))
  :hints (("Goal" :expand ((fn-wg-grammarp g)))))

(defthm fn-wg-grammarp-opener-rest
  (implies (equal (fn-wg-op g) :rest)
           (equal (fn-wg-grammarp g)
                  (and (true-listp g) (and (equal (len g) 4) (natp (fn-wg-arg 1 g)) (natp (fn-wg-arg 2 g))
            (<= (fn-wg-arg 1 g) (fn-wg-arg 2 g)) (fn-wg-classp (fn-wg-arg 3 g))))))
  :hints (("Goal" :expand ((fn-wg-grammarp g)))))

(defthm fn-wg-grammarp-opener-line
  (implies (equal (fn-wg-op g) :line)
           (equal (fn-wg-grammarp g)
                  (and (true-listp g) (and (equal (len g) 4) (natp (fn-wg-arg 1 g)) (natp (fn-wg-arg 2 g))
            (<= (fn-wg-arg 1 g) (fn-wg-arg 2 g)) (equal (fn-wg-arg 3 g) :header)))))
  :hints (("Goal" :expand ((fn-wg-grammarp g)))))

(defthm fn-wg-grammarp-opener-base64-lines
  (implies (equal (fn-wg-op g) :base64-lines)
           (equal (fn-wg-grammarp g)
                  (and (true-listp g) (and (equal (len g) 4) (posp (fn-wg-arg 1 g)) (natp (fn-wg-arg 2 g))
            (natp (fn-wg-arg 3 g)) (<= (fn-wg-arg 2 g) (fn-wg-arg 3 g))))))
  :hints (("Goal" :expand ((fn-wg-grammarp g)))))

(defthm fn-wg-grammarp-opener-enum
  (implies (equal (fn-wg-op g) :enum)
           (equal (fn-wg-grammarp g)
                  (and (true-listp g) (and (equal (len g) 4) (fn-wg-widthp (fn-wg-arg 1 g)) (natp (fn-wg-arg 2 g))
            (symbol-listp (fn-wg-arg 3 g)) (consp (fn-wg-arg 3 g))
            (no-duplicatesp-equal (fn-wg-arg 3 g))
            (<= (+ (fn-wg-arg 2 g) (len (fn-wg-arg 3 g))) (fn-wg-limit (fn-wg-arg 1 g)))))))
  :hints (("Goal" :expand ((fn-wg-grammarp g)))))

(defthm fn-wg-grammarp-opener-seq
  (implies (equal (fn-wg-op g) :seq)
           (equal (fn-wg-grammarp g)
                  (and (true-listp g) (if (consp (cdr g))
           (and (fn-wg-grammarp (fn-wg-arg 1 g))
                (or (not (consp (cddr g))) (fn-wg-delimitedp (fn-wg-arg 1 g)))
                (fn-wg-grammarp (fn-wg-next g)))
         t))))
  :hints (("Goal" :expand ((fn-wg-grammarp g)))))

(defthm fn-wg-grammarp-opener-tag
  (implies (equal (fn-wg-op g) :tag)
           (equal (fn-wg-grammarp g)
                  (and (true-listp g) (and (consp (cdr g)) (fn-wg-widthp (fn-wg-arg 1 g))
            (if (consp (cddr g))
                (and (fn-wg-armp (fn-wg-arg 2 g) (fn-wg-arg 1 g))
                     (fn-wg-grammarp (fn-wg-arg 2 (fn-wg-arg 2 g)))
                     (not (member-equal (fn-wg-arg 0 (fn-wg-arg 2 g))
                                        (fn-wg-tag-codes (fn-wg-tag-next g))))
                     (not (member-equal (fn-wg-arg 1 (fn-wg-arg 2 g))
                                        (fn-wg-tag-names (fn-wg-tag-next g))))
                     (fn-wg-grammarp (fn-wg-tag-next g)))
              t)))))
  :hints (("Goal" :expand ((fn-wg-grammarp g)))))

(defthm fn-wg-grammarp-opener-maybe
  (implies (equal (fn-wg-op g) :maybe)
           (equal (fn-wg-grammarp g)
                  (and (true-listp g) (and (equal (len g) 2) (fn-wg-grammarp (fn-wg-arg 1 g))
            (fn-wg-nonemptyp (fn-wg-arg 1 g))))))
  :hints (("Goal" :expand ((fn-wg-grammarp g)))))

(defthm fn-wg-grammarp-opener-where
  (implies (equal (fn-wg-op g) :where)
           (equal (fn-wg-grammarp g)
                  (and (true-listp g) (and (consp (cdr g)) (fn-wg-grammarp (fn-wg-arg 1 g))
            (equal (fn-wg-op (fn-wg-arg 1 g)) :seq)
            (fn-wg-check-listp (cddr g))))))
  :hints (("Goal" :expand ((fn-wg-grammarp g)))))

(defthm fn-wg-grammarp-opener-frame
  (implies (equal (fn-wg-op g) :frame)
           (equal (fn-wg-grammarp g)
                  (and (true-listp g) (and (equal (len g) 6)
            (fn-cbor-octet-listp (fn-wg-arg 1 g)) (equal (len (fn-wg-arg 1 g)) 4)
            (fn-cbor-octetp (fn-wg-arg 2 g)) (fn-cbor-octetp (fn-wg-arg 3 g))
            (natp (fn-wg-arg 4 g)) (< (fn-wg-arg 4 g) (fn-wg-limit 4))
            (fn-wg-grammarp (fn-wg-arg 5 g))))))
  :hints (("Goal" :expand ((fn-wg-grammarp g)))))
;; END GENERATED OPENERS


; The :seq and :tag openers stay closed: their recursion is along the same
; node kind (fn-wg-next, fn-wg-tag-next), and an open opener would unroll a
; whole element or arm list.  A proof about one opens it by :expand.
(in-theory (disable fn-wg-decode-opener-seq fn-wg-encode-opener-seq fn-wg-valuep-opener-seq fn-wg-delimitedp-opener-seq fn-wg-nonemptyp-opener-seq fn-wg-grammarp-opener-seq fn-wg-decode-opener-tag fn-wg-encode-opener-tag fn-wg-valuep-opener-tag fn-wg-delimitedp-opener-tag fn-wg-nonemptyp-opener-tag fn-wg-grammarp-opener-tag))

(defthm fn-wg-nonemptyp-of-tag
  (implies (equal (fn-wg-op g) :tag) (fn-wg-nonemptyp g))
  :hints (("Goal" :expand ((fn-wg-nonemptyp g)))))
(defthm fn-wg-nonemptyp-of-maybe
  (implies (equal (fn-wg-op g) :maybe) (not (fn-wg-nonemptyp g)))
  :hints (("Goal" :expand ((fn-wg-nonemptyp g)))))
(defthm fn-wg-delimitedp-of-tail-nodes
  (implies (member-equal (fn-wg-op g) '(:rest :maybe :base64-lines))
           (not (fn-wg-delimitedp g)))
  :hints (("Goal" :expand ((fn-wg-delimitedp g)))))

(defthm fn-wg-empty-seq
  (implies (and (equal (fn-wg-op g) :seq) (not (consp (cdr g))))
           (and (equal (fn-wg-encode g v) nil)
                (equal (fn-wg-valuep g v) (null v))
                (fn-wg-delimitedp g)
                (not (fn-wg-nonemptyp g))
                (equal (fn-wg-decode g xs) (fn-wg-ok nil xs))))
  :hints (("Goal" :expand ((fn-wg-encode g v) (fn-wg-valuep g v) (fn-wg-delimitedp g)
                           (fn-wg-nonemptyp g) (fn-wg-decode g xs)))))
(defthm fn-wg-empty-tag
  (implies (and (equal (fn-wg-op g) :tag) (not (consp (cddr g))))
           (and (equal (fn-wg-encode g v) nil)
                (not (fn-wg-valuep g v))
                (fn-wg-delimitedp g)
                (equal (fn-wg-tag-codes g) nil)
                (equal (fn-wg-tag-names g) nil)
                (equal (fn-wg-decode g xs) (fn-wg-malformed))))
  :hints (("Goal" :expand ((fn-wg-encode g v) (fn-wg-valuep g v) (fn-wg-delimitedp g)
                           (fn-wg-tag-codes g) (fn-wg-tag-names g) (fn-wg-decode g xs)))))

(defthm fn-wg-grammarp-of-unknown-op
  (implies (not (member-equal (fn-wg-op g)
                              '(:const :uint :bytes :rest :line :base64-lines :enum
                                :seq :tag :maybe :where :frame)))
           (not (fn-wg-grammarp g)))
  :hints (("Goal" :expand ((fn-wg-grammarp g)))))

(in-theory (disable (:definition fn-wg-decode) (:definition fn-wg-encode)
                    (:definition fn-wg-valuep) (:definition fn-wg-grammarp)
                    (:definition fn-wg-delimitedp) (:definition fn-wg-nonemptyp)))

(defthm fn-wg-encode-octets
  (implies (and (fn-wg-grammarp g) (fn-wg-valuep g v))
           (fn-cbor-octet-listp (fn-wg-encode g v)))
  :hints (("Goal" :induct (fn-wg-encode g v)
           :expand ((fn-wg-encode g v) (fn-wg-valuep g v) (fn-wg-grammarp g)
                    (fn-wg-nonemptyp g)))))

(defthm fn-wg-encode-nonempty
  (implies (and (fn-wg-grammarp g) (fn-wg-valuep g v) (fn-wg-nonemptyp g))
           (consp (fn-wg-encode g v)))
  :hints (("Goal" :induct (fn-wg-encode g v)
           :expand ((fn-wg-encode g v) (fn-wg-valuep g v) (fn-wg-grammarp g)
                    (fn-wg-nonemptyp g)))))

(defthm fn-wg-take-of-app-shorter
  (implies (<= (nfix n) (len xs))
           (equal (fn-wg-take n (fn-wg-app xs ys)) (fn-wg-take n xs)))
  :hints (("Goal" :induct (fn-wg-take n xs))))

(defun fn-wg-tag-code (g v)
  (declare (xargs :guard t :measure (acl2-count g) :verify-guards nil))
  (if (and (consp g) (consp (cdr g)) (consp (cddr g)))
      (if (equal (if (consp v) (car v) nil) (fn-wg-arg 1 (fn-wg-arg 2 g)))
          (fn-wg-arg 0 (fn-wg-arg 2 g))
        (fn-wg-tag-code (fn-wg-tag-next g) v))
    0))
(defthm fn-wg-tag-encode-head
  (implies (and (equal (fn-wg-op g) :tag) (fn-wg-grammarp g) (fn-wg-valuep g v))
           (and (equal (fn-wg-take (fn-wg-arg 1 g) (fn-wg-encode g v))
                       (fn-wg-be-bytes (fn-wg-arg 1 g) (fn-wg-tag-code g v)))
                (<= (fn-wg-arg 1 g) (len (fn-wg-encode g v)))
                (member-equal (fn-wg-tag-code g v) (fn-wg-tag-codes g))
                (natp (fn-wg-tag-code g v))
                (< (fn-wg-tag-code g v) (fn-wg-limit (fn-wg-arg 1 g)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-wg-tag-code g v)
           :expand ((fn-wg-grammarp g) (fn-wg-encode g v) (fn-wg-valuep g v) (fn-wg-tag-codes g)))))

(defthm fn-wg-list-of-two
  (implies (and (consp v) (true-listp (cdr v)) (equal (len (cdr v)) 1))
           (equal (list (car v) (cadr v)) v))
  :hints (("Goal" :expand ((len (cdr v)) (len (cddr v)) (true-listp (cdr v)) (true-listp (cddr v))))))

(defthm fn-wg-plus-cancel
  (equal (+ a (- a) p) (fix p)))
(defthm fn-wg-symbol-listp-true-list-fix
  (implies (symbol-listp x) (equal (true-list-fix x) x)))
(defthm fn-wg-nth-position-of-member
  (implies (member-equal v names)
           (equal (nth (fn-wg-position v names) names) v)))
(defthm fn-wg-position-bound
  (implies (member-equal v names) (< (fn-wg-position v names) (len names)))
  :rule-classes :linear)

(defthm fn-wg-decode-of-encode-const
  (implies (and (equal (fn-wg-op g) :const) (fn-wg-grammarp g) (fn-wg-valuep g v)
                (fn-cbor-octet-listp r))
           (equal (fn-wg-decode g (fn-wg-app (fn-wg-encode g v) r))
                  (fn-wg-ok v r)))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-wg-grammarp g) (fn-wg-encode g v) (fn-wg-valuep g v)
                           (:free (x) (fn-wg-decode g x))))))

(defthm fn-wg-decode-of-encode-uint
  (implies (and (equal (fn-wg-op g) :uint) (fn-wg-grammarp g) (fn-wg-valuep g v)
                (fn-cbor-octet-listp r))
           (equal (fn-wg-decode g (fn-wg-app (fn-wg-encode g v) r))
                  (fn-wg-ok v r)))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-wg-grammarp g) (fn-wg-encode g v) (fn-wg-valuep g v)
                           (:free (x) (fn-wg-decode g x))))))

(defthm fn-wg-decode-of-encode-bytes
  (implies (and (equal (fn-wg-op g) :bytes) (fn-wg-grammarp g) (fn-wg-valuep g v)
                (fn-cbor-octet-listp r))
           (equal (fn-wg-decode g (fn-wg-app (fn-wg-encode g v) r))
                  (fn-wg-ok v r)))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-wg-grammarp g) (fn-wg-encode g v) (fn-wg-valuep g v)
                           (:free (x) (fn-wg-decode g x))))))

(defthm fn-wg-decode-of-encode-rest
  (implies (and (equal (fn-wg-op g) :rest) (fn-wg-grammarp g) (fn-wg-valuep g v)
                (fn-cbor-octet-listp r)
                (null r))
           (equal (fn-wg-decode g (fn-wg-app (fn-wg-encode g v) r))
                  (fn-wg-ok v r)))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-wg-grammarp g) (fn-wg-encode g v) (fn-wg-valuep g v)
                           (:free (x) (fn-wg-decode g x))))))

(defthm fn-wg-decode-of-encode-line
  (implies (and (equal (fn-wg-op g) :line) (fn-wg-grammarp g) (fn-wg-valuep g v)
                (fn-cbor-octet-listp r))
           (equal (fn-wg-decode g (fn-wg-app (fn-wg-encode g v) r))
                  (fn-wg-ok v r)))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-wg-grammarp g) (fn-wg-encode g v) (fn-wg-valuep g v)
                           (:free (x) (fn-wg-decode g x))))))

(defthm fn-wg-decode-of-encode-base64-lines
  (implies (and (equal (fn-wg-op g) :base64-lines) (fn-wg-grammarp g) (fn-wg-valuep g v)
                (fn-cbor-octet-listp r)
                (null r))
           (equal (fn-wg-decode g (fn-wg-app (fn-wg-encode g v) r))
                  (fn-wg-ok v r)))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-wg-grammarp g) (fn-wg-encode g v) (fn-wg-valuep g v)
                           (:free (x) (fn-wg-decode g x))))))

(defthm fn-wg-decode-of-encode-enum
  (implies (and (equal (fn-wg-op g) :enum) (fn-wg-grammarp g) (fn-wg-valuep g v)
                (fn-cbor-octet-listp r))
           (equal (fn-wg-decode g (fn-wg-app (fn-wg-encode g v) r))
                  (fn-wg-ok v r)))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-wg-grammarp g) (fn-wg-encode g v) (fn-wg-valuep g v)
                           (:free (x) (fn-wg-decode g x))))))

(defthm fn-wg-decode-of-encode-seq
  (implies (and (equal (fn-wg-op g) :seq) (consp g) (consp (cdr g))
                (fn-wg-grammarp g) (fn-wg-valuep g v) (fn-cbor-octet-listp r)
                (or (fn-wg-delimitedp g) (null r))
                (implies (and (fn-wg-grammarp (fn-wg-arg 1 g)) (fn-wg-valuep (fn-wg-arg 1 g) (car v))
                         (fn-cbor-octet-listp (fn-wg-app (fn-wg-encode (fn-wg-next g) (cdr v)) r))
                         (or (fn-wg-delimitedp (fn-wg-arg 1 g)) (null (fn-wg-app (fn-wg-encode (fn-wg-next g) (cdr v)) r))))
                    (equal (fn-wg-decode (fn-wg-arg 1 g) (fn-wg-app (fn-wg-encode (fn-wg-arg 1 g) (car v)) (fn-wg-app (fn-wg-encode (fn-wg-next g) (cdr v)) r)))
                           (fn-wg-ok (car v) (fn-wg-app (fn-wg-encode (fn-wg-next g) (cdr v)) r))))
                (implies (and (fn-wg-grammarp (fn-wg-next g)) (fn-wg-valuep (fn-wg-next g) (cdr v))
                         (fn-cbor-octet-listp r)
                         (or (fn-wg-delimitedp (fn-wg-next g)) (null r)))
                    (equal (fn-wg-decode (fn-wg-next g) (fn-wg-app (fn-wg-encode (fn-wg-next g) (cdr v)) r))
                           (fn-wg-ok (cdr v) r))))
           (equal (fn-wg-decode g (fn-wg-app (fn-wg-encode g v) r)) (fn-wg-ok v r)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-wg-decode-opener-seq fn-wg-encode-opener-seq fn-wg-valuep-opener-seq fn-wg-delimitedp-opener-seq fn-wg-nonemptyp-opener-seq fn-wg-grammarp-opener-seq) :expand ((fn-wg-grammarp g) (fn-wg-encode g v) (fn-wg-valuep g v)
                           (fn-wg-delimitedp g)
                           (:free (x) (fn-wg-decode g x))))))

(defthm fn-wg-decode-of-encode-tag-hit
  (implies (and (equal (fn-wg-op g) :tag) (consp g) (consp (cdr g)) (consp (cddr g))
                (equal (if (consp v) (car v) nil) (fn-wg-arg 1 (fn-wg-arg 2 g)))
                (fn-wg-grammarp g) (fn-wg-valuep g v) (fn-cbor-octet-listp r)
                (or (fn-wg-delimitedp g) (null r))
                (implies (and (fn-wg-grammarp (fn-wg-arg 2 (fn-wg-arg 2 g))) (fn-wg-valuep (fn-wg-arg 2 (fn-wg-arg 2 g)) (cadr v))
                         (fn-cbor-octet-listp r)
                         (or (fn-wg-delimitedp (fn-wg-arg 2 (fn-wg-arg 2 g))) (null r)))
                    (equal (fn-wg-decode (fn-wg-arg 2 (fn-wg-arg 2 g)) (fn-wg-app (fn-wg-encode (fn-wg-arg 2 (fn-wg-arg 2 g)) (cadr v)) r))
                           (fn-wg-ok (cadr v) r))))
           (equal (fn-wg-decode g (fn-wg-app (fn-wg-encode g v) r)) (fn-wg-ok v r)))
  :rule-classes nil
  :otf-flg t
  :hints (("Goal" :in-theory (disable fn-wg-decode-opener-tag fn-wg-encode-opener-tag fn-wg-valuep-opener-tag fn-wg-delimitedp-opener-tag fn-wg-nonemptyp-opener-tag fn-wg-grammarp-opener-tag) :do-not (quote (generalize fertilize eliminate-destructors)) :do-not-induct t :expand ((fn-wg-grammarp g) (fn-wg-encode g v) (fn-wg-valuep g v)
                           (fn-wg-delimitedp g)
                           (:free (x) (fn-wg-decode g x))))))

(defthm fn-wg-decode-of-encode-tag-miss
  (implies (and (equal (fn-wg-op g) :tag) (consp g) (consp (cdr g)) (consp (cddr g))
                (not (equal (if (consp v) (car v) nil) (fn-wg-arg 1 (fn-wg-arg 2 g))))
                (fn-wg-grammarp g) (fn-wg-valuep g v) (fn-cbor-octet-listp r)
                (or (fn-wg-delimitedp g) (null r))
                (implies (and (fn-wg-grammarp (fn-wg-tag-next g)) (fn-wg-valuep (fn-wg-tag-next g) v)
                         (fn-cbor-octet-listp r)
                         (or (fn-wg-delimitedp (fn-wg-tag-next g)) (null r)))
                    (equal (fn-wg-decode (fn-wg-tag-next g) (fn-wg-app (fn-wg-encode (fn-wg-tag-next g) v) r))
                           (fn-wg-ok v r))))
           (equal (fn-wg-decode g (fn-wg-app (fn-wg-encode g v) r)) (fn-wg-ok v r)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-wg-decode-opener-tag fn-wg-encode-opener-tag fn-wg-valuep-opener-tag fn-wg-delimitedp-opener-tag fn-wg-nonemptyp-opener-tag fn-wg-grammarp-opener-tag) :use ((:instance fn-wg-tag-encode-head (g (fn-wg-tag-next g))))
           :expand ((fn-wg-grammarp g) (fn-wg-encode g v) (fn-wg-valuep g v)
                           (fn-wg-delimitedp g) (fn-wg-tag-codes g)
                           (:free (x) (fn-wg-decode g x))))))

(defthm fn-wg-decode-of-encode-maybe
  (implies (and (equal (fn-wg-op g) :maybe)
                (fn-wg-grammarp g) (fn-wg-valuep g v) (fn-cbor-octet-listp r)
                (or (fn-wg-delimitedp g) (null r))
                (implies (and (fn-wg-grammarp (fn-wg-arg 1 g)) (fn-wg-valuep (fn-wg-arg 1 g) (car v))
                         (fn-cbor-octet-listp r)
                         (or (fn-wg-delimitedp (fn-wg-arg 1 g)) (null r)))
                    (equal (fn-wg-decode (fn-wg-arg 1 g) (fn-wg-app (fn-wg-encode (fn-wg-arg 1 g) (car v)) r))
                           (fn-wg-ok (car v) r))))
           (equal (fn-wg-decode g (fn-wg-app (fn-wg-encode g v) r)) (fn-wg-ok v r)))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-wg-grammarp g) (fn-wg-encode g v) (fn-wg-valuep g v)
                           (fn-wg-delimitedp g)
                           (:free (x) (fn-wg-decode g x))))))

(defthm fn-wg-decode-of-encode-where
  (implies (and (equal (fn-wg-op g) :where)
                (fn-wg-grammarp g) (fn-wg-valuep g v) (fn-cbor-octet-listp r)
                (or (fn-wg-delimitedp g) (null r))
                (implies (and (fn-wg-grammarp (fn-wg-arg 1 g)) (fn-wg-valuep (fn-wg-arg 1 g) v)
                         (fn-cbor-octet-listp r)
                         (or (fn-wg-delimitedp (fn-wg-arg 1 g)) (null r)))
                    (equal (fn-wg-decode (fn-wg-arg 1 g) (fn-wg-app (fn-wg-encode (fn-wg-arg 1 g) v) r))
                           (fn-wg-ok v r))))
           (equal (fn-wg-decode g (fn-wg-app (fn-wg-encode g v) r)) (fn-wg-ok v r)))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-wg-grammarp g) (fn-wg-encode g v) (fn-wg-valuep g v)
                           (fn-wg-delimitedp g)
                           (:free (x) (fn-wg-decode g x))))))

(defthm fn-wg-decode-of-encode-frame
  (implies (and (equal (fn-wg-op g) :frame)
                (fn-wg-grammarp g) (fn-wg-valuep g v) (fn-cbor-octet-listp r)
                (or (fn-wg-delimitedp g) (null r))
                (implies (and (fn-wg-grammarp (fn-wg-arg 5 g)) (fn-wg-valuep (fn-wg-arg 5 g) v)
                         (fn-cbor-octet-listp nil)
                         (or (fn-wg-delimitedp (fn-wg-arg 5 g)) (null nil)))
                    (equal (fn-wg-decode (fn-wg-arg 5 g) (fn-wg-app (fn-wg-encode (fn-wg-arg 5 g) v) nil))
                           (fn-wg-ok v nil))))
           (equal (fn-wg-decode g (fn-wg-app (fn-wg-encode g v) r)) (fn-wg-ok v r)))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-wg-grammarp g) (fn-wg-encode g v) (fn-wg-valuep g v)
                           (fn-wg-delimitedp g)
                           (:free (x) (fn-wg-decode g x))))))

(defthm fn-wg-grammarp-op
  (implies (fn-wg-grammarp g)
           (or (equal (fn-wg-op g) :const) (equal (fn-wg-op g) :uint)
               (equal (fn-wg-op g) :bytes) (equal (fn-wg-op g) :rest)
               (equal (fn-wg-op g) :line) (equal (fn-wg-op g) :base64-lines)
               (equal (fn-wg-op g) :enum) (equal (fn-wg-op g) :seq)
               (equal (fn-wg-op g) :tag) (equal (fn-wg-op g) :maybe)
               (equal (fn-wg-op g) :where) (equal (fn-wg-op g) :frame)))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-wg-grammarp g)))))
(defthm fn-wg-grammarp-seq-tag-shape
  (implies (and (fn-wg-grammarp g) (or (equal (fn-wg-op g) :seq) (equal (fn-wg-op g) :tag)))
           (and (consp g)
                (implies (not (consp (cdr g))) (and (equal (fn-wg-op g) :seq) (null (cdr g))))
                (implies (and (equal (fn-wg-op g) :tag) (not (consp (cddr g)))) (null (cddr g)))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-wg-grammarp g)))))
(defun fn-wg-encode-induction (g v r)
  (declare (xargs :measure (acl2-count g) :verify-guards nil))
  (let ((op (fn-wg-op g)))
    (cond ((equal op :seq)
           (if (and (consp g) (consp (cdr g)))
               (list (fn-wg-encode-induction (fn-wg-arg 1 g) (car v)
                                             (fn-wg-app (fn-wg-encode (fn-wg-next g) (cdr v)) r))
                     (fn-wg-encode-induction (fn-wg-next g) (cdr v) r))
             (list g v r)))
          ((equal op :tag)
           (if (and (consp g) (consp (cdr g)) (consp (cddr g)))
               (if (equal (if (consp v) (car v) nil) (fn-wg-arg 1 (fn-wg-arg 2 g)))
                   (fn-wg-encode-induction (fn-wg-arg 2 (fn-wg-arg 2 g)) (cadr v) r)
                 (fn-wg-encode-induction (fn-wg-tag-next g) v r))
             (list g v r)))
          ((equal op :maybe) (fn-wg-encode-induction (fn-wg-arg 1 g) (car v) r))
          ((equal op :where) (fn-wg-encode-induction (fn-wg-arg 1 g) v r))
          ((equal op :frame) (fn-wg-encode-induction (fn-wg-arg 5 g) v nil))
          (t (list g v r)))))


(defthm fn-wg-shape-facts
  (and (implies (member-equal (fn-wg-op g) '(:rest :maybe :base64-lines))
                (not (fn-wg-delimitedp g)))
       (implies (and (equal (fn-wg-op g) :tag) (not (and (consp g) (consp (cdr g)) (consp (cddr g)))))
                (not (fn-wg-valuep g v)))
       (implies (and (equal (fn-wg-op g) :seq) (not (and (consp g) (consp (cdr g))))
                     (fn-wg-valuep g v))
                (equal (fn-wg-decode g (fn-wg-app (fn-wg-encode g v) r)) (fn-wg-ok v r))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-wg-delimitedp g) (fn-wg-valuep g v) (fn-wg-encode g v)
                           (fn-wg-decode g r)))))

; KEYSTONE.  Decoding an encoding answers the value and leaves what followed.
(defthm fn-wg-decode-of-encode
  (implies (and (fn-wg-grammarp g) (fn-wg-valuep g v)
                (fn-cbor-octet-listp r)
                (or (fn-wg-delimitedp g) (null r)))
           (equal (fn-wg-decode g (fn-wg-app (fn-wg-encode g v) r))
                  (fn-wg-ok v r)))
  :hints (("Goal" :induct (fn-wg-encode-induction g v r)
           :in-theory (disable fn-wg-decode fn-wg-encode fn-wg-valuep fn-wg-grammarp
                               fn-wg-delimitedp fn-wg-app fn-wg-ok)
           :do-not '(generalize fertilize eliminate-destructors))
          (and (equal (access clause-id id :pool-lst) '(1))
               (equal (len (access clause-id id :case-lst)) 1)
               (equal (access clause-id id :primes) 0)
               '(:use (fn-wg-shape-facts fn-wg-grammarp-op fn-wg-grammarp-seq-tag-shape fn-wg-decode-of-encode-const fn-wg-decode-of-encode-uint fn-wg-decode-of-encode-bytes fn-wg-decode-of-encode-rest fn-wg-decode-of-encode-line fn-wg-decode-of-encode-base64-lines fn-wg-decode-of-encode-enum fn-wg-decode-of-encode-seq fn-wg-decode-of-encode-tag-hit fn-wg-decode-of-encode-tag-miss fn-wg-decode-of-encode-maybe fn-wg-decode-of-encode-where fn-wg-decode-of-encode-frame)))))

; -----------------------------------------------------------------------------
; Encode of decode

(defthm fn-wg-be-bytes-of-value-take
  (implies (and (fn-cbor-octet-listp (fn-wg-take n xs)) (natp n))
           (equal (fn-wg-be-bytes n (fn-wg-be-value (fn-wg-take n xs)))
                  (fn-wg-take n xs)))
  :hints (("Goal" :use ((:instance fn-wg-be-bytes-of-value (xs (fn-wg-take n xs))))
           :in-theory (disable fn-wg-be-bytes-of-value))))
(defthm fn-wg-member-of-nth
  (implies (and (natp k) (< k (len names)))
           (member-equal (nth k names) names))
  :hints (("Goal" :induct (nth k names))))
(defthm fn-wg-line-split
  (let ((d (fn-wg-drop (len (fn-wg-upto-cr xs)) xs)))
    (implies (and (consp d) (equal 13 (car d)) (consp (cdr d)) (equal 10 (cadr d)))
             (equal (fn-wg-app (fn-wg-upto-cr xs) (list* 13 10 (fn-wg-drop 1 (cdr d))))
                    xs)))
  :hints (("Goal" :use ((:instance fn-wg-prefixp-app-drop (p (fn-wg-upto-cr xs))))
           :expand ((fn-wg-drop 1 (cdr (fn-wg-drop (len (fn-wg-upto-cr xs)) xs))))
           :in-theory (disable fn-wg-prefixp-app-drop))))
(defthm fn-wg-upto-cr-prefix
  (and (fn-wg-prefixp (fn-wg-upto-cr xs) xs)
       (true-listp (fn-wg-upto-cr xs))))
(defthm fn-wg-true-listp-of-unlines
  (true-listp (fn-wg-unlines w xs)))
(defthm fn-wg-header-octets-are-octets
  (implies (fn-wg-header-octetsp xs) (fn-cbor-octet-listp xs)))

(defthm fn-wg-encode-of-decode-const
  (implies (and (equal (fn-wg-op g) :const) (fn-wg-grammarp g) (fn-cbor-octet-listp xs) (fn-wg-okp (fn-wg-decode g xs)))
           (and (fn-wg-valuep g (fn-wg-value (fn-wg-decode g xs)))
                (equal (fn-wg-app (fn-wg-encode g (fn-wg-value (fn-wg-decode g xs))) (fn-wg-rest (fn-wg-decode g xs))) xs)
                (fn-cbor-octet-listp (fn-wg-rest (fn-wg-decode g xs)))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-wg-grammarp g) (:free (x) (fn-wg-decode g x)) (fn-wg-delimitedp g)
                           (:free (v) (fn-wg-encode g v)) (:free (v) (fn-wg-valuep g v))))))
(defthm fn-wg-encode-of-decode-uint
  (implies (and (equal (fn-wg-op g) :uint) (fn-wg-grammarp g) (fn-cbor-octet-listp xs) (fn-wg-okp (fn-wg-decode g xs)))
           (and (fn-wg-valuep g (fn-wg-value (fn-wg-decode g xs)))
                (equal (fn-wg-app (fn-wg-encode g (fn-wg-value (fn-wg-decode g xs))) (fn-wg-rest (fn-wg-decode g xs))) xs)
                (fn-cbor-octet-listp (fn-wg-rest (fn-wg-decode g xs)))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-wg-grammarp g) (:free (x) (fn-wg-decode g x)) (fn-wg-delimitedp g)
                           (:free (v) (fn-wg-encode g v)) (:free (v) (fn-wg-valuep g v))))))
(defthm fn-wg-encode-of-decode-bytes
  (implies (and (equal (fn-wg-op g) :bytes) (fn-wg-grammarp g) (fn-cbor-octet-listp xs) (fn-wg-okp (fn-wg-decode g xs)))
           (and (fn-wg-valuep g (fn-wg-value (fn-wg-decode g xs)))
                (equal (fn-wg-app (fn-wg-encode g (fn-wg-value (fn-wg-decode g xs))) (fn-wg-rest (fn-wg-decode g xs))) xs)
                (fn-cbor-octet-listp (fn-wg-rest (fn-wg-decode g xs)))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-wg-grammarp g) (:free (x) (fn-wg-decode g x)) (fn-wg-delimitedp g)
                           (:free (v) (fn-wg-encode g v)) (:free (v) (fn-wg-valuep g v))))))
(defthm fn-wg-encode-of-decode-rest
  (implies (and (equal (fn-wg-op g) :rest) (fn-wg-grammarp g) (fn-cbor-octet-listp xs) (fn-wg-okp (fn-wg-decode g xs)))
           (and (fn-wg-valuep g (fn-wg-value (fn-wg-decode g xs)))
                (equal (fn-wg-app (fn-wg-encode g (fn-wg-value (fn-wg-decode g xs))) (fn-wg-rest (fn-wg-decode g xs))) xs)
                (fn-cbor-octet-listp (fn-wg-rest (fn-wg-decode g xs)))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-wg-grammarp g) (:free (x) (fn-wg-decode g x)) (fn-wg-delimitedp g)
                           (:free (v) (fn-wg-encode g v)) (:free (v) (fn-wg-valuep g v))))))
(defthm fn-wg-encode-of-decode-line
  (implies (and (equal (fn-wg-op g) :line) (fn-wg-grammarp g) (fn-cbor-octet-listp xs) (fn-wg-okp (fn-wg-decode g xs)))
           (and (fn-wg-valuep g (fn-wg-value (fn-wg-decode g xs)))
                (equal (fn-wg-app (fn-wg-encode g (fn-wg-value (fn-wg-decode g xs))) (fn-wg-rest (fn-wg-decode g xs))) xs)
                (fn-cbor-octet-listp (fn-wg-rest (fn-wg-decode g xs)))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-wg-grammarp g) (:free (x) (fn-wg-decode g x)) (fn-wg-delimitedp g)
                           (:free (v) (fn-wg-encode g v)) (:free (v) (fn-wg-valuep g v))))))
(defthm fn-wg-encode-of-decode-base64-lines
  (implies (and (equal (fn-wg-op g) :base64-lines) (fn-wg-grammarp g) (fn-cbor-octet-listp xs) (fn-wg-okp (fn-wg-decode g xs)))
           (and (fn-wg-valuep g (fn-wg-value (fn-wg-decode g xs)))
                (equal (fn-wg-app (fn-wg-encode g (fn-wg-value (fn-wg-decode g xs))) (fn-wg-rest (fn-wg-decode g xs))) xs)
                (fn-cbor-octet-listp (fn-wg-rest (fn-wg-decode g xs)))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-wg-grammarp g) (:free (x) (fn-wg-decode g x)) (fn-wg-delimitedp g)
                           (:free (v) (fn-wg-encode g v)) (:free (v) (fn-wg-valuep g v))))))
(defthm fn-wg-tag-decode-name
  (implies (and (equal (fn-wg-op g) :tag) (fn-wg-okp (fn-wg-decode g xs)))
           (member-equal (car (fn-wg-value (fn-wg-decode g xs))) (fn-wg-tag-names g)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-wg-tag-names g)
           :expand ((fn-wg-decode g xs) (fn-wg-tag-names g)))))
(defthm fn-wg-encode-of-decode-seq
  (implies (and (equal (fn-wg-op g) :seq) (consp g) (consp (cdr g)) (fn-wg-grammarp g) (fn-cbor-octet-listp xs) (fn-wg-okp (fn-wg-decode g xs))
                (implies (and (fn-wg-grammarp (fn-wg-arg 1 g)) (fn-cbor-octet-listp xs) (fn-wg-okp (fn-wg-decode (fn-wg-arg 1 g) xs))) (and (fn-wg-valuep (fn-wg-arg 1 g) (fn-wg-value (fn-wg-decode (fn-wg-arg 1 g) xs)))
                (equal (fn-wg-app (fn-wg-encode (fn-wg-arg 1 g) (fn-wg-value (fn-wg-decode (fn-wg-arg 1 g) xs))) (fn-wg-rest (fn-wg-decode (fn-wg-arg 1 g) xs))) xs)
                (fn-cbor-octet-listp (fn-wg-rest (fn-wg-decode (fn-wg-arg 1 g) xs)))))
                (implies (and (fn-wg-grammarp (fn-wg-next g)) (fn-cbor-octet-listp (fn-wg-rest (fn-wg-decode (fn-wg-arg 1 g) xs))) (fn-wg-okp (fn-wg-decode (fn-wg-next g) (fn-wg-rest (fn-wg-decode (fn-wg-arg 1 g) xs))))) (and (fn-wg-valuep (fn-wg-next g) (fn-wg-value (fn-wg-decode (fn-wg-next g) (fn-wg-rest (fn-wg-decode (fn-wg-arg 1 g) xs)))))
                (equal (fn-wg-app (fn-wg-encode (fn-wg-next g) (fn-wg-value (fn-wg-decode (fn-wg-next g) (fn-wg-rest (fn-wg-decode (fn-wg-arg 1 g) xs))))) (fn-wg-rest (fn-wg-decode (fn-wg-next g) (fn-wg-rest (fn-wg-decode (fn-wg-arg 1 g) xs))))) (fn-wg-rest (fn-wg-decode (fn-wg-arg 1 g) xs)))
                (fn-cbor-octet-listp (fn-wg-rest (fn-wg-decode (fn-wg-next g) (fn-wg-rest (fn-wg-decode (fn-wg-arg 1 g) xs))))))))
           (and (fn-wg-valuep g (fn-wg-value (fn-wg-decode g xs)))
                (equal (fn-wg-app (fn-wg-encode g (fn-wg-value (fn-wg-decode g xs))) (fn-wg-rest (fn-wg-decode g xs))) xs)
                (fn-cbor-octet-listp (fn-wg-rest (fn-wg-decode g xs)))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-wg-grammarp g) (:free (x) (fn-wg-decode g x)) (fn-wg-delimitedp g)
                           (:free (v) (fn-wg-encode g v)) (:free (v) (fn-wg-valuep g v))))))
(defthm fn-wg-encode-of-decode-tag-hit
  (implies (and (equal (fn-wg-op g) :tag) (consp g) (consp (cdr g)) (consp (cddr g))
                (and (<= (nfix (fn-wg-arg 1 g)) (len xs))
                     (fn-cbor-octet-listp (fn-wg-take (nfix (fn-wg-arg 1 g)) xs))
                     (equal (fn-wg-be-value (fn-wg-take (nfix (fn-wg-arg 1 g)) xs))
                            (fn-wg-arg 0 (fn-wg-arg 2 g))))
                (fn-wg-grammarp g) (fn-cbor-octet-listp xs) (fn-wg-okp (fn-wg-decode g xs))
                (implies (and (fn-wg-grammarp (fn-wg-arg 2 (fn-wg-arg 2 g))) (fn-cbor-octet-listp (fn-wg-drop (nfix (fn-wg-arg 1 g)) xs)) (fn-wg-okp (fn-wg-decode (fn-wg-arg 2 (fn-wg-arg 2 g)) (fn-wg-drop (nfix (fn-wg-arg 1 g)) xs)))) (and (fn-wg-valuep (fn-wg-arg 2 (fn-wg-arg 2 g)) (fn-wg-value (fn-wg-decode (fn-wg-arg 2 (fn-wg-arg 2 g)) (fn-wg-drop (nfix (fn-wg-arg 1 g)) xs))))
                (equal (fn-wg-app (fn-wg-encode (fn-wg-arg 2 (fn-wg-arg 2 g)) (fn-wg-value (fn-wg-decode (fn-wg-arg 2 (fn-wg-arg 2 g)) (fn-wg-drop (nfix (fn-wg-arg 1 g)) xs)))) (fn-wg-rest (fn-wg-decode (fn-wg-arg 2 (fn-wg-arg 2 g)) (fn-wg-drop (nfix (fn-wg-arg 1 g)) xs)))) (fn-wg-drop (nfix (fn-wg-arg 1 g)) xs))
                (fn-cbor-octet-listp (fn-wg-rest (fn-wg-decode (fn-wg-arg 2 (fn-wg-arg 2 g)) (fn-wg-drop (nfix (fn-wg-arg 1 g)) xs)))))))
           (and (fn-wg-valuep g (fn-wg-value (fn-wg-decode g xs)))
                (equal (fn-wg-app (fn-wg-encode g (fn-wg-value (fn-wg-decode g xs))) (fn-wg-rest (fn-wg-decode g xs))) xs)
                (fn-cbor-octet-listp (fn-wg-rest (fn-wg-decode g xs)))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-wg-grammarp g) (:free (x) (fn-wg-decode g x)) (fn-wg-delimitedp g)
                           (:free (v) (fn-wg-encode g v)) (:free (v) (fn-wg-valuep g v))))))
(defthm fn-wg-encode-of-decode-maybe
  (implies (and (equal (fn-wg-op g) :maybe) (fn-wg-grammarp g) (fn-cbor-octet-listp xs) (fn-wg-okp (fn-wg-decode g xs))
                (implies (and (fn-wg-grammarp (fn-wg-arg 1 g)) (fn-cbor-octet-listp xs) (fn-wg-okp (fn-wg-decode (fn-wg-arg 1 g) xs))) (and (fn-wg-valuep (fn-wg-arg 1 g) (fn-wg-value (fn-wg-decode (fn-wg-arg 1 g) xs)))
                (equal (fn-wg-app (fn-wg-encode (fn-wg-arg 1 g) (fn-wg-value (fn-wg-decode (fn-wg-arg 1 g) xs))) (fn-wg-rest (fn-wg-decode (fn-wg-arg 1 g) xs))) xs)
                (fn-cbor-octet-listp (fn-wg-rest (fn-wg-decode (fn-wg-arg 1 g) xs))))))
           (and (fn-wg-valuep g (fn-wg-value (fn-wg-decode g xs)))
                (equal (fn-wg-app (fn-wg-encode g (fn-wg-value (fn-wg-decode g xs))) (fn-wg-rest (fn-wg-decode g xs))) xs)
                (fn-cbor-octet-listp (fn-wg-rest (fn-wg-decode g xs)))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-wg-grammarp g) (:free (x) (fn-wg-decode g x)) (fn-wg-delimitedp g)
                           (:free (v) (fn-wg-encode g v)) (:free (v) (fn-wg-valuep g v))))))
(defthm fn-wg-encode-of-decode-where
  (implies (and (equal (fn-wg-op g) :where) (fn-wg-grammarp g) (fn-cbor-octet-listp xs) (fn-wg-okp (fn-wg-decode g xs))
                (implies (and (fn-wg-grammarp (fn-wg-arg 1 g)) (fn-cbor-octet-listp xs) (fn-wg-okp (fn-wg-decode (fn-wg-arg 1 g) xs))) (and (fn-wg-valuep (fn-wg-arg 1 g) (fn-wg-value (fn-wg-decode (fn-wg-arg 1 g) xs)))
                (equal (fn-wg-app (fn-wg-encode (fn-wg-arg 1 g) (fn-wg-value (fn-wg-decode (fn-wg-arg 1 g) xs))) (fn-wg-rest (fn-wg-decode (fn-wg-arg 1 g) xs))) xs)
                (fn-cbor-octet-listp (fn-wg-rest (fn-wg-decode (fn-wg-arg 1 g) xs))))))
           (and (fn-wg-valuep g (fn-wg-value (fn-wg-decode g xs)))
                (equal (fn-wg-app (fn-wg-encode g (fn-wg-value (fn-wg-decode g xs))) (fn-wg-rest (fn-wg-decode g xs))) xs)
                (fn-cbor-octet-listp (fn-wg-rest (fn-wg-decode g xs)))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-wg-grammarp g) (:free (x) (fn-wg-decode g x)) (fn-wg-delimitedp g)
                           (:free (v) (fn-wg-encode g v)) (:free (v) (fn-wg-valuep g v))))))

(defthm fn-wg-position-of-nth
  (implies (and (no-duplicatesp-equal names) (natp k) (< k (len names)) (true-listp names))
           (equal (fn-wg-position (nth k names) names) k))
  :hints (("Goal" :induct (nth k names))))
(defthm fn-wg-encode-of-decode-enum
  (implies (and (equal (fn-wg-op g) :enum) (fn-wg-grammarp g) (fn-cbor-octet-listp xs) (fn-wg-okp (fn-wg-decode g xs)))
           (and (fn-wg-valuep g (fn-wg-value (fn-wg-decode g xs)))
                (equal (fn-wg-app (fn-wg-encode g (fn-wg-value (fn-wg-decode g xs))) (fn-wg-rest (fn-wg-decode g xs))) xs)
                (fn-cbor-octet-listp (fn-wg-rest (fn-wg-decode g xs)))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-wg-grammarp g) (:free (x) (fn-wg-decode g x)) (fn-wg-delimitedp g)
                           (:free (v) (fn-wg-encode g v)) (:free (v) (fn-wg-valuep g v))))))
(defthm fn-wg-tag-value-shape-rewrite
  (implies (and (equal (fn-wg-op g) :tag)
                (not (and (true-listp v) (equal (len v) 2))))
           (not (fn-wg-valuep g v)))
  :hints (("Goal" :expand ((fn-wg-valuep g v)))))
(defthm fn-wg-encode-of-decode-tag-miss
  (implies (and (equal (fn-wg-op g) :tag) (consp g) (consp (cdr g)) (consp (cddr g))
                (not (and (<= (nfix (fn-wg-arg 1 g)) (len xs))
                     (fn-cbor-octet-listp (fn-wg-take (nfix (fn-wg-arg 1 g)) xs))
                     (equal (fn-wg-be-value (fn-wg-take (nfix (fn-wg-arg 1 g)) xs))
                            (fn-wg-arg 0 (fn-wg-arg 2 g)))))
                (fn-wg-grammarp g) (fn-cbor-octet-listp xs) (fn-wg-okp (fn-wg-decode g xs))
                (implies (and (fn-wg-grammarp (fn-wg-tag-next g)) (fn-cbor-octet-listp xs) (fn-wg-okp (fn-wg-decode (fn-wg-tag-next g) xs))) (and (fn-wg-valuep (fn-wg-tag-next g) (fn-wg-value (fn-wg-decode (fn-wg-tag-next g) xs)))
                (equal (fn-wg-app (fn-wg-encode (fn-wg-tag-next g) (fn-wg-value (fn-wg-decode (fn-wg-tag-next g) xs))) (fn-wg-rest (fn-wg-decode (fn-wg-tag-next g) xs))) xs)
                (fn-cbor-octet-listp (fn-wg-rest (fn-wg-decode (fn-wg-tag-next g) xs))))))
           (and (fn-wg-valuep g (fn-wg-value (fn-wg-decode g xs)))
                (equal (fn-wg-app (fn-wg-encode g (fn-wg-value (fn-wg-decode g xs))) (fn-wg-rest (fn-wg-decode g xs))) xs)
                (fn-cbor-octet-listp (fn-wg-rest (fn-wg-decode g xs)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :do-not (quote (generalize eliminate-destructors fertilize)) :in-theory (disable fn-wg-tag-codes fn-wg-tag-names) :use ((:instance fn-wg-tag-decode-name (g (fn-wg-tag-next g))))
           :expand ((fn-wg-grammarp g) (:free (x) (fn-wg-decode g x)) (fn-wg-delimitedp g)
                    (:free (v) (fn-wg-encode g v)) (:free (v) (fn-wg-valuep g v))))))
(defthm fn-wg-octets-of-cdr
  (implies (fn-cbor-octet-listp x) (fn-cbor-octet-listp (cdr x))))
(defthm fn-wg-frame-reassembly
  (let* ((x1 (fn-wg-drop 4 xs))
         (x2 (cddr x1))
         (lenb (fn-wg-take 4 x2))
         (x3 (fn-wg-drop 4 x2))
         (n (fn-wg-be-value lenb))
         (payload (fn-wg-take n x3))
         (x4 (fn-wg-drop n x3)))
    (implies (and (fn-cbor-octet-listp xs)
                  (<= 4 (len xs)) (consp x1) (consp (cdr x1))
                  (<= 4 (len x2))
                  (<= (+ n 32) (len x3)))
             (equal (fn-wg-app (fn-wg-frame-protected (fn-wg-take 4 xs) (car x1) (cadr x1) payload)
                               (fn-wg-app (fn-wg-take 32 x4) (fn-wg-drop 32 x4)))
                    xs)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (enable fn-wg-frame-protected))))
(defthm fn-wg-decode-frame-inversion-2
  (let* ((x1 (fn-wg-drop 4 xs))
         (x2 (cddr x1))
         (lenb (fn-wg-take 4 x2))
         (x3 (fn-wg-drop 4 x2))
         (n (fn-wg-be-value lenb))
         (payload (fn-wg-take n x3))
         (x4 (fn-wg-drop n x3))
         (r (fn-wg-decode (fn-wg-arg 5 g) payload)))
    (implies (and (equal (fn-wg-op g) :frame) (fn-wg-okp (fn-wg-decode g xs)))
             (and (<= 4 (len xs)) (consp x1) (consp (cdr x1)) (<= 4 (len x2))
                  (<= (+ n 32) (len x3))
                  (<= n (nfix (fn-wg-arg 4 g)))
                  (equal (fn-wg-take 4 xs) (fn-wg-arg 1 g))
                  (equal (car x1) (fn-wg-arg 2 g))
                  (equal (cadr x1) (fn-wg-arg 3 g))
                  (equal (fn-wg-take 32 x4)
                         (fn-frame-digest (fn-wg-frame-protected (fn-wg-arg 1 g) (fn-wg-arg 2 g)
                                                                  (fn-wg-arg 3 g) payload)))
                  (fn-wg-okp r)
                  (not (consp (fn-wg-rest r)))
                  (equal (fn-wg-value (fn-wg-decode g xs)) (fn-wg-value r))
                  (equal (fn-wg-rest (fn-wg-decode g xs)) (fn-wg-drop 32 x4))
                  (implies (fn-cbor-octet-listp xs)
                           (fn-cbor-octet-listp (fn-wg-rest (fn-wg-decode g xs)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (disable fn-wg-frame-protected))))
(defthm fn-wg-encode-of-decode-frame
  (implies (and (equal (fn-wg-op g) :frame) (fn-wg-grammarp g) (fn-cbor-octet-listp xs) (fn-wg-okp (fn-wg-decode g xs))
                (implies (and (fn-wg-grammarp (fn-wg-arg 5 g)) (fn-cbor-octet-listp (fn-wg-take (fn-wg-be-value (fn-wg-take 4 (cddr (fn-wg-drop 4 xs)))) (fn-wg-drop 4 (cddr (fn-wg-drop 4 xs))))) (fn-wg-okp (fn-wg-decode (fn-wg-arg 5 g) (fn-wg-take (fn-wg-be-value (fn-wg-take 4 (cddr (fn-wg-drop 4 xs)))) (fn-wg-drop 4 (cddr (fn-wg-drop 4 xs))))))) (and (fn-wg-valuep (fn-wg-arg 5 g) (fn-wg-value (fn-wg-decode (fn-wg-arg 5 g) (fn-wg-take (fn-wg-be-value (fn-wg-take 4 (cddr (fn-wg-drop 4 xs)))) (fn-wg-drop 4 (cddr (fn-wg-drop 4 xs)))))))
                (equal (fn-wg-app (fn-wg-encode (fn-wg-arg 5 g) (fn-wg-value (fn-wg-decode (fn-wg-arg 5 g) (fn-wg-take (fn-wg-be-value (fn-wg-take 4 (cddr (fn-wg-drop 4 xs)))) (fn-wg-drop 4 (cddr (fn-wg-drop 4 xs))))))) (fn-wg-rest (fn-wg-decode (fn-wg-arg 5 g) (fn-wg-take (fn-wg-be-value (fn-wg-take 4 (cddr (fn-wg-drop 4 xs)))) (fn-wg-drop 4 (cddr (fn-wg-drop 4 xs))))))) (fn-wg-take (fn-wg-be-value (fn-wg-take 4 (cddr (fn-wg-drop 4 xs)))) (fn-wg-drop 4 (cddr (fn-wg-drop 4 xs)))))
                (fn-cbor-octet-listp (fn-wg-rest (fn-wg-decode (fn-wg-arg 5 g) (fn-wg-take (fn-wg-be-value (fn-wg-take 4 (cddr (fn-wg-drop 4 xs)))) (fn-wg-drop 4 (cddr (fn-wg-drop 4 xs))))))))))
           (and (fn-wg-valuep g (fn-wg-value (fn-wg-decode g xs)))
                (equal (fn-wg-app (fn-wg-encode g (fn-wg-value (fn-wg-decode g xs))) (fn-wg-rest (fn-wg-decode g xs))) xs)
                (fn-cbor-octet-listp (fn-wg-rest (fn-wg-decode g xs)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :do-not '(generalize eliminate-destructors fertilize)
           :use (fn-wg-decode-frame-inversion-2 fn-wg-frame-reassembly)
           :in-theory (disable fn-wg-decode-opener-frame fn-wg-frame-protected fn-wg-value fn-wg-rest fn-wg-okp))))

(defthm fn-wg-result-accessors
  (and (fn-wg-okp (fn-wg-ok v r))
       (equal (fn-wg-value (fn-wg-ok v r)) v)
       (equal (fn-wg-rest (fn-wg-ok v r)) r)
       (not (fn-wg-okp (fn-wg-refused reason)))
       (equal (fn-wg-app nil x) x)))

(defun fn-wg-decode-induction (g xs)
  (declare (xargs :measure (acl2-count g) :verify-guards nil))
  (let ((op (fn-wg-op g)))
    (cond ((equal op :seq)
           (if (and (consp g) (consp (cdr g)))
               (list (fn-wg-decode-induction (fn-wg-arg 1 g) xs)
                     (fn-wg-decode-induction (fn-wg-next g)
                                             (fn-wg-rest (fn-wg-decode (fn-wg-arg 1 g) xs))))
             (list g xs)))
          ((equal op :tag)
           (if (and (consp g) (consp (cdr g)) (consp (cddr g)))
               (if (and (<= (nfix (fn-wg-arg 1 g)) (len xs))
                        (fn-cbor-octet-listp (fn-wg-take (nfix (fn-wg-arg 1 g)) xs))
                        (equal (fn-wg-be-value (fn-wg-take (nfix (fn-wg-arg 1 g)) xs))
                               (fn-wg-arg 0 (fn-wg-arg 2 g))))
                   (fn-wg-decode-induction (fn-wg-arg 2 (fn-wg-arg 2 g))
                                           (fn-wg-drop (nfix (fn-wg-arg 1 g)) xs))
                 (fn-wg-decode-induction (fn-wg-tag-next g) xs))
             (list g xs)))
          ((equal op :maybe) (fn-wg-decode-induction (fn-wg-arg 1 g) xs))
          ((equal op :where) (fn-wg-decode-induction (fn-wg-arg 1 g) xs))
          ((equal op :frame) (fn-wg-decode-induction (fn-wg-arg 5 g) (fn-wg-take (fn-wg-be-value (fn-wg-take 4 (cddr (fn-wg-drop 4 xs)))) (fn-wg-drop 4 (cddr (fn-wg-drop 4 xs))))))
          (t (list g xs)))))

(defthm fn-wg-shape-facts-2
  (implies (and (equal (fn-wg-op g) :seq) (not (and (consp g) (consp (cdr g)))))
           (and (equal (fn-wg-decode g xs) (fn-wg-ok nil xs))
                (fn-wg-valuep g nil)
                (equal (fn-wg-encode g nil) nil)))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-wg-decode g xs) (fn-wg-valuep g nil) (fn-wg-encode g nil)))))

; KEYSTONE (canonicity).  An accepted octet string is the encoding of the
; value it decodes to, followed by what the decoder left; the value is a
; value of the grammar.  So each value has exactly one accepted encoding.
(defthm fn-wg-encode-of-decode
  (implies (and (fn-wg-grammarp g) (fn-cbor-octet-listp xs)
                (fn-wg-okp (fn-wg-decode g xs)))
           (and (fn-wg-valuep g (fn-wg-value (fn-wg-decode g xs)))
                (equal (fn-wg-app (fn-wg-encode g (fn-wg-value (fn-wg-decode g xs)))
                                  (fn-wg-rest (fn-wg-decode g xs)))
                       xs)
                (fn-cbor-octet-listp (fn-wg-rest (fn-wg-decode g xs)))))
  :hints (("Goal" :induct (fn-wg-decode-induction g xs)
           :in-theory (disable fn-wg-decode fn-wg-encode fn-wg-valuep fn-wg-grammarp
                               fn-wg-delimitedp fn-wg-app fn-wg-ok fn-wg-okp fn-wg-value
                               fn-wg-rest)
           :do-not '(generalize fertilize eliminate-destructors))
          (and (equal (access clause-id id :pool-lst) '(1))
               (equal (len (access clause-id id :case-lst)) 1)
               (equal (access clause-id id :primes) 0)
               '(:use (fn-wg-shape-facts-2 fn-wg-grammarp-op fn-wg-grammarp-seq-tag-shape fn-wg-encode-of-decode-const fn-wg-encode-of-decode-uint fn-wg-encode-of-decode-bytes fn-wg-encode-of-decode-rest fn-wg-encode-of-decode-line fn-wg-encode-of-decode-base64-lines fn-wg-encode-of-decode-enum fn-wg-encode-of-decode-seq fn-wg-encode-of-decode-tag-hit fn-wg-encode-of-decode-tag-miss fn-wg-encode-of-decode-maybe fn-wg-encode-of-decode-where fn-wg-encode-of-decode-frame)))))

; -----------------------------------------------------------------------------
; Guards: the interpreter is total and guard-verified at :guard t (any
; grammar, any value, any octets), so the image calls it at a family's
; grammar constant.

(verify-guards fn-wg-encode)
(verify-guards fn-wg-valuep)
(verify-guards fn-wg-decode)
