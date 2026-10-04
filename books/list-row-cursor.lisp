; Retained LIST row fields. String conversion and decimal construction never
; walk a whole row. One call emits at most one byte or advances one digit.
; Its residual (fn-lsr-reference) and finite potential (fn-lsr-remaining-work)
; are logical only; fn-lsr-start-reference ties the residual to the line.
; Integer arithmetic width remains a carried-profile tariff, not a byte bound.
(in-package "ACL2")
(include-book "nntp-session")
(include-book "nntp-projection")
(include-book "def-cursor")

(local (in-theory (disable (tau-system))))

; Fields: remaining pieces, phase, offset, quotient, reversed digits,
; remaining digit tail, first-byte flag. Pieces borrow strings or scalar numbers.
(defun fn-lsr-make (pieces phase offset quotient reversed digits firstp)
  (declare (xargs :guard t))
  (list pieces phase offset quotient reversed digits firstp))

(defun fn-lsr-start (group summary countsp status)
  (declare (xargs :guard t))
  (fn-lsr-make
   (append (list (list :text group) (list :text " ")
                 (list :number (fn-nntp-summary-high summary)) (list :text " ")
                 (list :number (fn-nntp-summary-low summary)))
           (if countsp (list (list :text " ")
                            (list :number (fn-nntp-summary-count summary))) nil)
           (list (list :text " ") (list :text status)))
   :piece 0 0 nil nil t))

(local
 (defthm fn-lsr-indexed-character
   (implies (and (stringp text) (natp k) (< k (length text)))
            (characterp (char text k)))
   :hints (("Goal" :use ((:instance character-listp-coerce (str text)))
            :in-theory (e/d (char length character-listp)
                            (character-listp-coerce))))))

(defun fn-lsr-one (cur)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((pieces (fn-cur-at 0 cur))
         (phase (fn-cur-at 1 cur))
         (offset (nfix (fn-cur-at 2 cur)))
         (quotient (fn-cur-at 3 cur))
         (reversed (fn-cur-at 4 cur))
         (digits (fn-cur-at 5 cur))
         (firstp (fn-cur-at 6 cur))
         (piece (fn-cur-at 0 pieces))
         (value (fn-cur-at 1 piece)))
    (cond
     ((not cur) (mv nil nil))
     ((eq phase :piece)
      (if (consp pieces)
          (if (eq (fn-cur-at 0 piece) :number)
              (mv nil (if (natp value)
                          (fn-lsr-make pieces :build 0 value nil nil firstp)
                        (fn-lsr-make pieces :digits 0 0 nil '(48) firstp)))
            (mv nil (fn-lsr-make pieces :text 0 0 nil nil firstp)))
        (mv nil (fn-lsr-make pieces :cr 0 0 nil nil firstp))))
     ((eq phase :text)
      (if (and (stringp value) (< offset (length value)))
          (let ((byte (char-code (char value offset))))
            (if (and firstp (eql byte 46))
                (mv '(46) (fn-lsr-make pieces :text offset 0 nil nil nil))
              (mv (list byte) (fn-lsr-make pieces :text (1+ offset) 0 nil nil nil))))
        (mv nil (fn-lsr-make (if (consp pieces) (cdr pieces) nil)
                            :piece 0 0 nil nil firstp))))
     ((eq phase :build)
      ; The existing field formatter maps more than ten decimal digits to 0.
      ; Stop at that decision, without exploding the remaining integer.
      (if (<= *fn-nntp-max-decimal-octets* offset)
          (mv nil (fn-lsr-make pieces :digits 0 0 nil '(48) firstp))
        (let* ((number (nfix quotient))
               (q (nfix (floor number 10)))
               (r (+ 48 (mod number 10))))
          (mv nil (if (zp q)
                      (fn-lsr-make pieces :digits 0 0 nil (cons r reversed) firstp)
                    (fn-lsr-make pieces :build (1+ offset) q
                                (cons r reversed) nil firstp))))))
     ((eq phase :digits)
      (if (consp digits)
          (mv (list (car digits))
              (fn-lsr-make pieces :digits 0 0 nil (cdr digits) nil))
        (mv nil (fn-lsr-make (if (consp pieces) (cdr pieces) nil)
                            :piece 0 0 nil nil firstp))))
     ((eq phase :cr) (mv '(13) (fn-lsr-make nil :lf 0 0 nil nil nil)))
     ((eq phase :lf) (mv '(10) nil))
     (t (mv nil nil)))))

(verify-guards fn-lsr-one
  :hints (("Goal" :in-theory
           (union-theories '(nfix natp length fn-lsr-indexed-character
                             (:type-prescription mod) (:type-prescription floor)
                             (:type-prescription len))
                           (theory 'minimal-theory)))))

(defthm fn-lsr-one-byte-bound
  (<= (len (mv-nth 0 (fn-lsr-one cur))) 1)
  :rule-classes :linear
  :hints (("Goal" :in-theory
           (union-theories '(fn-lsr-one len mv-nth fn-cur-at fn-lsr-make car-cons cdr-cons)
                           (theory 'minimal-theory)))))

(defthm fn-lsr-one-fixed-envelope
  (or (not (mv-nth 1 (fn-lsr-one cur)))
      (equal (len (mv-nth 1 (fn-lsr-one cur))) 7))
  :hints (("Goal" :in-theory
           (union-theories '(fn-lsr-one len mv-nth fn-cur-at fn-lsr-make car-cons cdr-cons)
                           (theory 'minimal-theory)))))

; Carried allocation shape. It is established once and preserved; the served
; controller never traverses this predicate or validates borrowed strings.
(defun fn-lsr-statep (cur)
  (declare (xargs :guard t))
  (or (not cur)
      (and (true-listp cur) (equal (len cur) 7)
           (natp (fn-cur-at 2 cur))
           (<= (len (fn-cur-at 4 cur)) *fn-nntp-max-decimal-octets*)
           (<= (len (fn-cur-at 5 cur)) *fn-nntp-max-decimal-octets*)
           (or (not (eq (fn-cur-at 1 cur) :build))
               (and (<= (fn-cur-at 2 cur) *fn-nntp-max-decimal-octets*)
                    (equal (len (fn-cur-at 4 cur)) (fn-cur-at 2 cur)))))))

(local
 (defthm fn-lsr-constructor-fields
   (and (equal (fn-cur-at 0 (fn-lsr-make p ph at q r d f)) p)
        (equal (fn-cur-at 1 (fn-lsr-make p ph at q r d f)) ph)
        (equal (fn-cur-at 2 (fn-lsr-make p ph at q r d f)) at)
        (equal (fn-cur-at 3 (fn-lsr-make p ph at q r d f)) q)
        (equal (fn-cur-at 4 (fn-lsr-make p ph at q r d f)) r)
        (equal (fn-cur-at 5 (fn-lsr-make p ph at q r d f)) d)
        (equal (fn-cur-at 6 (fn-lsr-make p ph at q r d f)) f)
        (true-listp (fn-lsr-make p ph at q r d f))
        (equal (len (fn-lsr-make p ph at q r d f)) 7))
   :hints (("Goal" :in-theory
            (union-theories '(fn-cur-at fn-lsr-make zp natp nfix len
                              true-listp car-cons cdr-cons)
                            (theory 'minimal-theory))))))

(defthm fn-lsr-start-statep
  (fn-lsr-statep (fn-lsr-start group summary countsp status))
  :hints (("Goal" :in-theory
           (union-theories '(fn-lsr-statep fn-lsr-start fn-lsr-constructor-fields
                             len true-listp car-cons cdr-cons zp natp nfix)
                           (theory 'minimal-theory)))))

(defthm fn-lsr-one-keeps-statep
  (implies (fn-lsr-statep cur) (fn-lsr-statep (mv-nth 1 (fn-lsr-one cur))))
  :hints (("Goal" :in-theory
           (union-theories '(fn-lsr-statep fn-lsr-one fn-lsr-constructor-fields
                             len true-listp car-cons cdr-cons nfix natp zp mv-nth)
                           (theory 'minimal-theory)))))


(in-theory (disable fn-lsr-make fn-lsr-start fn-lsr-one fn-lsr-statep))

; -----------------------------------------------------------------------------
; Logical residual and finite potential. Neither is computed by the served
; controller: they state what the retained row still owes and why it ends.
; FN-LSR-REFERENCE is the exact remaining octets of a row state;
; fn-lsr-one-keeps-reference says one call's octets followed by the residual
; of its successor are the residual it started from, for every state.

(defun-nx fn-lsr-build-reference (q reversed offset)
  (declare (xargs :measure (nfix (- *fn-nntp-max-decimal-octets* (nfix offset)))))
  (if (<= *fn-nntp-max-decimal-octets* (nfix offset)) '(48)
    (let* ((number (nfix q))
           (next (nfix (floor number 10)))
           (r (+ 48 (mod number 10))))
      (if (zp next) (cons r reversed)
        (fn-lsr-build-reference next (cons r reversed) (1+ (nfix offset)))))))

(defun-nx fn-lsr-piece-octets (piece)
  (let ((value (fn-cur-at 1 piece)))
    (if (eq (fn-cur-at 0 piece) :number)
        (if (natp value) (fn-lsr-build-reference value nil 0) '(48))
      (if (stringp value) (fn-nntp-string-octets value) nil))))

(defun-nx fn-lsr-pieces-octets (pieces)
  (if (consp pieces)
      (append (fn-lsr-piece-octets (car pieces)) (fn-lsr-pieces-octets (cdr pieces)))
    nil))

(defun-nx fn-lsr-stuff (firstp bytes)
  (if firstp (fn-wire-stuff-line bytes) bytes))

(defun-nx fn-lsr-reference (cur)
  (let* ((pieces (fn-cur-at 0 cur))
         (phase (fn-cur-at 1 cur))
         (offset (nfix (fn-cur-at 2 cur)))
         (quotient (fn-cur-at 3 cur))
         (reversed (fn-cur-at 4 cur))
         (digits (fn-cur-at 5 cur))
         (firstp (fn-cur-at 6 cur))
         (value (fn-cur-at 1 (fn-cur-at 0 pieces)))
         (rest (fn-lsr-pieces-octets (if (consp pieces) (cdr pieces) nil))))
    (cond ((not cur) nil)
          ((eq phase :piece) (append (fn-lsr-stuff firstp (fn-lsr-pieces-octets pieces)) '(13 10)))
          ((eq phase :text)
           (append (fn-lsr-stuff firstp
                     (append (if (stringp value) (nthcdr offset (fn-nntp-string-octets value)) nil)
                             rest))
                   '(13 10)))
          ((eq phase :build)
           (append (fn-lsr-build-reference quotient reversed offset) rest '(13 10)))
          ((eq phase :digits)
           (if (consp digits)
               (append digits rest '(13 10))
             (append (fn-lsr-stuff firstp rest) '(13 10))))
          ((eq phase :cr) '(13 10))
          ((eq phase :lf) '(10))
          (t nil))))

(local
 (defthm fn-lsr-string-octets-aux-len
   (equal (len (fn-nntp-string-octets-aux chars)) (len chars))
   :hints (("Goal" :in-theory (enable fn-nntp-string-octets-aux)))))

(local
 (defthm fn-lsr-nthcdr-string-octets-aux
   (implies (and (natp k) (< k (len chars)))
            (equal (nthcdr k (fn-nntp-string-octets-aux chars))
                   (cons (char-code (nth k chars))
                         (nthcdr (+ 1 k) (fn-nntp-string-octets-aux chars)))))
   :hints (("Goal" :induct (nthcdr k chars)
            :in-theory (enable fn-nntp-string-octets-aux)))))

(local
 (defthm fn-lsr-nthcdr-string-octets-aux-past
   (implies (and (natp k) (<= (len chars) k))
            (equal (nthcdr k (fn-nntp-string-octets-aux chars)) nil))
   :hints (("Goal" :induct (nthcdr k chars)
            :in-theory (enable fn-nntp-string-octets-aux)))))

(local
 (defthm fn-lsr-text-octet
   (implies (and (stringp text) (natp k) (< k (length text)))
            (equal (nthcdr k (fn-nntp-string-octets text))
                   (cons (char-code (char text k))
                         (nthcdr (+ 1 k) (fn-nntp-string-octets text)))))
   :hints (("Goal" :in-theory (enable fn-nntp-string-octets char length)))))

(local
 (defthm fn-lsr-text-past
   (implies (and (stringp text) (natp k) (<= (length text) k))
            (equal (nthcdr k (fn-nntp-string-octets text)) nil))
   :hints (("Goal" :in-theory (enable fn-nntp-string-octets length)))))

(local
 (defthm fn-lsr-build-reference-digit
   (and (consp (fn-lsr-build-reference q reversed offset))
        (not (equal (car (fn-lsr-build-reference q reversed offset)) 46)))
   :hints (("Goal" :induct (fn-lsr-build-reference q reversed offset)))))

(local
 (defthm fn-lsr-stuff-digit
   (implies (and (consp bytes) (not (equal (car bytes) 46)))
            (equal (fn-lsr-stuff firstp bytes) bytes))
   :hints (("Goal" :in-theory (enable fn-lsr-stuff fn-wire-stuff-line)))))

(local
 (defthm fn-lsr-stuff-of-nil-flag
   (equal (fn-lsr-stuff nil bytes) bytes)
   :hints (("Goal" :in-theory (enable fn-lsr-stuff)))))

(local (defthm fn-lsr-cur-at-zero
         (equal (fn-cur-at 0 x) (car x))
         :hints (("Goal" :in-theory (enable fn-cur-at)))))
(local (defthm fn-lsr-nthcdr-zero
         (equal (nthcdr 0 x) x)))
(local (defthm fn-lsr-car-make
         (equal (car (fn-lsr-make p ph at q r d f)) p)
         :hints (("Goal" :in-theory (enable fn-lsr-make)))))
(local (defthm fn-lsr-make-nonnil
         (fn-lsr-make p ph at q r d f)
         :hints (("Goal" :in-theory (enable fn-lsr-make)))))
(local (defthm fn-lsr-append-assoc
         (equal (append (append x y) z) (append x (append y z)))))
(local (defthm fn-lsr-stuff-cons
         (equal (fn-lsr-stuff f (cons b x))
                (if (and f (equal b 46)) (list* 46 46 x) (cons b x)))
         :hints (("Goal" :in-theory (enable fn-lsr-stuff fn-wire-stuff-line)))))
(local (defthm fn-lsr-stuff-build
         (equal (fn-lsr-stuff f (append (fn-lsr-build-reference q r o) y))
                (append (fn-lsr-build-reference q r o) y))
         :hints (("Goal" :use ((:instance fn-lsr-build-reference-digit (reversed r) (offset o)))
                  :in-theory (e/d (fn-lsr-stuff fn-wire-stuff-line) (fn-lsr-build-reference-digit))))))
(local (defthm fn-lsr-stuff-zero
         (equal (fn-lsr-stuff f (cons 48 y)) (cons 48 y))
         :hints (("Goal" :in-theory (enable fn-lsr-stuff fn-wire-stuff-line)))))
(local (defthm fn-lsr-stuff-empty
         (equal (fn-lsr-stuff f nil) nil)
         :hints (("Goal" :in-theory (enable fn-lsr-stuff fn-wire-stuff-line)))))
(local (defthm fn-lsr-nfix-nfix (equal (nfix (nfix x)) (nfix x))))
(local (defthm fn-lsr-nfix-successor (equal (nfix (+ 1 (nfix x))) (+ 1 (nfix x)))))
(defthm fn-lsr-one-keeps-reference
  (equal (append (mv-nth 0 (fn-lsr-one cur))
                 (fn-lsr-reference (mv-nth 1 (fn-lsr-one cur))))
         (fn-lsr-reference cur))
  :hints (("Goal" :in-theory
           (e/d (fn-lsr-one fn-lsr-reference fn-lsr-pieces-octets fn-lsr-piece-octets
                 fn-lsr-constructor-fields)
                (fn-lsr-make fn-cur-at fn-lsr-build-reference nfix fn-lsr-stuff
                 fn-wire-stuff-line fn-nntp-string-octets nthcdr char length floor mod))
           :expand ((fn-lsr-build-reference (fn-cur-at 3 cur) (fn-cur-at 4 cur)
                                            (nfix (fn-cur-at 2 cur)))))))

(defthm fn-lsr-one-output-true-listp
  (true-listp (mv-nth 0 (fn-lsr-one cur)))
  :hints (("Goal" :in-theory (enable fn-lsr-one))))

; Finite potential (harvested from codex/sol-served-20261003@232fa612a,
; admitted here with the constructor-field bridge it lacked). A live row
; state strictly reduces it on every call, emitted byte or not.
(defun-nx fn-lsr-piece-work (piece)
  (if (eq (fn-cur-at 0 piece) :number) 22
    (+ 2 (if (stringp (fn-cur-at 1 piece)) (length (fn-cur-at 1 piece)) 0))))

(defun-nx fn-lsr-pieces-work (pieces)
  (if (consp pieces)
      (+ (fn-lsr-piece-work (car pieces)) (fn-lsr-pieces-work (cdr pieces)))
    0))

(defun-nx fn-lsr-remaining-work (cur)
  (let* ((pieces (fn-cur-at 0 cur))
         (phase (fn-cur-at 1 cur))
         (offset (nfix (fn-cur-at 2 cur)))
         (digits (fn-cur-at 5 cur))
         (first (if (fn-cur-at 6 cur) 1 0))
         (value (fn-cur-at 1 (fn-cur-at 0 pieces)))
         (chars (if (stringp value) (length value) 0))
         (future (+ 3 first (fn-lsr-pieces-work (if (consp pieces) (cdr pieces) nil)))))
    (cond ((not cur) 0)
          ((eq phase :piece) (+ 3 first (fn-lsr-pieces-work pieces)))
          ((eq phase :text) (+ 1 (nfix (- chars offset)) future))
          ((eq phase :build) (+ (nfix (- 21 offset)) future))
          ((eq phase :digits) (+ 1 (len digits) future))
          ((eq phase :cr) 2)
          ((eq phase :lf) 1)
          (t 1))))

(defthm fn-lsr-remaining-work-natp
  (natp (fn-lsr-remaining-work cur))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable fn-lsr-remaining-work))))

; The carried digit shape covers the only phase whose potential uses a
; partially built decimal. No supplied data is scanned to establish it per step.
(defthm fn-lsr-one-finite-progress
  (implies (and cur (fn-lsr-statep cur))
           (< (fn-lsr-remaining-work (mv-nth 1 (fn-lsr-one cur)))
              (fn-lsr-remaining-work cur)))
  :hints (("Goal" :in-theory
           (e/d (fn-lsr-one fn-lsr-remaining-work fn-lsr-pieces-work
                 fn-lsr-piece-work fn-lsr-statep)
                (fn-cur-at fn-lsr-make)))))

; The retained renderer's first residual is the dot-stuffed CRLF line whose
; numbers are the status-line decimal field (the ten-digit rule included).
(encapsulate ()
(local (include-book "arithmetic-5/top" :dir :system))

(defun-nx fn-lsr-digits (q)
  (declare (xargs :measure (nfix q)))
  (if (zp q) nil
    (append (fn-lsr-digits (floor q 10)) (list (+ 48 (mod q 10))))))

(local
 (defthm fn-lsr-digit-char-code
   (implies (and (integerp d) (<= 0 d) (< d 10))
            (equal (char-code (digit-to-char d)) (+ 48 d)))
   :hints (("Goal" :in-theory (enable digit-to-char)))))

(local
 (defthm fn-lsr-octets-aux-append
   (equal (fn-nntp-string-octets-aux (append a b))
          (append (fn-nntp-string-octets-aux a) (fn-nntp-string-octets-aux b)))
   :hints (("Goal" :in-theory (enable fn-nntp-string-octets-aux)))))

(defthm fn-lsr-explode-digits
  (implies (posp q)
           (equal (fn-nntp-string-octets-aux (explode-nonnegative-integer q 10 a))
                  (append (fn-lsr-digits q) (fn-nntp-string-octets-aux a))))
  :hints (("Goal" :induct (explode-nonnegative-integer q 10 a)
           :in-theory (e/d (fn-nntp-string-octets-aux) (digit-to-char)))))

(local (defthm fn-lsr-len-append (equal (len (append a b)) (+ (len a) (len b)))))

(local (defthm fn-lsr-digits-positive-len
  (implies (posp q) (< 0 (len (fn-lsr-digits q))))
  :rule-classes :linear
  :hints (("Goal" :expand ((fn-lsr-digits q))))))

(defthm fn-lsr-build-reference-is-digits
  (implies (and (posp q) (natp offset))
           (equal (fn-lsr-build-reference q reversed offset)
                  (if (<= (+ offset (len (fn-lsr-digits q))) *fn-nntp-max-decimal-octets*)
                      (append (fn-lsr-digits q) reversed)
                    '(48))))
  :hints (("Goal" :induct (fn-lsr-build-reference q reversed offset))))
)

(encapsulate ()
(local (include-book "arithmetic-5/top" :dir :system))
(local (defthm fn-lsr-digits-true-listp (true-listp (fn-lsr-digits q))))
(local (defthm fn-lsr-tokenp-append
  (equal (fn-nntp-decimal-tokenp (append a b))
         (and (fn-nntp-decimal-tokenp a) (fn-nntp-decimal-tokenp b)))
  :hints (("Goal" :in-theory (enable fn-nntp-decimal-tokenp)))))
(local (defthm fn-lsr-digits-tokenp
  (fn-nntp-decimal-tokenp (fn-lsr-digits q))
  :hints (("Goal" :induct (fn-lsr-digits q)
           :in-theory (enable fn-nntp-decimal-tokenp fn-nntp-decimal-digitp)))))
(local (defthm fn-lsr-digits-consp
  (implies (posp q) (consp (fn-lsr-digits q)))
  :hints (("Goal" :expand ((fn-lsr-digits q))))))
(defthm fn-lsr-number-is-decimal-field
  (implies (natp v)
           (equal (fn-lsr-build-reference v nil 0) (fn-nntp-decimal-field v)))
  :hints (("Goal" :cases ((equal v 0))
           :in-theory (enable fn-nntp-decimal-field fn-nntp-decimal fn-nntp-decimal-rev))
          ("Subgoal 2" :use ((:instance fn-lsr-explode-digits (q v) (a nil))
                             (:instance fn-lsr-build-reference-is-digits (q v) (reversed nil) (offset 0))))))
)

(local (defthm fn-lsr-number-octets
         (equal (fn-lsr-piece-octets (list :number v))
                (fn-nntp-decimal-field v))
         :hints (("Goal" :cases ((natp v))
                  :in-theory (enable fn-lsr-piece-octets fn-nntp-decimal-field
                                     fn-nntp-decimal fn-cur-at)))))
(local (defthm fn-lsr-text-octets
         (equal (fn-lsr-piece-octets (list :text v))
                (fn-nntp-string-octets v))
         :hints (("Goal" :in-theory (enable fn-lsr-piece-octets fn-nntp-string-octets fn-cur-at)))))

(defthm fn-lsr-start-reference
  (equal (fn-lsr-reference (fn-lsr-start group summary countsp status))
         (fn-nntp-stuff-lines
          (list (fn-nntp-append-pieces
                 (append (list (fn-nntp-string-octets group) '(32)
                               (fn-nntp-decimal-field (fn-nntp-summary-high summary)) '(32)
                               (fn-nntp-decimal-field (fn-nntp-summary-low summary)))
                         (if countsp
                             (list '(32) (fn-nntp-decimal-field (fn-nntp-summary-count summary)))
                           nil)
                         (list '(32) (fn-nntp-string-octets status)))))))
  :hints (("Goal" :in-theory
           (e/d (fn-lsr-reference fn-lsr-start fn-lsr-pieces-octets fn-lsr-stuff
                 fn-lsr-constructor-fields fn-nntp-stuff-lines fn-nntp-crlf
                 fn-nntp-append-pieces)
                (fn-lsr-make fn-lsr-piece-octets fn-nntp-decimal-field
                 fn-nntp-string-octets fn-wire-stuff-line)))))

(in-theory (disable fn-lsr-build-reference fn-lsr-piece-octets fn-lsr-pieces-octets
                    fn-lsr-stuff fn-lsr-reference fn-lsr-digits
                    fn-lsr-piece-work fn-lsr-pieces-work fn-lsr-remaining-work))
