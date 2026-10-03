; Retained LIST row fields. String conversion and decimal construction never
; walk a whole row. One call emits at most one byte or advances one digit.
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
