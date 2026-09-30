; Bounded decimal setup for NOV continuations, PRF-1066 component.
; Each division emits one digit and spends one unit. The selected record
; codec fits ten divisions; no complete unbounded EXPLODE is executed.
(in-package "ACL2")
(include-book "records-shape")
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

(defun fn-nbw-decimal-tick (n fuel chars)
  (declare (xargs :guard (and (natp n) (natp fuel) (character-listp chars))
                  :verify-guards nil :measure (nfix fuel)))
  (if (zp n)
      (mv t (if (consp chars) chars (list #\0)) n 0)
    (if (zp fuel)
        (mv nil chars n 0)
      (mv-let (done next remaining used)
        (fn-nbw-decimal-tick (floor n 10) (- fuel 1)
                             (cons (digit-to-char (mod n 10)) chars))
        (mv done next remaining (+ 1 used))))))

(defthm fn-nbw-decimal-tick-used-natural
  (natp (mv-nth 3 (fn-nbw-decimal-tick n fuel chars)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-nbw-decimal-tick n fuel chars)
                  :in-theory (disable floor mod digit-to-char))))

(verify-guards fn-nbw-decimal-tick
  :hints (("Goal" :in-theory (disable floor mod digit-to-char))))

(defthm fn-nbw-decimal-tick-residual
  (implies (true-listp chars)
           (equal (explode-nonnegative-integer
                   (mv-nth 2 (fn-nbw-decimal-tick n fuel chars)) 10
                   (mv-nth 1 (fn-nbw-decimal-tick n fuel chars)))
                  (explode-nonnegative-integer n 10 chars)))
  :hints (("Goal" :induct (fn-nbw-decimal-tick n fuel chars)
                  :in-theory (disable floor mod digit-to-char))))

(defthm fn-nbw-decimal-tick-work-bounded
  (<= (mv-nth 3 (fn-nbw-decimal-tick n fuel chars)) (nfix fuel))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-nbw-decimal-tick n fuel chars)
                  :in-theory (disable floor mod digit-to-char))))

; Small proof vocabulary: keep the ten-way completion proof independent
; of the four-valued output and its accumulated characters.
(defun fn-nbw-decimal-fitsp (n fuel)
  (declare (xargs :guard (and (natp n) (natp fuel)) :measure (nfix fuel)
                  :guard-hints (("Goal" :in-theory (disable floor)))))
  (or (zp n)
      (and (not (zp fuel)) (fn-nbw-decimal-fitsp (floor n 10) (- fuel 1)))))

(defthm fn-nbw-decimal-done-is-fitsp
  (equal (mv-nth 0 (fn-nbw-decimal-tick n fuel chars))
         (fn-nbw-decimal-fitsp n fuel))
  :hints (("Goal" :induct (fn-nbw-decimal-tick n fuel chars)
                  :in-theory (disable floor mod digit-to-char))))

(defthm fn-nbw-decimal-codec-fits
  (implies (and (natp n) (<= n *fn-record-max-octets*))
           (fn-nbw-decimal-fitsp n 10))
  :hints (("Goal" :expand ((:free (n) (fn-nbw-decimal-fitsp n 10))
                           (:free (n) (fn-nbw-decimal-fitsp n 9))
                           (:free (n) (fn-nbw-decimal-fitsp n 8))
                           (:free (n) (fn-nbw-decimal-fitsp n 7))
                           (:free (n) (fn-nbw-decimal-fitsp n 6))
                           (:free (n) (fn-nbw-decimal-fitsp n 5))
                           (:free (n) (fn-nbw-decimal-fitsp n 4))
                           (:free (n) (fn-nbw-decimal-fitsp n 3))
                           (:free (n) (fn-nbw-decimal-fitsp n 2))
                           (:free (n) (fn-nbw-decimal-fitsp n 1))
                           (:free (n) (fn-nbw-decimal-fitsp n 0)))
                  :in-theory (disable floor))))

(defthm fn-nbw-decimal-tick-length
  (implies (true-listp chars)
           (equal (len (mv-nth 1 (fn-nbw-decimal-tick n fuel chars)))
                  (if (mv-nth 0 (fn-nbw-decimal-tick n fuel chars))
                      (max 1 (+ (len chars)
                                (mv-nth 3 (fn-nbw-decimal-tick n fuel chars))))
                    (+ (len chars) (mv-nth 3 (fn-nbw-decimal-tick n fuel chars))))))
  :hints (("Goal" :induct (fn-nbw-decimal-tick n fuel chars)
                  :in-theory (disable floor mod digit-to-char))))

(defthm fn-nbw-decimal-tick-keeps-chars
  (implies (character-listp chars)
           (character-listp (mv-nth 1 (fn-nbw-decimal-tick n fuel chars))))
  :hints (("Goal" :induct (fn-nbw-decimal-tick n fuel chars)
                  :in-theory (disable floor mod digit-to-char))))

(defthm fn-nbw-decimal-tick-done-zero
  (implies (and (natp n) (mv-nth 0 (fn-nbw-decimal-tick n fuel chars)))
           (equal (mv-nth 2 (fn-nbw-decimal-tick n fuel chars)) 0))
  :hints (("Goal" :induct (fn-nbw-decimal-tick n fuel chars)
                  :in-theory (disable floor mod digit-to-char))))

; This is the codec's representation limit, not an admission policy. A
; profile/writer invariant must supply it at the actual served entry.
(defthm fn-nbw-decimal-codec-complete
  (implies (and (natp n) (<= n *fn-record-max-octets*))
           (let ((r (fn-nbw-decimal-tick n 10 nil)))
             (and (mv-nth 0 r) (equal (mv-nth 2 r) 0)
                  (character-listp (mv-nth 1 r))
                  (<= (mv-nth 3 r) 10)
                  (< 0 (len (mv-nth 1 r)))
                  (<= (len (mv-nth 1 r)) 10)
                  (equal (mv-nth 1 r) (explode-nonnegative-integer n 10 nil)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-nbw-decimal-tick-residual (fuel 10) (chars nil))
                        (:instance fn-nbw-decimal-tick-length (fuel 10) (chars nil)))
                  :in-theory (disable fn-nbw-decimal-tick fn-nbw-decimal-fitsp
                                      fn-nbw-decimal-tick-length fn-nbw-decimal-tick-residual))))

(defthm fn-nbw-decimal-tick-keeps-natural
  (implies (natp n) (natp (mv-nth 2 (fn-nbw-decimal-tick n fuel chars))))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-nbw-decimal-tick n fuel chars)
                  :in-theory (disable floor mod digit-to-char))))

(defthm fn-nbw-decimal-tick-progress
  (implies (and (posp n) (posp fuel))
           (< (mv-nth 2 (fn-nbw-decimal-tick n fuel chars)) n))
  :rule-classes nil
  :hints (("Goal" :induct (fn-nbw-decimal-tick n fuel chars)
                  :in-theory (disable floor mod digit-to-char))))
