; Byte quanta over immutable NOV column references (PRF-1066, Q5c/J1).
; The pieces are cached strings or already-owned octet lists (the numeric
; fields and delimiters). A state holds the piece list and a string offset;
; no runtime conversion or concatenation of a complete field/row occurs.
; Every iteration consumes one work unit, including empty-piece transitions.
; The logical remaining bytes are theorem vocabulary, never host-called.
(in-package "ACL2")
(include-book "records-shape")

(defun fn-nbw-piecesp (pieces)
  (declare (xargs :guard t))
  (if (consp pieces)
      (and (or (stringp (car pieces)) (fn-cbor-octet-listp (car pieces)))
           (fn-nbw-piecesp (cdr pieces)))
    (null pieces)))

(defun-nx fn-nbw-remaining (pieces pos)
  (if (consp pieces)
      (append (if (stringp (car pieces))
                  (nthcdr (nfix pos) (fn-record-string-octets (car pieces)))
                (car pieces))
              (fn-nbw-remaining (cdr pieces) 0))
    nil))

(defun fn-nbw-step-aux (pieces pos fuel acc used)
  (declare (xargs :guard (and (fn-nbw-piecesp pieces) (natp pos)
                              (natp fuel) (true-listp acc) (natp used))
                  :measure (nfix fuel)))
  (if (or (zp fuel) (atom pieces))
      (mv (revappend acc nil) pieces pos used)
    (let ((part (car pieces)))
      (cond
       ((stringp part)
        (if (< pos (length part))
            (fn-nbw-step-aux pieces (+ 1 pos) (- fuel 1)
                             (cons (char-code (char part pos)) acc) (+ 1 used))
          (fn-nbw-step-aux (cdr pieces) 0 (- fuel 1) acc (+ 1 used))))
       ((consp part)
        (fn-nbw-step-aux (cons (cdr part) (cdr pieces)) 0 (- fuel 1)
                         (cons (car part) acc) (+ 1 used)))
       (t (fn-nbw-step-aux (cdr pieces) 0 (- fuel 1) acc (+ 1 used)))))))

(defun fn-nbw-step (pieces pos fuel)
  (declare (xargs :guard (and (fn-nbw-piecesp pieces) (natp pos) (natp fuel))))
  (fn-nbw-step-aux pieces pos fuel nil 0))

; Each remaining character/octet and each piece-end transition costs one
; unit.  This includes empty optional fields, which must yield progress
; even in a quantum that produces no octet.  Demand is proof vocabulary.
(defun-nx fn-nbw-demand (pieces pos)
  (if (consp pieces)
      (+ 1 (if (stringp (car pieces))
               (nfix (- (length (car pieces)) (nfix pos)))
             (len (car pieces)))
         (fn-nbw-demand (cdr pieces) 0))
    0))

(defthm fn-nbw-step-pays-exact-demand
  (implies (and (fn-nbw-piecesp pieces) (natp pos) (natp used))
           (equal (+ (- (mv-nth 3 (fn-nbw-step-aux pieces pos fuel acc used)) used)
                     (fn-nbw-demand
                      (mv-nth 1 (fn-nbw-step-aux pieces pos fuel acc used))
                      (mv-nth 2 (fn-nbw-step-aux pieces pos fuel acc used))))
                  (fn-nbw-demand pieces pos)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-nbw-step-aux pieces pos fuel acc used)
                  :in-theory (enable fn-nbw-demand))))

(defthm fn-nbw-step-keeps-pieces
  (implies (fn-nbw-piecesp pieces)
           (fn-nbw-piecesp (mv-nth 1 (fn-nbw-step-aux pieces pos fuel acc used)))))

(defthm fn-nbw-step-keeps-position
  (implies (natp pos)
           (natp (mv-nth 2 (fn-nbw-step-aux pieces pos fuel acc used))))
  :hints (("Goal" :induct (fn-nbw-step-aux pieces pos fuel acc used)))
  :rule-classes :type-prescription)

(defthm fn-nbw-step-work-at-most-fuel
  (implies (natp fuel)
           (and (<= used (mv-nth 3 (fn-nbw-step-aux pieces pos fuel acc used)))
                (<= (mv-nth 3 (fn-nbw-step-aux pieces pos fuel acc used))
                    (+ used fuel))))
  :rule-classes nil)

; The output representation stays octets, including CHAR's full ACL2
; character range. Offset/fuel/work hypotheses are unnecessary for this
; property; the logical function remains total outside its executable guard.
(local
 (defthm fn-nbw-octets-of-revappend
   (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))
            (fn-cbor-octet-listp (revappend a b)))
   :hints (("Goal" :induct (revappend a b)
                   :in-theory (enable fn-cbor-octet-listp)))))

(defthm fn-nbw-step-keeps-octets
  (implies (and (fn-nbw-piecesp pieces) (fn-cbor-octet-listp acc))
           (fn-cbor-octet-listp
            (mv-nth 0 (fn-nbw-step-aux pieces pos fuel acc used))))
  :hints (("Goal" :induct (fn-nbw-step-aux pieces pos fuel acc used)
                  :in-theory (enable fn-cbor-octet-listp fn-cbor-octetp))))

(local
 (defthm fn-nbw-len-of-revappend
   (equal (len (revappend a b)) (+ (len a) (len b)))
   :hints (("Goal" :induct (revappend a b)))))

(defthm fn-nbw-step-output-at-most-fuel
  (implies (natp fuel)
           (<= (len (mv-nth 0 (fn-nbw-step-aux pieces pos fuel acc used)))
               (+ (len acc) fuel)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable revappend))))

(local
 (defthm fn-nbw-string-octets-tail
   (equal (nthcdr n (fn-record-string-octets-aux chars))
          (fn-record-string-octets-aux (nthcdr n chars)))
   :hints (("Goal" :induct (nthcdr n chars)
                   :in-theory (enable fn-record-string-octets-aux nthcdr)))))

(local
 (defthm fn-nbw-char-tail-next
   (implies (and (natp pos) (< pos (len chars)))
            (equal (fn-record-string-octets-aux (nthcdr pos chars))
                   (cons (char-code (nth pos chars))
                         (fn-record-string-octets-aux (nthcdr (+ 1 pos) chars)))))
   :hints (("Goal" :induct (nthcdr pos chars)
                   :in-theory (enable fn-record-string-octets-aux nthcdr nth)))))

(local
 (defthm fn-nbw-string-tail-next
   (implies (and (stringp text) (natp pos) (< pos (length text)))
            (equal (nthcdr pos (fn-record-string-octets text))
                   (cons (char-code (char text pos))
                         (nthcdr (+ 1 pos) (fn-record-string-octets text)))))
   :hints (("Goal" :do-not-induct t
                   :use ((:instance fn-nbw-char-tail-next (chars (coerce text 'list))))
                   :in-theory (e/d (fn-record-string-octets char)
                                   (fn-record-string-octets-aux nthcdr nth))))))

(local
 (defthm fn-nbw-char-tail-empty
   (implies (and (true-listp chars) (natp pos) (<= (len chars) pos))
            (equal (nthcdr pos chars) nil))
   :hints (("Goal" :induct (nthcdr pos chars)))))

(local
 (defthm fn-nbw-string-tail-empty
   (implies (and (stringp text) (natp pos) (<= (length text) pos))
            (equal (nthcdr pos (fn-record-string-octets text)) nil))
   :hints (("Goal" :in-theory (enable fn-record-string-octets)))))

(local
 (defthm fn-nbw-append-revappend
   (equal (append (revappend a b) c) (revappend a (append b c)))
   :hints (("Goal" :induct (revappend a b)))))

(local
 (defthm fn-nbw-append-associative
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-nbw-revappend-cons
   (equal (revappend (cons x a) b) (revappend a (cons x b)))))

(defthm fn-nbw-step-preserves-complete-residual
  (implies (and (fn-nbw-piecesp pieces) (natp pos))
           (let ((next (fn-nbw-step-aux pieces pos fuel acc used)))
             (equal (append (mv-nth 0 next)
                            (fn-nbw-remaining (mv-nth 1 next) (mv-nth 2 next)))
                    (append (revappend acc nil) (fn-nbw-remaining pieces pos)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-nbw-step-aux pieces pos fuel acc used)
                  :in-theory (e/d (fn-nbw-remaining)
                                  (fn-record-string-octets revappend)))))

(local
 (defthm fn-nbw-used-is-monotonic
   (implies (natp used)
            (<= used (mv-nth 3 (fn-nbw-step-aux pieces pos fuel acc used))))
   :rule-classes :linear
   :hints (("Goal" :induct (fn-nbw-step-aux pieces pos fuel acc used)))))

(local
 (defthm fn-nbw-active-step-uses-work
   (implies (and (consp pieces) (posp fuel) (natp used))
            (< used (mv-nth 3 (fn-nbw-step-aux pieces pos fuel acc used))))
   :rule-classes :linear
   :hints (("Goal" :expand ((fn-nbw-step-aux pieces pos fuel acc used))
                   :in-theory (disable fn-nbw-step-aux)))))

(defthm fn-nbw-step-makes-bounded-progress
  (implies (and (fn-nbw-piecesp pieces) (natp pos) (posp fuel) (consp pieces))
           (let ((next (fn-nbw-step pieces pos fuel)))
             (and (fn-nbw-piecesp (mv-nth 1 next))
                  (natp (mv-nth 2 next))
                  (< 0 (mv-nth 3 next))
                  (<= (mv-nth 3 next) fuel)
                  (<= (len (mv-nth 0 next)) fuel)
                  (< (fn-nbw-demand (mv-nth 1 next) (mv-nth 2 next))
                     (fn-nbw-demand pieces pos))
                  (equal (append (mv-nth 0 next)
                                 (fn-nbw-remaining (mv-nth 1 next) (mv-nth 2 next)))
                         (fn-nbw-remaining pieces pos)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-nbw-step-pays-exact-demand (acc nil) (used 0))
                        (:instance fn-nbw-step-work-at-most-fuel (acc nil) (used 0))
                        (:instance fn-nbw-step-output-at-most-fuel (acc nil) (used 0))
                        (:instance fn-nbw-step-preserves-complete-residual (acc nil) (used 0)))
                  :in-theory (e/d (fn-nbw-step)
                                  (fn-nbw-step-aux fn-nbw-piecesp
                                   fn-nbw-remaining fn-nbw-demand)))))
