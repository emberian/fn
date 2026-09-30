; A row's fixed set of immutable field references, with resumable numerical
; setup and normalization. PRF-1066 component; not yet the served cursor.
(in-package "ACL2")
(include-book "nov-byte-window")
(include-book "nov-decimal-window")
(include-book "nov-span-window")

; These predicates are guard/proof vocabulary. No transition calls them or
; traverses the remaining fields to revalidate a maintained continuation.
(defun fn-npw-partp (part fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (cond
   ((stringp part) t)
   ((and (consp part) (eq (car part) :span))
    (and (true-listp part) (equal (len part) 6)
         (natp (nth 1 part)) (< (nth 1 part) (fn-arena-count fn-arena))
         (natp (nth 2 part)) (natp (nth 3 part))
         (<= (+ (nth 2 part) (nth 3 part))
             (fn-arena-payload-len (nth 1 part) fn-arena))))
   ((and (consp part) (eq (car part) :decimal))
    (and (true-listp part) (equal (len part) 3)
         (natp (nth 1 part)) (character-listp (nth 2 part))))
   ((and (consp part) (eq (car part) :chars)) (character-listp (cdr part)))
   (t (fn-cbor-octet-listp part))))

(defun fn-npw-piecesp (pieces fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (consp pieces)
      (and (fn-npw-partp (car pieces) fn-arena)
           (fn-npw-piecesp (cdr pieces) fn-arena))
    (null pieces)))

(defun-nx fn-npw-part-bytes (part pos fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (cond
   ((stringp part)
    (nthcdr (nfix pos) (fn-record-string-octets part)))
   ((and (consp part) (eq (car part) :span))
    (fn-nsw-remaining (nth 1 part) (nth 2 part) (nth 3 part) (nth 4 part) fn-arena))
   ((and (consp part) (eq (car part) :decimal))
    (fn-record-string-octets-aux
     (explode-nonnegative-integer (nth 1 part) 10 (nth 2 part))))
   ((and (consp part) (eq (car part) :chars))
    (fn-record-string-octets-aux (cdr part)))
   (t part)))

(defun-nx fn-npw-remaining (pieces pos fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (consp pieces)
      (append (fn-npw-part-bytes (car pieces) pos fn-arena)
              (fn-npw-remaining (cdr pieces) 0 fn-arena)) nil))

; One work unit emits zero or one octet. A numerical setup unit divides
; once; its completed character list is drained one character per later
; unit, never converted or reversed wholesale. Span updates retain PIN.
(defun fn-npw-one (pieces pos fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (fn-npw-piecesp pieces fn-arena) (natp pos))
                  :verify-guards nil))
  (if (atom pieces)
      (mv nil nil 0)
    (let ((part (car pieces)) (rest (cdr pieces)))
      (cond
       ((stringp part)
        (if (< pos (length part))
            (mv (list (char-code (char part pos))) pieces (+ 1 pos))
          (mv nil rest 0)))
       ((and (consp part) (eq (car part) :span))
        (mv-let (out at left pending used)
          (fn-nsw-step (nth 1 part) (nth 2 part) (nth 3 part) (nth 4 part) 1 fn-arena)
          (declare (ignore used))
          (mv out (if (and (equal left 0) (not pending)) rest
                    (cons (list :span (nth 1 part) at left pending (nth 5 part)) rest)) 0)))
       ((and (consp part) (eq (car part) :decimal))
        (mv-let (done chars n used) (fn-nbw-decimal-tick (nth 1 part) 1 (nth 2 part))
          (declare (ignore used))
          (mv nil (cons (if done (cons :chars chars) (list :decimal n chars)) rest) 0)))
       ((and (consp part) (eq (car part) :chars))
        (if (consp (cdr part))
            (mv (list (char-code (cadr part))) (cons (cons :chars (cddr part)) rest) 0)
          (mv nil rest 0)))
       ((consp part) (mv (list (car part)) (cons (cdr part) rest) 0))
       (t (mv nil rest 0))))))

(verify-guards fn-npw-one
  :hints (("Goal" :in-theory (enable fn-npw-piecesp fn-npw-partp))))

(defthm fn-npw-one-position-natural
  (implies (natp pos) (natp (mv-nth 2 (fn-npw-one pieces pos fn-arena))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (disable fn-nsw-step fn-nbw-decimal-tick))))

(defthm fn-npw-one-output-bounded
  (<= (len (mv-nth 0 (fn-npw-one pieces pos fn-arena))) 1)
  :rule-classes :linear
  :hints (("Goal" :use ((:instance fn-nsw-output-bounded
                                   (h (nth 1 (car pieces)))
                                   (at (nth 2 (car pieces)))
                                   (left (nth 3 (car pieces)))
                                   (pending (nth 4 (car pieces))) (fuel 1) (acc nil)))
                  :in-theory (e/d (fn-nsw-step)
                                  (fn-nsw-step-aux fn-nbw-decimal-tick)))))

(defthm fn-npw-one-keeps-pieces
  (implies (and (fn-npw-piecesp pieces fn-arena) (natp pos))
           (fn-npw-piecesp (mv-nth 1 (fn-npw-one pieces pos fn-arena)) fn-arena))
  :hints (("Goal" :use ((:instance fn-nsw-position-preserved
                                   (h (nth 1 (car pieces)))
                                   (at (nth 2 (car pieces)))
                                   (left (nth 3 (car pieces)))
                                   (pending (nth 4 (car pieces))) (fuel 1) (acc nil)))
                  :in-theory (e/d (fn-npw-one fn-npw-piecesp fn-npw-partp fn-nsw-step)
                                  (fn-nsw-step-aux fn-nbw-decimal-tick
                                   fn-arena-payload-len fn-arena-count)))))

(local
 (defthm fn-npw-string-one-residual
   (implies (and (stringp text) (natp pos))
            (equal (if (< pos (length text))
                       (cons (char-code (char text pos))
                             (nthcdr (+ 1 pos) (fn-record-string-octets text))) nil)
                   (nthcdr pos (fn-record-string-octets text))))
   :hints (("Goal"
            :use ((:instance fn-nbw-step-preserves-complete-residual
                             (pieces (list text)) (fuel 1) (acc nil) (used 0)))
            :expand ((fn-nbw-step-aux (list text) pos 1 nil 0)
                     (:free (pieces pos acc used) (fn-nbw-step-aux pieces pos 0 acc used)))
            :in-theory (e/d (fn-nbw-step-aux fn-nbw-piecesp fn-nbw-remaining)
                            (fn-record-string-octets char nthcdr))))))

(local
 (defthm fn-npw-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-npw-empty-span-residual
   (equal (fn-nsw-remaining h at 0 nil fn-arena) nil)
   :hints (("Goal" :in-theory (enable fn-nsw-remaining fn-nsw-source)))))

(local
 (defthm fn-npw-done-decimal-consp
   (implies (mv-nth 0 (fn-nbw-decimal-tick n fuel chars))
            (consp (mv-nth 1 (fn-nbw-decimal-tick n fuel chars))))
   :hints (("Goal" :induct (fn-nbw-decimal-tick n fuel chars)
                   :in-theory (disable floor mod digit-to-char)))))

(defthm fn-npw-one-residual
  (implies (and (fn-npw-piecesp pieces fn-arena) (natp pos))
           (let ((r (fn-npw-one pieces pos fn-arena)))
             (equal (append (mv-nth 0 r)
                            (fn-npw-remaining (mv-nth 1 r) (mv-nth 2 r) fn-arena))
                    (fn-npw-remaining pieces pos fn-arena))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((:free (chars) (explode-nonnegative-integer 0 10 chars)))
           :use ((:instance fn-nsw-step-residual
                            (h (nth 1 (car pieces))) (at (nth 2 (car pieces)))
                            (left (nth 3 (car pieces))) (pending (nth 4 (car pieces)))
                            (fuel 1) (acc nil))
                 (:instance fn-nbw-decimal-tick-residual
                            (n (nth 1 (car pieces))) (chars (nth 2 (car pieces))) (fuel 1))
                 (:instance fn-npw-string-one-residual (text (car pieces)))
                 (:instance fn-npw-done-decimal-consp
                            (n (nth 1 (car pieces))) (chars (nth 2 (car pieces))) (fuel 1)))
           :in-theory
           (e/d (fn-npw-one fn-npw-piecesp fn-npw-partp fn-npw-remaining
                 fn-npw-part-bytes fn-nsw-step)
                (fn-nsw-step-aux fn-nbw-decimal-tick fn-nsw-remaining
                 fn-record-string-octets explode-nonnegative-integer
                 fn-arena-payload-len fn-arena-count char nthcdr length nth
                 fn-npw-string-one-residual fn-nbw-decimal-tick-residual
                 fn-npw-done-decimal-consp fn-nbw-decimal-done-is-fitsp)))))

(local
 (defthm fn-npw-octet-types
   (equal (fn-cbor-octet-listp xs) (fn-octet-listp xs))
   :hints (("Goal" :induct (fn-octet-listp xs)
                   :in-theory (enable fn-octet-listp fn-octetp
                                      fn-cbor-octet-listp fn-cbor-octetp)))))

(defthm fn-npw-one-output-octets
  (implies (fn-npw-piecesp pieces fn-arena)
           (fn-cbor-octet-listp (mv-nth 0 (fn-npw-one pieces pos fn-arena))))
  :hints (("Goal" :use ((:instance fn-nsw-output-octets
                                   (h (nth 1 (car pieces))) (at (nth 2 (car pieces)))
                                   (left (nth 3 (car pieces))) (pending (nth 4 (car pieces)))
                                   (fuel 1) (acc nil)))
                  :in-theory
                  (e/d (fn-npw-one fn-npw-piecesp fn-npw-partp fn-nsw-step
                         fn-octet-listp fn-octetp fn-cbor-octet-listp fn-cbor-octetp)
                       (fn-nsw-step-aux fn-nbw-decimal-tick)))))

(defun fn-npw-tick-aux (pieces pos fuel acc fn-arena)
  (declare (xargs :stobjs fn-arena :measure (nfix fuel) :verify-guards nil
                  :guard (and (fn-npw-piecesp pieces fn-arena) (natp pos)
                              (natp fuel) (true-listp acc))))
  (if (or (zp fuel) (atom pieces))
      (mv (revappend acc nil) pieces pos 0)
    (mv-let (out next at) (fn-npw-one pieces pos fn-arena)
      (mv-let (bytes rest final used)
        (fn-npw-tick-aux next at (- fuel 1) (revappend out acc) fn-arena)
        (mv bytes rest final (+ 1 used))))))

(local
 (defthm fn-npw-octets-true-list
   (implies (fn-cbor-octet-listp xs) (true-listp xs))
   :hints (("Goal" :induct (fn-cbor-octet-listp xs)
                   :in-theory (enable fn-cbor-octet-listp fn-octet-listp)))))

(defthm fn-npw-one-output-true-list
  (implies (fn-npw-piecesp pieces fn-arena)
           (true-listp (mv-nth 0 (fn-npw-one pieces pos fn-arena))))
  :hints (("Goal" :use fn-npw-one-output-octets
                  :in-theory (disable fn-npw-one fn-npw-piecesp fn-npw-octet-types))))

(defthm fn-npw-tick-used-natural
  (natp (mv-nth 3 (fn-npw-tick-aux pieces pos fuel acc fn-arena)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-npw-tick-aux pieces pos fuel acc fn-arena)
                  :in-theory (disable fn-npw-one revappend revappend-removal))))

(verify-guards fn-npw-tick-aux
  :hints (("Goal" :use fn-npw-one-output-true-list
                  :in-theory (disable fn-npw-one fn-npw-piecesp
                                      fn-npw-one-output-true-list))))

(defun fn-npw-tick (pieces pos fuel fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (fn-npw-piecesp pieces fn-arena) (natp pos) (natp fuel))))
  (fn-npw-tick-aux pieces pos fuel nil fn-arena))

(defthm fn-npw-tick-work-bounded
  (<= (mv-nth 3 (fn-npw-tick-aux pieces pos fuel acc fn-arena)) (nfix fuel))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-npw-tick-aux pieces pos fuel acc fn-arena)
                  :in-theory (disable fn-npw-one revappend revappend-removal))))

(defthm fn-npw-tick-keeps-pieces
  (implies (and (fn-npw-piecesp pieces fn-arena) (natp pos))
           (fn-npw-piecesp
            (mv-nth 1 (fn-npw-tick-aux pieces pos fuel acc fn-arena)) fn-arena))
  :hints (("Goal" :induct (fn-npw-tick-aux pieces pos fuel acc fn-arena)
                  :in-theory (disable fn-npw-one fn-npw-piecesp
                                      revappend revappend-removal))))

(defthm fn-npw-tick-keeps-position
  (implies (natp pos)
           (natp (mv-nth 2 (fn-npw-tick-aux pieces pos fuel acc fn-arena))))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-npw-tick-aux pieces pos fuel acc fn-arena)
                  :in-theory (disable fn-npw-one revappend revappend-removal))))

(local
 (defthm fn-npw-len-revappend
   (equal (len (revappend a b)) (+ (len a) (len b)))
   :hints (("Goal" :induct (revappend a b)
                   :in-theory (disable revappend-removal)))))

(defthm fn-npw-tick-output-bounded
  (<= (len (mv-nth 0 (fn-npw-tick-aux pieces pos fuel acc fn-arena)))
      (+ (len acc) (nfix fuel)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-npw-tick-aux pieces pos fuel acc fn-arena)
                  :in-theory (disable fn-npw-one revappend revappend-removal))
          ("Subgoal *1/2" :use fn-npw-one-output-bounded)))

(local
 (defthm fn-npw-append-revappend
   (equal (append (revappend a b) c) (revappend a (append b c)))
   :hints (("Goal" :induct (revappend a b)
                   :in-theory (disable revappend-removal)))))

(local
 (defthm fn-npw-double-revappend
   (implies (true-listp a)
            (equal (revappend (revappend a b) nil) (append (revappend b nil) a)))
   :hints (("Goal" :induct (revappend a b)
                   :in-theory (disable revappend-removal)))))

(defthm fn-npw-tick-residual
  (implies (and (fn-npw-piecesp pieces fn-arena) (natp pos))
           (let ((r (fn-npw-tick-aux pieces pos fuel acc fn-arena)))
             (equal (append (mv-nth 0 r)
                            (fn-npw-remaining (mv-nth 1 r) (mv-nth 2 r) fn-arena))
                    (append (revappend acc nil)
                            (fn-npw-remaining pieces pos fn-arena)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-npw-tick-aux pieces pos fuel acc fn-arena)
                  :in-theory (disable fn-npw-one fn-npw-piecesp fn-npw-remaining
                                      revappend revappend-removal
                                      fn-npw-append-revappend fn-npw-one-output-true-list))
          ("Subgoal *1/2" :use (fn-npw-one-residual fn-npw-one-output-true-list))))

(local
 (defthm fn-npw-revappend-octets
   (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))
            (fn-cbor-octet-listp (revappend a b)))
   :hints (("Goal" :induct (revappend a b)
                   :in-theory (e/d (fn-cbor-octet-listp fn-octet-listp)
                                   (revappend-removal))))))

(defthm fn-npw-tick-output-octets
  (implies (and (fn-npw-piecesp pieces fn-arena) (natp pos) (fn-cbor-octet-listp acc))
           (fn-cbor-octet-listp
            (mv-nth 0 (fn-npw-tick-aux pieces pos fuel acc fn-arena))))
  :hints (("Goal" :induct (fn-npw-tick-aux pieces pos fuel acc fn-arena)
                  :in-theory (disable fn-npw-one fn-npw-piecesp fn-npw-octet-types
                                      revappend revappend-removal))
          ("Subgoal *1/2" :use fn-npw-one-output-octets)))

; A well-founded logical demand, not a runtime cost estimate. The numeric
; term deliberately bounds progress for arbitrary naturals; no codec cap
; becomes an article admission or rendering limit.
(defun-nx fn-npw-part-demand (part pos)
  (cond
   ((stringp part) (+ 1 (nfix (- (length part) (nfix pos)))))
   ((and (consp part) (eq (car part) :span))
    (+ 1 (* 2 (nfix (nth 3 part))) (if (nth 4 part) 1 0)))
   ((and (consp part) (eq (car part) :decimal))
    (+ 3 (* 2 (nfix (nth 1 part))) (len (nth 2 part))))
   ((and (consp part) (eq (car part) :chars)) (+ 1 (len (cdr part))))
   (t (+ 1 (len part)))))

(defun-nx fn-npw-demand (pieces pos)
  (if (consp pieces)
      (+ (fn-npw-part-demand (car pieces) pos) (fn-npw-demand (cdr pieces) 0)) 0))

(local
 (defthm fn-npw-decimal-one-length
   (implies (character-listp chars)
            (<= (len (mv-nth 1 (fn-nbw-decimal-tick n 1 chars))) (+ 1 (len chars))))
   :rule-classes :linear
   :hints (("Goal" :use ((:instance fn-nbw-decimal-tick-length (fuel 1))
                          (:instance fn-nbw-decimal-tick-work-bounded (fuel 1)))
                   :in-theory (disable fn-nbw-decimal-tick fn-nbw-decimal-tick-length)))))

(local
 (defthm fn-npw-empty-span-step
   (equal (fn-nsw-step-aux h at 0 nil fuel acc fn-arena)
          (list (revappend acc nil) at 0 nil 0))
   :hints (("Goal" :in-theory (enable fn-nsw-step-aux)))))

(local
 (defthm fn-npw-zero-decimal-done
   (mv-nth 0 (fn-nbw-decimal-tick 0 fuel chars))
   :hints (("Goal" :in-theory (enable fn-nbw-decimal-tick fn-nbw-decimal-fitsp)))))

(defthm fn-npw-one-progress
  (implies (and (fn-npw-piecesp pieces fn-arena) (natp pos) (consp pieces))
           (< (fn-npw-demand (mv-nth 1 (fn-npw-one pieces pos fn-arena))
                             (mv-nth 2 (fn-npw-one pieces pos fn-arena)))
              (fn-npw-demand pieces pos)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-nsw-progress
                            (h (nth 1 (car pieces))) (at (nth 2 (car pieces)))
                            (left (nth 3 (car pieces))) (pending (nth 4 (car pieces)))
                            (fuel 1) (acc nil))
                 (:instance fn-nbw-decimal-tick-progress
                            (n (nth 1 (car pieces))) (chars (nth 2 (car pieces))) (fuel 1))
                 (:instance fn-npw-decimal-one-length
                            (n (nth 1 (car pieces))) (chars (nth 2 (car pieces)))))
           :in-theory
           (e/d (fn-npw-one fn-npw-piecesp fn-npw-partp fn-npw-demand
                 fn-npw-part-demand fn-nsw-step)
                (fn-nsw-step-aux fn-nbw-decimal-tick fn-arena-count fn-arena-payload-len
                 fn-nbw-decimal-fitsp char nthcdr)))))

(defthm fn-npw-demand-natural
  (natp (fn-npw-demand pieces pos))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-npw-demand pieces pos)
                  :in-theory (enable fn-npw-part-demand))))

(defthm fn-npw-tick-demand-nonincreasing
  (implies (and (fn-npw-piecesp pieces fn-arena) (natp pos))
           (<= (fn-npw-demand
                (mv-nth 1 (fn-npw-tick-aux pieces pos fuel acc fn-arena))
                (mv-nth 2 (fn-npw-tick-aux pieces pos fuel acc fn-arena)))
               (fn-npw-demand pieces pos)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-npw-tick-aux pieces pos fuel acc fn-arena)
                  :in-theory (disable fn-npw-one fn-npw-piecesp fn-npw-demand
                                      revappend revappend-removal))
          ("Subgoal *1/2" :use fn-npw-one-progress)))

(defthm fn-npw-tick-progress
  (implies (and (fn-npw-piecesp pieces fn-arena) (natp pos)
                (posp fuel) (consp pieces))
           (< (fn-npw-demand
               (mv-nth 1 (fn-npw-tick-aux pieces pos fuel acc fn-arena))
               (mv-nth 2 (fn-npw-tick-aux pieces pos fuel acc fn-arena)))
              (fn-npw-demand pieces pos)))
  :rule-classes nil
  :hints (("Goal" :use (fn-npw-one-progress
                        (:instance fn-npw-tick-demand-nonincreasing
                                   (pieces (mv-nth 1 (fn-npw-one pieces pos fn-arena)))
                                   (pos (mv-nth 2 (fn-npw-one pieces pos fn-arena)))
                                   (fuel (- fuel 1))
                                   (acc (revappend (mv-nth 0 (fn-npw-one pieces pos fn-arena)) acc))))
                  :expand ((fn-npw-tick-aux pieces pos fuel acc fn-arena))
                  :in-theory (disable fn-npw-tick-aux fn-npw-one fn-npw-piecesp
                                      fn-npw-demand revappend revappend-removal))))

(defthm fn-npw-tick-positive-work
  (implies (and (posp fuel) (consp pieces))
           (< 0 (mv-nth 3 (fn-npw-tick-aux pieces pos fuel acc fn-arena))))
  :rule-classes :linear
  :hints (("Goal" :expand ((fn-npw-tick-aux pieces pos fuel acc fn-arena))
                  :in-theory (disable fn-npw-tick-aux fn-npw-one revappend revappend-removal))))

; The library boundary combines every concrete formatting case. No whole
; field, complete row, or complete decimal is materialized before yielding.
(defthm fn-npw-tick-makes-bounded-progress
  (implies (and (fn-npw-piecesp pieces fn-arena) (natp pos)
                (posp fuel) (consp pieces))
           (let ((r (fn-npw-tick pieces pos fuel fn-arena)))
             (and (fn-npw-piecesp (mv-nth 1 r) fn-arena)
                  (natp (mv-nth 2 r)) (fn-cbor-octet-listp (mv-nth 0 r))
                  (< 0 (mv-nth 3 r)) (<= (mv-nth 3 r) fuel)
                  (<= (len (mv-nth 0 r)) fuel)
                  (equal (append (mv-nth 0 r)
                                 (fn-npw-remaining (mv-nth 1 r) (mv-nth 2 r) fn-arena))
                         (fn-npw-remaining pieces pos fn-arena))
                  (< (fn-npw-demand (mv-nth 1 r) (mv-nth 2 r))
                     (fn-npw-demand pieces pos)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-npw-tick-keeps-pieces (acc nil))
                        (:instance fn-npw-tick-keeps-position (acc nil))
                        (:instance fn-npw-tick-output-octets (acc nil))
                        (:instance fn-npw-tick-positive-work (acc nil))
                        (:instance fn-npw-tick-work-bounded (acc nil))
                        (:instance fn-npw-tick-output-bounded (acc nil))
                        (:instance fn-npw-tick-residual (acc nil))
                        (:instance fn-npw-tick-progress (acc nil)))
                  :in-theory (e/d (fn-npw-tick)
                                  (fn-npw-tick-aux fn-npw-piecesp fn-npw-remaining
                                   fn-npw-demand fn-npw-octet-types)))))
