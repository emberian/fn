; Copied for fn2 squares E2 from acl2aiguide/examples/transport/read-state-summary.lisp
; Source commit: 2283433658784eb4767192508f0e5135a8c939b1
; Original content follows unchanged; all includes resolve inside this copy.
; examples/transport/read-state-summary.lisp
;
; What it shows: the summary representation of the same read-state
; (Experiment A).  The state is (HWM . ABOVE): every article 1..HWM is read,
; and ABOVE is the strictly increasing list of read articles above HWM.
; After each step the summary is compacted: entries <= HWM are dropped and
; HWM advances while HWM+1 is in ABOVE.  RS-S-OK is the admissibility
; predicate (HWM natural, ABOVE strictly increasing above HWM, compacted).
; RS-SUMMARIZE is the converter: the summary step folded over a history.
; The lemmas say, per event kind, how the step moves the read observation;
; the transport book relates this to the history.
;
; Cited by examples/transport/README.md, "Experiment A".

(in-package "ACL2")
(include-book "read-state-history")

(defun rs-above-okp (lo above)
  (declare (xargs :guard t))
  (if (atom above)
      (null above)
    (and (integerp (car above))
         (rationalp lo)
         (< lo (car above))
         (rs-above-okp (car above) (cdr above)))))

(defun rs-s-ok (s)
  (declare (xargs :guard t))
  (and (consp s)
       (natp (car s))
       (rs-above-okp (car s) (cdr s))
       (not (and (consp (cdr s)) (equal (cadr s) (+ 1 (car s)))))))

(defun rs-insert (n above)
  (declare (xargs :guard (and (rationalp n) (rational-listp above))))
  (cond ((atom above) (list n))
        ((< n (car above)) (cons n above))
        ((equal n (car above)) above)
        (t (cons (car above) (rs-insert n (cdr above))))))

; Drop the prefix of entries <= K.
(defun rs-drop-upto (k above)
  (declare (xargs :guard (and (rationalp k) (rational-listp above))))
  (cond ((atom above) nil)
        ((<= (car above) k) (rs-drop-upto k (cdr above)))
        (t above)))

(defun rs-compact (hwm above)
  (declare (xargs :guard (and (integerp hwm) (true-listp above))
                  :measure (len above)))
  (if (and (consp above) (equal (car above) (+ 1 hwm)))
      (rs-compact (+ 1 hwm) (cdr above))
    (cons hwm above)))

(defun rs-s-init () (declare (xargs :guard t)) (cons 0 nil))

(defun rs-s-step (s e)
  (declare (xargs :guard t :verify-guards nil))
  (let ((hwm (car s)) (above (cdr s)))
    (cond ((not (rs-eventp e)) s)
          ((eq (car e) :read)
           (if (<= (cadr e) hwm) s (rs-compact hwm (rs-insert (cadr e) above))))
          (t (let ((h (max hwm (cadr e))))
               (rs-compact h (rs-drop-upto h above)))))))

(defun rs-s-fold (s j)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom j) s (rs-s-fold (rs-s-step s (car j)) (cdr j))))

; The converter: a history (newest first) to its summary.
(defun rs-summarize (h)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom h) (rs-s-init) (rs-s-step (rs-summarize (cdr h)) (car h))))

; Membership as a Boolean scan with guard T.
(defun rs-memberp (n above)
  (declare (xargs :guard t))
  (cond ((atom above) nil)
        ((equal n (car above)) t)
        (t (rs-memberp n (cdr above)))))

(defun rs-covered (hwm above n)
  (declare (xargs :guard t))
  (if (and (posp n)
           (or (and (rationalp hwm) (<= n hwm))
               (rs-memberp n above)))
      t
    nil))

(defun rs-s-obs-read (s n)
  (declare (xargs :guard t))
  (and (consp s) (rs-covered (car s) (cdr s) n)))

(defun rs-s-obs-count (s b)
  (declare (xargs :guard (natp b)))
  (if (zp b)
      0
    (+ (if (rs-s-obs-read s b) 1 0)
       (rs-s-obs-count s (1- b)))))

(defun rs-s-obs (s q)
  (declare (xargs :guard t))
  (if (and (consp q) (eq (car q) :count) (consp (cdr q)))
      (rs-s-obs-count s (nfix (cadr q)))
    (rs-s-obs-read s (and (consp q) (consp (cdr q)) (cadr q)))))

; ---------------------------------------------------------------------------
; Admissibility is preserved.

(defthm rs-above-okp-of-insert
  (implies (and (rs-above-okp lo above) (integerp n) (rationalp lo) (< lo n))
           (rs-above-okp lo (rs-insert n above))))

(defthm rs-above-okp-of-drop-upto
  (implies (and (rs-above-okp lo above) (rationalp k) (<= lo k))
           (rs-above-okp k (rs-drop-upto k above))))

(defthm rs-s-ok-of-compact
  (implies (and (natp hwm) (rs-above-okp hwm above))
           (rs-s-ok (rs-compact hwm above))))

(defthm rs-s-ok-of-step
  (implies (rs-s-ok s) (rs-s-ok (rs-s-step s e))))

(defthm rs-s-ok-of-init (rs-s-ok (rs-s-init)))

(defthm rs-s-ok-of-summarize (rs-s-ok (rs-summarize h)))

; ---------------------------------------------------------------------------
; The read observation across each piece of the step.

(defthm rs-memberp-of-insert
  (equal (rs-memberp n (rs-insert x above))
         (or (equal n x) (rs-memberp n above))))

(defthm rs-covered-of-drop-upto
  (implies (rationalp k)
           (equal (rs-covered k (rs-drop-upto k above) n)
                  (rs-covered k above n))))

(defthm rs-covered-of-compact
  (implies (integerp hwm)
           (equal (rs-covered (car (rs-compact hwm above))
                              (cdr (rs-compact hwm above))
                              n)
                  (rs-covered hwm above n))))

(in-theory (disable rs-compact rs-insert rs-drop-upto))

; Per event kind: what the step does to "is N read?".
(defthm rs-s-obs-read-of-read-step
  (implies (and (rs-s-ok s) (rs-eventp e) (eq (car e) :read))
           (equal (rs-s-obs-read (rs-s-step s e) n)
                  (or (rs-event-covers e n) (rs-s-obs-read s n)))))

(defthm rs-s-obs-read-of-catchup-step
  (implies (and (rs-s-ok s) (rs-eventp e) (eq (car e) :catchup))
           (equal (rs-s-obs-read (rs-s-step s e) n)
                  (or (rs-event-covers e n) (rs-s-obs-read s n)))))

(defthm rs-s-obs-read-of-other-step
  (implies (not (rs-eventp e))
           (equal (rs-s-obs-read (rs-s-step s e) n)
                  (or (rs-event-covers e n) (rs-s-obs-read s n)))))

(in-theory (disable rs-s-step))

(assert-event (equal (rs-summarize '((:read 3) (:read 2) (:catchup 1)))
                     '(3)))
(assert-event (equal (rs-summarize '((:read 5) (:catchup 1))) '(1 5)))
