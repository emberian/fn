; Copied for fn2 squares E2 from acl2aiguide/examples/transport/read-state-history.lisp
; Source commit: 2283433658784eb4767192508f0e5135a8c939b1
; Original content follows unchanged; all includes resolve inside this copy.
; examples/transport/read-state-history.lisp
;
; What it shows: the retained-history representation of one consumer's
; monotone read-state in one group (Experiment A).  Events are (:READ N),
; article N read (N positive), and (:CATCHUP H), every article up to H read.
; The state is the event list itself, newest first.  Two observations:
; RS-H-OBS-READ, "is article N read?", a Boolean (a scan, never a
; MEMBER-EQUAL tail), and RS-H-OBS-COUNT, the number of read articles in
; 1..B, which is not pointwise.  RS-H-OBS answers a query (:READ N) or
; (:COUNT B).
;
; Cited by examples/transport/README.md, "Experiment A".

(in-package "ACL2")

(defun rs-eventp (e)
  (declare (xargs :guard t))
  (and (consp e) (consp (cdr e)) (null (cddr e))
       (or (and (eq (car e) :read) (posp (cadr e)))
           (and (eq (car e) :catchup) (natp (cadr e))))))

; Does event E mark article N read?
(defun rs-event-covers (e n)
  (declare (xargs :guard t))
  (and (rs-eventp e) (posp n)
       (if (eq (car e) :read)
           (equal (cadr e) n)
         (<= n (cadr e)))))

(defun rs-h-init () (declare (xargs :guard t)) nil)
(defun rs-h-ok (h) (declare (xargs :guard t)) (true-listp h))
(defun rs-h-step (h e) (declare (xargs :guard t)) (cons e h))

(defun rs-h-fold (h j)
  (declare (xargs :guard t))
  (if (atom j) h (rs-h-fold (rs-h-step h (car j)) (cdr j))))

(defun rs-h-obs-read (h n)
  (declare (xargs :guard t))
  (cond ((atom h) nil)
        ((rs-event-covers (car h) n) t)
        (t (rs-h-obs-read (cdr h) n))))

(defun rs-h-obs-count (h b)
  (declare (xargs :guard (natp b)))
  (if (zp b)
      0
    (+ (if (rs-h-obs-read h b) 1 0)
       (rs-h-obs-count h (1- b)))))

(defun rs-h-obs (h q)
  (declare (xargs :guard t))
  (if (and (consp q) (eq (car q) :count) (consp (cdr q)))
      (rs-h-obs-count h (nfix (cadr q)))
    (rs-h-obs-read h (and (consp q) (consp (cdr q)) (cadr q)))))

(defthm rs-h-obs-read-of-step
  (equal (rs-h-obs-read (rs-h-step h e) n)
         (or (rs-event-covers e n) (rs-h-obs-read h n))))

(defthm rs-h-ok-of-step
  (implies (rs-h-ok h) (rs-h-ok (rs-h-step h e))))

(in-theory (disable rs-h-step))

(assert-event (equal (rs-h-obs (rs-h-fold (rs-h-init) '((:read 3) (:catchup 1)))
                               '(:count 4))
                     2))
