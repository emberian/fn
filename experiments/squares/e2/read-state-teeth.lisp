; Copied for fn2 squares E2 from acl2aiguide/examples/transport/read-state-teeth.lisp
; Source commit: 2283433658784eb4767192508f0e5135a8c939b1
; Original content follows unchanged; all includes resolve inside this copy.
; examples/transport/read-state-teeth.lisp
;
; What it shows: the teeth of Experiment A, as evaluated witnesses first and
; refused events second.
;
; 1. A relation equal to the observation is too weak.  The observation in
;    hand is the count of read articles up to bound 2.  Two histories that
;    give the same count now, ((:READ 1)) and ((:READ 2)), give different
;    counts after one more event, (:READ 1).  So "equal answers now" is not
;    closed under the steps, and the contract refuses it: the functional
;    instance of FC-REL-FOLD with that relation fails by name.  The
;    certificate's relation must be strictly stronger than the observation
;    (here, agreement on every article), closed under every event kind.
;
; 2. A buggy summary.  RS-S-BAD-STEP compacts with an off-by-one: it also
;    advances HWM over a gap of one when HWM+2 is in ABOVE.  After
;    (:READ 1) (:READ 3) it says article 2 is read; the history says not.
;    Its per-event lemma for :READ is refused by name, and the concrete
;    related pair whose step is unrelated is a theorem.
;
; Cited by examples/transport/README.md, "Experiment A".

(in-package "ACL2")
(include-book "read-state-transport")
(include-book "std/testing/must-fail" :dir :system)

; ---------------------------------------------------------------------------
; 1. Equal now, different after one event.

(defun rs-count2-rel (h1 h2)
  (equal (rs-h-obs-count h1 2) (rs-h-obs-count h2 2)))

; The observation as a query function: every query asks the count at 2.
(defun rs-h-count2-obs (h q)
  (declare (ignore q))
  (rs-h-obs-count h 2))

(defconst *rs-s1* '((:read 1)))
(defconst *rs-s2* '((:read 2)))
(defconst *rs-suffix* '((:read 1)))

; The witness, evaluated.
(assert-event
 (and (equal (rs-h-obs-count *rs-s1* 2) 1)
      (equal (rs-h-obs-count *rs-s2* 2) 1)
      (equal (rs-h-obs-count (rs-h-fold *rs-s1* *rs-suffix*) 2) 1)
      (equal (rs-h-obs-count (rs-h-fold *rs-s2* *rs-suffix*) 2) 2)))

; The same fact as a theorem about the relation: related now, unrelated
; after one step.
(defthm rs-count2-rel-not-step-closed
  (and (rs-count2-rel *rs-s1* *rs-s2*)
       (not (rs-count2-rel (rs-h-step *rs-s1* '(:read 1))
                           (rs-h-step *rs-s2* '(:read 1)))))
  :rule-classes nil)

; The stronger relation already separates them: they disagree on article 1.
(assert-event (not (equal (rs-h-obs-read *rs-s1* 1) (rs-h-obs-read *rs-s2* 1))))

; The instance of FC-REL-STEP's relation conjunct for the weak relation is
; false, at this pair and this event: no proof of the functional instance
; below can exist, so its failure is not an automation failure.
(defthm rs-count2-rel-step-obligation-false
  (not (implies (and (rs-h-ok *rs-s1*) (rs-h-ok *rs-s2*)
                     (rs-count2-rel *rs-s1* *rs-s2*))
                (rs-count2-rel (rs-h-step *rs-s1* '(:read 1))
                               (rs-h-step *rs-s2* '(:read 1)))))
  :rule-classes nil)

; The contract refuses the weak relation by name.  (A lambda with a DECLARE
; is not a pseudo-lambda, and a must-fail on that syntax error would pass
; for the wrong reason; hence the named RS-H-COUNT2-OBS.  The failure was
; read in the prover's output: the FC-REL-STEP obligation, then the
; fallback induction, stop at a step that changes the count at 2.)
(must-fail
 (defthm rs-count2-rel-fold
   (implies (and (rs-h-ok h1) (rs-h-ok h2) (rs-count2-rel h1 h2))
            (rs-count2-rel (rs-h-fold h1 j) (rs-h-fold h2 j)))
   :hints (("Goal"
            :use ((:functional-instance fc-rel-fold
                                        (fc1-init rs-h-init) (fc2-init rs-h-init)
                                        (fc1-step rs-h-step) (fc2-step rs-h-step)
                                        (fc1-obs rs-h-count2-obs)
                                        (fc2-obs rs-h-count2-obs)
                                        (fc1-ok rs-h-ok) (fc2-ok rs-h-ok)
                                        (fc-rel rs-count2-rel)
                                        (fc1-fold rs-h-fold) (fc2-fold rs-h-fold)))))))

; ---------------------------------------------------------------------------
; 2. A buggy summary.

(defun rs-bad-compact (hwm above)
  (declare (xargs :measure (len above)))
  (cond ((and (consp above) (equal (car above) (+ 1 hwm)))
         (rs-bad-compact (+ 1 hwm) (cdr above)))
        ((and (consp above) (equal (car above) (+ 2 hwm)))   ; the bug
         (rs-bad-compact (+ 2 hwm) (cdr above)))
        (t (cons hwm above))))

(defun rs-s-bad-step (s e)
  (let ((hwm (car s)) (above (cdr s)))
    (cond ((not (rs-eventp e)) s)
          ((eq (car e) :read)
           (if (<= (cadr e) hwm) s (rs-bad-compact hwm (rs-insert (cadr e) above))))
          (t (let ((h (max hwm (cadr e))))
               (rs-bad-compact h (rs-drop-upto h above)))))))

(defun rs-s-bad-fold (s j)
  (if (atom j) s (rs-s-bad-fold (rs-s-bad-step s (car j)) (cdr j))))

; The witness, evaluated: the bad summary says 2 is read, the history and
; the correct summary say not.
(assert-event
 (let ((j '((:read 1) (:read 3))))
   (and (equal (rs-s-obs-read (rs-s-bad-fold (rs-s-init) j) 2) t)
        (equal (rs-h-obs-read (rs-h-fold (rs-h-init) j) 2) nil)
        (equal (rs-s-obs-read (rs-s-fold (rs-s-init) j) 2) nil))))

; A related pair whose bad step is unrelated.  Related before: the history
; ((:READ 1)) and the summary (1), the correct converter's output.
(defthm rs-bad-step-breaks-relation
  (and (rs-s-ok '(1))
       (rs-same-reads '((:read 1)) '(1))
       (not (rs-same-reads (rs-h-step '((:read 1)) '(:read 3))
                           (rs-s-bad-step '(1) '(:read 3)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance rs-summarize-related (h '((:read 1))))
                        (:instance rs-same-reads-necc
                                   (h (rs-h-step '((:read 1)) '(:read 3)))
                                   (s (rs-s-bad-step '(1) '(:read 3)))
                                   (n 2))))))

; Its per-event lemma for :READ is refused.
(must-fail
 (defthm rs-s-bad-same-reads-of-read
   (implies (and (rs-s-ok s) (rs-same-reads h s)
                 (rs-eventp e) (eq (car e) :read))
            (rs-same-reads (rs-h-step h e) (rs-s-bad-step s e)))
   :hints (("Goal"
            :expand ((rs-same-reads (rs-h-step h e) (rs-s-bad-step s e)))
            :use ((:instance rs-same-reads-necc
                             (n (rs-same-reads-witness (rs-h-step h e)
                                                       (rs-s-bad-step s e)))))))))
