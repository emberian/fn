; Cold metadata establishment walks actual ORIGINAL snapshots one worker
; quantum at a time, then reverses one evidence link per tick. It never
; replays identity, republishes a source token, or validates a whole context.
(in-package "ACL2")
(include-book "replay-enrollment-producer")

; Fixed7: phase, exact original context, remaining snapshots, reversed
; evidence, one snapshot worker, original issued source, ordered evidence.
(defun fn-rse-bootstrap-state (phase original remaining reversed worker source ordered)
 (declare (xargs :guard t))
 (list phase original remaining reversed worker source ordered))
(defun fn-rse-bootstrap-begin (original source)
 (declare (xargs :guard t))
 (fn-rse-bootstrap-state :seek original (fn-stxk-context-snapshots original)
                         nil nil source nil))
(defun fn-rse-bootstrap-step (s)
 (declare (xargs :guard t))
 (if (not (fn-rsc-widthp 7 s)) (mv :refused s)
  (let ((phase (fn-rsc-at 0 s)) (original (fn-rsc-at 1 s))
        (remaining (fn-rsc-at 2 s)) (reversed (fn-rsc-at 3 s))
        (worker (fn-rsc-at 4 s)) (source (fn-rsc-at 5 s))
        (ordered (fn-rsc-at 6 s)))
   (cond
    ((eq phase :done) (mv :done s))
    ((eq phase :seek)
     (cond
      ((consp remaining)
       (mv :working (fn-rse-bootstrap-state :decode original remaining reversed
        (fn-rse-snapshot-evidence-begin (car remaining) source) source nil)))
      ((null remaining)
       (mv :working (fn-rse-bootstrap-state :reverse original nil reversed nil source nil)))
      (t (mv :refused s))))
    ((eq phase :decode)
     (if (not (consp remaining)) (mv :refused s)
      (mv-let (word next) (fn-rse-produced-step worker)
       (cond
        ((eq word :refused) (mv :refused s))
        ((eq word :done)
         (let ((entry (fn-rse-snapshot-evidence-readout next)))
          (if (fn-rse-evidence-shapep entry)
           (mv :working (fn-rse-bootstrap-state :seek original (cdr remaining)
                           (cons entry reversed) nil source nil))
           (mv :refused s))))
        (t (mv :working (fn-rse-bootstrap-state :decode original remaining reversed
                                              next source nil)))))))
    ((eq phase :reverse)
     (cond
      ((consp reversed)
       (mv :working (fn-rse-bootstrap-state :reverse original nil (cdr reversed)
                         nil source (cons (car reversed) ordered))))
      ((null reversed)
       (mv :done (fn-rse-bootstrap-state :done original nil nil nil source ordered)))
      (t (mv :refused s))))
    (t (mv :refused s))))))
(defun fn-rse-bootstrap-readout (s)
 (declare (xargs :guard t))
 (cond ((not (fn-rsc-widthp 7 s)) :refused)
       ((eq (fn-rsc-at 0 s) :done)
        (list :established (fn-rsc-at 1 s) (fn-rsc-at 6 s) (fn-rsc-at 5 s)))
       (t :pending)))

(defthm fn-rse-bootstrap-step-preserves-original-context-and-source
 (implies (fn-rsc-widthp 7 s)
  (let ((next (mv-nth 1 (fn-rse-bootstrap-step s))))
   (and (fn-rsc-widthp 7 next)
        (equal (fn-rsc-at 1 next) (fn-rsc-at 1 s))
        (equal (fn-rsc-at 5 next) (fn-rsc-at 5 s)))))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-rse-bootstrap-step fn-rse-bootstrap-state fn-rsc-at fn-rsc-widthp)
       (fn-rse-snapshot-evidence-begin fn-rse-produced-step
        fn-rse-snapshot-evidence-readout fn-rse-evidence-shapep)))))
