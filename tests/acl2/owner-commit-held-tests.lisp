; Ground witnesses and teeth for books/owner-commit-held.lisp (ruling 19).
(in-package "ACL2")
(include-book "../../books/owner-commit-held")

; S1/S1b witnesses: a batch whose five effects return :ok runs START under
; the owner, the five phases off it, then COMPLETE and the held submission
; under the owner -- the inline commit's effects in its order.
(assert-event
 (equal (fn-och-run :started '(:ok :ok :ok :ok :ok))
        '((:owner . :start) (:off . :intents) (:off . :extend) (:off . :append)
          (:off . :fence) (:off . :resolutions) (:owner . :complete) (:owner . :submit))))
(assert-event
 (equal (fn-och-inline :started '(:ok :ok :ok :ok :ok))
        '(:start :intents :extend :append :fence :resolutions :complete :submit)))

; Nothing queued: the caller submits in its one quantum, no I/O off the owner.
(assert-event (equal (fn-och-run :started-none nil) '((:owner . :start) (:owner . :submit))))

; S4 witnesses: an uncertain fence stops with no take; a faulted append faults.
(assert-event
 (equal (fn-och-run :started '(:ok :ok :ok :uncertain))
        '((:owner . :start) (:off . :intents) (:off . :extend) (:off . :append)
          (:off . :fence) (:owner . :stop))))
(assert-event
 (equal (fn-och-run :started '(:ok :ok :eio))
        '((:owner . :start) (:off . :intents) (:off . :extend) (:off . :append)
          (:owner . :fault))))

; S3/S4 teeth: the take is not vacuous -- a fenced job does take the held
; submission, and it does so after the fence.
(assert-event
 (member-equal :submit (fn-och-after-fence
                        (strip-cdrs (fn-och-run :started '(:ok :ok :ok :ok :ok))))))

; S2 teeth: the held flag is what shuts START-NEXT out.  Without it a staged
; batch answers a START-NEXT (:wait) and opens a next batch; with it the same
; event faults and opens nothing.
(assert-event
 (mv-let (a p n h) (fn-och-step :staged nil nil :next-started)
   (declare (ignore p h))
   (and (equal a :wait) n)))
(assert-event
 (mv-let (a p n h) (fn-och-step :staged nil t :next-started)
   (declare (ignore p h))
   (and (equal a :fault) (not n))))

; S1b teeth: a run that moved COMPLETE off the owner is not labelled.
(assert-event
 (not (fn-och-labelsp '((:owner . :start) (:off . :intents) (:off . :complete)))))
(assert-event
 (not (fn-och-labelsp '((:owner . :start) (:owner . :fence)))))

; S5 teeth: the held flag is what keeps the committer off the batch.  Unheld,
; a returned sync wakes the committer to collect (:collect) and a queued
; member to START-NEXT; held, both are :wait and the caller collects.
(assert-event (equal (fn-och-committer-wake :staged nil nil t nil nil) :collect))
(assert-event (equal (fn-och-committer-wake :staged nil nil nil t nil) :start-next))
(assert-event (equal (fn-och-committer-wake :staged nil t t t nil) :wait))
(assert-event (equal (fn-och-caller-wake :staged t t) :collect))
(assert-event (equal (fn-och-caller-wake :staged t nil) :wait))
