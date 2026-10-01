; fn: the consumer bound across a reopen (PKT-370, row Q3d (iii) of
; build/coordinator/COMPLETE-BEFORE-6.6.0.md).
;
; The served registration is fn-cp-register-within under MAX, the opened
; Store profile's field 9 (fn-bs-profile-max-consumers; host/owner-host.lisp
; fn-owner-consumer-local-register reads it through host/store-host.lisp
; fn-store-profile-max-consumers).  The committed consumer events are
; interpreted by one fold, fn-cpe-projection-replay
; (books/consumer-store-projection), which re-runs fn-cp-register WITHOUT the
; bound: replay decides the committed event's validity, not its admission
; (whole-state revalidation of what the served decision already decided).
; There is no profile upgrade: a store keeps the profile it was opened under
; (D34; no migrations, 2026-09-28), so the bound a register was admitted
; under is the bound the reopen replays under.
;
; KEYSTONE fn-crb-replay-keeps-the-consumer-bound: when every :register the
; replay applies is one the served admission would write under the opened
; profile's field 9 in the state the replay has reached, the replayed table
; (fn-cp-nth 5) holds at most field 9 entries.  Every other operation (ack,
; rebase, unregister, rollover, bootstrap, a non-consumer record) leaves the
; table no larger (fn-cp-apply-preserves-consumer-capacity, PRF-167).
;
; Host: the open's replay is fn-cpe-projection-replay nil RECORDS 0
; (books/config-observed.lisp, books/checkpoint-auxiliary.lisp); a live
; completion runs one fn-cpe-projection-step of the same fold
; (fn-crb-projection-step-keeps-the-bound).
(in-package "ACL2")
(include-book "consumer-store-projection")
(include-book "store-profile-namespace")

; A step's :register, if the replay applies one, is one the served
; admission under MAX writes in the state S the replay has reached.
(defun fn-crb-step-admittedp (s event max)
  (declare (xargs :guard t))
  (let ((op (fn-cpe-operation event)))
    (or (not (fn-cpe-eventp event))
        (not (eq (fn-cp-nth 0 op) :register))
        (equal (fn-cp-register-within s max (fn-cp-nth 2 op) (fn-cp-nth 1 op)
                                      (fn-cp-nth 3 op) (fn-cp-nth 4 op)
                                      (fn-cp-nth 5 op))
               (list :write op)))))

; The same along the replay: the fold fn-cpe-projection-replay runs, with
; each step's register admitted.
(defun fn-crb-registers-within (s records expected max)
  (declare (xargs :guard t :measure (len records)))
  (if (not (consp records))
      t
    (let ((one (fn-cpe-projection-step s (car records) expected)))
      (and (fn-crb-step-admittedp s (car records) max)
           (if (eq (car one) :ok)
               (fn-crb-registers-within (fn-cp-nth 1 one) (cdr records)
                                        (1+ (nfix expected)) max)
             t)))))

(local (defthm fn-crb-initial-is-empty
  (equal (fn-cp-nth 5 (fn-cp-initial history incarnation frontier)) nil)
  :hints (("Goal" :in-theory (enable fn-cp-initial fn-cp-state-carry fn-cp-nth)))))

(local (defthm fn-crb-carry-entries
  (equal (fn-cp-nth 5 (fn-cp-state-carry history incarnation frontier next entries
                                         authority))
         entries)
  :hints (("Goal" :in-theory (enable fn-cp-state-carry fn-cp-nth)))))

(local (defthm fn-crb-advance-keeps-the-table
  (equal (fn-cp-nth 5 (fn-cpe-projection-advance s next)) (fn-cp-nth 5 s))
  :hints (("Goal" :in-theory (enable fn-cpe-projection-advance)))))

; The decision the replay applies is the register decision only for a register.
(local (defthm fn-crb-register-decision
  (implies (eq (fn-cp-nth 0 op) :register)
           (equal (fn-cpe-projection-decision s op)
                  (fn-cp-register s (fn-cp-nth 2 op) (fn-cp-nth 1 op)
                                  (fn-cp-nth 3 op) (fn-cp-nth 4 op) (fn-cp-nth 5 op))))
  :hints (("Goal" :in-theory (enable fn-cpe-projection-decision)))))

; Replay applies no remote registration: its decision is a refusal.
(local (defthm fn-crb-remote-register-decision
  (implies (eq (fn-cp-nth 0 op) :remote-register)
           (equal (fn-cpe-projection-decision s op) '(:refused :operation)))
  :hints (("Goal" :in-theory (enable fn-cpe-projection-decision)))))

(local (defthm fn-crb-nth-1-of-list
  (equal (fn-cp-nth 1 (list a b)) b)
  :hints (("Goal" :in-theory (enable fn-cp-nth)))))

; A completion's step keeps the table within MAX when its register (if any)
; is admitted.
(defthm fn-crb-projection-step-keeps-the-bound
  (implies (and (<= (len (fn-cp-nth 5 s)) (nfix max))
                (fn-crb-step-admittedp s event max))
           (<= (len (fn-cp-nth 5 (fn-cp-nth 1 (fn-cpe-projection-step s event expected))))
               (nfix max)))
  :hints (("Goal" :use ((:instance fn-cp-apply-preserves-consumer-capacity
                                   (event (fn-cpe-operation event))
                                   (caller (fn-cp-nth 2 (fn-cpe-operation event)))
                                   (consumer (fn-cp-nth 1 (fn-cpe-operation event)))
                                   (query (fn-cp-nth 3 (fn-cpe-operation event)))
                                   (qver (fn-cp-nth 4 (fn-cpe-operation event)))
                                   (view (fn-cp-nth 5 (fn-cpe-operation event)))
                                   (groups nil) (account nil)))
                  :in-theory (e/d (fn-cpe-projection-step)
                                  (fn-cp-apply fn-cp-register-within fn-cp-register
                                   fn-cp-remote-register fn-cpe-projection-decision
                                   fn-cpe-projection-advance fn-cp-initial
                                   fn-cp-state-carry fn-cpe-eventp fn-store-event-p
                                   fn-cpe-operation)))))

(local (defthm fn-crb-replay-keeps-the-bound
  (implies (and (<= (len (fn-cp-nth 5 s)) (nfix max))
                (fn-crb-registers-within s records expected max))
           (<= (len (fn-cp-nth 5 (fn-cp-nth 1 (fn-cpe-projection-replay s records
                                                                       expected))))
               (nfix max)))
  :hints (("Goal" :induct (fn-cpe-projection-replay s records expected)
                  :in-theory (e/d (fn-cpe-projection-replay)
                                  (fn-cpe-projection-step fn-crb-step-admittedp
                                   fn-crb-projection-step-keeps-the-bound)))
          ("Subgoal *1/4" :use ((:instance fn-crb-projection-step-keeps-the-bound
                                           (event (car records)))))
          ("Subgoal *1/3" :use ((:instance fn-crb-projection-step-keeps-the-bound
                                           (event (car records))))))))

; KEYSTONE (PKT-370).
(defthm fn-crb-replay-keeps-the-consumer-bound
  (implies (fn-crb-registers-within nil records 0 (fn-bs-profile-max-consumers values))
           (<= (len (fn-cp-nth 5 (fn-cp-nth 1 (fn-cpe-projection-replay nil records 0))))
               (nfix (fn-bs-profile-max-consumers values))))
  :hints (("Goal" :use ((:instance fn-crb-replay-keeps-the-bound
                                   (s nil) (expected 0)
                                   (max (fn-bs-profile-max-consumers values))))
                  :in-theory (e/d ((:e fn-cp-nth))
                                  (fn-crb-replay-keeps-the-bound fn-crb-registers-within
                                   fn-cpe-projection-replay
                                   fn-bs-profile-max-consumers)))))
