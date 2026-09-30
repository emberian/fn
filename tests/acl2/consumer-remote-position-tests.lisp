; Remote metadata kernel: not yet a served remote endpoint or durable codec.
(in-package "ACL2")
(include-book "../../books/consumer-remote-position")
(defconst *crp-groups* '((102 110 46 97) (102 110 46 98)))
(defconst *crp-more* '((102 110 46 97) (102 110 46 99)))
(defconst *crp-initial* (fn-cp-initial '(104) '(105) 20))
(defconst *crp-register*
  (fn-cp-remote-register *crp-initial* 1 '(112) '(99) '(113) 1 2
                         *crp-groups* '(97)))
(defconst *crp-state* (fn-cp-apply *crp-initial* (cadr *crp-register*)))
(defconst *crp-entry* (fn-cp-find '(99) (fn-cp-nth 5 *crp-state*)))
(defconst *crp-cursor* (update-nth 9 7 (fn-cp-scope-cursor *crp-state* *crp-entry*)))
(defconst *crp-ack* (fn-cp-ack *crp-state* '(112) 1 2 *crp-cursor*))
(defconst *crp-after-ack* (fn-cp-apply *crp-state* (cadr *crp-ack*)))

; Complete antecedent and conclusion of the state invariant, with a remote
; entry rather than an empty state. The proposal keeps all metadata atomic.
(assert-event
 (and (fn-cp-statep *crp-initial*) (equal (car *crp-register*) :write)
      (fn-cp-statep *crp-state*)
      (equal *crp-entry*
             (append (fn-cp-entry '(99) '(112) '(113) 1 2 1 0)
                     (list *crp-groups* '(97))))))
(assert-event
 (and (fn-cp-statep *crp-state*) (equal (len *crp-entry*) 10)
      (equal (car *crp-ack*) :write)
      (fn-cp-statep *crp-after-ack*)
      (equal (fn-cp-find '(99) (fn-cp-nth 5 *crp-after-ack*))
             (update-nth 7 7 *crp-entry*))))

; At capacity, the identical retry is a no-op; a new registration refuses.
(assert-event
 (equal (fn-cp-remote-register *crp-after-ack* 1 '(112) '(99) '(113) 1 2
                               *crp-groups* '(97))
        (list :no-op *crp-cursor*)))
(assert-event
 (equal (fn-cp-remote-register *crp-after-ack* 1 '(112) '(100) '(113) 1 2
                               *crp-groups* '(97))
        '(:refused :max-consumers)))
; Query-ID equality cannot erase an exact definition or incarnation change.
(assert-event
 (equal (fn-cp-remote-register *crp-after-ack* 1 '(112) '(99) '(113) 1 2
                               *crp-more* '(97))
        '(:refused :rebase-required)))
(assert-event
 (equal (fn-cp-remote-register *crp-after-ack* 1 '(112) '(99) '(113) 1 2
                               *crp-groups* '(98))
        '(:refused :rebase-required)))
(defconst *crp-rebase*
  (fn-cp-remote-rebase *crp-after-ack* '(112) '(99) '(113) 1 2
                       *crp-more* '(98)))
(defconst *crp-rebased* (fn-cp-apply *crp-after-ack* (cadr *crp-rebase*)))
(assert-event
 (and (fn-cp-statep *crp-after-ack*) (equal (car *crp-rebase*) :write)
      (fn-cp-statep *crp-rebased*)
      (equal (fn-cp-find '(99) (fn-cp-nth 5 *crp-rebased*))
             (append (fn-cp-entry '(99) '(112) '(113) 1 2 2 0)
                     (list *crp-more* '(98))))))
(assert-event (equal (fn-cp-ack *crp-rebased* '(112) 1 2 *crp-cursor*)
                     '(:refused :scope)))
(assert-event
 (equal (fn-cp-remote-rebase *crp-after-ack* '(111) '(99) '(113) 1 2
                             *crp-more* '(98))
        '(:refused :scope)))
(assert-event
 (equal (fn-cp-remote-rebase *crp-after-ack* '(112) '(99) '(113) 1 2
                             *crp-groups* '(97))
        (list :no-op *crp-cursor*)))

; Complete capacity theorem hypotheses for the remote registration arm.
(assert-event
 (let ((event (cadr *crp-register*)))
   (and (<= (len (fn-cp-nth 5 *crp-initial*)) 1)
        (equal (fn-cp-remote-register *crp-initial* 1 '(112) '(99) '(113) 1 2
                                      *crp-groups* '(97))
               (list :write event))
        (<= (len (fn-cp-nth 5 (fn-cp-apply *crp-initial* event))) 1))))
; Drop admission: retained initial-capacity hypothesis true, but a kernel
; event not admitted at zero slots grows the table past the budget.
(assert-event
 (let ((event (cadr *crp-register*)))
   (and (<= (len (fn-cp-nth 5 *crp-initial*)) 0)
        (member-eq (fn-cp-nth 0 event) '(:register :remote-register))
        (not (equal (fn-cp-register-within *crp-initial* 0 '(112) '(99) '(113) 1 2)
                    (list :write event)))
        (not (equal (fn-cp-remote-register *crp-initial* 0 '(112) '(99) '(113) 1 2
                                           *crp-groups* '(97))
                    (list :write event)))
        (not (<= (len (fn-cp-nth 5 (fn-cp-apply *crp-initial* event))) 0)))))
; Canonical set order and a nonempty account incarnation are required.
(assert-event
 (equal (fn-cp-remote-register *crp-initial* 1 '(112) '(99) '(113) 1 2
                               (reverse *crp-groups*) '(97))
        '(:refused :query)))
(assert-event
 (equal (fn-cp-remote-register *crp-initial* 1 '(112) '(99) '(113) 1 2
                               *crp-groups* nil)
        '(:refused :query)))
; A corrupt initial history ID falsifies the invariant; an unrelated event
; does not repair it. This is an invariant-removal, not a reachable state.
(assert-event
 (let ((bad (update-nth 1 nil *crp-state*)))
   (and (not (fn-cp-statep bad))
        (not (fn-cp-statep (fn-cp-apply bad '(:not-an-operation)))))))

; Literal hypothesis removals for the exact-definition theorems.
(assert-event
 (let ((d (fn-cp-remote-register *crp-initial* 0 '(112) '(99) '(113) 1 2
                                 *crp-groups* '(97))))
   (and (not (equal (car d) :write))
        (not (equal (fn-cp-find '(99) (fn-cp-nth 5 (fn-cp-apply *crp-initial* (cadr d))))
                    (append (fn-cp-entry '(99) '(112) '(113) 1 2 1 0)
                            (list *crp-groups* '(97))))))))
(assert-event
 (let ((d (fn-cp-remote-rebase *crp-after-ack* '(112) '(99) '(113) 1 2 nil '(98))))
   (and (not (equal (car d) :write))
        (not (equal (fn-cp-find '(99) (fn-cp-nth 5 (fn-cp-apply *crp-after-ack* (cadr d))))
                    (append (fn-cp-entry '(99) '(112) '(113) 1 2 2 0)
                            (list nil '(98))))))))
; Corrupted-state witness for removing the remote10 entry shape. The write
; hypothesis is affirmatively true; the exact-definition conclusion fails.
(assert-event
 (let* ((entry (append *crp-entry* '(extra)))
        (s (update-nth 5 (list entry) *crp-state*))
        (d (fn-cp-ack s '(112) 1 2 *crp-cursor*))
        (after (fn-cp-find '(99) (fn-cp-nth 5 (fn-cp-apply s (cadr d))))))
   (and (not (equal (len entry) 10)) (equal (car d) :write)
        (not (and (equal (fn-cp-nth 7 after) (fn-cp-nth 9 *crp-cursor*))
                  (equal (fn-cp-nth 8 after) (fn-cp-nth 8 entry))
                  (equal (fn-cp-nth 9 after) (fn-cp-nth 9 entry)))))))
(assert-event
 (let* ((cursor (update-nth 8 99 *crp-cursor*))
        (d (fn-cp-ack *crp-state* '(112) 1 2 cursor))
        (after (fn-cp-find '(99) (fn-cp-nth 5 (fn-cp-apply *crp-state* (cadr d))))))
   (and (equal (len *crp-entry*) 10) (not (equal (car d) :write))
        (not (and (equal (fn-cp-nth 7 after) (fn-cp-nth 9 cursor))
                  (equal (fn-cp-nth 8 after) (fn-cp-nth 8 *crp-entry*))
                  (equal (fn-cp-nth 9 after) (fn-cp-nth 9 *crp-entry*)))))))
; Remove initial-capacity hypothesis while retaining the non-registration
; alternative in full: an unrelated event leaves one entry above zero slots.
(assert-event
 (let ((event '(:not-an-operation)))
   (and (not (<= (len (fn-cp-nth 5 *crp-state*)) 0))
        (not (member-eq (fn-cp-nth 0 event) '(:register :remote-register)))
        (not (<= (len (fn-cp-nth 5 (fn-cp-apply *crp-state* event))) 0)))))
