; Literal actual issuance/read/cancellation/reset/once-only return.
; Source metadata is INTERNAL fixture input, not an installed-native witness.
(in-package "ACL2")
(include-book "../../books/history-capture-custody")
(defconst *hhct-ledger* (fn-prl-make '(10000 10000 10 10 100)))
(defconst *hhct-source* '(:history-source 41 42 43 (:root :borrowed) 0 1 3 44))
(defconst *hhct-admission* (mv-list 4 (fn-hhc-admit *hhct-ledger* nil 7 *hhct-source* '(128 0 0 0 1))))
(defconst *hhct-slot* (nth 3 *hhct-admission*))
(defconst *hhct-token* (nth 1 (nth 1 *hhct-admission*)))
(assert-event
 (and (eq (nth 0 *hhct-admission*) :captured)
      (equal (nth 1 *hhct-admission*) '(:history-prefix (:history-capture 0) 7 3 41 43))
      (equal (fn-hhc-at 3 *hhct-slot*) *hhct-source*)
      (equal (fn-prl-nth 2 (nth 2 *hhct-admission*)) 1)))
(assert-event
 (and (equal (fn-hhc-read-plan *hhct-slot* *hhct-token* 7 2)
              (list :read *hhct-source* 2))
      (fn-hhc-matches *hhct-slot* *hhct-token*)
      (natp 2) (< 2 (fn-hhc-at 7 *hhct-source*))
      (equal 7 (fn-hhc-at 2 *hhct-slot*))
      (eq (fn-hhc-at 5 *hhct-slot*) :retained)))
(assert-event
 (and (equal (fn-hhc-read-plan *hhct-slot* *hhct-token* 7 3)
              '(:refused :history-ordinal))
      (equal (fn-hhc-read-plan *hhct-slot* '(:history-capture 1) 7 0)
              '(:refused :history-source-stale))
      (equal (fn-hhc-read-plan *hhct-slot* *hhct-token* 8 0)
              '(:refused :history-source-stale))))
(assert-event
 (let ((cancelled (fn-hhc-cancel *hhct-slot* *hhct-token*)))
  (and (eq (fn-hhc-reset-status *hhct-slot*) :history-source-held)
       (eq (fn-hhc-reset-status cancelled) :history-source-held)
       (eq (fn-hhc-at 5 cancelled) :cancelled)
       (equal (fn-hhc-at 3 cancelled) *hhct-source*)
       (let ((refused (mv-list 3 (fn-hhc-release (nth 2 *hhct-admission*) cancelled *hhct-token*))))
        (and (eq (nth 0 refused) :history-source-held)
             (equal (nth 1 refused) (nth 2 *hhct-admission*))
             (equal (nth 2 refused) cancelled))))))
(assert-event
 (let* ((released (mv-list 3 (fn-hhc-release (nth 2 *hhct-admission*)
                         (fn-hhc-quiesce *hhct-slot* *hhct-token*) *hhct-token*)))
        (duplicate (mv-list 3 (fn-hhc-release (nth 1 released) (nth 2 released) *hhct-token*))))
  (and (eq (nth 0 released) :released) (null (nth 2 released))
       (equal (fn-prl-nth 2 (nth 1 released)) 1)
       (equal (fn-prl-nth 4 (fn-prl-nth 1 (nth 1 released))) 1)
       (eq (fn-hhc-reset-status (nth 2 released)) :history-reset-clear)
       (eq (nth 0 duplicate) :history-source-held)
       (equal (nth 1 duplicate) (nth 1 released)) (null (nth 2 duplicate)))))
; Mutation witness: dropping the actual slot falsely permits destructive reset.
(assert-event
 (and (fn-hhc-matches *hhct-slot* *hhct-token*)
      (eq (fn-hhc-reset-status *hhct-slot*) :history-source-held)
      (not (eq (fn-hhc-reset-status nil) :history-source-held))))
; Hypothesis removal: :captured is essential. Busy admission retains the
; previous owner and cannot satisfy the new descriptor/next identity law.
(assert-event
 (let ((r (mv-list 4 (fn-hhc-admit (nth 2 *hhct-admission*) *hhct-slot*
                          7 *hhct-source* '(128 0 0 0 1)))))
  (and (not (eq (nth 0 r) :captured))
       (not (and
        (equal (nth 1 r) (list :history-prefix
                           (list :history-capture (fn-prl-nth 2 (nth 2 *hhct-admission*)))
                           7 (fn-hhc-at 7 *hhct-source*)
                           (fn-hhc-at 1 *hhct-source*) (fn-hhc-at 3 *hhct-source*)))
        (equal (fn-hhc-at 3 (nth 3 r)) *hhct-source*)
        (equal (fn-prl-nth 2 (nth 2 r))
               (+ 1 (fn-prl-nth 2 (nth 2 *hhct-admission*)))))))))
; Hypothesis removal: successful :read is essential at the exact frontier.
(assert-event
 (let ((r (fn-hhc-read-plan *hhct-slot* *hhct-token* 7 3)))
  (and (not (eq (car r) :read))
       (not (and (equal r (list :read *hhct-source* 3))
                 (fn-hhc-matches *hhct-slot* *hhct-token*) (natp 3)
                 (< 3 (fn-hhc-at 7 *hhct-source*))
                 (equal 7 (fn-hhc-at 2 *hhct-slot*))
                 (eq (fn-hhc-at 5 *hhct-slot*) :retained))))))
; Hypothesis removal: an absent owner does not match and permits reset.
(assert-event
 (and (not (fn-hhc-matches nil *hhct-token*))
      (not (and (eq (fn-hhc-reset-status nil) :history-source-held)
                (eq (fn-hhc-reset-status (fn-hhc-cancel nil *hhct-token*))
                    :history-source-held)))))
; Hypothesis removal: a cancelled owner has not terminal-returned.
(assert-event
 (let* ((cancelled (fn-hhc-cancel *hhct-slot* *hhct-token*))
        (old (nth 2 *hhct-admission*))
        (r (mv-list 3 (fn-hhc-release old cancelled *hhct-token*))))
  (and (not (eq (nth 0 r) :released))
       (not (and (equal (nth 2 r) nil)
                 (equal (fn-prl-nth 2 (nth 1 r)) (fn-prl-nth 2 old))
                 (equal (fn-prl-nth 4 (fn-prl-nth 1 (nth 1 r)))
                        (fn-prl-nth 4 (fn-prl-nth 1 old))))))))
; Hypothesis removal: successful release changes custody and reusable charge.
(assert-event
 (let* ((old (nth 2 *hhct-admission*))
        (slot (fn-hhc-quiesce *hhct-slot* *hhct-token*))
        (r (mv-list 3 (fn-hhc-release old slot *hhct-token*))))
  (and (eq (nth 0 r) :released)
       (not (and (equal (nth 1 r) old) (equal (nth 2 r) slot))))))
