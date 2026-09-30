(in-package "ACL2")
(include-book "../../books/incoming-setup-ranges")
(defun isrt-begin (token total capacity limits)
  (mv-let (word plan) (fn-isr-begin token total capacity limits) (list word plan)))
(defun isrt-next (plan)
  (mv-let (word grant next-plan) (fn-isr-next plan) (list word grant next-plan)))
(defun isrt-ack (plan grant outcome)
  (mv-let (word next-plan) (fn-isr-ack plan grant outcome) (list word next-plan)))
(defun isrt-plan ()
  (mv-nth 1 (isrt-begin '(:incoming 7) 5000 8192 nil)))
(defun isrt-issued () (mv-nth 2 (isrt-next (isrt-plan))))
(defun isrt-grant () (mv-nth 1 (isrt-next (isrt-plan))))
(defun isrt-after-first ()
  (mv-nth 1 (isrt-ack (isrt-issued) (isrt-grant) :copied)))
(assert-event
 (and (equal (mv-nth 0 (isrt-begin '(:incoming 7) 5000 8192 nil)) :setup-started)
      (fn-isr-planp (isrt-plan))
      (fn-isr-planp (isrt-issued))
      (equal (isrt-grant) '(:incoming-copy (:incoming 7) 0 4096))
      (equal (mv-nth 2 (isrt-next (isrt-issued))) (isrt-issued))
      (equal (mv-nth 1 (isrt-next (isrt-issued))) (isrt-grant))))
(assert-event
 (and (fn-isr-planp (isrt-after-first))
      (equal (mv-nth 1 (isrt-next (isrt-after-first)))
             '(:incoming-copy (:incoming 7) 4096 904))
      (equal (mv-nth 0 (isrt-ack (isrt-after-first) (isrt-grant) :copied)) :stale-copy)
      (equal (mv-nth 1 (isrt-ack (isrt-after-first) (isrt-grant) :copied))
             (isrt-after-first))))
(assert-event
 (let* ((pending (mv-nth 2 (isrt-next (isrt-after-first))))
        (grant (mv-nth 1 (isrt-next (isrt-after-first))))
        (complete (mv-nth 1 (isrt-ack pending grant :copied))))
   (and (fn-isr-planp complete) (fn-isr-sealablep complete)
        (equal (fn-prl-nth 4 complete) (fn-prl-nth 1 complete))
        (not (fn-prl-nth 5 complete))
        (equal (mv-nth 0 (isrt-next complete)) :complete))))
(assert-event
 (let ((cancelled (mv-nth 1 (isrt-ack (isrt-issued) (isrt-grant) :uncertain))))
   (and (fn-isr-planp cancelled) (not (fn-isr-sealablep cancelled))
        (equal (fn-prl-nth 5 cancelled) (isrt-grant))
        (equal (mv-nth 0 (isrt-next cancelled)) :setup-unavailable))))
; Corrupted source state is not a carried setup plan: sealable alone cannot
; establish complete copying. Omitted invariant false, retained sealable true,
; advertised complete-offset conclusion false.
(assert-event
 (let ((bad (fn-isr-plan '(:incoming 7) 5000 8192 4096 0 nil :complete)))
   (and (not (fn-isr-planp bad)) (fn-isr-sealablep bad)
        (not (equal (fn-prl-nth 4 bad) (fn-prl-nth 1 bad))))))
; Remove sealable: carried copying state has not yet reached its total.
(assert-event
 (and (fn-isr-planp (isrt-plan)) (not (fn-isr-sealablep (isrt-plan)))
      (not (equal (fn-prl-nth 4 (isrt-plan)) (fn-prl-nth 1 (isrt-plan))))))
; Reachable empty setup anchors sealable TRUE with the full carried invariant.
(assert-event
 (and (equal (mv-nth 0 (isrt-begin '(:incoming 7) 0 64 nil)) :setup-started)
      (fn-isr-planp (mv-nth 1 (isrt-begin '(:incoming 7) 0 64 nil)))
      (fn-isr-sealablep (mv-nth 1 (isrt-begin '(:incoming 7) 0 64 nil)))
      (equal (fn-prl-nth 4 (mv-nth 1 (isrt-begin '(:incoming 7) 0 64 nil)))
             (fn-prl-nth 1 (mv-nth 1 (isrt-begin '(:incoming 7) 0 64 nil))))
      (not (fn-prl-nth 5 (mv-nth 1 (isrt-begin '(:incoming 7) 0 64 nil))))))
