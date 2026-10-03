(in-package "ACL2")
(include-book "../../books/bp-session-received-source")
(defconst *bpsrx-row* (fn-bpsg-row 2 17 :incoming))
(defconst *bpsrx-plan* (fn-bpsrx-start *bpsrx-row* 7 4 1000 '((67 68) (65 66))))
(assert-event
 (and (equal (car *bpsrx-plan*) :source-operation)
      (equal (cadr *bpsrx-plan*) '(:bp-private-received 2 17 7 4))
      (equal (caddr *bpsrx-plan*) 4)
      (equal (fn-tsc-at 8 (cadddr *bpsrx-plan*)) '((67 68) (65 66)))))
(assert-event
 (let ((r (fn-bpsrx-turn (cadr *bpsrx-plan*) *bpsrx-row* (cadddr *bpsrx-plan*))))
  (and (eq (car r) :source-complete) (equal (caddr r) '(65 66 67 68))
       (<= (cadddr r) 64)
       (equal (fn-tsc-at 8 (cadr r)) '((67 68) (65 66))))))
; Discrimination: stale, outgoing, terminal logical or affirmative physical
; observations cannot resume the old operation or publish its source.
(assert-event
 (and (equal (car (fn-bpsrx-turn (cadr *bpsrx-plan*) (fn-bpsg-row 2 18 :incoming)
                                  (cadddr *bpsrx-plan*))) :uncertain)
      (equal (car (fn-bpsrx-start (fn-bpsg-row 2 17 :outgoing) 7 4 1000 nil)) :uncertain)
      (not (fn-bpsrx-authorizedp (cadr *bpsrx-plan*) '(:bp-session-grant 2 17 :incoming t nil)
                                 (cadddr *bpsrx-plan*)))
      (not (fn-bpsrx-authorizedp (cadr *bpsrx-plan*) '(:bp-session-grant 2 17 :incoming nil t)
                                 (cadddr *bpsrx-plan*)))
      (equal (fn-bpsrx-start *bpsrx-row* 7 1001 1000 nil) '(:refused :private-source-count))))
