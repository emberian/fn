(in-package "ACL2")
(include-book "../../books/decoded-window-descriptor")

; Reachable decoded coordinates: requested offset exceeds stored C but is
; within decoded N. A raw descriptor cannot represent this request.
(defconst *pwzt-d* '(7 100 320 120 40 200 99 250 0))
(defconst *pwzt-token* (cons :decoded-window (cons 17 *pwzt-d*)))
(assert-event
 (and (fn-pwz-descriptorp *pwzt-d*) (fn-pwz-tokenp *pwzt-token*)
      (equal (len *pwzt-token*) 11) (equal (fn-pwz-dictionary *pwzt-token*) nil)
      (< (nth 4 *pwzt-d*) (nth 5 *pwzt-d*))))

; Unknown preset, invalid physical span, decoded offset and bomb admission
; are separately refused by the actual descriptor decision.
(assert-event (not (fn-pwz-descriptorp '(7 100 320 120 40 200 99 250 123))))
(assert-event (not (fn-pwz-descriptorp '(7 100 320 90 40 200 99 250 0))))
(assert-event (not (fn-pwz-descriptorp '(7 100 320 120 400 200 99 250 0))))
(assert-event (not (fn-pwz-descriptorp '(7 100 320 120 40 251 99 250 0))))
(assert-event (not (fn-pwz-descriptorp '(7 100 320 120 40 0 99 100000 0))))
(assert-event (not (fn-pwz-tokenp '(:window 17 7 100 320 120 40 200 99 250 0))))
(assert-event (not (fn-pwz-tokenp '(:decoded-window 17 7 100 320 120 40 200 99 250))))
(assert-event (not (fn-pwz-tokenp '(:decoded-window 17 7 100 320 120 40 200 99 250 0 1))))
(assert-event
 (equal (fn-pwz-cold-descriptor 7 100 320 120 40 99 250 nil 200)
        '(7 100 320 120 40 200 99 250 0)))
(assert-event
 (equal (fn-pwz-cold-descriptor 7 100 320 120 40 99 250 '(1) 200)
        '(7 100 320 120 40 200 99 250 :unknown-dictionary)))
