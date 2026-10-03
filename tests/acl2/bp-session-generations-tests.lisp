(in-package "ACL2")
(include-book "../../books/bp-session-scheduler")
(defconst *bpsched-first-key* '(:bp-session 2 3 :incoming))
(defconst *bpsched-second-key* '(:bp-session 3 1 :incoming))
(defconst *bpsched-first*
 (fn-bpsched-listener-step
  (fn-bplc-make :stable 9 '(4101) 9 '(4101) nil nil nil 1 1 t nil)
  (list :retained-accepted *bpsched-first-key* '(:accept 9 4101))))
(defconst *bpsched-installed*
 (fn-bplc-make :stable 10 '(4102) 10 '(4102) nil nil nil 1 2 t
               (fn-bplc-session *bpsched-first*)))
(defconst *bpsched-second*
 (fn-bpsched-listener-step *bpsched-installed*
  (list :retained-accepted *bpsched-second-key* '(:accept 10 4102))))
(assert-event
 (equal (fn-bplc-runtime-line *bpsched-first*)
        "BP NODE GENERATION 9 LISTENER-FDS 1 PEAK 1 SESSION 9"))
(assert-event
 (equal (fn-bplc-runtime-line *bpsched-second*)
        "BP NODE GENERATION 10 LISTENER-FDS 1 PEAK 2 SESSION 9"))
(assert-event
 (let ((s (fn-bpsched-listener-step *bpsched-second*
           (list :retained-closed *bpsched-first-key*))))
  (and (equal (fn-bplc-runtime-line s)
              "BP NODE GENERATION 10 LISTENER-FDS 1 PEAK 2 SESSION 10")
       (equal (fn-bplc-session s)
              (fn-bplc-session (fn-bpsched-listener-step s '(:retained-closed unknown))))
       (equal (fn-bplc-runtime-line
               (fn-bpsched-listener-step s (list :retained-closed *bpsched-second-key*)))
              "BP NODE GENERATION 10 LISTENER-FDS 1 PEAK 2 SESSION none"))))
