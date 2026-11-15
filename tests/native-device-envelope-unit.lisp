(in-package "ACL2")
(include-book "../sim/native-device-envelope")
(defconst *fn2-nde-write-take*
 (list :take 4 7 *fn2-action-write* 0 0 2 3 0 3 100 0 0 0 0 0 0))
(defconst *fn2-nde-write-post*
 (list :post 0 4 7 *fn2-event-write-result* *fn2-outcome-failed* *fn2-reason-uncertain*
       2 0 0 0 '(0 0 0 0 0) nil))
(defconst *fn2-nde-write-physical*
 '((:submit 1 (17 4 7 :write 100 3 (8 9 10))) (:begin 1) (:return 1 2 0 nil)))
(assert-event
 (and (fn2-nde-take-descriptor-p *fn2-nde-write-take* '(17 4 7 :write 100 3 (8 9 10)))
      (not (fn2-nde-take-descriptor-p *fn2-nde-write-take* '(17 4 8 :write 100 3 (8 9 10))))
      (not (fn2-nde-take-descriptor-p *fn2-nde-write-take* '(17 4 7 :write 101 3 (8 9 10))))
      (not (fn2-nde-take-descriptor-p *fn2-nde-write-take* '(17 4 7 :write 100 2 (8 9))))))
(assert-event
 (and (fn2-nde-post-p *fn2-nde-write-post* (list *fn2-nde-write-take*) *fn2-nde-write-physical*)
      (not (fn2-nde-post-p (update-nth 7 3 *fn2-nde-write-post*) (list *fn2-nde-write-take*) *fn2-nde-write-physical*))
      (not (fn2-nde-post-p *fn2-nde-write-post* (list *fn2-nde-write-take*) nil))
      (not (fn2-nde-post-p *fn2-nde-write-post* (list *fn2-nde-write-take*) (take 2 *fn2-nde-write-physical*)))))
