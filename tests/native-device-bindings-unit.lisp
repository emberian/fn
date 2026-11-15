(in-package "ACL2")
(include-book "../sim/native-device-bindings")
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
(defconst *fn2-nde-read-take*
 (list :take 5 7 *fn2-action-read* 0 0 2 3 0 3 100 0 0 0 0 0 0))
(defconst *fn2-nde-read-post*
 (list :post 0 5 7 *fn2-event-read-result* *fn2-outcome-short* *fn2-reason-none*
       2 0 0 0 '(0 0 0 0 0) '(8 9)))
(assert-event
 (let ((records '((:submit 2 (17 5 7 :read 100 3 nil)) (:begin 2) (:return 2 2 0 (8 9)))))
  (and (fn2-nde-post-p *fn2-nde-read-post* (list *fn2-nde-read-take*) records)
       (not (fn2-nde-post-p (update-nth 12 '(8 10) *fn2-nde-read-post*) (list *fn2-nde-read-take*) records)))))
; Only an explicit unsupported FUA request explains a device Post without a
; physical job. An ordinary failed Write still requires its physical evidence.
(assert-event
 (let* ((fua (update-nth 11 1 *fn2-nde-write-take*))
        (failed (update-nth 7 0 (update-nth 6 *fn2-reason-io* *fn2-nde-write-post*))))
  (and (fn2-nde-post-p failed (list fua) nil)
       (not (fn2-nde-post-p failed (list *fn2-nde-write-take*) nil)))))
