(in-package "ACL2")
(include-book "../../books/snapshot-job-capture")
; Complete positive witness for the cheap cleanup fence. Not a proof of
; native join, file cleanup, resource adequacy or the whole snapshot job.
(assert-event
 (and (equal (car (fn-osj-cleanup-word :returned :none)) :release)
      (equal (fn-osj-cleanup-word :returned :none)
             '(:release :source :payload-view :capture :maintenance))))
(assert-event
 (and (equal (fn-osj-cleanup-word :running :none)
             '(:refused :action-not-joined))
      (equal (fn-osj-cleanup-word :returned :private)
             '(:uncertain :stage-not-settled))
      (equal (fn-osj-cleanup-word :returned :uncertain)
             '(:uncertain :stage-not-settled))))
(assert-event
 (and (equal (fn-osj-stage-observation :private :ambiguous) :uncertain)
      (equal (fn-osj-stage-observation :uncertain :deleted) :deleted)
      (equal (car (fn-osj-cleanup-word :returned :deleted)) :release)
      (equal (fn-osj-stage-observation :uncertain :published) :uncertain)))
