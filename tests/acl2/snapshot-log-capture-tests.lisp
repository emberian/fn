(in-package "ACL2")
(include-book "../../books/snapshot-job-capture")
(include-book "../../books/owner-maintenance-admission")
(assert-event
 (and (equal (fn-osj-log-observation :rotation-returned) :frozen)
      (equal (fn-osj-log-observation :rotation-threw) :uncertain)
      (equal (fn-osj-cleanup-log-word :returned :none
                                     (fn-osj-log-observation :rotation-threw))
             '(:uncertain :log-not-settled))
      (not (equal (car (fn-osj-cleanup-log-word :returned :none
                                               (fn-osj-log-observation :rotation-threw)))
                  :release))))
(assert-event
 (and (equal (fn-osj-cleanup-log-word :returned :none :frozen)
             '(:release :source :payload-view :capture :maintenance))
      (equal (fn-osj-cleanup-log-word :returned :private :frozen)
             '(:uncertain :stage-not-settled))
      (equal (fn-ort-maintenance-action nil) :admit)
      (equal (fn-ort-maintenance-action '(:retire 17)) :skip)))
(assert-event
 (and (equal (fn-osj-log-fence-word :frozen) :fence)
      (equal (fn-osj-log-fence-word :durable) :durable)
      (equal (fn-osj-log-fence-word :uncertain) :uncertain)
      (equal (fn-osj-cleanup-log-word :returned :none :garbage)
             '(:refused :log-phase))))
