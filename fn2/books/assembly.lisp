; The sole served core instance, in generated-section include order.
(in-package "ACL2")
(include-book "assembly-reference")

(assert-event
 (and (fn2-core-profilep *fn2-profile-concrete*)
      (fn2-core-profilep *fn2-profile-tiny*)
      (fn2-core-profilep *fn2-profile-tiny-near-limit*)))
