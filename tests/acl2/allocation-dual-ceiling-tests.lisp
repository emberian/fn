(in-package "ACL2")
(include-book "../../books/allocation-epoch")
; Synthetic arithmetic tuples, not genuine installed runtime authority.
(defconst *fn-aec-test-dynamic13*
  '(:allocation-epoch-installation
    (:allocation-epoch-association :runtime :image :profile 4096 100)
    10000 1000 1 0 0 0 0 0 0 0 20))
(defconst *fn-aec-test-physical13*
  '(:allocation-epoch-installation
    (:allocation-epoch-association :runtime :image :profile 4096 1000)
    10000 70 1 0 0 0 0 0 0 0 0))
(assert-event
 (mv-let (word mode allocated)
   (fn-aec-body *fn-aec-test-dynamic13* :active 0 40 39 1 nil 2 nil)
   (and (fn-aec-installationp *fn-aec-test-dynamic13*)
        (equal (fn-aec-physical-ceiling *fn-aec-test-dynamic13*) 1000)
        (equal (fn-aec-ceiling *fn-aec-test-dynamic13*) 80)
        (fn-aec-statep *fn-aec-test-dynamic13* :active 0 40 39 1 nil)
        (natp 2) (booleanp nil)
        (equal word :yield) (equal mode :draining) (equal allocated 39))))
(assert-event
 (mv-let (word mode allocated)
   (fn-aec-body *fn-aec-test-physical13* :active 0 40 29 1 nil 2 nil)
   (and (fn-aec-installationp *fn-aec-test-physical13*)
        (equal (fn-aec-ceiling *fn-aec-test-physical13*) 70)
        (fn-aec-statep *fn-aec-test-physical13* :active 0 40 29 1 nil)
        (natp 2) (booleanp nil)
        (equal word :yield) (equal mode :draining) (equal allocated 29))))
; Mutation tooth: restoring the physical-only room check accepts the body
; whose actual independent dynamic ceiling above refuses.
(assert-event
 (and (fn-aec-statep *fn-aec-test-dynamic13* :active 0 40 39 1 nil)
      (fn-aed-ordinary-roomp 40 41 0
                            (fn-aec-physical-ceiling *fn-aec-test-dynamic13*) 10000)
      (not (fn-aed-ordinary-roomp 40 41 0
                                 (fn-aec-ceiling *fn-aec-test-dynamic13*) 10000))))
(assert-event
 (not (fn-aec-installationp
       '(:allocation-epoch-installation
         (:allocation-epoch-association :runtime :image :profile 4096 100)
         10000 1000 1 0 0 0 0 0 0 0 101))))
