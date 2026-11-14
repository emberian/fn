(in-package "ACL2")
(include-book "../books/owed-reclamation")

; Exercise the actual live registry guard. An absent served statement is a
; requirement, not a proved theorem or a passed checker. These controls do
; not claim to exercise a storage release path: no such path is bound yet.
(make-event
 (let* ((id 'fn2-persistent-reclamation-lifetime)
        (row (fn2-decl-row (list :square id) (w state))))
  (if (and row
           (fn2-square-rowp id row (w state))
           (equal (fn2-decl-get :proof row) '(:owed))
           (not (fn2-decl-get :statement row))
           (not (fn2-decl-get :checks row))
           (not (fn2-square-rowp id
                  (fn2-decl-set :proof '(:proved fn2-allocator-only-proof) row)
                  (w state)))
           (not (fn2-square-rowp id
                  (fn2-decl-set :checks
                    '((:contract :allocator-only :revision :fixture
                       :profile :tiny :domain :reclaim :horizon 1
                       :unit :events :reached 1 :exercised 1
                       :verdict :pass :location "allocator-only-fixture")) row)
                  (w state))))
      (value '(value-triple :reclamation-requirement-remains-unbound))
    (er soft 'owed-reclamation-unit
        "Missing reclamation requirement or unbound row accepted evidence."))))
