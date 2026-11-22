(in-package "ACL2")
(include-book "assurance-proof-support-unit")

; Run this in a fresh world including the certified book, not after its source
; admission.  Missing proof support MUST NOT become a known-empty closure.
(make-event
 (let* ((node (fn2-proof-support-node
               'fn2-proof-support-real-consumer '(fn2-a-native-span) (w state)))
        (report (fn2-proof-support-report
                 '(fn2-proof-support-real-consumer) '(fn2-a-native-span) 32
                 (w state))))
   (value
    (list 'assert-event
          (and (getpropc 'fn2-proof-support-real-consumer 'theorem nil (w state))
               (eq (cadr (assoc-keyword :support-state node))
                   :absent-or-empty-unknown)
               (not (cadr (assoc-keyword :complete report))))))))
