(in-package "ACL2")
(include-book "../books/assurance-proof-support")
(include-book "../books/assumptions-native-span")

; Actual project assumption, actual admitted :USE proof, no authored dependency.
(defthm fn2-proof-support-real-consumer
  (implies (fn2-a-native-span reference native)
           (equal native reference))
  :hints (("Goal" :use fn2-a-native-span-correspondence))
  :rule-classes nil)

; Merely mentioning the same constrained function is NOT a proof-support edge.
(defthm fn2-proof-support-formula-only
  (implies (fn2-a-native-span reference native)
           (equal reference reference))
  :rule-classes nil)

(make-event
 (let* ((world (w state))
        (entries (fn2-proof-support-entries
                  'fn2-proof-support-real-consumer
                  (global-val 'proof-supporters-alist world)))
        (names (fn2-proof-support-names entries))
        (mention (fn2-proof-support-entries
                  'fn2-proof-support-formula-only
                  (global-val 'proof-supporters-alist world)))
        (contexts (fn2-proof-assumption-contexts
                   'fn2-a-native-span-correspondence
                   (getpropc 'fn2-a-native-span-correspondence 'theorem nil world)
                   '(fn2-a-native-span) world)))
   (value
    (list 'assert-event
          (and (member-eq 'fn2-a-native-span-correspondence names)
               (not (member-eq 'fn2-a-native-span-correspondence
                               (fn2-proof-support-names mention)))
               (eq (cadr (assoc-keyword :status (car contexts)))
                   :exact-live-constraint-theorem)
               (not (fn2-proof-constraint-match
                     'unrelated '(quote t)
                     '((quote t))
                     '((theorem fn2-a-native-span-correspondence)))))))))
