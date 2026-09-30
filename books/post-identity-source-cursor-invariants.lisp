; Carried fixed layout and immutable virtual-source configuration.
(in-package "ACL2")
(include-book "post-identity-source-cursor")
(defun fn-psc-configuration (c)
 (declare (xargs :guard (true-listp c)))
 (list (fn-psc-get mode c) (fn-psc-get n c)
       (fn-psc-get incoming-n c) (fn-psc-get msgid c)))
(local (defthm fn-psc-finish-preserves-layout
 (implies (equal (len c) 24) (equal (len (fn-psc-finish result c)) 24))
 :hints (("Goal" :in-theory (e/d (fn-psc-finish ) (nth update-nth nfix len))))))
(local (defthm fn-psc-finish-preserves-configuration
 (equal (fn-psc-configuration (fn-psc-finish result c)) (fn-psc-configuration c))
 :hints (("Goal" :in-theory (e/d (fn-psc-finish fn-psc-configuration) (nth update-nth nfix len))))))
(local (defthm fn-psc-compare-preserves-layout
 (implies (equal (len c) 24) (equal (len (fn-psc-compare pos ref start count resume c)) 24))
 :hints (("Goal" :in-theory (e/d (fn-psc-compare ) (nth update-nth nfix len))))))
(local (defthm fn-psc-compare-preserves-configuration
 (equal (fn-psc-configuration (fn-psc-compare pos ref start count resume c)) (fn-psc-configuration c))
 :hints (("Goal" :in-theory (e/d (fn-psc-compare fn-psc-configuration) (nth update-nth nfix len))))))
(local (defthm fn-psc-literal-preserves-layout
 (implies (equal (len c) 24) (equal (len (fn-psc-literal pos bytes resume c)) 24))
 :hints (("Goal" :in-theory (e/d (fn-psc-literal ) (nth update-nth nfix len))))))
(local (defthm fn-psc-literal-preserves-configuration
 (equal (fn-psc-configuration (fn-psc-literal pos bytes resume c)) (fn-psc-configuration c))
 :hints (("Goal" :in-theory (e/d (fn-psc-literal fn-psc-configuration) (nth update-nth nfix len))))))
(local (defthm fn-psc-return-preserves-layout
 (implies (equal (len c) 24) (equal (len (fn-psc-return ok c)) 24))
 :hints (("Goal" :in-theory (e/d (fn-psc-return ) (nth update-nth nfix len))))))
(local (defthm fn-psc-return-preserves-configuration
 (equal (fn-psc-configuration (fn-psc-return ok c)) (fn-psc-configuration c))
 :hints (("Goal" :in-theory (e/d (fn-psc-return fn-psc-configuration) (nth update-nth nfix len))))))
(local (defthm fn-psc-agent-compare-preserves-layout
 (implies (equal (len c) 24) (equal (len (fn-psc-agent-compare pos resume c)) 24))
 :hints (("Goal" :in-theory (e/d (fn-psc-agent-compare ) (nth update-nth nfix len))))))
(local (defthm fn-psc-agent-compare-preserves-configuration
 (equal (fn-psc-configuration (fn-psc-agent-compare pos resume c)) (fn-psc-configuration c))
 :hints (("Goal" :in-theory (e/d (fn-psc-agent-compare fn-psc-configuration) (nth update-nth nfix len))))))
(local (defthm fn-psc-msgid-compare-preserves-layout
 (implies (equal (len c) 24) (equal (len (fn-psc-msgid-compare pos resume c)) 24))
 :hints (("Goal" :in-theory (e/d (fn-psc-msgid-compare ) (nth update-nth nfix len))))))
(local (defthm fn-psc-msgid-compare-preserves-configuration
 (equal (fn-psc-configuration (fn-psc-msgid-compare pos resume c)) (fn-psc-configuration c))
 :hints (("Goal" :in-theory (e/d (fn-psc-msgid-compare fn-psc-configuration) (nth update-nth nfix len))))))
(local (defthm fn-psc-date-compare-preserves-layout
 (implies (equal (len c) 24) (equal (len (fn-psc-date-compare pos resume c)) 24))
 :hints (("Goal" :in-theory (e/d (fn-psc-date-compare ) (nth update-nth nfix len))))))
(local (defthm fn-psc-date-compare-preserves-configuration
 (equal (fn-psc-configuration (fn-psc-date-compare pos resume c)) (fn-psc-configuration c))
 :hints (("Goal" :in-theory (e/d (fn-psc-date-compare fn-psc-configuration) (nth update-nth nfix len))))))
(local (defthm fn-psc-info-compare-preserves-layout
 (implies (equal (len c) 24) (equal (len (fn-psc-info-compare pos resume c)) 24))
 :hints (("Goal" :in-theory (e/d (fn-psc-info-compare ) (nth update-nth nfix len))))))
(local (defthm fn-psc-info-compare-preserves-configuration
 (equal (fn-psc-configuration (fn-psc-info-compare pos resume c)) (fn-psc-configuration c))
 :hints (("Goal" :in-theory (e/d (fn-psc-info-compare fn-psc-configuration) (nth update-nth nfix len))))))
(local (defthm fn-psc-control-preserves-layout
 (implies (equal (len c) 24) (equal (len (fn-psc-control c)) 24))
 :hints (("Goal" :in-theory (e/d (fn-psc-control ) (nth update-nth nfix len))))))
(local (defthm fn-psc-control-preserves-configuration
 (equal (fn-psc-configuration (fn-psc-control c)) (fn-psc-configuration c))
 :hints (("Goal" :in-theory (e/d (fn-psc-control fn-psc-configuration) (nth update-nth nfix len))))))
(defthm fn-psc-begin-fixed-layout
 (equal (len (fn-psc-begin mode n msgid agent-span incoming-n)) 24)
 :hints (("Goal" :in-theory (e/d (fn-psc-begin) (nth nfix update-nth)))))
(defthm fn-psc-step-preserves-fixed-layout
 (implies (equal (len c) 24) (equal (len (fn-psc-step c byte)) 24))
 :hints (("Goal" :in-theory (e/d (fn-psc-step) (nth update-nth nfix len)))))
(defthm fn-psc-step-preserves-configuration
 (equal (fn-psc-configuration (fn-psc-step c byte))
        (fn-psc-configuration c))
 :hints (("Goal" :in-theory (e/d (fn-psc-step fn-psc-configuration)
                               (nth update-nth nfix len)))))
(in-theory (disable fn-psc-configuration))
(defun fn-psc-referencep (ref)
 (declare (xargs :guard t))
 (or (member-eq ref '(:incoming :self :msgid :path))
     (member-equal ref
      (list nil *fn-cll-lock-field* *fn-cll-key-field* *fn-inj-path-field*
            *fn-inj-injection-date-field* *fn-inj-injection-info-field*
            *fn-inj-message-id-field* *fn-inj-date-field* '(13 10) '(10) '(33)
            '(33 110 111 116 45 102 111 114 45 109 97 105 108 13 10)))))
(defthm fn-psc-reference-has-bounded-literal
 (implies (fn-psc-referencep ref) (<= (len ref) 16))
 :hints (("Goal" :in-theory (enable fn-psc-referencep))))
(local (defthm fn-psc-finish-reference-unfolds
 (equal (fn-psc-get ref (fn-psc-finish result c)) (fn-psc-get ref c))
 :hints (("Goal" :in-theory (e/d (fn-psc-finish) (nth update-nth nfix len))))))
(local (defthm fn-psc-return-reference-unfolds
 (equal (fn-psc-get ref (fn-psc-return ok c)) (fn-psc-get ref c))
 :hints (("Goal" :in-theory (e/d (fn-psc-return) (nth update-nth nfix len))))))
(local (defthm fn-psc-compare-reference-unfolds
 (equal (fn-psc-get ref (fn-psc-compare pos ref start count resume c)) ref)
 :hints (("Goal" :in-theory (e/d (fn-psc-compare) (nth update-nth nfix len))))))
(local (defthm fn-psc-literal-reference-unfolds
 (equal (fn-psc-get ref (fn-psc-literal pos bytes resume c)) bytes)
 :hints (("Goal" :in-theory (e/d (fn-psc-literal) (nth update-nth nfix len))))))
(local (defthm fn-psc-agent-compare-reference-unfolds
 (equal (fn-psc-get ref (fn-psc-agent-compare pos resume c)) :incoming)
 :hints (("Goal" :in-theory (e/d (fn-psc-agent-compare) (nth update-nth nfix len))))))
(local (defthm fn-psc-msgid-compare-reference-unfolds
 (equal (fn-psc-get ref (fn-psc-msgid-compare pos resume c)) *fn-inj-message-id-field*)
 :hints (("Goal" :in-theory (e/d (fn-psc-msgid-compare) (nth update-nth nfix len))))))
(local (defthm fn-psc-date-compare-reference-unfolds
 (equal (fn-psc-get ref (fn-psc-date-compare pos resume c)) *fn-inj-date-field*)
 :hints (("Goal" :in-theory (e/d (fn-psc-date-compare) (nth update-nth nfix len))))))
(local (defthm fn-psc-info-compare-reference-unfolds
 (equal (fn-psc-get ref (fn-psc-info-compare pos resume c)) *fn-inj-injection-info-field*)
 :hints (("Goal" :in-theory (e/d (fn-psc-info-compare) (nth update-nth nfix len))))))
(local (defthm fn-psc-control-preserves-reference
 (implies (fn-psc-referencep (fn-psc-get ref c))
          (fn-psc-referencep (fn-psc-get ref (fn-psc-control c))))
 :hints (("Goal" :in-theory (e/d (fn-psc-control) (nth update-nth nfix len fn-psc-referencep))))))
(defthm fn-psc-begin-established-reference
 (fn-psc-referencep (fn-psc-get ref (fn-psc-begin mode n msgid agent-span incoming-n)))
 :hints (("Goal" :in-theory (e/d (fn-psc-begin) (nth update-nth nfix len fn-psc-referencep)))))
(defthm fn-psc-step-preserves-reference
 (implies (fn-psc-referencep (fn-psc-get ref c))
          (fn-psc-referencep (fn-psc-get ref (fn-psc-step c byte))))
 :hints (("Goal" :in-theory (e/d (fn-psc-step) (nth update-nth nfix len fn-psc-referencep)))))
(in-theory (disable fn-psc-referencep))
(local (defthm fn-psc-finish-true-listp
 (implies (true-listp c) (true-listp (fn-psc-finish result c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-finish) (nth update-nth nfix len))))))
(local (defthm fn-psc-compare-true-listp
 (implies (true-listp c) (true-listp (fn-psc-compare pos ref start count resume c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-compare) (nth update-nth nfix len))))))
(local (defthm fn-psc-literal-true-listp
 (implies (true-listp c) (true-listp (fn-psc-literal pos bytes resume c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-literal) (nth update-nth nfix len))))))
(local (defthm fn-psc-return-true-listp
 (implies (true-listp c) (true-listp (fn-psc-return ok c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-return) (nth update-nth nfix len))))))
(local (defthm fn-psc-agent-compare-true-listp
 (implies (true-listp c) (true-listp (fn-psc-agent-compare pos resume c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-agent-compare) (nth update-nth nfix len))))))
(local (defthm fn-psc-msgid-compare-true-listp
 (implies (true-listp c) (true-listp (fn-psc-msgid-compare pos resume c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-msgid-compare) (nth update-nth nfix len))))))
(local (defthm fn-psc-date-compare-true-listp
 (implies (true-listp c) (true-listp (fn-psc-date-compare pos resume c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-date-compare) (nth update-nth nfix len))))))
(local (defthm fn-psc-info-compare-true-listp
 (implies (true-listp c) (true-listp (fn-psc-info-compare pos resume c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-info-compare) (nth update-nth nfix len))))))
(local (defthm fn-psc-control-true-listp
 (implies (true-listp c) (true-listp (fn-psc-control c)))
 :hints (("Goal" :in-theory (e/d (fn-psc-control) (nth update-nth nfix len))))))
(defthm fn-psc-step-preserves-true-listp
 (implies (true-listp c) (true-listp (fn-psc-step c byte)))
 :rule-classes (:rewrite :type-prescription)
 :hints (("Goal" :in-theory (e/d (fn-psc-step) (nth update-nth nfix len)))))
