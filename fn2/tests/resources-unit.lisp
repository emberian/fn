; Negative fixtures for every certification-time check of resources.lisp:
; each predicate accepts the real table and rejects one named defect.
; Run: sh fn2/tools/certify.sh tests/resources-unit.lisp
(in-package "ACL2")
(include-book "../books/resources")

(defmacro fn2-resource-rejects (name form)
  `(assert-event (not ,form) :msg (msg "~x0: a defective table was accepted" ',name)))

; (a) one total order: no tie, no gap, no duplicate kind, no prose-free row.
(fn2-resource-rejects :order-tie
  (fn2-resource-order-p
   (cons (cons :tie (cdr (car *fn2-resource-order*))) *fn2-resource-order*)))
(fn2-resource-rejects :order-gap (fn2-resource-order-p (cdr *fn2-resource-order*)))
(fn2-resource-rejects :order-duplicate
  (fn2-resource-order-p
   (append *fn2-resource-order*
           (list (cons :operation '(:rank 23 :unit :op :bound (:profile :o) :why "again"))))))
(fn2-resource-rejects :order-no-why
  (fn2-resource-order-p
   (append *fn2-resource-order* (list '(:extra :rank 23 :unit :op :bound (:profile :o))))))

(defun fn2-resource-test-bundle (acquires holds reserve transition)
  (declare (xargs :guard t))
  (list (list 'fn2-test transition) :acquires acquires :holds holds :reserve reserve
        :status :exists :owed-by nil :why "fixture"))
(defmacro fn2-resource-bundle-ok (acquires holds reserve transition)
  `(fn2-resource-bundle-p (fn2-resource-test-bundle ',acquires ',holds ',reserve ',transition)
                          *fn2-resource-order* *fn2-resource-reserves*))

; (b)/(c) bundles: the control is accepted, each defect refused.
(assert-event (fn2-resource-bundle-ok (:rx-range :operation) (:connection-row) nil :receive))
(fn2-resource-rejects :bundle-descends (fn2-resource-bundle-ok (:operation :rx-range) nil nil :receive))
(fn2-resource-rejects :bundle-tie (fn2-resource-bundle-ok (:rx-range :rx-range) nil nil :receive))
(fn2-resource-rejects :holds-above-first
  (fn2-resource-bundle-ok (:rx-range :operation) (:tls-slot) nil :receive))
(fn2-resource-rejects :holds-equal-first
  (fn2-resource-bundle-ok (:rx-range :operation) (:rx-range) nil :receive))
(fn2-resource-rejects :unknown-kind (fn2-resource-bundle-ok (:bogus) nil nil :receive))
(fn2-resource-rejects :unknown-held (fn2-resource-bundle-ok (:operation) (:bogus) nil :receive))
; (e) protected transitions draw a reserve covering the whole bundle.
(assert-event (fn2-resource-bundle-ok (:operation) (:connection-row) :close :close))
(fn2-resource-rejects :close-unreserved (fn2-resource-bundle-ok (:operation) nil nil :close))
(fn2-resource-rejects :fence-reserve-short (fn2-resource-bundle-ok (:fence-slot :operation) nil :close :fence))
(fn2-resource-rejects :wrong-reserve (fn2-resource-bundle-ok (:operation) nil :system :arm-wake))
; No unit an issue reserve covers is held while waiting.
(fn2-resource-rejects :reserve-held-while-waiting
  (fn2-resource-bundle-ok (:operation) (:fence-slot) :close :close))
(fn2-resource-rejects :duplicate-bundle
  (fn2-resource-bundles-p (append *fn2-resource-bundles* (list (car *fn2-resource-bundles*)))
                          *fn2-resource-order* *fn2-resource-reserves*))
(fn2-resource-rejects :bad-owed-by
  (fn2-resource-bundles-p
   (list (list '(fn2-test :receive) :acquires '(:operation) :holds nil :reserve nil
               :status :exists :owed-by :someone :why "fixture"))
   *fn2-resource-order* *fn2-resource-reserves*))

; (d) release lists descend; a refusal releases nothing.
(fn2-resource-rejects :release-ascends
  (fn2-resource-releases-p '(((fn2-test :close) :releases (:connection-row :operation)))
                           *fn2-resource-order*))
(fn2-resource-rejects :refusal-releases
  (fn2-resource-releases-p '(((fn2-test :refusal) :releases (:operation))) *fn2-resource-order*))

; (e) reserves name known kinds once.
(fn2-resource-rejects :reserve-unknown-kind
  (fn2-resource-reserves-p '((:close :covers (:bogus) :issue t :why "x")) *fn2-resource-order*))
(fn2-resource-rejects :reserve-duplicate
  (fn2-resource-reserves-p (cons (car *fn2-resource-reserves*) *fn2-resource-reserves*)
                           *fn2-resource-order*))

; (f) no per-recipient debt in a batch; no membership after publish.
(fn2-resource-rejects :batch-holds-recipient
  (fn2-resource-batch-phases-p '((:collect :holds (:batch-membership :wait-row) :after-publish nil))
                               *fn2-resource-order* *fn2-resource-per-recipient*))
(fn2-resource-rejects :membership-after-publish
  (fn2-resource-batch-phases-p '((:notify :holds (:batch-membership) :after-publish t))
                               *fn2-resource-order* *fn2-resource-per-recipient*))

; Effects: transfer and release only what is held; acquisitions ascend.
(assert-event (fn2-resource-effects-p
               '(((fn2-listener :admit) :holds-before (:accept-credit :connection-row)
                  :effects ((:transfer (:connection-row) :to fn2-echo) (:acquire (:rx-range) :for fn2-echo))))
               *fn2-resource-order*))
(fn2-resource-rejects :transfer-unheld
  (fn2-resource-effects-p '(((fn2-test :admit) :holds-before (:accept-credit)
                             :effects ((:transfer (:connection-row) :to fn2-echo))))
                          *fn2-resource-order*))
(fn2-resource-rejects :acquire-below-held
  (fn2-resource-effects-p '(((fn2-test :admit) :holds-before (:rx-range)
                             :effects ((:acquire (:connection-row)))))
                          *fn2-resource-order*))
(fn2-resource-rejects :release-unheld-after-transfer
  (fn2-resource-effects-p '(((fn2-test :admit) :holds-before (:accept-credit :connection-row)
                             :effects ((:transfer (:connection-row) :to fn2-echo)
                                       (:release (:connection-row)))))
                          *fn2-resource-order*))
(fn2-resource-rejects :unknown-effect
  (fn2-resource-effects-p '(((fn2-test :admit) :holds-before (:accept-credit)
                             :effects ((:borrow (:connection-row)))))
                          *fn2-resource-order*))

; Interim A holds and wait reasons.
(fn2-resource-rejects :holds-unknown
  (fn2-resource-machine-holds-p '((fn2-test (:free :bogus))) *fn2-resource-order*))
(fn2-resource-rejects :wait-reason-unknown
  (fn2-resource-wait-reasons-p '((:op-credit . :bogus)) *fn2-resource-order*))

; (g) The proved lemma has a subject: an unranked pair of waiters, each
; holding what the other awaits, is a cycle, and the ranked check refuses it.
(defconst *fn2-resource-test-cycle*
  '(((:rx-range) . :connection-row) ((:connection-row) . :rx-range)))
(assert-event (fn2-resource-cyclep *fn2-resource-test-cycle*))
(fn2-resource-rejects :cycle-ranked
  (fn2-resource-waiters-ranked-p *fn2-resource-test-cycle* *fn2-resource-order*))
(assert-event (fn2-resource-waiters-ranked-p
               '(((:connection-row :rx-range) . :operation) ((:accept-credit) . :connection-row))
               *fn2-resource-order*))
