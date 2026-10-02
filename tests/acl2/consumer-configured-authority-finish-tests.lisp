; Inner account boundary; the configured-node/identity issuer is a separate
; composition prerequisite. Node and identity labels below are fixture inputs.
(in-package "ACL2")
(include-book "../../books/consumer-configured-authority-finish")
(include-book "consumer-account-config-commit-tests") ; its fixtures are used by non-local events

(defconst *caeft-event* '(:consumer-authority 0 1 0 (:authority-begin (65) 0 1 7)))
(defconst *caeft-produced*
 (list (fn-stxk-initial-context 1) :same-fields :carried :none nil nil))
(defconst *caeft-before*
 (fn-capr-state :actual-node-input (fn-stxk-initial-context 0) :prior-fields
                 *acjt-initial* *acjt-metadata* nil
                 (list :ok *acjt-initial* :committed-root 17) nil
                 :withdrawals :visible :verdicts 7 0 nil
                 (list *caeft-event*) :config-source))
(defconst *caeft-one*
 (fn-cape-authority-finish *caeft-before* *caeft-produced* :retained-next-node *bcpt-base* nil 0))

;@positive-witness fn-cape-authority-finish-preserves-exposed-view-and-root
(assert-event
 (let ((after (fn-cp-nth 1 *caeft-one*)))
  (and (equal (fn-cp-nth 0 *caeft-one*) :advanced)
       (equal (fn-cp-nth 9 after) (fn-cp-nth 9 *caeft-before*))
       (equal (fn-cp-nth 10 after) (fn-cp-nth 10 *caeft-before*))
       (equal (fn-cp-nth 11 after) (fn-cp-nth 11 *caeft-before*))
       (equal (fn-cp-nth 2 (fn-cp-nth 7 after)) (fn-cp-nth 2 (fn-cp-nth 7 *caeft-before*)))
       (equal (fn-cp-nth 3 (fn-cp-nth 7 after)) (fn-cp-nth 3 (fn-cp-nth 7 *caeft-before*))))))
; The theorem is unconditional, so it has no hypothesis-removal obligations.
;@mutation-witness authority-installed-fields-come-from-same-full7
(assert-event
 (let ((after (fn-cp-nth 1 *caeft-one*)) (full (fn-cp-nth 2 *caeft-one*)))
  (and (equal full (fn-acj-stage *acjt-initial* *acjt-metadata* nil *bcpt-base* *caeft-event* 0 nil))
       (equal (len full) 7) (null (fn-cp-nth 2 full)) (null (fn-cp-nth 3 full))
       (equal (fn-cp-nth 1 after) :retained-next-node)
       (equal (fn-cp-nth 2 after) (fn-cp-nth 0 *caeft-produced*))
       (equal (fn-cp-nth 3 after) (fn-cp-nth 1 *caeft-produced*))
       (equal (fn-cp-nth 4 after) (fn-cp-nth 1 full))
       (equal (fn-cp-nth 5 after) (fn-cp-nth 4 full))
       (equal (fn-cp-nth 6 after) (fn-cp-nth 6 full))
       (equal (fn-cp-nth 8 after) 0) (equal (fn-cp-nth 12 after) 7)
       (equal (fn-cp-nth 13 after) 1) (null (fn-cp-nth 15 after)))))
;@corrupted-state authority-rejects-effects-before-account-mutation
(assert-event
 (and (equal (fn-cape-authority-finish *caeft-before* (update-nth 3 :verdict *caeft-produced*)
                 :retained-next-node *bcpt-base* nil 0)
             (list :unavailable *caeft-before* :authority-identity-effect))
      (equal (fn-cape-authority-finish *caeft-before* (update-nth 2 :unavailable *caeft-produced*)
                 :retained-next-node *bcpt-base* nil 0)
             (list :unavailable *caeft-before* :identity-carries))
      (equal (fn-cape-authority-finish (update-nth 13 7 *caeft-before*) *caeft-produced*
                 :retained-next-node *bcpt-base* nil 0)
             (fn-capr-fault (update-nth 13 7 *caeft-before*) :event-sequence))))
;@mutation-witness actual-preparation-never-publishes-before-typed-C
(assert-event
 (and (equal (fn-cp-nth 0 *acjt-final*) :ok)
      (equal (fn-cp-nth 3 *acjt-final*) (fn-cp-nth 3 (fn-cp-nth 0 *acjt-prepared*)))
      (equal (fn-cfg-generation (fn-cp-nth 6 *acjt-final*)) 8)
      (equal (fn-cp-nth 1 (fn-cp-nth 6 (fn-cp-nth 1 *acjt-final*))) 1)
      (equal (fn-cp-nth 3 (fn-cp-nth 2 *acjt-final*)) (list *cadt-b*))))
;@mutation-witness same-account-decision-produces-seven-exact-cp-child-carries
(assert-event
 (let* ((full (fn-cp-nth 2 *caeft-one*)) (cp (fn-cp-nth 1 full))
        (metadata (fn-cp-nth 4 full)))
  (equal (fn-cp-nth 1 metadata) (fn-acjt-fields cp))))

;@corrupted-state dense-coordinate-is-not-an-identity-sequence
; This inner scalar-provenance witness deliberately varies the supplied count;
; it is not a reachable whole-Store claim about a mismatched count/sequence.
(assert-event
 (let* ((one (fn-cape-authority-finish *caeft-before* *caeft-produced*
                    :retained-next-node *bcpt-base* nil 23))
        (after (fn-cp-nth 1 one)))
  (and (equal (fn-cp-nth 0 one) :advanced)
       (equal (fn-cp-nth 1 *caeft-event*) 0)
       (equal (fn-cp-nth 8 after) 23))))
;@corrupted-state malformed-dense-coordinate-never-mutates
(assert-event
 (equal (fn-cape-authority-finish *caeft-before* *caeft-produced*
               :retained-next-node *bcpt-base* nil -1)
        (fn-capr-fault *caeft-before* :event-count)))
