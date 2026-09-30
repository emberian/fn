(in-package "ACL2")
(include-book "../../books/consumer-config-publication")
(include-book "config-owner-publish-tests")

; Actual existing reachable durable configuration input. These proposed
; fixtures require matching source admission; raw routing does not prove them.
(defconst *ccpt-configuration* (mv-list 2 (fn-oclc-publish *ocp-closed* 3 *ocp-max*)))
(defconst *ccpt-approved* '(:ok nil :literal-borrowed-metadata))
;@positive fn-ccp-durable-collector-installs-the-approved-consumer
(assert-event
 (let ((one (fn-ccp-collect (car *ccpt-configuration*)
                           (cadr *ccpt-configuration*) *ocp-closed* *ccpt-approved*)))
   (and (eq (car *ccpt-configuration*) :durable)
        (eq (car *ccpt-approved*) :ok)
        (eq (car one) :durable)
        (equal (fn-sn-consumer (fn-own-store (fn-ocfg-owner (cadr one)))) nil)
        (equal (caddr one) :literal-borrowed-metadata)
        (null (cadddr one)))))
;@hypothesis-removal fn-ccp-durable-collector-installs-the-approved-consumer durable-verdict
(assert-event
 (let ((one (fn-ccp-collect :recovery-required (cadr *ccpt-configuration*)
                           *ocp-closed* *ccpt-approved*)))
   (and (not (eq :recovery-required :durable))
        (eq (car *ccpt-approved*) :ok)
        (not (eq (car one) :durable)))))
;@hypothesis-removal fn-ccp-durable-collector-installs-the-approved-consumer approved
(assert-event
 (let ((one (fn-ccp-collect :durable (cadr *ccpt-configuration*)
                           *ocp-closed* '(:recovery-required :stale))))
   (and (eq :durable :durable)
        (not (eq (car '(:recovery-required :stale)) :ok))
        (not (eq (car one) :durable)))))
;@positive fn-ccp-unapproved-publication-requires-recovery
(assert-event
 (and (not (eq (car '(:recovery-required :stale)) :ok))
      (equal (fn-ccp-publish *ocp-closed* 3 *ocp-max* '(:recovery-required :stale))
             (list :recovery-required *ocp-closed* nil nil))))
;@hypothesis-removal fn-ccp-unapproved-publication-requires-recovery approved
(assert-event
 (and (eq (car *ccpt-approved*) :ok)
      (not (equal (fn-ccp-publish *ocp-closed* 3 *ocp-max* *ccpt-approved*)
                   (list :recovery-required *ocp-closed* nil nil)))))
