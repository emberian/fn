; Literal full-retained establishment, reachable readiness removal and a
; separately labelled corrupted-state removal of the retained invariant.
(in-package "ACL2")
(include-book "../../books/catalog-context-recovery")
(include-book "../../books/codec-attach")
(include-book "../../books/crypto-attach")
(defconst *ccr-principal* (make-list 32 :initial-element 7))
(defconst *ccr-keys* (list (cons :ed25519 (make-list 32 :initial-element 11))
                         (cons :ml-dsa-65 (make-list 1952 :initial-element 13))))
(make-event `(defconst *ccr-enroll*
 ',(fn-hl-enroll-event 0 0 0 1 *ccr-principal* *ccr-keys* nil)))
(make-event `(defconst *ccr-open*
 ',(fn-cpo-open-observed (list *fn-cfg-default-record*) 1 (list *ccr-enroll*))))
(make-event `(defconst *ccr-ready*
 ',(fn-snrt-run (fn-sn-open-state *ccr-open*)
               '((:io :recovery-barrier :ok)
                 (:io :recovery-barrier :ok)
                 (:io :recovery-barrier :ok)))))
(assert-event
 (and (fn-sn-open-okp *ccr-open*)
      (consp (fn-sn-keyring-snapshots *ccr-ready*))
      (consp (fn-sn-keyring *ccr-ready*))
      (fn-osr-retainedp *ccr-ready*)
      (equal (fn-sf-phase (fn-sn-files *ccr-ready*)) :ready)
      (fn-snh-recovery-context-coherentp *ccr-ready*)))
(make-event `(defconst *ccr-next-enroll*
 ',(fn-hl-enroll-event 1 1 1 2 *ccr-principal* *ccr-keys*
                      (fn-sn-keyring-snapshots *ccr-ready*))))
(make-event `(defconst *ccr-reserved*
 ',(fn-snrt-run *ccr-ready*
     '((:io :start-frontier nil) (:io :frontier-file :ok)
       (:io :frontier-replace :ok) (:io :frontier-directory :ok)))))
(make-event `(defconst *ccr-completing*
 ',(fn-snrt-run (fn-sn-prepare-identity *ccr-reserved* *ccr-next-enroll*)
               '((:io :record-file :ok) (:io :record-link :ok)
                 (:io :record-directory :ok)))))
; Readiness is necessary: a newly published snapshot precedes live finish.
(assert-event
 (and (fn-osr-retainedp *ccr-completing*)
      (fn-sn-completion-enabledp *ccr-completing*)
      (not (equal (fn-sf-phase (fn-sn-files *ccr-completing*)) :ready))
      (not (fn-snh-recovery-context-coherentp *ccr-completing*))))
; Corrupted-state removal of full retained carry; readiness still holds.
(assert-event
 (let ((s (update-nth 6 99 *ccr-ready*)))
   (and (not (fn-osr-retainedp s))
        (equal (fn-sf-phase (fn-sn-files s)) :ready)
        (not (fn-snh-recovery-context-coherentp s)))))
