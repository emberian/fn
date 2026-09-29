; Durable lifecycle witnesses. Primitive authenticity is a separate native
; coordinate; these tests exercise real Store reserve/publish/finish paths.
(in-package "ACL2")
(include-book "../../books/statement-keyring-publication")
(include-book "../../books/codec-attach")
(include-book "../../books/crypto-attach")
(defconst *skpt-principal* (make-list 32 :initial-element 7))
(defconst *skpt-keys*
 (list (cons :ed25519 (make-list 32 :initial-element 11))
       (cons :ml-dsa-65 (make-list 1952 :initial-element 13))))
(defun skpt-reserve (s)
 (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil)
                              :frontier-file :ok)
                    :frontier-replace :ok) :frontier-directory :ok))
(defun skpt-publish (s)
 (fn-sn-io (fn-sn-io (fn-sn-io s :record-file :ok)
                    :record-link :ok) :record-directory :ok))
(make-event `(defconst *skpt-enroll*
 ',(fn-hl-enroll-event 0 0 0 1 *skpt-principal* *skpt-keys* nil)))
(make-event `(defconst *skpt-completing*
 ',(skpt-publish (fn-sn-prepare-identity
                  (skpt-reserve (fn-sn-initial '("example") 32)) *skpt-enroll*))))
(assert-event (and (fn-sn-completion-enabledp *skpt-completing*)
                  (fn-stxk-p (fn-sn-completion-record *skpt-completing*))
                  (fn-skp-resolvedp *skpt-completing*)))
; Complete antecedent and conclusion of the all-kind keystone, at the actual
; identity arm of finish, with the observed durable files and current node.
(assert-event
 (fn-skp-resolvedp
  (fn-sn-finish-identity *skpt-completing* (fn-sn-files *skpt-completing*)
                        (fn-sn-completion-record *skpt-completing*)
                        (fn-sn-node *skpt-completing*))))
(make-event `(defconst *skpt-after* ',(fn-sn-finish *skpt-completing*)))
(assert-event
 (and (fn-skp-resolvedp *skpt-after*)
      (equal (fn-sn-keyring-generation *skpt-after*) 1)
      (equal (fn-sn-keyring *skpt-after*)
             (list (cons *skpt-principal* (cdr (cadr *skpt-keys*)))))))
; Corrupted-state hypothesis removal: change only the old carried generation.
; Every retained hypothesis (none) holds; the omitted resolvedp is false and
; a nonsnapshot identity finish cannot repair it. Not a reachable-state claim.
(make-event `(defconst *skpt-corrupt*
 ',(update-nth 6 99 *skpt-after*)))
(assert-event
 (and (not (fn-skp-resolvedp *skpt-corrupt*))
      (not (fn-skp-resolvedp
             (fn-sn-finish-identity *skpt-corrupt* (fn-sn-files *skpt-corrupt*)
                                   nil (fn-sn-node *skpt-corrupt*))))))

; Literal host-called finish theorem, including the sole carried premise.
(assert-event
 (and (fn-skp-resolvedp *skpt-completing*)
      (fn-skp-resolvedp (fn-sn-finish *skpt-completing*))))
; Corrupted-state removal witness for the actual finish subject: idle state
; carries no enabled completion and therefore preserves its bad generation.
(assert-event
 (and (not (fn-skp-resolvedp *skpt-corrupt*))
      (not (fn-skp-resolvedp (fn-sn-finish *skpt-corrupt*)))))
