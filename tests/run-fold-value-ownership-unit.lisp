; Prepared declaration controls. No ACL2 admission/execution is claimed.
(in-package "ACL2")
(include-book "../books/runs-served")
(defconst *fn2-rf-owned-control-fold*
 '(:events ((:add (group amount) :set ((total (+ total amount)))))
   :init :empty :coverage :history-start :observe (total)))
(assert-event
 (and (fn2-rf-okp *fn2-rf-owned-control-fold* '((group (:id group))) '((total :u60)) :latest)
      (equal (car (fn2-defrunschema 'fn2-rf-owned-control 240 '((group (:id group))) '((total :u60)) :latest :run-data *fn2-rf-owned-control-fold* nil)) 'progn)
      (not (fn2-rf-valuesp '((total :digest))))
      (not (fn2-rf-valuesp '((total (:octets 32)))))
      (not (fn2-rf-valuesp '((total (:octets 1024)))))
      (not (fn2-rf-valuesp '((total (:ref :physical)))))
      (equal (car (fn2-defrunschema 'fn2-rf-borrowed-control 241 '((group (:id group))) '((total (:octets 32))) :latest :run-data *fn2-rf-owned-control-fold* nil)) 'make-event)
      ; Removing FOLD admits the same octet representation: this restricts
      ; unsupported borrowed fold semantics, not the stored byte domain.
      (equal (car (fn2-defrunschema 'fn2-rf-byte-control 242 '((group (:id group))) '((total (:octets 32))) :latest :run-data nil nil)) 'progn)
      (equal (car (fn2-defrunschema 'fn2-rf-unique-control 243 '((group (:id group))) '((total (:octets 1024))) :unique :run-data nil nil)) 'progn)
      ; UNION's scalar equality must also reject a vector beyond key bounds.
      (not (fn2-rs-int-valuesp '((total (:octets 1024)))))
      (equal (car (fn2-defrunschema 'fn2-rf-union-control 244 '((group (:id group))) '((total (:octets 1024))) :union :run-data nil nil)) 'make-event)))
(make-event
 (let ((rows (fn2-decl-rows :schema (w state))))
  (value `(assert-event
           (and (< 0 (fn2-rs-fold-descriptor-count ',rows))
                (fn2-rs-fold-values-ownedp ',rows))))))
