(in-package "ACL2")
(include-book "../../books/consumer-entry-completion-model")
(local (include-book "consumer-entry-preparation-tests"))

(defconst *cect-cp*
 (fn-cp-apply-trace (fn-cp-initial '(10) '(11) 6)
  '((:register (4) (8) (9) 0 0 1) (:register (3) (7) (9) 0 0 2)
    (:register (2) (6) (9) 0 0 3) (:register (1) (5) (9) 0 0 4))))
(defconst *cect-entries* (fn-cp-nth 5 *cect-cp*))
(defconst *cect-meta* (fn-cpmm-annotation *cect-cp*))
(defconst *cect-remove* '(:unregister (2) 3))
(defconst *cect-old* (fn-cp-find '(2) *cect-entries*))
(defconst *cect-rest* (fn-cp-remove '(2) *cect-entries*))
(defconst *cect-ack* (list :ack (fn-cp-cursor '(10) '(11) '(2) '(6) '(9) 0 0 3 2)))

;@positive fn-cecm-selected-local-is-actual-apply
(assert-event
 (and (not (member-eq (fn-cp-nth 0 *cect-remove*) '(:remote-register :remote-rebase)))
      (equal *cect-old* (fn-cp-find (fn-cep-operation-key *cect-remove*) *cect-entries*))
      (equal *cect-rest* (fn-cp-remove (fn-cep-operation-key *cect-remove*) *cect-entries*))
      (implies (eq (fn-cp-nth 0 *cect-remove*) :ack)
               (or (equal (len *cect-old*) 8) (equal (len *cect-old*) 10)))
      (equal (fn-cp-nth 1 (fn-cec-selected-local *cect-cp* *cect-remove* *cect-old* *cect-rest*))
             (fn-cp-apply *cect-cp* *cect-remove*))))
;@hypothesis-removal fn-cecm-selected-local-is-actual-apply local-kind
(assert-event
 (let ((op '(:remote-register (99) (6) (9) 0 0 5 ((97)) (88))))
  (and (member-eq (fn-cp-nth 0 op) '(:remote-register :remote-rebase))
       (equal nil (fn-cp-find (fn-cep-operation-key op) *cect-entries*))
       (equal *cect-entries* (fn-cp-remove (fn-cep-operation-key op) *cect-entries*))
       (implies (eq (fn-cp-nth 0 op) :ack) (or (equal (len nil) 8) (equal (len nil) 10)))
       (not (equal (fn-cp-nth 1 (fn-cec-selected-local *cect-cp* op nil *cect-entries*))
                    (fn-cp-apply *cect-cp* op))))))
;@hypothesis-removal fn-cecm-selected-local-is-actual-apply exact-selected-old
(assert-event
 (let ((bad (fn-cp-entry '(2) '(6) '(9) 0 0 4 0)))
  (and (not (member-eq (fn-cp-nth 0 *cect-remove*) '(:remote-register :remote-rebase)))
       (not (equal bad (fn-cp-find (fn-cep-operation-key *cect-remove*) *cect-entries*)))
       (equal *cect-rest* (fn-cp-remove (fn-cep-operation-key *cect-remove*) *cect-entries*))
       (implies (eq (fn-cp-nth 0 *cect-remove*) :ack)
                (or (equal (len bad) 8) (equal (len bad) 10)))
       (not (equal (fn-cp-nth 1 (fn-cec-selected-local *cect-cp* *cect-remove* bad *cect-rest*))
                    (fn-cp-apply *cect-cp* *cect-remove*))))))
;@hypothesis-removal fn-cecm-selected-local-is-actual-apply exact-removal
(assert-event
 (and (not (member-eq (fn-cp-nth 0 *cect-remove*) '(:remote-register :remote-rebase)))
      (equal *cect-old* (fn-cp-find (fn-cep-operation-key *cect-remove*) *cect-entries*))
      (not (equal nil (fn-cp-remove (fn-cep-operation-key *cect-remove*) *cect-entries*)))
      (implies (eq (fn-cp-nth 0 *cect-remove*) :ack)
               (or (equal (len *cect-old*) 8) (equal (len *cect-old*) 10)))
      (not (equal (fn-cp-nth 1 (fn-cec-selected-local *cect-cp* *cect-remove* *cect-old* nil))
                   (fn-cp-apply *cect-cp* *cect-remove*)))))
;@hypothesis-removal fn-cecm-selected-local-is-actual-apply maintained-ack-entry-shape
; The eleven-field entry is separately labeled corrupted durable state.
(assert-event
 (let* ((bad (append *cect-old* '(nil nil nil)))
        (cp (update-nth 5 (list bad) *cect-cp*)) (op *cect-ack*))
  (and (not (member-eq (fn-cp-nth 0 op) '(:remote-register :remote-rebase)))
       (equal bad (fn-cp-find (fn-cep-operation-key op) (fn-cp-nth 5 cp)))
       (equal nil (fn-cp-remove (fn-cep-operation-key op) (fn-cp-nth 5 cp)))
       (not (implies (eq (fn-cp-nth 0 op) :ack)
                     (or (equal (len bad) 8) (equal (len bad) 10))))
       (not (equal (fn-cp-nth 1 (fn-cec-selected-local cp op bad nil)) (fn-cp-apply cp op))))))

;@positive fn-cecm-selected-proposal-is-actual-projection-decision
(assert-event
 (and (equal *cect-old* (fn-cp-find (fn-cep-operation-key *cect-ack*) *cect-entries*))
      (equal (fn-cec-proposal-local *cect-cp* *cect-ack* *cect-old*)
             (fn-cpe-projection-decision *cect-cp* *cect-ack*))
      (equal (fn-cec-proposal-local *cect-cp* *cect-ack* *cect-old*) (list :write *cect-ack*))))
;@hypothesis-removal fn-cecm-selected-proposal-is-actual-projection-decision exact-selected-old
(assert-event
 (and (not (equal nil (fn-cp-find (fn-cep-operation-key *cect-remove*) *cect-entries*)))
      (not (equal (fn-cec-proposal-local *cect-cp* *cect-remove* nil)
                   (fn-cpe-projection-decision *cect-cp* *cect-remove*)))))

(defun fn-cect-local-carry-lawp (c p q qv v e a)
 (declare (xargs :guard t :verify-guards nil))
 (equal (fn-cec-local-entry-carry (fn-cp-entry c p q qv v e a))
        (fn-scs-summary (fn-cp-entry c p q qv v e a))))
;@positive fn-cecm-local-entry-constructor-carry
(assert-event
 (and (fn-scc-octet-listp '(1)) (fn-scc-octet-listp '(2)) (fn-scc-octet-listp '(3))
      (integerp 0) (integerp 0) (integerp 1) (integerp 256)
      (fn-cect-local-carry-lawp '(1) '(2) '(3) 0 0 1 256)))
;@hypothesis-removal fn-cecm-local-entry-constructor-carry consumer-octets
(assert-event
 (and (not (fn-scc-octet-listp '(999)))
      (fn-scc-octet-listp '(2))
      (fn-scc-octet-listp '(3))
      (integerp 0)
      (integerp 0)
      (integerp 1)
      (integerp 256)
      (not (fn-cect-local-carry-lawp '(999) '(2) '(3) 0 0 1 256))))
;@hypothesis-removal fn-cecm-local-entry-constructor-carry principal-octets
(assert-event
 (and (fn-scc-octet-listp '(1))
      (not (fn-scc-octet-listp '(999)))
      (fn-scc-octet-listp '(3))
      (integerp 0)
      (integerp 0)
      (integerp 1)
      (integerp 256)
      (not (fn-cect-local-carry-lawp '(1) '(999) '(3) 0 0 1 256))))
;@hypothesis-removal fn-cecm-local-entry-constructor-carry query-octets
(assert-event
 (and (fn-scc-octet-listp '(1))
      (fn-scc-octet-listp '(2))
      (not (fn-scc-octet-listp '(999)))
      (integerp 0)
      (integerp 0)
      (integerp 1)
      (integerp 256)
      (not (fn-cect-local-carry-lawp '(1) '(2) '(999) 0 0 1 256))))
;@hypothesis-removal fn-cecm-local-entry-constructor-carry qver-scalar
(assert-event
 (and (fn-scc-octet-listp '(1))
      (fn-scc-octet-listp '(2))
      (fn-scc-octet-listp '(3))
      (not (integerp '(3)))
      (integerp 0)
      (integerp 1)
      (integerp 256)
      (not (fn-cect-local-carry-lawp '(1) '(2) '(3) '(3) 0 1 256))))
;@hypothesis-removal fn-cecm-local-entry-constructor-carry view-scalar
(assert-event
 (and (fn-scc-octet-listp '(1))
      (fn-scc-octet-listp '(2))
      (fn-scc-octet-listp '(3))
      (integerp 0)
      (not (integerp '(3)))
      (integerp 1)
      (integerp 256)
      (not (fn-cect-local-carry-lawp '(1) '(2) '(3) 0 '(3) 1 256))))
;@hypothesis-removal fn-cecm-local-entry-constructor-carry epoch-scalar
(assert-event
 (and (fn-scc-octet-listp '(1))
      (fn-scc-octet-listp '(2))
      (fn-scc-octet-listp '(3))
      (integerp 0)
      (integerp 0)
      (not (integerp '(3)))
      (integerp 256)
      (not (fn-cect-local-carry-lawp '(1) '(2) '(3) 0 0 '(3) 256))))
;@hypothesis-removal fn-cecm-local-entry-constructor-carry ack-scalar
(assert-event
 (and (fn-scc-octet-listp '(1))
      (fn-scc-octet-listp '(2))
      (fn-scc-octet-listp '(3))
      (integerp 0)
      (integerp 0)
      (integerp 1)
      (not (integerp '(3)))
      (not (fn-cect-local-carry-lawp '(1) '(2) '(3) 0 0 1 '(3)))))

(defun fn-cect-remote-entry (a groups account)
 (declare (xargs :guard t))
 (append (fn-cp-entry '(1) '(2) '(3) 0 0 1 a) (list groups account)))
(defun fn-cect-remote-carry-lawp (a b groups account carry)
 (declare (xargs :guard t :verify-guards nil))
 (equal (fn-cec-remote-ack-carry (fn-cect-remote-entry a groups account) carry b)
        (fn-scs-summary (fn-cect-remote-entry b groups account))))
;@positive fn-cecm-remote-ack-retains-exact-carry
(assert-event
 (let ((carry (fn-scs-summary (fn-cect-remote-entry 255 '((97)) '(88)))))
  (and (not (fn-scc-octet-listp (list '((97)) '(88))))
       (integerp 255) (integerp 256)
       (equal carry (fn-scs-summary (fn-cect-remote-entry 255 '((97)) '(88))))
       (fn-cect-remote-carry-lawp 255 256 '((97)) '(88) carry))))
;@hypothesis-removal fn-cecm-remote-ack-retains-exact-carry noncollapsing-remote-tail
; Numeric group/account is separately labeled corrupted stored entry state.
(assert-event
 (let ((carry (fn-scs-summary (fn-cect-remote-entry 255 1 2))))
  (and (fn-scc-octet-listp (list 1 2)) (integerp 255) (integerp 256)
       (equal carry (fn-scs-summary (fn-cect-remote-entry 255 1 2)))
       (not (fn-cect-remote-carry-lawp 255 256 1 2 carry)))))
;@hypothesis-removal fn-cecm-remote-ack-retains-exact-carry old-ack-scalar
(assert-event
 (let ((carry (fn-scs-summary (fn-cect-remote-entry '(3) '((97)) '(88)))))
  (and (not (fn-scc-octet-listp (list '((97)) '(88))))
       (not (integerp '(3))) (integerp 256)
       (equal carry (fn-scs-summary (fn-cect-remote-entry '(3) '((97)) '(88))))
       (not (fn-cect-remote-carry-lawp '(3) 256 '((97)) '(88) carry)))))
;@hypothesis-removal fn-cecm-remote-ack-retains-exact-carry new-ack-scalar
(assert-event
 (let ((carry (fn-scs-summary (fn-cect-remote-entry 255 '((97)) '(88)))))
  (and (not (fn-scc-octet-listp (list '((97)) '(88))))
       (integerp 255) (not (integerp '(3)))
       (equal carry (fn-scs-summary (fn-cect-remote-entry 255 '((97)) '(88))))
       (not (fn-cect-remote-carry-lawp 255 '(3) '((97)) '(88) carry)))))
;@hypothesis-removal fn-cecm-remote-ack-retains-exact-carry exact-old-root-carry
(assert-event
 (let ((bad '(999 nil nil)))
  (and (not (fn-scc-octet-listp (list '((97)) '(88))))
       (integerp 255) (integerp 256)
       (not (equal bad (fn-scs-summary (fn-cect-remote-entry 255 '((97)) '(88)))))
       (not (fn-cect-remote-carry-lawp 255 256 '((97)) '(88) bad)))))

(defun fn-cect-finish (cp op)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((metadata (fn-cpmm-annotation cp))
        (cursor (fn-cept-run (fn-cp-nth 1 (fn-cep-begin cp op metadata)) 20)))
  (fn-cec-local-preflight cp op metadata cursor)))
; Complete actual carried results from one selected decision. No whole-table
; summary executes in the runtime producer; the test compares its proof oracle.
;@mutation-witness fn-cec-register-complete-carried-result
(assert-event
 (let* ((op '(:register (99) (6) (9) 0 0 5)) (one (fn-cect-finish *cect-cp* op)))
  (and (equal (car one) :ok) (equal (fn-cp-nth 1 one) (fn-cp-apply *cect-cp* op))
       (equal (fn-cp-nth 2 one) (fn-cpmm-annotation (fn-cp-nth 1 one))))))
;@mutation-witness fn-cec-rebase-complete-carried-result
(assert-event
 (let* ((op '(:rebase (2) (6) (10) 0 0 5)) (one (fn-cect-finish *cect-cp* op)))
  (and (equal (car one) :ok) (equal (fn-cp-nth 1 one) (fn-cp-apply *cect-cp* op))
       (equal (fn-cp-nth 2 one) (fn-cpmm-annotation (fn-cp-nth 1 one))))))
;@mutation-witness fn-cec-ack-complete-carried-result
(assert-event
 (let ((one (fn-cect-finish *cect-cp* *cect-ack*)))
  (and (equal (car one) :ok) (equal (fn-cp-nth 1 one) (fn-cp-apply *cect-cp* *cect-ack*))
       (equal (fn-cp-nth 2 one) (fn-cpmm-annotation (fn-cp-nth 1 one))))))
;@mutation-witness fn-cec-unregister-complete-carried-result
(assert-event
 (let ((one (fn-cect-finish *cect-cp* *cect-remove*)))
  (and (equal (car one) :ok) (equal (fn-cp-nth 1 one) (fn-cp-apply *cect-cp* *cect-remove*))
       (equal (fn-cp-nth 2 one) (fn-cpmm-annotation (fn-cp-nth 1 one))))))
;@mutation-witness fn-cec-no-op-never-proposed-as-a-durable-ack
(assert-event
 (equal (fn-cect-finish *cect-cp*
           (list :ack (fn-cp-cursor '(10) '(11) '(2) '(6) '(9) 0 0 3 0)))
        '(:refused :operation)))
;@mutation-witness fn-cec-incomplete-and-old-metadata-remain-unavailable
(assert-event
 (and (equal (fn-cec-finish-local *cect-cp* *cect-remove* (fn-cpm-account4 *cect-meta*) nil)
              '(:refused :consumer-metadata-unavailable))
      (equal (fn-cec-finish-local *cect-cp* *cect-remove* *cect-meta* nil)
              '(:refused :consumer-preparation-incomplete))))
