(in-package "ACL2")
(include-book "../../books/consumer-account-transaction-driver")
(local (include-book "consumer-account-config-commit-tests"))

(defconst *catdt-input*
 (mv-let (index im)
  (fn-cait-put-octets '(98) (fn-aic-intent 0 2 *bcpt-new*)
                      (fn-aic-intent-carry 0 2) nil nil)
  (fn-aic-state (fn-cad-initial 7) index im nil nil nil nil nil :idle)))
(defun fn-catdt-job (b)
 (declare (xargs :guard t :verify-guards nil))
 (fn-cadd-job :ready '(:test-source) '(65) nil nil nil *catdt-input*
              (list *cadt-b*) nil (list :account-preparation b) 0))
(defconst *catdt-row-selection*
 (fn-catd-next (fn-catdt-job (fn-cp-nth 2 *acjt-begin*))
               (fn-cp-nth 0 *acjt-begin*) 1 2 0 7 1))
(defconst *catdt-after-row*
 (fn-cp-nth 1
  (fn-catd-published (fn-catdt-job (fn-cp-nth 2 *acjt-begin*))
    *catdt-row-selection*
    (list :ok (fn-cp-nth 0 *acjt-row*) nil nil (fn-cp-nth 1 *acjt-row*) nil
              (fn-cp-nth 2 *acjt-row*)) 1)))
(defconst *catdt-binding-selection*
 (fn-catd-next *catdt-after-row* (fn-cp-nth 0 *acjt-row*) 2 3 0 7 2))
;@mutation-witness actual-row-waits-for-paired-binding
(assert-event
 (and (equal (fn-cp-nth 0 (fn-cp-nth 4 (fn-cp-nth 1 *catdt-row-selection*))) :authority-row)
      (null (fn-cp-nth 2 *catdt-row-selection*))
      (equal (fn-cp-nth 8 *catdt-after-row*) (list *cadt-b*))
      (equal *catdt-binding-selection*
             (list :publish (list :consumer-authority 2 3 0
                    (fn-cab-operation '(65) 0 '(98) 0 2 *bcpt-new*)) t))))
;@mutation-witness actual-binding-durable-consumes-exactly-one-candidate
(assert-event
 (let* ((one (fn-catd-published *catdt-after-row* *catdt-binding-selection*
                  (list :ok (fn-cp-nth 0 *acjt-bound*) nil nil
                            (fn-cp-nth 1 *acjt-bound*) nil (fn-cp-nth 2 *acjt-bound*)) 2))
        (job (fn-cp-nth 1 one)))
  (and (eq (fn-cp-nth 0 one) :yield) (null (fn-cp-nth 8 job))
       (equal (fn-catd-preparation job) (fn-cp-nth 2 *acjt-bound*)))))
;@mutation-witness actual-ready-config-selects-sole-c-commit
(assert-event
 (let* ((cp (fn-cp-nth 0 *acjt-prepared*))
        (job (fn-catdt-job (fn-cp-nth 2 *acjt-prepared*)))
        (selection (fn-catd-next job cp 99 99 0 7 (fn-cp-nth 3 cp)))
        (one (fn-catd-published job selection *acjt-final* 5)))
  (and (equal selection (list :configure *acjt-marker*))
       (equal (fn-cp-nth 0 one) :accepted)
       (equal (fn-cp-nth 1 (fn-cp-nth 1 one)) :done))))
;@mutation-witness actual-config-preparation-remains-resumable-e-work
(assert-event
 (let* ((cp (fn-cp-nth 0 *acjt-prepared*))
        (b (update-nth 4 :scan (fn-cp-nth 2 *acjt-prepared*)))
        (one (fn-catd-next (fn-catdt-job b) cp 99 99 0 7 (fn-cp-nth 3 cp))))
  (and (eq (fn-cp-nth 0 one) :publish)
       (equal (fn-cp-nth 4 (fn-cp-nth 1 one)) '(:authority-prepare (65) 0)))))
;@mutation-witness actual-selector-refuses-missing-binding-provenance
(assert-event
 (let* ((job (update-nth 7 (fn-aic-initial 7 nil) *catdt-after-row*))
        (one (fn-catd-next job (fn-cp-nth 0 *acjt-row*) 2 3 0 7 2)))
  (equal one '(:refused :candidate-binding-intent))))

;@corrupted-state begin-records-dense-predecessor-not-event-sequence
; Scalar producer witness only: actual custody of this coordinate is supplied
; by the registered holder/receipt in the owner collector, not this fixture.
(assert-event
 (let* ((job (fn-catdt-job nil))
        (selection '(:publish (:consumer-authority 0 1 0
                                (:authority-begin (65) 0 1 7)) nil))
        (one (fn-catd-published job selection
                (list :ok nil nil nil nil nil nil) 23)))
  (and (equal (fn-cp-nth 0 one) :yield)
       (equal (fn-cp-nth 1 (fn-cp-nth 1 selection)) 0)
       (equal (fn-cp-nth 11 (fn-cp-nth 1 one)) 23))))
;@corrupted-state invalid-dense-predecessor-refuses-published-update
(assert-event
 (equal (fn-catd-published *catdt-after-row* *catdt-binding-selection*
                (list :ok nil nil nil nil nil nil) -1)
        '(:recovery-required :account-decision)))

;@corrupted-state older-unpaired-source-helper-also-keeps-dense-coordinate
(assert-event
 (let* ((job (fn-catdt-job nil))
        (selection '(:publish (:consumer-authority 0 1 0
                                (:authority-begin (65) 0 1 7)) nil))
        (one (fn-cadd-published job selection nil 23)))
  (and (equal (fn-cp-nth 0 one) :yield)
       (equal (fn-cp-nth 11 (fn-cp-nth 1 one)) 23))))
;@corrupted-state older-unpaired-helper-refuses-malformed-coordinate
(assert-event
 (equal (fn-cadd-published *catdt-after-row* *catdt-binding-selection* nil -1)
        '(:recovery-required :account-event-count)))
