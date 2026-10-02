(in-package "ACL2")
(include-book "../../books/consumer-account-input")
(include-book "consumer-account-candidate-tests") ; its fixtures are used by non-local events

(defun fn-aict-complete (s fuel)
 (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel) '(:refused :test-fuel)
  (let ((one (fn-aic-tick s)))
   (if (eq (fn-cp-nth 0 one) :yield)
       (fn-aict-complete (fn-cp-nth 1 one) (1- fuel)) one))))
(defun fn-aict-feed (s credential origin)
 (declare (xargs :guard t :verify-guards nil))
 (let ((one (fn-aic-feed s credential origin)))
  (if (eq (fn-cp-nth 0 one) :yield)
      (fn-aict-complete (fn-cp-nth 1 one) 60) one)))
(defconst *aict-signer* (make-list 32 :initial-element 9))
(defconst *aict-static*
 (fn-cp-nth 1 (fn-aict-feed (fn-aic-initial 7 (list (cons '(98) *aict-signer*))) *cadt-b* 0)))
(defconst *aict-duplicate*
 (fn-cp-nth 1 (fn-aict-feed *aict-static* *cadt-b-later* 1)))
(defconst *aict-delete*
 (fn-cp-nth 1 (fn-aict-feed *aict-duplicate* *cadt-a* 0)))
(defconst *aict-redeemed*
 (fn-cp-nth 1 (fn-aict-feed (fn-aic-initial 7 nil) *cadt-b* 1)))

;@mutation-witness actual-static-signing-and-first-source-intent
(assert-event
 (and (equal (fn-cp-nth 2 (fn-cp-nth 1 *aict-static*)) (list *cadt-b*))
      (equal (fn-cai-get-octets '(98) (fn-cp-nth 2 *aict-static*))
             (fn-aic-intent 0 2 *aict-signer*))
      (equal (fn-cp-nth 2 (fn-cp-nth 1 *aict-duplicate*)) (list *cadt-b*))
      (equal (fn-cp-nth 2 *aict-duplicate*) (fn-cp-nth 2 *aict-static*))
      (equal (fn-cp-nth 3 *aict-duplicate*) (fn-cp-nth 3 *aict-static*))))
;@mutation-witness actual-missing-static-signing-explicit-unbind
(assert-event
 (and (equal (fn-cp-nth 2 (fn-cp-nth 1 *aict-delete*)) (list *cadt-a* *cadt-b*))
      (equal (fn-cai-get-octets '(97) (fn-cp-nth 2 *aict-delete*))
             (fn-aic-intent 0 1 (make-list 32 :initial-element 0)))
      (equal (fn-cai-get-octets '(98) (fn-cp-nth 2 *aict-delete*))
             (fn-aic-intent 0 2 *aict-signer*))))
;@mutation-witness actual-absent-static-redeemed-binding-preserved
(assert-event
 (equal (fn-cai-get-octets '(98) (fn-cp-nth 2 *aict-redeemed*))
        (fn-aic-intent 1 0 (make-list 32 :initial-element 0))))
;@mutation-witness actual-intent-path-carry-produced-with-insertion
(assert-event
 (and (equal (fn-cait-carry (fn-cp-nth 3 *aict-delete*))
             (fn-scs-summary (fn-cp-nth 2 *aict-delete*)))
      (equal (fn-caac-list-carry (fn-cp-nth 3 (fn-cp-nth 1 *aict-delete*)))
             (fn-scs-summary (fn-cp-nth 2 (fn-cp-nth 1 *aict-delete*))))))
;@mutation-witness actual-input-binding-domain-and-reentrant-refusal
(assert-event
 (let* ((bad (fn-aic-initial 7 (list (cons '(98) '(9)))))
        (fed (fn-cp-nth 1 (fn-aic-feed bad *cadt-b* 0))))
  (and (equal (fn-aic-tick fed) '(:refused :account-input-binding))
       (equal (fn-aic-feed fed *cadt-a* 0) '(:refused :account-input-phase))
       (equal (fn-aic-feed bad *cadt-a* 2) '(:refused :account-input-phase)))))
