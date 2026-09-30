(in-package "ACL2")
(include-book "../../books/consumer-account-candidate-model")

(defconst *cadt-secret* (fn-authsec-verifier
                       (make-list 16 :initial-element 0)
                       (make-list 32 :initial-element 1)
                       (make-list 32 :initial-element 2)
                       (make-list 32 :initial-element 3)))
(defconst *cadt-a* (fn-auth-make-cred '(97) (make-list 32 :initial-element 4) *cadt-secret* t))
(defconst *cadt-b* (fn-auth-make-cred '(98) (make-list 32 :initial-element 5) *cadt-secret* nil))
(defconst *cadt-b-later* (fn-auth-make-cred '(98) (make-list 32 :initial-element 6) *cadt-secret* t))

; Test-only driver executes the actual tick. Fuel is a witness, not a data cap
; or a served scheduling policy. The production driver yields between ticks.
(defun fn-cadt-complete (s fuel)
 (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel) '(:refused :test-fuel)
  (let ((one (fn-cad-tick s)))
   (if (eq (fn-cp-nth 0 one) :yield)
       (fn-cadt-complete (fn-cp-nth 1 one) (1- fuel)) one))))
(defun fn-cadt-feed (s credential)
 (declare (xargs :guard t :verify-guards nil))
 (let ((one (fn-cad-feed s credential)))
  (if (eq (fn-cp-nth 0 one) :yield)
      (fn-cadt-complete (fn-cp-nth 1 one) 20) one)))
(defconst *cadt-first* (fn-cp-nth 1 (fn-cadt-feed (fn-cad-initial 7) *cadt-b*)))
(defconst *cadt-second* (fn-cp-nth 1 (fn-cadt-feed *cadt-first* *cadt-a*)))
(defconst *cadt-third* (fn-cp-nth 1 (fn-cadt-feed *cadt-second* *cadt-b-later*)))
(defconst *cadt-seek* (fn-cp-nth 1 (fn-cad-feed *cadt-second* *cadt-b-later*)))
(defconst *cadt-match* (fn-cp-nth 1 (fn-cad-tick *cadt-seek*)))
(defconst *cadt-rebuild*
 (fn-cad-state :rebuild nil nil nil nil (list *cadt-a*) nil (list *cadt-b*) nil 7))

;@positive-witness fn-cadm-actual-tick-preserves-complete-denotation
(assert-event
 (let ((s *cadt-seek*))
  (and (fn-cadm-sourcep s)
       (member-eq (fn-cp-nth 0 (fn-cad-tick s)) '(:yield :ready))
       (equal (fn-cadm-denotation (fn-cp-nth 1 (fn-cad-tick s)))
              (fn-cadm-denotation s)))))
;@corrupted-state-witness fn-cadm-actual-tick-preserves-complete-denotation omitted=sourcep
(assert-event
 (let ((bad (update-nth 1 :unknown *cadt-seek*)))
  (and (not (fn-cadm-sourcep bad))
       (not (and (member-eq (fn-cp-nth 0 (fn-cad-tick bad)) '(:yield :ready))
                 (equal (fn-cadm-denotation (fn-cp-nth 1 (fn-cad-tick bad)))
                        (fn-cadm-denotation bad)))))))

;@positive-witness fn-cadm-actual-ready-is-the-complete-candidate
(assert-event
 (let ((s *cadt-match*))
  (and (fn-cadm-sourcep s)
       (eq (fn-cp-nth 0 (fn-cad-tick s)) :ready)
       (equal (fn-cp-nth 2 (fn-cp-nth 1 (fn-cad-tick s))) (fn-cadm-denotation s)))))
;@corrupted-state-witness fn-cadm-actual-ready-is-the-complete-candidate omitted=sourcep
(assert-event
 (let ((bad (update-nth 2 nil *cadt-match*)))
  (and (not (fn-cadm-sourcep bad))
       (eq (fn-cp-nth 0 (fn-cad-tick bad)) :ready)
       (not (equal (fn-cp-nth 2 (fn-cp-nth 1 (fn-cad-tick bad))) (fn-cadm-denotation bad))))))
;@hyp-removal-witness fn-cadm-actual-ready-is-the-complete-candidate omitted=ready
(assert-event
 (let ((s *cadt-rebuild*))
  (and (fn-cadm-sourcep s)
       (not (eq (fn-cp-nth 0 (fn-cad-tick s)) :ready))
       (not (equal (fn-cp-nth 2 (fn-cp-nth 1 (fn-cad-tick s))) (fn-cadm-denotation s))))))

;@mutation-witness fn-cad-actual-input-order-and-first-credential
(assert-event
 (and (equal (fn-cp-nth 2 *cadt-third*) (list *cadt-a* *cadt-b*))
      (not (equal *cadt-b* *cadt-b-later*))
      (equal (fn-auth-find-cred '(98) (fn-cp-nth 2 *cadt-third*))
             (fn-auth-find-cred '(98) (list *cadt-b* *cadt-a* *cadt-b-later*)))
      (equal (fn-cp-nth 3 *cadt-third*) (fn-cp-nth 3 *cadt-second*))
      (equal (fn-cp-nth 10 *cadt-third*) 7)))
;@mutation-witness fn-cad-feed-refuses-existing-credential-domain-violation
(assert-event
 (and (equal (fn-cad-feed (fn-cad-initial 7)
                         (update-nth 1 (make-list 65 :initial-element 97) *cadt-a*))
             '(:refused :candidate-credential))
      (equal (fn-cad-feed *cadt-seek* *cadt-a*) '(:refused :candidate-credential))))

; Actual row operation retains all credential fields; encode/decode charges
; remain the existing FNCE grammar, not a host-constructed authority record.
;@mutation-witness fn-cad-selected-event-roundtrips-exact-credential
(assert-event
 (let* ((operation (fn-cad-row-operation '(65) 0 *cadt-b* 3))
        (event (fn-cp-nth 1 (fn-cad-authority-event 1 3 0 (list :operation operation t)))))
  (and (fn-cac-eventp event)
       (equal (fn-caa-row-credential operation) *cadt-b*)
       (equal (fn-cac-decode-exact (fn-cac-encode event)) (list :ok event))
       (equal (fn-cac-event-charge event) (len (fn-cac-encode event))))))
