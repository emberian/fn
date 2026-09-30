(in-package "ACL2")
(include-book "../../books/incoming-authority-freshness")
(local (include-book "consumer-authority-carried-result-tests"))

(local
 (defun fn-iaft-canonical (cp count)
  (list :ready 7 count nil nil cp nil 0 0 nil)))
(local
 (defun fn-iaft-pub (result fence)
  (let ((a (fn-cp-nth 6 (fn-cp-nth 1 result))))
   (list :ready 7 (fn-cp-nth 3 a) (fn-cp-nth 1 a) fence (fn-cp-nth 2 result)))))
(local (defconst *iaft-intent* (make-list 32 :initial-element 19)))
(local (defconst *iaft-cp* (fn-cp-nth 1 *carfct-fence*)))
(local (defconst *iaft-canonical* (fn-iaft-canonical *iaft-cp* 5)))
(local (defconst *iaft-pub* (fn-iaft-pub *carfct-fence* 5)))
(local
 (defconst *iaft-saved*
  (list :incoming-freshness :awaiting-query '(:incoming 0) 7 *iaft-intent* 9
        (fn-cp-nth 3 (fn-cp-nth 6 *iaft-cp*))
        (fn-cp-nth 1 (fn-cp-nth 6 *iaft-cp*)) 5
        (fn-cp-nth 2 *carfct-fence*) '(:retained-original-input) nil)))

;@positive-witness fn-iaf-fixed-octets-match-is-exact
(assert-event (and (fn-iaf-octets= 32 *iaft-intent* *iaft-intent*)
                   (equal *iaft-intent* *iaft-intent*)))
;@hypothesis-removal fn-iaf-fixed-octets-match-is-exact
(assert-event (and (not (fn-iaf-octets= 1 '(0) '(1))) (not (equal '(0) '(1)))))
;@positive-witness fn-iaf-available-uses-canonical-current-publication
(assert-event
 (and (eq (fn-iaf-authority-status 7 9 5 *iaft-canonical* *iaft-pub*) :authority-available)
      (equal 7 (fn-cp-nth 1 *iaft-canonical*))
      (equal 5 (fn-cp-nth 2 *iaft-canonical*))
      (fn-cra-availablep *iaft-cp* 7 5 *iaft-pub*)
      (eq (fn-iaf-compare-current *iaft-saved* '(:incoming 0) 7 *iaft-intent* 9
                                  *iaft-canonical* *iaft-pub*) :authority-current)))
;@hypothesis-removal fn-iaf-available-uses-canonical-current-publication
(assert-event
 (and (not (eq (fn-iaf-authority-status 8 9 5 *iaft-canonical* *iaft-pub*) :authority-available))
      (not (equal 8 (fn-cp-nth 1 *iaft-canonical*)))
      (not (fn-cra-availablep *iaft-cp* 8 5 *iaft-pub*))))
;@positive-witness fn-iaf-current-refuses-changed-configuration
(assert-event
 (and (not (equal 10 (fn-cp-nth 5 *iaft-saved*)))
      (eq (fn-iaf-compare-current *iaft-saved* '(:incoming 0) 7 *iaft-intent* 10
                                  *iaft-canonical* *iaft-pub*) :recapture-required)))
;@hypothesis-removal fn-iaf-current-refuses-changed-configuration
(assert-event
 (and (equal 9 (fn-cp-nth 5 *iaft-saved*))
      (not (eq (fn-iaf-compare-current *iaft-saved* '(:incoming 0) 7 *iaft-intent* 9
                                       *iaft-canonical* *iaft-pub*) :recapture-required))))
; Actual config publication changes revision while retaining namespace/root.
;@positive-witness fn-iaf-current-refuses-changed-authority
(assert-event
 (let* ((result (fn-carfc-config-step *iaft-cp* (fn-cp-nth 4 *carfct-fence*)))
        (nextcp (fn-cp-nth 1 result)) (a (fn-cp-nth 6 nextcp))
        (canonical (fn-iaft-canonical nextcp 6))
        (pub (list :ready 7 (fn-cp-nth 3 a) (fn-cp-nth 1 a) 5 (fn-cp-nth 5 *iaft-pub*))))
  (and (eq (fn-cp-nth 0 result) :ok)
       (not (equal (fn-cp-nth 1 a) (fn-cp-nth 7 *iaft-saved*)))
       (eq (fn-iaf-authority-status 7 10 6 canonical pub) :authority-available)
       (eq (fn-iaf-authority-status 7 10 6 canonical *iaft-pub*) :authority-unavailable)
       (eq (fn-iaf-compare-current *iaft-saved* '(:incoming 0) 7 *iaft-intent* 9 canonical pub)
           :recapture-required))))
;@hypothesis-removal fn-iaf-current-refuses-changed-authority
(assert-event
 (and (equal (fn-cp-nth 1 (fn-cp-nth 6 *iaft-cp*)) (fn-cp-nth 7 *iaft-saved*))
      (not (eq (fn-iaf-compare-current *iaft-saved* '(:incoming 0) 7 *iaft-intent* 9
                                       *iaft-canonical* *iaft-pub*) :recapture-required))))
; Actual account deletion/recreation changes publication, not incoming intent.
;@mutation-witness incoming-authority-publication-interleaving
(assert-event
 (let* ((nextcp (fn-cp-nth 1 *carfct-delete-fence*))
        (canonical (fn-iaft-canonical nextcp 10))
        (pub (fn-iaft-pub *carfct-delete-fence* 10)))
  (and (eq (fn-iaf-authority-status 7 9 10 canonical pub) :authority-available)
       (eq (fn-iaf-compare-current *iaft-saved* '(:incoming 0) 7 *iaft-intent* 9 canonical pub)
           :recapture-required)
       (equal (fn-cp-nth 2 *iaft-saved*) '(:incoming 0))
       (equal (fn-cp-nth 10 *iaft-saved*) '(:retained-original-input)))))
;@corrupted-state-witness incoming-authority-swapped-publication
(assert-event
 (let ((swapped (list :ready 7 (fn-cp-nth 3 *iaft-pub*) (fn-cp-nth 2 *iaft-pub*)
                      5 (fn-cp-nth 5 *iaft-pub*))))
  (eq (fn-iaf-authority-status 7 9 5 *iaft-canonical* swapped) :authority-unavailable)))
