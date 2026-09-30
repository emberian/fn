(in-package "ACL2")
(include-book "../../books/consumer-authority-carried-result-model")
(local (include-book "consumer-progress-metadata-tests"))
(local (include-book "../../books/consumer-account-auth"))

(defun fn-carfct-next (previous txid op)
 (declare (xargs :guard t))
 (let ((cp (fn-cp-nth 1 previous)))
  (fn-carfc-authority-step cp (fn-caammt-event cp txid op)
                            (fn-cp-nth 3 cp) (fn-cp-nth 4 previous))))
(defun fn-carfct-fullp (result)
 (declare (xargs :guard t :verify-guards nil))
 (and (eq (fn-cp-nth 0 result) :ok)
      (equal (fn-cp-nth 4 result) (fn-cpmm-annotation (fn-cp-nth 1 result)))
      (if (fn-cp-nth 2 result)
          (and (equal (fn-cp-nth 3 result) (fn-cp-nth 3 (fn-cp-nth 1 result)))
               (equal (fn-cp-nth 5 result) (fn-scs-summary (fn-cp-nth 2 result))))
        (and (not (fn-cp-nth 3 result)) (not (fn-cp-nth 5 result))))))
(defconst *carfct-seed* (fn-carfc-result (car *cpmm-seed*) nil nil (cadr *cpmm-seed*) nil))
(defconst *carfct-begin* (fn-carfct-next *carfct-seed* 1 *caammt-begin-op*))
(defconst *carfct-row* (fn-carfct-next *carfct-begin* 2 *caammt-row-op*))
(defconst *carfct-seal* (fn-carfct-next *carfct-row* 3 *caammt-seal-op*))
(defconst *carfct-prepare* (fn-carfct-next *carfct-seal* 4 '(:authority-prepare (65) 0)))
(defconst *carfct-fence* (fn-carfct-next *carfct-prepare* 5 *caammt-fence-op*))
;@mutation-witness fn-carfc-actual-create-retains-six-field-publication
(assert-event
 (and (fn-carfct-fullp *carfct-begin*) (fn-carfct-fullp *carfct-row*)
      (fn-carfct-fullp *carfct-seal*) (fn-carfct-fullp *carfct-prepare*)
      (fn-carfct-fullp *carfct-fence*)
      (equal (fn-cp-nth 1 *carfct-fence*) (fn-caammt-cp *cpmm-fence*))
      (equal (fn-cp-nth 4 *carfct-fence*) (fn-cp-nth 1 *cpmm-fence*))
      (equal (fn-cp-nth 5 *carfct-fence*) (fn-cp-nth 2 *cpmm-fence*))
      (equal (fn-cp-nth 3 *carfct-fence*) 5)))
(defconst *carfct-delete-begin* (fn-carfct-next *carfct-fence* 6 '(:authority-begin (66) 1 3 7)))
(defconst *carfct-tombstone* (fn-carfct-next *carfct-delete-begin* 7 *cpmst-tombstone-op*))
(defconst *carfct-delete-seal* (fn-carfct-next *carfct-tombstone* 8
                               (fn-caammt-final-op (fn-cp-nth 1 *carfct-tombstone*) :authority-seal)))
(defconst *carfct-delete-prepare* (fn-carfct-next *carfct-delete-seal* 9 '(:authority-prepare (66) 1)))
(defconst *carfct-delete-fence* (fn-carfct-next *carfct-delete-prepare* 10
                                (fn-caammt-final-op (fn-cp-nth 1 *carfct-delete-prepare*) :authority-fence)))
(defconst *carfct-recreate-begin* (fn-carfct-next *carfct-delete-fence* 11 '(:authority-begin (67) 2 8 7)))
(defconst *carfct-recreate-row* (fn-carfct-next *carfct-recreate-begin* 12 *cpmst-recreate-op*))
(defconst *carfct-recreate-seal* (fn-carfct-next *carfct-recreate-row* 13
                                 (fn-caammt-final-op (fn-cp-nth 1 *carfct-recreate-row*) :authority-seal)))
(defconst *carfct-recreate-prepare* (fn-carfct-next *carfct-recreate-seal* 14 '(:authority-prepare (67) 2)))
(defconst *carfct-recreate-fence* (fn-carfct-next *carfct-recreate-prepare* 15
                                  (fn-caammt-final-op (fn-cp-nth 1 *carfct-recreate-prepare*) :authority-fence)))
;@mutation-witness fn-carfc-actual-delete-tombstone-recreate-retains-six-field-publication
(assert-event
 (let* ((original (car (fn-cp-nth 4 (fn-cp-nth 6 (fn-cp-nth 1 *carfct-fence*)))))
        (deleted (car (fn-cp-nth 4 (fn-cp-nth 6 (fn-cp-nth 1 *carfct-delete-fence*)))))
        (recreated (car (fn-cp-nth 4 (fn-cp-nth 6 (fn-cp-nth 1 *carfct-recreate-fence*))))))
  (and (fn-carfct-fullp *carfct-delete-begin*) (fn-carfct-fullp *carfct-tombstone*)
       (fn-carfct-fullp *carfct-delete-seal*) (fn-carfct-fullp *carfct-delete-prepare*)
       (fn-carfct-fullp *carfct-delete-fence*) (fn-carfct-fullp *carfct-recreate-begin*)
       (fn-carfct-fullp *carfct-recreate-row*) (fn-carfct-fullp *carfct-recreate-seal*)
       (fn-carfct-fullp *carfct-recreate-prepare*) (fn-carfct-fullp *carfct-recreate-fence*)
       (equal (fn-cp-nth 2 original) (fn-cp-nth 2 deleted))
       (not (fn-cp-nth 3 deleted))
       (not (equal (fn-cp-nth 2 original) (fn-cp-nth 2 recreated)))
       (equal (fn-cp-creation-coordinate (fn-cp-nth 2 recreated)) 12)
       (equal (fn-cp-nth 3 *carfct-delete-fence*) 10)
       (equal (fn-cp-nth 3 *carfct-recreate-fence*) 15))))
;@mutation-witness fn-carfc-config-companion-retains-metadata-and-no-new-root
(assert-event
 (let* ((cp (fn-cp-nth 1 *carfct-fence*)) (m (fn-cp-nth 4 *carfct-fence*))
        (old (fn-cpm-config-preflight cp m)) (result (fn-carfc-config-step cp m)))
  (and (eq (fn-cp-nth 0 result) :ok)
       (equal (fn-cp-nth 1 result) (fn-cp-nth 1 old))
       (equal (fn-cp-nth 4 result) (fn-cp-nth 2 old))
       (equal (fn-cp-nth 4 result) (fn-cpmm-annotation (fn-cp-nth 1 result)))
       (not (fn-cp-nth 2 result)) (not (fn-cp-nth 3 result)) (not (fn-cp-nth 5 result)))))
;@mutation-witness fn-carfc-old-metadata-and-wrong-sequence-never-create-ready-result
(assert-event
 (and (equal (fn-carfc-authority-step (car *cpmm-seed*)
               (fn-caammt-event (car *cpmm-seed*) 1 *caammt-begin-op*) 0
               (fn-cpm-account4 (cadr *cpmm-seed*)))
             '(:refused :consumer-metadata-unavailable))
      (equal (fn-carfc-authority-step (car *cpmm-seed*)
               (fn-caammt-event (car *cpmm-seed*) 1 *caammt-begin-op*) 1 (cadr *cpmm-seed*))
             '(:refused :sequence))))
;@mutation-witness fn-carfc-config-exhaustion-keeps-original-refusal
(assert-event
 (let* ((cp (fn-cp-nth 1 *carfct-fence*))
        (bad (update-nth 6 (update-nth 1 *fn-cbor-max-uint* (fn-cp-nth 6 cp)) cp)))
  (equal (fn-carfc-config-step bad (fn-cpmm-annotation bad))
         '(:refused :authority-revision-exhausted))))
;@mutation-witness fn-carfc-actual-fence-config-publication-separates-namespace-and-revision
; Actual authority fence, actual config decision and actual current-publication
; accessor. This is not an owner STATE collector or durable I/O observation.
; The namespace is forty octets and the revision is scalar, so swapped slots
; affirmatively fail rather than passing on coincidentally equal values.
(assert-event
 (let* ((cp (fn-cp-nth 1 *carfct-fence*))
        (a (fn-cp-nth 6 cp))
        (root (fn-cp-nth 2 *carfct-fence*))
        (pub (list :ready 7 (fn-cp-nth 3 a) (fn-cp-nth 1 a) 5 root))
        (swapped (list :ready 7 (fn-cp-nth 1 a) (fn-cp-nth 3 a) 5 root))
        (configured (fn-carfc-config-step cp (fn-cp-nth 4 *carfct-fence*)))
        (nextcp (fn-cp-nth 1 configured)) (nexta (fn-cp-nth 6 nextcp))
        (nextpub (list :ready 7 (fn-cp-nth 3 nexta) (fn-cp-nth 1 nexta) 5 root)))
  (and (fn-cp-authority-namespacep (fn-cp-nth 3 a))
       (fn-cp-uintp (fn-cp-nth 1 a))
       (not (equal (fn-cp-nth 1 a) (fn-cp-nth 3 a)))
       (fn-cra-availablep cp 7 5 pub)
       (not (fn-cra-availablep cp 7 5 swapped))
       (eq (fn-cp-nth 0 configured) :ok)
       (equal (fn-cp-nth 3 nexta) (fn-cp-nth 3 a))
       (equal (fn-cp-nth 1 nexta) (1+ (fn-cp-nth 1 a)))
       (not (fn-cra-availablep nextcp 7 5 pub))
       (fn-cra-availablep nextcp 7 5 nextpub)
       (equal (fn-cp-nth 5 nextpub) root)
       (not (fn-cp-nth 2 configured)))))
