(in-package "ACL2")
(include-book "../../books/consumer-account-metadata-step")
(local (include-book "consumer-account-metadata-tests"))

(defun fn-camst-hypotheses (s event metadata installed)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((a (fn-cp-nth 6 s)) (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
        (kind (fn-cp-nth 0 (fn-cp-nth 4 event)))
        (one (car (mv-list 3 (fn-caac-step s event metadata)))))
  (list (fn-caam-authority-sizep a)
        (equal metadata (fn-caam-annotation s))
        (implies (member-eq kind '(:authority-row :authority-tombstone))
          (and (fn-caps-merge-relp p installed)
               (fn-cais-triep (fn-cp-nth 2 (fn-cp-nth 5 prep)))))
        (implies (equal kind :authority-prepare) (fn-caar-preparation-relp prep))
        (equal (car one) :ok))))
(defun fn-camst-conclusion (s event metadata)
 (declare (xargs :guard t :verify-guards nil))
 (mv-let (one nm rootcarry) (fn-caac-step s event metadata)
  (declare (ignore rootcarry))
  (fn-caam-correspondsp (fn-cp-nth 1 one) nm)))
(defun fn-camst-positive (s event metadata installed)
 (declare (xargs :guard t :verify-guards nil))
 (and (equal (fn-camst-hypotheses s event metadata installed) '(t t t t t))
      (fn-camst-conclusion s event metadata)))

;@positive fn-cams-actual-authority-step-maintains-full-metadata
(assert-event
 (fn-camst-positive (car *caammt-seed*)
   (fn-caammt-event (car *caammt-seed*) 1 *caammt-begin-op*)
   (cadr *caammt-seed*) nil))
;@mutation-witness fn-cams-actual-stage-seal-prepare-fence
(assert-event
 (and
  (fn-camst-positive (fn-caammt-cp *caammt-begin*) *caammt-row-event*
                    (cadr *caammt-begin*) nil)
  (fn-camst-positive (fn-caammt-cp *caammt-row*)
   (fn-caammt-event (fn-caammt-cp *caammt-row*) 3 *caammt-seal-op*)
   (cadr *caammt-row*) nil)
  (fn-camst-positive (fn-caammt-cp *caammt-seal*)
   (fn-caammt-event (fn-caammt-cp *caammt-seal*) 4 '(:authority-prepare (65) 0))
   (cadr *caammt-seal*) nil)
  (fn-camst-positive (fn-caammt-cp *caammt-prepare*)
   (fn-caammt-event (fn-caammt-cp *caammt-prepare*) 5 *caammt-fence-op*)
   (cadr *caammt-prepare*) nil)))

; Every removal below is a deliberately corrupted maintained state/input.
; It asserts all four other literal premises, not merely a failed conclusion.
 ;@hypothesis-removal fn-cams-actual-authority-step-maintains-full-metadata authority-size
(assert-event
 (let* ((original (fn-caammt-cp *caammt-begin*))
        (s (update-nth 6 (update-nth 2 '(bad) (fn-cp-nth 6 original)) original))
        (m (fn-caam-annotation s)))
  (and (equal (fn-camst-hypotheses s *caammt-row-event* m nil) '(nil t t t t))
       (not (fn-camst-conclusion s *caammt-row-event* m)))))
;@hypothesis-removal fn-cams-actual-authority-step-maintains-full-metadata old-metadata
(assert-event
 (let* ((s (fn-caammt-cp *caammt-begin*)) (m (update-nth 1 nil (cadr *caammt-begin*))))
  (and (equal (fn-camst-hypotheses s *caammt-row-event* m nil) '(t nil t t t))
       (not (fn-camst-conclusion s *caammt-row-event* m)))))
;@hypothesis-removal fn-cams-actual-authority-step-maintains-full-metadata stage-relation
(assert-event
 (let* ((original (fn-caammt-cp *caammt-begin*))
        (a (fn-cp-nth 6 original)) (p (fn-cp-nth 5 a))
        (prep (fn-cp-nth 5 p)) (root (fn-cp-nth 5 prep))
        (s (update-nth 6 (update-nth 5 (update-nth 5
             (update-nth 5 (update-nth 2 (list (cons '(bad) nil)) root) prep) p) a) original))
        (m (fn-caam-annotation s)))
  (and (equal (fn-camst-hypotheses s *caammt-row-event* m nil) '(t t nil t t))
       (not (fn-camst-conclusion s *caammt-row-event* m)))))
;@hypothesis-removal fn-cams-actual-authority-step-maintains-full-metadata prepare-relation
(assert-event
 (let* ((original (fn-caammt-cp *caammt-seal*))
        (a (fn-cp-nth 6 original)) (p (fn-cp-nth 5 a))
        (prep (fn-cp-nth 5 p)) (root (fn-cp-nth 5 prep))
        (row (car (fn-cp-nth 3 prep)))
        (index (fn-cai-put-octets (fn-cp-nth 1 row) (list :account-binding row '(bad))
                                 (fn-cp-nth 2 root)))
        (s (update-nth 6 (update-nth 5 (update-nth 5
             (update-nth 5 (update-nth 2 index root) prep) p) a) original))
        (event (fn-caammt-event s 4 '(:authority-prepare (65) 0)))
        (m (fn-caam-annotation s)))
  (and (equal (fn-camst-hypotheses s event m nil) '(t t t nil t))
       (not (fn-camst-conclusion s event m)))))
;@hypothesis-removal fn-cams-actual-authority-step-maintains-full-metadata successful-decision
(assert-event
 (let* ((s (fn-caammt-cp *caammt-begin*))
        (event (update-nth 1 99 *caammt-row-event*)) (m (cadr *caammt-begin*)))
  (and (equal (fn-camst-hypotheses s event m nil) '(t t t t nil))
       (not (fn-camst-conclusion s event m)))))

(defun fn-camst-root-hypotheses (s event metadata)
 (declare (xargs :guard t :verify-guards nil))
 (list (fn-caam-authority-sizep (fn-cp-nth 6 s))
       (equal metadata (fn-caam-annotation s))
       (equal (fn-cp-nth 0 (fn-cp-nth 4 event)) :authority-fence)
       (equal (car (car (mv-list 3 (fn-caac-step s event metadata)))) :ok)))
(defun fn-camst-root-conclusion (s event metadata)
 (declare (xargs :guard t :verify-guards nil))
 (mv-let (one nm rootcarry) (fn-caac-step s event metadata)
  (declare (ignore nm))
  (equal rootcarry (fn-scs-summary (fn-cp-nth 2 one)))))
(defconst *camst-fence-event*
 (fn-caammt-event (fn-caammt-cp *caammt-prepare*) 5 *caammt-fence-op*))
;@positive fn-cams-actual-fence-publishes-exact-root-carry
(assert-event
 (and (equal (fn-camst-root-hypotheses (fn-caammt-cp *caammt-prepare*)
             *camst-fence-event* (cadr *caammt-prepare*)) '(t t t t))
      (fn-camst-root-conclusion (fn-caammt-cp *caammt-prepare*)
             *camst-fence-event* (cadr *caammt-prepare*))))
; Corrupted-state witnesses below preserve all other literal premises.
;@hypothesis-removal fn-cams-actual-fence-publishes-exact-root-carry authority-size
(assert-event
 (let* ((original (fn-caammt-cp *caammt-prepare*))
        (a (fn-cp-nth 6 original)) (p (fn-cp-nth 5 a))
        (prep (fn-cp-nth 5 p)) (root (fn-cp-nth 5 prep))
        (s (update-nth 6 (update-nth 5 (update-nth 5
             (update-nth 5 (update-nth 1 '(bad) root) prep) p) a) original))
        (m (fn-caam-annotation s)))
  (and (equal (fn-camst-root-hypotheses s *camst-fence-event* m) '(nil t t t))
       (not (fn-camst-root-conclusion s *camst-fence-event* m)))))
;@hypothesis-removal fn-cams-actual-fence-publishes-exact-root-carry old-metadata
(assert-event
 (let* ((s (fn-caammt-cp *caammt-prepare*))
        (m (update-nth 3 (update-nth 4 nil (fn-cp-nth 3 (cadr *caammt-prepare*)))
                       (cadr *caammt-prepare*))))
  (and (equal (fn-camst-root-hypotheses s *camst-fence-event* m) '(t nil t t))
       (not (fn-camst-root-conclusion s *camst-fence-event* m)))))
;@hypothesis-removal fn-cams-actual-fence-publishes-exact-root-carry fence-operation
(assert-event
 (let* ((s (fn-caammt-cp *caammt-seal*))
        (event (fn-caammt-event s 4 '(:authority-prepare (65) 0)))
        (m (cadr *caammt-seal*)))
  (and (equal (fn-camst-root-hypotheses s event m) '(t t nil t))
       (not (fn-camst-root-conclusion s event m)))))
;@hypothesis-removal fn-cams-actual-fence-publishes-exact-root-carry successful-decision
(assert-event
 (let* ((s (fn-caammt-cp *caammt-prepare*))
        (event (update-nth 1 99 *camst-fence-event*)) (m (cadr *caammt-prepare*)))
  (and (equal (fn-camst-root-hypotheses s event m) '(t t t nil))
       (not (fn-camst-root-conclusion s event m)))))

; Actual same-pass mutation lifecycle: deletion retains the creation token
; in a tombstone; recreation gets a distinct persisted-stage token. No host
; authority or durable/native qualification is claimed by these executions.
(defconst *camst-delete-begin*
 (fn-caammt-next *caammt-fence* 6 '(:authority-begin (66) 1 3 7)))
(defconst *camst-tombstone-op* '(:authority-tombstone (66) 1 (97) 2))
(defconst *camst-tombstone*
 (fn-caammt-next *camst-delete-begin* 7 *camst-tombstone-op*))
(defconst *camst-delete-seal*
 (fn-caammt-next *camst-tombstone* 8
  (fn-caammt-final-op (fn-caammt-cp *camst-tombstone*) :authority-seal)))
(defconst *camst-delete-prepare*
 (fn-caammt-next *camst-delete-seal* 9 '(:authority-prepare (66) 1)))
(defconst *camst-delete-fence*
 (fn-caammt-next *camst-delete-prepare* 10
  (fn-caammt-final-op (fn-caammt-cp *camst-delete-prepare*) :authority-fence)))
(defconst *camst-recreate-begin*
 (fn-caammt-next *camst-delete-fence* 11 '(:authority-begin (67) 2 8 7)))
(defconst *camst-recreate-op*
 (update-nth 4 12 (update-nth 2 2 (update-nth 1 '(67) *caammt-row-op*))))
(defconst *camst-recreate-row*
 (fn-caammt-next *camst-recreate-begin* 12 *camst-recreate-op*))
(defconst *camst-recreate-seal*
 (fn-caammt-next *camst-recreate-row* 13
  (fn-caammt-final-op (fn-caammt-cp *camst-recreate-row*) :authority-seal)))
(defconst *camst-recreate-prepare*
 (fn-caammt-next *camst-recreate-seal* 14 '(:authority-prepare (67) 2)))
(defconst *camst-recreate-fence*
 (fn-caammt-next *camst-recreate-prepare* 15
  (fn-caammt-final-op (fn-caammt-cp *camst-recreate-prepare*) :authority-fence)))
;@mutation-witness fn-cams-actual-tombstone-and-recreation
(assert-event
 (let* ((original (car (fn-cp-nth 4 (fn-cp-nth 6 (fn-caammt-cp *caammt-fence*)))))
        (deleted (car (fn-cp-nth 4 (fn-cp-nth 6 (fn-caammt-cp *camst-delete-fence*)))))
        (recreated (car (fn-cp-nth 4 (fn-cp-nth 6 (fn-caammt-cp *camst-recreate-fence*)))))
        (delete-root (fn-cp-nth 2 (car *camst-delete-fence*))))
  (and (fn-caammt-fullp *camst-delete-begin*) (fn-caammt-fullp *camst-tombstone*)
       (fn-caammt-fullp *camst-delete-seal*) (fn-caammt-fullp *camst-delete-prepare*)
       (fn-caammt-fullp *camst-delete-fence*)
       (fn-caammt-fullp *camst-recreate-begin*) (fn-caammt-fullp *camst-recreate-row*)
       (fn-caammt-fullp *camst-recreate-seal*) (fn-caammt-fullp *camst-recreate-prepare*)
       (fn-caammt-fullp *camst-recreate-fence*)
       (equal (fn-cp-nth 2 original) (fn-cp-nth 2 deleted))
       (null (fn-cp-nth 3 deleted)) (null (fn-cp-nth 3 delete-root))
       (not (equal (fn-cp-nth 2 deleted) (fn-cp-nth 2 recreated)))
       (equal (fn-cp-creation-coordinate (fn-cp-nth 2 recreated)) 12)
       (equal (fn-cp-nth 2 *camst-delete-fence*) (fn-scs-summary delete-root))
       (equal (fn-cp-nth 2 *camst-recreate-fence*)
              (fn-scs-summary (fn-cp-nth 2 (car *camst-recreate-fence*)))))))
