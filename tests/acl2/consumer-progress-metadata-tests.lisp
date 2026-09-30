(in-package "ACL2")

(include-book "../../books/consumer-progress-metadata")

(local (include-book "consumer-account-metadata-tests"))

(defconst *cpmm-seed* (mv-list 2 (fn-cpm-initial *caammt-bytes32* *caammt-bytes32* 0 32 32)))

(defun fn-cpmmt-next (result txid op)
 (declare (xargs :guard t))
 (let ((cp (fn-caammt-cp result)))
  (mv-list 3 (fn-cpm-authority-step cp (fn-caammt-event cp txid op) (fn-cp-nth 1 result)))))

(defconst *cpmm-begin* (mv-list 3 (fn-cpm-authority-step (car *cpmm-seed*)
 (fn-caammt-event (car *cpmm-seed*) 1 *caammt-begin-op*) (cadr *cpmm-seed*))))

(defconst *cpmm-row* (fn-cpmmt-next *cpmm-begin* 2 *caammt-row-op*))

(defconst *cpmm-seal* (fn-cpmmt-next *cpmm-row* 3 *caammt-seal-op*))

(defconst *cpmm-prepare* (fn-cpmmt-next *cpmm-seal* 4 '(:authority-prepare (65) 0)))

(defconst *cpmm-fence* (fn-cpmmt-next *cpmm-prepare* 5 *caammt-fence-op*))

(defun fn-cpmmt-correspondsp (cp m)
 (declare (xargs :guard t :verify-guards nil))
 (equal m (fn-cpmm-annotation cp)))

(defun fn-cpmmst-hypotheses (s event metadata installed)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((a (fn-cp-nth 6 s)) (p (fn-cp-nth 5 a)) (prep (fn-cp-nth 5 p))
        (kind (fn-cp-nth 0 (fn-cp-nth 4 event)))
        (one (car (mv-list 3 (fn-cpm-authority-step s event metadata)))))
  (list (fn-caam-authority-sizep a)
        (equal metadata (fn-cpmm-annotation s))
        (implies (member-eq kind '(:authority-row :authority-tombstone))
          (and (fn-caps-merge-relp p installed)
               (fn-cais-triep (fn-cp-nth 2 (fn-cp-nth 5 prep)))))
        (implies (equal kind :authority-prepare) (fn-caar-preparation-relp prep))
        (equal (car one) :ok))))

(defun fn-cpmmst-conclusion (s event metadata)
 (declare (xargs :guard t :verify-guards nil))
 (mv-let (one nm rootcarry) (fn-cpm-authority-step s event metadata)
  (declare (ignore rootcarry))
  (fn-cpmmt-correspondsp (fn-cp-nth 1 one) nm)))

(defun fn-cpmmst-positive (s event metadata installed)
 (declare (xargs :guard t :verify-guards nil))
 (and (equal (fn-cpmmst-hypotheses s event metadata installed) '(t t t t t))
      (fn-cpmmst-conclusion s event metadata)))

;@positive fn-cpmm-actual-authority-step-maintains-fixed-five-metadata
(assert-event
 (fn-cpmmst-positive (car *cpmm-seed*)
   (fn-caammt-event (car *cpmm-seed*) 1 *caammt-begin-op*)
   (cadr *cpmm-seed*) nil))

;@mutation-witness fn-cpmm-actual-authority-stage-seal-prepare-fence
(assert-event
 (and
  (fn-cpmmst-positive (fn-caammt-cp *cpmm-begin*) *caammt-row-event*
                    (cadr *cpmm-begin*) nil)
  (fn-cpmmst-positive (fn-caammt-cp *cpmm-row*)
   (fn-caammt-event (fn-caammt-cp *cpmm-row*) 3 *caammt-seal-op*)
   (cadr *cpmm-row*) nil)
  (fn-cpmmst-positive (fn-caammt-cp *cpmm-seal*)
   (fn-caammt-event (fn-caammt-cp *cpmm-seal*) 4 '(:authority-prepare (65) 0))
   (cadr *cpmm-seal*) nil)
  (fn-cpmmst-positive (fn-caammt-cp *cpmm-prepare*)
   (fn-caammt-event (fn-caammt-cp *cpmm-prepare*) 5 *caammt-fence-op*)
   (cadr *cpmm-prepare*) nil)))

;@hypothesis-removal fn-cpmm-actual-authority-step-maintains-fixed-five-metadata authority-size
(assert-event
 (let* ((original (fn-caammt-cp *cpmm-begin*))
        (s (update-nth 6 (update-nth 2 '(bad) (fn-cp-nth 6 original)) original))
        (m (fn-cpmm-annotation s)))
  (and (equal (fn-cpmmst-hypotheses s *caammt-row-event* m nil) '(nil t t t t))
       (not (fn-cpmmst-conclusion s *caammt-row-event* m)))))

;@hypothesis-removal fn-cpmm-actual-authority-step-maintains-fixed-five-metadata old-metadata
(assert-event
 (let* ((s (fn-caammt-cp *cpmm-begin*)) (m (update-nth 1 nil (cadr *cpmm-begin*))))
  (and (equal (fn-cpmmst-hypotheses s *caammt-row-event* m nil) '(t nil t t t))
       (not (fn-cpmmst-conclusion s *caammt-row-event* m)))))

;@hypothesis-removal fn-cpmm-actual-authority-step-maintains-fixed-five-metadata stage-relation
(assert-event
 (let* ((original (fn-caammt-cp *cpmm-begin*))
        (a (fn-cp-nth 6 original)) (p (fn-cp-nth 5 a))
        (prep (fn-cp-nth 5 p)) (root (fn-cp-nth 5 prep))
        (s (update-nth 6 (update-nth 5 (update-nth 5
             (update-nth 5 (update-nth 2 (list (cons '(bad) nil)) root) prep) p) a) original))
        (m (fn-cpmm-annotation s)))
  (and (equal (fn-cpmmst-hypotheses s *caammt-row-event* m nil) '(t t nil t t))
       (not (fn-cpmmst-conclusion s *caammt-row-event* m)))))

;@hypothesis-removal fn-cpmm-actual-authority-step-maintains-fixed-five-metadata prepare-relation
(assert-event
 (let* ((original (fn-caammt-cp *cpmm-seal*))
        (a (fn-cp-nth 6 original)) (p (fn-cp-nth 5 a))
        (prep (fn-cp-nth 5 p)) (root (fn-cp-nth 5 prep))
        (row (car (fn-cp-nth 3 prep)))
        (index (fn-cai-put-octets (fn-cp-nth 1 row) (list :account-binding row '(bad))
                                 (fn-cp-nth 2 root)))
        (s (update-nth 6 (update-nth 5 (update-nth 5
             (update-nth 5 (update-nth 2 index root) prep) p) a) original))
        (event (fn-caammt-event s 4 '(:authority-prepare (65) 0)))
        (m (fn-cpmm-annotation s)))
  (and (equal (fn-cpmmst-hypotheses s event m nil) '(t t t nil t))
       (not (fn-cpmmst-conclusion s event m)))))

;@hypothesis-removal fn-cpmm-actual-authority-step-maintains-fixed-five-metadata successful-decision
(assert-event
 (let* ((s (fn-caammt-cp *cpmm-begin*))
        (event (update-nth 1 99 *caammt-row-event*)) (m (cadr *cpmm-begin*)))
  (and (equal (fn-cpmmst-hypotheses s event m nil) '(t t t t nil))
       (not (fn-cpmmst-conclusion s event m)))))

(defun fn-cpmmct-hypotheses (cp metadata)
 (declare (xargs :guard t :verify-guards nil))
 (list (integerp (fn-cp-nth 3 cp))
       (fn-caam-authority-sizep (fn-cp-nth 6 cp))
       (equal metadata (fn-cpmm-annotation cp))
       (equal (car (fn-cpm-config-preflight cp metadata)) :ok)))

(defun fn-cpmmct-conclusion (cp metadata)
 (declare (xargs :guard t :verify-guards nil))
 (let ((approved (fn-cpm-config-preflight cp metadata)))
  (fn-cpmmt-correspondsp (fn-cp-nth 1 approved) (fn-cp-nth 2 approved))))

;@positive fn-cpmm-config-preflight-maintains-fixed-five-metadata
(assert-event
 (let* ((cp (fn-caammt-cp *cpmm-fence*)) (metadata (cadr *cpmm-fence*))
        (approved (fn-cpm-config-preflight cp metadata))
        (next (fn-cp-nth 1 approved)))
  (and (equal (fn-cpmmct-hypotheses cp metadata) '(t t t t))
       (fn-cpmmct-conclusion cp metadata)
       (equal (fn-cp-nth 1 (fn-cp-nth 6 next))
              (1+ (fn-cp-nth 1 (fn-cp-nth 6 cp))))
       (equal (fn-cp-nth 4 (fn-cp-nth 6 next))
              (fn-cp-nth 4 (fn-cp-nth 6 cp)))
       (not (fn-cp-nth 5 (fn-cp-nth 6 next))))))

;@mutation-witness fn-cpmm-config-aborts-pending-without-adoption
(assert-event
 (let* ((cp (fn-caammt-cp *cpmm-begin*)) (metadata (cadr *cpmm-begin*))
        (approved (fn-cpm-config-preflight cp metadata))
        (next (fn-cp-nth 1 approved)) (nm (fn-cp-nth 2 approved)))
  (and (equal (fn-cpmmct-hypotheses cp metadata) '(t t t t))
       (fn-cpmmct-conclusion cp metadata)
       (fn-cp-nth 5 (fn-cp-nth 6 cp))
       (not (fn-cp-nth 5 (fn-cp-nth 6 next)))
       (not (fn-cp-nth 3 nm))
       (equal (fn-cp-nth 4 (fn-cp-nth 6 next))
              (fn-cp-nth 4 (fn-cp-nth 6 cp))))))

;@hypothesis-removal fn-cpmm-config-preflight-maintains-fixed-five-metadata frontier-scalar
(assert-event
 (let* ((cp (update-nth 3 '(7) (fn-caammt-cp *cpmm-fence*)))
        (m (fn-cpmm-annotation cp)))
  (and (equal (fn-cpmmct-hypotheses cp m) '(nil t t t))
       (not (fn-cpmmct-conclusion cp m)))))

;@hypothesis-removal fn-cpmm-config-preflight-maintains-fixed-five-metadata authority-size
(assert-event
 (let* ((original (fn-caammt-cp *cpmm-fence*))
        (cp (update-nth 6 (update-nth 2 '(bad) (fn-cp-nth 6 original)) original))
        (m (fn-cpmm-annotation cp)))
  (and (equal (fn-cpmmct-hypotheses cp m) '(t nil t t))
       (not (fn-cpmmct-conclusion cp m)))))

;@hypothesis-removal fn-cpmm-config-preflight-maintains-fixed-five-metadata old-metadata
(assert-event
 (let* ((cp (fn-caammt-cp *cpmm-fence*))
        (m (update-nth 1 nil (cadr *cpmm-fence*))))
  (and (equal (fn-cpmmct-hypotheses cp m) '(t t nil t))
       (not (fn-cpmmct-conclusion cp m)))))

;@hypothesis-removal fn-cpmm-config-preflight-maintains-fixed-five-metadata approved
(assert-event
 (let* ((original (fn-caammt-cp *cpmm-fence*))
        (cp (update-nth 6 (update-nth 1 *fn-cbor-max-uint* (fn-cp-nth 6 original)) original))
        (m (fn-cpmm-annotation cp)))
  (and (equal (fn-cpmmct-hypotheses cp m) '(t t t nil))
       (not (fn-cpmmct-conclusion cp m))
       (equal (fn-cpm-config-preflight cp m) '(:refused :authority-revision-exhausted)))))

;@mutation-witness fn-cpmm-old-four-schema-is-unavailable
(assert-event
 (and (equal (car (mv-list 3 (fn-cpm-authority-step (car *cpmm-seed*)
                        (fn-caammt-event (car *cpmm-seed*) 1 *caammt-begin-op*)
                        (fn-cpm-account4 (cadr *cpmm-seed*)))))
             '(:refused :consumer-metadata-unavailable))
      (equal (fn-cpm-config-preflight (car *cpmm-seed*)
                                     (fn-cpm-account4 (cadr *cpmm-seed*)))
             '(:refused :consumer-metadata-unavailable))))

(defun fn-cpmmt-seed-correspondp (history incarnation frontier hn in)
 (declare (xargs :guard t :verify-guards nil))
 (mv-let (cp metadata) (fn-cpm-initial history incarnation frontier hn in)
  (equal metadata (fn-cpmm-annotation cp))))
;@positive fn-cpmm-initial-establishes-fixed-five-metadata
(assert-event
 (and (equal (fn-caammt-seed-hypotheses '(1 2) '(3 4) 7 2 2) '(t t t t t))
      (fn-cpmmt-seed-correspondp '(1 2) '(3 4) 7 2 2)))

;@hypothesis-removal fn-cpmm-initial-establishes-fixed-five-metadata history-octets
(assert-event
 (and (equal (fn-caammt-seed-hypotheses '(300) '(3 4) 7 1 2) '(nil t t t t))
      (not (fn-cpmmt-seed-correspondp '(300) '(3 4) 7 1 2))))

;@hypothesis-removal fn-cpmm-initial-establishes-fixed-five-metadata history-count
(assert-event
 (and (equal (fn-caammt-seed-hypotheses '(1 2) '(3 4) 7 3 2) '(t nil t t t))
      (not (fn-cpmmt-seed-correspondp '(1 2) '(3 4) 7 3 2))))

;@hypothesis-removal fn-cpmm-initial-establishes-fixed-five-metadata incarnation-octets
(assert-event
 (and (equal (fn-caammt-seed-hypotheses '(1 2) '(300) 7 2 1) '(t t nil t t))
      (not (fn-cpmmt-seed-correspondp '(1 2) '(300) 7 2 1))))

;@hypothesis-removal fn-cpmm-initial-establishes-fixed-five-metadata incarnation-count
(assert-event
 (and (equal (fn-caammt-seed-hypotheses '(1 2) '(3 4) 7 2 3) '(t t t nil t))
      (not (fn-cpmmt-seed-correspondp '(1 2) '(3 4) 7 2 3))))

;@hypothesis-removal fn-cpmm-initial-establishes-fixed-five-metadata frontier-scalar
(assert-event
 (and (equal (fn-caammt-seed-hypotheses '(1 2) '(3 4) '(7) 2 2) '(t t t t nil))
      (not (fn-cpmmt-seed-correspondp '(1 2) '(3 4) '(7) 2 2))))
(defun fn-cpmmt-fullp (result)
 (declare (xargs :guard t :verify-guards nil))
 (and (equal (car (car result)) :ok)
      (equal (cadr result) (fn-cpmm-annotation (fn-caammt-cp result)))))

(defconst *cpmst-delete-begin*
 (fn-cpmmt-next *cpmm-fence* 6 '(:authority-begin (66) 1 3 7)))

(defconst *cpmst-tombstone-op* '(:authority-tombstone (66) 1 (97) 2))

(defconst *cpmst-tombstone*
 (fn-cpmmt-next *cpmst-delete-begin* 7 *cpmst-tombstone-op*))

(defconst *cpmst-delete-seal*
 (fn-cpmmt-next *cpmst-tombstone* 8
  (fn-caammt-final-op (fn-caammt-cp *cpmst-tombstone*) :authority-seal)))

(defconst *cpmst-delete-prepare*
 (fn-cpmmt-next *cpmst-delete-seal* 9 '(:authority-prepare (66) 1)))

(defconst *cpmst-delete-fence*
 (fn-cpmmt-next *cpmst-delete-prepare* 10
  (fn-caammt-final-op (fn-caammt-cp *cpmst-delete-prepare*) :authority-fence)))

(defconst *cpmst-recreate-begin*
 (fn-cpmmt-next *cpmst-delete-fence* 11 '(:authority-begin (67) 2 8 7)))

(defconst *cpmst-recreate-op*
 (update-nth 4 12 (update-nth 2 2 (update-nth 1 '(67) *caammt-row-op*))))

(defconst *cpmst-recreate-row*
 (fn-cpmmt-next *cpmst-recreate-begin* 12 *cpmst-recreate-op*))

(defconst *cpmst-recreate-seal*
 (fn-cpmmt-next *cpmst-recreate-row* 13
  (fn-caammt-final-op (fn-caammt-cp *cpmst-recreate-row*) :authority-seal)))

(defconst *cpmst-recreate-prepare*
 (fn-cpmmt-next *cpmst-recreate-seal* 14 '(:authority-prepare (67) 2)))

(defconst *cpmst-recreate-fence*
 (fn-cpmmt-next *cpmst-recreate-prepare* 15
  (fn-caammt-final-op (fn-caammt-cp *cpmst-recreate-prepare*) :authority-fence)))

;@mutation-witness fn-cpmm-actual-delete-tombstone-recreate-keeps-all-five
(assert-event
 (let* ((original (car (fn-cp-nth 4 (fn-cp-nth 6 (fn-caammt-cp *cpmm-fence*)))))
        (deleted (car (fn-cp-nth 4 (fn-cp-nth 6 (fn-caammt-cp *cpmst-delete-fence*)))))
        (recreated (car (fn-cp-nth 4 (fn-cp-nth 6 (fn-caammt-cp *cpmst-recreate-fence*)))))
        (delete-root (fn-cp-nth 2 (car *cpmst-delete-fence*))))
  (and (fn-cpmmt-fullp *cpmst-delete-begin*) (fn-cpmmt-fullp *cpmst-tombstone*)
       (fn-cpmmt-fullp *cpmst-delete-seal*) (fn-cpmmt-fullp *cpmst-delete-prepare*)
       (fn-cpmmt-fullp *cpmst-delete-fence*)
       (fn-cpmmt-fullp *cpmst-recreate-begin*) (fn-cpmmt-fullp *cpmst-recreate-row*)
       (fn-cpmmt-fullp *cpmst-recreate-seal*) (fn-cpmmt-fullp *cpmst-recreate-prepare*)
       (fn-cpmmt-fullp *cpmst-recreate-fence*)
       (equal (fn-cp-nth 2 original) (fn-cp-nth 2 deleted))
       (null (fn-cp-nth 3 deleted)) (null (fn-cp-nth 3 delete-root))
       (not (equal (fn-cp-nth 2 deleted) (fn-cp-nth 2 recreated)))
       (equal (fn-cp-creation-coordinate (fn-cp-nth 2 recreated)) 12)
       (equal (fn-cp-nth 2 *cpmst-delete-fence*) (fn-scs-summary delete-root))
       (equal (fn-cp-nth 2 *cpmst-recreate-fence*)
              (fn-scs-summary (fn-cp-nth 2 (car *cpmst-recreate-fence*)))))))
