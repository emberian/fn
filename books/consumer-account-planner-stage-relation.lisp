; Actual row/tombstone planner joins to complete candidate reconstruction.
; All added recognizers are proof-only: no served old-list validation.
(in-package "ACL2")
(include-book "consumer-account-relation-stage")
(include-book "consumer-account-row-relation")

(defun fn-caps-suffixp (suffix rows)
  (declare (xargs :guard t :verify-guards nil))
  (if (equal suffix rows) t
    (and (consp rows) (fn-caps-suffixp suffix (cdr rows)))))

(defun fn-caps-old-rowsp (rows watermark)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp rows)
      (and (fn-cp-authority-rowp (car rows) watermark)
           (fn-cai-namep (fn-cp-nth 1 (car rows)) *fn-auth-max-name-octets*)
           (or (not (consp (cdr rows)))
               (fn-caa-name-lessp (fn-cp-nth 1 (car rows))
                                 (fn-cp-nth 1 (cadr rows))))
           (fn-caps-old-rowsp (cdr rows) watermark))
    (null rows)))

(defun fn-caps-merge-relp (p installed)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((prep (fn-cp-nth 5 p)) (old (fn-cp-nth 2 prep)))
    (and (fn-caas-merge-relp p)
         (fn-caps-suffixp old installed)
         (fn-caps-old-rowsp old (fn-cp-nth 4 p)))))

(local
 (defthm fn-caps-suffix-of-self
   (fn-caps-suffixp rows rows)
   :hints (("Goal" :in-theory (enable fn-caps-suffixp)))))
(local
 (defthm fn-caps-suffix-cdr
   (implies (and (fn-caps-suffixp old installed) (consp old))
            (fn-caps-suffixp (cdr old) installed))
   :hints (("Goal" :induct (fn-caps-suffixp old installed)
            :in-theory (enable fn-caps-suffixp)))))
(local
 (defthm fn-caps-old-rows-cdr
   (implies (fn-caps-old-rowsp rows watermark)
            (fn-caps-old-rowsp (cdr rows) watermark))
   :hints (("Goal" :in-theory (enable fn-caps-old-rowsp)))))
(local
 (defthm fn-caps-old-rows-head
   (implies (and (fn-caps-old-rowsp rows watermark) (consp rows))
            (and (consp (car rows))
                 (fn-cp-account-creationp (fn-cp-nth 2 (car rows)) watermark)
                 (fn-cai-namep (fn-cp-nth 1 (car rows)) *fn-auth-max-name-octets*)))
   :hints (("Goal" :in-theory
            (e/d (fn-caps-old-rowsp fn-cp-authority-rowp)
                 (fn-cp-account-creationp fn-cai-namep fn-cp-nth))))))
(local
 (defthm fn-caps-old-rows-watermark-monotone
   (implies (and (fn-caps-old-rowsp rows old)
                 (<= (nfix old) (nfix new)))
            (fn-caps-old-rowsp rows new))
   :hints (("Goal" :induct (fn-caps-old-rowsp rows old)
            :in-theory
            (e/d (fn-caps-old-rowsp fn-cp-authority-rowp fn-cp-account-creationp)
                 (fn-cp-nth fn-cp-creation-coordinate fn-cai-namep
                  fn-caa-name-lessp))))))

; Exact cursor movement is the actual planner's decision. A row insertion
; preserves the borrow; only a matching login consumes one old cell.
(defthm fn-caps-successful-row-plan-cursor-unfolds
  (let* ((p (fn-cp-nth 5 a)) (old (fn-cp-nth 2 (fn-cp-nth 5 p)))
         (plan (fn-caa-row-plan a event op)))
    (implies (and (fn-caps-merge-relp p installed)
                  (equal (car plan) :stage))
             (and (equal (fn-cp-nth 1 (fn-cp-nth 1 plan)) (fn-cp-nth 3 op))
                  (or (not (fn-cp-nth 6 p))
                      (fn-caa-name-lessp (fn-cp-nth 6 p) (fn-cp-nth 3 op)))
                  (equal (fn-cp-nth 3 plan)
                         (if (and (consp old)
                                  (equal (fn-cp-nth 3 op) (fn-cp-nth 1 (car old))))
                             (cdr old) old)))))
  :hints (("Goal"
           :use ((:instance fn-caps-old-rows-head
                            (rows (fn-cp-nth 2 (fn-cp-nth 5 (fn-cp-nth 5 a))))
                            (watermark (fn-cp-nth 4 (fn-cp-nth 5 a)))))
           :in-theory (e/d (fn-caps-merge-relp fn-caa-row-plan fn-cp-nth)
                            (fn-caps-old-rowsp fn-caps-suffixp fn-caas-merge-relp
                             fn-cp-account-creationp fn-caa-row-credential
                             fn-caa-row-descriptor fn-auth-credp fn-caa-name-lessp
                             fn-cp-account-creation fn-cp-creation-coordinate
                             fn-caps-old-rows-head)))))

(defthm fn-caps-successful-tombstone-plan-cursor-unfolds
  (let* ((p (fn-cp-nth 5 a)) (old (fn-cp-nth 2 (fn-cp-nth 5 p)))
         (plan (fn-caa-tombstone-plan a event op)))
    (implies (equal (car plan) :stage)
             (and (consp old)
                  (equal (fn-cp-nth 1 (fn-cp-nth 1 plan)) (fn-cp-nth 1 (car old)))
                  (equal (fn-cp-nth 1 (fn-cp-nth 1 plan)) (fn-cp-nth 3 op))
                  (equal (fn-cp-nth 2 (fn-cp-nth 1 plan)) (fn-cp-nth 2 (car old)))
                  (or (not (fn-cp-nth 6 p))
                      (fn-caa-name-lessp (fn-cp-nth 6 p) (fn-cp-nth 3 op)))
                  (equal (fn-cp-nth 3 plan) (cdr old)))))
  :hints (("Goal" :in-theory
           (e/d (fn-caa-tombstone-plan fn-cp-nth)
                (fn-caa-name-lessp fn-cp-creation-coordinate)))))

(defthm fn-caps-begin-establishes-borrowed-merge
  (implies (and (natp (fn-cp-nth 2 a))
                (natp (fn-cp-nth 4 op)) (<= (fn-cp-nth 4 op) 7)
                (fn-caps-old-rowsp (fn-cp-nth 4 a) (fn-cp-nth 2 a))
                (equal (car (fn-caa-begin s a event op)) :ok))
           (fn-caps-merge-relp
            (fn-cp-nth 5 (fn-cp-nth 6
             (fn-cp-nth 1 (fn-caa-begin s a event op)))) (fn-cp-nth 4 a)))
  :hints (("Goal" :use fn-caas-begin-establishes-merge-relation
           :in-theory
           (e/d (fn-caps-merge-relp fn-caa-begin fn-caa-success
                 fn-caa-authority-pending fn-caa-preparation fn-caa-pending
                 fn-cp-state-carry fn-cp-nth)
                (fn-caas-merge-relp fn-caps-old-rowsp fn-caps-suffixp
                 fn-caa-namespace fn-cp-authority-namespacep fn-sha256 fn-cac-encode)))))

(local
 (defthm fn-caps-selected-stage-preserves-borrowed-merge
   (let* ((p (fn-cp-nth 5 a)) (old (fn-cp-nth 2 (fn-cp-nth 5 p))))
     (implies
      (and (fn-caps-merge-relp p installed)
           (or (not (fn-cp-nth 6 p))
               (fn-caa-name-lessp (fn-cp-nth 6 p) (fn-cp-nth 1 row)))
           (fn-caar-bindingp row (list :account-binding row credential)
             (max (nfix (fn-cp-nth 4 p)) (1+ (nfix (fn-cp-nth 2 event)))))
           (or (equal old-rest old)
               (and (consp old) (equal old-rest (cdr old)))))
      (fn-caps-merge-relp
       (fn-cp-nth 5 (fn-cp-nth 6
        (fn-cp-nth 1 (fn-caa-stage-selected s a event row credential old-rest))))
       installed)))
   :hints (("Goal"
            :use ((:instance fn-caas-selected-stage-preserves-complete-merge)
                  (:instance fn-caps-suffix-cdr
                             (old (fn-cp-nth 2 (fn-cp-nth 5 (fn-cp-nth 5 a)))))
                  (:instance fn-caps-old-rows-cdr
                             (rows (fn-cp-nth 2 (fn-cp-nth 5 (fn-cp-nth 5 a))))
                             (watermark (fn-cp-nth 4 (fn-cp-nth 5 a))))
                  (:instance fn-caps-old-rows-watermark-monotone
                             (rows old-rest)
                             (old (fn-cp-nth 4 (fn-cp-nth 5 a)))
                             (new (max (nfix (fn-cp-nth 4 (fn-cp-nth 5 a)))
                                       (1+ (nfix (fn-cp-nth 2 event)))))))
            :in-theory
            (e/d (fn-caps-merge-relp fn-caa-stage-selected fn-caa-stage-indexed
                  fn-caa-preparation fn-caa-pending fn-caa-root fn-caa-success
                  fn-caa-authority-pending fn-cp-state-carry fn-cp-nth)
                 (fn-caas-merge-relp fn-caps-suffixp fn-caps-old-rowsp
                  fn-caar-bindingp fn-caa-name-lessp fn-cai-put-octets
                  fn-sha256 fn-cac-encode
                  fn-caas-selected-stage-preserves-complete-merge))))))

; The old cursor supplies the retained token premise pointwise. No namespace
; equality is assumed for restored/inherited account creation tokens.
(defthm fn-caps-actual-row-preserves-borrowed-complete-merge
  (let ((p (fn-cp-nth 5 a)))
    (implies
     (and (fn-caps-merge-relp p installed)
          (fn-cac-operationp op)
          (fn-cp-authority-namespacep (fn-cp-nth 6 (fn-cp-nth 5 p)))
          (fn-cp-uintp (fn-cp-nth 2 event))
          (equal (car (fn-caa-row-plan a event op)) :stage))
     (fn-caps-merge-relp
      (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 (fn-caa-row s a event op))))
      installed)))
  :hints (("Goal"
           :expand ((fn-cp-nth 0 (fn-caa-row-plan a event op)))
           :use ((:instance fn-caarr-row-plan-establishes-binding)
                 (:instance fn-caps-successful-row-plan-cursor-unfolds)
                 (:instance fn-caps-old-rows-head
                            (rows (fn-cp-nth 2 (fn-cp-nth 5 (fn-cp-nth 5 a))))
                            (watermark (fn-cp-nth 4 (fn-cp-nth 5 a))))
                 (:instance fn-caps-selected-stage-preserves-borrowed-merge
                            (row (fn-cp-nth 1 (fn-caa-row-plan a event op)))
                            (credential (fn-cp-nth 2 (fn-caa-row-plan a event op)))
                            (old-rest (fn-cp-nth 3 (fn-caa-row-plan a event op)))))
           :in-theory
           (e/d (fn-caa-row fn-caps-merge-relp)
                (max nfix fn-caas-merge-relp fn-caps-old-rowsp fn-caps-suffixp fn-cp-nth
                 fn-caa-row-plan fn-caa-stage-selected fn-caar-bindingp
                 fn-cac-operationp fn-cp-authority-namespacep fn-cp-uintp
                 fn-cp-account-creationp fn-cai-namep fn-caa-name-lessp
                 fn-caarr-row-plan-establishes-binding
                 fn-caps-successful-row-plan-cursor-unfolds
                 fn-caps-selected-stage-preserves-borrowed-merge)))))

(defthm fn-caps-actual-tombstone-preserves-borrowed-complete-merge
  (let ((p (fn-cp-nth 5 a)))
    (implies
     (and (fn-caps-merge-relp p installed)
          (equal (car (fn-caa-tombstone-plan a event op)) :stage))
     (fn-caps-merge-relp
      (fn-cp-nth 5 (fn-cp-nth 6 (fn-cp-nth 1 (fn-caa-tombstone s a event op))))
      installed)))
  :hints (("Goal"
           :expand ((fn-cp-nth 0 (fn-caa-tombstone-plan a event op)))
           :use ((:instance fn-caarr-tombstone-plan-establishes-binding)
                 (:instance fn-caps-successful-tombstone-plan-cursor-unfolds)
                 (:instance fn-caps-old-rows-head
                            (rows (fn-cp-nth 2 (fn-cp-nth 5 (fn-cp-nth 5 a))))
                            (watermark (fn-cp-nth 4 (fn-cp-nth 5 a))))
                 (:instance fn-caps-selected-stage-preserves-borrowed-merge
                            (row (fn-cp-nth 1 (fn-caa-tombstone-plan a event op)))
                            (credential (fn-cp-nth 2 (fn-caa-tombstone-plan a event op)))
                            (old-rest (fn-cp-nth 3 (fn-caa-tombstone-plan a event op)))))
           :in-theory
           (e/d (fn-caa-tombstone fn-caps-merge-relp)
                (max nfix fn-caas-merge-relp fn-caps-old-rowsp fn-caps-suffixp fn-cp-nth
                 fn-caa-tombstone-plan fn-caa-stage-selected fn-caar-bindingp
                 fn-cp-account-creationp fn-cai-namep fn-caa-name-lessp
                 fn-caarr-tombstone-plan-establishes-binding
                 fn-caps-successful-tombstone-plan-cursor-unfolds
                 fn-caps-selected-stage-preserves-borrowed-merge)))))

; The installed publication relation supplies the initial old-row input.
; This proof projection neither walks the installed table nor revalidates it.
(local
 (defthm fn-caps-complete-rows-imply-typed-order
   (implies (fn-caar-rowsp rows index watermark)
            (fn-caps-old-rowsp rows watermark))
   :hints (("Goal" :induct (fn-caar-rowsp rows index watermark)
            :in-theory
            (e/d (fn-caar-rowsp fn-caar-bindingp fn-caps-old-rowsp)
                 (fn-cp-authority-rowp fn-cai-namep fn-cp-nth
                  fn-cai-get-octets fn-caa-name-lessp fn-auth-credp
                  fn-caar-credential-descriptor))))))

(defthm fn-caps-installed-root-typed-order-unfolds
  (implies (fn-caar-root-relp rows watermark root)
           (fn-caps-old-rowsp rows watermark))
  :hints (("Goal"
           :use ((:instance fn-caps-complete-rows-imply-typed-order
                            (index (fn-cp-nth 2 root))))
           :in-theory (e/d (fn-caar-root-relp fn-caar-index-relp)
                            (fn-caar-rowsp fn-caps-old-rowsp
                             fn-caps-complete-rows-imply-typed-order)))))

; Actual seal cannot discard an unconsumed old live row or tombstone.
(defthm fn-caps-successful-seal-exhausts-old-cursor-unfolds
  (implies (equal (car (fn-caa-seal s a event op)) :ok)
           (not (fn-cp-nth 2 (fn-cp-nth 5 (fn-cp-nth 5 a)))))
  :hints (("Goal" :in-theory
           (e/d (fn-caa-seal fn-caa-success fn-cp-nth)
                (fn-caa-count-digest-matchp fn-caa-pending fn-caa-preparation
                 fn-caa-authority-pending fn-cp-state-carry)))))

(in-theory (disable fn-caps-suffixp fn-caps-old-rowsp fn-caps-merge-relp))
