; Whole-predicate witnesses, including a cache corrupted after startup.
(in-package "ACL2")
(include-book "../../books/owner-history-carried")
(include-book "../../books/defkeystone")

(defun fn-hsc-state ()
  (declare (xargs :guard t :verify-guards nil))
  (build-state))

(defthm fn-hsc-startup-positive
  (fn-owner-history-cache-statep (fn-hist-count nil)
                                (fn-owner-history-cache-startup nil (fn-hsc-state))))

(defthm fn-hsc-startup-mutation
  (and (fn-owner-history-cache-statep (fn-hist-count nil)
                                     (fn-owner-history-cache-startup nil (fn-hsc-state)))
       (not (fn-owner-history-cache-statep
             (fn-hist-count nil)
             (f-put-global 'fn-owner-record-debt '(1 . 0)
                           (fn-owner-history-cache-startup nil (fn-hsc-state))))))
  :hints (("Goal" :in-theory (enable fn-owner-history-cache-statep
                                    fn-hist-cache-ready-p))))

(defteeth fn-owner-history-cache-startup-establishes-ready
  :claim (() (fn-owner-history-cache-statep (fn-hist-count hist)
                                           (fn-owner-history-cache-startup hist st)))
  :subject fn-owner-history-startup
  :witness ((hist nil) (st (fn-hsc-state)))
  :witness-lemma fn-hsc-startup-positive
  :breaks ()
  :mutations ((over-count-cache
               (:conclusion
                (fn-owner-history-cache-statep
                 (fn-hist-count hist)
                 (f-put-global 'fn-owner-record-debt '(1 . 0)
                               (fn-owner-history-cache-startup hist st))))
               ((hist nil) (st (fn-hsc-state)))
               :fault "a mid-run cache writer sets its index past the history count"
               :lemma fn-hsc-startup-mutation)))

(defun fn-hsc-debt-store ()
  (declare (xargs :guard t))
  (fn-sn-make-v2
   nil 0
   (fn-sf-make :ready 1 nil
               (list (fn-store-retention-event-make :undertake 1 1 1
                                                    "work" "subject" "evidence" 3))
               nil nil nil nil)
   nil nil nil 0 nil nil 0))

(defthm fn-hsc-debt-positive
  (and (fn-hist-cache-ready-p '(0 . 0) (fn-hist-count nil) t)
       (equal (fn-hist-debt-served '(0 . 0) nil)
              (fn-hist-debt-carried '(0 . 0) nil nil)))
  :hints (("Goal" :in-theory (enable fn-hist-cache-ready-p))))

(defthm fn-hsc-debt-missing-cache
  (and (not (fn-hist-cache-ready-p nil (fn-hist-count nil) t))
       (not (equal (fn-hist-debt-served nil nil)
                   (fn-hist-debt-carried nil (fn-hsc-debt-store) nil))))
  :hints (("Goal" :in-theory (enable fn-hist-cache-ready-p fn-hist-debt-served
                                    fn-hist-debt-carried fn-sf-records))))

(defteeth fn-hist-debt-served-is-carried
  :claim (((cache-ready (fn-hist-cache-ready-p cache (fn-hist-count hist) t)))
          (equal (fn-hist-debt-served cache hist) (fn-hist-debt-carried cache s hist)))
  :subject fn-owner-record-debt
  :witness ((cache '(0 . 0)) (hist nil) (s nil))
  :witness-lemma fn-hsc-debt-positive
  :breaks ((cache-ready ((cache nil) (hist nil) (s (fn-hsc-debt-store)))
                        :lemma fn-hsc-debt-missing-cache))
  :mutations (:not-applicable "over-count mutation is attached to cache initialization"))
