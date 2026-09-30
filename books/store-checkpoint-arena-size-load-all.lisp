; One actual arena finish, retaining same-parse R child2 consumer metadata.
; Existing finish's first three values are the exact projection below.
(in-package "ACL2")
(include-book "store-checkpoint-arena-size-load")
(include-book "store-checkpoint-size-reader-all")

(defun fn-sckas-finish-all (rest s i b fn-octets)
 (declare (xargs :stobjs fn-octets :guard t :verify-guards nil))
 (if (not (equal i b)) (mv (list :refused :arena) nil nil nil)
  (mv-let (loaded info region consumer-info) (fn-sctsr-load-all rest fn-octets)
   (if (not (eq (car loaded) :ok)) (mv loaded nil nil nil)
    (if (not (equal (fn-sco-at 1 (fn-sct-tables-f (cadr loaded))) s))
     (mv (list :refused :close) nil nil nil)
     (mv (fn-sshr-share loaded) info region consumer-info))))))

(verify-guards fn-sckas-finish-all
 :hints (("Goal"
  :use ((:instance fn-sctsr-load-existing-result-true-listp (plan rest))
        (:instance fn-sctsr-load-all-original-three-by-definition (plan rest)))
  :in-theory (disable fn-sctsr-load fn-sctsr-load-all
                     fn-sctsr-load-existing-result-true-listp
                     fn-sctsr-load-all-original-three-by-definition))))

(defthm fn-sckas-finish-all-original-three-by-definition
 (and (equal (mv-nth 0 (fn-sckas-finish-all rest s i b fn-octets))
             (mv-nth 0 (fn-sckas-finish rest s i b fn-octets)))
      (equal (mv-nth 1 (fn-sckas-finish-all rest s i b fn-octets))
             (mv-nth 1 (fn-sckas-finish rest s i b fn-octets)))
      (equal (mv-nth 2 (fn-sckas-finish-all rest s i b fn-octets))
             (mv-nth 2 (fn-sckas-finish rest s i b fn-octets))))
 :hints (("Goal"
  :use ((:instance fn-sctsr-load-all-original-three-by-definition (plan rest)))
  :in-theory (e/d (fn-sckas-finish-all fn-sckas-finish)
                 (fn-sctsr-load fn-sctsr-load-all fn-sshr-share
                  fn-sctsr-load-all-original-three-by-definition)))))

(in-theory (disable fn-sckas-finish-all))
