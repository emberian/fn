; Installed owner FNFD boundary over the carried table relation.
(in-package "ACL2")
(include-book "owner-feed-counts")
(include-book "feed-live-carried")

(defun fn-own-feed-port-peer-carried (peer tbl event)
  (declare (xargs :guard (and (fn-own-feed-tablep tbl)
                              (fn-ofct-table-relationp tbl))
                  :verify-guards nil))
  (mbe
   :logic (fn-own-feed-port-peer peer tbl event)
   :exec
   (let ((e (fn-own-feed-entry-of peer tbl)))
     (if (null e)
         (fn-own-feed-port-result :ignored tbl nil nil)
       (let ((step (fn-feed-live-port-step-carried
                    (fn-own-feed-entry-feed e) event)))
         (if (equal (fn-feed-port-step-status step) :accepted)
             (let ((effects (fn-feed-port-step-effects step)))
               (fn-own-feed-port-result-counted
                :accepted
                (fn-own-feed-put peer (fn-own-feed-entry-record e)
                                 (fn-feed-port-step-feed step) tbl)
                (fn-feed-port-step-records step)
                (if (null effects) nil (list (cons peer effects)))
                (fn-own-feed-pending-delta
                 (fn-own-feed-entry-feed e) (fn-feed-port-step-feed step))))
           (fn-own-feed-port-result :refused tbl nil nil)))))))

(local
 (defthm fn-ofcv-found-feed-is-valid
   (implies (and (fn-own-feed-tablep tbl) (fn-own-feed-entry-of peer tbl))
            (fn-feedp (fn-own-feed-entry-feed (fn-own-feed-entry-of peer tbl))))
   :hints (("Goal" :use fn-own-feed-entry-of-is-okp
            :in-theory (e/d (fn-own-feed-entry-okp fn-own-feed-feed-okp)
                             (fn-own-feed-tablep fn-own-feed-entry-of
                              fn-own-feed-entry-of-is-okp fn-feedp))))))


(defun fn-ofcv-enqueue-one (peer tbl msgid tick pending)
  (declare (xargs :guard (and (fn-own-feed-tablep tbl)
                              (fn-ofct-table-relationp tbl)
                              (acl2-numberp pending)) :verify-guards nil))
  (let ((e (fn-own-feed-entry-of peer tbl)))
    (if (null e) (cons tbl pending)
      (let* ((old (fn-own-feed-entry-feed e))
             (new (fn-fcv-raw-enqueue old msgid tick)))
        (cons (fn-own-feed-put peer (fn-own-feed-entry-record e) new tbl)
              (+ pending (fn-own-feed-pending-delta old new)))))))

(local
 (defthm fn-ofcv-raw-enqueue-is-enqueue
   (implies (and (fn-feedp f) (fn-feed-count-relationp f))
            (equal (fn-fcv-raw-enqueue f id tick) (fn-feed-enqueue f id tick)))
   :hints (("Goal" :in-theory
            (e/d (fn-fcv-raw-enqueue fn-feed-enqueue fn-feed-count-relationp)
                 (fn-feedp fn-feed-undelivered fn-feed-queue))))))

(defthm fn-ofcv-enqueue-one-is-counted-singleton
  (implies (and (fn-own-feed-tablep tbl) (fn-ofct-table-relationp tbl))
           (equal (fn-ofcv-enqueue-one peer tbl id tick pending)
                  (fn-own-feed-enqueue-all-counted (list peer) tbl id tick pending)))
  :hints (("Goal" :in-theory
           (e/d (fn-ofcv-enqueue-one fn-own-feed-enqueue-all-counted)
                (fn-own-feed-tablep fn-ofct-table-relationp fn-own-feed-entry-of
                 fn-fcv-raw-enqueue fn-feed-enqueue fn-own-feed-put)))))

(defthm fn-ofcv-enqueue-one-preserves-tablep
  (implies (and (fn-own-feed-tablep tbl) (fn-ofct-table-relationp tbl))
           (fn-own-feed-tablep (car (fn-ofcv-enqueue-one peer tbl id tick pending))))
  :hints (("Goal" :in-theory (disable fn-ofcv-enqueue-one
                                     fn-own-feed-tablep fn-own-feed-enqueue-all))))

(defthm fn-ofcv-enqueue-one-preserves-count-relation
  (implies (and (fn-own-feed-tablep tbl) (fn-ofct-table-relationp tbl))
           (fn-ofct-table-relationp (car (fn-ofcv-enqueue-one peer tbl id tick pending))))
  :hints (("Goal" :in-theory
           (e/d (fn-ofcv-enqueue-one)
                (fn-ofcv-enqueue-one-is-counted-singleton
                 fn-fcv-raw-enqueue fn-feed-enqueue fn-own-feed-put
                 fn-own-feed-entry-of fn-own-feed-tablep fn-ofct-table-relationp)))))

(verify-guards fn-ofcv-enqueue-one
 :hints (("Goal" :in-theory (disable fn-own-feed-tablep fn-ofct-table-relationp
                                    fn-own-feed-entry-of fn-feedp))))

(defun fn-own-feed-enqueue-all-carried (names tbl msgid tick pending)
  (declare (xargs :guard (and (fn-own-feed-tablep tbl)
                              (fn-ofct-table-relationp tbl)
                              (acl2-numberp pending)) :verify-guards nil))
  (if (consp names)
      (let ((one (fn-ofcv-enqueue-one (car names) tbl msgid tick pending)))
        (fn-own-feed-enqueue-all-carried (cdr names) (car one) msgid tick (cdr one)))
    (cons tbl pending)))

(defthm fn-ofcv-enqueue-one-pending-is-numeric
  (implies (acl2-numberp pending)
           (acl2-numberp (cdr (fn-ofcv-enqueue-one peer tbl id tick pending))))
  :hints (("Goal" :in-theory (enable fn-ofcv-enqueue-one))))

(verify-guards fn-own-feed-enqueue-all-carried
  :hints (("Goal" :in-theory (disable fn-ofcv-enqueue-one fn-ofcv-enqueue-one-is-counted-singleton
                                     fn-own-feed-tablep fn-ofct-table-relationp))))

(defthm fn-own-feed-enqueue-all-carried-is-counted-reference
  (implies (and (fn-own-feed-tablep tbl) (fn-ofct-table-relationp tbl))
           (equal (fn-own-feed-enqueue-all-carried names tbl id tick pending)
                  (fn-own-feed-enqueue-all-counted names tbl id tick pending)))
  :hints (("Goal" :induct (fn-own-feed-enqueue-all-carried names tbl id tick pending)
           :in-theory (e/d (fn-own-feed-enqueue-all-carried
                             fn-own-feed-enqueue-all-counted)
                            (fn-ofcv-enqueue-one fn-own-feed-entry-of
                             fn-own-feed-tablep fn-ofct-table-relationp
                             fn-own-feed-put fn-feed-enqueue)))
          ("Subgoal *1/1"
           :use ((:instance fn-ofcv-enqueue-one-preserves-tablep (peer (car names)))
                 (:instance fn-ofcv-enqueue-one-preserves-count-relation (peer (car names)))))))

(defun fn-own-feed-enqueue-all-counted-carried (names tbl id tick pending)
  (declare (xargs :guard (and (fn-own-feed-tablep tbl)
                              (fn-ofct-table-relationp tbl)
                              (acl2-numberp pending))))
  (mbe :logic (fn-own-feed-enqueue-all-counted names tbl id tick pending)
       :exec (fn-own-feed-enqueue-all-carried names tbl id tick pending)))

(defthm fn-own-feed-enqueue-all-counted-carried-is-reference-by-definition
  (equal (fn-own-feed-enqueue-all-counted-carried names tbl id tick pending)
         (fn-own-feed-enqueue-all-counted names tbl id tick pending)))

(verify-guards fn-own-feed-port-peer-carried
  :hints (("Goal"
           :in-theory (e/d (fn-own-feed-port-peer-carried
                             fn-own-feed-port-peer fn-own-feed-entry-okp
                             fn-own-feed-feed-okp fn-feed-live-port-step-carried)
                            (fn-own-feed-tablep fn-ofct-table-relationp fn-own-feed-entry-of
                             fn-feed-live-port-step fn-feedp)))))

; Projection equality is the MBE logic, not the keystone. The guard proof
; above establishes the actual scan-free branch's full result equivalence.
(defthm fn-own-feed-port-peer-carried-is-reference-by-definition
  (equal (fn-own-feed-port-peer-carried peer tbl event)
         (fn-own-feed-port-peer peer tbl event)))

(in-theory (disable fn-own-feed-port-peer-carried fn-ofcv-enqueue-one
                    fn-own-feed-enqueue-all-carried fn-own-feed-enqueue-all-counted-carried))
