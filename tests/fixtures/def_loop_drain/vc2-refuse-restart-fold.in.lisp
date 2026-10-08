(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-own-feed-port-restart-fold-loop (names current original racc)
  (declare (xargs :guard t))
  (if (consp names)
      (let ((one (fn-own-feed-port-restart-peer (car names) current)))
        (if (not (equal (fn-own-feed-port-status one) :accepted))
            (fn-own-feed-port-result :refused original nil nil)
          (fn-own-feed-port-restart-fold-loop
           (cdr names) (fn-own-feed-port-table one) original
           (fn-ag-rev-onto (fn-own-feed-port-records one) racc))))
    (fn-own-feed-port-result :accepted current (fn-ag-rev-onto racc nil) nil)))

(defun fn-own-feed-port-restart-fold (names current original)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (if (consp names)
             (let ((one (fn-own-feed-port-restart-peer (car names) current)))
               (if (not (equal (fn-own-feed-port-status one) :accepted))
                   (fn-own-feed-port-result :refused original nil nil)
                 (let ((rest (fn-own-feed-port-restart-fold
                              (cdr names) (fn-own-feed-port-table one) original)))
                   (if (not (equal (fn-own-feed-port-status rest) :accepted))
                       (fn-own-feed-port-result :refused original nil nil)
                     (fn-own-feed-port-result
                      :accepted
                      (fn-own-feed-port-table rest)
                      (append (fn-own-feed-port-records one)
                              (fn-own-feed-port-records rest))
                      nil)))))
           (fn-own-feed-port-result :accepted current nil nil))
       :exec (fn-own-feed-port-restart-fold-loop names current original nil)))

(defthm fn-own-feed-port-restart-fold-loop-is-fold
  (equal (fn-own-feed-port-restart-fold-loop names current original racc)
         (let ((r (fn-own-feed-port-restart-fold names current original)))
           (if (equal (fn-own-feed-port-status r) :accepted)
               (fn-own-feed-port-result
                :accepted (fn-own-feed-port-table r)
                (fn-ag-rev-onto racc (fn-own-feed-port-records r)) nil)
             (fn-own-feed-port-result :refused original nil nil))))
  :hints (("Goal" :induct (fn-own-feed-port-restart-fold-loop names current original racc)
                  :in-theory (e/d (fn-own-feed-port-result fn-own-feed-port-result-counted fn-own-feed-port-status
                                   fn-own-feed-port-table fn-own-feed-port-records
                                   fn-frame-item)
                                  (fn-own-feed-port-restart-peer)))))

(verify-guards fn-own-feed-port-restart-fold
  :hints (("Goal" :use ((:instance fn-own-feed-port-restart-fold-shape))
                  :in-theory (e/d (fn-own-feed-port-result fn-own-feed-port-result-counted fn-own-feed-port-status
                                   fn-own-feed-port-table fn-own-feed-port-records
                                   fn-frame-item)
                                  (fn-own-feed-port-restart-peer
                                   fn-own-feed-port-restart-fold-loop)))))
