(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-served-feed-loop (conn octets fn-arena acc)
  (declare (xargs :stobjs fn-arena :guard (fn-wire-statep (fn-served-conn-wire conn))
                  :verify-guards nil
                  :measure (len octets)))
  (if (or (not (consp octets))
          (fn-served-closed-wirep (fn-served-conn-wire conn))
          (fn-served-haltedp conn))
      (fn-served-make-result conn (fn-ag-rev-onto acc nil))
    (let ((here (fn-served-feed-byte conn (car octets) fn-arena)))
      (fn-served-feed-loop (fn-served-result-conn here) (cdr octets) fn-arena
                           (fn-ag-rev-onto (fn-served-result-effects here) acc)))))

(defun fn-served-feed (conn octets fn-arena)
  (declare (xargs :stobjs fn-arena :guard (fn-wire-statep (fn-served-conn-wire conn))
                  :verify-guards nil
                  :measure (len octets)))
  (mbe :logic
  (if (or (not (consp octets))
          (fn-served-closed-wirep (fn-served-conn-wire conn))
          (fn-served-haltedp conn))
      (fn-served-make-result conn nil)
    (let* ((here (fn-served-feed-byte conn (car octets) fn-arena))
           (tail (fn-served-feed (fn-served-result-conn here) (cdr octets) fn-arena)))
      (fn-served-make-result
       (fn-served-result-conn tail)
       (mbe :logic (append (fn-served-result-effects here)
                           (fn-served-result-effects tail))
            :exec (fn-ag-append (fn-served-result-effects here)
                                (fn-served-result-effects tail))))))
  :exec (fn-served-feed-loop conn octets fn-arena nil)))

(defthm fn-served-feed-loop-is-rev-onto
  (equal (fn-served-feed-loop conn octets fn-arena acc)
         (fn-served-make-result
          (fn-served-result-conn (fn-served-feed conn octets fn-arena))
          (fn-ag-rev-onto acc (fn-served-result-effects
                               (fn-served-feed conn octets fn-arena)))))
  :hints (("Goal" :induct (fn-served-feed-loop conn octets fn-arena acc)
                  :in-theory (disable fn-served-feed-byte fn-served-closed-wirep
                                      fn-served-haltedp))))

(verify-guards fn-served-feed-loop
  :hints (("Goal" :in-theory (disable fn-served-dispatch-events
                                      fn-wire-feed-byte fn-wire-statep))))

(verify-guards fn-served-feed
  :hints (("Goal" :expand ((fn-served-feed conn octets fn-arena))
                  :in-theory (disable fn-served-dispatch-events
                                      fn-wire-feed-byte fn-wire-statep))))
