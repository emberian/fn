; Positional completion reads over the carried resident history.
(in-package "ACL2")
(include-book "owner-commit-carried")
(include-book "history-columns-relation")

(defun fn-hist-completion-record (s fn-hist)
  (declare (xargs :stobjs fn-hist :guard t))
  (let* ((pair (fn-sf-completion (fn-sn-files s)))
         (i (if (and (consp pair) (natp (car pair))) (car pair) 0)))
    (if (< i (fn-hist-count fn-hist))
        (let ((r (fn-hist-at i fn-hist)))
          (if (and (fn-store-event-p r)
                   (equal pair (cons (fn-evc-sequence r) (fn-evc-txid r))))
              r nil))
      nil)))

(defthm fn-hist-completion-record-is-store-event
  (implies (fn-hist-completion-record s hist)
           (fn-store-event-p (fn-hist-completion-record s hist)))
  :hints (("Goal" :in-theory (enable fn-hist-completion-record))))

(defthm fn-hist-completion-record-is-reference
  (implies (and (fn-sn-statep s) (fn-hist-of-storep hist s))
           (equal (fn-hist-completion-record s hist)
                  (fn-ccar-completion-record s)))
  :hints (("Goal" :use ((:instance fn-ccar-completion-record-is-a-store-event))
           :in-theory (union-theories
                        '(fn-hist-completion-record fn-ccar-completion-record
                          fn-ccar-seek-at fn-sf-records-nth fn-sf-records-count
                          fn-hist-of-storep fn-hist-at-is-nth fn-hist-count-is-len)
                        (theory 'minimal-theory)))))

(in-theory (disable fn-hist-completion-record))
