(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-nntp-active-line (archive group)
  (let ((summary (fn-nntp-group-summary archive group)))
    (fn-nntp-append-pieces
     (list (fn-nntp-string-octets group) '(32)
           (fn-nntp-decimal-field (fn-nntp-summary-high summary)) '(32)
           (fn-nntp-decimal-field (fn-nntp-summary-low summary))
           (fn-nntp-string-octets " y")))))

(defun fn-nntp-active-lines-loop (archive groups acc)
  (declare (xargs :guard (true-listp acc) :verify-guards nil))
  (if (consp groups)
      (fn-nntp-active-lines-loop archive
                                 (cdr groups)
                                 (cons (fn-nntp-active-line archive (car groups)) acc))
    (revappend acc nil)))

(defun fn-nntp-active-lines (archive groups)
  (mbe :logic
       (if (consp groups)
           (cons (fn-nntp-active-line archive (car groups))
                 (fn-nntp-active-lines archive (cdr groups)))
         nil)
       :exec (fn-nntp-active-lines-loop archive groups nil)))

(local
 (defthm fn-nntp-active-lines-loop-is-revappend
   (equal (fn-nntp-active-lines-loop archive groups acc)
          (revappend acc (fn-nntp-active-lines archive groups)))
   :hints (("Goal" :induct (fn-nntp-active-lines-loop archive groups acc)
                   :in-theory (union-theories '(fn-nntp-active-lines-loop fn-nntp-active-lines revappend car-cons cdr-cons)
                                              (theory 'minimal-theory))))))

(defthm fn-nntp-active-lines-true-listp
  (true-listp (fn-nntp-active-lines archive groups)))

(verify-guards fn-nntp-active-line)

(verify-guards fn-nntp-active-lines-loop)

(verify-guards fn-nntp-active-lines
  :hints (("Goal" :in-theory (union-theories '(revappend fn-nntp-active-lines)
                                                  (union-theories (theory 'minimal-theory)
                                                                  (executable-counterpart-theory :here)))
                  :use ((:instance fn-nntp-active-lines-loop-is-revappend (acc nil))))))

