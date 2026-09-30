; Exact old OVER row renderer definitions extracted for the selected-source join.
; Names, bodies and original guard-verification events are unchanged.
(in-package "ACL2")
(include-book "article-fields")
(include-book "article-arena-reads")
(include-book "nov-fields")

(defun fn-nov-crlf-count-aux (bytes pending n)
  (declare (xargs :guard (natp n) :measure (acl2-count bytes)))
  (if (consp bytes)
      (if (equal (car bytes) 13)
          (if (and (consp (cdr bytes)) (equal (car (cdr bytes)) 10))
              (fn-nov-crlf-count-aux (cdr (cdr bytes)) nil (+ 1 n))
            nil)
        (if (or (equal (car bytes) 10) (equal (car bytes) 0))
            nil
          (fn-nov-crlf-count-aux (cdr bytes) t n)))
    (if pending nil n)))

(defthm fn-nov-crlf-count-aux-is-len-of-lines
  (let ((r (fn-nntp-crlf-lines-aux bytes line-rev lines-rev)))
    (equal (fn-nov-crlf-count-aux bytes (consp line-rev) (len lines-rev))
           (if (equal (car r) :ok) (len (car (cdr r))) nil)))
  :hints (("Goal" :induct (fn-nntp-crlf-lines-aux bytes line-rev lines-rev)
           :in-theory (enable fn-nntp-crlf-lines-aux))))

(defun fn-nov-body-line-count (payload)
  (declare (xargs :guard t :verify-guards nil))
  (let ((split (fn-nntp-split-article payload)))
    (if (fn-nntp-split-okp split)
        (mbe :logic
             (let ((lines (fn-nntp-crlf-lines (fn-nntp-split-body split))))
               (if (equal (car lines) :ok) (fn-ng-len (car (cdr lines))) 0))
             :exec
             (let ((body (fn-nntp-split-body split)))
               (if (fn-octet-listp body)
                   (let ((n (fn-nov-crlf-count-aux body nil 0)))
                     (if n n 0))
                 0)))
      0)))

(defun fn-nov-overview (article fn-arena)
  ; (:ok subject from date message-id references bytes lines) | (:error)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (let* ((payload (fn-nntp-article-bytes article fn-arena))
         (parsed (fn-article-parse payload)))
    (if (not (and (true-listp parsed)
                  (fn-article-result-okp parsed)
                  (fn-article-syntax-p (fn-article-result-article parsed))))
        (list :error)
      (let ((view (fn-article-result-article parsed)))
        (list :ok
              (fn-nov-header-content view *fn-nov-subject-name*)
              (fn-nov-header-content view *fn-nov-from-name*)
              (fn-nov-header-content view *fn-nov-date-name*)
              (fn-nov-header-content view *fn-nov-message-id-name*)
              (fn-nov-header-content view *fn-nov-references-name*)
              (fn-nntp-article-length article fn-arena)
              (fn-nov-body-line-count payload))))))

(verify-guards fn-nov-body-line-count
  :hints (("Goal" :in-theory (enable fn-nntp-crlf-lines)
           :use ((:instance fn-nov-crlf-count-aux-is-len-of-lines
                            (bytes (fn-nntp-split-body (fn-nntp-split-article payload)))
                            (line-rev nil) (lines-rev nil))))))

(verify-guards fn-nov-overview
  :hints (("Goal" :in-theory (disable fn-article-get-headers
                                      fn-article-syntax-p))))
