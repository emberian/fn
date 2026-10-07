(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-nntp-newnews-scan-cat-loop (groups threshold articles horizon fn-arena fn-cat acc)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (true-listp acc) :verify-guards nil
                  :measure (acl2-count articles)))
  (if (not (consp articles))
      (revappend acc nil)
    (let* ((article (fn-ag-car articles))
           (stamp (fn-article-stamp article)))
      (fn-nntp-newnews-scan-cat-loop
       groups threshold (fn-ag-cdr articles) (if (natp stamp) stamp horizon) fn-arena fn-cat
       (if (and (fn-nntp-newnews-candidatep groups article)
                (not (fn-scol-tombstonep article fn-arena fn-cat))
                (fn-nntp-newnews-newp threshold stamp horizon))
           (cons (fn-nntp-string-octets (fn-article-msgid article)) acc)
         acc)))))

(defun fn-nntp-newnews-scan-cat (groups threshold articles horizon fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t :verify-guards nil
                  :measure (acl2-count articles)))
  (mbe :logic
       (if (not (consp articles))
           nil
         (let* ((article (fn-ag-car articles))
                (stamp (fn-article-stamp article))
                (rest (fn-nntp-newnews-scan-cat
                       groups threshold (fn-ag-cdr articles)
                       (if (natp stamp) stamp horizon) fn-arena fn-cat)))
           (if (and (fn-nntp-newnews-candidatep groups article)
                    (not (fn-scol-tombstonep article fn-arena fn-cat))
                    (fn-nntp-newnews-newp threshold stamp horizon))
               (cons (fn-nntp-string-octets (fn-article-msgid article)) rest)
             rest)))
       :exec (fn-nntp-newnews-scan-cat-loop groups threshold articles horizon fn-arena fn-cat nil)))

(local
 (defthm fn-nntp-newnews-scan-cat-loop-is-revappend
   (equal (fn-nntp-newnews-scan-cat-loop groups threshold articles horizon fn-arena fn-cat acc)
          (revappend acc (fn-nntp-newnews-scan-cat groups threshold articles horizon fn-arena fn-cat)))
   :hints (("Goal" :in-theory (disable fn-nntp-newnews-candidatep fn-scol-tombstonep
                                       fn-nntp-newnews-newp fn-nntp-string-octets
                                       fn-article-stamp fn-article-msgid)))))

(verify-guards fn-nntp-newnews-scan-cat-loop)

(verify-guards fn-nntp-newnews-scan-cat
  :hints (("Goal" :in-theory (disable fn-nntp-newnews-scan-cat-loop fn-nntp-newnews-candidatep
                                      fn-scol-tombstonep fn-nntp-newnews-newp
                                      fn-nntp-string-octets fn-article-stamp fn-article-msgid)
                  :use ((:instance fn-nntp-newnews-scan-cat-loop-is-revappend (acc nil))))))
