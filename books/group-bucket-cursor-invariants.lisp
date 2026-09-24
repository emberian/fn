; Selected-group cursor correspondence without outer NNTP dispatcher imports.
(in-package "ACL2")
(include-book "nntp-index")
(include-book "group-bucket-index")

(defthm fn-gidx-index-group-numbers-of-select
  (implies (and (fn-index-listp entries) (stringp group))
           (equal (fn-nntp-index-group-numbers
                   (fn-gidx-select group entries) group)
                  (fn-nntp-index-group-numbers entries group)))
  :hints (("Goal" :in-theory (enable fn-nntp-index-group-numbers))))

(defthm fn-gidx-group-low-of-build
  (implies (and (fn-article-listp configured articles) (stringp group))
           (equal (fn-nntp-index-group-low
                   (fn-gidx-bucket group (fn-gidx-build articles)) group)
                  (fn-nntp-group-low group articles)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-index-build-listp)
                 (:instance fn-gidx-index-group-numbers-of-select
                            (entries (fn-index-build articles)))
                 (:instance fn-nntp-index-group-low-equals-fold))
           :in-theory
           (e/d (fn-gidx-build fn-nntp-index-group-low)
                (fn-gidx-index-group-numbers-of-select
                 fn-nntp-index-group-low-equals-fold)))))
