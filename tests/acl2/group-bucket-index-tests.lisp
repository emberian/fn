; Sparse local numbers, crossposts and a retained earlier view.
(in-package "ACL2")
(include-book "../../books/group-bucket-index")
(include-book "std/testing/must-fail" :dir :system)

(defconst *gix-groups* '("fn.one" "fn.two" "fn.three"))
(defconst *gix-a*
  (fn-make-article "<gix-a@example.invalid>" '(65)
                   '("fn.one" "fn.two")
                   (list (cons "fn.one" 2) (cons "fn.two" 70))
                   t 841000000))
(defconst *gix-b*
  (fn-make-article "<gix-b@example.invalid>" '(66)
                   '("fn.three") (list (cons "fn.three" 9))
                   t 841000000))
(defconst *gix-c*
  (fn-make-article "<gix-c@example.invalid>" '(67)
                   '("fn.one") (list (cons "fn.one" 100))
                   t 841000000))
(defconst *gix-old* (list *gix-a* *gix-b*))
(defconst *gix-new* (list *gix-a* *gix-b* *gix-c*))
(defconst *gix-old-buckets* (fn-gidx-build *gix-old*))
(defconst *gix-new-buckets* (fn-gidx-build *gix-new*))

(assert-event (fn-article-listp *gix-groups* *gix-new*))
(assert-event (equal (fn-gidx-range-numbers *gix-new-buckets*
                                            "fn.one" 3 100)
                     '(100)))
(assert-event (equal (fn-gidx-range-numbers *gix-new-buckets*
                                            "fn.one" 1 100)
                     '(2 100)))
(assert-event (equal (fn-gidx-range-numbers *gix-new-buckets*
                                            "fn.two" 1 100)
                     '(70)))
(assert-event (equal (fn-gidx-range-numbers *gix-new-buckets*
                                            "fn.three" 1 100)
                     '(9)))
(assert-event (equal (fn-gidx-range-numbers *gix-old-buckets*
                                            "fn.one" 1 100)
                     '(2)))
(assert-event (equal (fn-gidx-range-numbers *gix-new-buckets*
                                            "fn.empty" 1 100)
                     nil))
(assert-event (equal (fn-gidx-range-numbers *gix-new-buckets*
                                            "fn.one" 1 100)
                     (fn-nntp-group-range-numbers "fn.one" 1 100 *gix-new*)))
(assert-event (< (fn-gidx-range-work *gix-new-buckets* "fn.one")
                 (len (fn-index-build *gix-new*))))

; Without article-list consistency, a malformed historical membership can
; make the source fold and index interpretation differ.  This is the same
; live-state hypothesis the existing flat-index range keystone needs.
(must-fail
 (defthm gix-range-without-article-listp
   (equal (fn-gidx-range-numbers (fn-gidx-build articles) group low high)
          (fn-nntp-group-range-numbers group low high articles))
   :hints (("Goal" :do-not-induct t))))
(must-fail
 (defthm gix-range-without-group-type
   (implies (and (fn-article-listp configured articles)
                 (natp low) (natp high))
            (equal (fn-gidx-range-numbers (fn-gidx-build articles)
                                           group low high)
                   (fn-nntp-group-range-numbers group low high articles)))
   :hints (("Goal" :do-not-induct t))))
(must-fail
 (defthm gix-range-without-low-type
   (implies (and (fn-article-listp configured articles)
                 (stringp group) (natp high))
            (equal (fn-gidx-range-numbers (fn-gidx-build articles)
                                           group low high)
                   (fn-nntp-group-range-numbers group low high articles)))
   :hints (("Goal" :do-not-induct t))))
(must-fail
 (defthm gix-range-without-high-type
   (implies (and (fn-article-listp configured articles)
                 (stringp group) (natp low))
            (equal (fn-gidx-range-numbers (fn-gidx-build articles)
                                           group low high)
                   (fn-nntp-group-range-numbers group low high articles)))
   :hints (("Goal" :do-not-induct t))))
