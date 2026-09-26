; over-number-index (PRF-189): witnesses and teeth for the group index's
; number index.  Reachable witnesses use buckets the owner's refresh
; builds (`fn-gidx-refresh', books/owner.lisp); the corrupted-state
; witnesses are labelled and are proof counterexamples, never runtime
; evidence.
(in-package "ACL2")
(include-book "../../books/nntp-range-indexed")
(include-book "../../books/owner")
(include-book "std/testing/must-fail" :dir :system)

(defun fn-tgn-payload (id subject)
  (append (fn-nntp-string-octets "Message-ID: ")
          (fn-nntp-string-octets id) '(13 10)
          (fn-nntp-string-octets "Subject: ")
          (fn-nntp-string-octets subject) '(13 10 13 10 88 13 10)))

(defconst *tgn-groups* '("fn.one" "fn.two"))
(defconst *tgn-a*
  (fn-make-article "<tgn-a@example.invalid>"
                   (fn-tgn-payload "<tgn-a@example.invalid>" "A")
                   '("fn.one" "fn.two")
                   (list (cons "fn.one" 2) (cons "fn.two" 70))
                   t 841000000))
(defconst *tgn-b*
  (fn-make-article "<tgn-b@example.invalid>"
                   (fn-tgn-payload "<tgn-b@example.invalid>" "B")
                   '("fn.one") (list (cons "fn.one" 3))
                   t 841000000))
; The largest RFC 3977 number: 31 trie levels.
(defconst *tgn-c*
  (fn-make-article "<tgn-c@example.invalid>"
                   (fn-tgn-payload "<tgn-c@example.invalid>" "C")
                   '("fn.one") (list (cons "fn.one" 2147483647))
                   t 841000000))
(defconst *tgn-old* (list *tgn-b* *tgn-a*))
(defconst *tgn-new* (list *tgn-c* *tgn-b* *tgn-a*))
(assert-event (fn-article-listp *tgn-groups* *tgn-new*))

; Reachable: the owner's refresh from nothing (a build) and then by one
; prepended article (a put of its entries).
(defconst *tgn-old-buckets* (fn-gidx-refresh nil nil *tgn-old*))
(defconst *tgn-new-buckets*
  (fn-gidx-refresh *tgn-old-buckets* *tgn-old* *tgn-new*))
(defconst *tgn-trie* (fn-midx-build *tgn-new*))
(assert-event (equal *tgn-new-buckets* (fn-gidx-build *tgn-new*)))

;; fn-gnix-get-of-set: a witness per branch, a must-fail per hypothesis.
(assert-event (and (posp 6) (posp 6)
                   (equal (fn-gnix-get 6 (fn-gnix-set 6 :v (fn-gnix-set 7 :w nil)))
                          :v)))
(assert-event (and (posp 7) (posp 6) (not (equal 7 6))
                   (equal (fn-gnix-get 7 (fn-gnix-set 6 :v (fn-gnix-set 7 :w nil)))
                          (fn-gnix-get 7 (fn-gnix-set 7 :w nil)))
                   (equal (fn-gnix-get 7 (fn-gnix-set 7 :w nil)) :w)))
; Without (posp n): 0 reads the root, where 1 is kept.
(assert-event (and (not (posp 0)) (posp 1)
                   (not (equal (fn-gnix-get 0 (fn-gnix-set 1 :v nil))
                               (if (equal 0 1) :v (fn-gnix-get 0 nil))))))
(must-fail
 (defthm fn-tgn-get-of-set-without-posp-n
   (implies (posp 1)
            (equal (fn-gnix-get 0 (fn-gnix-set 1 :v nil))
                   (if (equal 0 1) :v (fn-gnix-get 0 nil))))))
; Without (posp m): setting 0 writes the root, which 1 reads.
(assert-event (and (posp 1) (not (posp 0))
                   (not (equal (fn-gnix-get 1 (fn-gnix-set 0 :v nil))
                               (if (equal 1 0) :v (fn-gnix-get 1 nil))))))
(must-fail
 (defthm fn-tgn-get-of-set-without-posp-m
   (implies (posp 1)
            (equal (fn-gnix-get 1 (fn-gnix-set 0 :v nil))
                   (if (equal 1 0) :v (fn-gnix-get 1 nil))))))

;; fn-gnix-find-of-build (no hypothesis): the first entry of a number wins,
;; and an entry whose Message-ID is not valid is not indexed.
(defconst *tgn-bad-entry* (list "fn.one" 5 "no angle brackets"))
(defconst *tgn-dup-entries*
  (list (list "fn.one" 4 "<first@example.invalid>")
        (list "fn.one" 4 "<second@example.invalid>")
        *tgn-bad-entry*))
(assert-event
 (and (equal (fn-gnix-find 4 (fn-gnix-build "fn.one" *tgn-dup-entries*))
             (fn-gidx-find-number-entry "fn.one" 4 *tgn-dup-entries*))
      (equal (fn-index-entry-msgid
              (fn-gnix-find 4 (fn-gnix-build "fn.one" *tgn-dup-entries*)))
             "<first@example.invalid>")
      (equal (fn-gnix-find 5 (fn-gnix-build "fn.one" *tgn-dup-entries*)) nil)
      (equal (fn-gidx-find-number-entry "fn.one" 5 *tgn-dup-entries*) nil)))

;; The relation: established by the refresh's build, preserved by its put.
(assert-event (and (fn-gidx-numbers-okp *tgn-old-buckets*)
                   (fn-gidx-numbers-okp *tgn-new-buckets*)))

;; KEYSTONE fn-gidx-nidx-number-article-is-walk.  Reachable witness: the
;; refreshed buckets, the relation holds, and the number 2^31 - 1 and 2
;; find their articles (non-degenerate: a cons article each).
(assert-event
 (and (fn-gidx-numbers-okp *tgn-new-buckets*)
      (equal (fn-gidx-nidx-number-article
              2147483647 (fn-gidx-bucket-numbers "fn.one" *tgn-new-buckets*)
              *tgn-trie*)
             (fn-gidx-entry-number-article
              "fn.one" 2147483647 (fn-gidx-bucket "fn.one" *tgn-new-buckets*)
              *tgn-trie*))
      (equal (fn-gidx-nidx-number-article
              2147483647 (fn-gidx-bucket-numbers "fn.one" *tgn-new-buckets*)
              *tgn-trie*)
             *tgn-c*)
      (equal (fn-gidx-nidx-number-article
              70 (fn-gidx-bucket-numbers "fn.two" *tgn-new-buckets*)
              *tgn-trie*)
             *tgn-a*)
      (equal (fn-gidx-nidx-number-article
              70 (fn-gidx-bucket-numbers "fn.one" *tgn-new-buckets*)
              *tgn-trie*)
             nil)))
; CORRUPTED STATE (not reachable): fn.one's number index emptied.  The
; relation fails and so does the conclusion.
(defconst *tgn-corrupt-buckets*
  (cons (cons "fn.one" (cons (fn-gidx-bucket "fn.one" *tgn-new-buckets*) nil))
        *tgn-new-buckets*))
(assert-event
 (and (not (fn-gidx-numbers-okp *tgn-corrupt-buckets*))
      (consp (fn-gidx-entry-number-article
              "fn.one" 2 (fn-gidx-bucket "fn.one" *tgn-corrupt-buckets*)
              *tgn-trie*))
      (not (equal (fn-gidx-nidx-number-article
                   2 (fn-gidx-bucket-numbers "fn.one" *tgn-corrupt-buckets*)
                   *tgn-trie*)
                  (fn-gidx-entry-number-article
                   "fn.one" 2 (fn-gidx-bucket "fn.one" *tgn-corrupt-buckets*)
                   *tgn-trie*)))))
(must-fail
 (defthm fn-tgn-keystone-without-relation
   (equal (fn-gidx-nidx-number-article
           2 (fn-gidx-bucket-numbers "fn.one" *tgn-corrupt-buckets*) *tgn-trie*)
          (fn-gidx-entry-number-article
           "fn.one" 2 (fn-gidx-bucket "fn.one" *tgn-corrupt-buckets*) *tgn-trie*))))

;; fn-gidx-numbers-okp-of-put.  Reachable witness: the put of the new
;; article's first entry into the refreshed buckets.  Without the
;; hypothesis: a put of a fn.two entry leaves corrupted fn.one as it was.
(defconst *tgn-put-entry* (list "fn.one" 9 "<tgn-put@example.invalid>"))
(assert-event
 (and (fn-gidx-numbers-okp *tgn-old-buckets*)
      (fn-gidx-numbers-okp (fn-gidx-put *tgn-put-entry* *tgn-old-buckets*))
      (equal (fn-gnix-find 9 (fn-gidx-bucket-numbers
                              "fn.one"
                              (fn-gidx-put *tgn-put-entry* *tgn-old-buckets*)))
             *tgn-put-entry*)))
(assert-event
 (and (not (fn-gidx-numbers-okp *tgn-corrupt-buckets*))
      (not (fn-gidx-numbers-okp
            (fn-gidx-put (list "fn.two" 71 "<tgn-two@example.invalid>")
                         *tgn-corrupt-buckets*)))))
(must-fail
 (defthm fn-tgn-put-without-relation
   (fn-gidx-numbers-okp
    (fn-gidx-put (list "fn.two" 71 "<tgn-two@example.invalid>")
                 *tgn-corrupt-buckets*))))

;; fn-gidx-numbers-okp-of-put-all and -of-refresh (books/owner.lisp).
(assert-event
 (and (fn-gidx-numbers-okp *tgn-old-buckets*)
      (fn-gidx-numbers-okp
       (fn-gidx-put-all (fn-index-article-entries *tgn-c*) *tgn-old-buckets*))
      (fn-gidx-numbers-okp
       (fn-gidx-refresh *tgn-old-buckets* *tgn-old* *tgn-new*))))
(assert-event
 (and (not (fn-gidx-numbers-okp *tgn-corrupt-buckets*))
      (not (fn-gidx-numbers-okp (fn-gidx-put-all nil *tgn-corrupt-buckets*)))
      (not (fn-gidx-numbers-okp
            (fn-gidx-refresh *tgn-corrupt-buckets* *tgn-new* *tgn-new*)))))
(must-fail
 (defthm fn-tgn-put-all-without-relation
   (fn-gidx-numbers-okp (fn-gidx-put-all nil *tgn-corrupt-buckets*))))
(must-fail
 (defthm fn-tgn-refresh-without-relation
   (fn-gidx-numbers-okp
    (fn-gidx-refresh *tgn-corrupt-buckets* *tgn-new* *tgn-new*))))

;; fn-nntp-over-range-indexed-is-walk: the served OVER equals the walk's
;; on the refreshed buckets (reachable), rows found; not on the corrupted.
(defconst *tgn-state*
  (fn-make-state *tgn-groups*
                 (list (cons "fn.one" 2147483647) (cons "fn.two" 71))
                 *tgn-new* 3 nil nil))
(defconst *tgn-session*
  (fn-nntp-set-cursor (fn-nntp-open-session *tgn-state*) "fn.one" 2))
(defconst *tgn-range* (fn-nntp-string-octets "1-2147483647"))
(assert-event
 (and (fn-gidx-numbers-okp *tgn-new-buckets*)
      (equal (fn-nntp-over-range-indexed *tgn-session* *tgn-new-buckets*
                                         *tgn-trie* *tgn-range* nil)
             (fn-nntp-over-range-walk *tgn-session* *tgn-new-buckets*
                                      *tgn-trie* *tgn-range* nil))
      (equal (len (fn-nov-lines-for-numbers-numbered
                   '(2 3 2147483647)
                   (fn-gidx-bucket-numbers "fn.one" *tgn-new-buckets*)
                   *tgn-trie*))
             3)))
(assert-event
 (and (not (fn-gidx-numbers-okp *tgn-corrupt-buckets*))
      (not (equal (fn-nntp-over-range-indexed *tgn-session* *tgn-corrupt-buckets*
                                              *tgn-trie* *tgn-range* nil)
                  (fn-nntp-over-range-walk *tgn-session* *tgn-corrupt-buckets*
                                           *tgn-trie* *tgn-range* nil)))))
(must-fail
 (defthm fn-tgn-over-range-without-relation
   (equal (fn-nntp-over-range-indexed *tgn-session* *tgn-corrupt-buckets*
                                      *tgn-trie* *tgn-range* nil)
          (fn-nntp-over-range-walk *tgn-session* *tgn-corrupt-buckets*
                                   *tgn-trie* *tgn-range* nil))))
