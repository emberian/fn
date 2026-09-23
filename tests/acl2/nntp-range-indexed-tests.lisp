; Sparse, cross-posted and historically pinned OVER/XOVER range witnesses.
(in-package "ACL2")
(include-book "../../books/nntp-range-indexed-invariants")
(include-book "std/testing/must-fail" :dir :system)

(defun fn-xri-payload (id subject)
  (append (fn-nntp-string-octets "Message-ID: ")
          (fn-nntp-string-octets id) '(13 10)
          (fn-nntp-string-octets "Subject: ")
          (fn-nntp-string-octets subject) '(13 10 13 10 88 13 10)))

(defconst *xri-groups* '("fn.one" "fn.two" "fn.three"))
(defconst *xri-a*
  (fn-make-article "<xri-a@example.invalid>"
                   (fn-xri-payload "<xri-a@example.invalid>" "A")
                   '("fn.one" "fn.two")
                   (list (cons "fn.one" 2) (cons "fn.two" 70))
                   t 841000000))
(defconst *xri-b*
  (fn-make-article "<xri-b@example.invalid>"
                   (fn-xri-payload "<xri-b@example.invalid>" "B")
                   '("fn.three") (list (cons "fn.three" 9))
                   t 841000000))
(defconst *xri-c*
  (fn-make-article "<xri-c@example.invalid>"
                   (fn-xri-payload "<xri-c@example.invalid>" "C")
                   '("fn.one") (list (cons "fn.one" 100))
                   t 841000000))
(defconst *xri-old-articles* (list *xri-a* *xri-b*))
(defconst *xri-new-articles* (list *xri-a* *xri-b* *xri-c*))
(defconst *xri-nexts-old*
  (list (cons "fn.one" 3) (cons "fn.two" 71) (cons "fn.three" 10)))
(defconst *xri-nexts-new*
  (list (cons "fn.one" 101) (cons "fn.two" 71) (cons "fn.three" 10)))
(defconst *xri-old*
  (fn-make-state *xri-groups* *xri-nexts-old* *xri-old-articles* 2 nil nil))
(defconst *xri-new*
  (fn-make-state *xri-groups* *xri-nexts-new* *xri-new-articles* 3 nil nil))
(defconst *xri-session*
  (fn-nntp-set-cursor (fn-nntp-open-session *xri-new*) "fn.one" 2))
(defconst *xri-old-pin*
  (fn-gidx-pin (fn-midx-build *xri-old-articles*)
               (fn-gidx-build *xri-old-articles*)))
(defconst *xri-new-pin*
  (fn-gidx-pin (fn-midx-build *xri-new-articles*)
               (fn-gidx-build *xri-new-articles*)))
(defconst *xri-env* (fn-nntp-env nil nil nil))

(assert-event (and (fn-statep *xri-old*) (fn-statep *xri-new*)
                   (fn-nntp-sessionp *xri-session*)))
; Invalid ranges and an untagged index use the archive fallback in the
; called dispatcher.  Neither is a premise of the carried theorem.
(assert-event
 (and (equal (fn-nntp-archive-command-pinned
              *xri-session* *xri-new* *xri-new-pin* nil *xri-env*
              (fn-nntp-string-octets "OVER")
              (list (fn-nntp-string-octets "broken")))
             (fn-nntp-archive-command
              *xri-session* *xri-new* *xri-env*
              (fn-nntp-string-octets "OVER")
              (list (fn-nntp-string-octets "broken"))))
      (equal (fn-nntp-archive-command-pinned
              *xri-session* *xri-new* (fn-gidx-pin-trie *xri-new-pin*)
              nil *xri-env* (fn-nntp-string-octets "OVER")
              (list (fn-nntp-string-octets "1-100")))
             (fn-nntp-archive-command
              *xri-session* *xri-new* *xri-env*
              (fn-nntp-string-octets "OVER")
              (list (fn-nntp-string-octets "1-100"))))))
(assert-event (equal (fn-gidx-range-numbers
                      (fn-gidx-pin-buckets *xri-new-pin*) "fn.one" 1 100)
                     '(2 100)))
(assert-event (equal (len (fn-nov-lines-for-numbers-indexed
                           "fn.one" '(2 100)
                           (fn-gidx-bucket "fn.one"
                                            (fn-gidx-pin-buckets *xri-new-pin*))
                           (fn-gidx-pin-trie *xri-new-pin*))) 2))
(assert-event (equal (len (fn-nov-lines-for-numbers-indexed
                           "fn.one" '(2 100)
                           (fn-gidx-bucket "fn.one"
                                            (fn-gidx-pin-buckets *xri-old-pin*))
                           (fn-gidx-pin-trie *xri-old-pin*))) 1))
(assert-event
 (and (equal (fn-nntp-step-pinned
              *xri-session* *xri-new* *xri-new-pin* nil *xri-env*
              (list :command (fn-nntp-string-octets "OVER 1-100")))
             (fn-nntp-step *xri-session* *xri-new* *xri-env*
                           (list :command (fn-nntp-string-octets "OVER 1-100"))))
      (equal (fn-nntp-step-pinned
              *xri-session* *xri-new* *xri-new-pin* nil *xri-env*
              (list :command (fn-nntp-string-octets "XOVER 101-200")))
             (fn-nntp-step *xri-session* *xri-new* *xri-env*
                           (list :command (fn-nntp-string-octets "XOVER 101-200"))))))
(assert-event
 (and (equal (fn-nntp-archive-command-pinned
              *xri-session* *xri-new* *xri-new-pin* nil *xri-env*
              (fn-nntp-string-octets "OVER")
              (list (fn-nntp-string-octets "101-200")))
             (fn-nntp-single *xri-session* "423 no articles in that range"))
      (equal (fn-nntp-archive-command-pinned
              *xri-session* *xri-new* *xri-new-pin* nil *xri-env*
              (fn-nntp-string-octets "XOVER")
              (list (fn-nntp-string-octets "101-200")))
             (fn-nntp-single *xri-session* "420 no article(s) selected"))))

; An old bucket and a missing trie are both concrete counterexamples to
; dropping the carried correspondence premises.
(defconst *xri-stale-bucket-pin*
  (fn-gidx-pin (fn-gidx-pin-trie *xri-new-pin*)
               (fn-gidx-pin-buckets *xri-old-pin*)))
(defconst *xri-missing-trie-pin*
  (fn-gidx-pin nil (fn-gidx-pin-buckets *xri-new-pin*)))
(assert-event
 (not (equal (fn-nntp-archive-command-pinned
              *xri-session* *xri-new* *xri-stale-bucket-pin* nil *xri-env*
              (fn-nntp-string-octets "OVER")
              (list (fn-nntp-string-octets "1-100")))
             (fn-nntp-archive-command
              *xri-session* *xri-new* *xri-env*
              (fn-nntp-string-octets "OVER")
              (list (fn-nntp-string-octets "1-100"))))))
(assert-event
 (not (equal (fn-nntp-archive-command-pinned
              *xri-session* *xri-new* *xri-missing-trie-pin* nil *xri-env*
              (fn-nntp-string-octets "OVER")
              (list (fn-nntp-string-octets "1-100")))
             (fn-nntp-archive-command
              *xri-session* *xri-new* *xri-env*
              (fn-nntp-string-octets "OVER")
              (list (fn-nntp-string-octets "1-100"))))))
(must-fail
 (defthm fn-xri-without-bucket-correspondence
   (implies (and (fn-statep archive)
                 (fn-midx-correspondencep
                  (fn-gidx-pin-trie index) (fn-state-articles archive))
                 (fn-nntp-keywordp keyword "OVER"))
            (equal (fn-nntp-archive-command-pinned
                    session archive index nil nil keyword (list token))
                   (fn-nntp-archive-command
                    session archive nil keyword (list token))))
   :hints (("Goal" :do-not-induct t))))
(must-fail
 (defthm fn-xri-without-trie-correspondence
   (implies (and (fn-statep archive)
                 (fn-gidx-pin-correspondencep index archive)
                 (fn-nntp-keywordp keyword "OVER"))
            (equal (fn-nntp-archive-command-pinned
                    session archive index nil nil keyword (list token))
                   (fn-nntp-archive-command
                    session archive nil keyword (list token))))
   :hints (("Goal" :do-not-induct t))))

; Duplicate accepted IDs cannot occur in fn-statep, but show why the
; archive-validity premise of the bucket/trie-to-archive theorem matters.
; This is a malformed-state proof counterexample, never runtime evidence.
(defconst *xri-duplicate-articles*
  (list *xri-a*
        (fn-make-article "<xri-a@example.invalid>"
                         (fn-xri-payload "<xri-a@example.invalid>" "DUP")
                         '("fn.one") (list (cons "fn.one" 100))
                         t 841000000)))
(assert-event (not (fn-article-listp *xri-groups* *xri-duplicate-articles*)))
(assert-event
 (not (equal (fn-gidx-number-article
              "fn.one" 100 (fn-gidx-build *xri-duplicate-articles*)
              (fn-midx-build *xri-duplicate-articles*))
             (fn-nntp-available-article
              "fn.one" 100 *xri-duplicate-articles*))))
(defconst *xri-duplicate-state*
  (fn-make-state *xri-groups* *xri-nexts-new*
                 *xri-duplicate-articles* 3 nil nil))
(defconst *xri-duplicate-pin*
  (fn-gidx-pin (fn-midx-build *xri-duplicate-articles*)
               (fn-gidx-build *xri-duplicate-articles*)))
(assert-event
 (and (not (fn-statep *xri-duplicate-state*))
      (fn-gidx-pin-correspondencep *xri-duplicate-pin*
                                    *xri-duplicate-state*)
      (fn-midx-correspondencep
       (fn-gidx-pin-trie *xri-duplicate-pin*)
       (fn-state-articles *xri-duplicate-state*))
      (not (equal
            (fn-nntp-archive-command-pinned
             *xri-session* *xri-duplicate-state* *xri-duplicate-pin*
             nil *xri-env* (fn-nntp-string-octets "OVER")
             (list (fn-nntp-string-octets "100-100")))
            (fn-nntp-archive-command
             *xri-session* *xri-duplicate-state* *xri-env*
             (fn-nntp-string-octets "OVER")
             (list (fn-nntp-string-octets "100-100")))))))
(must-fail
 (defthm fn-xri-without-valid-archive
   (equal (fn-gidx-number-article
           group number (fn-gidx-build articles) (fn-midx-build articles))
          (fn-nntp-available-article group number articles))
   :hints (("Goal" :do-not-induct t))))
(must-fail
 (defthm fn-xri-carried-without-valid-archive
   (implies (and (fn-gidx-pin-correspondencep index archive)
                 (fn-midx-correspondencep
                  (fn-gidx-pin-trie index) (fn-state-articles archive))
                 (fn-nntp-keywordp keyword "OVER"))
            (equal (fn-nntp-archive-command-pinned
                    session archive index nil nil keyword (list token))
                   (fn-nntp-archive-command
                    session archive nil keyword (list token))))
   :hints (("Goal" :do-not-induct t))))

; The keyword scope is substantive: a pinned :FN-VERIFIED HDR reads the
; historical verdict projection, while ordinary HDR reads an article field.
(assert-event
 (not (equal
       (fn-nntp-archive-command-pinned
        *xri-session* *xri-new* *xri-new-pin* nil *xri-env*
        (fn-nntp-string-octets "HDR")
        (list (fn-nntp-string-octets ":FN-VERIFIED")))
       (fn-nntp-archive-command
        *xri-session* *xri-new* *xri-env*
        (fn-nntp-string-octets "HDR")
        (list (fn-nntp-string-octets ":FN-VERIFIED"))))))
(must-fail
 (defthm fn-xri-carried-without-over-keyword-scope
   (implies (and (fn-statep archive)
                 (fn-gidx-pin-correspondencep index archive)
                 (fn-midx-correspondencep
                  (fn-gidx-pin-trie index) (fn-state-articles archive)))
            (equal (fn-nntp-archive-command-pinned
                    session archive index verdicts env keyword (list token))
                   (fn-nntp-archive-command
                    session archive env keyword (list token))))
   :hints (("Goal" :do-not-induct t))))
