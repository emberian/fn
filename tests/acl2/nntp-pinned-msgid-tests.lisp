; Teeth for books/nntp-pinned-msgid.lisp.
(in-package "ACL2")
(include-book "../../books/nntp-pinned-msgid")
(include-book "std/testing/must-fail" :dir :system)

(defconst *npm-t-id* "<Case@Id.invalid>")
(defconst *npm-t-payload*
  '(77 101 115 115 97 103 101 45 73 68 58 32 60 67 97 115 101 64 73 100 46 105 110 118 97 108 105 100 62 13 10
    83 117 98 106 101 99 116 58 32 84 101 115 116 13 10 13 10
    72 101 108 108 111 13 10 46 100 111 116 13 10))
(defconst *npm-t-archive*
  (fn-accept-complete
   (fn-accept-prepare (fn-initial-state '("fn.letters" "fn.empty")) 1
                      *npm-t-id* *npm-t-payload* '("fn.letters") 841000000)
   0 1 :durable))
(defconst *npm-t-session* (fn-nntp-open-session *npm-t-archive*))
(defconst *npm-t-trie* (fn-midx-build (fn-state-articles *npm-t-archive*)))
(defconst *npm-t-stat* (fn-nntp-string-octets "STAT"))
(defconst *npm-t-article* (fn-nntp-string-octets "ARTICLE"))
(defconst *npm-t-arg* (list (fn-nntp-string-octets *npm-t-id*)))

(defmacro npm-t-pinned (index keyword args)
  `(fn-nntp-archive-command-pinned *npm-t-session* *npm-t-archive* ,index nil
                                   nil ,keyword ,args))
(defmacro npm-t-scan (keyword args)
  `(fn-nntp-archive-command *npm-t-session* *npm-t-archive* nil ,keyword ,args))

; Reachable, non-degenerate witness: one accepted article, its trie, and
; STAT / ARTICLE by its Message-ID answer 223 / 220 through the pinned trie,
; and exactly what the scanning dispatcher answers.
(assert-event (fn-statep *npm-t-archive*))
(assert-event (equal (fn-nntp-session-projected *npm-t-session*) t))
(assert-event (fn-midx-correspondencep *npm-t-trie*
                                       (fn-state-articles *npm-t-archive*)))
(assert-event (equal (npm-t-pinned *npm-t-trie* *npm-t-stat* *npm-t-arg*)
                     (npm-t-scan *npm-t-stat* *npm-t-arg*)))
(assert-event (equal (npm-t-pinned *npm-t-trie* *npm-t-article* *npm-t-arg*)
                     (npm-t-scan *npm-t-article* *npm-t-arg*)))
(assert-event (not (equal (npm-t-pinned *npm-t-trie* *npm-t-stat* *npm-t-arg*)
                          (npm-t-pinned *npm-t-trie* *npm-t-stat*
                                        (list (fn-nntp-string-octets
                                               "<absent@Id.invalid>"))))))

; Hypothesis 1, the correspondence.  A trie that is not the build of the
; archive (here the empty one) answers 430 where the scan answers 223.
(assert-event (not (equal (npm-t-pinned nil *npm-t-stat* *npm-t-arg*)
                          (npm-t-scan *npm-t-stat* *npm-t-arg*))))
(must-fail
 (defthm npm-t-false-without-correspondence
   (implies (fn-nntp-keywordp keyword "STAT")
            (equal (fn-nntp-archive-command-pinned
                    session archive index verdicts env keyword args)
                   (fn-nntp-archive-command session archive env keyword args)))))

; Hypothesis 2, the keyword.  The pinned dispatcher is not the scan on
; every keyword: HDR :fn-verified is answered from the pinned verdicts.
(defconst *npm-t-hdr* (fn-nntp-string-octets "HDR"))
(defconst *npm-t-hdr-args* (list (fn-nntp-string-octets ":fn-verified")
                                 (fn-nntp-string-octets *npm-t-id*)))
(assert-event (not (equal (npm-t-pinned *npm-t-trie* *npm-t-hdr* *npm-t-hdr-args*)
                          (npm-t-scan *npm-t-hdr* *npm-t-hdr-args*))))
(must-fail
 (defthm npm-t-false-without-keyword
   (implies (fn-midx-correspondencep (fn-gidx-pin-trie index)
                                     (fn-state-articles archive))
            (equal (fn-nntp-archive-command-pinned
                    session archive index verdicts env keyword args)
                   (fn-nntp-archive-command session archive env keyword args)))))
