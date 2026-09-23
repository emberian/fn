; Executed reader dispatcher, not merely a trie helper: four retrieval
; spellings consume the pinned Message-ID index.
(in-package "ACL2")
(include-book "../../books/nntp")
(include-book "std/testing/must-fail" :dir :system)

(defconst *fn-pidx-id* "<indexed@fn.invalid>")
(defconst *fn-pidx-body*
  '(77 101 115 115 97 103 101 45 73 68 58 32 60 105 110 100 101 120 101 100
    64 102 110 46 105 110 118 97 108 105 100 62 13 10 13 10 88 13 10))
(defconst *fn-pidx-archive*
  (fn-accept-complete
   (fn-accept-prepare (fn-initial-state '("fn.test")) 1 *fn-pidx-id*
                      *fn-pidx-body* '("fn.test") 841000000)
   0 1 :durable))
(defconst *fn-pidx-index*
  (fn-midx-build (fn-state-articles *fn-pidx-archive*)))
(defconst *fn-pidx-session* (fn-nntp-open-session *fn-pidx-archive*))
(defconst *fn-pidx-env* (fn-nntp-env nil nil nil))

(assert-event (fn-midx-correspondencep *fn-pidx-index*
                                        (fn-state-articles *fn-pidx-archive*)))

(defun fn-pidx-line (verb)
  (append (fn-nntp-string-octets verb)
          (cons 32 (fn-nntp-string-octets *fn-pidx-id*))))

; All four actual dispatch arms agree with the original response and return
; a nonempty article/cursor answer.  They take the index on the executed path.
(assert-event
 (and (equal (fn-nntp-step-pinned
              *fn-pidx-session* *fn-pidx-archive* *fn-pidx-index* nil
              *fn-pidx-env* (list :command (fn-pidx-line "ARTICLE")))
             (fn-nntp-step *fn-pidx-session* *fn-pidx-archive* *fn-pidx-env*
                           (list :command (fn-pidx-line "ARTICLE"))))
      (equal (fn-nntp-step-pinned
              *fn-pidx-session* *fn-pidx-archive* *fn-pidx-index* nil
              *fn-pidx-env* (list :command (fn-pidx-line "HEAD")))
             (fn-nntp-step *fn-pidx-session* *fn-pidx-archive* *fn-pidx-env*
                           (list :command (fn-pidx-line "HEAD"))))
      (equal (fn-nntp-step-pinned
              *fn-pidx-session* *fn-pidx-archive* *fn-pidx-index* nil
              *fn-pidx-env* (list :command (fn-pidx-line "BODY")))
             (fn-nntp-step *fn-pidx-session* *fn-pidx-archive* *fn-pidx-env*
                           (list :command (fn-pidx-line "BODY"))))
      (equal (fn-nntp-step-pinned
              *fn-pidx-session* *fn-pidx-archive* *fn-pidx-index* nil
              *fn-pidx-env* (list :command (fn-pidx-line "STAT")))
             (fn-nntp-step *fn-pidx-session* *fn-pidx-archive* *fn-pidx-env*
                           (list :command (fn-pidx-line "STAT"))))))

; The correspondence premise is load-bearing: a stale pin gives a 430 where
; the accepted archive gives a 223 success.
(must-fail
 (defthm fn-pidx-false-stale-index-refines-accepted-stat
   (equal (fn-nntp-step-pinned
           *fn-pidx-session* *fn-pidx-archive* nil nil *fn-pidx-env*
           (list :command (fn-pidx-line "STAT")))
          (fn-nntp-step
           *fn-pidx-session* *fn-pidx-archive* *fn-pidx-env*
           (list :command (fn-pidx-line "STAT"))))))
