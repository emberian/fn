; Executed reader dispatcher, not merely a trie helper: four retrieval
; spellings consume the pinned Message-ID index.
(in-package "ACL2")
(include-book "../../books/nntp")
(include-book "must-fail-checked")

(defconst *fn-pidx-id* "<indexed@fn.invalid>")
(defconst *fn-pidx-body*
  '(77 101 115 115 97 103 101 45 73 68 58 32 60 105 110 100 101 120 101 100
    64 102 110 46 105 110 118 97 108 105 100 62 13 10 13 10 88 13 10))
; by specification: the flip -- the acceptance payload is a handle into the
; arena (records-flip, books/held-record.lisp); *fn-pidx-body* is interned
; first, so the article holds handle 0.
(defconst *fn-pidx-archive*
  (fn-accept-complete
   (fn-accept-prepare (fn-initial-state '("fn.test")) 1 *fn-pidx-id*
                      0 '("fn.test") 841000000)
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
(include-book "arena-lift")
;; The arena: handle 0 = *fn-pidx-body*.
(defconst *sr-arena* (list *fn-pidx-body*))
(bpr-lift fn-nntp-step 4)
(bpr-lift fn-nntp-step-pinned 6)
(assert-event
 (and (equal (in-arena-fn-nntp-step-pinned *sr-arena* *fn-pidx-session* *fn-pidx-archive* *fn-pidx-index* nil *fn-pidx-env* (list :command (fn-pidx-line "ARTICLE")))
             (in-arena-fn-nntp-step *sr-arena* *fn-pidx-session* *fn-pidx-archive* *fn-pidx-env* (list :command (fn-pidx-line "ARTICLE"))))
      (equal (in-arena-fn-nntp-step-pinned *sr-arena* *fn-pidx-session* *fn-pidx-archive* *fn-pidx-index* nil *fn-pidx-env* (list :command (fn-pidx-line "HEAD")))
             (in-arena-fn-nntp-step *sr-arena* *fn-pidx-session* *fn-pidx-archive* *fn-pidx-env* (list :command (fn-pidx-line "HEAD"))))
      (equal (in-arena-fn-nntp-step-pinned *sr-arena* *fn-pidx-session* *fn-pidx-archive* *fn-pidx-index* nil *fn-pidx-env* (list :command (fn-pidx-line "BODY")))
             (in-arena-fn-nntp-step *sr-arena* *fn-pidx-session* *fn-pidx-archive* *fn-pidx-env* (list :command (fn-pidx-line "BODY"))))
      (equal (in-arena-fn-nntp-step-pinned *sr-arena* *fn-pidx-session* *fn-pidx-archive* *fn-pidx-index* nil *fn-pidx-env* (list :command (fn-pidx-line "STAT")))
             (in-arena-fn-nntp-step *sr-arena* *fn-pidx-session* *fn-pidx-archive* *fn-pidx-env* (list :command (fn-pidx-line "STAT"))))))

; The correspondence premise is load-bearing: a stale pin gives a 430 where
; the accepted archive gives a 223 success.
(must-fail-checked
 (defthm fn-pidx-false-stale-index-refines-accepted-stat
   (equal (fn-nntp-step-pinned *fn-pidx-session* *fn-pidx-archive* nil nil *fn-pidx-env* (list :command (fn-pidx-line "STAT")) fn-arena)
          (fn-nntp-step *fn-pidx-session* *fn-pidx-archive* *fn-pidx-env* (list :command (fn-pidx-line "STAT")) fn-arena))))
