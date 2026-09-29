; store-number-projection.lisp -- the served projection recognizer from the
; Store's facts once the whole-archive article count left it (lane
; join-f2-615, 2026-09-28; PKT-615).  books/store-number-bound.lisp keeps the
; watermarks within RFC 3977 section 6's bound by admission; this book says
; that is all fn-nntp-projectionp still asks beyond the state and its group
; names.
;
; Shares the prefix `fn-snb-' with books/store-number-bound.lisp.

(in-package "ACL2")

(include-book "store-number-bound")

; -----------------------------------------------------------------------------
; The projection recognizer, with the whole-archive count gone, is the
; archive's state, its served group names and its watermarks: the last is
; what the admission keeps, so no served step counts articles.
(defthm fn-snb-projectionp-unfolds
  (equal (fn-nntp-projectionp archive)
         (and (fn-statep archive)
              (fn-nntp-safe-group-listp (fn-state-groups archive))
              (fn-nntp-nexts-boundedp (fn-state-nexts archive))))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-nntp-projectionp))))

; KEYSTONE (the served projection from the Store's facts): the acceptance
; state a history of admitted records replays to is a projection exactly
; when it is a state whose group names are servable -- the article count
; is no longer asked, and the watermarks are the admission's.
(defthm fn-snb-replayed-acceptance-is-projection
  (let ((a (fn-node-acceptance (fn-replay-result-node (fn-replay groups capacity records)))))
    (implies (and (fn-snb-history-fitp (fn-node-initial-state groups capacity) records)
                  (fn-statep a)
                  (fn-nntp-safe-group-listp (fn-state-groups a)))
             (fn-nntp-projectionp a)))
  :hints (("Goal" :in-theory '(fn-nntp-projectionp)
           :use (fn-snb-replay-keeps-nexts-bounded))))


