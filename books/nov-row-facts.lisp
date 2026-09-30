; Read the already-selected OVER row's cached facts without searching its
; Message-ID history. PRF-1066 component; served cursor integration remains open.
(in-package "ACL2")
(include-book "nov-row-facts-model")
(include-book "nov-column-window")
(include-book "nov-row-capture")



; The selection predicate is deliberately separate: a caller cannot infer
; visibility or group membership merely from the existence of these facts.


(local
 (defthm fn-nrf-ok-has-facts
   (implies (fn-hnov-ok (fn-hf-nov facts)) facts)
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-hf-nov fn-hnov-ok)))))

; A fixed set of immutable cached references denotes the exact article row.
; Numeric setup in fn-nbw-column-pieces remains subject to the separate
; resumable-decimal/profile integration obligation.
(defthm fn-nrf-column-pieces-refine-row
  (implies (and (fn-scol-okp fn-arena fn-cat)
                (fn-hnov-ok (fn-hf-nov (fn-nrf-facts seq fn-cat)))
                (equal (fn-article-payload article)
                       (fn-record-payload (fn-cat-at seq fn-cat))))
           (equal (fn-nbw-remaining
                   (fn-nbw-column-pieces
                    number (fn-nrf-facts seq fn-cat)
                    (fn-nntp-article-length article fn-arena)) 0)
                  (append (fn-nov-line number (fn-nov-overview article fn-arena))
                          '(13 10))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-nbw-column-pieces-are-complete-row
                            (facts (fn-nrf-facts seq fn-cat)))
                 (:instance fn-nrf-facts-are-row-bytes-facts)
                 (:instance fn-nrf-facts-handle)
                 (:instance fn-nrf-ok-has-facts (facts (fn-nrf-facts seq fn-cat)))
                 (:instance fn-hnov-p-of-hnov-of
                            (bytes (fn-nntp-article-bytes article fn-arena)))
                 (:instance fn-scol-nov-overview-of-bytes-facts))
           :in-theory
           (e/d (fn-nntp-article-bytes)
                (fn-nbw-column-pieces-are-complete-row
                 fn-nrf-facts-are-row-bytes-facts fn-scol-nov-overview-of-bytes-facts
                 fn-hnov-p-of-hnov-of fn-scol-okp fn-nrf-facts
                 fn-hf-nov fn-hnov-p fn-hnov-of fn-nntp-payload-bytes
                 fn-nbw-column-pieces fn-nbw-remaining fn-nov-line
                 fn-scol-nov-overview fn-nov-overview fn-held-facts-of
                 fn-nntp-article-length fn-cat-at-is-nth)))))
