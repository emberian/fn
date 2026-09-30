(in-package "ACL2")
(include-book "../../books/checkpoint-suffix-admission")
(include-book "std/testing/assert-bang" :dir :system)
; Complete reachable positives: empty initial state; a durable checkpoint
; at5 followed by3 accepted records; the next POST fills the fourth slot.
(assert! (and (equal (fn-csa-post-admission nil 0 2) :ok)
              (natp 0) (posp 2) (<= (nfix nil) 0)
              (<= (- (+ 1 0) (nfix nil)) (* 2 2))))
(assert! (and (equal (fn-csa-post-admission 5 8 2) :ok)
              (natp 8) (posp 2) (<= (nfix 5) 8)
              (<= (- (+ 1 8) (nfix 5)) (* 2 2))))
; Hypothesis removal: actual exhausted state, no omitted-state assumption.
(assert! (and (not (equal (fn-csa-post-admission 5 9 2) :ok))
              (not (and (natp 9) (posp 2) (<= (nfix 5) 9)
                        (<= (- (+ 1 9) (nfix 5)) (* 2 2))))))
; Complete positive of the literal refused theorem.
(assert! (and (natp 9) (posp 2) (< (* 2 2) (- (+ 1 9) (nfix 5)))
              (equal (fn-csa-post-admission 5 9 2) :checkpoint-deferred)))
; Hypothesis-removal witness for the sole inequality hypothesis. The
; stronger theorem needs no separate natp/posp hypotheses.
(assert! (and (natp 8) (posp 2) (not (< (* 2 2) (- (+ 1 8) (nfix 5))))
              (not (equal (fn-csa-post-admission 5 8 2) :checkpoint-deferred))))
; New durable checkpoint frees the same previously refused next POST.
(assert! (equal (fn-csa-post-admission 9 9 2) :ok))
; Separately labeled corrupted-state/malformed-profile cases.
(assert! (equal (fn-csa-post-admission 10 9 2) :checkpoint-deferred))
(assert! (equal (fn-csa-post-admission 5 9 0) :checkpoint-deferred))
