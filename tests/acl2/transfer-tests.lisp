; Executable scenarios for the bounded resumable transfer staging kernel.

(in-package "ACL2")
(include-book "../../books/transfer")

(defconst *fn-transfer-profile*
  (fn-transfer-make-profile 12 8 4 3 3 4))
(defconst *fn-transfer-empty-label* '(9))
(defconst *fn-transfer-label* '(1 2))
(defconst *fn-transfer-other-label* '(3))
(defconst *fn-transfer-initial*
  (fn-transfer-initial-state *fn-transfer-profile*))

(assert-event (fn-transfer-statep *fn-transfer-initial*))

; The declared length consumes capacity before any bytes arrive.  An empty
; declaration is explicit and produces an unverified empty candidate only.
(defconst *fn-transfer-empty-result*
  (fn-transfer-reserve *fn-transfer-initial* *fn-transfer-empty-label* 0))
(assert-event (equal (fn-transfer-result-outcome *fn-transfer-empty-result*) :reserved))
(assert-event (equal (fn-transfer-result-candidate *fn-transfer-empty-result*)
                     '(:candidate nil)))
(assert-event (equal (fn-transfer-missing-ranges
                      (fn-transfer-result-state *fn-transfer-empty-result*)
                      *fn-transfer-empty-label*)
                     '(:ok nil)))

(defconst *fn-transfer-reserved-result*
  (fn-transfer-reserve *fn-transfer-initial* *fn-transfer-label* 6))
(defconst *fn-transfer-reserved*
  (fn-transfer-result-state *fn-transfer-reserved-result*))
(assert-event (equal (fn-transfer-result-outcome *fn-transfer-reserved-result*) :reserved))
(assert-event (equal (fn-transfer-reserved-bytes
                      (fn-transfer-state-entries *fn-transfer-reserved*))
                     6))

; Reordered fragments make progress, but the two-byte gap has no candidate.
(defconst *fn-transfer-late-result*
  (fn-transfer-add-chunk *fn-transfer-reserved* *fn-transfer-label* 4 '(5 6)))
(defconst *fn-transfer-late*
  (fn-transfer-result-state *fn-transfer-late-result*))
(assert-event (equal (fn-transfer-result-outcome *fn-transfer-late-result*) :stored))
(assert-event (not (fn-transfer-result-candidate *fn-transfer-late-result*)))
(assert-event (equal (fn-transfer-missing-ranges *fn-transfer-late*
                                               *fn-transfer-label*)
                     '(:ok ((0 1) (1 1) (2 1) (3 1)))))

(defconst *fn-transfer-first-result*
  (fn-transfer-add-chunk *fn-transfer-late* *fn-transfer-label* 0 '(1 2)))
(defconst *fn-transfer-gap*
  (fn-transfer-result-state *fn-transfer-first-result*))
(assert-event (equal (fn-transfer-missing-ranges *fn-transfer-gap*
                                               *fn-transfer-label*)
                     '(:ok ((2 1) (3 1)))))
(assert-event (not (fn-transfer-result-candidate *fn-transfer-first-result*)))

; Exact duplicate bytes/range have no effect, even after other fragments.
(defconst *fn-transfer-duplicate-result*
  (fn-transfer-add-chunk *fn-transfer-gap* *fn-transfer-label* 4 '(5 6)))
(assert-event (equal (fn-transfer-result-outcome *fn-transfer-duplicate-result*) :duplicate))
(assert-event (equal (fn-transfer-result-state *fn-transfer-duplicate-result*)
                     *fn-transfer-gap*))

; A conflicting overlap returns retained evidence and does not select a winner.
(defconst *fn-transfer-conflict-result*
  (fn-transfer-add-chunk *fn-transfer-gap* *fn-transfer-label* 1 '(99 98)))
(assert-event (equal (fn-transfer-result-outcome *fn-transfer-conflict-result*)
                     :overlap-conflict))
(assert-event (equal (fn-transfer-result-state *fn-transfer-conflict-result*)
                     *fn-transfer-gap*))
(assert-event (equal (fn-transfer-result-diagnostic *fn-transfer-conflict-result*)
                     '(:retained-overlap (0 (1 2)))))

; Filling the gap yields bytes in declared-offset order, not arrival order.
(defconst *fn-transfer-complete-result*
  (fn-transfer-add-chunk *fn-transfer-gap* *fn-transfer-label* 2 '(3 4)))
(defconst *fn-transfer-complete*
  (fn-transfer-result-state *fn-transfer-complete-result*))
(assert-event (equal (fn-transfer-result-outcome *fn-transfer-complete-result*) :stored))
(assert-event (equal (fn-transfer-result-candidate *fn-transfer-complete-result*)
                     '(:candidate (1 2 3 4 5 6))))
(assert-event (equal (fn-transfer-missing-ranges *fn-transfer-complete*
                                               *fn-transfer-label*)
                     '(:ok nil)))

; Boundary and resource failures preserve the earlier staged fragments.
(assert-event
 (equal (fn-transfer-result-outcome
         (fn-transfer-add-chunk *fn-transfer-complete* *fn-transfer-label* 6 '(7)))
        :bounds))
(assert-event
 (equal (fn-transfer-result-state
         (fn-transfer-add-chunk *fn-transfer-complete* *fn-transfer-label* 6 '(7)))
        *fn-transfer-complete*))
(assert-event
 (equal (fn-transfer-result-outcome
         (fn-transfer-add-chunk *fn-transfer-reserved* *fn-transfer-label* 0 '(1 2 3 4 5)))
        :invalid-chunk))
(assert-event
 (equal (fn-transfer-result-outcome
         (fn-transfer-reserve *fn-transfer-reserved* '(1 2 3 4) 1))
        :invalid-label))
(assert-event
 (equal (fn-transfer-result-outcome
         (fn-transfer-reserve *fn-transfer-reserved* *fn-transfer-other-label* 7))
        :capacity))

; Fragment count is bounded independently from byte length.  The third stored
; one-byte fragment reaches this profile's three-fragment limit; a fourth is
; rejected without losing the retained three.
(defconst *fn-transfer-count-result*
  (fn-transfer-reserve *fn-transfer-initial* *fn-transfer-other-label* 4))
(defconst *fn-transfer-count-0* (fn-transfer-result-state *fn-transfer-count-result*))
(defconst *fn-transfer-count-1*
  (fn-transfer-result-state
   (fn-transfer-add-chunk *fn-transfer-count-0* *fn-transfer-other-label* 0 '(10))))
(defconst *fn-transfer-count-2*
  (fn-transfer-result-state
   (fn-transfer-add-chunk *fn-transfer-count-1* *fn-transfer-other-label* 1 '(11))))
(defconst *fn-transfer-count-3*
  (fn-transfer-result-state
   (fn-transfer-add-chunk *fn-transfer-count-2* *fn-transfer-other-label* 2 '(12))))
(assert-event
 (equal (fn-transfer-result-outcome
         (fn-transfer-add-chunk *fn-transfer-count-3* *fn-transfer-other-label* 3 '(13)))
        :chunk-limit))

; A valid zero-fragment profile still permits an empty declared object, but it
; may not stage even one nonempty byte.  This is the max-chunks=0 regression.
(defconst *fn-transfer-zero-chunk-profile*
  (fn-transfer-make-profile 1 1 1 0 1 1))
(defconst *fn-transfer-zero-chunk-state*
  (fn-transfer-result-state
   (fn-transfer-reserve
    (fn-transfer-initial-state *fn-transfer-zero-chunk-profile*) '(1) 1)))
(defconst *fn-transfer-zero-chunk-result*
  (fn-transfer-add-chunk *fn-transfer-zero-chunk-state* '(1) 0 '(7)))
(assert-event (fn-transfer-statep *fn-transfer-zero-chunk-state*))
(assert-event (equal (fn-transfer-result-outcome *fn-transfer-zero-chunk-result*)
                     :chunk-limit))
(assert-event (equal (fn-transfer-result-state *fn-transfer-zero-chunk-result*)
                     *fn-transfer-zero-chunk-state*))
(assert-event (fn-transfer-statep
               (fn-transfer-result-state *fn-transfer-zero-chunk-result*)))

; Empty objects consume a reservation slot even though they charge zero bytes.
; A zero-slot profile refuses the first distinct empty label and its state
; recognizer rejects any manually constructed over-limit entry list.
(defconst *fn-transfer-zero-reservation-profile*
  (fn-transfer-make-profile 0 0 0 0 16 0))
(defconst *fn-transfer-zero-reservation-initial*
  (fn-transfer-initial-state *fn-transfer-zero-reservation-profile*))
(defconst *fn-transfer-zero-reservation-result*
  (fn-transfer-reserve *fn-transfer-zero-reservation-initial* '(1) 0))
(assert-event (fn-transfer-statep *fn-transfer-zero-reservation-initial*))
(assert-event (equal (fn-transfer-result-outcome *fn-transfer-zero-reservation-result*)
                     :reservation-limit))
(assert-event (equal (fn-transfer-result-state *fn-transfer-zero-reservation-result*)
                     *fn-transfer-zero-reservation-initial*))
(assert-event
 (not (fn-transfer-statep
       (fn-transfer-make-state
        *fn-transfer-zero-reservation-profile*
        (list (fn-transfer-make-entry '(1) 0 nil))))))

; One reservation admits one empty object and its exact replay, then refuses a
; second distinct label without overwriting the valid staged state.
(defconst *fn-transfer-one-reservation-profile*
  (fn-transfer-make-profile 0 0 0 0 16 1))
(defconst *fn-transfer-one-reservation-first*
  (fn-transfer-reserve
   (fn-transfer-initial-state *fn-transfer-one-reservation-profile*) '(1) 0))
(defconst *fn-transfer-one-reservation-state*
  (fn-transfer-result-state *fn-transfer-one-reservation-first*))
(defconst *fn-transfer-one-reservation-second*
  (fn-transfer-reserve *fn-transfer-one-reservation-state* '(2) 0))
(assert-event (equal (fn-transfer-result-outcome *fn-transfer-one-reservation-first*)
                     :reserved))
(assert-event (equal (fn-transfer-result-candidate *fn-transfer-one-reservation-first*)
                     '(:candidate nil)))
(assert-event (equal (fn-transfer-result-outcome *fn-transfer-one-reservation-second*)
                     :reservation-limit))
(assert-event (equal (fn-transfer-result-state *fn-transfer-one-reservation-second*)
                     *fn-transfer-one-reservation-state*))
(assert-event (fn-transfer-statep *fn-transfer-one-reservation-state*))
(assert-event
 (equal (fn-transfer-result-outcome
         (fn-transfer-reserve *fn-transfer-one-reservation-state* '(1) 0))
        :already-reserved))

; Opaque octets that look like Lisp syntax remain ordinary data.  Neither this
; book nor the tests invoke a reader/evaluator on incoming labels or chunks.
(defconst *fn-transfer-lisp-label* '(40 114 109 32 45 114 102 32 47 41))
(defconst *fn-transfer-lisp-profile*
  (fn-transfer-make-profile 12 8 4 3 16 3))
(defconst *fn-transfer-lisp-state*
  (fn-transfer-result-state
   (fn-transfer-reserve (fn-transfer-initial-state *fn-transfer-lisp-profile*)
                        *fn-transfer-lisp-label* 2)))
(assert-event
 (equal (fn-transfer-result-candidate
         (fn-transfer-add-chunk *fn-transfer-lisp-state* *fn-transfer-lisp-label*
                                0 '(40 41)))
        '(:candidate (40 41))))
