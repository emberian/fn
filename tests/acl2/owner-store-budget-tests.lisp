; Teeth for books/owner-store-budget: the called article prepare refuses at
; its budget with the owner unchanged, and below it is the owner prepare.
; The owner states are the host-shaped ones of
; owner-prepare-correspondence-tests: one committed record, a second
; reservation, so the used count is 1 and budgets 0, 1, 2 are
; budget+1, budget and budget-1 relative to it.
(in-package "ACL2")
(include-book "../../books/owner-store-budget")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *osbt-groups* '("fn.letters" "fn.test"))
(defconst *osbt-config*
  (fn-config-replay 0 (fn-cnode-line-ceiling)
                    (list *fn-cfg-default-record*)))
(defconst *osbt-post-config*
  (fn-inj-make-config
   t '(102 110 46 111 112 99 46 105 110 118 97 108 105 100)
   (list (fn-nntp-string-octets "fn.letters")
         (fn-nntp-string-octets "fn.test"))
   32768))
(defconst *osbt-first*
  (fn-record-make 0 0 0 "<osbt-first@example.invalid>" '(65 66)
                  *osbt-groups* "osbt-pin-1" "osbt-subject-1"
                  "osbt-release-1" 2 841000000))
(defconst *osbt-second*
  (fn-record-make 1 1 1 "<osbt-second@example.invalid>" '(67 68)
                  '("fn.test") "osbt-pin-2" "osbt-subject-2"
                  "osbt-release-2" 1 841000000))

(defun osbt-run (oc events)
  (declare (xargs :guard (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
                  :verify-guards nil))
  (if (consp events)
      (osbt-run (fn-ocfg-step oc (car events)) (cdr events))
    oc))

(defconst *osbt-reserve-events*
  '((:store (:io :start-frontier nil))
    (:store (:io :frontier-file :ok))
    (:store (:io :frontier-replace :ok))
    (:store (:io :frontier-directory :ok))))
(defconst *osbt-0*
  (fn-ocfg-make
   (fn-own-configure (fn-own-start (fn-sn-initial *osbt-groups* 10) 3)
                     *osbt-post-config*)
   *osbt-config* nil nil))
(defconst *osbt-first-reserved* (osbt-run *osbt-0* *osbt-reserve-events*))
(defconst *osbt-ready-one*
  (fn-ocfg-step
   (osbt-run (fn-opc-prepare *osbt-first-reserved* *osbt-first*)
             '((:store (:io :record-file :ok))
               (:store (:io :record-link :ok))
               (:store (:io :record-directory :ok))))
   '(:complete)))
(defconst *osbt-reserved* (osbt-run *osbt-ready-one* *osbt-reserve-events*))
(defconst *osbt-staged* (fn-opc-prepare *osbt-reserved* *osbt-second*))

(assert-event (equal (fn-sbud-used (fn-sbud-oc-store *osbt-reserved*)) 1))
; The owner prepare is not degenerate here: it stages the second record.
(assert-event (not (equal *osbt-staged* *osbt-reserved*)))
(assert-event (equal (fn-sf-phase (fn-sn-files (fn-sbud-oc-store *osbt-staged*)))
                     :record-staged))

; budget 2 (used = budget-1): the same POST is prepared.
(assert-event (equal (fn-sbud-prepare *osbt-reserved* *osbt-second* 2)
                     *osbt-staged*))
; budget 1 (used = budget) and budget 0 (used = budget+1): refused, the
; owner unchanged, and the word is :unaffordable.
(assert-event (equal (fn-sbud-prepare *osbt-reserved* *osbt-second* 1)
                     *osbt-reserved*))
(assert-event (equal (fn-sbud-prepare *osbt-reserved* *osbt-second* 0)
                     *osbt-reserved*))
(assert-event (equal (fn-sbud-refusal-kind *osbt-reserved* 1) :unaffordable))
(assert-event (equal (fn-sbud-refusal-kind *osbt-reserved* 0) :unaffordable))
(assert-event (equal (fn-sbud-refusal-kind *osbt-reserved* 2) :refused))
; The refusal line the owner renders for that word.
(assert-event (equal (fn-post-store-refusal-line :unaffordable)
                     "441 posting failed; the store has no capacity for this article"))
; After the first record the development profile's budget still admits.
(assert-event (equal (fn-sbud-prepare *osbt-reserved* *osbt-second*
                                      (fn-sbud-budget
                                       (fn-bs-config-for-profile :development)
                                       :article))
                     *osbt-staged*))

;; One must-fail per hypothesis, each at the concrete owner above.
; Without "at or over the budget": budget 2 admits, and the owner moves.
(must-fail
 (defthm osbt-refuses-without-the-budget-hypothesis
   (equal (fn-sbud-prepare *osbt-reserved* *osbt-second* 2) *osbt-reserved*)))
; Without (natp budget): 3/2 exceeds the count but is no budget.
(must-fail
 (defthm osbt-below-budget-without-natp
   (equal (fn-sbud-prepare *osbt-reserved* *osbt-second* 3/2)
          (fn-opc-prepare *osbt-reserved* *osbt-second*))))
; Without "below the budget": budget 1 is the count.
(must-fail
 (defthm osbt-below-budget-without-below
   (equal (fn-sbud-prepare *osbt-reserved* *osbt-second* 1)
          (fn-opc-prepare *osbt-reserved* *osbt-second*))))
; The refusal word without "at or over the budget".
(must-fail
 (defthm osbt-unaffordable-without-the-budget-hypothesis
   (equal (fn-sbud-refusal-kind *osbt-reserved* 2) :unaffordable)))
