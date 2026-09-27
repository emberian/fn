; Teeth for books/store-profile-carried.lisp (PRF-278).
;
; The profile is the :scale preset (the one a production store is initialised
; under), the article a 2,048-octet POST in one group, as post-alloc-2's
; allocation profile measured.  The carry is what fn-owner-install-profile
; writes (fn-pvc-make of the installed profile).
(in-package "ACL2")
(include-book "../../books/store-profile-carried")

(defconst *pvct-profile* (fn-bs-config-for-profile :scale))
(defconst *pvct-dev* (fn-bs-config-for-profile :development))
(defconst *pvct-carry* (fn-pvc-make *pvct-profile*))
(defconst *pvct-record*
  (fn-record-make 1 2 3 "<pvct@example>" (make-list 2048 :initial-element 65)
                  '("fn.letters") "o" "s" "e" 4 841000000))
(defconst *pvct-msgid* (fn-record-string-octets "<pvct@example>"))

; -----------------------------------------------------------------------------
; Positive witnesses, reachable: the carry fn-owner-install-profile writes,
; the profile fn-owner-store-profile reads (the same value), a store below
; its budget.  Hypothesis and conclusion of each KEYSTONE hold, and the
; value is the admitting one (not the 0 / :unaffordable / refusal every
; unadmitted profile gives).

(assert-event (fn-bs-profile-admittedp *pvct-profile*))
(assert-event (fn-pvc-carryp *pvct-carry*))

; fn-pvc-article-budget-carried-is-cvec-article-budget-for
(assert-event
 (let ((carried (fn-pvc-article-budget-carried *pvct-carry* *pvct-profile*
                                               10 100000 *pvct-record* 1))
       (logical (fn-cvec-article-budget-for *pvct-profile* 10 100000
                                            *pvct-record* 1)))
   (and (equal carried logical)
        (equal carried 4096))))

; fn-pvc-verdict-carried-is-cvec-verdict-at, for every kind with a ceiling
; and one without.
(assert-event
 (let ((kinds (cons :no-such-kind *fn-bs-profile-event-kinds*)))
   (and (equal (fn-pvc-verdict-carried *pvct-carry* *pvct-profile* :undertake
                                       10 100000 1)
               :admissible)
        (equal (fn-pvc-verdict-carried *pvct-carry* *pvct-profile* :release
                                       10 100000 1)
               (fn-cvec-verdict-at *pvct-profile* :release 10 100000 1))
        (equal (fn-pvc-verdict-carried *pvct-carry* *pvct-profile* (nth 0 kinds)
                                       10 100000 1)
               (fn-cvec-verdict-at *pvct-profile* (nth 0 kinds) 10 100000 1))
        (equal (fn-pvc-verdict-carried *pvct-carry* *pvct-profile* :consumer
                                       10 100000 1)
               (fn-cvec-verdict-at *pvct-profile* :consumer 10 100000 1)))))

; fn-pvc-post-boundary-carried-is-sbud-post-boundary: :ok, and each refusal.
(assert-event
 (and (equal (fn-pvc-post-boundary-carried *pvct-carry* *pvct-profile*
                                           *pvct-msgid* 2048 1 3)
             :ok)
      (equal (fn-sbud-post-boundary *pvct-profile* *pvct-msgid* 2048 1 3) :ok)
      (equal (fn-pvc-post-boundary-carried *pvct-carry* *pvct-profile*
                                           *pvct-msgid* 40000 1 3)
             (fn-sbud-post-boundary *pvct-profile* *pvct-msgid* 40000 1 3))
      (equal (fn-pvc-post-boundary-carried *pvct-carry* *pvct-profile*
                                           *pvct-msgid* 40000 1 3)
             :payload-bound)
      (equal (fn-pvc-post-boundary-carried *pvct-carry* *pvct-profile*
                                           *pvct-msgid* 2048 70000 3)
             :group-bound)))

; At the budget: the carried budget and the logical one are both 0 (the
; count gate), and the verdict :unaffordable.
(assert-event
 (and (equal (fn-pvc-article-budget-carried *pvct-carry* *pvct-profile*
                                            4096 100000 *pvct-record* 0)
             (fn-cvec-article-budget-for *pvct-profile* 4096 100000
                                         *pvct-record* 0))
      (equal (fn-pvc-verdict-carried *pvct-carry* *pvct-profile* :undertake
                                     4096 100000 0)
             :unaffordable)))

; Before a profile is installed (the recovery reset): the carry is NIL, which
; satisfies the recognizer, and the answers are the unadmitted ones.
(assert-event
 (and (fn-pvc-carryp nil)
      (equal (fn-pvc-article-budget-carried nil nil 0 0 *pvct-record* 0) 0)
      (equal (fn-cvec-article-budget-for nil 0 0 *pvct-record* 0) 0)
      (equal (fn-pvc-post-boundary-carried nil nil *pvct-msgid* 2048 1 3)
             :payload-bound)))

; A carry that names another profile (not reachable in composition: the
; carry and the profile are installed together) is still correct: the reader
; decides afresh.
(assert-event
 (and (fn-pvc-carryp (fn-pvc-make *pvct-dev*))
      (equal (fn-pvc-article-budget-carried (fn-pvc-make *pvct-dev*)
                                            *pvct-profile* 10 100000
                                            *pvct-record* 1)
             4096)))

; -----------------------------------------------------------------------------
; Hypothesis-removal witness (the KEYSTONES' one hypothesis, fn-pvc-carryp).
; CORRUPTED STATE, not reachable: the carry names the admitted profile with
; the verdict NIL.  The recognizer fails; the conclusion fails with it (the
; carried budget is 0, the logical one 4096; the boundary refuses a POST the
; profile admits; the verdict refuses an admissible undertaking).

(defconst *pvct-bad* (cons *pvct-profile* nil))

(assert-event
 (and (not (fn-pvc-carryp *pvct-bad*))
      (not (equal (fn-pvc-article-budget-carried *pvct-bad* *pvct-profile*
                                                 10 100000 *pvct-record* 1)
                  (fn-cvec-article-budget-for *pvct-profile* 10 100000
                                              *pvct-record* 1)))
      (not (equal (fn-pvc-post-boundary-carried *pvct-bad* *pvct-profile*
                                                *pvct-msgid* 2048 1 3)
                  (fn-sbud-post-boundary *pvct-profile* *pvct-msgid* 2048 1 3)))
      (not (equal (fn-pvc-verdict-carried *pvct-bad* *pvct-profile* :undertake
                                          10 100000 1)
                  (fn-cvec-verdict-at *pvct-profile* :undertake 10 100000 1)))))

; MUTATION witness: the opposite corruption (an unadmitted profile carried
; as admitted) would admit what the profile refuses.  The profile is the
; scale preset with its format text damaged.
(defconst *pvct-damaged* (cons (list 0) (cdr *pvct-profile*)))
(defconst *pvct-lie* (cons *pvct-damaged* t))

(assert-event
 (and (not (fn-bs-profile-admittedp *pvct-damaged*))
      (not (fn-pvc-carryp *pvct-lie*))
      (equal (fn-cvec-article-budget-for *pvct-damaged* 10 100000
                                         *pvct-record* 1)
             0)
      (not (equal (fn-pvc-article-budget-carried *pvct-lie* *pvct-damaged*
                                                 10 100000 *pvct-record* 1)
                  0))))
