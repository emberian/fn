; Teeth for the NNTP session keystone.
;
; `fn-nntp-step-preserves-consistent-session' (books/nntp-invariants.lisp:786)
; is the reader's one-step safety property: a session whose selected group and
; article cursor exist in the archive still does after any wire event.  It now
; has a single hypothesis: the archive-configuration hypothesis it used to
; carry was removed when the verdict moved into the session (the review's D3),
; so the teeth below are all for that one hypothesis and each separates a
; different clause of `fn-nntp-session-consistentp'.

(in-package "ACL2")
(include-book "../../books/nntp-invariants")
(include-book "std/testing/must-fail" :dir :system)

; This book reasons about the NNTP transitions themselves, so it opens the
; vocabularies the five books of the nntp cluster withdraw at their export
; events (2026-09-19 split of books/nntp.lisp).
(local (in-theory (enable fn-nntp-syntax-vocabulary fn-nntp-session-vocabulary fn-nntp-projection-vocabulary fn-nntp-responses-vocabulary fn-nntp-vocabulary)))
; The reader environment every transcript below runs against: one wall clock
; reading (2026-09-19T12:34:56Z as DTN milliseconds) and one persisted group
; creation fact.  No transcript lets the reader invent either.
(defconst *fn-nntp-obs0*
  (fn-clock-observation 1000 843136496000 1000 t))
(defconst *fn-nntp-blind-obs*
  (fn-clock-observation 1000 0 0 nil))
(defconst *fn-nntp-facts0*
  (list (fn-nntp-group-fact "fn.letters" 0 *fn-nntp-blind-obs*)
        (fn-nntp-group-fact "fn.empty" 811728000000 *fn-nntp-blind-obs*)))
(defconst *fn-nntp-env0* (fn-nntp-env *fn-nntp-obs0* *fn-nntp-facts0* nil))
(defconst *fn-nntp-blind-env* (fn-nntp-env *fn-nntp-blind-obs* nil nil))
(assert-event (fn-nntp-envp *fn-nntp-env0*))
(assert-event (fn-nntp-envp *fn-nntp-blind-env*))

; -----------------------------------------------------------------------------
; A reachable, non-degenerate witness: a real archive with one committed
; article in one of two configured groups, so that a consistent session has
; something to be consistent about and an empty group exists to distinguish
; "group known" from "group has articles".

(defconst *nnt-groups* '("fn.letters" "fn.empty"))
(defconst *nnt-id* "<Case@Id.invalid>")
(defconst *nnt-payload*
  '(77 101 115 115 97 103 101 45 73 68 58 32 60 67 97 115 101 64 73 100 46
    105 110 118 97 108 105 100 62 13 10
    83 117 98 106 101 99 116 58 32 84 101 115 116 13 10 13 10
    72 101 108 108 111 13 10 46 100 111 116 13 10))
(defconst *nnt-archive*
  (fn-accept-complete
   (fn-accept-prepare (fn-initial-state *nnt-groups*) 1 *nnt-id* *nnt-payload*
                      '("fn.letters") 841000000)
   0 1 :durable))

(assert-event (fn-statep *nnt-archive*))
(assert-event (fn-nntp-projectionp *nnt-archive*))
(assert-event (equal (len (fn-state-articles *nnt-archive*)) 1))

; GROUP selects, and the selected session is consistent: group present, cursor
; at an article that exists.
(defconst *nnt-selected*
  (fn-nntp-result-session
   (fn-nntp-step (fn-nntp-open-session *nnt-archive*) *nnt-archive* *fn-nntp-env0*
                 '(:command (103 82 111 85 112 32 102 110 46 108 101 116 116
                             101 114 115)))))
(assert-event (equal (fn-nntp-session-group *nnt-selected*) "fn.letters"))
(assert-event (equal (fn-nntp-session-current *nnt-selected*) 1))
(assert-event (fn-nntp-session-consistentp *nnt-selected* *nnt-archive*))

; Non-degenerate: the empty group is selectable and leaves no cursor, so a
; session predicate that conflated "no group" with "no articles" would not
; separate these two consistent sessions.
(defconst *nnt-empty-selected*
  (fn-nntp-result-session
   (fn-nntp-step *nnt-selected* *nnt-archive* *fn-nntp-env0*
                 '(:command (71 82 79 85 80 32 102 110 46 101 109 112 116 121)))))
(assert-event (equal (fn-nntp-session-group *nnt-empty-selected*) "fn.empty"))
(assert-event (null (fn-nntp-session-current *nnt-empty-selected*)))
(assert-event (fn-nntp-session-consistentp *nnt-empty-selected* *nnt-archive*))

; The keystone holds across a step from the consistent witness.
(assert-event
 (fn-nntp-session-consistentp
  (fn-nntp-result-session
   (fn-nntp-step *nnt-selected* *nnt-archive* *fn-nntp-env0* '(:command (72 69 65 68))))
  *nnt-archive*))

; -----------------------------------------------------------------------------
; Teeth for `fn-nntp-step-preserves-consistent-session'
;   (implies (fn-nntp-session-consistentp session archive)        ; H1
;            (fn-nntp-session-consistentp
;             (fn-nntp-result-session (fn-nntp-step session archive *fn-nntp-env0* wire-event))
;             archive))

; H1 dropped.  A well-typed session that names a group the archive does not
; configure is inconsistent, and a command the dispatcher does not recognise
; leaves it exactly as it was: the step neither repairs nor detects it.  This
; is why the invariant has to be established at session creation and carried,
; not recomputed.
(defconst *nnt-forged-session* (list t "fn.unknown" nil t))
(assert-event (fn-nntp-sessionp *nnt-forged-session*))
(assert-event (not (fn-nntp-session-consistentp *nnt-forged-session* *nnt-archive*)))
(assert-event
 (not (fn-nntp-session-consistentp
       (fn-nntp-result-session
        (fn-nntp-step *nnt-forged-session* *nnt-archive* *fn-nntp-env0*
                      '(:command (88 89 90 90 89))))
       *nnt-archive*)))

(local
 (must-fail
  (defthm nnt-teeth-step-without-a-consistent-session
    (fn-nntp-session-consistentp
     (fn-nntp-result-session
      (fn-nntp-step *nnt-forged-session* *nnt-archive* *fn-nntp-env0*
                    '(:command (88 89 90 90 89))))
     *nnt-archive*))))

; A second inconsistency, this time in the cursor rather than the group, so the
; case does not rest on one clause of `fn-nntp-session-consistentp'.
(defconst *nnt-stale-cursor* (list t "fn.letters" 99 t))
(assert-event (not (fn-nntp-session-consistentp *nnt-stale-cursor* *nnt-archive*)))
(assert-event
 (not (fn-nntp-session-consistentp
       (fn-nntp-result-session
        (fn-nntp-step *nnt-stale-cursor* *nnt-archive* *fn-nntp-env0*
                      '(:command (88 89 90 90 89))))
       *nnt-archive*)))

(local
 (must-fail
  (defthm nnt-teeth-step-without-a-valid-cursor
    (fn-nntp-session-consistentp
     (fn-nntp-result-session
      (fn-nntp-step *nnt-stale-cursor* *nnt-archive* *fn-nntp-env0*
                    '(:command (88 89 90 90 89))))
     *nnt-archive*))))

; There is no second hypothesis any more.  The old statement also assumed
; `(fn-nntp-projectionp archive)', which did no work: `fn-nntp-step' re-ran the
; whole-archive recognizer on every command and answered 503 without touching
; the session when it failed, so a non-projectable archive made the step a
; session no-op and the conclusion followed from H1 alone.  That recomputation
; was the review's D3.  `fn-nntp-step' no longer mentions
; `fn-nntp-projectionp'; the verdict is decided once by `fn-nntp-open-session'
; and carried in the session's fourth field, and the third witness below keeps
; that field true so the forged inconsistency is in the group and the cursor,
; not in the carried verdict.  The statement is therefore strictly stronger
; than the one these teeth were first written against.
;
; Teeth for the carried verdict itself, for the effect grammar and for the
; GROUP cursor keystone live in tests/acl2/nntp-tests.lisp.
