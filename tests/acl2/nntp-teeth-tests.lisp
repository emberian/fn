; Teeth for the NNTP session keystone.
;
; `fn-nntp-step-preserves-consistent-session' (books/nntp-invariants.lisp:485)
; is the reader's one-step safety property: a session whose selected group and
; article cursor exist in the archive still does after any wire event.  Two
; hypotheses; one has teeth and one does not, and the one that does not is a
; consequence of the review's D3.

(in-package "ACL2")
(include-book "../../books/nntp-invariants")
(include-book "std/testing/must-fail" :dir :system)

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
                      '("fn.letters"))
   0 1 :durable))

(assert-event (fn-statep *nnt-archive*))
(assert-event (fn-nntp-projectionp *nnt-archive*))
(assert-event (equal (len (fn-state-articles *nnt-archive*)) 1))

; GROUP selects, and the selected session is consistent: group present, cursor
; at an article that exists.
(defconst *nnt-selected*
  (fn-nntp-result-session
   (fn-nntp-step (fn-nntp-initial-session) *nnt-archive*
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
   (fn-nntp-step *nnt-selected* *nnt-archive*
                 '(:command (71 82 79 85 80 32 102 110 46 101 109 112 116 121)))))
(assert-event (equal (fn-nntp-session-group *nnt-empty-selected*) "fn.empty"))
(assert-event (null (fn-nntp-session-current *nnt-empty-selected*)))
(assert-event (fn-nntp-session-consistentp *nnt-empty-selected* *nnt-archive*))

; The keystone holds across a step from the consistent witness.
(assert-event
 (fn-nntp-session-consistentp
  (fn-nntp-result-session
   (fn-nntp-step *nnt-selected* *nnt-archive* '(:command (72 69 65 68))))
  *nnt-archive*))

; -----------------------------------------------------------------------------
; Teeth for `fn-nntp-step-preserves-consistent-session'
;   (implies (and (fn-nntp-session-consistentp session archive)  ; H1
;                 (fn-nntp-projectionp archive))                 ; H2
;            (fn-nntp-session-consistentp
;             (fn-nntp-result-session (fn-nntp-step session archive wire-event))
;             archive))

; H1 dropped.  A well-typed session that names a group the archive does not
; configure is inconsistent, and a command the dispatcher does not recognise
; leaves it exactly as it was: the step neither repairs nor detects it.  This
; is why the invariant has to be established at session creation and carried,
; not recomputed.
(defconst *nnt-forged-session* (list t "fn.unknown" nil))
(assert-event (fn-nntp-sessionp *nnt-forged-session*))
(assert-event (not (fn-nntp-session-consistentp *nnt-forged-session* *nnt-archive*)))
(assert-event
 (not (fn-nntp-session-consistentp
       (fn-nntp-result-session
        (fn-nntp-step *nnt-forged-session* *nnt-archive*
                      '(:command (88 89 90 90 89))))
       *nnt-archive*)))

(local
 (must-fail
  (defthm nnt-teeth-step-without-a-consistent-session
    (fn-nntp-session-consistentp
     (fn-nntp-result-session
      (fn-nntp-step *nnt-forged-session* *nnt-archive*
                    '(:command (88 89 90 90 89))))
     *nnt-archive*))))

; A second inconsistency, this time in the cursor rather than the group, so the
; case does not rest on one clause of `fn-nntp-session-consistentp'.
(defconst *nnt-stale-cursor* (list t "fn.letters" 99))
(assert-event (not (fn-nntp-session-consistentp *nnt-stale-cursor* *nnt-archive*)))
(assert-event
 (not (fn-nntp-session-consistentp
       (fn-nntp-result-session
        (fn-nntp-step *nnt-stale-cursor* *nnt-archive*
                      '(:command (88 89 90 90 89))))
       *nnt-archive*)))

(local
 (must-fail
  (defthm nnt-teeth-step-without-a-valid-cursor
    (fn-nntp-session-consistentp
     (fn-nntp-result-session
      (fn-nntp-step *nnt-stale-cursor* *nnt-archive*
                    '(:command (88 89 90 90 89))))
     *nnt-archive*))))

; H2, `(fn-nntp-projectionp archive)', has no teeth, and none is forged.
; `fn-nntp-step' re-runs `fn-nntp-projectionp' over the whole archive on every
; command and answers 503 without touching the session when it fails
; (books/nntp.lisp:1115-1116; the review's D3).  So a non-projectable archive
; makes the step a session no-op, and the conclusion follows from H1 alone.
; H2 is doing no work in THIS theorem; it is the availability defect D3
; describes, priced as a hypothesis.  Recorded as a finding in HANDOFF.md.
