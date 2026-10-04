; Teeth for the io step family's O(1) guard (lane carrier S1, 2026-10-04;
; planning/design/owner-carrier-2026-10-04.md section 7).
;
; Before S1 every fn-sf io step was (if (and (mbe :logic (fn-sf-statep s) :exec
; t) PHASE-TEST) STEP s): logically the identity off the invariant, and its guard
; therefore the whole-log walk fn-sf-statep, forced up the chain to fn-owner-io
; where the executable counterpart evaluated it once per call (COST-GATE: 92 ms
; and 11.8 MB per call at 1,000 articles).  After S1 the io steps are
; unconditional under the O(1) guard fn-sf-countersp.  These are the teeth:
;
; T1  the identity off the invariant is GONE and observable: a state that is
;     countersp but not statep, in phase :ready, is stepped to :frontier-staged;
; T2  world facts: the guards of the io steps, fn-sn-file-step, fn-sn-io,
;     their concrete twins and the owner layers up to fn-olr-ocfg-reserve and
;     -order mention no whole-log predicate (fn-owner-io's own guard is
;     checked the same way where it is defined, host/owner-retain-host.lisp);
; T3  countersp is satisfiable (the initial state) and strictly weaker than
;     statep (T1's witness), so the preservation theorems' hypothesis is not
;     vacuous and the guard is not a disguised statep.

(in-package "ACL2")
(include-book "../../books/records-concrete")
(include-book "../../books/owner-log-route") ; the owner layers of the chain
(include-book "../../books/codec-attach")

; T3 / T1's witness: the initial state with one barrier too many
; (fn-sf-statep bounds the count by *fn-sf-recovery-barrier-count*).
; countersp, not statep.
(defconst *sfc-junk*
  (fn-sf-make :ready 0 nil nil nil nil nil (1+ *fn-sf-recovery-barrier-count*)))
(assert-event (fn-sf-countersp *sfc-junk*))
(assert-event (not (fn-sf-statep *sfc-junk*)))
(assert-event (fn-sf-countersp (fn-sf-initial-state)))
(assert-event (fn-sf-statep (fn-sf-initial-state)))

; T1: the step steps.  Before S1 this was (equal (fn-sf-start-frontier *sfc-junk*) *sfc-junk*).
(assert-event (equal (fn-sf-phase (fn-sf-start-frontier *sfc-junk*)) :frontier-staged))
(assert-event (not (equal (fn-sf-start-frontier *sfc-junk*) *sfc-junk*)))
; and the same through the store-node and concrete dispatchers
(assert-event (equal (fn-sf-phase (fn-sn-file-step *sfc-junk* :start-frontier nil)) :frontier-staged))
(assert-event (equal (fn-sf-phase (fn-rcon-sn-file-step *sfc-junk* :start-frontier nil)) :frontier-staged))

; T2: the guards, read from the world.
(defun sfc-guard-fns (fn state)
  (declare (xargs :mode :program :stobjs state))
  (all-fnnames (guard fn nil (w state))))
(defconst *sfc-whole-log*
  '(fn-sf-statep fn-sn-statep fn-sf-record-listp fn-sf-success-listp
    fn-sf-record-list-walkp fn-sf-success-listp-fill fn-sf-shapep fn-sn-shapep
    fn-node-statep))
(defun sfc-bad-guards (fns state)
  (declare (xargs :mode :program :stobjs state))
  (if (endp fns) nil
    (if (intersectp-eq (sfc-guard-fns (car fns) state) *sfc-whole-log*)
        (cons (car fns) (sfc-bad-guards (cdr fns) state))
      (sfc-bad-guards (cdr fns) state))))
(make-event
 (let ((bad (sfc-bad-guards '(fn-sf-start-frontier fn-sf-frontier-file-result
                              fn-sf-frontier-replace-result fn-sf-frontier-dir-result
                              fn-sf-record-file-result fn-sf-record-link-result
                              fn-sf-record-dir-result fn-sf-recovery-barrier
                              fn-sn-file-step fn-sn-io
                              fn-rcon-sf-record-dir-result fn-rcon-sn-file-step fn-rcon-sn-io
                              fn-rcon-own-store-io fn-rcon-ocfg-io
                              fn-olr-ocfg-reserve fn-olr-ocfg-order)
                            state)))
   (if bad
       (er soft 'sfc-t2 "whole-log predicate in the guard of ~x0" bad)
     (value '(value-triple :sfc-t2-ok)))))
; T2 names the guard's head; the head itself must be O(1): fn-sf-countersp's
; body calls nothing but natp and the two O(1) accessors.
(make-event
 (if (subsetp-eq (all-fnnames (body 'fn-sf-countersp nil (w state)))
                 '(if natp fn-sf-frontier fn-sf-barriers))
     (value '(value-triple :sfc-countersp-o1))
   (er soft 'sfc-countersp "fn-sf-countersp calls ~x0"
       (all-fnnames (body 'fn-sf-countersp nil (w state))))))
; T2's own teeth: the check names a step S1 left on the whole-log guard (the
; finish chain, S3), so an empty answer above is not a blind check.
(make-event
 (if (equal (sfc-bad-guards '(fn-sf-core-completion fn-sf-start-frontier) state)
            '(fn-sf-core-completion))
     (value '(value-triple :sfc-t2-teeth-ok))
   (er soft 'sfc-t2-teeth "the guard check does not see fn-sf-core-completion's fn-sf-statep")))

; The twins are still unconditional (the abstract and concrete side share the
; kernel steps and lost the mbe together); evaluated at the junk witness too.
(assert-event (equal (fn-rcon-sn-file-step *sfc-junk* :start-frontier nil)
                     (fn-sn-file-step *sfc-junk* :start-frontier nil)))
