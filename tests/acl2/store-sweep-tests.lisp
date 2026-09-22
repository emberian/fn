; store-sweep-tests.lisp -- teeth for the staging sweep.
;
; The scenario is finding 5 of planning/evidence/deploy-cce4b11-2026-09-20.md:
; an uncertain publication left `.stage-1821597-850fc8a5e5a24494a2c8734e' in
; the staging directory and two recoveries reported it and collected none.

(in-package "ACL2")

(include-book "../../books/store-sweep")
(include-book "../../books/codec-attach")

(local (in-theory (enable fn-sn-staging-namep fn-sn-final-namespace-namep
                          fn-sn-sweep-enabledp fn-sn-sweep-staging)))

(defconst *ss-stage-a* '(46 115 116 97 103 101 45 49 56 50 49 53 57 55 45 56 53 48 102 99 56 97 53 101 53 97 50 52 52 57 52 97 50 99 56 55 51 52 101))
(defconst *ss-stage-b* '(46 115 116 97 103 101 45 49 56 50 49 53 57 55 45 48 48 48 48 48 48 48 48 48 48 48 48 48 48 48 48 48 48 48 48 48 48 102 102))
(defconst *ss-final*   '(48 48 48 48 48 48 48 48 48 48 48 48 48 48 48 48 48 48 48 49))
(defconst *ss-anchor*  '(46 97 110 99 104 111 114 45 49 56 50 49 53 57 55 45 56 53 48 102 99 56 97 53 101 53 97 50 52 52 57 52 97 50 99 56 55 51 52 101))
(defconst *ss-short*   '(46 115 116 97 103))

; The two namespaces, concretely.
(assert-event (fn-sn-staging-namep *ss-stage-a*))
(assert-event (not (fn-sn-staging-namep *ss-final*)))
(assert-event (not (fn-sn-staging-namep *ss-anchor*)))
(assert-event (not (fn-sn-staging-namep *ss-short*)))
(assert-event (fn-sn-final-namespace-namep *ss-final*))
(assert-event (not (fn-sn-final-namespace-namep *ss-stage-a*)))

; The host takes this bound from the ACL2 sweep interface before it enumerates
; a staging directory.  It is positive, so the boundary never silently turns
; every existing stage namespace into an empty observation.
(assert-event (equal (fn-sn-staging-observation-limit) 64))
(assert-event (< 0 (fn-sn-staging-observation-limit)))

; A store with nothing in flight: the phase fn-own-take-submission also
; requires before it lets a submission into the durable path.
(defconst *ss-ready* (fn-sn-initial nil 0))
(assert-event (fn-sn-statep *ss-ready*))
(assert-event (fn-sn-sweep-enabledp *ss-ready*))

; The witness: the deploy gate's directory, swept.  The orphan goes; the
; anchor file and a final-namespace name that should never be in staging at
; all both stay.
(assert-event
 (equal (car (fn-sn-sweep-staging *ss-ready*
                                  (list *ss-anchor* *ss-final* *ss-stage-a* *ss-stage-b*)
                                  nil))
        (list *ss-stage-a* *ss-stage-b*)))
(assert-event (equal (cdr (fn-sn-sweep-staging *ss-ready* (list *ss-stage-a*) nil))
                     *ss-ready*))

; One violating value per hypothesis of
; fn-sn-sweep-removes-only-unheld-staging-names: drop the held test and the
; live publication's own staging file goes; drop the namespace test and the
; committed record's file goes.
(assert-event
 (equal (car (fn-sn-sweep-staging *ss-ready*
                                  (list *ss-stage-a* *ss-stage-b*)
                                  (list *ss-stage-a*)))
        (list *ss-stage-b*)))
(assert-event
 (not (member-equal *ss-final*
                    (car (fn-sn-sweep-staging *ss-ready*
                                              (list *ss-final* *ss-stage-a*) nil)))))

; The kernel gate, on two violating states: a record staged but not yet
; linked, and a phase that is not :ready.  Both are outside the guard of
; every store transition, so they are evaluated with guard checking off.
(defconst *ss-staged*
  (fn-sn-make nil 0
              (fn-sf-make :ready 0 nil nil '(:a-staged-record) nil nil 5)
              nil nil (fn-stx-index-empty)))
(defconst *ss-recording*
  (fn-sn-make nil 0
              (fn-sf-make :recording 0 nil nil nil nil nil 5)
              nil nil (fn-stx-index-empty)))
(assert-event
 (with-guard-checking :none
  (and (not (fn-sn-sweep-enabledp *ss-staged*))
       (equal (car (fn-sn-sweep-staging *ss-staged* (list *ss-stage-a*) nil)) nil))))
(assert-event
 (with-guard-checking :none
  (and (not (fn-sn-sweep-enabledp *ss-recording*))
       (equal (car (fn-sn-sweep-staging *ss-recording* (list *ss-stage-a*) nil)) nil))))
