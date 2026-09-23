; store-sweep-tests.lisp -- teeth for the staging sweep.
;
; The scenario is finding 5 of planning/evidence/deploy-cce4b11-2026-09-20.md:
; an uncertain publication left `.stage-1821597-850fc8a5e5a24494a2c8734e' in
; the staging directory and two recoveries reported it and collected none.

(in-package "ACL2")

(include-book "../../books/store-sweep")

(local (in-theory (enable fn-sn-staging-namep fn-sn-final-namespace-namep
                          fn-sn-sweep-enabledp fn-sn-sweep-staging)))

(defconst *ss-stage-a* '(46 115 116 97 103 101 45 49 56 50 49 53 57 55 45 56 53 48 102 99 56 97 53 101 53 97 50 52 52 57 52 97 50 99 56 55 51 52 101))
(defconst *ss-stage-b* '(46 115 116 97 103 101 45 49 56 50 49 53 57 55 45 48 48 48 48 48 48 48 48 48 48 48 48 48 48 48 48 48 48 48 48 48 48 102 102))
(defconst *ss-final*   '(48 48 48 48 48 48 48 48 48 48 48 48 48 48 48 48 48 48 48 49))
(defconst *ss-anchor*  '(46 97 110 99 104 111 114 45 49 56 50 49 53 57 55 45 56 53 48 102 99 56 97 53 101 53 97 50 52 52 57 52 97 50 99 56 55 51 52 101))
(defconst *ss-operator* '(46 111 112 101 114 97 116 111 114 45 101 118 105 100 101 110 99 101)) ; .operator-evidence
(defconst *ss-short*   '(46 115 116 97 103))

; The two namespaces, concretely.
(assert-event (fn-sn-staging-namep *ss-stage-a*))
(assert-event (not (fn-sn-staging-namep *ss-final*)))
(assert-event (fn-sn-staging-namep *ss-anchor*))
(assert-event (not (fn-sn-staging-namep *ss-operator*)))
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

; The witness: the deploy gate's directory, swept.  The orphans go (the
; anchor stage is one since 2026-09-22); an unrecognized name and a
; final-namespace name that should never be in staging at all both stay.
(assert-event
 (equal (car (fn-sn-sweep-staging *ss-ready*
                                  (list *ss-anchor* *ss-operator* *ss-final*
                                        *ss-stage-a* *ss-stage-b*)
                                  nil))
        (list *ss-anchor* *ss-stage-a* *ss-stage-b*)))
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

; -----------------------------------------------------------------------------
; Finding F2 of planning/evidence/campaign-dabebb84-2026-09-22.md.
;
; Every prefix a host program stages under, as the host spells it.
(defun ss-octets (string) (declare (xargs :mode :program)) (fn-record-string-octets string))
(assert-event
 (and (fn-sn-staging-namep (ss-octets ".allocation-2716993-0123456789abcdef01234567"))
      (fn-sn-staging-namep (ss-octets ".init-2716993-0123456789abcdef01234567"))
      (fn-sn-staging-namep (ss-octets ".anchor-1-00"))
      (fn-sn-staging-namep (ss-octets ".checkpoint-1-00"))
      (fn-sn-staging-namep (ss-octets ".selection-1-00"))
      (fn-sn-staging-namep (ss-octets ".pack-1-00"))
      (fn-sn-staging-namep (ss-octets ".pack-selection-1-00"))
      (fn-sn-staging-namep (ss-octets ".stage-1-00"))
      (not (fn-sn-staging-namep (ss-octets ".allocation")))
      (not (fn-sn-staging-namep (ss-octets "allocation-frontier.json")))
      (not (fn-sn-staging-namep (ss-octets ".incoming-1-00")))))

; The campaign's store: N allocation orphans, one per death at
; frontier-staged-durable.  N = 65 is one more than an observation.
(defun ss-allocation-orphans (n)
  (declare (xargs :mode :program))
  (if (zp n) nil
    (cons (ss-octets (concatenate 'string ".allocation-4242-"
                                  (coerce (explode-atom (+ 1000 n) 10) 'string)))
          (ss-allocation-orphans (1- n)))))
(defun ss-foreign-names (n)
  (declare (xargs :mode :program))
  (if (zp n) nil
    (cons (ss-octets (concatenate 'string ".operator-"
                                  (coerce (explode-atom (+ 1000 n) 10) 'string)))
          (ss-foreign-names (1- n)))))

(assert-event (equal (len (ss-allocation-orphans 65)) 65))
(assert-event (fn-sn-all-sweepablep (ss-allocation-orphans 65) nil))

; One round of the host's loop on the first 64: all 64 go and the answer is
; :again, because the enumeration saw a 65th.
(assert-event
 (let ((window (fn-sn-take-names 64 (ss-allocation-orphans 65))))
   (equal (fn-sn-sweep-round *ss-ready* window t nil)
          (list :again window))))
; The last round: one name, nothing beyond it, :done.
(assert-event
 (equal (fn-sn-sweep-round *ss-ready* (last (ss-allocation-orphans 65)) nil nil)
        (list :done (last (ss-allocation-orphans 65)))))

; fn-sn-sweep-rounds-collect-every-orphan, the witness: 65 orphans, and 200,
; end :done with nothing left.
(assert-event (equal (fn-sn-sweep-rounds *ss-ready* (ss-allocation-orphans 65) nil 64)
                     (list :done nil)))
(assert-event (equal (fn-sn-sweep-rounds *ss-ready* (ss-allocation-orphans 200) nil 64)
                     (list :done nil)))

; One violating value per hypothesis of fn-sn-sweep-rounds-collect-every-orphan.
;   The gate: a record staged and not linked.  Nothing is swept and 65 names
;   are over the observation, so the loop refuses with all of them left.
(assert-event
 (with-guard-checking :none
  (equal (fn-sn-sweep-rounds *ss-staged* (ss-allocation-orphans 65) nil 64)
         (list :refused (ss-allocation-orphans 65)))))
;   Every name sweepable: one unrecognized name survives the loop.
(assert-event
 (equal (fn-sn-sweep-rounds *ss-ready*
                            (cons *ss-operator* (ss-allocation-orphans 65)) nil 64)
        (list :done (list *ss-operator*))))
;   Every name unheld: a held allocation stage survives the loop.
(assert-event
 (equal (fn-sn-sweep-rounds *ss-ready* (ss-allocation-orphans 65)
                            (list (car (ss-allocation-orphans 65))) 64)
        (list :done (list (car (ss-allocation-orphans 65))))))
;   A positive bound: an observation of nothing makes no progress.
(assert-event
 (equal (fn-sn-sweep-rounds *ss-ready* (ss-allocation-orphans 65) nil 0)
        (list :refused (ss-allocation-orphans 65))))

; fn-sn-sweep-rounds-keep-every-name-they-may-not-remove: its witness is the
; unrecognized-name case above.  Its teeth: without the name test, the
; orphans themselves are not kept; without membership, a name that was never
; in the directory is not in the result either.
(assert-event
 (not (fn-sn-name-memberp (car (ss-allocation-orphans 65))
                          (cadr (fn-sn-sweep-rounds *ss-ready*
                                                    (ss-allocation-orphans 65) nil 64)))))
(assert-event
 (not (fn-sn-name-memberp *ss-operator*
                          (cadr (fn-sn-sweep-rounds *ss-ready*
                                                    (ss-allocation-orphans 65) nil 64)))))

; fn-sn-sweep-rounds-end-done-or-refused, the refusal it characterizes: 65
; names the model does not recognize.  More than an observation remain and
; the observation removes nothing.  This is the only way to :refused with
; the gate open; crashes alone do not reach it.
(assert-event
 (let ((result (fn-sn-sweep-rounds *ss-ready* (ss-foreign-names 65) nil 64)))
   (and (equal (car result) :refused)
        (equal (len (cadr result)) 65))))
; 64 of them fit in one observation: the loop ends :done and reports them.
(assert-event
 (equal (fn-sn-sweep-rounds *ss-ready* (ss-foreign-names 64) nil 64)
        (list :done (ss-foreign-names 64))))
; Orphans mixed with foreign names beyond one observation still go, as long
; as each observation has something to remove.
(assert-event
 (equal (fn-sn-sweep-rounds *ss-ready*
                            (append (ss-allocation-orphans 100) (ss-foreign-names 10))
                            nil 64)
        (list :done (ss-foreign-names 10))))
