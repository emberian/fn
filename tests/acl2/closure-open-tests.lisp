; Teeth for books/closure-open.lisp (PRF-945, lane closure-theorems-2).
; The fixture is open-frontier-tests' (row B10): two retention events at
; txids 0 and 1, txids 2..6 consumed with no record, a configuration record
; naming txid 7; the clean stop's frontier is 7, and so is the fold's.
(in-package "ACL2")
(include-book "../../books/closure-open")
(include-book "open-frontier-tests")

(defconst *clo-t-capture* (fn-sco-capture *ofr-t-configs* *ofr-t-events*))
(defconst *clo-t-frontier* (fn-ofr-frontier *ofr-t-configs* *ofr-t-events* 0))

; -----------------------------------------------------------------------------
; fn-clo-store-open-of-clean-stop-is-accepted-or-identity, reachable, positive:
; every hypothesis, then the conclusion -- and which disjunct: the open.

(assert-event (true-listp *ofr-t-events*))
(assert-event (fn-cst-recoverablep *ofr-t-configs* *ofr-t-events* 7))
(assert-event (natp 0))
(assert-event (consp *ofr-t-configs*))
(assert-event (equal *clo-t-frontier* 7))
(assert-event (fn-sn-observed-historyp *clo-t-frontier* *ofr-t-events*))
(assert-event
 (let ((answer (cadr (fn-sco-store-open *clo-t-capture* *ofr-t-configs* *clo-t-frontier*))))
   (and (or (equal (fn-sn-open-kind answer) :ok)
            (equal answer (fn-sn-open-error :identity)))
        (equal (fn-sn-open-kind answer) :ok))))

; fn-clo-capture-of-clean-stop-is-accepted-or-identity and the general form
; on the same fixture (the capture's records and drained fold are the
; history's, as the general form assumes).
(assert-event (equal (fn-sco-records *clo-t-capture*) *ofr-t-events*))
(assert-event (equal (fn-sco-cpr-finish (fn-sco-cpr *clo-t-capture*) *ofr-t-configs*)
                     (fn-cpr-replay *ofr-t-configs* *ofr-t-events*)))
(assert-event
 (equal (fn-sn-open-kind (fn-sco-finalize *clo-t-capture* *ofr-t-configs* *clo-t-frontier*))
        :ok))

; -----------------------------------------------------------------------------
; fn-clo-finalize-never-answers-frontier-at-the-computed-frontier, and the
; arm it closes: MUTATION witness -- at a frontier that is NOT the fold of the
; records (6, below the node's next id 7) the same clean stop IS refused
; :frontier.  The arm is live off the computed frontier and dead on it.

(assert-event (not (equal (fn-sco-finalize *clo-t-capture* *ofr-t-configs* *clo-t-frontier*)
                          (fn-sn-open-error :frontier))))
(assert-event (equal (fn-sco-finalize *clo-t-capture* *ofr-t-configs* 6)
                     (fn-sn-open-error :frontier)))
(assert-event (fn-sn-observed-historyp 6 *ofr-t-events*))

; -----------------------------------------------------------------------------
; HYPOTHESIS REMOVAL: without the clean stop, at the computed frontier, the
; finalize answers :replay.  The history whose configuration chain starts at
; the late record is not recoverable (retained hypotheses affirmed; the
; omitted one fails; the conclusion fails).

(defconst *clo-t-improper-configs* (list *ofr-t-late-config*))
(defconst *clo-t-improper-capture* (fn-sco-capture *clo-t-improper-configs* *ofr-t-events*))
(defconst *clo-t-improper-frontier*
  (fn-ofr-frontier *clo-t-improper-configs* *ofr-t-events* 0))

(assert-event (true-listp *ofr-t-events*))
(assert-event (natp 0))
(assert-event (consp *clo-t-improper-configs*))
(assert-event (fn-sn-observed-historyp *clo-t-improper-frontier* *ofr-t-events*))
(assert-event (not (fn-cst-recoverablep *clo-t-improper-configs* *ofr-t-events*
                                        *clo-t-improper-frontier*)))
(assert-event (not (fn-cst-recoverablep *clo-t-improper-configs* *ofr-t-events* 7)))
(assert-event
 (let ((answer (cadr (fn-sco-store-open *clo-t-improper-capture* *clo-t-improper-configs*
                                        *clo-t-improper-frontier*))))
   (and (not (or (equal (fn-sn-open-kind answer) :ok)
                 (equal answer (fn-sn-open-error :identity))))
        (equal answer (fn-sn-open-error :replay)))))

; The one refusal the keystone leaves open is :identity, never :history,
; :replay or :frontier: the improper history above is refused :replay
; because it is not a clean stop, not because of the frontier.
(assert-event
 (not (equal (fn-sco-finalize *clo-t-improper-capture* *clo-t-improper-configs*
                              *clo-t-improper-frontier*)
             (fn-sn-open-error :frontier))))
