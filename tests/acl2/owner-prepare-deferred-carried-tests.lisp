; Teeth for books/owner-prepare-deferred-carried.lisp (lane
; served-incremental-2): the retention, consumer and topic prepares the host
; calls, staged without the appended-history replay.
;
; Store-level keystones are witnessed on stores the Store machine reaches from
; fn-sn-initial (fn-snrt-run; fn-snrt-initialized-mixed-trace-has-live-
; history-relation gives fn-snt-relation there).  Owner-level keystones are
; witnessed on owner-log-ocl-tests' configured owner (*lgt-reserved*), driven
; by the events ACL2 proposes (owner-prepare-served-events-tests).
(in-package "ACL2")
(include-book "owner-prepare-served-events-tests")
(include-book "../../books/owner-prepare-deferred-carried")

; -----------------------------------------------------------------------------
; Reached stores.  A consumer bootstrap committed through the Store machine,
; then a retention undertake committed, then a fresh reservation.
(defconst *pdt-groups* '("fn.letters" "fn.test"))
(defconst *pdt-ida* (make-list 32 :initial-element 1))
(defconst *pdt-idb* (make-list 32 :initial-element 2))
(defconst *pdt-idc* (make-list 32 :initial-element 3))
(defconst *pdt-reserve*
  '((:io :start-frontier nil) (:io :frontier-file :ok)
    (:io :frontier-replace :ok) (:io :frontier-directory :ok)))
(defconst *pdt-publish*
  '((:io :record-file :ok) (:io :record-link :ok) (:io :record-directory :ok)
    (:finish)))
(defconst *pdt-bootstrap* (list :consumer 0 0 0 (list :bootstrap *pdt-ida* *pdt-idb*)))
(defconst *pdt-undertake*
  (fn-store-retention-event-make :undertake 1 1 1 "pdt-id-1" "pdt-subject" "pdt-evidence" 5))
(defconst *pdt-s1*
  (fn-snrt-run (fn-sn-initial *pdt-groups* 20)
               (append *pdt-reserve*
                       (list (list :prepare-consumer *pdt-bootstrap*))
                       *pdt-publish*
                       *pdt-reserve*
                       (list (list :prepare-retention *pdt-undertake*))
                       *pdt-publish*
                       *pdt-reserve*)))
(assert-event (equal (len (fn-sf-records (fn-sn-files *pdt-s1*))) 2))
(assert-event (equal (fn-sf-phase (fn-sn-files *pdt-s1*)) :reserved))
(assert-event (fn-sn-statep *pdt-s1*))
(assert-event (fn-snt-relation *pdt-s1*))

(defconst *pdt-rollover* (list :consumer 2 2 2 (list :rollover *pdt-idc*)))
(defconst *pdt-undertake-2*
  (fn-store-retention-event-make :undertake 2 2 2 "pdt-id-2" "pdt-subject" "pdt-evidence" 5))
(defconst *pdt-release-unknown*
  (fn-store-retention-event-make :release 2 2 2 "pdt-id-9" "pdt-subject" "pdt-evidence" 0))

; -----------------------------------------------------------------------------
; fn-pdc-sn-prepare-consumer-is-sn-prepare-consumer-under-relation and
; fn-pdc-sn-prepare-retention-is-sn-prepare-retention-under-relation.
; Reachable positive witness: the antecedent (fn-snt-relation) holds, every
; conjunct of the shared gate holds, and the conclusion holds with the record
; staged (the case the theorem exists for).
(defmacro pdt-gate-consumer (s e)
  `(and (fn-sn-statep ,s)
        (equal (fn-sf-phase (fn-sn-files ,s)) :reserved)
        (fn-cpe-eventp ,e)
        (eq (car (fn-cpe-projection-step (fn-sn-consumer ,s) ,e (fn-sn-identity-next ,s))) :ok)
        (consp (fn-replay-apply-record (fn-sn-node ,s) ,e))
        (fn-sf-candidatep ,e (fn-sf-records (fn-sn-files ,s)) (fn-sf-frontier (fn-sn-files ,s)))))
(defmacro pdt-gate-retention (s e)
  `(and (fn-sn-statep ,s)
        (equal (fn-sf-phase (fn-sn-files ,s)) :reserved)
        (fn-store-retention-event-p ,e)
        (eq (car (fn-cpe-projection-step (fn-sn-consumer ,s) ,e (fn-sn-identity-next ,s))) :ok)
        (consp (fn-replay-apply-retention-event (fn-sn-node ,s) ,e))
        (fn-sf-candidatep ,e (fn-sf-records (fn-sn-files ,s)) (fn-sf-frontier (fn-sn-files ,s)))))

(assert-event (pdt-gate-consumer *pdt-s1* *pdt-rollover*))
(assert-event (equal (fn-pdc-sn-prepare-consumer *pdt-s1* *pdt-rollover*)
                     (fn-sn-prepare-consumer *pdt-s1* *pdt-rollover*)))
(assert-event (equal (fn-sf-phase (fn-sn-files (fn-pdc-sn-prepare-consumer *pdt-s1* *pdt-rollover*)))
                     :record-staged))
(assert-event (equal (fn-sf-record-candidate
                      (fn-sn-files (fn-pdc-sn-prepare-consumer *pdt-s1* *pdt-rollover*)))
                     *pdt-rollover*))

(assert-event (pdt-gate-retention *pdt-s1* *pdt-undertake-2*))
(assert-event (equal (fn-pdc-sn-prepare-retention *pdt-s1* *pdt-undertake-2*)
                     (fn-sn-prepare-retention *pdt-s1* *pdt-undertake-2*)))
(assert-event (equal (fn-sf-phase (fn-sn-files (fn-pdc-sn-prepare-retention *pdt-s1* *pdt-undertake-2*)))
                     :record-staged))

; The same witnesses are the positive witnesses of the -when-staged keystones:
; the reference stages, and the carried prepare is the reference.
(assert-event (not (equal (fn-sn-prepare-consumer *pdt-s1* *pdt-rollover*) *pdt-s1*)))
(assert-event (not (equal (fn-sn-prepare-retention *pdt-s1* *pdt-undertake-2*) *pdt-s1*)))

; Hypothesis-removal witness (CORRUPTED STATE, labelled): the store with its
; capacity field set to 1 below the committed undertake's charge 5.  It is
; still a store-node state, reserved, and every conjunct of the carried gate
; holds (the live node is unchanged); fn-snt-relation fails (the unconfigured
; replay of the history over capacity 1 refuses the undertake), and the
; conclusion fails: the reference's replay refuses, the carried prepare stages.
; The same store is the -when-staged keystones' removal witness: the
; reference does not stage and the two differ.
(defconst *pdt-bad-cap*
  (let ((s *pdt-s1*))
    (fn-sn-make-v6 (fn-sn-groups s) 1 (fn-sn-files s) (fn-sn-node s)
                   (fn-sn-keyring s) (fn-sn-index s) (fn-sn-keyring-generation s)
                   (fn-sn-verdicts s) (fn-sn-keyring-snapshots s) (fn-sn-identity-next s)
                   (fn-sn-config-history s) (fn-sn-consumer s) (fn-sn-topic s)
                   (fn-sn-event-index s))))
(assert-event (pdt-gate-consumer *pdt-bad-cap* *pdt-rollover*))
(assert-event (not (fn-snt-relation *pdt-bad-cap*)))
(assert-event (equal (fn-sn-prepare-consumer *pdt-bad-cap* *pdt-rollover*) *pdt-bad-cap*))
(assert-event (equal (fn-sf-phase (fn-sn-files (fn-pdc-sn-prepare-consumer *pdt-bad-cap* *pdt-rollover*)))
                     :record-staged))
(assert-event (not (equal (fn-pdc-sn-prepare-consumer *pdt-bad-cap* *pdt-rollover*)
                          (fn-sn-prepare-consumer *pdt-bad-cap* *pdt-rollover*))))

; MUTATION witness (labelled): the applied-node test of the carried gate is
; load-bearing.  A release of an obligation no pin holds passes every other
; conjunct and the file stage alone would stage it; the node refuses it, and
; the carried prepare (like the reference) leaves the store unchanged.
(assert-event (fn-store-retention-event-p *pdt-release-unknown*))
(assert-event (eq (car (fn-cpe-projection-step (fn-sn-consumer *pdt-s1*) *pdt-release-unknown*
                                               (fn-sn-identity-next *pdt-s1*))) :ok))
(assert-event (null (fn-replay-apply-retention-event (fn-sn-node *pdt-s1*) *pdt-release-unknown*)))
(assert-event (equal (fn-sf-phase (fn-pcar-stage-record (fn-sn-files *pdt-s1*) *pdt-release-unknown*))
                     :record-staged))
(assert-event (equal (fn-pdc-sn-prepare-retention *pdt-s1* *pdt-release-unknown*) *pdt-s1*))
(assert-event (equal (fn-sn-prepare-retention *pdt-s1* *pdt-release-unknown*) *pdt-s1*))

; -----------------------------------------------------------------------------
; Owner level: fn-pdc-ocfg-prepare-consumer-preserves-invariant and
; fn-pdc-psrv-prepare-topic-preserves-invariant, and the entries' words.
; Reachable positive witness: the antecedent fn-lgoc-invariantp holds on the
; configured owner at :reserved; the carried prepares stage the events ACL2
; proposed, are the reference owners the host installed before
; (*pse-consumer-staged*, *pse-topic-staged*), and the conclusion holds.
(assert-event (fn-lgoc-invariantp *lgt-reserved*))
(make-event `(defconst *pdt-consumer-staged*
               ',(fn-pdc-ocfg-prepare-consumer *lgt-reserved* *pse-consumer-event*)))
(assert-event (equal *pdt-consumer-staged* *pse-consumer-staged*))
(assert-event (equal (lgt-phase *pdt-consumer-staged*) :record-staged))
(assert-event (fn-lgoc-invariantp *pdt-consumer-staged*))
(assert-event (equal (mv-nth 0 (fn-pdc-pout-prepare-consumer *lgt-reserved* *pse-consumer-event*))
                     :prepared))
(make-event `(defconst *pdt-topic-staged*
               ',(fn-pdc-psrv-prepare-topic *lgt-reserved* *pse-topic-event*)))
(assert-event (equal *pdt-topic-staged* *pse-topic-staged*))
(assert-event (fn-lgoc-invariantp *pdt-topic-staged*))
(assert-event (equal (mv-nth 0 (fn-pdc-pout-prepare-topic *lgt-reserved* *pse-topic-event*))
                     :prepared))
; Hypothesis-removal witness (CORRUPTED STATE, labelled: owner-prepare-served-
; events-tests' *lgt-bad-reserved*, the topic counter moved): the antecedent
; fails, and so does the conclusion after each carried prepare.
(assert-event (not (fn-lgoc-invariantp *lgt-bad-reserved*)))
(assert-event (not (fn-lgoc-invariantp
                    (fn-pdc-ocfg-prepare-consumer *lgt-bad-reserved* *pse-consumer-event*))))
(assert-event (not (fn-lgoc-invariantp
                    (fn-pdc-psrv-prepare-topic *lgt-bad-reserved* *pse-topic-event*))))
; A refused prepare answers :refused and leaves the owner unchanged: the
; consumer bootstrap proposed again after it committed.
(assert-event (equal (mv-nth 0 (fn-pdc-pout-prepare-consumer *pse-consumer-finished* *pse-consumer-event*))
                     :refused))
(assert-event (equal (lgt-store (mv-nth 1 (fn-pdc-pout-prepare-consumer *pse-consumer-finished*
                                                                       *pse-consumer-event*)))
                     (lgt-store *pse-consumer-finished*)))
