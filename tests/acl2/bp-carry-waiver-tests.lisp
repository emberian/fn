; Teeth for books/bp-carry-waiver.lisp (lane carry-abandon, PRF-950): the
; operator's waiver of a BP carry obligation (`carry drop WORK --abandon').
(in-package "ACL2")
(include-book "node-binding-fixture")
(include-book "../../books/bp-carry-waiver")
(include-book "../../books/bp-carry-frame")
(include-book "must-fail-checked")

; A reachable workflow image with one undertaken forwarding obligation (the
; construction of tests/acl2/bp-release-tests.lisp).
(defconst *cw-groups* '("fn.letters"))
(defconst *cw-node*
  (fn-node-complete
   (fn-node-prepare (fn-node-initial-state *cw-groups* 16) 9 "<cw@example.invalid>" 0
                    *cw-groups* "archive-cw" "subject-cw" "operator-release" 4 841000000 *nbft-binding*)
   0 9 :durable))
(defconst *cw-config*
  (fn-bp-make-config "dtn://home/fn" "dtn://peer/fn" "policy-1"
                     "receipt-authority" 1000 "home-incarnation-1"
                     "authorization-context-1"))
(defconst *cw-enqueued*
  (fn-bp-result-state
   (fn-bp-complete
    (fn-bp-prepare-enqueue (fn-bp-initial-state *cw-node* *cw-config*) 10 0 "work-1"
                           "<cw@example.invalid>" "forward-1" "policy-1" "terms-1")
    10 0 :durable)))
(defconst *cw-bp* (fn-bprl-undertake *cw-enqueued* "work-1" 3))
(defconst *cw-work* (fn-bp-find-work "work-1" (fn-bp-state-works *cw-bp*)))
(assert-event (fn-bprl-work-pinnedp *cw-bp* *cw-work*))
(assert-event (fn-retain-statep (fn-node-retention (fn-bp-state-node *cw-bp*))))

(defconst *cw-waiver* '(:waive "abandon" "work-1" "peer retired" "uid:1000"))
(defconst *cw-drop* '(:carry "drop" "work-1" "peer retired"))
(assert-event (fn-bpcc-waiver-recordp *cw-waiver*))
(assert-event (equal (fn-bpcc-operator-principal 1000) "uid:1000"))
(assert-event (null (fn-bpcc-waiver-refusal *cw-bp* (fn-bpcc-initial) *cw-waiver*)))
(defconst *cw-c* (fn-bpcc-apply (fn-bpcc-initial) *cw-waiver*))
(defconst *cw-event* (fn-bpcc-waiver-release-event *cw-bp* *cw-c* "work-1"))
(defconst *cw-next* (fn-bpcw-after-release *cw-bp* *cw-event*))

; fn-bpcw-admitted-waiver-authors-its-release: the pin's own id, subject and
; evidence (the receipt's event shape), charge 0.
(assert-event
 (equal *cw-event*
        (list :release "forward-1" "subject-cw"
              "fn-forward-release/1|work-1|subject-cw|receipt-authority|policy-1|terms-1|home-incarnation-1"
              0)))
; The waiver drops the work and records who waived it and why.
(assert-event (equal (fn-bpcc-work-state *cw-c* "work-1") :dropped))
(assert-event (equal (fn-bpcc-waived-by *cw-c* "work-1") "uid:1000"))
(assert-event (equal (fn-bpcc-waiver-reason *cw-c* "work-1") "peer retired"))
(assert-event (equal (fn-bpcc-request-gate *cw-c* "work-1" :plan) '(:refused :carry-dropped)))

; KEYSTONE fn-bpcw-waiver-releases-exactly-once, positive witness: every
; hypothesis and every conclusion.
(assert-event *cw-event*)
(assert-event (consp (fn-bpcc-waiver-entry *cw-c* "work-1")))
(assert-event (equal (fn-bprl-pins *cw-next*)
                     (fn-retain-remove-id "forward-1" (fn-bprl-pins *cw-bp*))))
(assert-event (null (fn-retain-find-id "forward-1" (fn-bprl-pins *cw-next*))))
(assert-event (not (fn-bprl-work-pinnedp *cw-next* *cw-work*)))
(assert-event (null (fn-bpcc-waiver-release-event *cw-next* *cw-c* "work-1")))
(assert-event (not (fn-bprl-release-okp *cw-next* '(:any) *cw-work*)))
; The recovery arm: pending before the Store event, none after.
(assert-event (equal (fn-bpcc-pending-waivers *cw-bp* *cw-c*) '("work-1")))
(assert-event (null (fn-bpcc-pending-waivers *cw-next* *cw-c*)))

; Hypothesis removal (the event): a drop WITHOUT --abandon authors no
; release and keeps the pin; the retention hypothesis holds, the event and
; the waiver entry do not.
(defconst *cw-dropped* (fn-bpcc-apply (fn-bpcc-initial) *cw-drop*))
(assert-event (null (fn-bpcc-refusal *cw-bp* (fn-bpcc-initial) *cw-drop*)))
(assert-event (equal (fn-bpcc-work-state *cw-dropped* "work-1") :dropped))
(assert-event (null (fn-bpcc-waiver-release-event *cw-bp* *cw-dropped* "work-1")))
(assert-event (not (consp (fn-bpcc-waiver-entry *cw-dropped* "work-1"))))
(assert-event (fn-bprl-work-pinnedp *cw-bp* *cw-work*))
(assert-event (null (fn-bpcc-pending-waivers *cw-bp* *cw-dropped*)))

; Hypothesis removal (retention's state), CORRUPTED-STATE witness: a ledger
; holding the pin twice.  The event stands; one release leaves the second
; copy pinned, so the conclusion fails.
(defconst *cw-ret* (fn-node-retention (fn-bp-state-node *cw-bp*)))
(defconst *cw-dup-bp*
  (fn-bprl-with-node
   *cw-bp*
   (fn-bprl-node-with-retention
    (fn-bp-state-node *cw-bp*)
    (fn-retain-make-state (fn-retain-capacity *cw-ret*) (fn-retain-reserved *cw-ret*)
                          (cons (fn-retain-find-id "forward-1" (fn-retain-pins *cw-ret*))
                                (fn-retain-pins *cw-ret*))
                          (fn-retain-releases *cw-ret*)))))
(assert-event (not (fn-retain-statep (fn-node-retention (fn-bp-state-node *cw-dup-bp*)))))
(assert-event (fn-bpcc-waiver-release-event *cw-dup-bp* *cw-c* "work-1"))
; (The corrupted ledger violates fn-retain-release's guard, so it runs
; without guard checking: the logical function is the claim's.)
(assert-event (with-guard-checking
               :none
               (fn-bprl-work-pinnedp
                (fn-bpcw-after-release *cw-dup-bp*
                                       (fn-bpcc-waiver-release-event *cw-dup-bp* *cw-c* "work-1"))
                *cw-work*)))
(must-fail-checked
 (defthm cw-release-without-retention-state
   (implies (fn-bpcc-waiver-release-event bp c w)
            (not (fn-bprl-work-pinnedp
                  (fn-bpcw-after-release bp (fn-bpcc-waiver-release-event bp c w))
                  (fn-bp-find-work w (fn-bp-state-works bp)))))
   :rule-classes nil))

; fn-bpcw-waiver-of-an-unheld-obligation-is-refused: by name.  Before the
; undertaking (no pin), after the release (a fresh overlay), an unknown work,
; and a second waiver.
(assert-event (equal (fn-bpcc-waiver-refusal *cw-enqueued* (fn-bpcc-initial) *cw-waiver*)
                     :not-held))
(assert-event (equal (fn-bpcc-waiver-refusal *cw-next* (fn-bpcc-initial) *cw-waiver*)
                     :not-held))
(assert-event (equal (fn-bpcc-waiver-refusal
                      *cw-bp* (fn-bpcc-initial)
                      '(:waive "abandon" "work-9" "peer retired" "uid:1000"))
                     :unknown-work))
(assert-event (equal (fn-bpcc-waiver-refusal *cw-bp* *cw-c* *cw-waiver*) :already-waived))
; Hypothesis removal (the pin is held): with the pin, no refusal.
(must-fail-checked
 (defthm cw-waiver-always-refused
   (implies (fn-bpcc-waiver-recordp record)
            (fn-bpcc-waiver-refusal bp c record))
   :rule-classes nil))

; fn-bpcw-only-a-waiver-waives, hypothesis removal: the waiver of W itself
; makes W waived.
(assert-event (not (consp (fn-bpcc-waiver-entry (fn-bpcc-initial) "work-1"))))
(assert-event (consp (fn-bpcc-waiver-entry (fn-bpcc-apply (fn-bpcc-initial) *cw-waiver*)
                                           "work-1")))
; A drop, then a waiver of the dropped work: the first drop's reason stays.
(assert-event (null (fn-bpcc-waiver-refusal *cw-bp* *cw-dropped* *cw-waiver*)))
(assert-event (equal (fn-bpcc-dropped-reason (fn-bpcc-apply *cw-dropped* *cw-waiver*) "work-1")
                     "peer retired"))

; fn-bpcw-refusal-ignores-the-pin: the journal replays the waiver after its
; own release (restart after the Store event landed), to the same overlay.
(defconst *cw-journal* (list (fn-bpcc-journal-config) *cw-waiver*))
(assert-event (equal (fn-bpcc-replay *cw-bp* *cw-journal*) (cons t *cw-c*)))
(assert-event (equal (fn-bpcc-replay *cw-next* *cw-journal*) (cons t *cw-c*)))
; A second waiver of the same work in the journal is a replay fault.
(assert-event (not (car (fn-bpcc-replay *cw-next* (append *cw-journal* (list *cw-waiver*))))))

; A receipt for a waived work is refused by name; another work's passes.
(assert-event (equal (fn-bpcc-receipt-gate *cw-c* '(:receipt-intent 12 0 "receipt-1" "work-1" "s"))
                     '(:refused :carry-waived)))
(assert-event (equal (fn-bpcc-receipt-gate *cw-c* '(:receipt-intent 12 0 "receipt-2" "work-2" "s"))
                     '(:receipt-intent 12 0 "receipt-2" "work-2" "s")))
(assert-event (equal (fn-bpcc-receipt-gate *cw-dropped* '(:receipt-intent 12 0 "receipt-1" "work-1" "s"))
                     '(:receipt-intent 12 0 "receipt-1" "work-1" "s")))

; The frame: a waiver seals and reads back as itself (fn-bpcc-frame-decode-of-sealed).
(defconst *cw-digest* (make-list 32 :initial-element 7))
(defconst *cw-wire*
  (list (fn-record-string-octets "abandon") (fn-record-string-octets "work-1")
        (fn-record-string-octets "peer retired") (fn-record-string-octets "uid:1000")))
(assert-event (not (equal (fn-bpcc-frame-protected :waive *cw-wire*) :bad)))
(assert-event (equal (fn-bpcc-frame-decode
                      (append (fn-bpcc-frame-protected :waive *cw-wire*) *cw-digest*)
                      *cw-digest*)
                     (fn-frame-ok *fn-bpcc-frame-magic* *fn-frame-version* :waive *cw-wire*)))
(assert-event (equal (fn-bpcc-frame-protected :waive (cdr *cw-wire*)) :bad))
