; Witness and teeth for the forwarding-obligation release (wave 2, packet A).
;
; The witness is reachable: node prepare/complete, workflow enqueue, undertake,
; attempt, delivery, checked receipt, durable receipt completion, release.
; Every RET-004 adjective then gets a ground refusal; the two node-shape guards
; and the capacity guard get one each; the journal wrapper is exercised on a
; release record, a mismatched release record, an undertake record and an
; ordinary fn-bp record.
(in-package "ACL2")
(include-book "../../books/bp-release-invariants")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; Reachable witness

(defconst *rl-groups* '("fn.letters"))
(defconst *rl-payload* '(72 105 13 10))
(defconst *rl-node-empty* (fn-node-initial-state *rl-groups* 16))
(defconst *rl-node-prepared*
  (fn-node-prepare *rl-node-empty* 9 "<rl@example.invalid>" *rl-payload*
                   *rl-groups* "archive-rl" "subject-rl" "operator-release" 4))
(defconst *rl-node-committed* (fn-node-complete *rl-node-prepared* 0 9 :durable))
(defconst *rl-config*
  (fn-bp-make-config "dtn://home/fn" "dtn://peer/fn" "policy-1"
                     "receipt-authority" 1000 "home-incarnation-1"
                     "authorization-context-1"))
(defconst *rl-empty* (fn-bp-initial-state *rl-node-committed* *rl-config*))
(defconst *rl-enqueued*
  (fn-bp-result-state
   (fn-bp-complete
    (fn-bp-prepare-enqueue *rl-empty* 10 0 "work-1" "<rl@example.invalid>"
                           "forward-1" "policy-1" "terms-1")
    10 0 :durable)))
(assert-event (fn-bp-binding-statep *rl-enqueued*))
(assert-event (fn-bp-work-outstandingp
               (fn-bp-find-work "work-1" (fn-bp-state-works *rl-enqueued*))))
(defconst *rl-work* (fn-bp-find-work "work-1" (fn-bp-state-works *rl-enqueued*)))

; Before undertaking there is no :forward pin at all.
(assert-event (equal (fn-retain-find-id "forward-1" (fn-bprl-pins *rl-enqueued*)) nil))
(assert-event (not (fn-bprl-work-pinnedp *rl-enqueued* *rl-work*)))

(defconst *rl-undertaken* (fn-bprl-undertake *rl-enqueued* "work-1" 3))
(assert-event (not (equal *rl-undertaken* *rl-enqueued*)))
(assert-event (fn-bprl-work-pinnedp *rl-undertaken* *rl-work*))
(assert-event (fn-node-statep (fn-bp-state-node *rl-undertaken*)))
(assert-event (fn-bp-binding-statep *rl-undertaken*))
(assert-event (equal (fn-retain-obligation-kind
                      (fn-retain-find-id "forward-1" (fn-bprl-pins *rl-undertaken*)))
                     :forward))
(assert-event (equal (fn-retain-reserved (fn-node-retention (fn-bp-state-node *rl-undertaken*)))
                     (+ 3 (fn-retain-reserved (fn-node-retention (fn-bp-state-node *rl-enqueued*))))))
; The required evidence is the rendered term: no receipt id in it.
(assert-event
 (equal (fn-retain-obligation-evidence
         (fn-retain-find-id "forward-1" (fn-bprl-pins *rl-undertaken*)))
        "fn-forward-release/1|work-1|subject-rl|receipt-authority|policy-1|terms-1|home-incarnation-1"))

(defconst *rl-delivered*
  (fn-bp-observe-transport
   (fn-bp-result-state
    (fn-bp-complete (fn-bp-prepare-attempt *rl-undertaken* 11 0 "work-1" "attempt-0")
                    11 0 :durable))
   "work-1" "attempt-0" 0 :delivered))
(defconst *rl-receipt*
  (fn-bp-make-receipt "receipt-1" "work-1" "subject-rl" "receipt-authority"
                      "dtn://peer/fn" "policy-1" "home-incarnation-1"
                      "authorization-context-1" "terms-1"))
(assert-event (fn-bp-authorized-receiptp *rl-config* *rl-work* *rl-receipt*))
(defconst *rl-receipt-pending*
  (fn-bp-prepare-receipt *rl-delivered* 12 0 *rl-receipt* t))
(assert-event (consp (fn-bp-state-pending *rl-receipt-pending*)))
(defconst *rl-receipted*
  (fn-bp-result-state (fn-bp-complete *rl-receipt-pending* 12 0 :durable)))
(assert-event (equal (fn-bp-state-receipts *rl-receipted*) (list *rl-receipt*)))
(assert-event (not (fn-bp-work-outstandingp
                    (fn-bp-find-work "work-1" (fn-bp-state-works *rl-receipted*)))))
; The receipt closed the work, and the pin is STILL there: this is the gap.
(assert-event (fn-bprl-work-pinnedp *rl-receipted* *rl-work*))

(defconst *rl-decision* (fn-bprl-release-decision *rl-receipted* "receipt-1"))
(defconst *rl-released* (fn-bprl-decision-state *rl-decision*))
(assert-event (equal (fn-bprl-decision-okp *rl-decision*) t))
(assert-event (equal (fn-bprl-decision-evidence *rl-decision*)
                     (fn-bprl-make-evidence "receipt-1" "work-1" "subject-rl"
                                            "receipt-authority"
                                            (fn-bprl-make-term "policy-1" "terms-1")
                                            "home-incarnation-1")))
(assert-event (fn-bprl-evidencep (fn-bprl-decision-evidence *rl-decision*)))
; The forward pin is released; the archive pin is byte-identical.
(assert-event (equal (fn-retain-find-id "forward-1" (fn-bprl-pins *rl-released*)) nil))
(assert-event (equal (fn-retain-find-id "archive-rl" (fn-bprl-pins *rl-released*))
                     (fn-retain-find-id "archive-rl" (fn-bprl-pins *rl-receipted*))))
(assert-event (equal (fn-retain-obligation-kind
                      (fn-retain-find-id "archive-rl" (fn-bprl-pins *rl-released*)))
                     :archive))
(assert-event (equal (car (fn-retain-releases (fn-node-retention (fn-bp-state-node *rl-released*))))
                     (fn-retain-make-release
                      "forward-1" "subject-rl" :forward
                      "fn-forward-release/1|work-1|subject-rl|receipt-authority|policy-1|terms-1|home-incarnation-1")))
; Release keeps the one-unit history charge: 3 charged, 2 freed.
(assert-event (equal (fn-retain-reserved (fn-node-retention (fn-bp-state-node *rl-released*)))
                     (- (fn-retain-reserved (fn-node-retention (fn-bp-state-node *rl-receipted*))) 2)))
(assert-event (fn-node-statep (fn-bp-state-node *rl-released*)))
(assert-event (fn-bp-statep *rl-released*))
(assert-event (fn-bp-binding-statep *rl-released*))
; Everything but the node is untouched.
(assert-event (equal (fn-bp-state-works *rl-released*) (fn-bp-state-works *rl-receipted*)))
(assert-event (equal (fn-bp-state-receipts *rl-released*) (fn-bp-state-receipts *rl-receipted*)))

; -----------------------------------------------------------------------------
; Teeth: RET-004 adjectives, each a ground refusal of the decision

(defun rl-refused (s receipt-id)
  (and (not (fn-bprl-decision-okp (fn-bprl-release-decision s receipt-id)))
       (equal (fn-bprl-decision-state (fn-bprl-release-decision s receipt-id)) s)))

; stale: the receipt is prepared but not committed; and an unknown id.
(assert-event (rl-refused *rl-receipt-pending* "receipt-1"))
(assert-event (rl-refused *rl-receipted* "receipt-never-seen"))
; duplicated: the same committed receipt cannot release twice.
(assert-event (rl-refused *rl-released* "receipt-1"))
; not undertaken: a committed authorized receipt for a work with no forward pin.
(defconst *rl-unpinned-receipted*
  (fn-bp-result-state
   (fn-bp-complete
    (fn-bp-prepare-receipt
     (fn-bp-observe-transport
      (fn-bp-result-state
       (fn-bp-complete (fn-bp-prepare-attempt *rl-enqueued* 11 0 "work-1" "attempt-0")
                       11 0 :durable))
      "work-1" "attempt-0" 0 :delivered)
     12 0 *rl-receipt* t)
    12 0 :durable)))
(assert-event (equal (fn-bp-state-receipts *rl-unpinned-receipted*) (list *rl-receipt*)))
(assert-event (rl-refused *rl-unpinned-receipted* "receipt-1"))

; Fabricated histories isolate fn-bp-authorized-receiptp's clauses.  Each
; state is structurally valid (fn-bp-statep) and carries the bad receipt both
; on the work and in history, so only the named clause refuses.
(defun rl-with-history-receipt (s receipt)
  (fn-bp-make-state
   (fn-bp-state-node s) (fn-bp-state-config s)
   (fn-bp-replace-work
    (fn-bp-work-with-receipt (fn-bp-find-work "work-1" (fn-bp-state-works s)) receipt)
    (fn-bp-state-works s))
   (list receipt) nil nil (fn-bp-state-used-txs s)))
(defconst *rl-wrong-subject*
  (rl-with-history-receipt
   *rl-delivered*
   (fn-bp-make-receipt "receipt-1" "work-1" "subject-other" "receipt-authority"
                       "dtn://peer/fn" "policy-1" "home-incarnation-1"
                       "authorization-context-1" "terms-1")))
(assert-event (fn-bp-statep *rl-wrong-subject*))
(assert-event (rl-refused *rl-wrong-subject* "receipt-1"))
(defconst *rl-unauthorized*
  (rl-with-history-receipt
   *rl-delivered*
   (fn-bp-make-receipt "receipt-1" "work-1" "subject-rl" "someone-else"
                       "dtn://peer/fn" "policy-1" "home-incarnation-1"
                       "authorization-context-1" "terms-1")))
(assert-event (fn-bp-statep *rl-unauthorized*))
(assert-event (rl-refused *rl-unauthorized* "receipt-1"))
(defconst *rl-wrong-incarnation*
  (rl-with-history-receipt
   *rl-delivered*
   (fn-bp-make-receipt "receipt-1" "work-1" "subject-rl" "receipt-authority"
                       "dtn://peer/fn" "policy-1" "home-incarnation-0"
                       "authorization-context-1" "terms-1")))
(assert-event (fn-bp-statep *rl-wrong-incarnation*))
(assert-event (rl-refused *rl-wrong-incarnation* "receipt-1"))
(defconst *rl-insufficient-terms*
  (rl-with-history-receipt
   *rl-delivered*
   (fn-bp-make-receipt "receipt-1" "work-1" "subject-rl" "receipt-authority"
                       "dtn://peer/fn" "policy-1" "home-incarnation-1"
                       "authorization-context-1" "terms-weaker")))
(assert-event (fn-bp-statep *rl-insufficient-terms*))
(assert-event (rl-refused *rl-insufficient-terms* "receipt-1"))
; wrong-work: a committed receipt in history that names another work.
(defconst *rl-wrong-work*
  (fn-bp-make-state
   (fn-bp-state-node *rl-delivered*) (fn-bp-state-config *rl-delivered*)
   (fn-bp-state-works *rl-delivered*)
   (list (fn-bp-make-receipt "receipt-1" "work-2" "subject-rl" "receipt-authority"
                             "dtn://peer/fn" "policy-1" "home-incarnation-1"
                             "authorization-context-1" "terms-1"))
   nil nil (fn-bp-state-used-txs *rl-delivered*)))
(assert-event (fn-bp-statep *rl-wrong-work*))
(assert-event (rl-refused *rl-wrong-work* "receipt-1"))
; A receipt in history that the work does not carry (committed for nothing).
(defconst *rl-orphan-receipt*
  (fn-bp-make-state
   (fn-bp-state-node *rl-delivered*) (fn-bp-state-config *rl-delivered*)
   (fn-bp-state-works *rl-delivered*) (list *rl-receipt*)
   nil nil (fn-bp-state-used-txs *rl-delivered*)))
(assert-event (fn-bp-statep *rl-orphan-receipt*))
(assert-event (rl-refused *rl-orphan-receipt* "receipt-1"))

; -----------------------------------------------------------------------------
; Teeth: node-shape and capacity guards of the undertaking

; A forwarding id that is the archive id is refused: one pin, one obligation.
(defconst *rl-collided*
  (fn-bp-result-state
   (fn-bp-complete
    (fn-bp-prepare-enqueue *rl-empty* 10 0 "work-1" "<rl@example.invalid>"
                           "archive-rl" "policy-1" "terms-1")
    10 0 :durable)))
(assert-event (fn-bp-binding-statep *rl-collided*))
(assert-event (equal (fn-bprl-undertake *rl-collided* "work-1" 3) *rl-collided*))
; A staged archive transaction on the node blocks the undertaking.
(defconst *rl-staged*
  (fn-bprl-with-node
   *rl-enqueued*
   (fn-node-prepare (fn-bp-state-node *rl-enqueued*) 10 "<rl2@example.invalid>"
                    *rl-payload* *rl-groups* "archive-rl2" "subject-rl2"
                    "operator-release" 4)))
(assert-event (fn-bp-binding-statep *rl-staged*))
(assert-event (consp (fn-node-stage (fn-bp-state-node *rl-staged*))))
(assert-event (equal (fn-bprl-undertake *rl-staged* "work-1" 3) *rl-staged*))
; No capacity: the ledger refuses before creating any pin.
(assert-event (equal (fn-bprl-undertake *rl-enqueued* "work-1" 100) *rl-enqueued*))
; Unknown work and non-positive charge.
(assert-event (equal (fn-bprl-undertake *rl-enqueued* "work-9" 3) *rl-enqueued*))
(assert-event (equal (fn-bprl-undertake *rl-enqueued* "work-1" 0) *rl-enqueued*))
; A second undertaking of the same obligation is a known-id refusal.
(assert-event (equal (fn-bprl-undertake *rl-undertaken* "work-1" 3) *rl-undertaken*))

; -----------------------------------------------------------------------------
; Journal wrapper

(defconst *rl-release-record*
  '(:release "receipt-1" "work-1" "subject-rl" "receipt-authority"
             "policy-1" "terms-1" "home-incarnation-1"))
(assert-event (fn-bprl-release-recordp *rl-release-record*))
(assert-event (not (fn-bp-journal-recordp *rl-release-record*)))
(assert-event (equal (fn-bprl-apply-journal-record *rl-receipted* *rl-release-record*)
                     (list t *rl-released* '((:released "work-1")))))
; The host-called function refuses the record it does not know.
(assert-event (equal (car (fn-bp-apply-journal-record *rl-receipted* *rl-release-record*)) nil))
; A release record whose evidence disagrees with the computed decision is refused.
(assert-event (equal (fn-bprl-apply-journal-record
                      *rl-receipted*
                      '(:release "receipt-1" "work-1" "subject-other" "receipt-authority"
                                 "policy-1" "terms-1" "home-incarnation-1"))
                     (list nil *rl-receipted* nil)))
; Replaying the release twice is refused the second time.
(assert-event (equal (car (fn-bprl-apply-journal-record *rl-released* *rl-release-record*)) nil))
(assert-event (equal (fn-bprl-apply-journal-record *rl-enqueued* '(:undertake "work-1" 3))
                     (list t *rl-undertaken* '((:undertaken "work-1")))))
(assert-event (equal (car (fn-bprl-apply-journal-record *rl-undertaken* '(:undertake "work-1" 3))) nil))
; An ordinary fn-bp record goes to the host-called function unchanged.
(defconst *rl-transport-record* '(:transport "work-1" "attempt-0" 0 :forwarded))
(assert-event (fn-bp-journal-recordp *rl-transport-record*))
(assert-event (equal (fn-bprl-apply-journal-record *rl-undertaken* *rl-transport-record*)
                     (fn-bp-apply-journal-record *rl-undertaken* *rl-transport-record*)))

; -----------------------------------------------------------------------------
; must-fail siblings

; fn-bprl-release-preserves-independent-pin without its inequality: the
; released pin itself is the counterexample.
(must-fail
 (defthm rl-teeth-released-pin-is-not-independent
   (equal (fn-retain-find-id "forward-1" (fn-bprl-pins *rl-released*))
          (fn-retain-find-id "forward-1" (fn-bprl-pins *rl-receipted*)))))
; fn-bprl-authorized-receipt-evidence-matches-required without authorization:
; a wrong-subject receipt renders to a different string.
(must-fail
 (defthm rl-teeth-unauthorized-evidence-does-not-match
   (equal (fn-bprl-evidence-string
           (fn-bprl-receipt-evidence
            (fn-bp-make-receipt "receipt-1" "work-1" "subject-other"
                                "receipt-authority" "dtn://peer/fn" "policy-1"
                                "home-incarnation-1" "authorization-context-1"
                                "terms-1")))
          (fn-bprl-required-evidence *rl-config* *rl-work*))))
; The decision without its pin premise: the unpinned receipted state.
(must-fail
 (defthm rl-teeth-no-pin-no-release
   (fn-bprl-decision-okp (fn-bprl-release-decision *rl-unpinned-receipted* "receipt-1"))))
; The undertaking without the stage guard would have to change a staged node.
(must-fail
 (defthm rl-teeth-staged-node-refuses
   (not (equal (fn-bprl-undertake *rl-staged* "work-1" 3) *rl-staged*))))
