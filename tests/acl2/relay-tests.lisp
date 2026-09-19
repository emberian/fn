; Witness and teeth for the relay undertaking (wave 2, packet B).
;
; The witness is reachable end to end: Store ingress of a legacy article,
; receiver acceptance of the request for it, sender enqueue of the onward
; work, the recorded undertaking, the forwarding receipt intent, its commit,
; and the receipt ADU.  The crash constructor is exercised at the enqueue
; pending point and at the receipt intent point with every outcome, and the
; same content under an archival terms table yields an :archived receipt with
; no onward work at all.
(in-package "ACL2")
(include-book "../../books/relay-crash-invariants")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; Store with one durably accepted article (the receiver test's construction)

(defconst *ry-groups* '("fn.letters"))
(defconst *ry-map*
  (list (list '(102 110 46 108 101 116 116 101 114 115) "fn.letters")))
(defconst *ry-policy*
  (fn-bpi-make-policy "dtn://relay.lab/inbox" "dtn://relay.lab/inbox" *ry-map*
                      "archive:relay-1" "subject:relay-1"
                      "unsigned-ingress-v0" 1 "relay-policy" "terms-1"
                      "dtn://relay.lab/issuer"))
(defconst *ry-ingress-context*
  (fn-bpi-make-context "dtn://relay.lab/inbox" "dtn://home.lab"
                       "local-bid-1" 300))
(defconst *ry-adu*
  '(77 101 115 115 97 103 101 45 73 68 58 32 60 114 101 99 101 105 112 116 45 49 64 101 120 97 109 112 108 101 62 13 10
    78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 108 101 116 116 101 114 115 13 10 13 10
    66 111 100 121 13 10))
(defun ry-reserve (s)
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil)
                                :frontier-file :ok)
                      :frontier-replace :ok)
            :frontier-directory :ok))
(defconst *ry-prepared*
  (fn-bpi-ingress-prepare (ry-reserve (fn-sn-initial *ry-groups* 20))
                          *ry-policy* *ry-ingress-context* *ry-adu*))
(defconst *ry-record* (fn-bpi-result-record *ry-prepared*))
(defconst *ry-store* (fn-bpi-finish-prepared (fn-bpi-result-store *ry-prepared*)))
(assert-event (fn-bpi-durably-acceptedp *ry-store* *ry-record*))
(defconst *ry-msgid* (fn-record-msgid *ry-record*))

; -----------------------------------------------------------------------------
; Relay: receiver config, sender config, terms table

(defconst *ry-request*
  (fn-bpa-make-request "up-work-1" "subject:relay-1" "dtn://home.lab"
                       "dtn://relay.lab/inbox" "relay-policy" "home-inc-7"
                       "wire-auth-context" "terms-forward" *ry-adu*))
(defconst *ry-receiver-config*
  (fn-bpr-make-config "dtn://relay.lab/inbox" "relay-policy"
                      "dtn://relay.lab/issuer"))
(defconst *ry-sender-config*
  (fn-bp-make-config "dtn://relay.lab/fn" "dtn://next.lab/fn" "relay-policy"
                     "next-authority" 1000 "relay-inc-1" "auth-ctx-1"))
(defconst *ry-terms* '(("terms-forward" . :forwarding)
                       ("terms-archive" . :archived)))
(defconst *ry-initial*
  (fn-relay-initial-state *ry-store* *ry-receiver-config* *ry-sender-config*
                          *ry-terms*))
(assert-event (fn-relay-invp *ry-initial*))

(defconst *ry-accepted* (fn-relay-accept *ry-initial* *ry-record* *ry-request* t))
(assert-event (equal (car *ry-accepted*) :accepted))
(defconst *ry-ctx-state* (car (cdr *ry-accepted*)))
(assert-event (fn-relay-invp *ry-ctx-state*))
(defconst *ry-ctx*
  (fn-bpr-find-context "up-work-1"
                       (fn-bpr-state-contexts (fn-relay-receiver *ry-ctx-state*))))
(assert-event (consp *ry-ctx*))
(assert-event (fn-relay-content-durablep (fn-relay-node *ry-ctx-state*) *ry-ctx*))
(assert-event (equal (fn-bpr-context-msgid *ry-ctx*) *ry-msgid*))

; -----------------------------------------------------------------------------
; No onward work, no forwarding promise

(assert-event (equal (fn-relay-undertake *ry-ctx-state* "up-work-1" "receipt-1" t)
                     (list nil *ry-ctx-state*)))
(assert-event (equal (fn-relay-record-undertaking *ry-ctx-state* "up-work-1" "onward-1")
                     *ry-ctx-state*))

; The enqueue-then-crash gap: a pending (not yet durable) enqueue backs nothing.
(defconst *ry-enqueue-pending*
  (car (fn-relay-sender-step
        *ry-ctx-state*
        (fn-bp-enqueue-prepare-event 10 0 "onward-1" *ry-msgid* "forward-1"
                                     "relay-policy" "terms-forward"))))
(assert-event (consp (fn-bp-state-pending (fn-relay-sender *ry-enqueue-pending*))))
(assert-event (fn-relay-invp *ry-enqueue-pending*))
(assert-event (not (fn-relay-onward-presentp (fn-relay-sender *ry-enqueue-pending*)
                                             "onward-1")))
(assert-event (equal (fn-relay-record-undertaking *ry-enqueue-pending* "up-work-1" "onward-1")
                     *ry-enqueue-pending*))
(assert-event (equal (fn-relay-undertake *ry-enqueue-pending* "up-work-1" "receipt-1" t)
                     (list nil *ry-enqueue-pending*)))
; Crash here.  Enqueue found absent: no work, no promise.
(defconst *ry-crash-absent* (fn-relay-crash-recover *ry-enqueue-pending* :absent :absent))
(assert-event (fn-relay-invp *ry-crash-absent*))
(assert-event (null (fn-relay-receipt *ry-crash-absent* "up-work-1")))
(assert-event (null (fn-bp-state-works (fn-relay-sender *ry-crash-absent*))))
; Enqueue found committed: the work is durable, and still no promise.
(defconst *ry-crash-committed*
  (fn-relay-crash-recover *ry-enqueue-pending* :absent :committed))
(assert-event (fn-relay-invp *ry-crash-committed*))
(assert-event (fn-relay-onward-durablep (fn-relay-sender *ry-crash-committed*)
                                        "onward-1" *ry-ctx*))
(assert-event (null (fn-relay-receipt *ry-crash-committed* "up-work-1")))

; -----------------------------------------------------------------------------
; The straight path

(defconst *ry-enqueued*
  (car (fn-relay-sender-step *ry-enqueue-pending*
                             (fn-bp-storage-complete-event 10 0 :durable))))
(assert-event (fn-relay-invp *ry-enqueued*))
(assert-event (fn-relay-onward-durablep (fn-relay-sender *ry-enqueued*)
                                        "onward-1" *ry-ctx*))
; Durable work but no recorded undertaking: still no forwarding promise.
(assert-event (equal (fn-relay-undertake *ry-enqueued* "up-work-1" "receipt-1" t)
                     (list nil *ry-enqueued*)))
; A work that does not name this content cannot back the promise.
(assert-event (equal (fn-relay-record-undertaking *ry-enqueued* "up-work-1" "onward-9")
                     *ry-enqueued*))
(defconst *ry-undertaking*
  (fn-relay-record-undertaking *ry-enqueued* "up-work-1" "onward-1"))
(assert-event (not (equal *ry-undertaking* *ry-enqueued*)))
(assert-event (fn-relay-invp *ry-undertaking*))
; Recorded twice is refused.
(assert-event (equal (fn-relay-record-undertaking *ry-undertaking* "up-work-1" "onward-1")
                     *ry-undertaking*))

(defconst *ry-promise-pending* (fn-relay-undertake *ry-undertaking* "up-work-1" "receipt-1" t))
(assert-event (equal (car *ry-promise-pending*) :forwarding))
(defconst *ry-pending* (car (cdr *ry-promise-pending*)))
(assert-event (fn-relay-invp *ry-pending*))
; An intent is not a promise: no typed receipt and no ADU yet.
(assert-event (null (fn-relay-receipt *ry-pending* "up-work-1")))
(assert-event (null (fn-relay-receipt-adu *ry-pending* *ry-request*)))
; Crash at the receipt intent.  Absent: no promise.  Committed: promise with
; its obligation.  The sender has nothing pending, so its result is moot.
(defconst *ry-pending-absent* (fn-relay-crash-recover *ry-pending* :absent :absent))
(assert-event (fn-relay-invp *ry-pending-absent*))
(assert-event (null (fn-relay-receipt *ry-pending-absent* "up-work-1")))
(defconst *ry-pending-committed* (fn-relay-crash-recover *ry-pending* :committed :absent))
(assert-event (fn-relay-invp *ry-pending-committed*))
(assert-event (equal (car (fn-relay-receipt *ry-pending-committed* "up-work-1")) :forwarding))
(assert-event (fn-relay-onward-presentp (fn-relay-sender *ry-pending-committed*) "onward-1"))

(defconst *ry-committed*
  (fn-relay-commit-receipt *ry-pending* "up-work-1" "receipt-1" :committed))
(assert-event (fn-relay-invp *ry-committed*))
(assert-event (equal (car (fn-relay-receipt *ry-committed* "up-work-1")) :forwarding))
(assert-event (consp (fn-relay-receipt-adu *ry-committed* *ry-request*)))
(assert-event (equal (fn-relay-receipt-adu *ry-committed* *ry-request*)
                     (fn-bpr-receipt-adu (fn-relay-receiver *ry-committed*) *ry-request*)))
(assert-event (fn-bpa-receiptp (car (cdr (fn-relay-receipt *ry-committed* "up-work-1")))))

; The promise survives sender progress and a restart.
(defconst *ry-after-attempt*
  (car (fn-relay-sender-step
        (car (fn-relay-sender-step
              *ry-committed*
              (fn-bp-attempt-prepare-event 11 0 "onward-1" "attempt-0")))
        (fn-bp-storage-complete-event 11 0 :durable))))
(assert-event (fn-relay-invp *ry-after-attempt*))
(defconst *ry-restarted* (fn-relay-crash-recover *ry-after-attempt* :absent :absent))
(assert-event (fn-relay-invp *ry-restarted*))
(assert-event (equal (car (fn-relay-receipt *ry-restarted* "up-work-1")) :forwarding))
(assert-event (fn-relay-onward-presentp (fn-relay-sender *ry-restarted*) "onward-1"))

; -----------------------------------------------------------------------------
; Archival acceptance is a different promise over the same bytes

(defconst *ry-archival*
  (fn-relay-make-state *ry-store* (fn-relay-receiver *ry-ctx-state*)
                       (fn-relay-sender *ry-ctx-state*)
                       '(("terms-forward" . :archived)) nil))
(assert-event (fn-relay-invp *ry-archival*))
(defconst *ry-archival-pending* (fn-relay-undertake *ry-archival* "up-work-1" "receipt-a" t))
(assert-event (equal (car *ry-archival-pending*) :archived))
(defconst *ry-archived*
  (fn-relay-commit-receipt (car (cdr *ry-archival-pending*)) "up-work-1" "receipt-a"
                           :committed))
(assert-event (fn-relay-invp *ry-archived*))
(assert-event (equal (car (fn-relay-receipt *ry-archived* "up-work-1")) :archived))
(assert-event (null (fn-bp-state-works (fn-relay-sender *ry-archived*))))
(assert-event (not (equal (car (fn-relay-receipt *ry-archived* "up-work-1"))
                          (car (fn-relay-receipt *ry-committed* "up-work-1")))))
; Unknown terms promise nothing; the relay's table has no destination kind.
(defconst *ry-unknown-terms*
  (fn-relay-make-state *ry-store* (fn-relay-receiver *ry-ctx-state*)
                       (fn-relay-sender *ry-ctx-state*) nil nil))
(assert-event (equal (fn-relay-undertake *ry-unknown-terms* "up-work-1" "receipt-u" t)
                     (list nil *ry-unknown-terms*)))
(assert-event (not (fn-relay-kindp :destination)))
(assert-event (not (fn-relay-terms-tablep '(("terms-x" . :destination)))))
; A-POLICY nil is refused by the receiver's entry point, and so here.
(assert-event (equal (fn-relay-undertake *ry-undertaking* "up-work-1" "receipt-1" nil)
                     (list nil *ry-undertaking*)))
; Unknown upstream context.
(assert-event (equal (fn-relay-undertake *ry-undertaking* "up-work-9" "receipt-1" t)
                     (list nil *ry-undertaking*)))

; -----------------------------------------------------------------------------
; What the invariant excludes: a forwarding receipt with no undertaking.  It
; is a structurally valid relay state and it is exactly what no transition
; and no crash produces.

(defconst *ry-promise-alone*
  (fn-relay-make-state *ry-store* (fn-relay-receiver *ry-committed*)
                       (fn-relay-sender *ry-ctx-state*) *ry-terms* nil))
(assert-event (fn-relay-statep *ry-promise-alone*))
(assert-event (equal (car (fn-relay-receipt *ry-promise-alone* "up-work-1")) :forwarding))
(assert-event (not (fn-relay-invp *ry-promise-alone*)))
; Same with the undertaking recorded but the work gone: also excluded.
(defconst *ry-promise-unbacked*
  (fn-relay-make-state *ry-store* (fn-relay-receiver *ry-committed*)
                       (fn-relay-sender *ry-ctx-state*) *ry-terms*
                       (fn-relay-undertakings *ry-committed*)))
(assert-event (fn-relay-statep *ry-promise-unbacked*))
(assert-event (not (fn-relay-invp *ry-promise-unbacked*)))

; -----------------------------------------------------------------------------
; must-fail siblings

; fn-relay-forwarding-receipt-has-durable-onward-obligation without invp.
(must-fail
 (defthm ry-teeth-promise-alone-has-no-obligation
   (consp (fn-relay-find-undertaking "up-work-1"
                                     (fn-relay-undertakings *ry-promise-alone*)))))
; A pending enqueue is not a durable onward work.
(must-fail
 (defthm ry-teeth-pending-enqueue-is-not-durable
   (fn-relay-onward-presentp (fn-relay-sender *ry-enqueue-pending*) "onward-1")))
; A receipt intent is not a promise.
(must-fail
 (defthm ry-teeth-intent-is-not-a-promise
   (consp (fn-relay-receipt *ry-pending* "up-work-1"))))
; Archival receipts carry no onward work: the forwarding conclusion is false there.
(must-fail
 (defthm ry-teeth-archived-receipt-has-no-onward-work
   (consp (fn-bp-state-works (fn-relay-sender *ry-archived*)))))
