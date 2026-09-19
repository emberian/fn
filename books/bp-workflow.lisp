; fn BPv7 durable-outbox workflow experiment.
;
; This book models local fn workflow decisions around a BPA.  It does not
; define a portable payload grammar, a BP implementation, cryptography, or a
; claim that a BP status report is application acceptance.

(in-package "ACL2")

(include-book "node-invariants")
; fn-node-statep is withdrawn at node's export (core, 2026-09-19); the guards below open it.
(local (in-theory (enable fn-node-statep)))

; -----------------------------------------------------------------------------
; Total record selectors

(defun fn-bp-nth (n x)
  (declare (xargs :guard t :measure (nfix n)))
  (if (not (and (integerp n) (fn-ag-less 0 n)))
      (fn-ag-car x)
    (fn-bp-nth (1- n) (fn-ag-cdr x))))

; Config: (schema local-eid peer-eid policy-id receipt-authority lifetime
;          node-incarnation authorization-context).
(defun fn-bp-config-schema (x) (declare (xargs :guard t)) (fn-bp-nth 0 x))
(defun fn-bp-config-local-eid (x) (declare (xargs :guard t)) (fn-bp-nth 1 x))
(defun fn-bp-config-peer-eid (x) (declare (xargs :guard t)) (fn-bp-nth 2 x))
(defun fn-bp-config-policy-id (x) (declare (xargs :guard t)) (fn-bp-nth 3 x))
(defun fn-bp-config-authority (x) (declare (xargs :guard t)) (fn-bp-nth 4 x))
(defun fn-bp-config-lifetime (x) (declare (xargs :guard t)) (fn-bp-nth 5 x))
(defun fn-bp-config-incarnation (x) (declare (xargs :guard t)) (fn-bp-nth 6 x))
(defun fn-bp-config-auth-context (x) (declare (xargs :guard t)) (fn-bp-nth 7 x))

(defun fn-bp-make-config (local-eid peer-eid policy-id authority lifetime
                                    incarnation auth-context)
  (declare (xargs :guard t))
  (list 1 local-eid peer-eid policy-id authority lifetime
        incarnation auth-context))

(defun fn-bp-configp (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 8)
       (equal (fn-bp-config-schema x) 1)
       (stringp (fn-bp-config-local-eid x))
       (stringp (fn-bp-config-peer-eid x))
       (stringp (fn-bp-config-policy-id x))
       (stringp (fn-bp-config-authority x))
       (posp (fn-bp-config-lifetime x))
       (stringp (fn-bp-config-incarnation x))
       (stringp (fn-bp-config-auth-context x))))

; Attempt: (attempt-id generation transport-status bp-lifetime).
(defun fn-bp-attempt-id (x) (declare (xargs :guard t)) (fn-bp-nth 0 x))
(defun fn-bp-attempt-generation (x) (declare (xargs :guard t)) (fn-bp-nth 1 x))
(defun fn-bp-attempt-status (x) (declare (xargs :guard t)) (fn-bp-nth 2 x))
(defun fn-bp-attempt-lifetime (x) (declare (xargs :guard t)) (fn-bp-nth 3 x))

(defun fn-bp-transport-statusp (x)
  (declare (xargs :guard t))
  (member-equal x '(:intent :bpa-submit-replied :bpa-accepted :attempted
                    :forwarded :delivered :deleted :expired :unknown
                    :no-contact :inbound-persisted :dequeued
                    :restart-observed)))

(defun fn-bp-retryable-statusp (x)
  (declare (xargs :guard t))
  (member-equal x '(:deleted :expired :unknown :no-contact
                    :restart-observed)))

(defun fn-bp-make-attempt (id generation status lifetime)
  (declare (xargs :guard t))
  (list id generation status lifetime))

(defun fn-bp-attemptp (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 4)
       (stringp (fn-bp-attempt-id x))
       (natp (fn-bp-attempt-generation x))
       (fn-bp-transport-statusp (fn-bp-attempt-status x))
       (posp (fn-bp-attempt-lifetime x))))

; Application receipt evidence:
; (receipt-id work-id subject issuer-eid peer-eid policy-id incarnation
;             authorization-context terms-id).
; A checked instance is an explicit A-POLICY input, not a cryptographic proof.
(defun fn-bp-receipt-id (x) (declare (xargs :guard t)) (fn-bp-nth 0 x))
(defun fn-bp-receipt-work-id (x) (declare (xargs :guard t)) (fn-bp-nth 1 x))
(defun fn-bp-receipt-subject (x) (declare (xargs :guard t)) (fn-bp-nth 2 x))
(defun fn-bp-receipt-issuer (x) (declare (xargs :guard t)) (fn-bp-nth 3 x))
(defun fn-bp-receipt-peer-eid (x) (declare (xargs :guard t)) (fn-bp-nth 4 x))
(defun fn-bp-receipt-policy-id (x) (declare (xargs :guard t)) (fn-bp-nth 5 x))
(defun fn-bp-receipt-incarnation (x) (declare (xargs :guard t)) (fn-bp-nth 6 x))
(defun fn-bp-receipt-auth-context (x) (declare (xargs :guard t)) (fn-bp-nth 7 x))
(defun fn-bp-receipt-terms-id (x) (declare (xargs :guard t)) (fn-bp-nth 8 x))

(defun fn-bp-make-receipt (receipt-id work-id subject issuer peer-eid
                                      policy-id incarnation auth-context terms-id)
  (declare (xargs :guard t))
  (list receipt-id work-id subject issuer peer-eid policy-id
        incarnation auth-context terms-id))

(defun fn-bp-receiptp (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 9)
       (stringp (fn-bp-receipt-id x))
       (stringp (fn-bp-receipt-work-id x))
       (stringp (fn-bp-receipt-subject x))
       (stringp (fn-bp-receipt-issuer x))
       (stringp (fn-bp-receipt-peer-eid x))
       (stringp (fn-bp-receipt-policy-id x))
       (stringp (fn-bp-receipt-incarnation x))
       (stringp (fn-bp-receipt-auth-context x))
       (stringp (fn-bp-receipt-terms-id x))))

(defun fn-bp-receipt-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-bp-receiptp (car xs))
           (fn-bp-receipt-listp (cdr xs)))
    (null xs)))

; Work: (work-id msgid subject archive-obligation-id forward-obligation-id
;        peer-eid policy-id incarnation authorization-context terms-id
;        next-attempt-generation attempt receipt).
(defun fn-bp-work-id (x) (declare (xargs :guard t)) (fn-bp-nth 0 x))
(defun fn-bp-work-msgid (x) (declare (xargs :guard t)) (fn-bp-nth 1 x))
(defun fn-bp-work-subject (x) (declare (xargs :guard t)) (fn-bp-nth 2 x))
(defun fn-bp-work-archive-id (x) (declare (xargs :guard t)) (fn-bp-nth 3 x))
(defun fn-bp-work-obligation-id (x) (declare (xargs :guard t)) (fn-bp-nth 4 x))
(defun fn-bp-work-peer-eid (x) (declare (xargs :guard t)) (fn-bp-nth 5 x))
(defun fn-bp-work-policy-id (x) (declare (xargs :guard t)) (fn-bp-nth 6 x))
(defun fn-bp-work-incarnation (x) (declare (xargs :guard t)) (fn-bp-nth 7 x))
(defun fn-bp-work-auth-context (x) (declare (xargs :guard t)) (fn-bp-nth 8 x))
(defun fn-bp-work-terms-id (x) (declare (xargs :guard t)) (fn-bp-nth 9 x))
(defun fn-bp-work-next-generation (x) (declare (xargs :guard t)) (fn-bp-nth 10 x))
(defun fn-bp-work-attempt (x) (declare (xargs :guard t)) (fn-bp-nth 11 x))
(defun fn-bp-work-receipt (x) (declare (xargs :guard t)) (fn-bp-nth 12 x))

(defun fn-bp-make-work (work-id msgid subject archive-id obligation-id
                                peer-eid policy-id incarnation auth-context
                                terms-id next-generation attempt receipt)
  (declare (xargs :guard t))
  (list work-id msgid subject archive-id obligation-id peer-eid policy-id
        incarnation auth-context terms-id next-generation attempt receipt))

(defun fn-bp-workp (config x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 13)
       (stringp (fn-bp-work-id x))
       (stringp (fn-bp-work-msgid x))
       (stringp (fn-bp-work-subject x))
       (stringp (fn-bp-work-archive-id x))
       (stringp (fn-bp-work-obligation-id x))
       (equal (fn-bp-work-peer-eid x) (fn-bp-config-peer-eid config))
       (equal (fn-bp-work-policy-id x) (fn-bp-config-policy-id config))
       (equal (fn-bp-work-incarnation x) (fn-bp-config-incarnation config))
       (equal (fn-bp-work-auth-context x) (fn-bp-config-auth-context config))
       (stringp (fn-bp-work-terms-id x))
       (natp (fn-bp-work-next-generation x))
       (or (null (fn-bp-work-attempt x))
           (and (fn-bp-attemptp (fn-bp-work-attempt x))
                (< (fn-bp-attempt-generation (fn-bp-work-attempt x))
                   (fn-bp-work-next-generation x))))
       (or (null (fn-bp-work-receipt x))
           (fn-bp-receiptp (fn-bp-work-receipt x)))))

(defun fn-bp-work-listp (config xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-bp-workp config (car xs))
           (fn-bp-work-listp config (cdr xs)))
    (null xs)))

(defun fn-bp-find-work (work-id xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (equal work-id (fn-bp-work-id (car xs)))
          (car xs)
        (fn-bp-find-work work-id (cdr xs)))
    nil))

(defun fn-bp-find-work-by-msgid (msgid xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (equal msgid (fn-bp-work-msgid (car xs)))
          (car xs)
        (fn-bp-find-work-by-msgid msgid (cdr xs)))
    nil))

(defun fn-bp-replace-work (work xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (equal (fn-bp-work-id work) (fn-bp-work-id (car xs)))
          (cons work (cdr xs))
        (cons (car xs) (fn-bp-replace-work work (cdr xs))))
    nil))

(defun fn-bp-work-outstandingp (work)
  (declare (xargs :guard t))
  (and (consp work) (null (fn-bp-work-receipt work))))

(defun fn-bp-work-retryablep (work)
  (declare (xargs :guard t))
  (and (fn-bp-work-outstandingp work)
       (or (null (fn-bp-work-attempt work))
           (fn-bp-retryable-statusp
            (fn-bp-attempt-status (fn-bp-work-attempt work))))))

(defun fn-bp-authorized-receiptp (config work receipt)
  (declare (xargs :guard t))
  (and (fn-bp-configp config)
       (fn-bp-workp config work)
       (fn-bp-receiptp receipt)
       (equal (fn-bp-receipt-work-id receipt) (fn-bp-work-id work))
       (equal (fn-bp-receipt-subject receipt) (fn-bp-work-subject work))
       (equal (fn-bp-receipt-issuer receipt) (fn-bp-config-authority config))
       (equal (fn-bp-receipt-peer-eid receipt) (fn-bp-work-peer-eid work))
       (equal (fn-bp-receipt-policy-id receipt) (fn-bp-work-policy-id work))
       (equal (fn-bp-receipt-incarnation receipt)
              (fn-bp-work-incarnation work))
       (equal (fn-bp-receipt-auth-context receipt)
              (fn-bp-work-auth-context work))
       (equal (fn-bp-receipt-terms-id receipt) (fn-bp-work-terms-id work))))

(defun fn-bp-work-with-attempt (work attempt)
  (declare (xargs :guard t))
  (fn-bp-make-work
   (fn-bp-work-id work) (fn-bp-work-msgid work) (fn-bp-work-subject work)
   (fn-bp-work-archive-id work) (fn-bp-work-obligation-id work)
   (fn-bp-work-peer-eid work) (fn-bp-work-policy-id work)
   (fn-bp-work-incarnation work) (fn-bp-work-auth-context work)
   (fn-bp-work-terms-id work) (1+ (nfix (fn-bp-attempt-generation attempt)))
   attempt (fn-bp-work-receipt work)))

(defun fn-bp-work-with-receipt (work receipt)
  (declare (xargs :guard t))
  (fn-bp-make-work
   (fn-bp-work-id work) (fn-bp-work-msgid work) (fn-bp-work-subject work)
   (fn-bp-work-archive-id work) (fn-bp-work-obligation-id work)
   (fn-bp-work-peer-eid work) (fn-bp-work-policy-id work)
   (fn-bp-work-incarnation work) (fn-bp-work-auth-context work)
   (fn-bp-work-terms-id work) (fn-bp-work-next-generation work)
   (fn-bp-work-attempt work) receipt))

(defun fn-bp-work-with-status (work status)
  (declare (xargs :guard t))
  (let ((attempt (fn-bp-work-attempt work)))
    (fn-bp-work-with-attempt
     work (fn-bp-make-attempt (fn-bp-attempt-id attempt)
                              (fn-bp-attempt-generation attempt)
                              status (fn-bp-attempt-lifetime attempt)))))

; -----------------------------------------------------------------------------
; Journal intents and durable workflow state

; Pending transaction: (kind transaction-id transaction-generation work receipt).
(defun fn-bp-pending-kind (x) (declare (xargs :guard t)) (fn-bp-nth 0 x))
(defun fn-bp-pending-txid (x) (declare (xargs :guard t)) (fn-bp-nth 1 x))
(defun fn-bp-pending-generation (x) (declare (xargs :guard t)) (fn-bp-nth 2 x))
(defun fn-bp-pending-work (x) (declare (xargs :guard t)) (fn-bp-nth 3 x))
(defun fn-bp-pending-receipt (x) (declare (xargs :guard t)) (fn-bp-nth 4 x))

(defun fn-bp-make-pending (kind txid generation work receipt)
  (declare (xargs :guard t))
  (list kind txid generation work receipt))

(defun fn-bp-pendingp (config x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 5)
       (member-equal (fn-bp-pending-kind x) '(:enqueue :attempt :receipt))
       (natp (fn-bp-pending-txid x))
       (natp (fn-bp-pending-generation x))
       (fn-bp-workp config (fn-bp-pending-work x))
       (if (equal (fn-bp-pending-kind x) :receipt)
           (and (fn-bp-receiptp (fn-bp-pending-receipt x))
                (equal (fn-bp-work-receipt (fn-bp-pending-work x))
                       (fn-bp-pending-receipt x)))
         (and (null (fn-bp-pending-receipt x))
              (if (equal (fn-bp-pending-kind x) :attempt)
                  (consp (fn-bp-work-attempt (fn-bp-pending-work x)))
                t)))))

; Reserved transaction pair: (transaction-id transaction-generation).  A pair
; enters this history when a preparation succeeds, before its outcome is known,
; and is never removed.  Thus aborted and uncertain intents cannot donate their
; identity to a later operation.
(defun fn-bp-make-tx-key (txid generation)
  (declare (xargs :guard t))
  (list txid generation))

(defun fn-bp-tx-keyp (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 2)
       (natp (fn-bp-nth 0 x)) (natp (fn-bp-nth 1 x))))

(defun fn-bp-tx-key-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-bp-tx-keyp (car xs))
           (fn-bp-tx-key-listp (cdr xs)))
    (null xs)))

; State: (node config durable-works durable-receipt-history pending fencedp
;         reserved-transaction-pairs).
(defun fn-bp-state-node (x) (declare (xargs :guard t)) (fn-bp-nth 0 x))
(defun fn-bp-state-config (x) (declare (xargs :guard t)) (fn-bp-nth 1 x))
(defun fn-bp-state-works (x) (declare (xargs :guard t)) (fn-bp-nth 2 x))
(defun fn-bp-state-receipts (x) (declare (xargs :guard t)) (fn-bp-nth 3 x))
(defun fn-bp-state-pending (x) (declare (xargs :guard t)) (fn-bp-nth 4 x))
(defun fn-bp-state-fenced (x) (declare (xargs :guard t)) (fn-bp-nth 5 x))
(defun fn-bp-state-used-txs (x) (declare (xargs :guard t)) (fn-bp-nth 6 x))

(defun fn-bp-make-state (node config works receipts pending fenced used-txs)
  (declare (xargs :guard t))
  (list node config works receipts pending fenced used-txs))

(defun fn-bp-statep (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 7)
       (fn-node-statep (fn-bp-state-node x))
       (fn-bp-configp (fn-bp-state-config x))
       (fn-bp-work-listp (fn-bp-state-config x) (fn-bp-state-works x))
       (fn-bp-receipt-listp (fn-bp-state-receipts x))
       (or (null (fn-bp-state-pending x))
           (fn-bp-pendingp (fn-bp-state-config x)
                           (fn-bp-state-pending x)))
       (or (null (fn-bp-state-fenced x))
           (equal (fn-bp-state-fenced x) t))
       (or (null (fn-bp-state-fenced x))
           (consp (fn-bp-state-pending x)))
       (fn-bp-tx-key-listp (fn-bp-state-used-txs x))))

(defun fn-bp-initial-state (node config)
  (declare (xargs :guard t))
  (if (and (fn-node-statep node) (fn-bp-configp config))
      (fn-bp-make-state node config nil nil nil nil nil)
    nil))

(defun fn-bp-pending-matchesp (s txid generation)
  (declare (xargs :guard t))
  (and (fn-bp-statep s)
       (consp (fn-bp-state-pending s))
       (equal txid (fn-bp-pending-txid (fn-bp-state-pending s)))
       (equal generation
              (fn-bp-pending-generation (fn-bp-state-pending s)))))

(defun fn-bp-work-boundp (node work)
  (declare (xargs :guard t))
  (let ((binding (fn-node-find-binding (fn-bp-work-msgid work)
                                       (fn-node-bindings node))))
    (and (consp binding)
         (equal (fn-node-binding-subject binding) (fn-bp-work-subject work))
         (equal (fn-node-binding-id binding) (fn-bp-work-archive-id work)))))

(defun fn-bp-works-boundp (node works)
  (declare (xargs :guard t))
  (if (consp works)
      (and (fn-bp-work-boundp node (car works))
           (fn-bp-works-boundp node (cdr works)))
    t))

; -----------------------------------------------------------------------------
; Prepared durable mutations

(defun fn-bp-prepare-enqueue (s txid tx-generation work-id msgid
                                obligation-id policy-id terms-id)
  (declare (xargs :guard t))
  (if (or (not (fn-bp-statep s))
          (consp (fn-bp-state-pending s))
          (fn-bp-state-fenced s)
          (not (natp txid))
          (not (natp tx-generation))
          (not (stringp work-id))
          (not (stringp msgid))
          (not (stringp obligation-id))
          (not (stringp terms-id))
          (not (equal policy-id
                      (fn-bp-config-policy-id (fn-bp-state-config s))))
          (fn-ag-member (fn-bp-make-tx-key txid tx-generation)
                        (fn-bp-state-used-txs s))
          (fn-bp-find-work work-id (fn-bp-state-works s))
          (fn-bp-find-work-by-msgid msgid (fn-bp-state-works s)))
      s
    (let ((binding (fn-node-find-binding
                    msgid (fn-node-bindings (fn-bp-state-node s)))))
      (if (not (consp binding))
          s
        (let ((work
               (fn-bp-make-work
                work-id msgid (fn-node-binding-subject binding)
                (fn-node-binding-id binding) obligation-id
                (fn-bp-config-peer-eid (fn-bp-state-config s))
                policy-id
                (fn-bp-config-incarnation (fn-bp-state-config s))
                (fn-bp-config-auth-context (fn-bp-state-config s))
                terms-id 0 nil nil)))
          (fn-bp-make-state
           (fn-bp-state-node s) (fn-bp-state-config s)
           (fn-bp-state-works s) (fn-bp-state-receipts s)
           (fn-bp-make-pending :enqueue txid tx-generation work nil) nil
           (cons (fn-bp-make-tx-key txid tx-generation)
                 (fn-bp-state-used-txs s))))))))

(defun fn-bp-prepare-attempt (s txid tx-generation work-id attempt-id)
  (declare (xargs :guard t))
  (if (or (not (fn-bp-statep s))
          (consp (fn-bp-state-pending s))
          (fn-bp-state-fenced s)
          (not (natp txid))
          (not (natp tx-generation))
          (not (stringp attempt-id))
          (fn-ag-member (fn-bp-make-tx-key txid tx-generation)
                        (fn-bp-state-used-txs s)))
      s
    (let ((work (fn-bp-find-work work-id (fn-bp-state-works s))))
      (if (not (fn-bp-work-retryablep work))
          s
        (let* ((attempt
                (fn-bp-make-attempt
                 attempt-id (fn-bp-work-next-generation work) :intent
                 (fn-bp-config-lifetime (fn-bp-state-config s))))
               (next-work (fn-bp-work-with-attempt work attempt)))
          (fn-bp-make-state
           (fn-bp-state-node s) (fn-bp-state-config s)
           (fn-bp-state-works s) (fn-bp-state-receipts s)
           (fn-bp-make-pending :attempt txid tx-generation next-work nil)
           nil (cons (fn-bp-make-tx-key txid tx-generation)
                     (fn-bp-state-used-txs s))))))))

(defun fn-bp-prepare-receipt (s txid tx-generation receipt policy-authorizedp)
  (declare (xargs :guard t))
  (if (or (not (fn-bp-statep s))
          (consp (fn-bp-state-pending s))
          (fn-bp-state-fenced s)
          (not (natp txid))
          (not (natp tx-generation))
          (not (equal policy-authorizedp t))
          (fn-ag-member (fn-bp-make-tx-key txid tx-generation)
                        (fn-bp-state-used-txs s)))
      s
    (let ((work (fn-bp-find-work (fn-bp-receipt-work-id receipt)
                                 (fn-bp-state-works s))))
      (if (or (not (fn-bp-work-outstandingp work))
              (not (fn-bp-authorized-receiptp
                    (fn-bp-state-config s) work receipt)))
          s
        (fn-bp-make-state
         (fn-bp-state-node s) (fn-bp-state-config s)
         (fn-bp-state-works s) (fn-bp-state-receipts s)
         (fn-bp-make-pending
          :receipt txid tx-generation
          (fn-bp-work-with-receipt work receipt) receipt)
         nil (cons (fn-bp-make-tx-key txid tx-generation)
                   (fn-bp-state-used-txs s)))))))

(defun fn-bp-apply-pending (s pending)
  (declare (xargs :guard t))
  (let ((kind (fn-bp-pending-kind pending))
        (work (fn-bp-pending-work pending)))
    (fn-bp-make-state
     (fn-bp-state-node s) (fn-bp-state-config s)
     (if (equal kind :enqueue)
         (cons work (fn-bp-state-works s))
       (fn-bp-replace-work work (fn-bp-state-works s)))
     (if (equal kind :receipt)
         (cons (fn-bp-pending-receipt pending) (fn-bp-state-receipts s))
       (fn-bp-state-receipts s))
     nil nil (fn-bp-state-used-txs s))))

(defun fn-bp-effect-for-pending (s pending)
  (declare (xargs :guard t))
  (let ((kind (fn-bp-pending-kind pending))
        (work (fn-bp-pending-work pending)))
    (if (equal kind :enqueue)
        (list :enqueue-ack (fn-bp-work-id work))
      (if (equal kind :attempt)
          (list :submit
                (fn-bp-work-id work)
                (fn-bp-attempt-id (fn-bp-work-attempt work))
                (fn-bp-attempt-generation (fn-bp-work-attempt work))
                (fn-bp-config-local-eid (fn-bp-state-config s))
                (fn-bp-config-peer-eid (fn-bp-state-config s))
                (fn-bp-attempt-lifetime (fn-bp-work-attempt work)))
        (list :receipt-ack (fn-bp-receipt-id
                            (fn-bp-pending-receipt pending)))))))

; Result: (state effects).
(defun fn-bp-make-result (st effects)
  (declare (xargs :guard t))
  (list st effects))
(defun fn-bp-result-state (x) (declare (xargs :guard t)) (fn-bp-nth 0 x))
(defun fn-bp-result-effects (x) (declare (xargs :guard t)) (fn-bp-nth 1 x))

(defun fn-bp-complete (s txid generation outcome)
  (declare (xargs :guard t))
  (if (or (not (fn-bp-pending-matchesp s txid generation))
          (fn-bp-state-fenced s))
      (fn-bp-make-result s nil)
    (let ((pending (fn-bp-state-pending s)))
      (if (equal outcome :durable)
          (fn-bp-make-result (fn-bp-apply-pending s pending)
                             (list (fn-bp-effect-for-pending s pending)))
        (if (equal outcome :aborted)
            (fn-bp-make-result
             (fn-bp-make-state
              (fn-bp-state-node s) (fn-bp-state-config s)
              (fn-bp-state-works s) (fn-bp-state-receipts s) nil nil
              (fn-bp-state-used-txs s))
             nil)
          (if (equal outcome :indeterminate)
              (fn-bp-make-result
               (fn-bp-make-state
                (fn-bp-state-node s) (fn-bp-state-config s)
                (fn-bp-state-works s) (fn-bp-state-receipts s) pending t
                (fn-bp-state-used-txs s))
               (list (list :recover-required txid generation)))
            (fn-bp-make-result s nil)))))))

(defun fn-bp-recovery-pending (pending)
  (declare (xargs :guard t))
  (if (equal (fn-bp-pending-kind pending) :attempt)
      (let ((work (fn-bp-pending-work pending)))
        (fn-bp-make-pending
         :attempt (fn-bp-pending-txid pending)
         (fn-bp-pending-generation pending)
         (fn-bp-work-with-status work :unknown) nil))
    pending))

(defun fn-bp-recover (s txid generation result)
  (declare (xargs :guard t))
  (if (or (not (fn-bp-pending-matchesp s txid generation))
          (not (equal (fn-bp-state-fenced s) t)))
      (fn-bp-make-result s nil)
    (let ((pending (fn-bp-state-pending s)))
      (if (equal result :committed)
          (let ((recovered (fn-bp-recovery-pending pending)))
            (fn-bp-make-result
             (fn-bp-apply-pending s recovered)
             (if (equal (fn-bp-pending-kind pending) :attempt)
                 nil
               (list (fn-bp-effect-for-pending s pending)))))
        (if (equal result :absent)
            (fn-bp-make-result
             (fn-bp-make-state
              (fn-bp-state-node s) (fn-bp-state-config s)
              (fn-bp-state-works s) (fn-bp-state-receipts s) nil nil
              (fn-bp-state-used-txs s))
             nil)
          (fn-bp-make-result s nil))))))

; -----------------------------------------------------------------------------
; Durable observations and restart

; Attempt lifecycle.  A live status is one that transport evidence may still
; advance.  The rank orders the lifecycle: durable intent, BPA reply, BPA
; inventory, transmission attempt, forwarding, inbound persistence, dequeue,
; delivery, then the retryable end states.  An observation is accepted only if
; it repeats the current status or strictly advances a live one.  :delivered
; leaves only through an explicit policy retry (fn-bp-request-retry), and a
; retryable status leaves only through a new attempt at a new generation
; (fn-bp-prepare-attempt).  No observation returns an attempt to :intent, so
; the one-shot submit gate keyed on :intent cannot be reopened by transport
; evidence.  See bp-workflow-transport-invariants for the theorems.
(defun fn-bp-live-statusp (x)
  (declare (xargs :guard t))
  (member-equal x '(:intent :bpa-submit-replied :bpa-accepted :attempted
                    :forwarded :inbound-persisted :dequeued)))

(defun fn-bp-status-rank (x)
  (declare (xargs :guard t))
  (cond ((equal x :intent) 0)
        ((equal x :bpa-submit-replied) 1)
        ((equal x :bpa-accepted) 2)
        ((equal x :attempted) 3)
        ((equal x :forwarded) 4)
        ((equal x :inbound-persisted) 5)
        ((equal x :dequeued) 6)
        ((equal x :delivered) 7)
        (t 8)))

(defun fn-bp-transport-transition-okp (old new)
  (declare (xargs :guard t))
  (and (fn-bp-transport-statusp new)
       (or (equal old new)
           (and (fn-bp-live-statusp old)
                (< (fn-bp-status-rank old) (fn-bp-status-rank new))))))

(defun fn-bp-observe-transport (s work-id attempt-id generation status)
  (declare (xargs :guard t))
  (if (or (not (fn-bp-statep s))
          (consp (fn-bp-state-pending s))
          (fn-bp-state-fenced s))
      s
    (let* ((work (fn-bp-find-work work-id (fn-bp-state-works s)))
           (attempt (fn-bp-work-attempt work)))
      (if (or (not (consp attempt))
              (not (equal attempt-id (fn-bp-attempt-id attempt)))
              (not (equal generation (fn-bp-attempt-generation attempt)))
              (not (fn-bp-transport-transition-okp
                    (fn-bp-attempt-status attempt) status)))
          s
        (fn-bp-make-state
         (fn-bp-state-node s) (fn-bp-state-config s)
         (fn-bp-replace-work (fn-bp-work-with-status work status)
                             (fn-bp-state-works s))
         (fn-bp-state-receipts s) nil nil (fn-bp-state-used-txs s))))))

; An explicit local policy decision may retry a delivered bundle whose fn
; application receipt was lost.  BP delivery alone never closes the work.
(defun fn-bp-request-retry (s work-id attempt-id generation policy-id)
  (declare (xargs :guard t))
  (if (or (not (fn-bp-statep s))
          (consp (fn-bp-state-pending s))
          (fn-bp-state-fenced s)
          (not (equal policy-id
                      (fn-bp-config-policy-id (fn-bp-state-config s)))))
      s
    (let* ((work (fn-bp-find-work work-id (fn-bp-state-works s)))
           (attempt (fn-bp-work-attempt work)))
      (if (or (not (fn-bp-work-outstandingp work))
              (not (consp attempt))
              (not (equal attempt-id (fn-bp-attempt-id attempt)))
              (not (equal generation (fn-bp-attempt-generation attempt))))
          s
        (fn-bp-make-state
         (fn-bp-state-node s) (fn-bp-state-config s)
         (fn-bp-replace-work (fn-bp-work-with-status work :unknown)
                             (fn-bp-state-works s))
         (fn-bp-state-receipts s) nil nil (fn-bp-state-used-txs s))))))

(defun fn-bp-restart-work (work)
  (declare (xargs :guard t))
  (let ((attempt (fn-bp-work-attempt work)))
    (if (and (consp attempt)
             (not (fn-bp-retryable-statusp
                   (fn-bp-attempt-status attempt)))
             (not (equal (fn-bp-attempt-status attempt) :delivered)))
        (fn-bp-work-with-status work :restart-observed)
      work)))

(defun fn-bp-restart-works (works)
  (declare (xargs :guard t))
  (if (consp works)
      (cons (fn-bp-restart-work (car works))
            (fn-bp-restart-works (cdr works)))
    nil))

(defun fn-bp-restart (s)
  (declare (xargs :guard t))
  (if (not (fn-bp-statep s))
      s
    (fn-bp-make-state
     (fn-bp-state-node s) (fn-bp-state-config s)
     (fn-bp-restart-works (fn-bp-state-works s))
     (fn-bp-state-receipts s) (fn-bp-state-pending s)
     (if (consp (fn-bp-state-pending s)) t (fn-bp-state-fenced s))
     (fn-bp-state-used-txs s))))

; -----------------------------------------------------------------------------
; Event dispatcher and finite traces

(defun fn-bp-event-kind (x) (declare (xargs :guard t)) (fn-bp-nth 0 x))

(defun fn-bp-enqueue-prepare-event (txid tx-generation work-id msgid
                                          obligation-id policy-id terms-id)
  (declare (xargs :guard t))
  (list :enqueue-prepare txid tx-generation work-id msgid obligation-id
        policy-id terms-id))

(defun fn-bp-attempt-prepare-event (txid tx-generation work-id attempt-id)
  (declare (xargs :guard t))
  (list :attempt-prepare txid tx-generation work-id attempt-id))

(defun fn-bp-receipt-prepare-event (txid tx-generation receipt
                                          policy-authorizedp)
  (declare (xargs :guard t))
  (list :receipt-prepare txid tx-generation receipt policy-authorizedp))

(defun fn-bp-storage-complete-event (txid tx-generation outcome)
  (declare (xargs :guard t))
  (list :storage-complete txid tx-generation outcome))

(defun fn-bp-storage-recover-event (txid tx-generation result)
  (declare (xargs :guard t))
  (list :storage-recover txid tx-generation result))

(defun fn-bp-transport-event (work-id attempt-id attempt-generation status)
  (declare (xargs :guard t))
  (list :transport work-id attempt-id attempt-generation status))

(defun fn-bp-no-contact-event (work-id attempt-id attempt-generation)
  (declare (xargs :guard t))
  (list :no-contact work-id attempt-id attempt-generation))

(defun fn-bp-retry-request-event (work-id attempt-id attempt-generation
                                          policy-id)
  (declare (xargs :guard t))
  (list :retry-request work-id attempt-id attempt-generation policy-id))

(defun fn-bp-restart-event ()
  (declare (xargs :guard t))
  (list :restart))

(defun fn-bp-eventp (event)
  (declare (xargs :guard t))
  (let ((kind (fn-bp-event-kind event)))
    (if (equal kind :enqueue-prepare)
        (and (true-listp event) (equal (len event) 8)
             (natp (fn-bp-nth 1 event)) (natp (fn-bp-nth 2 event))
             (stringp (fn-bp-nth 3 event)) (stringp (fn-bp-nth 4 event))
             (stringp (fn-bp-nth 5 event)) (stringp (fn-bp-nth 6 event))
             (stringp (fn-bp-nth 7 event)))
      (if (equal kind :attempt-prepare)
          (and (true-listp event) (equal (len event) 5)
               (natp (fn-bp-nth 1 event)) (natp (fn-bp-nth 2 event))
               (stringp (fn-bp-nth 3 event)) (stringp (fn-bp-nth 4 event)))
        (if (equal kind :receipt-prepare)
            (and (true-listp event) (equal (len event) 5)
                 (natp (fn-bp-nth 1 event)) (natp (fn-bp-nth 2 event))
                 (fn-bp-receiptp (fn-bp-nth 3 event))
                 (or (null (fn-bp-nth 4 event))
                     (equal (fn-bp-nth 4 event) t)))
          (if (equal kind :storage-complete)
              (and (true-listp event) (equal (len event) 4)
                   (natp (fn-bp-nth 1 event)) (natp (fn-bp-nth 2 event))
                   (member-equal (fn-bp-nth 3 event)
                                 '(:durable :aborted :indeterminate)))
            (if (equal kind :storage-recover)
                (and (true-listp event) (equal (len event) 4)
                     (natp (fn-bp-nth 1 event))
                     (natp (fn-bp-nth 2 event))
                     (member-equal (fn-bp-nth 3 event)
                                   '(:committed :absent)))
              (if (equal kind :transport)
                  (and (true-listp event) (equal (len event) 5)
                       (stringp (fn-bp-nth 1 event))
                       (stringp (fn-bp-nth 2 event))
                       (natp (fn-bp-nth 3 event))
                       (fn-bp-transport-statusp (fn-bp-nth 4 event)))
                (if (equal kind :no-contact)
                    (and (true-listp event) (equal (len event) 4)
                         (stringp (fn-bp-nth 1 event))
                         (stringp (fn-bp-nth 2 event))
                         (natp (fn-bp-nth 3 event)))
                  (if (equal kind :retry-request)
                      (and (true-listp event) (equal (len event) 5)
                           (stringp (fn-bp-nth 1 event))
                           (stringp (fn-bp-nth 2 event))
                           (natp (fn-bp-nth 3 event))
                           (stringp (fn-bp-nth 4 event)))
                    (and (equal kind :restart)
                         (true-listp event) (equal (len event) 1))))))))))))

(defun fn-bp-step (s event)
  (declare (xargs :guard t))
  (let ((kind (fn-bp-event-kind event)))
    (if (equal kind :enqueue-prepare)
        (fn-bp-make-result
         (fn-bp-prepare-enqueue
          s (fn-bp-nth 1 event) (fn-bp-nth 2 event) (fn-bp-nth 3 event)
          (fn-bp-nth 4 event) (fn-bp-nth 5 event) (fn-bp-nth 6 event)
          (fn-bp-nth 7 event))
         nil)
      (if (equal kind :attempt-prepare)
          (fn-bp-make-result
           (fn-bp-prepare-attempt
            s (fn-bp-nth 1 event) (fn-bp-nth 2 event)
            (fn-bp-nth 3 event) (fn-bp-nth 4 event))
           nil)
        (if (equal kind :receipt-prepare)
            (fn-bp-make-result
             (fn-bp-prepare-receipt
              s (fn-bp-nth 1 event) (fn-bp-nth 2 event)
              (fn-bp-nth 3 event) (fn-bp-nth 4 event))
             nil)
          (if (equal kind :storage-complete)
              (fn-bp-complete s (fn-bp-nth 1 event) (fn-bp-nth 2 event)
                              (fn-bp-nth 3 event))
            (if (equal kind :storage-recover)
                (fn-bp-recover s (fn-bp-nth 1 event) (fn-bp-nth 2 event)
                               (fn-bp-nth 3 event))
              (if (equal kind :transport)
                  (fn-bp-make-result
                   (fn-bp-observe-transport
                    s (fn-bp-nth 1 event) (fn-bp-nth 2 event)
                    (fn-bp-nth 3 event) (fn-bp-nth 4 event))
                   nil)
                (if (equal kind :no-contact)
                    (fn-bp-make-result
                     (fn-bp-observe-transport
                      s (fn-bp-nth 1 event) (fn-bp-nth 2 event)
                      (fn-bp-nth 3 event) :no-contact)
                     nil)
                  (if (equal kind :retry-request)
                      (fn-bp-make-result
                       (fn-bp-request-retry
                        s (fn-bp-nth 1 event) (fn-bp-nth 2 event)
                        (fn-bp-nth 3 event) (fn-bp-nth 4 event))
                       nil)
                    (if (equal kind :restart)
                        (fn-bp-make-result (fn-bp-restart s) nil)
                      (fn-bp-make-result s nil))))))))))))

(defun fn-bp-trace (s events)
  (declare (xargs :guard t))
  (if (consp events)
      (fn-bp-trace (fn-bp-result-state (fn-bp-step s (car events)))
                   (cdr events))
    s))
