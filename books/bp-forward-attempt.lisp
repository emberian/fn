; One retained-row transition for durable kind-8 attempts and kind-9 results.
; Live callbacks and ordered FNBS replay call these same functions.
(in-package "ACL2")
(include-book "bp-forward-image")
(set-verify-guards-eagerness 0)

(defun fn-bpnp-session-idp (session)
  (declare (xargs :guard t))
  (and (consp session)
       (fn-frame-natp (car session))
       (fn-frame-natp (cdr session))))

(defun fn-bpnp-forward-attempt-record
  (epoch op arrival identity peer session age)
  (declare (xargs :guard t))
  (list :bpnf-attempting epoch op arrival identity peer session age))

(defun fn-bpnp-forward-attempt-recordp (record)
  (declare (xargs :guard t))
  (and (true-listp record) (equal (len record) 8)
       (equal (car record) :bpnf-attempting)
       (fn-frame-natp (fn-bpn-nth 1 record))
       (fn-frame-natp (fn-bpn-nth 2 record))
       (fn-frame-natp (fn-bpn-nth 3 record))
       (fn-cbor-octet-listp (fn-bpn-nth 4 record))
       (consp (fn-bpn-nth 4 record))
       (<= (len (fn-bpn-nth 4 record)) 1024)
       (fn-bpp-eidp (fn-bpn-nth 5 record))
       (fn-bpnp-session-idp (fn-bpn-nth 6 record))
       (or (null (fn-bpn-nth 7 record))
           (fn-frame-natp (fn-bpn-nth 7 record)))))

;; Retry after an uncertain send (decision candidate of 2026-09-24, default
;; adopted by the coordinator, pending ember; specs/bp-node-machine.md 4.3.1).
;; A slot (:forwarding epoch op peer session retries) whose epoch precedes the
;; current process epoch names a durable kind 8 that no kind 9 settled before
;; its process died.  The row is offered again, with its unchanged held bundle,
;; on a later session to the same next hop; the receiver's bundle-id admission
;; is the duplicate control.  Each re-offer counts; at the bound the row stays
;; held with its reserved result debt and is reported, never re-offered.
(defconst *fn-bpnp-max-forward-retries* 3)

(defun fn-bpnp-attempt-retries (slot)
  (declare (xargs :guard t))
  (nfix (fn-bpn-nth 5 slot)))

; An attempt is uncertain when its process died before a kind 9 settled it
; (a :forwarding slot of an earlier epoch), or when a kind 9 recorded the
; transfer itself as :uncertain (the connection failed after the durable
; kind 8; fn-bpnp-tcpcl-outcome).  That kind 9 keeps the slot, headed
; :uncertain, so the count survives it exactly as it survives a restart.
(defun fn-bpnp-uncertain-attemptp (slot epoch peer)
  (declare (xargs :guard t))
  (and (or (and (equal (fn-bpn-nth 0 slot) :forwarding)
                (natp (fn-bpn-nth 1 slot))
                (natp epoch)
                (< (fn-bpn-nth 1 slot) epoch))
           (equal (fn-bpn-nth 0 slot) :uncertain))
       (equal (fn-bpn-nth 3 slot) peer)))

(defun fn-bpnp-retry-eligible-slotp (slot epoch peer)
  (declare (xargs :guard t))
  (and (fn-bpnp-uncertain-attemptp slot epoch peer)
       (< (fn-bpnp-attempt-retries slot) *fn-bpnp-max-forward-retries*)))

(defun fn-bpnp-stranded-slotp (slot epoch peer)
  (declare (xargs :guard t))
  (and (fn-bpnp-uncertain-attemptp slot epoch peer)
       (<= *fn-bpnp-max-forward-retries* (fn-bpnp-attempt-retries slot))))

(defun fn-bpnp-attempted-held (h record)
  (declare (xargs :guard (true-listp h)))
  (update-nth 13
              (list :forwarding (fn-bpn-nth 1 record) (fn-bpn-nth 2 record)
                    (fn-bpn-nth 5 record) (fn-bpn-nth 6 record)
                    (if (fn-bpn-nth 13 h)
                        (1+ (fn-bpnp-attempt-retries (fn-bpn-nth 13 h)))
                      0))
              h))

(defun fn-bpnp-attempt-matches-heldp (record h)
  (declare (xargs :guard t))
  (and (fn-bpnp-forward-attempt-recordp record)
       (true-listp h)
       (equal (fn-bpn-nth 0 h) :bpnf-held)
       (equal (fn-bpn-nth 3 h) (fn-bpn-nth 3 record))
       (equal (fn-bpah-held-primary-identity h) (fn-bpn-nth 4 record))
       (equal (fn-bpn-nth 11 h) (fn-bpn-nth 5 record))
       (equal (fn-bpn-nth 12 h) '(:forward-pending))
       (or (null (fn-bpn-nth 13 h))
           (fn-bpnp-retry-eligible-slotp
            (fn-bpn-nth 13 h) (fn-bpn-nth 1 record) (fn-bpn-nth 5 record)))
       (null (fn-bpn-nth 14 h))))

(defun fn-bpnp-attempt-replace (arrival record held)
  (declare (xargs :guard t :measure (acl2-count held)))
  (if (atom held) nil
    (if (equal arrival (fn-bpn-nth 3 (car held)))
        (if (true-listp (car held))
            (cons (fn-bpnp-attempted-held (car held) record) (cdr held))
          nil)
      (cons (car held)
            (fn-bpnp-attempt-replace arrival record (cdr held))))))

(defun fn-bpnp-attempt-apply (record held)
  (declare (xargs :guard t))
  (let* ((arrival (fn-bpn-nth 3 record))
         (h (fn-bpnf-find-arrival arrival held)))
    (if (and (equal (fn-bpnf-arrival-count arrival held) 1)
             (fn-bpnp-attempt-matches-heldp record h))
        (list :ready
              (fn-bpnp-attempt-replace arrival record held)
              (fn-bpnp-attempted-held h record))
      (list :fault :attempt-row))))

; What a transfer can report: the TCPCL outcome of one session.
(defun fn-bpnp-transfer-outcomep (outcome)
  (declare (xargs :guard t))
  (or (and (member-equal outcome '(:sent :failed :uncertain)) t)
      (and (true-listp outcome) (equal (len outcome) 2)
           (equal (car outcome) :refused)
           (fn-frame-natp (cadr outcome)))))

; A kind-9 outcome: a transfer outcome, or :resumed, the operator's durable
; re-arming of a stranded attempt (fn-bpnp-operator-resume-step).  No
; transfer reports :resumed; only the operator arm proposes it.
(defun fn-bpnp-forward-outcomep (outcome)
  (declare (xargs :guard t))
  (or (fn-bpnp-transfer-outcomep outcome)
      (equal outcome :resumed)))

(defun fn-bpnp-forward-terminalp (outcome)
  (declare (xargs :guard t))
  (or (equal outcome :sent) (equal outcome '(:refused 1))))

(defun fn-bpnp-forward-result-record
  (epoch op arrival identity attempt-epoch attempt-op session outcome)
  (declare (xargs :guard t))
  (list :bpnf-forwarded epoch op arrival identity
        attempt-epoch attempt-op session outcome))

(defun fn-bpnp-forward-result-recordp (record)
  (declare (xargs :guard t))
  (and (true-listp record) (equal (len record) 9)
       (equal (car record) :bpnf-forwarded)
       (fn-frame-natp (fn-bpn-nth 1 record))
       (fn-frame-natp (fn-bpn-nth 2 record))
       (fn-frame-natp (fn-bpn-nth 3 record))
       (fn-cbor-octet-listp (fn-bpn-nth 4 record))
       (consp (fn-bpn-nth 4 record))
       (<= (len (fn-bpn-nth 4 record)) 1024)
       (fn-frame-natp (fn-bpn-nth 5 record))
       (fn-frame-natp (fn-bpn-nth 6 record))
       (fn-bpnp-session-idp (fn-bpn-nth 7 record))
       (fn-bpnp-forward-outcomep (fn-bpn-nth 8 record))))

; A kind 9 settles the slot, except :uncertain, which keeps it (retries
; and all) headed :uncertain: the transfer may or may not have reached the
; peer, so the row is retried under the same bound.  :resumed clears it, so
; the next kind 8 counts from 0; the kind-8 and kind-9 rows keep the history.
(defun fn-bpnp-forward-result-slot (slot outcome)
  (declare (xargs :guard t))
  (if (and (equal outcome :uncertain) (consp slot))
      (cons :uncertain (cdr slot))
    nil))

(defun fn-bpnp-forward-result-held (h outcome)
  (declare (xargs :guard (true-listp h)))
  (update-nth 13 (fn-bpnp-forward-result-slot (fn-bpn-nth 13 h) outcome)
              (if (fn-bpnp-forward-terminalp outcome)
                  (update-nth 12 '(:dispatch-done) h)
                h)))

(defun fn-bpnp-attempt-slot-namesp (slot epoch op peer session)
  (declare (xargs :guard t))
  (and (true-listp slot) (equal (len slot) 6)
       (equal (fn-bpn-nth 0 slot) :forwarding)
       (equal (fn-bpn-nth 1 slot) epoch)
       (equal (fn-bpn-nth 2 slot) op)
       (equal (fn-bpn-nth 3 slot) peer)
       (equal (fn-bpn-nth 4 slot) session)))

; The slot a :resumed kind 9 re-arms: stranded at the record's own epoch
; (the epoch of the process that wrote it, so live and replay agree) for the
; row's next hop, naming the record's attempt, under either head.
(defun fn-bpnp-resume-slot-namesp (slot epoch op peer session record-epoch)
  (declare (xargs :guard t))
  (and (true-listp slot) (equal (len slot) 6)
       (fn-bpnp-stranded-slotp slot record-epoch peer)
       (equal (fn-bpn-nth 1 slot) epoch)
       (equal (fn-bpn-nth 2 slot) op)
       (equal (fn-bpn-nth 4 slot) session)))

(defun fn-bpnp-forward-result-matches-heldp (record h)
  (declare (xargs :guard t))
  (and (fn-bpnp-forward-result-recordp record)
       (true-listp h)
       (equal (fn-bpn-nth 0 h) :bpnf-held)
       (equal (fn-bpn-nth 3 h) (fn-bpn-nth 3 record))
       (equal (fn-bpah-held-primary-identity h) (fn-bpn-nth 4 record))
       (equal (fn-bpn-nth 12 h) '(:forward-pending))
       (if (equal (fn-bpn-nth 8 record) :resumed)
           (fn-bpnp-resume-slot-namesp
            (fn-bpn-nth 13 h) (fn-bpn-nth 5 record) (fn-bpn-nth 6 record)
            (fn-bpn-nth 11 h) (fn-bpn-nth 7 record) (fn-bpn-nth 1 record))
         (fn-bpnp-attempt-slot-namesp
          (fn-bpn-nth 13 h) (fn-bpn-nth 5 record) (fn-bpn-nth 6 record)
          (fn-bpn-nth 11 h) (fn-bpn-nth 7 record)))
       (null (fn-bpn-nth 14 h))))

(defun fn-bpnp-forward-result-replace (arrival outcome held)
  (declare (xargs :guard t :measure (acl2-count held)))
  (if (atom held) nil
    (if (equal arrival (fn-bpn-nth 3 (car held)))
        (if (true-listp (car held))
            (cons (fn-bpnp-forward-result-held (car held) outcome) (cdr held))
          nil)
      (cons (car held)
            (fn-bpnp-forward-result-replace arrival outcome (cdr held))))))

(defun fn-bpnp-forward-result-apply (record held)
  (declare (xargs :guard t))
  (let* ((arrival (fn-bpn-nth 3 record))
         (h (fn-bpnf-find-arrival arrival held))
         (outcome (fn-bpn-nth 8 record)))
    (if (and (equal (fn-bpnf-arrival-count arrival held) 1)
             (fn-bpnp-forward-result-matches-heldp record h))
        (list :ready
              (fn-bpnp-forward-result-replace arrival outcome held)
              (fn-bpnp-forward-result-held h outcome))
      (list :fault :result-row))))
