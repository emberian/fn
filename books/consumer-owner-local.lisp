; E2's first owner command profile: the local control socket's owner identity.
; This profile has immutable historical group-membership selection.  It does
; not use the mutable NNTP reader authorization view or grant peer access.
(in-package "ACL2")
(include-book "owner")
(include-book "consumer-store-projection")
(include-book "consumer-poll-index")

(defconst *fn-col-principal* '(108 111 99 97 108)) ; local
(defconst *fn-col-query-version* 1)
(defconst *fn-col-view-version* 0)

(defun fn-col-result-event (o result)
  (declare (xargs :guard (true-listp result)))
  (if (not (eq (fn-cp-nth 0 result) :write)) result
    (let* ((s (fn-own-store o))
           (txid (fn-state-next-txid (fn-node-acceptance (fn-sn-node s))))
           (event (fn-cpe-make (fn-sn-identity-next s) txid txid
                               (fn-cp-nth 1 result))))
      (if (fn-cpe-eventp event) (list :write event)
        (list :refused :coordinates)))))

; The host observes fresh entropy; ACL2 validates the two independent
; 32-octet identities and constructs the one durable bootstrap operation.
; No socket path, clock, configuration generation or endpoint names an
; incarnation.  A retry after ambiguous publication is resolved by reopen.
(defun fn-col-bootstrap (o history incarnation)
  (let ((s (fn-sn-consumer (fn-own-store o))))
    (if (or s (not (fn-cbor-octet-listp history))
            (not (fn-cbor-octet-listp incarnation))
            (not (equal (len history) 32))
            (not (equal (len incarnation) 32))
            (equal history incarnation))
        (list :refused :identity)
      (fn-col-result-event
       o (list :write (list :bootstrap history incarnation))))))

(defun fn-col-register (o consumer group)
  (let* ((store (fn-own-store o))
         (s (fn-sn-consumer store)))
    (if (or (not s) (not (fn-af-newsgroup-namep group))
            (not (fn-cp-idp group))
            (not (true-listp (fn-sn-groups store)))
            (not (member-equal (fn-record-octets-string group)
                               (fn-sn-groups store))))
        (list :refused :query)
      (fn-col-result-event
       o (fn-cp-register s *fn-col-principal* consumer group
                         *fn-col-query-version* *fn-col-view-version*)))))

(defun fn-col-ack (o cursor-octets)
  (let ((decoded (fn-cp-cursor-decode cursor-octets))
        (s (fn-sn-consumer (fn-own-store o))))
    (if (not (eq (fn-cp-nth 0 decoded) :ok)) decoded
      (if (not s) (list :refused :unbootstrapped)
        (fn-col-result-event
         o (fn-cp-ack s *fn-col-principal* *fn-col-query-version*
                      *fn-col-view-version* (fn-cp-nth 1 decoded)))))))

(defun fn-col-scope-entry (s consumer)
  "Look up one bounded consumer entry in this local owner's fixed scope."
  (let ((entry (and s (fn-cp-idp consumer)
                    (fn-cp-find consumer (fn-cp-nth 5 s)))))
    (if (and entry
             (equal (fn-cp-nth 2 entry) *fn-col-principal*)
             (equal (fn-cp-nth 4 entry) *fn-col-query-version*)
             (equal (fn-cp-nth 5 entry) *fn-col-view-version*)
             (fn-cp-idp (fn-cp-nth 3 entry))
             (natp (fn-cp-nth 7 entry))
             (natp (fn-cp-nth 3 s))
             (<= (fn-cp-nth 7 entry) (fn-cp-nth 3 s)))
        (list :scope entry)
      (list :refused :scope))))

(defun fn-col-position (o consumer)
  (let* ((s (fn-sn-consumer (fn-own-store o)))
         (scoped (fn-col-scope-entry s consumer)))
    (if (eq (car scoped) :scope)
        (list :position
              (fn-cp-cursor-encode
               (fn-cp-scope-cursor s (fn-cp-nth 1 scoped))))
      scoped)))

(defun fn-col-status (o consumer)
  "Return the committed ACK, journal frontier, and event-distance gap."
  (let* ((s (fn-sn-consumer (fn-own-store o)))
         (scoped (fn-col-scope-entry s consumer)))
    (if (eq (car scoped) :scope)
        (let ((ack (fn-cp-nth 7 (fn-cp-nth 1 scoped)))
              (frontier (fn-cp-nth 3 s)))
          (list :status ack frontier (- frontier ack)))
      scoped)))

(defthm fn-col-status-event-distance
  (implies (eq (car (fn-col-status o consumer)) :status)
           (and (<= (fn-cp-nth 1 (fn-col-status o consumer))
                    (fn-cp-nth 2 (fn-col-status o consumer)))
                (equal (fn-cp-nth 3 (fn-col-status o consumer))
                       (- (fn-cp-nth 2 (fn-col-status o consumer))
                          (fn-cp-nth 1 (fn-col-status o consumer))))))
  :rule-classes nil)

(defun fn-col-unregister (o consumer)
  (let ((s (fn-sn-consumer (fn-own-store o))))
    (if (not s) (list :refused :unbootstrapped)
      (fn-col-result-event
       o (fn-cp-unregister s *fn-col-principal* consumer)))))

(defun fn-col-poll (o consumer)
  (let* ((store (fn-own-store o))
         (s (fn-sn-consumer store))
         (scoped (fn-col-scope-entry s consumer)))
    (if (not (eq (car scoped) :scope))
        scoped
      (let* ((entry (fn-cp-nth 1 scoped))
             (position (fn-cp-nth 7 entry))
             (frontier (fn-cp-nth 3 s))
             (scan (fn-col-poll-scan
                    (fn-col-poll-window
                     (fn-col-poll-drop (fn-sf-records (fn-sn-files store))
                                       position)
                     *fn-col-poll-max-scan*)
                    (fn-cp-nth 3 entry) position frontier
                    *fn-col-poll-max-scan*)))
        (if (not (eq (car scan) :scan)) scan
          (let ((cursor (update-nth 9 (fn-cp-nth 1 scan)
                                    (fn-cp-scope-cursor s entry))))
            (list :poll (fn-cp-cursor-encode cursor)
                  (fn-cp-nth 2 scan))))))))

(verify-guards fn-col-result-event)
(verify-guards fn-col-bootstrap)
(verify-guards fn-col-register)
(verify-guards fn-col-ack)
(verify-guards fn-col-scope-entry)
(verify-guards fn-col-position)
(verify-guards fn-col-status)
(verify-guards fn-col-unregister)
(verify-guards fn-col-poll)
