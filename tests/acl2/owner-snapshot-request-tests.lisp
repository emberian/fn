; tests/acl2/owner-snapshot-request-tests.lisp -- teeth for
; books/owner-snapshot-request.lisp (row S7, lane operability-12, PRF-1050).

(in-package "ACL2")
(include-book "../../books/owner-snapshot-request")

; The request's words, each observation pair.
(assert-event (equal (fn-osn-request-word nil nil) :requested))
(assert-event (equal (fn-osn-request-word t nil) :snapshot-in-flight))
(assert-event (equal (fn-osn-request-word nil t) :target-exists))
(assert-event (equal (fn-osn-request-word t t) :snapshot-in-flight))

(assert-event (equal (fn-osn-request-status :requested) :accepted))
(assert-event (equal (fn-osn-request-status :snapshot-in-flight) :refused))
(assert-event (equal (fn-osn-request-status :target-exists) :refused))

; KEYSTONE fn-osn-one-snapshot-in-flight, reachable positive witness: the
; complete antecedent (a snapshot in flight, DIR absent) and the complete
; conclusion (the word is :snapshot-in-flight, so not :requested).
(assert-event (and (equal (fn-osn-request-word t nil) :snapshot-in-flight)
                   (not (equal (fn-osn-request-word t nil) :requested))))
; Hypothesis-removal witness: with no snapshot in flight the same DIR
; observation is :requested (the omitted hypothesis fails, the conclusion
; fails).
(assert-event (and (not (equal (fn-osn-request-word nil nil) :snapshot-in-flight))
                   (equal (fn-osn-request-word nil nil) :requested)))

; The status words.
(assert-event (equal (fn-osn-status-word t nil) :in-flight))
(assert-event (equal (fn-osn-status-word t '(:done . 7)) :in-flight))
(assert-event (equal (fn-osn-status-word nil '(:done . 7)) :done))
(assert-event (equal (fn-osn-status-word nil '(:failed . :copy-write)) :failed))
(assert-event (equal (fn-osn-status-word nil nil) :idle))
(assert-event (equal (fn-osn-status-status :failed) :refused))
(assert-event (equal (fn-osn-status-status :done) :accepted))
(assert-event (equal (fn-osn-status-status :in-flight) :accepted))

; The client reads every word back from its reply octets; other octets are
; no word.
(assert-event (equal (fn-osn-word-of-octets (fn-nctrl-reason-word :requested)) :requested))
(assert-event (equal (fn-osn-word-of-octets (fn-nctrl-reason-word :snapshot-in-flight))
                     :snapshot-in-flight))
(assert-event (equal (fn-osn-word-of-octets (fn-nctrl-reason-word :target-exists)) :target-exists))
(assert-event (equal (fn-osn-word-of-octets (fn-nctrl-reason-word :in-flight)) :in-flight))
(assert-event (equal (fn-osn-word-of-octets (fn-nctrl-reason-word :done)) :done))
(assert-event (equal (fn-osn-word-of-octets (fn-nctrl-reason-word :failed)) :failed))
(assert-event (equal (fn-osn-word-of-octets (fn-nctrl-reason-word :idle)) :idle))
(assert-event (equal (fn-osn-word-of-octets '(120 121)) nil))
(assert-event (equal (fn-osn-word-of-octets nil) nil))

; KEYSTONE fn-osn-bless-word-blessed-exactly-when (PRF-1050), reachable
; positive witness: the complete antecedent (marker present, the open :ok,
; the secret present) and the complete conclusion (:blessed, accepted).
(assert-event (and (equal (fn-osn-bless-word t :ok t) :blessed)
                   (equal (fn-osn-bless-status (fn-osn-bless-word t :ok t)) :accepted)))
; Hypothesis-removal witnesses, one per observation: each retained
; observation holds, the omitted one fails, and the verdict is that
; observation's name (never :blessed, refused).
(assert-event (and (equal :ok :ok) (equal t t)
                   (equal (fn-osn-bless-word nil :ok t) :snapshot-incomplete)
                   (not (equal (fn-osn-bless-word nil :ok t) :blessed))
                   (equal (fn-osn-bless-status :snapshot-incomplete) :refused)))
(assert-event (and (equal t t) (equal t t)
                   (not (equal "open refused reason=foreign-lineage: the log's segments do not hold the history from segment 2" :ok))
                   (equal (fn-osn-bless-word
                           t "open refused reason=foreign-lineage: the log's segments do not hold the history from segment 2" t)
                          :open-refused)
                   (not (equal (fn-osn-bless-word t "open refused reason=foreign-lineage" t) :blessed))
                   (equal (fn-osn-bless-status :open-refused) :refused)))
(assert-event (and (equal t t) (equal :ok :ok)
                   (equal (fn-osn-bless-word t :ok nil) :no-node-secret)
                   (not (equal (fn-osn-bless-word t :ok nil) :blessed))
                   (equal (fn-osn-bless-status :no-node-secret) :refused)))
; The first failing observation names the verdict: an absent marker is
; named even when the copy would not open and has no secret.
(assert-event (equal (fn-osn-bless-word nil "open refused reason=log-damaged" nil)
                     :snapshot-incomplete))
(assert-event (equal (fn-osn-bless-word t "open refused reason=log-damaged" nil)
                     :open-refused))
; An absent marker takes no open observation.
(assert-event (and (not (fn-osn-bless-open-needed nil))
                   (fn-osn-bless-open-needed t)
                   (equal (fn-osn-bless-word nil :never-observed t)
                          (fn-osn-bless-word nil :ok t))))

; The marker's text names the capture.
(assert-event (equal (fn-osn-marker-text 3 4096 9)
                     (concatenate 'string "fn snapshot 1" (coerce (list #\Newline) 'string)
                                  "active-segment=3 frontier=4096 files=9"
                                  (coerce (list #\Newline) 'string))))

; The lines: every word has one, and the refusals say what it would take.
(assert-event (natp (search "snapshot requested target=/var/backups/s1"
                            (fn-osn-request-line :requested "/var/backups/s1"))))
(assert-event (natp (search "reason=snapshot-in-flight"
                            (fn-osn-request-line :snapshot-in-flight "/var/backups/s1"))))
(assert-event (natp (search "reason=target-exists: /var/backups/s1 exists"
                            (fn-osn-request-line :target-exists "/var/backups/s1"))))
(assert-event (natp (search "what it would take"
                            (fn-osn-request-line :target-exists "/var/backups/s1"))))
(assert-event (natp (search "snapshot taken target=/var/backups/s1: complete"
                            (fn-osn-outcome-line :done "/var/backups/s1"))))
(assert-event (natp (search "snapshot failed target=/var/backups/s1"
                            (fn-osn-outcome-line :failed "/var/backups/s1"))))
(assert-event (natp (search "snapshot in-flight" (fn-osn-outcome-line :in-flight "/x"))))
(assert-event (natp (search "snapshot idle" (fn-osn-outcome-line :idle "/x"))))
(assert-event (natp (search "reason=no-owner" (fn-osn-status-no-owner-line))))
(assert-event (natp (search "blessed snapshot=/var/backups/s1 transactions=12:"
                            (fn-osn-bless-line :blessed "/var/backups/s1" :ok 12))))
(assert-event (natp (search "reason=snapshot-incomplete: /var/backups/s1 has no SNAPSHOT marker"
                            (fn-osn-bless-line :snapshot-incomplete "/var/backups/s1" :ok 0))))
(assert-event (natp (search "reason=open-refused: open refused reason=foreign-lineage"
                            (fn-osn-bless-line :open-refused "/var/backups/s1"
                                               "open refused reason=foreign-lineage: the log's segments do not hold the history from segment 2"
                                               0))))
(assert-event (natp (search "reason=no-node-secret: /var/backups/s1/keys holds no node-secret.key"
                            (fn-osn-bless-line :no-node-secret "/var/backups/s1" :ok 0))))
