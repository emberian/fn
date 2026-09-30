; SCN-1024 / PRF-1118. Actual durable Store revocation of a receipt signer.
(in-package "ACL2")
(include-book "../../books/receipt-revocation")
(include-book "bp-release-authority-tests")
(include-book "receipt-revocation-store-fixtures")

; The existing fixture accepted a signed article after enrolling principal 7.
; The same principal is the receipt signer authorized by the issuer boundary.
; Reuse only signature-shape observations, not a cryptographic-validity claim.
(defconst *rr-obs* (list *sit-ml-key* :verified :verified))
(make-event
 `(defconst *rr-tomb*
    ',(fn-hl-revoke-event 2 2 2 2 *sit-principal*
                         (fn-sn-keyring-snapshots *sit-after-composite*))))
(make-event
 `(defconst *rr-prepared*
    ',(fn-sn-prepare-identity (fn-sit-reserve *sit-after-composite*) *rr-tomb*)))
(make-event `(defconst *rr-completing* ',(fn-sit-publish *rr-prepared*)))
(make-event `(defconst *rr-after* ',(fn-sn-finish *rr-completing*)))

; Positive for the complete literal durable theorem: a nonempty Store and
; outstanding workflow obligation, accepted signature before revocation,
; current refusal after durable completion, exact old snapshots and verdicts.
(assert-event
 (let ((snapshots (fn-sn-keyring-snapshots *rr-completing*)))
  (and (consp (fn-sf-records (fn-sn-files *rr-completing*)))
       (consp (fn-sn-verdicts *rr-completing*))
       (fn-bp-work-outstandingp (fn-bp-find-work "work-1" (fn-bp-state-works *bra-wf*)))
       (fn-bpah-receipt-gatep *bra-signed-view* *bra-signed-cfg* snapshots *rr-obs*)
       (fn-bpah-receipt-release-record *bra-signed-view* *bra-signed-cfg*
                                       *bra-wf* snapshots *rr-obs*)
       (fn-hl-revoke-event 2 2 2 2 *sit-principal* snapshots)
       (fn-sn-completion-enabledp *rr-completing*)
       (equal (fn-sn-completion-record *rr-completing*) *rr-tomb*)
       (not (fn-stxk-find 2 snapshots))
       (equal (fn-bpsr-principal (fn-bpah-view-signed *bra-signed-view*)) *sit-principal*)
       (not (fn-bpah-receipt-gatep *bra-signed-view* *bra-signed-cfg*
                                  (fn-sn-keyring-snapshots *rr-after*) *rr-obs*))
       (equal (fn-bpah-receipt-release-record *bra-signed-view* *bra-signed-cfg*
                 *bra-wf* (fn-sn-keyring-snapshots *rr-after*) *rr-obs*) nil)
       (equal (fn-sn-keyring-snapshots *rr-after*) (cons *rr-tomb* snapshots))
       (equal (fn-sn-verdicts *rr-after*) (fn-sn-verdicts *rr-completing*))
       (equal (fn-node-retention (fn-sn-node *rr-after*))
              (fn-node-retention (fn-sn-node *rr-completing*))))))

; Constructor/signer theorem positive, all premises and both conclusions.
(assert-event
 (let* ((snapshots (fn-sn-keyring-snapshots *rr-completing*))
        (tomb (fn-hl-revoke-event 2 2 2 2 *sit-principal* snapshots)))
  (and tomb
       (equal (fn-bpsr-principal (fn-bpah-view-signed *bra-signed-view*)) *sit-principal*)
       (equal (fn-bpah-receipt-signer-keys (cons tomb snapshots) *sit-principal*) nil)
       (not (fn-bpah-receipt-gatep *bra-signed-view* *bra-signed-cfg* (cons tomb snapshots) *rr-obs*))
       (equal (fn-bpah-receipt-release-record *bra-signed-view* *bra-signed-cfg*
                 *bra-wf* (cons tomb snapshots) *rr-obs*) nil))))

; Remove constructor success: generation 1 is not the next generation.
; The unchanged principal equality holds, and the old current keys authorize.
(assert-event
 (let* ((snapshots (fn-sn-keyring-snapshots *rr-completing*))
        (tomb (fn-hl-revoke-event 2 2 2 1 *sit-principal* snapshots)))
  (and (not tomb)
       (equal (fn-bpsr-principal (fn-bpah-view-signed *bra-signed-view*)) *sit-principal*)
       (fn-bpah-receipt-signer-keys (cons tomb snapshots) *sit-principal*)
       (fn-bpah-receipt-gatep *bra-signed-view* *bra-signed-cfg* (cons tomb snapshots) *rr-obs*)
       (fn-bpah-receipt-release-record *bra-signed-view* *bra-signed-cfg*
                 *bra-wf* (cons tomb snapshots) *rr-obs*))))

; A second principal is enrolled in the actual Store, then revoked. Revoking
; another principal must not revoke this receipt signer (signer-match removal).
(defconst *rr-other-principal* (make-list 32 :initial-element 8))
(make-event
 `(defconst *rr-other-enrollment*
    ',(fn-hl-enroll-event 2 2 2 2 *rr-other-principal* *sit-keys*
                          (fn-sn-keyring-snapshots *sit-after-composite*))))
(make-event `(defconst *rr-other-before*
              ',(fn-sit-commit-identity *sit-after-composite* *rr-other-enrollment*)))
(make-event
 `(defconst *rr-other-tomb*
    ',(fn-hl-revoke-event 3 3 3 3 *rr-other-principal*
                          (fn-sn-keyring-snapshots *rr-other-before*))))
(make-event `(defconst *rr-other-completing*
              ',(fn-sit-publish (fn-sn-prepare-identity
                                (fn-sit-reserve *rr-other-before*) *rr-other-tomb*))))
(assert-event
 (let ((snapshots (fn-sn-keyring-snapshots *rr-other-completing*)))
  (and (fn-hl-revoke-event 3 3 3 3 *rr-other-principal* snapshots)
       (fn-sn-completion-enabledp *rr-other-completing*)
       (equal (fn-sn-completion-record *rr-other-completing*) *rr-other-tomb*)
       (not (fn-stxk-find 3 snapshots))
       (not (equal (fn-bpsr-principal (fn-bpah-view-signed *bra-signed-view*)) *rr-other-principal*))
       (fn-bpah-receipt-gatep *bra-signed-view* *bra-signed-cfg*
          (cons *rr-other-tomb* snapshots) *rr-obs*)
       (fn-bpah-receipt-release-record *bra-signed-view* *bra-signed-cfg* *bra-wf*
          (fn-sn-keyring-snapshots (fn-sn-finish *rr-other-completing*)) *rr-obs*))))

; Durable record-match removal: the actual completed event enrolls another
; principal rather than revoking the receipt signer. All other premises hold.
(make-event `(defconst *rr-other-enrolling*
              ',(fn-sit-publish (fn-sn-prepare-identity
                   (fn-sit-reserve *sit-after-composite*) *rr-other-enrollment*))))
(assert-event
 (let* ((s *rr-other-enrolling*) (snapshots (fn-sn-keyring-snapshots s))
        (tomb (fn-hl-revoke-event 2 2 2 2 *sit-principal* snapshots)))
  (and tomb (fn-sn-completion-enabledp s)
       (not (equal (fn-sn-completion-record s) tomb))
       (not (fn-stxk-find 2 snapshots))
       (equal (fn-bpsr-principal (fn-bpah-view-signed *bra-signed-view*)) *sit-principal*)
       (fn-bpah-receipt-release-record *bra-signed-view* *bra-signed-cfg* *bra-wf*
          (fn-sn-keyring-snapshots (fn-sn-finish s)) *rr-obs*))))

; Corrupted-state completion-gate removal: retain the exact durable completion
; record but replace the file phase. This is explicitly not a reachable cut.
(defconst *rr-wrong-phase*
 (fn-sn-update *rr-completing* (update-nth 1 :ready (fn-sn-files *rr-completing*))
               (fn-sn-node *rr-completing*)))
(assert-event
 (with-guard-checking :none
 (let* ((s *rr-wrong-phase*) (snapshots (fn-sn-keyring-snapshots s))
        (tomb (fn-hl-revoke-event 2 2 2 2 *sit-principal* snapshots)))
  (and tomb (not (fn-sn-completion-enabledp s))
       (equal (fn-sn-completion-record s) tomb)
       (not (fn-stxk-find 2 snapshots))
       (equal (fn-bpsr-principal (fn-bpah-view-signed *bra-signed-view*)) *sit-principal*)
       (fn-bpah-receipt-release-record *bra-signed-view* *bra-signed-cfg* *bra-wf*
          (fn-sn-keyring-snapshots (fn-sn-finish s)) *rr-obs*)))) )

; Corrupted-state fresh-generation removal: a future tombstone is inserted
; behind the still-current enrollment. All individual snapshots are typed,
; but the ordered history invariant has been violated. Replay recognizes the
; old identical snapshot and does not prepend it or change current authority.
(defun rr-test-with-snapshots (s snapshots)
  (fn-sn-make-v6
   (fn-sn-groups s) (fn-sn-capacity s) (fn-sn-files s) (fn-sn-node s)
   (fn-sn-keyring s) (fn-sn-index s) (fn-sn-keyring-generation s)
   (fn-sn-verdicts s) snapshots (fn-sn-identity-next s)
   (fn-sn-config-history s) (fn-sn-consumer s) (fn-sn-topic s) (fn-sn-event-index s)))
(defconst *rr-unordered*
 (rr-test-with-snapshots *rr-completing* (list *sit-enrollment* *rr-tomb*)))
(assert-event
 (let* ((s *rr-unordered*) (snapshots (fn-sn-keyring-snapshots s))
        (tomb (fn-hl-revoke-event 2 2 2 2 *sit-principal* snapshots)))
  (and tomb (fn-sn-completion-enabledp s)
       (equal (fn-sn-completion-record s) tomb)
       (fn-stxk-find 2 snapshots)
       (equal (fn-bpsr-principal (fn-bpah-view-signed *bra-signed-view*)) *sit-principal*)
       (fn-bpah-receipt-release-record *bra-signed-view* *bra-signed-cfg* *bra-wf*
          (fn-sn-keyring-snapshots (fn-sn-finish s)) *rr-obs*)
       (not (equal (fn-sn-keyring-snapshots (fn-sn-finish s)) (cons tomb snapshots))))))

; Past authorization still replays its already-accepted intent. Revocation
; cannot reinterpret that durable event as a newly submitted receipt. The
; prospective selector above is nil at the same time.
(assert-event
 (and (consp *bra-signed-record*)
      (car (fn-bprl-apply-journal-record *bra-wf* *bra-signed-record*))
      (not (fn-bpah-receipt-release-record *bra-signed-view* *bra-signed-cfg* *bra-wf*
               (fn-sn-keyring-snapshots *rr-after*) *rr-obs*))))

; Mutation: erasing prior snapshots, accepted verdicts or pins on revocation
; disagrees with actual completion of this nonempty accepted history.
(assert-event
 (and (consp (cdr (fn-sn-keyring-snapshots *rr-after*)))
      (consp (fn-sn-verdicts *rr-after*))
      (consp (fn-retain-pins (fn-node-retention (fn-sn-node *rr-after*))))))

; Positive for both literal finish-frame theorems, including all premises.
(assert-event
 (let* ((s *rr-completing*) (e (fn-sn-completion-record s)))
  (and (fn-sn-completion-enabledp s) (fn-stxk-p e)
       (not (fn-stxk-find (fn-stxk-keyring-generation e) (fn-sn-keyring-snapshots s)))
       (equal (fn-sn-keyring-snapshots (fn-sn-finish s))
              (cons e (fn-sn-keyring-snapshots s)))
       (consp (fn-sn-verdicts s))
       (equal (fn-sn-verdicts (fn-sn-finish s)) (fn-sn-verdicts s))
       (consp (fn-retain-pins (fn-node-retention (fn-sn-node s))))
       (equal (fn-node-retention (fn-sn-node (fn-sn-finish s)))
              (fn-node-retention (fn-sn-node s))))))

; Snapshot-kind removal from exact-history frame: this actual kind-4
; acceptance changes verdicts and does not prepend an enrollment snapshot.
(make-event `(defconst *rr-article-completing*
              ',(fn-sit-publish (fn-sn-prepare-identity
                   (fn-sit-reserve *sit-after-enrollment*) *sit-composite*))))
(assert-event
 (let* ((s *rr-article-completing*) (e (fn-sn-completion-record s)))
  (and (fn-sn-completion-enabledp s) (not (fn-stxk-p e))
       (not (fn-stxk-find (fn-stxk-keyring-generation e) (fn-sn-keyring-snapshots s)))
       (not (equal (fn-sn-keyring-snapshots (fn-sn-finish s))
                    (cons e (fn-sn-keyring-snapshots s))))
       (not (equal (fn-sn-verdicts (fn-sn-finish s)) (fn-sn-verdicts s))))))

(make-event
 `(defconst *rr-staged-retention*
    ',(fn-sn-prepare-retention
       (fn-sit-reserve *sit-after-composite*)
       (fn-store-retention-event-make :undertake 2 2 2
        "rr-forward" "rr-subject" "rr-evidence" 5))))

; Snapshot-kind removal from retention frame: actual undertaking adds a
; forward pin, affirming that the frame is specific to authority snapshots.
(assert-event
 (let ((s (fn-sit-publish *rr-staged-retention*)))
  (and (fn-sn-completion-enabledp s)
       (not (fn-stxk-p (fn-sn-completion-record s)))
       (not (equal (fn-node-retention (fn-sn-node (fn-sn-finish s)))
                    (fn-node-retention (fn-sn-node s)))))))

; Frame completion/freshness premise removals, affirm all retained premises.
(assert-event
 (with-guard-checking :none
 (let* ((s *rr-wrong-phase*) (e (fn-sn-completion-record s)))
  (and (not (fn-sn-completion-enabledp s)) (fn-stxk-p e)
       (not (fn-stxk-find (fn-stxk-keyring-generation e) (fn-sn-keyring-snapshots s)))
       (not (equal (fn-sn-keyring-snapshots (fn-sn-finish s))
                    (cons e (fn-sn-keyring-snapshots s))))))))
(assert-event
 (let* ((s *rr-unordered*) (e (fn-sn-completion-record s)))
  (and (fn-sn-completion-enabledp s) (fn-stxk-p e)
       (fn-stxk-find (fn-stxk-keyring-generation e) (fn-sn-keyring-snapshots s))
       (not (equal (fn-sn-keyring-snapshots (fn-sn-finish s))
                    (cons e (fn-sn-keyring-snapshots s)))))))
