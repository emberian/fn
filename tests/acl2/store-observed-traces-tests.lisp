; The process-root witnesses for the trace relation (D6), acknowledged-record
; retention across a real reopen (D5), and the teeth for both.  Every witness
; opens through fn-sn-open-observed, the entry host/store-node-host.lisp:27
; calls on each process start.
(in-package "ACL2")
(include-book "../../books/store-observed")

(defconst *fn-so-groups* '("fn.letters"))
(defconst *fn-so-empty*
  (fn-sn-open-observed *fn-so-groups* 10 0 nil))
(assert-event (fn-sn-open-okp *fn-so-empty*))
(assert-event (fn-snt-relation (fn-sn-open-state *fn-so-empty*)))
(defconst *fn-so-record0*
  (fn-record-make 0 0 0 "<observed@example>" '(65) *fn-so-groups*
                  "observed-pin" "observed-content" "observed-release" 1))
(defconst *fn-so-replayed*
  (fn-sn-open-observed *fn-so-groups* 10 1 (list *fn-so-record0*)))
(assert-event (fn-sn-open-okp *fn-so-replayed*))
(assert-event (fn-snt-relation (fn-sn-open-state *fn-so-replayed*)))

; Structurally valid but unreplayable: a record in a group this store does
; not configure.  This is the witness that :replay is a distinct refusal and
; the teeth for the recoverability hypothesis of
; fn-sn-open-observed-succeeds-on-recoverable-image.
(defconst *fn-so-alien*
  (fn-record-make 0 0 0 "<alien@example>" '(65) '("fn.other")
                  "alien-pin" "alien-content" "alien-release" 1))
(assert-event (fn-sn-observed-historyp 1 (list *fn-so-alien*)))
(assert-event (not (fn-sf-history-recoverablep *fn-so-groups* 10 (list *fn-so-alien*) 1)))
(assert-event (equal (fn-sn-open-observed *fn-so-groups* 10 1 (list *fn-so-alien*))
                     '(:error :replay)))
(assert-event (with-guard-checking :none (not (fn-sn-open-okp (fn-sn-open-observed *fn-so-groups* 10 1 (list *fn-so-alien*))))))
; Teeth for fn-sn-open-observed-success-has-live-history-relation: a refused
; open carries no state and the relation fails on what it does carry.
(assert-event (with-guard-checking :none (not (fn-snt-relation
                 (fn-sn-open-state
                  (fn-sn-open-observed *fn-so-groups* 10 1 (list *fn-so-alien*)))))))

; -----------------------------------------------------------------------------
; D6 witness: open from a two-record image with a consumed frontier gap and
; run a mixed trace including refusal, known abort, publication with
; acknowledgement, an uncertain link, crash and recovery.

(defconst *fn-so-live-groups* '("fn.letters" "fn.test"))
(defconst *fn-so-first*
  (fn-record-make 0 0 0 "<first@example>" '(65) *fn-so-live-groups*
                  "first-pin" "first-content" "first-release" 1))
; txid 1 was consumed without a record before this image was taken.
(defconst *fn-so-second*
  (fn-record-make 1 2 2 "<second@example>" '(66) '("fn.test")
                  "second-pin" "second-content" "second-release" 1))
; txid 3 was also consumed: the image frontier is 4.
(defconst *fn-so-gap-open*
  (fn-sn-open-observed *fn-so-live-groups* 10 4 (list *fn-so-first* *fn-so-second*)))
(assert-event (fn-sn-open-okp *fn-so-gap-open*))
(defconst *fn-so-gap-opened* (fn-sn-open-state *fn-so-gap-open*))
(assert-event (fn-snt-relation *fn-so-gap-opened*))
(assert-event (equal (fn-sn-node *fn-so-gap-opened*)
                     (fn-sf-replay-node *fn-so-live-groups* 10
                                        (list *fn-so-first* *fn-so-second*) 4)))
(assert-event (equal (fn-state-next-txid (fn-node-acceptance (fn-sn-node *fn-so-gap-opened*)))
                     4))
(assert-event (fn-sn-committed-recordp (fn-sn-node *fn-so-gap-opened*) *fn-so-first*))
(assert-event (fn-sn-committed-recordp (fn-sn-node *fn-so-gap-opened*) *fn-so-second*))

(defconst *fn-so-barriers*
  '((:io :recovery-barrier :ok) (:io :recovery-barrier :ok)
    (:io :recovery-barrier :ok) (:io :recovery-barrier :ok)
    (:io :recovery-barrier :ok)))
(defconst *fn-so-reserve*
  '((:io :start-frontier nil) (:io :frontier-file :ok)
    (:io :frontier-replace :ok) (:io :frontier-directory :ok)))
; txid 4 is refused; txid 5 is prepared then known-aborted; txid 6 is
; published and acknowledged; txid 7 is linked with an uncertain result.
(defconst *fn-so-third*
  (fn-record-make 2 5 5 "<third@example>" '(67) *fn-so-live-groups*
                  "third-pin" "third-content" "third-release" 1))
(defconst *fn-so-fourth*
  (fn-record-make 2 6 6 "<fourth@example>" '(68) '("fn.letters")
                  "fourth-pin" "fourth-content" "fourth-release" 1))
(defconst *fn-so-fifth*
  (fn-record-make 3 7 7 "<fifth@example>" '(69) '("fn.test")
                  "fifth-pin" "fifth-content" "fifth-release" 1))

(defconst *fn-so-acked*
  (fn-snrt-run *fn-so-gap-opened*
               (append *fn-so-barriers*
                       *fn-so-reserve* '((:refuse-reservation 4))
                       *fn-so-reserve* (list (list :prepare *fn-so-third*))
                       '((:known-abort))
                       *fn-so-reserve* (list (list :prepare *fn-so-fourth*))
                       '((:io :record-file :ok) (:io :record-link :ok)
                         (:io :record-directory :ok) (:finish)))))
(assert-event (fn-snt-relation *fn-so-acked*))
(assert-event (equal (fn-sf-phase (fn-sn-files *fn-so-acked*)) :ready))
(assert-event (equal (fn-sf-frontier (fn-sn-files *fn-so-acked*)) 7))
(assert-event (equal (fn-sf-successes (fn-sn-files *fn-so-acked*)) '((2 . 6))))
(assert-event (equal (fn-sf-records (fn-sn-files *fn-so-acked*))
                     (list *fn-so-first* *fn-so-second* *fn-so-fourth*)))
(assert-event (fn-sn-committed-recordp (fn-sn-node *fn-so-acked*) *fn-so-fourth*))
(assert-event (not (fn-sn-committed-recordp (fn-sn-node *fn-so-acked*) *fn-so-third*)))

(defconst *fn-so-mixed-final*
  (fn-snrt-run *fn-so-acked*
               (append *fn-so-reserve* (list (list :prepare *fn-so-fifth*))
                       '((:io :record-file :ok) (:io :record-link :error)
                         (:known-abort) (:finish)
                         (:crash :old :present) (:recover))
                       *fn-so-barriers*)))
(assert-event (fn-snt-relation *fn-so-mixed-final*))
(assert-event (equal (fn-sf-phase (fn-sn-files *fn-so-mixed-final*)) :ready))
(assert-event (equal (fn-sf-records (fn-sn-files *fn-so-mixed-final*))
                     (list *fn-so-first* *fn-so-second* *fn-so-fourth* *fn-so-fifth*)))
(assert-event (equal (fn-sf-successes (fn-sn-files *fn-so-mixed-final*)) '((2 . 6))))
(assert-event (equal (fn-sn-node *fn-so-mixed-final*)
                     (fn-sf-replay-node *fn-so-live-groups* 10
                                        (list *fn-so-first* *fn-so-second*
                                              *fn-so-fourth* *fn-so-fifth*)
                                        8)))
(assert-event (fn-sn-committed-recordp (fn-sn-node *fn-so-mixed-final*) *fn-so-fifth*))

; -----------------------------------------------------------------------------
; D5 witness: acknowledge, die at the final-link cut, reopen through the host
; entry on each admissible image.

(defconst *fn-so-pre-crash*
  (fn-snrt-run *fn-so-acked*
               (append *fn-so-reserve* (list (list :prepare *fn-so-fifth*))
                       '((:io :record-file :ok)))))
(assert-event (fn-snt-relation *fn-so-pre-crash*))
(assert-event (equal (fn-sf-phase (fn-sn-files *fn-so-pre-crash*)) :record-data-durable))
(assert-event (equal (fn-sf-frontier (fn-sn-files *fn-so-pre-crash*)) 8))
(assert-event (equal (fn-sf-successes (fn-sn-files *fn-so-pre-crash*)) '((2 . 6))))

(defconst *fn-so-image-absent*
  (list *fn-so-first* *fn-so-second* *fn-so-fourth*))
(defconst *fn-so-image-present*
  (list *fn-so-first* *fn-so-second* *fn-so-fourth* *fn-so-fifth*))
; The platform may leave either image (A-DURABILITY as hypothesis)...
(assert-event (fn-sf-crash-imagep (fn-sn-files *fn-so-pre-crash*) 8 *fn-so-image-absent*))
(assert-event (fn-sf-crash-imagep (fn-sn-files *fn-so-pre-crash*) 8 *fn-so-image-present*))
; ...but not one that drops the acknowledged record, nor one whose frontier
; is neither the stable value nor a live candidate.
(assert-event (not (fn-sf-crash-imagep (fn-sn-files *fn-so-pre-crash*) 8
                                       (list *fn-so-first* *fn-so-second*))))
(assert-event (not (fn-sf-crash-imagep (fn-sn-files *fn-so-pre-crash*) 7 *fn-so-image-absent*)))
(assert-event (not (fn-sf-crash-imagep (fn-sn-files *fn-so-pre-crash*) 9 *fn-so-image-absent*)))

(defconst *fn-so-reopen-absent*
  (fn-sn-open-observed *fn-so-live-groups* 10 8 *fn-so-image-absent*))
(defconst *fn-so-reopen-present*
  (fn-sn-open-observed *fn-so-live-groups* 10 8 *fn-so-image-present*))
(assert-event (fn-sn-open-okp *fn-so-reopen-absent*))
(assert-event (fn-sn-open-okp *fn-so-reopen-present*))
(assert-event (fn-snt-relation (fn-sn-open-state *fn-so-reopen-absent*)))
(assert-event (fn-snt-relation (fn-sn-open-state *fn-so-reopen-present*)))
(assert-event (fn-sf-record-has-pairp
               '(2 . 6) (fn-sf-records (fn-sn-files (fn-sn-open-state *fn-so-reopen-absent*)))))
(assert-event (fn-sf-record-has-pairp
               '(2 . 6) (fn-sf-records (fn-sn-files (fn-sn-open-state *fn-so-reopen-present*)))))
(assert-event (fn-sn-committed-recordp
               (fn-sn-node (fn-sn-open-state *fn-so-reopen-present*)) *fn-so-fourth*))
; Honest about what is not carried: the acknowledgement list is nil after
; reopen; the guarantee rides on records.
(assert-event (equal (fn-sf-successes (fn-sn-files (fn-sn-open-state *fn-so-reopen-present*)))
                     nil))
; Unacknowledged survival: the present image installs the fifth record; the
; absent image burns its txid and installs nothing.
(assert-event (fn-sn-committed-recordp
               (fn-sn-node (fn-sn-open-state *fn-so-reopen-present*)) *fn-so-fifth*))
(assert-event (not (fn-sn-committed-recordp
                    (fn-sn-node (fn-sn-open-state *fn-so-reopen-absent*)) *fn-so-fifth*)))
(assert-event (equal (fn-state-next-txid
                      (fn-node-acceptance (fn-sn-node (fn-sn-open-state *fn-so-reopen-absent*))))
                     8))

; The core-durable cut: death after fn-sn-finish returned is a crash from
; :ready; the only admissible image carries the acknowledged record.
(assert-event (fn-sf-crash-imagep (fn-sn-files *fn-so-acked*) 7 *fn-so-image-absent*))
(assert-event (not (fn-sf-crash-imagep (fn-sn-files *fn-so-acked*) 7
                                       (list *fn-so-first* *fn-so-second*))))
(assert-event (fn-sf-record-has-pairp
               '(2 . 6)
               (fn-sf-records
                (fn-sn-files
                 (fn-sn-open-state
                  (fn-sn-open-observed *fn-so-live-groups* 10 7 *fn-so-image-absent*))))))

; The reopened process continues: five barriers, another publication, another
; crash; the acknowledged record is still there
; (fn-snrt-acknowledged-record-retained-across-observed-reopen).
(defconst *fn-so-sixth*
  (fn-record-make 4 8 8 "<sixth@example>" '(70) *fn-so-live-groups*
                  "sixth-pin" "sixth-content" "sixth-release" 1))
(defconst *fn-so-after-reopen*
  (fn-snrt-run (fn-sn-open-state *fn-so-reopen-present*)
               (append *fn-so-barriers*
                       *fn-so-reserve* (list (list :prepare *fn-so-sixth*))
                       '((:io :record-file :ok) (:crash :old :absent) (:recover))
                       *fn-so-barriers*)))
(assert-event (fn-snt-relation *fn-so-after-reopen*))
(assert-event (fn-sf-record-has-pairp '(2 . 6) (fn-sf-records (fn-sn-files *fn-so-after-reopen*))))
(assert-event (equal (fn-sf-records (fn-sn-files *fn-so-after-reopen*)) *fn-so-image-present*))
(assert-event (equal (fn-sf-frontier (fn-sn-files *fn-so-after-reopen*)) 9))

; -----------------------------------------------------------------------------
; Teeth for fn-sn-acknowledged-record-survives-observed-reopen.

; crash-imagep dropped: an image that rolled back the acknowledged record is
; structurally valid and replayable, so the reopen succeeds, and the pair
; then has no record.  This is exactly the whole-store rollback the adapter
; cannot detect without a freshness anchor.
(defconst *fn-so-reopen-rolled-back*
  (fn-sn-open-observed *fn-so-live-groups* 10 8 (list *fn-so-first* *fn-so-second*)))
(assert-event (fn-sn-open-okp *fn-so-reopen-rolled-back*))
(assert-event (with-guard-checking :none (not (fn-sf-record-has-pairp
                 '(2 . 6)
                 (fn-sf-records (fn-sn-files (fn-sn-open-state *fn-so-reopen-rolled-back*)))))))
; member dropped: a pair that was never acknowledged names no record.
(assert-event (with-guard-checking :none (not (fn-sf-record-has-pairp
                 '(9 . 9)
                 (fn-sf-records (fn-sn-files (fn-sn-open-state *fn-so-reopen-present*)))))))
; relation dropped (weakened to fn-sn-statep): a structurally valid state whose
; history is not replayable carries an acknowledged pair and an admissible
; image, and the reopen refuses it.
(defconst *fn-so-unrelated*
  (fn-sn-make *fn-so-live-groups* 10
              (fn-sf-make :ready 1 nil (list *fn-so-alien*) nil nil '((0 . 0)) 5)
              (fn-node-initial-state *fn-so-live-groups* 10)))
(assert-event (fn-sn-statep *fn-so-unrelated*))
(assert-event (not (fn-snt-relation *fn-so-unrelated*)))
(assert-event (fn-sf-crash-imagep (fn-sn-files *fn-so-unrelated*) 1 (list *fn-so-alien*)))
(assert-event (member-equal '(0 . 0) (fn-sf-successes (fn-sn-files *fn-so-unrelated*))))
(assert-event (with-guard-checking :none (not (fn-sn-open-okp
                 (fn-sn-open-observed *fn-so-live-groups* 10 1 (list *fn-so-alien*))))))

; -----------------------------------------------------------------------------
; D14-b: the recovery freedom, the two gates that bound it, and the
; counterexample that keeps it out of the reliance predicate.
;
; *fn-so-gap-opened* is the witness the freedom exists for: a process that
; opened on a two-record image and has not yet run its five recovery fences.
; It replayed both records from the scan of the VIEW, so the second one's
; directory entry may still be the pending link the dead process left, and a
; crash here drops it.

(assert-event (fn-sf-recovery-visiblep (fn-sn-files *fn-so-gap-opened*)))
(assert-event (equal (fn-sf-successes (fn-sn-files *fn-so-gap-opened*)) nil))
(assert-event (fn-sf-record-rollback-visiblep (fn-sn-files *fn-so-gap-opened*)))
; Non-degenerate: the freedom's image is a two-record list minus its last,
; not an empty list, and it is not the first disjunct restated.
(assert-event (fn-sf-recovery-crash-imagep (fn-sn-files *fn-so-gap-opened*) 4
                                           (list *fn-so-first* *fn-so-second*)))
(assert-event (fn-sf-recovery-crash-imagep (fn-sn-files *fn-so-gap-opened*) 4
                                           (list *fn-so-first*)))
(assert-event (equal (fn-sf-stable-records (fn-sn-files *fn-so-gap-opened*))
                     (list *fn-so-first*)))
; ...and no more: two dropped records, a dropped FIRST record, and a
; rolled-back frontier are all refused.
(assert-event (not (fn-sf-recovery-crash-imagep (fn-sn-files *fn-so-gap-opened*) 4 nil)))
(assert-event (not (fn-sf-recovery-crash-imagep (fn-sn-files *fn-so-gap-opened*) 4
                                                (list *fn-so-second*))))
(assert-event (not (fn-sf-recovery-crash-imagep (fn-sn-files *fn-so-gap-opened*) 3
                                                (list *fn-so-first*))))
; The two predicates are genuinely different here, which is the whole of
; D14-b: the platform may leave the shorter image, and no consumer of this
; state may rely on it.
(assert-event (not (fn-sf-crash-imagep (fn-sn-files *fn-so-gap-opened*) 4
                                       (list *fn-so-first*))))
(assert-event (fn-sf-crash-imagep (fn-sn-files *fn-so-gap-opened*) 4
                                  (list *fn-so-first* *fn-so-second*)))
; The constructor inhabits the new arm, and reproduces exactly that image.
(assert-event (equal (fn-sf-records
                      (fn-sf-crash-rollback (fn-sn-files *fn-so-gap-opened*)))
                     (list *fn-so-first*)))
(assert-event (equal (fn-sf-phase
                      (fn-sf-crash-rollback (fn-sn-files *fn-so-gap-opened*)))
                     :replaying))
(assert-event (equal (fn-sf-records
                      (fn-sf-image-crash (fn-sn-files *fn-so-gap-opened*) 4
                                         (list *fn-so-first*)))
                     (list *fn-so-first*)))
(assert-event (fn-sf-statep
               (fn-sf-crash-rollback (fn-sn-files *fn-so-gap-opened*))))
; The rolled-back image still opens, so the freedom is not an image the host
; would refuse: it is one it cannot tell from the durable one.
(assert-event (fn-sn-open-okp
               (fn-sn-open-observed *fn-so-live-groups* 10 4 (list *fn-so-first*))))

; Tooth for the PHASE conjunct.  The same two records, the same empty success
; history, the same frontier -- but the five recovery fences have run, so the
; un-fenced tail is fenced and the freedom is closed.
(defconst *fn-so-gap-ready* (fn-snrt-run *fn-so-gap-opened* *fn-so-barriers*))
(assert-event (equal (fn-sf-phase (fn-sn-files *fn-so-gap-ready*)) :ready))
(assert-event (equal (fn-sf-records (fn-sn-files *fn-so-gap-ready*))
                     (list *fn-so-first* *fn-so-second*)))
(assert-event (equal (fn-sf-successes (fn-sn-files *fn-so-gap-ready*)) nil))
(assert-event (not (fn-sf-record-rollback-visiblep (fn-sn-files *fn-so-gap-ready*))))
(assert-event (not (fn-sf-recovery-crash-imagep (fn-sn-files *fn-so-gap-ready*) 4
                                                (list *fn-so-first*))))
(assert-event (equal (fn-sf-stable-records (fn-sn-files *fn-so-gap-ready*))
                     (list *fn-so-first* *fn-so-second*)))

; Tooth for the SUCCESS conjunct, and the reason it is not prose.  fn-sf-crash
; carries the ghost history across a crash, so a :replaying state reached that
; way holds the pair it acknowledged; without the conjunct the freedom would
; admit an image that drops that pair's record, which is precisely what
; fn-sf-recovery-admissible-image-facts forbids.
(defconst *fn-so-acked-replaying*
  (fn-sn-files (fn-snt-step *fn-so-acked* '(:crash :old :absent))))
(assert-event (fn-sf-recovery-visiblep *fn-so-acked-replaying*))
(assert-event (equal (fn-sf-successes *fn-so-acked-replaying*) '((2 . 6))))
(assert-event (not (fn-sf-record-rollback-visiblep *fn-so-acked-replaying*)))
(assert-event (equal (fn-sf-records *fn-so-acked-replaying*) *fn-so-image-absent*))
(assert-event (not (fn-sf-recovery-crash-imagep *fn-so-acked-replaying* 7
                                                (list *fn-so-first* *fn-so-second*))))
(assert-event (equal (fn-sf-stable-records *fn-so-acked-replaying*)
                     *fn-so-image-absent*))
; ...and the record the dropped image would have lost is the acknowledged one.
(assert-event (fn-sf-record-has-pairp '(2 . 6) *fn-so-image-absent*))
(assert-event (with-guard-checking :none
               (not (fn-sf-record-has-pairp
                     '(2 . 6) (list *fn-so-first* *fn-so-second*)))))

; The (consp records) conjunct.  On an empty record list the third arm would
; be the first disjunct restated -- (fn-sf-but-last nil) is nil -- so it
; admits no image the predicate did not already admit; the conjunct is what
; makes fn-sf-record-rollback-visiblep mean "a record may be dropped here".
(assert-event (equal (fn-sf-records (fn-sn-files (fn-sn-open-state *fn-so-empty*))) nil))
(assert-event (fn-sf-recovery-visiblep (fn-sn-files (fn-sn-open-state *fn-so-empty*))))
(assert-event (not (fn-sf-record-rollback-visiblep
                    (fn-sn-files (fn-sn-open-state *fn-so-empty*)))))
(assert-event (equal (fn-sf-stable-records
                      (fn-sn-files (fn-sn-open-state *fn-so-empty*))) nil))

; -----------------------------------------------------------------------------
; Why fn-sf-crash-imagep itself was NOT widened: the counterexample, kernel
; half.  *fn-so-gap-opened* is a recovery-window state whose success history
; is empty and whose SECOND record is one an earlier process completed and
; acknowledged -- the kernel cannot tell that record from the un-fenced tail,
; because which records are fenced is a fact about the byte store's pending
; list, not about this state.  A consumer that holds a promise about the
; second record (the owner's ledger, fn-own-ledger-durablep; the receiver's
; history, fn-bprv-extendsp) therefore loses it if the reopen gate admits the
; rolled-back image.  The owner half is in tests/acl2/owner-tests.lisp.
(assert-event (fn-sf-record-has-pairp '(1 . 2)
                                      (list *fn-so-first* *fn-so-second*)))
(assert-event (with-guard-checking :none
               (not (fn-sf-record-has-pairp '(1 . 2) (list *fn-so-first*)))))
(assert-event (fn-sf-recovery-crash-imagep (fn-sn-files *fn-so-gap-opened*) 4
                                           (list *fn-so-first*)))
(assert-event (not (fn-sf-crash-imagep (fn-sn-files *fn-so-gap-opened*) 4
                                       (list *fn-so-first*))))
