; fn: the operator's waiver of a BP carry obligation, its keystones (lane
; carry-abandon, PRF-950; `fn operator CONFIG carry JOURNAL drop WORK
; --abandon REASON...', PKT-869).
;
; The waiver's definitions live in books/bp-carry-control.lisp (the image's
; book): the record (:waive "abandon" WORK REASON PRINCIPAL) of the carry
; journal, its append decision fn-bpcc-waiver-refusal (the pin must stand),
; its replay admissibility fn-bpcc-refusal, and the Store retention event it
; authors, fn-bpcc-waiver-release-event, which is the receipt's own event
; shape.  Host callers: host/workflow-host.lisp fn-workflow-carry-record
; (the decision), host/bp-release-owner-host.lisp fn-owner-workflow-store-waive
; (the event, published by host/native/bp-obligation.lisp through
; host/native/owner.lisp fnn-owner-retention-commit, whose Store step is
; books/retention.lisp fn-retain-release with kind :forward:
; books/store-node-retention.lisp fn-snrt-retention-of-apply-retention-event).
;
; KEYSTONE fn-bpcw-waiver-releases-exactly-once: the waiver's Store event,
; applied by retention, removes exactly the obligation's pin; afterwards the
; waiver authors no second event, the work is no longer pinned, and no
; receipt's release decision is admissible for it.
; fn-bpcw-only-a-waiver-waives: no carry record but a waiver of W (a drop
; without --abandon among them) makes W waived, so nothing but a waiver
; authors this event (the receipt's is fn-bprl-release-decision's).
; fn-bpcw-admitted-waiver-authors-its-release: a waiver the decision admits
; authors the event with the pin's own id, subject and evidence.
; fn-bpcw-waiver-of-an-unheld-obligation-is-refused: refused by name.
; fn-bpcw-refusal-ignores-the-pin: the replay admissibility does not read the
; retention, so the waiver replays after its own release.
(in-package "ACL2")
(include-book "bp-carry-control")
(include-book "bp-release-invariants")

; The workflow image once the Store's retention step for EVENT (the :release
; arm, kind :forward) has run and the owner re-read the Store node
; (host/bp-release-owner-host.lisp fn-owner-workflow-sync-store-node).
(defun fn-bpcw-after-release (bp event)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bprl-with-node
   bp
   (fn-bprl-node-with-retention
    (fn-bp-state-node bp)
    (fn-retain-release (fn-node-retention (fn-bp-state-node bp))
                       (fn-bp-nth 1 event) (fn-bp-nth 2 event) :forward
                       (fn-bp-nth 3 event)))))

(local (in-theory (disable fn-retain-release fn-retain-find-id fn-retain-remove-id
                           fn-retain-matching-releasep fn-retain-statep
                           fn-bprl-with-node fn-bprl-node-with-retention)))

(local
 (defthm fn-bpcw-nth-of-event
   (and (equal (fn-bp-nth 1 (list :release a b e 0)) a)
        (equal (fn-bp-nth 2 (list :release a b e 0)) b)
        (equal (fn-bp-nth 3 (list :release a b e 0)) e))
   :hints (("Goal" :in-theory (enable fn-bp-nth)))))

(defthm fn-bpcw-waiver-release-event-formula
  (equal (fn-bpcc-waiver-release-event bp c w)
         (let ((work (fn-bp-find-work w (fn-bp-state-works bp))))
           (if (and (consp (fn-bpcc-waiver-entry c w))
                    (consp work)
                    (fn-bprl-work-pinnedp bp work))
               (list :release (fn-bp-work-obligation-id work) (fn-bp-work-subject work)
                     (fn-bprl-required-evidence (fn-bp-state-config bp) work) 0)
             nil)))
  :hints (("Goal" :in-theory (enable fn-bpcc-waiver-release-event))))

(local (in-theory (disable fn-bpcc-waiver-release-event fn-bprl-work-pinnedp)))

(local
 (defthm fn-bpcw-pinned-find-id
   (implies (fn-bprl-work-pinnedp bp work)
            (fn-retain-matching-releasep
             (fn-retain-find-id (fn-bp-work-obligation-id work) (fn-bprl-pins bp))
             (fn-bp-work-obligation-id work) (fn-bp-work-subject work) :forward
             (fn-bprl-required-evidence (fn-bp-state-config bp) work)))
   :hints (("Goal" :in-theory (enable fn-bprl-work-pinnedp fn-bprl-work-pin)))))

(local
 (defthm fn-bpcw-matching-is-consp
   (implies (fn-retain-matching-releasep pin id subject kind evidence)
            (consp pin))
   :hints (("Goal" :in-theory (enable fn-retain-matching-releasep)))
   :rule-classes :forward-chaining))

;; Proof vocabulary: the work's pin fields stay opaque from here.
(local (in-theory (disable fn-bprl-required-evidence fn-bp-work-obligation-id
                           fn-bp-work-subject fn-bp-find-work fn-bprl-pins
                           fn-bprl-release-okp)))

; The Store's retention step removes exactly the obligation's pin.
(local
 (defthm fn-bpcw-pins-after-release
   (implies (and (fn-retain-statep (fn-node-retention (fn-bp-state-node bp)))
                 (fn-bprl-work-pinnedp bp work))
            (equal (fn-bprl-pins
                    (fn-bpcw-after-release
                     bp (list :release (fn-bp-work-obligation-id work)
                              (fn-bp-work-subject work)
                              (fn-bprl-required-evidence (fn-bp-state-config bp) work)
                              0)))
                   (fn-retain-remove-id (fn-bp-work-obligation-id work)
                                        (fn-bprl-pins bp))))
   :hints (("Goal" :in-theory (e/d (fn-bprl-pins fn-bpcw-after-release)
                                   (fn-bprl-release-pins fn-bpcw-pinned-find-id))
            :use ((:instance fn-bprl-release-pins
                             (s (fn-node-retention (fn-bp-state-node bp)))
                             (id (fn-bp-work-obligation-id work))
                             (subject (fn-bp-work-subject work))
                             (kind :forward)
                             (evidence (fn-bprl-required-evidence
                                        (fn-bp-state-config bp) work)))
                  (:instance fn-bpcw-pinned-find-id))))))

(local
 (defthm fn-bpcw-not-pinned-without-pin
   (implies (not (fn-retain-find-id (fn-bp-work-obligation-id work) (fn-bprl-pins bp)))
            (not (fn-bprl-work-pinnedp bp work)))
   :hints (("Goal" :in-theory (enable fn-bprl-work-pinnedp fn-bprl-work-pin
                                      fn-retain-matching-releasep)))))

(local
 (defthm fn-bpcw-after-release-keeps-works-and-config
   (and (equal (fn-bp-state-works (fn-bpcw-after-release bp event))
               (fn-bp-state-works bp))
        (equal (fn-bp-state-config (fn-bpcw-after-release bp event))
               (fn-bp-state-config bp)))
   :hints (("Goal" :in-theory (enable fn-bpcw-after-release)))))

(local
 (defthm fn-bpcw-no-duplicate-pins
   (implies (fn-retain-statep (fn-node-retention (fn-bp-state-node bp)))
            (fn-retain-no-duplicatesp (fn-retain-obligation-ids (fn-bprl-pins bp))))
   :hints (("Goal" :in-theory (enable fn-bprl-pins)))))

; The release, for any pinned work: its pin goes, and nothing pins it after.
(local
 (defthm fn-bpcw-release-of-a-pinned-work
   (let ((next (fn-bpcw-after-release
                bp (list :release (fn-bp-work-obligation-id work)
                         (fn-bp-work-subject work)
                         (fn-bprl-required-evidence (fn-bp-state-config bp) work)
                         0))))
     (implies (and (fn-retain-statep (fn-node-retention (fn-bp-state-node bp)))
                   (fn-bprl-work-pinnedp bp work))
              (not (fn-bprl-work-pinnedp next work))))
   :hints (("Goal" :in-theory (disable fn-bpcw-after-release fn-bpcw-not-pinned-without-pin
                                       fn-bprl-find-id-of-remove-self)
            :use ((:instance fn-bprl-find-id-of-remove-self
                             (id (fn-bp-work-obligation-id work))
                             (pins (fn-bprl-pins bp)))
                  (:instance fn-bpcw-not-pinned-without-pin
                             (bp (fn-bpcw-after-release
                                  bp (list :release (fn-bp-work-obligation-id work)
                                           (fn-bp-work-subject work)
                                           (fn-bprl-required-evidence
                                            (fn-bp-state-config bp) work)
                                           0)))))))))

(local
 (defthm fn-bpcw-release-okp-needs-the-pin
   (implies (not (fn-bprl-work-pinnedp s work))
            (not (fn-bprl-release-okp s receipt work)))
   :hints (("Goal" :in-theory (enable fn-bprl-release-okp)))))

; KEYSTONE.
(defthm fn-bpcw-waiver-releases-exactly-once
  (let* ((event (fn-bpcc-waiver-release-event bp c w))
         (work (fn-bp-find-work w (fn-bp-state-works bp)))
         (next (fn-bpcw-after-release bp event)))
    (implies (and (fn-retain-statep (fn-node-retention (fn-bp-state-node bp)))
                  event)
             (and (consp (fn-bpcc-waiver-entry c w))
                  (equal (fn-bprl-pins next)
                         (fn-retain-remove-id (fn-bp-work-obligation-id work)
                                              (fn-bprl-pins bp)))
                  (not (fn-bprl-work-pinnedp next work))
                  (null (fn-bpcc-waiver-release-event next c w))
                  (not (fn-bprl-release-okp next receipt work)))))
  :hints (("Goal" :in-theory (disable fn-bpcw-after-release fn-bpcc-waiver-entry
                                      fn-retain-statep))))

; Nothing but a waiver of W makes W waived: a drop without --abandon, a
; pause, a resume or a waiver of another work leave W's waiver as it was.
(local
 (defthm fn-bpcw-waived-of-apply
   (equal (fn-bpcc-waived (fn-bpcc-apply c record))
          (let ((waived (if (alistp (fn-bpcc-waived c)) (fn-bpcc-waived c) nil)))
            (if (fn-bpcc-waiver-recordp record)
                (cons (cons (fn-bpcc-record-work record)
                            (cons (fn-bpcc-waiver-principal record)
                                  (fn-bpcc-record-reason record)))
                      waived)
              waived)))
   :hints (("Goal" :in-theory (e/d (fn-bpcc-apply fn-bpcc-waived)
                                   (fn-bpcc-waiver-recordp fn-bpcc-record-work
                                    fn-bpcc-record-reason fn-bpcc-waiver-principal
                                    fn-bpcc-verb fn-bpcc-remove fn-bpcc-dropped
                                    fn-bpcc-paused fn-bpcc-all))))))

(defthm fn-bpcw-only-a-waiver-waives
  (implies (and (not (consp (fn-bpcc-waiver-entry c w)))
                (not (and (fn-bpcc-waiver-recordp record)
                          (equal (fn-bpcc-record-work record) w))))
           (not (consp (fn-bpcc-waiver-entry (fn-bpcc-apply c record) w))))
  :hints (("Goal" :in-theory (e/d (fn-bpcc-waiver-entry)
                                  (fn-bpcc-apply fn-bpcc-waived fn-bpcc-waiver-recordp
                                   fn-bpcc-record-work fn-bpcc-record-reason
                                   fn-bpcc-waiver-principal)))))

(defthm fn-bpcw-only-a-waiver-authors-a-waiver-release
  (implies (and (not (consp (fn-bpcc-waiver-entry c w)))
                (not (and (fn-bpcc-waiver-recordp record)
                          (equal (fn-bpcc-record-work record) w))))
           (null (fn-bpcc-waiver-release-event bp (fn-bpcc-apply c record) w)))
  :hints (("Goal" :in-theory (disable fn-bpcc-apply fn-bpcc-waiver-entry
                                      fn-bpcc-waiver-recordp fn-bpcc-record-work
                                      fn-bprl-work-pinnedp)
           :use fn-bpcw-only-a-waiver-waives)))

(defthm fn-bpcw-admitted-waiver-authors-its-release
  (let ((work (fn-bp-find-work (fn-bpcc-record-work record) (fn-bp-state-works bp))))
    (implies (and (fn-bpcc-waiver-recordp record)
                  (null (fn-bpcc-waiver-refusal bp c record)))
             (equal (fn-bpcc-waiver-release-event bp (fn-bpcc-apply c record)
                                                  (fn-bpcc-record-work record))
                    (list :release (fn-bp-work-obligation-id work)
                          (fn-bp-work-subject work)
                          (fn-bprl-required-evidence (fn-bp-state-config bp) work)
                          0))))
  :hints (("Goal" :in-theory (enable fn-bpcc-heldp))))

(defthm fn-bpcw-waiver-of-an-unheld-obligation-is-refused
  (implies (and (fn-bpcc-waiver-recordp record)
                (not (fn-bpcc-heldp bp (fn-bpcc-record-work record))))
           (member-equal (fn-bpcc-waiver-refusal bp c record)
                         '(:unknown-work :already-waived :not-held))))

(defthm fn-bpcw-refusal-ignores-the-pin
  (equal (fn-bpcc-refusal (fn-bpcw-after-release bp event) c record)
         (fn-bpcc-refusal bp c record))
  :hints (("Goal" :in-theory (disable fn-bpcw-after-release))))
