; Witnesses and teeth for the fragment journal (C2-04).
;
; The witness is a two-fragment restart trace on the six-byte object of
; tests/acl2/transfer-tests.lisp: reserve, the tail fragment, the head
; fragment, a crash, replay, the exact missing ranges, then the middle
; fragment completes an :unverified candidate.  Every keystone of
; books/transfer-journal-invariants.lisp then gets one concrete case per
; hypothesis in which the conclusion fails without it.

(in-package "ACL2")
(include-book "../../books/transfer-journal-invariants")

(defconst *tj-profile* (fn-transfer-make-profile 12 8 4 3 3 4))
(defconst *tj-label* '(1 2))
(defconst *tj-initial* (fn-transfer-initial-state *tj-profile*))
(defconst *tj-digest*
  '(1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16
    17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32))
(defconst *tj-other-digest*
  '(32 31 30 29 28 27 26 25 24 23 22 21 20 19 18 17
    16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1))

; -----------------------------------------------------------------------------
; Witness: two fragments, restart, resume.

(defconst *tj-inputs*
  (list (list :reserve *tj-label* 6)
        (list :chunk *tj-label* 4 '(5 6))
        (list :chunk *tj-label* 0 '(1 2))))

(defconst *tj-live* (fn-tj-run *tj-initial* *tj-inputs*))
(defconst *tj-journal* (fn-tj-journal *tj-initial* *tj-inputs*))
(assert-event (fn-transfer-statep *tj-live*))
(assert-event
 (equal *tj-journal*
        (list (list :reserve *tj-label* 6 :reserved)
              (list :chunk *tj-label* 4 '(5 6) :stored)
              (list :chunk *tj-label* 0 '(1 2) :stored))))

; The crash: only the journal survives.  Replay reproduces the live state
; exactly, and the kernel reports the same two missing bytes.
(defconst *tj-replayed* (fn-tj-replay-records *tj-initial* *tj-journal* 0))
(assert-event (equal *tj-replayed* (list :ok *tj-live* 3)))
(assert-event
 (equal (fn-transfer-missing-ranges (fn-frame-item 1 *tj-replayed*) *tj-label*)
        '(:ok ((2 1) (3 1)))))
(assert-event (equal (fn-tj-candidate (fn-frame-item 1 *tj-replayed*) *tj-label*)
                     nil))

; Resume after the restart: the middle fragment completes the object, and the
; only thing exported is an unverified candidate.
(defconst *tj-resumed*
  (fn-tj-run (fn-frame-item 1 *tj-replayed*)
             (list (list :chunk *tj-label* 2 '(3 4)))))
(assert-event (equal (fn-tj-candidate *tj-resumed* *tj-label*)
                     '(:unverified (1 2 3 4 5 6))))
(assert-event (equal (fn-transfer-missing-ranges *tj-resumed* *tj-label*)
                     '(:ok nil)))

; The whole journal from a profile record, through fn-tj-replay.
(defconst *tj-full-journal*
  (cons (fn-tj-profile-record *tj-profile*)
        (append *tj-journal* (list (list :chunk *tj-label* 2 '(3 4) :stored)))))
(assert-event (equal (fn-tj-replay *tj-full-journal*)
                     (list :ok *tj-resumed* 5)))
(assert-event (equal (fn-tj-replay *tj-journal*) (list :fault :no-profile nil 0)))

; -----------------------------------------------------------------------------
; Duplicate, byte-identical overlap, differing overlap, reorder, malformed.

; An exact duplicate is journaled as :duplicate and replays to the same state.
(defconst *tj-duplicate-record*
  (fn-tj-write *tj-live* (list :chunk *tj-label* 4 '(5 6))))
(assert-event (equal (fn-tj-outcome *tj-duplicate-record*) :duplicate))
(assert-event (equal (fn-tj-apply *tj-live* *tj-duplicate-record*)
                     (list :ok *tj-live*)))

; A differing overlap is journaled as :overlap-conflict and replays to the
; same state: no byte of the refused arrival is retained.
(defconst *tj-conflict-record*
  (fn-tj-write *tj-live* (list :chunk *tj-label* 1 '(99 98))))
(assert-event (equal (fn-tj-outcome *tj-conflict-record*) :overlap-conflict))
(assert-event (equal (fn-tj-apply *tj-live* *tj-conflict-record*)
                     (list :ok *tj-live*)))

; A byte-identical overlap is accepted: it is :stored, it moves the state, and
; it fills exactly the one new byte it carried.
(defconst *tj-identical-record*
  (fn-tj-write *tj-live* (list :chunk *tj-label* 1 '(2 3))))
(assert-event (equal (fn-tj-outcome *tj-identical-record*) :stored))
(defconst *tj-after-identical*
  (fn-frame-item 1 (fn-tj-apply *tj-live* *tj-identical-record*)))
(assert-event (not (equal *tj-after-identical* *tj-live*)))
(assert-event (equal (fn-transfer-missing-ranges *tj-after-identical* *tj-label*)
                     '(:ok ((3 1)))))

; Reorder: two arrival orders leave different retained fragments and the same
; candidate bytes.
(defconst *tj-forward*
  (fn-tj-run *tj-initial*
             (list (list :reserve *tj-label* 6)
                   (list :chunk *tj-label* 0 '(1 2))
                   (list :chunk *tj-label* 2 '(3 4))
                   (list :chunk *tj-label* 4 '(5 6)))))
(defconst *tj-backward*
  (fn-tj-run *tj-initial*
             (list (list :reserve *tj-label* 6)
                   (list :chunk *tj-label* 4 '(5 6))
                   (list :chunk *tj-label* 2 '(3 4))
                   (list :chunk *tj-label* 0 '(1 2)))))
(assert-event (not (equal *tj-forward* *tj-backward*)))
(assert-event (equal (fn-tj-candidate *tj-forward* *tj-label*)
                     (fn-tj-candidate *tj-backward* *tj-label*)))
(assert-event (equal (fn-tj-candidate *tj-forward* *tj-label*)
                     '(:unverified (1 2 3 4 5 6))))

; A malformed input (no offset, no octets) is journaled with the refusal the
; kernel gave it and replays to the same refusal; the keystone needs no
; well-formedness hypothesis on inputs.
(defconst *tj-malformed-record* (fn-tj-write *tj-live* '(:chunk (1 2))))
(assert-event (equal *tj-malformed-record* '(:chunk (1 2) nil nil :invalid-offset)))
(assert-event (equal (fn-tj-replay-records *tj-live* (list *tj-malformed-record*) 0)
                     (list :ok *tj-live* 1)))

; -----------------------------------------------------------------------------
; Frames: the host path with its digests.

(assert-event (fn-tj-records-okp *tj-journal*))
(defconst *tj-frames*
  (list (fn-tj-encode (nth 0 *tj-journal*) *tj-digest*)
        (fn-tj-encode (nth 1 *tj-journal*) *tj-digest*)
        (fn-tj-encode (nth 2 *tj-journal*) *tj-digest*)))
(defconst *tj-digests* (list *tj-digest* *tj-digest* *tj-digest*))
(assert-event (fn-cbor-octet-listp (nth 0 *tj-frames*)))
(assert-event (equal (fn-tj-decode (nth 1 *tj-frames*) *tj-digest*)
                     (fn-frame-ok *fn-tj-magic* *fn-tj-version* :chunk
                                  (list *tj-label* 4 '(5 6) :stored))))
(assert-event
 (equal (fn-tj-replay-frames-with *tj-initial* *tj-frames* *tj-digests* 0)
        (list :ok *tj-live* 3)))

; Corruption 1: a truncated frame.  Replay ends at a typed :corrupt fault
; with the state of the two good records; the truncated chunk is nowhere.
(defconst *tj-truncated* (take 20 (nth 2 *tj-frames*)))
(defconst *tj-truncated-replay*
  (fn-tj-replay-frames-with
   *tj-initial* (list (nth 0 *tj-frames*) (nth 1 *tj-frames*) *tj-truncated*)
   *tj-digests* 0))
(assert-event (equal (fn-frame-item 0 *tj-truncated-replay*) :fault))
(assert-event (equal (car (fn-frame-item 1 *tj-truncated-replay*)) :corrupt))
(assert-event (equal (fn-frame-item 2 *tj-truncated-replay*)
                     (fn-tj-run *tj-initial* (take 2 *tj-inputs*))))
(assert-event (equal (fn-frame-item 3 *tj-truncated-replay*) 2))

; Corruption 2: the trailer does not match the digest the host computed over
; the prefix (the third frame's payload was altered on disk).
(defconst *tj-trailer-replay*
  (fn-tj-replay-frames-with
   *tj-initial* *tj-frames*
   (list *tj-digest* *tj-digest* *tj-other-digest*) 0))
(assert-event (equal (fn-frame-item 0 *tj-trailer-replay*) :fault))
(assert-event (equal (car (fn-frame-item 1 *tj-trailer-replay*)) :corrupt))
(assert-event (equal (fn-frame-item 2 *tj-trailer-replay*)
                     (fn-tj-run *tj-initial* (take 2 *tj-inputs*))))

; Corruption 3: a well-formed frame whose recorded outcome the kernel
; contradicts (a duplicate claimed as :stored).
(defconst *tj-lying-record* (list :chunk *tj-label* 4 '(5 6) :stored))
(assert-event (equal (fn-tj-apply *tj-live* *tj-lying-record*)
                     (list :fault :outcome-mismatch *tj-live*)))
(assert-event
 (equal (fn-tj-replay-frames-with
         *tj-initial*
         (append *tj-frames* (list (fn-tj-encode *tj-lying-record* *tj-digest*)))
         (append *tj-digests* (list *tj-digest*)) 0)
        (list :fault :outcome-mismatch *tj-live* 3)))

; -----------------------------------------------------------------------------
; Teeth for fn-tj-replay-of-journal-is-run
;   (implies (natp index)
;            (equal (fn-tj-replay-records st (fn-tj-journal st inputs) index)
;                   (list :ok (fn-tj-run st inputs) (+ (len inputs) index))))
; The one hypothesis dropped: a non-numeric index is returned as given by an
; empty replay, while the conclusion's sum is a number.
(assert-event
 (not (equal (fn-tj-replay-records *tj-live* (fn-tj-journal *tj-live* nil) :x)
             (list :ok (fn-tj-run *tj-live* nil) 0))))

; -----------------------------------------------------------------------------
; A-CRYPTO and the teeth.  `fn-tj-seal` and `fn-tj-open` are stated against
; the constrained `fn-frame-digest`, so no ground term evaluates them and no
; `assert-event` can exhibit a violating value for a hypothesis of
; `fn-tj-open-of-seal`, or for the sealed-frame statements of
; `fn-tj-replay-sealed-journal-is-run` and
; `fn-tj-corrupt-frame-ends-replay-at-typed-fault`.  The witnesses below are
; on the executable host twin, `fn-tj-encode`/`fn-tj-decode` and
; `fn-tj-replay-frames-with` with the host digest supplied; they are the same
; frames and the same replay, which is what
; `fn-tj-replay-frames-with-is-replay-frames` says.  A hypothesis whose only
; violating value would need an evaluated `fn-frame-digest` is recorded open
; in specs/transfer-journal.md rather than asserted.
;
; Teeth for fn-tj-replay-sealed-journal-is-run: natp index (above) and
;   (fn-tj-records-okp (fn-tj-journal st inputs)).
; Hypothesis 2 dropped: an empty label is a kernel-valid input the frame
; grammar cannot carry (a blob is nonempty).  The kernel reserves it, the
; record is not encodable, the frame is :bad, and replay faults.
; Hypothesis 1 dropped, on the empty journal: an empty replay returns the
; index it was given, and `:x` is not the number the conclusion computes.
(assert-event
 (equal (fn-tj-replay-frames *tj-initial* (fn-tj-seal-journal nil) :x)
        (list :ok *tj-initial* :x)))
(assert-event
 (not (equal (fn-tj-replay-frames *tj-initial* (fn-tj-seal-journal nil) :x)
             (list :ok (fn-tj-run *tj-initial* nil) 0))))

(defconst *tj-empty-label-inputs* (list (list :reserve nil 6)))
(defconst *tj-empty-label-record* (fn-tj-write *tj-initial* (list :reserve nil 6)))
(assert-event (equal (fn-tj-outcome *tj-empty-label-record*) :reserved))
(assert-event
 (not (fn-tj-records-okp (fn-tj-journal *tj-initial* *tj-empty-label-inputs*))))
(assert-event (equal (fn-tj-encode *tj-empty-label-record* *tj-digest*) :bad))
(assert-event
 (equal (fn-frame-item 0
         (fn-tj-replay-frames-with
          *tj-initial* (list (fn-tj-encode *tj-empty-label-record* *tj-digest*))
          (list *tj-digest*) 0))
        :fault))

; -----------------------------------------------------------------------------
; Teeth for fn-tj-corrupt-frame-ends-replay-at-typed-fault: the two
; hypotheses above and (not (fn-frame-result-okp (fn-tj-open bad))).
; Hypothesis 1 dropped (index :x, no good records): the fault carries :x
; where the conclusion has the number 0.
; Hypothesis 2 dropped: the unencodable empty-label record faults first, so
; the fault state is the initial state, not the run.
; Hypothesis 1 dropped, on the host twin: with a non-natural index the fault
; carries `:x` itself, not the number the conclusion computes.
(assert-event
 (equal (fn-tj-replay-frames-with *tj-initial* (list *tj-truncated*)
                                  (list *tj-digest*) :x)
        (list :fault
              (list :corrupt (fn-frame-item 1 (fn-tj-decode *tj-truncated*
                                                            *tj-digest*)))
              *tj-initial* :x)))
(assert-event
 (not (equal (fn-frame-item 3 (fn-tj-replay-frames-with
                               *tj-initial* (list *tj-truncated*)
                               (list *tj-digest*) :x))
             0)))
; Hypothesis 2 dropped, on the host twin: the unencodable empty-label record
; faults first, so the fault state is the initial state at index 0, not the
; run at index 1.
(assert-event
 (equal (fn-tj-replay-frames-with
         *tj-initial*
         (list (fn-tj-encode *tj-empty-label-record* *tj-digest*)
               *tj-truncated*)
         (list *tj-digest* *tj-digest*) 0)
        (list :fault
              (list :corrupt (fn-frame-item 1 (fn-tj-decode :bad *tj-digest*)))
              *tj-initial* 0)))
(assert-event
 (not (equal (fn-frame-item 2 (fn-tj-replay-frames-with
                               *tj-initial*
                               (list (fn-tj-encode *tj-empty-label-record*
                                                   *tj-digest*)
                                     *tj-truncated*)
                               (list *tj-digest* *tj-digest*) 0))
             (fn-tj-run *tj-initial* *tj-empty-label-inputs*))))
; Hypothesis 3 dropped: a frame that opens is not corrupt; replay continues
; through it to :ok, and no :corrupt fault appears.
(defconst *tj-fourth-frame*
  (fn-tj-encode (list :chunk *tj-label* 2 '(3 4) :stored) *tj-digest*))
(assert-event
 (equal (fn-tj-replay-frames-with
         *tj-initial* (append *tj-frames* (list *tj-fourth-frame*))
         (append *tj-digests* (list *tj-digest*)) 0)
        (list :ok *tj-resumed* 4)))

; -----------------------------------------------------------------------------
; Teeth for fn-tj-refused-record-replays-to-same-state
;   (implies (and (not (equal (fn-tj-outcome r) :reserved))
;                 (not (equal (fn-tj-outcome r) :stored)))
;            (equal (fn-frame-item 1 (fn-tj-apply st r)) st))

; Hypothesis 1 dropped: a confirmed :reserved record moves the state.
(defconst *tj-reserved-record* (list :reserve *tj-label* 6 :reserved))
(assert-event
 (not (equal (fn-frame-item 1 (fn-tj-apply *tj-initial* *tj-reserved-record*))
             *tj-initial*)))

; Hypothesis 2 dropped: a confirmed :stored record moves the state.
(assert-event
 (not (equal (fn-frame-item 1 (fn-tj-apply *tj-live* *tj-identical-record*))
             *tj-live*)))

; -----------------------------------------------------------------------------
; Teeth for fn-tj-run-preserves-statep: (fn-transfer-statep st) dropped.
; Every transition returns a non-state unchanged, so the fold of any inputs
; over :junk is :junk, which is not a state.
(assert-event (equal (fn-tj-run :junk *tj-inputs*) :junk))
(assert-event (not (fn-transfer-statep (fn-tj-run :junk *tj-inputs*))))

; -----------------------------------------------------------------------------
; Teeth for fn-tj-replay-frames-with-is-replay-frames: the digests must be
; the host's digests of the prefixes.  With another digest list the host
; entry point faults where the specification replay succeeds.
(assert-event
 (equal (fn-frame-item 0
         (fn-tj-replay-frames-with
          *tj-initial* *tj-frames*
          (list *tj-other-digest* *tj-digest* *tj-digest*) 0))
        :fault))

; -----------------------------------------------------------------------------
; Teeth for fn-tj-decode-of-encode
;   (implies (and (fn-tj-record-okp r) (fn-frame-digestp digest)) ...)
; and fn-tj-open-of-seal (fn-tj-record-okp r).
; Hypothesis 1 dropped: a record outside the grammar encodes to :bad, which
; decodes to a frame error, not to the record.
(defconst *tj-bad-record* (list :reserve nil 6 :reserved))
(assert-event (not (fn-tj-record-okp *tj-bad-record*)))
(assert-event (equal (fn-tj-encode *tj-bad-record* *tj-digest*) :bad))
(assert-event (not (fn-frame-result-okp (fn-tj-decode :bad *tj-digest*))))
; Hypothesis 2 dropped: a digest of the wrong length encodes to :bad.
(assert-event (equal (fn-tj-encode (nth 0 *tj-journal*) '(1 2 3)) :bad))

; A record kind outside the table is refused by the grammar, so no record
; can carry an acceptance: the table is exactly :profile, :reserve, :chunk.
(assert-event (equal *fn-tj-kinds* '(:profile :reserve :chunk)))
(assert-event (not (fn-tj-record-okp (list :accepted *tj-label* 6 :reserved))))
(assert-event (equal (fn-tj-apply *tj-live* (list :accepted *tj-label* 6 :reserved))
                     (list :fault :not-a-transition *tj-live*)))
