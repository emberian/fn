; Teeth for the file-kernel publication and crash-fidelity keystones.
;
; The 2026-09-18 review §5: "Acknowledgement cannot be forged ... The
; five-barrier gate is structural through `fn-sf-phase-shapep'."  The
; file-kernel half of that is `fn-sf-success-requires-matching-completion'
; and `fn-sf-completing-admits-only-matching-completion': a success record
; appears only for the exact completion the core produced, in the one phase
; that admits it.  D4 of the review ("every process-death cut is a model
; crash point") is `fn-sf-crash-realizes-every-admissible-image' together
; with the crash-point fidelity theorems around it.
;
; The kernel this book tests is the one after the crash-fidelity rewrite:
; `fn-sf-core-completion' takes (s sequence txid) and there are no
; :fenced-core, :fenced-reservation or :fenced-before-record phases.  The
; teeth that used to target those phases are replaced here by the cases for
; the crash choices that took their place: in the two data-durable phases a
; crash may yield either whole value, and a completed directory barrier
; removes the choice it settled.

(in-package "ACL2")
(include-book "../../books/store-files-invariants")
(include-book "std/testing/must-fail" :dir :system)

; -----------------------------------------------------------------------------
; A reachable, non-degenerate witness: the whole publication sequence, driven
; by the production transitions, named at every phase a crash choice can be
; live in.  Non-degenerate because it passes through every barrier, carries a
; real record, and reaches :completed rather than being written down.

(defconst *sft-groups* '("fn.letters" "fn.test"))
(defconst *sft-record*
  (fn-record-make 0 0 0 "<zero@example.invalid>" '(90)
                  '("fn.letters" "fn.test")
                  "archive-zero" "content-zero" "release-zero" 2))

(defconst *sft-frontier-staged* (fn-sf-start-frontier (fn-sf-initial-state)))
(defconst *sft-frontier-durable*
  (fn-sf-frontier-file-result *sft-frontier-staged* :ok))
(defconst *sft-frontier-attempted*
  (fn-sf-frontier-replace-result *sft-frontier-durable* :ok))
(defconst *sft-reserved* (fn-sf-frontier-dir-result *sft-frontier-attempted* :ok))
(defconst *sft-staged*
  (fn-sf-prepare-record *sft-reserved* *sft-record* *sft-groups* 10))
(defconst *sft-record-durable* (fn-sf-record-file-result *sft-staged* :ok))
(defconst *sft-record-attempted*
  (fn-sf-record-link-result *sft-record-durable* :ok))
(defconst *sft-published* (fn-sf-record-dir-result *sft-record-attempted* :ok))
(defconst *sft-completed* (fn-sf-core-completion *sft-published* 0 0))
(defconst *sft-acknowledged* (fn-sf-emit-success *sft-completed* 0 0))

(assert-event (fn-sf-statep *sft-frontier-staged*))
(assert-event (fn-sf-statep *sft-frontier-durable*))
(assert-event (fn-sf-statep *sft-reserved*))
(assert-event (fn-sf-statep *sft-record-durable*))
(assert-event (fn-sf-statep *sft-published*))
(assert-event (fn-sf-statep *sft-acknowledged*))

(assert-event (equal (fn-sf-phase *sft-frontier-staged*) :frontier-staged))
(assert-event (equal (fn-sf-phase *sft-frontier-durable*) :frontier-data-durable))
(assert-event (equal (fn-sf-phase *sft-frontier-attempted*) :frontier-attempted))
(assert-event (equal (fn-sf-phase *sft-reserved*) :reserved))
(assert-event (equal (fn-sf-phase *sft-staged*) :record-staged))
(assert-event (equal (fn-sf-phase *sft-record-durable*) :record-data-durable))
(assert-event (equal (fn-sf-phase *sft-record-attempted*) :record-attempted))
(assert-event (equal (fn-sf-phase *sft-published*) :completing))
(assert-event (equal (fn-sf-phase *sft-completed*) :completed))
(assert-event (equal (fn-sf-phase *sft-acknowledged*) :ready))

(assert-event (equal (fn-sf-frontier *sft-frontier-durable*) 0))
(assert-event (equal (fn-sf-frontier-candidate *sft-frontier-durable*) 1))
(assert-event (equal (fn-sf-frontier *sft-reserved*) 1))
(assert-event (equal (fn-sf-record-candidate *sft-record-durable*) *sft-record*))
(assert-event (null (fn-sf-records *sft-record-durable*)))
(assert-event (equal (fn-sf-records *sft-completed*) (list *sft-record*)))
(assert-event (null (fn-sf-successes *sft-completed*)))
(assert-event (equal (fn-sf-successes *sft-acknowledged*) '((0 . 0))))

; The ordered publication history is over the tagged store-event grammar, not
; only legacy article records.  Exercise the candidate append lemma with a
; retention event and separate both of its premises with concrete values.
(defconst *sft-retention-candidate*
  (fn-store-retention-event-make
   :undertake 0 0 0 "obligation-zero" "subject-zero" "evidence-zero" 1))
(assert-event (fn-store-event-p *sft-retention-candidate*))
(assert-event (fn-sf-candidatep *sft-retention-candidate* nil 1))
(assert-event
 (fn-sf-record-listp (list *sft-retention-candidate*) 0 0 1))

; Without candidatep, an otherwise valid empty history does not admit an event
; with the wrong carried sequence.
(defconst *sft-wrong-sequence-event*
  (fn-store-retention-event-make
   :undertake 1 0 0 "obligation-one" "subject-one" "evidence-one" 1))
(assert-event (fn-sf-record-listp nil 0 0 1))
(assert-event (not (fn-sf-candidatep *sft-wrong-sequence-event* nil 1)))
(assert-event
 (not (fn-sf-record-listp (list *sft-wrong-sequence-event*) 0 0 1)))

; Without the ordered-history premise, candidatep alone cannot repair a bad
; prefix.  The total next-lower fold sees the bad prefix as one carried slot,
; while record-listp rejects it as a store event.
(defconst *sft-after-bad-prefix*
  (fn-store-retention-event-make
   :undertake 1 1 1 "obligation-two" "subject-two" "evidence-two" 1))
(assert-event (fn-sf-candidatep *sft-after-bad-prefix* '(bad-prefix) 2))
(assert-event (not (fn-sf-record-listp '(bad-prefix) 0 0 2)))
(assert-event
 (not (fn-sf-record-listp '(bad-prefix
                            (:retention :undertake 1 1 1
                             "obligation-two" "subject-two" "evidence-two" 1))
                          0 0 2)))

; Each premise is proof-relevant: ACL2 must reject the universal theorem when
; either the ordered-history premise or the candidate premise is omitted.
(local
 (must-fail
  (defthm sft-candidate-append-without-ordered-history
    (implies (fn-sf-candidatep record records frontier)
             (fn-sf-record-listp (append records (list record))
                                 0 0 frontier)))))
(local
 (must-fail
  (defthm sft-candidate-append-without-candidate
    (implies (fn-sf-record-listp records 0 0 frontier)
             (fn-sf-record-listp (append records (list record))
                                 0 0 frontier)))))

; Emission is reachable exactly at :completed, and it is the only thing that
; grows the success list.  Not before the phase, and not for another identity.
(assert-event (equal (fn-sf-emit-success *sft-published* 0 0) *sft-published*))
(assert-event (equal (fn-sf-emit-success *sft-completed* 0 1) *sft-completed*))
(assert-event (equal (fn-sf-emit-success *sft-completed* 1 0) *sft-completed*))
(assert-event (equal (fn-sf-core-completion *sft-published* 0 1) *sft-published*))

; -----------------------------------------------------------------------------
; Teeth for `fn-sf-success-requires-matching-completion'
;   (implies (not (and (equal (fn-sf-phase s) :completed)
;                      (equal (cons sequence txid) (fn-sf-completion s))))
;            (equal (fn-sf-emit-success s sequence txid) s))

; The sole hypothesis dropped: the one state and identity pair that satisfies
; the conjunction is exactly where emission is not a no-op.
(assert-event (equal (fn-sf-phase *sft-completed*) :completed))
(assert-event (equal (cons 0 0) (fn-sf-completion *sft-completed*)))

(assert-event (with-guard-checking :none (not (equal (fn-sf-emit-success *sft-completed* 0 0) *sft-completed*))))

; -----------------------------------------------------------------------------
; Teeth for `fn-sf-completing-admits-only-matching-completion'
;   (implies (and (fn-sf-statep s) (equal (fn-sf-phase s) :completing))
;            (and (equal (fn-sf-start-frontier s) s)
;                 (equal (fn-sf-prepare-record s record groups capacity) s)
;                 (equal (fn-sf-emit-success s sequence txid) s)
;                 (implies (not (equal (cons sequence txid) (fn-sf-completion s)))
;                          (equal (fn-sf-core-completion s sequence txid) s))))

; The phase hypothesis dropped.  In :reserved the staging transition is live,
; so the second conjunct is false there: it is the :completing phase, not the
; shape of the call, that closes the mutation gate.
(assert-event (with-guard-checking :none (not (equal (fn-sf-prepare-record *sft-reserved* *sft-record* *sft-groups* 10)
           *sft-reserved*))))

; The inner mismatch hypothesis of the last conjunct dropped.  For the pair
; the core actually produced, `fn-sf-core-completion' is exactly the step out
; of :completing, so it is not a no-op.
(assert-event (with-guard-checking :none (not (equal (fn-sf-core-completion *sft-published* 0 0) *sft-published*))))

; -----------------------------------------------------------------------------
; Teeth for `fn-sf-stable-records-prefix-of-crash'
;   (implies (and (fn-sf-statep s)                                     ; H1
;                 (fn-sf-crash-choicep frontier-choice record-choice))  ; H2
;            (fn-sf-prefixp (fn-sf-records s)
;                           (fn-sf-records (fn-sf-crash s frontier-choice record-choice))))

; H1 dropped.  `fn-sf-crash' refuses a non-state, so the crash image is the
; forged state itself -- and `fn-sf-prefixp' is reflexive only on true lists
; (books/store-files-invariants.lisp:21-24).  A forged state whose record list
; has an improper tail is not a prefix of itself.
(defconst *sft-forged*
  (fn-sf-make :ready 1 nil (cons *sft-record* :improper-tail) nil nil nil 5))
(assert-event (not (fn-sf-statep *sft-forged*)))
(assert-event (fn-sf-crash-choicep :old :absent))
(assert-event (equal (fn-sf-crash *sft-forged* :old :absent) *sft-forged*))
(assert-event
 (not (fn-sf-prefixp (fn-sf-records *sft-forged*) (fn-sf-records *sft-forged*))))

(assert-event (with-guard-checking :none (not (fn-sf-prefixp (fn-sf-records *sft-forged*)
                   (fn-sf-records (fn-sf-crash *sft-forged* :old :absent))))))

; H2 has no teeth, and none is forged.  `fn-sf-crash' returns its argument
; unchanged for a choice outside `fn-sf-crash-choicep', and under H1 the record
; list of a state is a true list, so the conclusion holds for every choice
; whatever H2 says.  H2 is load-bearing for the theorems about what a crash may
; CHANGE, not for this one about what it may not DROP.  Recorded in HANDOFF.md.
(assert-event (not (fn-sf-crash-choicep :sideways :absent)))
(assert-event (equal (fn-sf-crash *sft-completed* :sideways :absent) *sft-completed*))

; -----------------------------------------------------------------------------
; Teeth for `fn-sf-crash-realizes-every-admissible-image' (D4)
;   (implies (fn-sf-crash-imagep s frontier records)
;            (let ((crashed (fn-sf-crash s (fn-sf-image-frontier-choice s frontier)
;                                          (fn-sf-image-record-choice s records))))
;              (and (equal (fn-sf-frontier crashed) frontier)
;                   (equal (fn-sf-records crashed) records) ...)))

; The witness side first: in :record-data-durable the link may already have
; been issued, so the image that carries the candidate is admissible and the
; constructor reproduces it exactly.
(assert-event (fn-sf-crash-imagep *sft-record-durable* 1 (list *sft-record*)))
(assert-event
 (equal (fn-sf-records
         (fn-sf-crash *sft-record-durable*
                      (fn-sf-image-frontier-choice *sft-record-durable* 1)
                      (fn-sf-image-record-choice *sft-record-durable*
                                                 (list *sft-record*))))
        (list *sft-record*)))

; The sole hypothesis dropped.  A frontier of 2 is neither the stable value (1)
; nor the candidate (no replacement can have been issued in a record phase), so
; the image is inadmissible and the choice function cannot conjure it: the
; crash still carries the stable frontier.
(assert-event (not (fn-sf-crash-imagep *sft-record-durable* 2
                                       (fn-sf-records *sft-record-durable*))))
(assert-event
 (equal (fn-sf-frontier
         (fn-sf-crash *sft-record-durable*
                      (fn-sf-image-frontier-choice *sft-record-durable* 2)
                      (fn-sf-image-record-choice *sft-record-durable*
                                                 (fn-sf-records *sft-record-durable*))))
        1))

(assert-event (with-guard-checking :none (not (equal (fn-sf-frontier
            (fn-sf-crash *sft-record-durable*
                         (fn-sf-image-frontier-choice *sft-record-durable* 2)
                         (fn-sf-image-record-choice
                          *sft-record-durable*
                          (fn-sf-records *sft-record-durable*))))
           2))))

; -----------------------------------------------------------------------------
; Teeth for `fn-sf-unobserved-frontier-replacement-crash-is-old-or-new'
;   (implies (and (fn-sf-statep s)
;                 (equal (fn-sf-phase s) :frontier-data-durable)   ; the tooth
;                 (or (equal record-choice :absent) (equal record-choice :present)))
;            (and (equal (fn-sf-frontier (fn-sf-crash s :old record-choice))
;                        (fn-sf-frontier s))
;                 (equal (fn-sf-frontier (fn-sf-crash s :new record-choice))
;                        (fn-sf-frontier-candidate s)) ...))

; The witness: in the data-durable phase BOTH whole values are outcomes.
(assert-event (equal (fn-sf-frontier (fn-sf-crash *sft-frontier-durable* :old :absent)) 0))
(assert-event (equal (fn-sf-frontier (fn-sf-crash *sft-frontier-durable* :new :absent)) 1))

; The phase hypothesis dropped.  One transition earlier, in :frontier-staged,
; no os.replace can have been issued yet, so :new does not select the
; candidate -- the crash point begins at the file barrier, not before it.
(assert-event (equal (fn-sf-frontier-candidate *sft-frontier-staged*) 1))
(assert-event (equal (fn-sf-frontier (fn-sf-crash *sft-frontier-staged* :new :absent)) 0))

(assert-event (with-guard-checking :none (not (equal (fn-sf-frontier (fn-sf-crash *sft-frontier-staged* :new :absent))
           (fn-sf-frontier-candidate *sft-frontier-staged*)))))

; -----------------------------------------------------------------------------
; Teeth for `fn-sf-unobserved-record-link-crash-is-absent-or-present'
;   (implies (and (fn-sf-statep s)
;                 (equal (fn-sf-phase s) :record-data-durable)   ; the tooth
;                 (or (equal frontier-choice :old) (equal frontier-choice :new)))
;            (and (equal (fn-sf-records (fn-sf-crash s frontier-choice :absent))
;                        (fn-sf-records s))
;                 (equal (fn-sf-records (fn-sf-crash s frontier-choice :present))
;                        (append (fn-sf-records s) (list (fn-sf-record-candidate s))))
;                 ...))

; The witness: in the data-durable phase BOTH images are outcomes, and they
; differ.
(assert-event (null (fn-sf-records (fn-sf-crash *sft-record-durable* :old :absent))))
(assert-event (equal (fn-sf-records (fn-sf-crash *sft-record-durable* :old :present))
                     (list *sft-record*)))

; The phase hypothesis dropped.  One transition earlier, in :record-staged, no
; os.link can have been issued, so :present does not publish the candidate.
(assert-event (with-guard-checking :none (not (equal (fn-sf-records (fn-sf-crash *sft-staged* :old :present))
           (append (fn-sf-records *sft-staged*)
                   (list (fn-sf-record-candidate *sft-staged*)))))))

; -----------------------------------------------------------------------------
; Teeth for `fn-sf-crash-outside-namespace-window-keeps-image'
;   (implies (and (fn-sf-statep s)
;                 (not (fn-sf-frontier-new-visiblep s))       ; H1
;                 (not (fn-sf-record-present-visiblep s)))    ; H2
;            (and (equal (fn-sf-frontier (fn-sf-crash s fc rc)) (fn-sf-frontier s))
;                 (equal (fn-sf-records (fn-sf-crash s fc rc)) (fn-sf-records s))))

; H1 dropped: the frontier window is open in :frontier-data-durable, and the
; image does change there.
(assert-event (fn-sf-frontier-new-visiblep *sft-frontier-durable*))
(assert-event (with-guard-checking :none (not (equal (fn-sf-frontier (fn-sf-crash *sft-frontier-durable* :new :absent))
           (fn-sf-frontier *sft-frontier-durable*)))))

; H2 dropped: the link window is open in :record-data-durable, and the record
; list does change there.
(assert-event (fn-sf-record-present-visiblep *sft-record-durable*))
(assert-event (with-guard-checking :none (not (equal (fn-sf-records (fn-sf-crash *sft-record-durable* :old :present))
           (fn-sf-records *sft-record-durable*)))))

; -----------------------------------------------------------------------------
; Teeth for `fn-sf-completed-frontier-barrier-removes-old-choice'
;   (implies (and (fn-sf-statep s) (equal (fn-sf-phase s) :frontier-attempted))
;            (equal (fn-sf-frontier (fn-sf-crash (fn-sf-frontier-dir-result s :ok) fc rc))
;                   (fn-sf-frontier-candidate s)))

; The witness: after the allocator directory barrier, EVERY choice yields the
; new frontier.  The old value is gone as a crash outcome.
(assert-event
 (equal (fn-sf-frontier
         (fn-sf-crash (fn-sf-frontier-dir-result *sft-frontier-attempted* :ok)
                      :old :absent))
        1))

; The phase hypothesis dropped.  Applied one transition early, in
; :frontier-data-durable, the barrier step is a no-op, the window is still
; open and :old still selects the old frontier.
(assert-event (equal (fn-sf-frontier-dir-result *sft-frontier-durable* :ok)
                     *sft-frontier-durable*))
(assert-event (with-guard-checking :none (not (equal (fn-sf-frontier
            (fn-sf-crash (fn-sf-frontier-dir-result *sft-frontier-durable* :ok)
                         :old :absent))
           (fn-sf-frontier-candidate *sft-frontier-durable*)))))

; -----------------------------------------------------------------------------
; Teeth for `fn-sf-completed-record-barrier-removes-absent-choice'
;   (implies (and (fn-sf-statep s) (equal (fn-sf-phase s) :record-attempted))
;            (equal (fn-sf-records (fn-sf-crash (fn-sf-record-dir-result s :ok) fc rc))
;                   (append (fn-sf-records s) (list (fn-sf-record-candidate s)))))

; The witness: after the transaction directory barrier, EVERY choice yields the
; published record.  Absence is gone as a crash outcome.
(assert-event
 (equal (fn-sf-records
         (fn-sf-crash (fn-sf-record-dir-result *sft-record-attempted* :ok)
                      :old :absent))
        (list *sft-record*)))

; The phase hypothesis dropped.  Applied one transition early, in
; :record-data-durable, the barrier step is a no-op and :absent still yields
; the empty history.
(assert-event (equal (fn-sf-record-dir-result *sft-record-durable* :ok)
                     *sft-record-durable*))
(assert-event (with-guard-checking :none (not (equal (fn-sf-records
            (fn-sf-crash (fn-sf-record-dir-result *sft-record-durable* :ok)
                         :old :absent))
           (append (fn-sf-records *sft-record-durable*)
                   (list (fn-sf-record-candidate *sft-record-durable*)))))))
