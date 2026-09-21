; Teeth for the unforgeable-acknowledgement and reopen-fidelity keystones.
;
; The 2026-09-18 review §5: "Acknowledgement cannot be forged.
; `fn-sn-new-success-requires-actual-matching-durable-node-completion' and
; `fn-sn-actual-durable-completion-installs-record'; every single-field
; mismatch blocks `finish'."  D6 (the theorem subject is the function the host
; calls) is `fn-sn-open-observed-success-has-live-history-relation' and D5
; (A-DURABILITY as a hypothesis, not a constructor) is
; `fn-sn-acknowledged-record-survives-observed-reopen'; both are reached here
; through store-observed-traces, which this book includes.
;
; The composition tested here is the one after the crash-fidelity rewrite:
; `fn-sn-finish' performs the three-argument `fn-sf-core-completion' and
; `fn-sf-emit-success' in one call, and the crash choices are live only in the
; data-durable phases.  The cases that used to target the removed fenced
; phases are replaced by the composed crash-choice cases below.

(in-package "ACL2")
(include-book "../../books/store-observed")

; -----------------------------------------------------------------------------
; A reachable, non-degenerate witness: the composed store driven from its
; initial state through allocation, staging, publication and finish, with a
; record whose Message-ID, archive identity, content subject and release
; evidence are four different strings across two groups.

(defconst *snt-groups* '("fn.letters" "fn.test"))
(defconst *snt-record*
  (fn-record-make 0 0 0 "<sn@example>" '(65 66) *snt-groups*
                  "sn-pin" "sn-content" "sn-release" 2))

(defconst *snt-reserved*
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-initial *snt-groups* 10)
                                          :start-frontier nil)
                                :frontier-file :ok)
                      :frontier-replace :ok)
            :frontier-directory :ok))
(defconst *snt-prepared* (fn-sn-prepare *snt-reserved* *snt-record*))
(defconst *snt-record-durable* (fn-sn-io *snt-prepared* :record-file :ok))
(defconst *snt-record-attempted* (fn-sn-io *snt-record-durable* :record-link :ok))
(defconst *snt-completing* (fn-sn-io *snt-record-attempted* :record-directory :ok))
(defconst *snt-finished* (fn-sn-finish *snt-completing*))

(assert-event (fn-sn-statep *snt-prepared*))
(assert-event (fn-sn-statep *snt-record-durable*))
(assert-event (fn-sn-statep *snt-completing*))
(assert-event (fn-sn-statep *snt-finished*))
(assert-event (fn-sn-record-bindsp (fn-sn-node *snt-prepared*) *snt-record*))
(assert-event (equal (fn-sf-phase (fn-sn-files *snt-record-durable*))
                     :record-data-durable))
(assert-event (equal (fn-sf-phase (fn-sn-files *snt-completing*)) :completing))
(assert-event (equal (fn-sf-phase (fn-sn-files *snt-finished*)) :ready))

; Non-degenerate: the record binds on every field, and the four identities in
; it are distinct, so a relation that compared only one of them would not do.
(assert-event (not (equal (fn-record-msgid *snt-record*)
                          (fn-record-content-subject *snt-record*))))
(assert-event (not (equal (fn-record-obligation-id *snt-record*)
                          (fn-record-release-evidence *snt-record*))))

; The success appears only at finish, and the record is committed by it.
(assert-event (null (fn-sf-successes (fn-sn-files *snt-completing*))))
(assert-event (equal (fn-sf-successes (fn-sn-files *snt-finished*)) '((0 . 0))))
(assert-event (fn-sn-committed-recordp (fn-sn-node *snt-finished*) *snt-record*))
(assert-event (equal (fn-sn-finish *snt-finished*) *snt-finished*))

; -----------------------------------------------------------------------------
; Teeth for `fn-sn-actual-durable-completion-installs-record'
;   (implies (fn-sn-record-bindsp node record)
;            (fn-sn-committed-recordp
;             (fn-node-complete node (fn-record-txid record)
;                               (fn-record-generation record) :durable)
;             record))

; The sole hypothesis dropped.  A record that differs from the staged one in a
; single field -- the payload -- shares its sequence, transaction and
; generation, so the completion it names still fires; what it does not do is
; commit the record it claims.
(defconst *snt-other-record*
  (fn-record-make 0 0 0 "<sn@example>" '(99) *snt-groups*
                  "sn-pin" "sn-content" "sn-release" 2))
(assert-event
 (equal (fn-record-txid *snt-other-record*) (fn-record-txid *snt-record*)))
(assert-event
 (equal (fn-record-generation *snt-other-record*)
        (fn-record-generation *snt-record*)))
(assert-event
 (not (fn-sn-record-bindsp (fn-sn-node *snt-prepared*) *snt-other-record*)))

(assert-event (with-guard-checking :none (not (fn-sn-committed-recordp
     (fn-node-complete (fn-sn-node *snt-prepared*)
                       (fn-record-txid *snt-other-record*)
                       (fn-record-generation *snt-other-record*)
                       :durable)
     *snt-other-record*))))

; -----------------------------------------------------------------------------
; Teeth for `fn-sn-new-success-requires-actual-matching-durable-node-completion'
;   (implies (not (equal (fn-sf-successes (fn-sn-files (fn-sn-finish s)))
;                        (fn-sf-successes (fn-sn-files s))))
;            (and (fn-sn-completion-enabledp s)
;                 (fn-sn-record-bindsp (fn-sn-node s) (fn-sn-completion-record s))
;                 ...
;                 (fn-sn-committed-recordp (fn-sn-node (fn-sn-finish s))
;                                          (fn-sn-completion-record s))))

; The sole hypothesis dropped.  In the staged state, finish is a no-op, so the
; success list does not change and the hypothesis is false; the conclusion is
; false there too, in both of the conjuncts below, because completion is not
; enabled before the record directory barrier.  That is the direction the
; theorem is protecting: no success without an enabled, matching, durable
; completion.
(assert-event
 (equal (fn-sf-successes (fn-sn-files (fn-sn-finish *snt-prepared*)))
        (fn-sf-successes (fn-sn-files *snt-prepared*))))
(assert-event (not (fn-sn-completion-enabledp *snt-prepared*)))

(assert-event (with-guard-checking :none (not (fn-sn-completion-enabledp *snt-prepared*))))

(assert-event (with-guard-checking :none (not (fn-sn-committed-recordp (fn-sn-node (fn-sn-finish *snt-prepared*))
                             (fn-sn-completion-record *snt-prepared*)))))

; -----------------------------------------------------------------------------
; Teeth for `fn-sn-finish-disabled-is-no-op'
;   (implies (not (fn-sn-completion-enabledp s)) (equal (fn-sn-finish s) s))
; and `fn-sn-finish-acknowledges-exact-pair'
;   (implies (fn-sn-completion-enabledp s)
;            (equal (fn-sf-successes (fn-sn-files (fn-sn-finish s)))
;                   (append (fn-sf-successes (fn-sn-files s))
;                           (list (fn-sf-completion (fn-sn-files s))))))

; The no-op theorem's sole hypothesis dropped: where completion IS enabled,
; finish is exactly the step that is not a no-op.
(assert-event (fn-sn-completion-enabledp *snt-completing*))
(assert-event (with-guard-checking :none (not (equal (fn-sn-finish *snt-completing*) *snt-completing*))))

; The acknowledgement theorem's sole hypothesis dropped: where completion is
; not enabled, the success list does not grow by the completion pair.  In the
; staged state that pair is not even bound.
(assert-event (null (fn-sf-completion (fn-sn-files *snt-prepared*))))
(assert-event (with-guard-checking :none (not (equal (fn-sf-successes (fn-sn-files (fn-sn-finish *snt-prepared*)))
           (append (fn-sf-successes (fn-sn-files *snt-prepared*))
                   (list (fn-sf-completion (fn-sn-files *snt-prepared*))))))))

; -----------------------------------------------------------------------------
; Teeth for `fn-sn-crash-files-are-kernel-crash'
;   (implies (and (fn-sn-statep s)                                     ; H1
;                 (fn-sf-crash-choicep frontier-choice record-choice))  ; H2
;            (and (equal (fn-sn-files (fn-sn-crash s fc rc))
;                        (fn-sf-crash (fn-sn-files s) fc rc)) ...))

; The witness side first, and the crash choices the rewrite left in place: in
; the data-durable phase the composed crash yields BOTH images, and after the
; record directory barrier the absent choice is gone.
(assert-event
 (null (fn-sf-records (fn-sn-files (fn-sn-crash *snt-record-durable* :old :absent)))))
(assert-event
 (equal (fn-sf-records (fn-sn-files (fn-sn-crash *snt-record-durable* :old :present)))
        (list *snt-record*)))
(assert-event
 (equal (fn-sf-records (fn-sn-files (fn-sn-crash *snt-completing* :old :absent)))
        (list *snt-record*)))
(assert-event
 (equal (fn-sn-node (fn-sn-crash *snt-record-durable* :old :present))
        (fn-node-initial-state *snt-groups* 10)))

; H1 dropped.  A forged composition whose node component is not a node refuses
; the composed crash, so its file component is left in :record-data-durable
; while the kernel crash of that same component is a :replaying image carrying
; the linked record.  The two are not equal.
(defconst *snt-forged*
  (fn-sn-make *snt-groups* 10 (fn-sn-files *snt-record-durable*) :not-a-node
              nil (fn-stx-index-empty)))
(assert-event (not (fn-sn-statep *snt-forged*)))
(assert-event (fn-sf-crash-choicep :old :present))
(assert-event (equal (fn-sn-crash *snt-forged* :old :present) *snt-forged*))

(assert-event (with-guard-checking :none (not (equal (fn-sn-files (fn-sn-crash *snt-forged* :old :present))
           (fn-sf-crash (fn-sn-files *snt-forged*) :old :present)))))

; H2 has no teeth, and none is forged.  Outside `fn-sf-crash-choicep' both
; `fn-sn-crash' and `fn-sf-crash' return their argument unchanged, so the
; equality holds for every non-choice whatever H2 says; H2 is load-bearing for
; the theorems about what a crash may CHANGE.  Recorded in HANDOFF.md.
(assert-event (not (fn-sf-crash-choicep :old :sideways)))
(assert-event
 (equal (fn-sn-files (fn-sn-crash *snt-completing* :old :sideways))
        (fn-sf-crash (fn-sn-files *snt-completing*) :old :sideways)))

; -----------------------------------------------------------------------------
; Teeth for `fn-sn-open-observed-success-has-live-history-relation' (D6)
;   (implies (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier records))
;            (fn-snt-relation
;             (fn-sn-open-state (fn-sn-open-observed groups capacity frontier records))))

; The witness: the image the host actually resumes from -- the durable frontier
; and the published record -- opens successfully and satisfies the relation, so
; every trace theorem rooted at the relation applies to it.
(assert-event
 (fn-sn-open-okp (fn-sn-open-observed *snt-groups* 10 1 (list *snt-record*))))
(assert-event
 (fn-snt-relation
  (fn-sn-open-state (fn-sn-open-observed *snt-groups* 10 1 (list *snt-record*)))))

; The sole hypothesis dropped.  A record whose txid is not below the frontier
; is a structurally invalid history: the open refuses with a distinct code and
; there is no state for the relation to hold of.
(assert-event
 (fn-sn-open-errorp (fn-sn-open-observed *snt-groups* 10 0 (list *snt-record*))))
(assert-event (with-guard-checking :none (not (fn-snt-relation
     (fn-sn-open-state (fn-sn-open-observed *snt-groups* 10 0 (list *snt-record*)))))))

; -----------------------------------------------------------------------------
; Teeth for `fn-sn-acknowledged-record-survives-observed-reopen' (D5)
;   (implies (and (fn-snt-relation s)                                    ; H1
;                 (fn-sf-crash-imagep (fn-sn-files s) frontier records)   ; H2
;                 (member-equal pair (fn-sf-successes (fn-sn-files s))))  ; H3
;            (and (fn-sn-open-okp (fn-sn-open-observed ... frontier records))
;                 (fn-sf-record-has-pairp
;                  pair (fn-sf-records (fn-sn-files (fn-sn-open-state ...))))))

; The witness: the acknowledged pair of the finished store survives the reopen
; on the admissible image.
(assert-event (fn-snt-relation *snt-finished*))
(assert-event (fn-sf-crash-imagep (fn-sn-files *snt-finished*) 1 (list *snt-record*)))
(assert-event (member-equal '(0 . 0) (fn-sf-successes (fn-sn-files *snt-finished*))))
(assert-event
 (fn-sf-record-has-pairp
  '(0 . 0)
  (fn-sf-records
   (fn-sn-files
    (fn-sn-open-state
     (fn-sn-open-observed (fn-sn-groups *snt-finished*) (fn-sn-capacity *snt-finished*)
                          1 (list *snt-record*)))))))

; H2 dropped -- this is A-DURABILITY itself.  An empty record list at the same
; frontier is a structurally valid, replayable image, so the reopen SUCCEEDS;
; what it does not do is retain the acknowledged pair.  Nothing but the
; admissibility premise stands between an acknowledged record and its
; disappearance.
(assert-event (not (fn-sf-crash-imagep (fn-sn-files *snt-finished*) 1 nil)))
(assert-event
 (fn-sn-open-okp
  (fn-sn-open-observed (fn-sn-groups *snt-finished*) (fn-sn-capacity *snt-finished*)
                       1 nil)))
(assert-event (with-guard-checking :none (not (fn-sf-record-has-pairp
     '(0 . 0)
     (fn-sf-records
      (fn-sn-files
       (fn-sn-open-state
        (fn-sn-open-observed (fn-sn-groups *snt-finished*)
                             (fn-sn-capacity *snt-finished*) 1 nil))))))))

; H1 dropped.  A forged composition with the same file component but a
; configuration that is not a group list carries the same acknowledgement and
; the same admissible image, yet the reopen refuses: the relation is what
; guarantees the configuration the reopen is handed is the one that replays.
(defconst *snt-relation-forged*
  (fn-sn-make '(:not-a-group) 10 (fn-sn-files *snt-finished*)
              (fn-sn-node *snt-finished*) nil (fn-stx-index-empty)))
(assert-event (not (fn-snt-relation *snt-relation-forged*)))
(assert-event
 (fn-sf-crash-imagep (fn-sn-files *snt-relation-forged*) 1 (list *snt-record*)))
(assert-event
 (member-equal '(0 . 0) (fn-sf-successes (fn-sn-files *snt-relation-forged*))))
(assert-event (with-guard-checking :none (not (fn-sn-open-okp
     (fn-sn-open-observed (fn-sn-groups *snt-relation-forged*)
                          (fn-sn-capacity *snt-relation-forged*)
                          1 (list *snt-record*))))))

; H3 dropped.  A pair that was never acknowledged names no record in the
; reopened history, on exactly the admissible image that retains the one that
; was.
(assert-event (not (member-equal '(9 . 9) (fn-sf-successes (fn-sn-files *snt-finished*)))))
(assert-event (with-guard-checking :none (not (fn-sf-record-has-pairp
     '(9 . 9)
     (fn-sf-records
      (fn-sn-files
       (fn-sn-open-state
        (fn-sn-open-observed (fn-sn-groups *snt-finished*)
                             (fn-sn-capacity *snt-finished*)
                             1 (list *snt-record*)))))))))
