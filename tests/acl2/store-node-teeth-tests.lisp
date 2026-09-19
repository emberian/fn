; Teeth for the unforgeable-acknowledgement keystones.
;
; The 2026-09-18 review §5: "Acknowledgement cannot be forged.
; `fn-sn-new-success-requires-actual-matching-durable-node-completion' and
; `fn-sn-actual-durable-completion-installs-record'; every single-field
; mismatch blocks `finish'."  One hypothesis each; both get teeth.

(in-package "ACL2")
(include-book "../../books/store-node-invariants")
(include-book "std/testing/must-fail" :dir :system)

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
(defconst *snt-completing*
  (fn-sn-io (fn-sn-io (fn-sn-io *snt-prepared* :record-file :ok)
                      :record-link :ok)
            :record-directory :ok))
(defconst *snt-finished* (fn-sn-finish *snt-completing*))

(assert-event (fn-sn-statep *snt-prepared*))
(assert-event (fn-sn-statep *snt-completing*))
(assert-event (fn-sn-statep *snt-finished*))
(assert-event (fn-sn-record-bindsp (fn-sn-node *snt-prepared*) *snt-record*))

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

(local
 (must-fail
  (defthm snt-teeth-installs-record-without-binding
    (fn-sn-committed-recordp
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
;                 ...))

; The sole hypothesis dropped.  In the staged state, finish is a no-op, so the
; success list does not change and the hypothesis is false; the conclusion is
; false there too, because completion is not enabled before the record
; directory barrier.  That is the direction the theorem is protecting: no
; success without an enabled, matching, durable completion.
(assert-event
 (equal (fn-sf-successes (fn-sn-files (fn-sn-finish *snt-prepared*)))
        (fn-sf-successes (fn-sn-files *snt-prepared*))))
(assert-event (not (fn-sn-completion-enabledp *snt-prepared*)))

(local
 (must-fail
  (defthm snt-teeth-new-success-without-a-new-success
    (fn-sn-completion-enabledp *snt-prepared*))))
