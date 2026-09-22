; Identity and key-succession invariants for books/principal.lisp.
;
; Keystones:
;   fn-prin-preimage-injective
;     the encoded (public key, token) preimage determines both; this is what
;     "a principal id commits to a key" means BELOW the digest.  Equal ids
;     implying equal preimages is A-CRYPTO and is not proved (the seam's
;     constraints are satisfied by a constant digest; see the test book).
;   fn-prin-sign-succession-advances-key
;     the holder of the current key can move the key (the satisfiable pole).
;   fn-prin-first-key-move-is-verified-under-prior-key
;     if resolution ever moves the key, the first statement it accepted is a
;     :succession by this principal that verifies under the key held BEFORE
;     it; together with fn-prin-trail-is-valid-chain every later move is
;     verified under the key its predecessor installed.  Conditional on
;     fn-sig-verify, i.e. on what the seam's verifier accepts.

(in-package "ACL2")
(include-book "principal")
(include-book "statement-invariants")

; cluster-local theory: this book is inside the substrate cluster and opens
; the definitions its neighbours withdraw at export (docs/proof-style.md 2).
(local (in-theory (enable fn-crypto-seam-internals
                          fn-stmt-internals
                          fn-stmt-invariants-vocabulary
                          fn-prin-internals)))

;; Convergence (board, codecs ANSWER to substrate): re-open the codecs vocabulary this codec is built on.
(local (in-theory (enable fn-cbor-codec-vocabulary fn-cbor-invariants-vocabulary fn-record-record-vocabulary fn-record-codec-vocabulary fn-record-guard-vocabulary fn-record-invariants-vocabulary)))

; -----------------------------------------------------------------------------
; Identity

(defthm fn-prin-preimage-decodes
  (implies (and (fn-sig-public-key-p pk)
                (fn-prin-tokenp token))
           (equal (fn-stmt-decode-items 2 (fn-prin-preimage pk token))
                  (fn-stmt-ok (list (cons :bytes pk) (cons :bytes token)))))
  :hints (("Goal"
           :use ((:instance fn-stmt-decode-items-of-encode-items
                            (items (list (cons :bytes pk) (cons :bytes token)))
                            (fuel 2)))
           :in-theory (disable fn-stmt-decode-items fn-cbor-encode
                               fn-stmt-decode-items-of-encode-items))))

(defthm fn-prin-preimage-injective
  (implies (and (fn-sig-public-key-p pk1) (fn-prin-tokenp token1)
                (fn-sig-public-key-p pk2) (fn-prin-tokenp token2)
                (equal (fn-prin-preimage pk1 token1)
                       (fn-prin-preimage pk2 token2)))
           (and (equal pk1 pk2)
                (equal token1 token2)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-prin-preimage-decodes (pk pk1) (token token1))
                 (:instance fn-prin-preimage-decodes (pk pk2) (token token2)))
           ; The codec vocabulary this book opens at the top is what
           ; `fn-prin-preimage-decodes' needed; this goal needs none of it and
           ; the bounded codec made it a rewriter loop (call depth 1000 in
           ; Subgoal 2: `fn-cbor-decode' now opens into `fn-cbor-decode-bounded'
           ; and `fn-cbor-decode-prechecked', all three definitions being in
           ; `fn-cbor-codec-vocabulary').  Withdrawing the vocabulary for this
           ; goal alone leaves the proof to the two decode instances and the
           ; record shape rules, which is all it ever used.
           :in-theory (set-difference-theories
                       (disable fn-prin-preimage fn-stmt-decode-items
                                fn-prin-preimage-decodes)
                       (theory 'fn-cbor-codec-vocabulary)))))

; By definition; the name says exactly what is implied and nothing more.
(defthm fn-prin-id-unfolds
  (equal (fn-prin-id pk token)
         (fn-digest (fn-digest-tagged-preimage *fn-prin-id-tag*
                                               (fn-prin-preimage pk token)))))

; -----------------------------------------------------------------------------
; Succession: the satisfiable pole

(defthm fn-prin-succession-payload-is-payload
  (implies (fn-sig-public-key-p new-pk)
           (fn-stmt-payloadp (fn-prin-succession-payload new-pk)))
  :hints (("Goal" :in-theory (disable fn-cbor-encode))))

(defthm fn-prin-succession-key-of-payload
  (implies (fn-sig-public-key-p new-pk)
           (equal (fn-stmt-decode-items 1 (fn-prin-succession-payload new-pk))
                  (fn-stmt-ok (list (cons :bytes new-pk)))))
  :hints (("Goal"
           :use ((:instance fn-stmt-decode-items-of-encode-items
                            (items (list (cons :bytes new-pk)))
                            (fuel 1)))
           :in-theory (disable fn-stmt-decode-items fn-cbor-encode
                               fn-stmt-decode-items-of-encode-items))))

(defthm fn-prin-succession-key-of-sign
  (implies (and (fn-prin-statep st)
                (fn-sig-public-key-p new-pk))
           (equal (fn-prin-succession-key (fn-prin-sign-succession sk st new-pk))
                  new-pk))
  :hints (("Goal" :in-theory (disable fn-stmt-decode-items
                                      fn-prin-succession-payload
                                      fn-digest-tagged fn-stmt-signing-preimage
                                      fn-stmt-payload-ref))))

(defthm fn-prin-sign-succession-is-verified
  (implies (and (fn-prin-statep st)
                (fn-sig-seed-p sk)
                (fn-sig-public-key-p new-pk))
           (fn-stmt-verifiedp (fn-prin-sign-succession sk st new-pk)
                              (fn-sig-public-key sk)))
  :hints (("Goal"
           :use ((:instance fn-stmt-sign-is-verified
                            (creator (fn-prin-state-id st))
                            (incarnation (fn-prin-state-incarnation st))
                            (sequence (fn-prin-state-next st))
                            (preds nil)
                            (kind :succession)
                            (payload (fn-prin-succession-payload new-pk))))
           :in-theory (disable fn-stmt-sign-is-verified fn-stmt-sign
                               fn-stmt-verifiedp fn-prin-succession-payload
                               fn-stmt-payloadp))))

(defthm fn-prin-sign-succession-fields
  (implies (fn-prin-statep st)
           (and (equal (fn-stmt-kind (fn-prin-sign-succession sk st new-pk))
                       :succession)
                (equal (fn-stmt-creator (fn-prin-sign-succession sk st new-pk))
                       (fn-prin-state-id st))
                (equal (fn-stmt-incarnation
                        (fn-prin-sign-succession sk st new-pk))
                       (fn-prin-state-incarnation st))
                (equal (fn-stmt-sequence (fn-prin-sign-succession sk st new-pk))
                       (fn-prin-state-next st))))
  :hints (("Goal" :in-theory (disable fn-stmt-payload-ref
                                      fn-stmt-signing-preimage
                                      fn-prin-succession-payload))))

(defthm fn-prin-verified-implies-stmt-p
  (implies (fn-stmt-verifiedp s pk)
           (fn-stmt-p s))
  :hints (("Goal" :in-theory '(fn-stmt-verifiedp))))

(defthm fn-prin-sign-succession-is-stmt
  (implies (and (fn-prin-statep st)
                (fn-sig-seed-p sk)
                (fn-sig-public-key-p new-pk))
           (fn-stmt-p (fn-prin-sign-succession sk st new-pk)))
  :hints (("Goal"
           :use ((:instance fn-prin-sign-succession-is-verified))
           :in-theory '(fn-stmt-verifiedp))))

(defthm fn-prin-sign-succession-is-acceptable
  (implies (and (fn-prin-statep st)
                (fn-sig-seed-p sk)
                (equal (fn-sig-public-key sk) (fn-prin-state-key st))
                (fn-sig-public-key-p new-pk)
                (< (fn-prin-state-next st) *fn-cbor-max-uint*))
           (fn-prin-succession-acceptablep
            st (fn-prin-sign-succession sk st new-pk)))
  :hints (("Goal"
           :use ((:instance fn-prin-sign-succession-is-verified)
                 (:instance fn-prin-sign-succession-is-stmt)
                 (:instance fn-prin-sign-succession-fields)
                 (:instance fn-prin-succession-key-of-sign))
           :in-theory (disable fn-prin-sign-succession fn-stmt-verifiedp
                               fn-prin-succession-key fn-stmt-kind
                               fn-stmt-creator fn-stmt-incarnation
                               fn-stmt-sequence fn-prin-statep fn-stmt-p
                               fn-prin-sign-succession-is-verified
                               fn-prin-sign-succession-is-stmt
                               fn-prin-sign-succession-fields
                               fn-prin-succession-key-of-sign))))

(defthm fn-prin-sign-succession-advances-key
  (implies (and (fn-prin-statep st)
                (fn-sig-seed-p sk)
                (equal (fn-sig-public-key sk) (fn-prin-state-key st))
                (fn-sig-public-key-p new-pk)
                (< (fn-prin-state-next st) *fn-cbor-max-uint*))
           (equal (fn-prin-state-key
                   (fn-prin-apply-succession
                    st (fn-prin-sign-succession sk st new-pk)))
                  new-pk))
  :hints (("Goal"
           :use ((:instance fn-prin-sign-succession-is-acceptable)
                 (:instance fn-prin-succession-key-of-sign))
           :in-theory (disable fn-prin-sign-succession
                               fn-prin-succession-acceptablep
                               fn-prin-succession-key fn-prin-statep
                               fn-prin-sign-succession-is-acceptable
                               fn-prin-succession-key-of-sign))))

; -----------------------------------------------------------------------------
; Succession: confinement to the prior key

(defthm fn-prin-apply-succession-preserves-statep
  (implies (fn-prin-statep st)
           (fn-prin-statep (fn-prin-apply-succession st s)))
  :hints (("Goal" :in-theory (disable fn-stmt-verifiedp fn-stmt-p
                                      fn-stmt-decode-items))))

(defthm fn-prin-resolve-preserves-statep
  (implies (fn-prin-statep st)
           (fn-prin-statep (fn-prin-resolve st stmts)))
  :hints (("Goal" :in-theory (disable fn-prin-apply-succession
                                      fn-prin-statep))))

(defthm fn-prin-trail-is-valid-chain
  (fn-prin-chain-validp st (fn-prin-trail st stmts))
  :hints (("Goal" :induct (fn-prin-trail st stmts)
           :in-theory (disable fn-prin-succession-acceptablep
                               fn-prin-apply-succession))))

(defthm fn-prin-apply-succession-when-not-acceptable
  (implies (not (fn-prin-succession-acceptablep st s))
           (equal (fn-prin-apply-succession st s) st))
  :hints (("Goal" :in-theory '(fn-prin-apply-succession))))

(defthm fn-prin-resolve-is-resolve-of-trail
  (equal (fn-prin-resolve st (fn-prin-trail st stmts))
         (fn-prin-resolve st stmts))
  :hints (("Goal" :induct (fn-prin-trail st stmts)
           :in-theory (disable fn-prin-apply-succession
                               fn-prin-succession-acceptablep
                               fn-prin-statep))))

; Every step of a valid chain is a :succession by the principal, verified under
; the key held before that step.  Definitional; stated so the chain theorem
; above reads as the confinement it is.
(defthm fn-prin-chain-step-unfolds
  (implies (and (fn-prin-chain-validp st trail)
                (consp trail))
           (and (fn-stmt-verifiedp (car trail) (fn-prin-state-key st))
                (equal (fn-stmt-creator (car trail)) (fn-prin-state-id st))
                (equal (fn-stmt-kind (car trail)) :succession)
                (fn-prin-chain-validp (fn-prin-apply-succession st (car trail))
                                      (cdr trail))))
  :hints (("Goal" :in-theory '(fn-prin-chain-validp
                               fn-prin-succession-acceptablep))))

(defthm fn-prin-first-key-move-is-verified-under-prior-key
  (implies (and (fn-prin-statep st)
                (not (equal (fn-prin-state-key (fn-prin-resolve st stmts))
                            (fn-prin-state-key st))))
           (and (member-equal (fn-prin-first-accepted st stmts) stmts)
                (fn-stmt-verifiedp (fn-prin-first-accepted st stmts)
                                   (fn-prin-state-key st))
                (equal (fn-stmt-creator (fn-prin-first-accepted st stmts))
                       (fn-prin-state-id st))
                (equal (fn-stmt-kind (fn-prin-first-accepted st stmts))
                       :succession)))
  :hints (("Goal" :induct (fn-prin-first-accepted st stmts)
           :in-theory (e/d (fn-prin-apply-succession)
                           (fn-stmt-verifiedp fn-stmt-creator fn-stmt-kind
                            fn-prin-succession-key fn-stmt-p
                            fn-stmt-incarnation fn-stmt-sequence
                            fn-prin-statep)))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2).
;
; The keystones below stay enabled on include; everything else this book
; proves is proof vocabulary and is withdrawn under `fn-prin-invariants-vocabulary',
; which a book inside this cluster enables locally in one line.
;
; * fn-prin-preimage-injective
; * fn-prin-sign-succession-is-acceptable
; * fn-prin-sign-succession-advances-key
; * fn-prin-apply-succession-preserves-statep
; * fn-prin-resolve-preserves-statep
; * fn-prin-trail-is-valid-chain
; * fn-prin-first-key-move-is-verified-under-prior-key
; * fn-prin-verified-implies-stmt-p

(deftheory fn-prin-invariants-vocabulary
  '(
    fn-prin-preimage-decodes
    fn-prin-id-unfolds
    fn-prin-succession-payload-is-payload
    fn-prin-succession-key-of-payload
    fn-prin-succession-key-of-sign
    fn-prin-sign-succession-is-verified
    fn-prin-sign-succession-fields
    fn-prin-sign-succession-is-stmt
    fn-prin-apply-succession-when-not-acceptable
    fn-prin-resolve-is-resolve-of-trail
    fn-prin-chain-step-unfolds))

(in-theory (disable fn-prin-invariants-vocabulary))
