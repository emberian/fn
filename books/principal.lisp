; fn: principals, their identities and their key succession.
;
; A principal id is the tagged digest of an unambiguous encoding of (public
; key, token), mirroring dregg's
;   CellId = blake3::derive_key("dregg-cell-id-v1", pubkey || token)
; (~/dev/breadstuffs/README-LLMs.md section 2).  The token lets one key own
; several principals; the id is a commitment to the key.  A node checks a
; claimed genesis binding by recomputing the id (`fn-prin-genesis-bindsp`).
;
; The id is stable across key succession (D09: stable principals with
; recorded authorized key succession).  A succession is a statement
; (books/statement.lisp) of kind :succession issued by the principal whose
; payload names the NEW public key and whose signature verifies under the
; CURRENT key.  The principal's key chain is a state (id key incarnation
; next-sequence); applying a succession moves the key only when the statement
; is well formed, is by this principal, carries the expected (incarnation,
; sequence), decodes to a key and verifies under the current key.  This is the
; root-anchored chain shape of Dregg2/Crypto/CapabilityChain.lean `VerifyFrom`
; (each block verified under the parent's `nextPk`) and
; Dregg2/Authority/BiscuitGraph.lean `WellFormed`.
;
; A keyring is the node's resolved (id . public key) table.  It is an input to
; policy evaluation; how it was built (genesis bindings plus verified chains)
; is this book's job, and the policy theorems are conditional on it.

(in-package "ACL2")
(include-book "statement")

; cluster-local theory: this book is inside the substrate cluster and opens
; the definitions its neighbours withdraw at export (docs/proof-style.md 2).
(local (in-theory (enable fn-crypto-seam-internals
                          fn-stmt-internals)))

(defconst *fn-prin-id-tag* (fn-record-string-octets "fn-principal-v1"))
(defconst *fn-prin-max-token-octets* 64)

(defun fn-prin-tokenp (x)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp x)
       (<= (len x) *fn-prin-max-token-octets*)))

(defun fn-prin-idp (x)
  (declare (xargs :guard t))
  (fn-digest-octetsp x))

; -----------------------------------------------------------------------------
; Identity derivation

(defun fn-prin-preimage (pk token)
  (declare (xargs :guard (and (fn-sig-public-key-p pk)
                              (fn-prin-tokenp token))))
  (fn-stmt-encode-items (list (cons :bytes pk) (cons :bytes token))))

(defun fn-prin-id (pk token)
  (declare (xargs :guard (and (fn-sig-public-key-p pk)
                              (fn-prin-tokenp token))))
  (fn-digest-tagged *fn-prin-id-tag* (fn-prin-preimage pk token)))

(defthm fn-prin-id-is-id
  (fn-prin-idp (fn-prin-id pk token)))

(defun fn-prin-genesis-bindsp (id pk token)
  (declare (xargs :guard (and (fn-sig-public-key-p pk)
                              (fn-prin-tokenp token))))
  (equal id (fn-prin-id pk token)))

; -----------------------------------------------------------------------------
; Key chain state

(defun fn-prin-make-state (id key incarnation next)
  (declare (xargs :guard t))
  (list id key incarnation next))
(defun fn-prin-state-id (st)
  (declare (xargs :guard (true-listp st)))
  (car st))
(defun fn-prin-state-key (st)
  (declare (xargs :guard (true-listp st)))
  (car (cdr st)))
(defun fn-prin-state-incarnation (st)
  (declare (xargs :guard (true-listp st)))
  (car (cdr (cdr st))))
(defun fn-prin-state-next (st)
  (declare (xargs :guard (true-listp st)))
  (car (cdr (cdr (cdr st)))))

(defun fn-prin-statep (st)
  (declare (xargs :guard t))
  (and (true-listp st)
       (equal (len st) 4)
       (fn-prin-idp (fn-prin-state-id st))
       (fn-sig-public-key-p (fn-prin-state-key st))
       (fn-record-uint32p (fn-prin-state-incarnation st))
       (fn-record-uint32p (fn-prin-state-next st))))

(defun fn-prin-genesis-state (pk token incarnation)
  (declare (xargs :guard (and (fn-sig-public-key-p pk)
                              (fn-prin-tokenp token))))
  (fn-prin-make-state (fn-prin-id pk token) pk incarnation 1))

; -----------------------------------------------------------------------------
; Succession statements

; The payload of a succession is one byte-string item: the new public key.
(defun fn-prin-succession-key (s)
  (declare (xargs :guard (fn-stmt-p s)))
  (let ((r (fn-stmt-decode-items 1 (fn-stmt-payload s))))
    (if (and (fn-stmt-okp r)
             (consp (fn-stmt-value r))
             (null (cdr (fn-stmt-value r)))
             (fn-stmt-bytes-item-p (car (fn-stmt-value r)))
             (fn-sig-public-key-p (cdr (car (fn-stmt-value r)))))
        (cdr (car (fn-stmt-value r)))
      nil)))

(defun fn-prin-succession-acceptablep (st s)
  (declare (xargs :guard t))
  (and (fn-prin-statep st)
       (fn-stmt-p s)
       (equal (fn-stmt-kind s) :succession)
       (equal (fn-stmt-creator s) (fn-prin-state-id st))
       (equal (fn-stmt-incarnation s) (fn-prin-state-incarnation st))
       (equal (fn-stmt-sequence s) (fn-prin-state-next st))
       (< (fn-prin-state-next st) *fn-cbor-max-uint*)
       (if (fn-prin-succession-key s) t nil)
       (fn-stmt-verifiedp s (fn-prin-state-key st))))

(defthm fn-prin-acceptablep-implies-shapes
  (implies (fn-prin-succession-acceptablep st s)
           (and (fn-prin-statep st)
                (true-listp st)
                (fn-stmt-p s)
                (integerp (fn-prin-state-next st))
                (<= 0 (fn-prin-state-next st))))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory '(fn-prin-succession-acceptablep fn-prin-statep
                               fn-record-uint32p natp))))

(defun fn-prin-apply-succession (st s)
  (declare (xargs :guard t
                  :guard-hints
                  (("Goal"
                    :use fn-prin-acceptablep-implies-shapes
                    :do-not-induct t
                    :in-theory (disable fn-prin-succession-acceptablep
                                        fn-prin-statep
                                        fn-stmt-p fn-prin-succession-key)))))
  (if (fn-prin-succession-acceptablep st s)
      (fn-prin-make-state (fn-prin-state-id st)
                          (fn-prin-succession-key s)
                          (fn-prin-state-incarnation st)
                          (1+ (fn-prin-state-next st)))
    st))

(defun fn-prin-resolve (st stmts)
  (declare (xargs :guard t :measure (acl2-count stmts)))
  (if (consp stmts)
      (fn-prin-resolve (fn-prin-apply-succession st (car stmts)) (cdr stmts))
    st))

; The statements the walk actually accepted, in application order.
(defun fn-prin-trail (st stmts)
  (declare (xargs :guard t))
  (if (consp stmts)
      (if (fn-prin-succession-acceptablep st (car stmts))
          (cons (car stmts)
                (fn-prin-trail (fn-prin-apply-succession st (car stmts))
                               (cdr stmts)))
        (fn-prin-trail st (cdr stmts)))
    nil))

(defun fn-prin-chain-validp (st trail)
  (declare (xargs :guard t :measure (acl2-count trail)))
  (if (consp trail)
      (and (fn-prin-succession-acceptablep st (car trail))
           (fn-prin-chain-validp (fn-prin-apply-succession st (car trail))
                                 (cdr trail)))
    (null trail)))

(defun fn-prin-first-accepted (st stmts)
  (declare (xargs :guard t))
  (if (consp stmts)
      (if (fn-prin-succession-acceptablep st (car stmts))
          (car stmts)
        (fn-prin-first-accepted st (cdr stmts)))
    nil))

(defun fn-prin-succession-payload (new-pk)
  (declare (xargs :guard (fn-sig-public-key-p new-pk)))
  (fn-stmt-encode-items (list (cons :bytes new-pk))))

; Author a succession from the current chain state with seed `sk`.
(defun fn-prin-sign-succession (sk st new-pk)
  (declare (xargs :guard (and (fn-prin-statep st)
                              (fn-sig-public-key-p new-pk))))
  (fn-stmt-sign sk
                (fn-prin-state-id st)
                (fn-prin-state-incarnation st)
                (fn-prin-state-next st)
                nil
                :succession
                (fn-prin-succession-payload new-pk)))

; -----------------------------------------------------------------------------
; Keyrings

(defun fn-prin-keyringp (k)
  (declare (xargs :guard t))
  (if (consp k)
      (and (consp (car k))
           (fn-prin-idp (car (car k)))
           (fn-sig-public-key-p (cdr (car k)))
           (fn-prin-keyringp (cdr k)))
    (null k)))

(defun fn-prin-key-for (id keyring)
  (declare (xargs :guard (fn-prin-keyringp keyring)))
  (if (consp keyring)
      (if (equal id (car (car keyring)))
          (cdr (car keyring))
        (fn-prin-key-for id (cdr keyring)))
    nil))

(defun fn-prin-state-entry (st)
  (declare (xargs :guard (true-listp st)))
  (cons (fn-prin-state-id st) (fn-prin-state-key st)))

(defun fn-prin-state-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-prin-statep (car xs))
           (fn-prin-state-listp (cdr xs)))
    (null xs)))

(defun fn-prin-keyring-of-states (states)
  (declare (xargs :guard (fn-prin-state-listp states)))
  (if (consp states)
      (cons (fn-prin-state-entry (car states))
            (fn-prin-keyring-of-states (cdr states)))
    nil))

; A statement is verified against a keyring when its creator is a KNOWN
; principal and the statement verifies under that principal's resolved key.
; An unknown creator never verifies, whatever the seam says about NIL keys.
(defun fn-prin-verifiedp (s keyring)
  (declare (xargs :guard (fn-prin-keyringp keyring)))
  (and (fn-stmt-p s)
       (let ((pk (fn-prin-key-for (fn-stmt-creator s) keyring)))
         (and (fn-sig-public-key-p pk)
              (fn-stmt-verifiedp s pk)))))

; -----------------------------------------------------------------------------
; Record lemmas (docs/proof-style.md section 1).  Accessor of constructor,
; one per field, so nothing above this book opens a record.

(defthm fn-prin-state-id-of-fn-prin-make-state
  (equal (fn-prin-state-id (fn-prin-make-state id key incarnation next))
         id))
(defthm fn-prin-state-key-of-fn-prin-make-state
  (equal (fn-prin-state-key (fn-prin-make-state id key incarnation next))
         key))
(defthm fn-prin-state-incarnation-of-fn-prin-make-state
  (equal (fn-prin-state-incarnation (fn-prin-make-state id key incarnation next))
         incarnation))
(defthm fn-prin-state-next-of-fn-prin-make-state
  (equal (fn-prin-state-next (fn-prin-make-state id key incarnation next))
         next))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2).
;
; The key-chain record, the id derivation and the succession
; transitions are withdrawn; the chain-walking vocabulary stays.
;
; Only the `:definition' rune is withdrawn, so type prescriptions and
; executable counterparts still decide ground terms.  A book inside this
; cluster that must open one of these enables `fn-prin-internals' locally.

(deftheory fn-prin-internals
  '(
    (:d fn-prin-tokenp)
    (:d fn-prin-idp)
    (:d fn-prin-preimage)
    (:d fn-prin-id)
    (:d fn-prin-genesis-bindsp)
    (:d fn-prin-make-state)
    (:d fn-prin-state-id)
    (:d fn-prin-state-key)
    (:d fn-prin-state-incarnation)
    (:d fn-prin-state-next)
    (:d fn-prin-statep)
    (:d fn-prin-genesis-state)
    (:d fn-prin-succession-key)
    (:d fn-prin-succession-acceptablep)
    (:d fn-prin-apply-succession)
    (:d fn-prin-succession-payload)
    (:d fn-prin-sign-succession)
    (:d fn-prin-state-entry)
    (:d fn-prin-verifiedp)))

(in-theory (disable fn-prin-internals))
