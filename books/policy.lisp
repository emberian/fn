; fn: group policy, authorization and the policy term.
;
; A group's policy is a statement (books/statement.lisp) of kind :policy
; whose creator is the group's AUTHORITY principal and whose payload names
; the group, the principals authorized to post, and terms.  The policy in
; force in a lace is the authority's latest verified policy statement for the
; group (by (incarnation, sequence)); two distinct policy statements at one
; slot are an equivocation by the authority and leave the group with NO
; policy in force (fail closed, both retained as evidence).
;
; Authorization is a function of the lace and a keyring (books/principal.lisp):
;   :policy  only the authority may change the policy
;   :post    a principal listed by the policy in force, or the authority
; The authority-confinement theorems (books/policy-invariants.lisp) are
; conditional on the seam's `fn-sig-verify` through `fn-prin-verifiedp`.
;
; The POLICY TERM (ATLAS law 12: bind the policy term, not the decision bit)
; is (content id of the policy statement in force . digest of the evidence
; used), where the evidence is the two resolved public keys and the admitted
; statement's canonical bytes.  A receipt commits to the term; a later reader
; with the lace and keyring re-resolves it (fn-pol-receipt-re-verifiable).
;
; Shapes mirror the capability-chain reading of authority: a policy statement
; is the root block naming who may act, checked under the authority's key
; (Dregg2/Crypto/CapabilityChain.lean:65 `VerifyChain`,
; Dregg2/Authority/BiscuitGraph.lean:55 `SigChecker`); delegation depth is one
; (owner/admin succession, D11), so no attenuation chain is modelled yet.

(in-package "ACL2")
(include-book "lace")
(include-book "principal")
(include-book "statement-invariants")


;; Convergence: the codecs cluster withdraws its proof vocabulary on export;
;; re-open it locally (agreed on the deputy board, codecs ANSWER to substrate).
(local (in-theory (enable fn-cbor-codec-vocabulary fn-cbor-invariants-vocabulary fn-record-record-vocabulary fn-record-codec-vocabulary fn-record-guard-vocabulary fn-record-invariants-vocabulary)))

; cluster-local theory: this book is inside the substrate cluster and opens
; the definitions its neighbours withdraw at export (docs/proof-style.md 2).
(local (in-theory (enable fn-crypto-seam-internals
                          fn-stmt-internals
                          fn-stmt-invariants-vocabulary
                          fn-prin-internals
                          fn-lace-internals)))

(local (in-theory (disable fn-stmt-id fn-stmt-p fn-stmt-creator
                           fn-stmt-incarnation fn-stmt-sequence fn-stmt-preds
                           fn-stmt-payload fn-stmt-header fn-stmt-kind
                           fn-stmt-sign fn-stmt-payload-ref
                           fn-stmt-signing-preimage)))

(defthm fn-pol-stmt-p-shape
  (implies (fn-stmt-p s)
           (and (true-listp s) (consp s)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable fn-stmt-p))))

(defconst *fn-pol-max-members* 64)
(defconst *fn-pol-max-name-octets* 128)
(defconst *fn-pol-max-terms-octets* 256)
(defconst *fn-pol-max-policy-items* 68)
(defconst *fn-pol-evidence-tag* (fn-record-string-octets "fn-policy-evidence-v1"))

; -----------------------------------------------------------------------------
; Policy payloads: (group members terms)

(defun fn-pol-namep (x)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp x)
       (consp x)
       (<= (len x) *fn-pol-max-name-octets*)))

(defun fn-pol-termsp (x)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp x)
       (<= (len x) *fn-pol-max-terms-octets*)))

(defun fn-pol-make-policy (group members terms)
  (declare (xargs :guard t))
  (list group members terms))
(defun fn-pol-policy-group (p)
  (declare (xargs :guard (true-listp p)))
  (car p))
(defun fn-pol-policy-members (p)
  (declare (xargs :guard (true-listp p)))
  (car (cdr p)))
(defun fn-pol-policy-terms (p)
  (declare (xargs :guard (true-listp p)))
  (car (cdr (cdr p))))

(defun fn-pol-policy-p (p)
  (declare (xargs :guard t))
  (and (true-listp p)
       (equal (len p) 3)
       (fn-pol-namep (fn-pol-policy-group p))
       (fn-stmt-id-listp (fn-pol-policy-members p))
       (<= (len (fn-pol-policy-members p)) *fn-pol-max-members*)
       (fn-stmt-no-duplicatesp (fn-pol-policy-members p))
       (fn-pol-termsp (fn-pol-policy-terms p))))

(defun fn-pol-policy-items (p)
  (declare (xargs :guard (fn-pol-policy-p p)))
  (append (list (cons :bytes (fn-pol-policy-group p))
                (cons :uint (len (fn-pol-policy-members p))))
          (fn-stmt-id-items (fn-pol-policy-members p))
          (list (cons :bytes (fn-pol-policy-terms p)))))

(defun fn-pol-policy-of-items (items)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :do-not-induct t
                                 :in-theory (disable fn-stmt-okp fn-stmt-value fn-stmt-rest
                                                     fn-stmt-take-id-items
                                                     fn-digest-octetsp
                                                     fn-record-uint32p
                                                     fn-cbor-octet-listp
                                                     fn-stmt-no-duplicatesp
                                                     fn-pol-namep
                                                     fn-pol-termsp
                                                     fn-pol-make-policy)))))
  (if (not (and (consp items)
                (fn-stmt-bytes-item-p (car items))
                (fn-pol-namep (cdr (car items)))))
      (fn-stmt-error :group)
    (let ((i1 (cdr items)))
      (if (not (and (consp i1)
                    (fn-stmt-uint-item-p (car i1))
                    (<= (cdr (car i1)) *fn-pol-max-members*)))
          (fn-stmt-error :member-count)
        (let ((taken (fn-stmt-take-id-items (cdr (car i1)) (cdr i1))))
          (if (not (fn-stmt-okp taken))
              taken
            (let ((members (fn-stmt-value taken))
                  (i2 (fn-stmt-rest taken)))
              (if (not (fn-stmt-no-duplicatesp members))
                  (fn-stmt-error :duplicate-member)
                (if (not (and (consp i2)
                              (fn-stmt-bytes-item-p (car i2))
                              (fn-pol-termsp (cdr (car i2)))))
                    (fn-stmt-error :terms)
                  (if (not (null (cdr i2)))
                      (fn-stmt-error :trailing)
                    (fn-stmt-ok (fn-pol-make-policy
                                 (cdr (car items)) members
                                 (cdr (car i2))))))))))))))

(defthm fn-pol-policy-items-are-items
  (implies (fn-pol-policy-p p)
           (fn-stmt-item-listp (fn-pol-policy-items p))))

(defun fn-pol-policy-encode (p)
  (declare (xargs :guard t))
  (if (fn-pol-policy-p p)
      (fn-stmt-encode-items (fn-pol-policy-items p))
    nil))

(defun fn-pol-policy-decode-exact (octets)
  (declare (xargs :guard t))
  (if (not (fn-cbor-at-mostp octets *fn-stmt-max-payload-octets*))
      (fn-stmt-error :limit)
    (let ((items (fn-stmt-decode-items *fn-pol-max-policy-items* octets)))
      (if (not (fn-stmt-okp items))
          items
        (fn-pol-policy-of-items (fn-stmt-value items))))))

; The policy a statement carries, or NIL.
(defun fn-pol-statement-policy (s)
  (declare (xargs :guard (fn-stmt-p s)))
  (let ((r (fn-pol-policy-decode-exact (fn-stmt-payload s))))
    (if (and (fn-stmt-okp r) (fn-pol-policy-p (fn-stmt-value r)))
        (fn-stmt-value r)
      nil)))

(defthm fn-pol-statement-policy-is-policy
  (implies (fn-pol-statement-policy s)
           (fn-pol-policy-p (fn-pol-statement-policy s)))
  :hints (("Goal" :in-theory (disable fn-pol-policy-decode-exact
                                      fn-pol-policy-p))))

; -----------------------------------------------------------------------------
; Candidates: the authority's verified policy statements for a group

(defun fn-pol-candidatep (s keyring group authority)
  (declare (xargs :guard (fn-prin-keyringp keyring)))
  (and (fn-stmt-p s)
       (equal (fn-stmt-kind s) :policy)
       (equal (fn-stmt-creator s) authority)
       (fn-prin-verifiedp s keyring)
       (let ((p (fn-pol-statement-policy s)))
         (and (consp p)
              (equal (fn-pol-policy-group p) group)))))

(defun fn-pol-candidates (lace keyring group authority)
  (declare (xargs :guard (and (fn-lace-p lace) (fn-prin-keyringp keyring))))
  (if (consp lace)
      (if (fn-pol-candidatep (car lace) keyring group authority)
          (cons (car lace)
                (fn-pol-candidates (cdr lace) keyring group authority))
        (fn-pol-candidates (cdr lace) keyring group authority))
    nil))

(defun fn-pol-candidate-listp (xs keyring group authority)
  (declare (xargs :guard (fn-prin-keyringp keyring)))
  (if (consp xs)
      (and (fn-pol-candidatep (car xs) keyring group authority)
           (fn-pol-candidate-listp (cdr xs) keyring group authority))
    (null xs)))

; Strict lexicographic order on (incarnation, sequence).  The fields are
; naturals for every statement; `nfix` makes the order total in the logic so
; the maximality theorem needs no well-formedness premise.
(defun fn-pol-slot-lessp (a b)
  (declare (xargs :guard (and (fn-stmt-p a) (fn-stmt-p b))))
  (let ((ia (nfix (fn-stmt-incarnation a)))
        (ib (nfix (fn-stmt-incarnation b)))
        (sa (nfix (fn-stmt-sequence a)))
        (sb (nfix (fn-stmt-sequence b))))
    (or (< ia ib)
        (and (equal ia ib) (< sa sb)))))

(defun fn-pol-latest (cands)
  (declare (xargs :guard (fn-lace-p cands) :verify-guards nil))
  (if (consp cands)
      (let ((rest (fn-pol-latest (cdr cands))))
        (if (and (consp rest) (fn-pol-slot-lessp (car cands) rest))
            rest
          (car cands)))
    nil))

(defthm fn-pol-latest-is-stmt
  (implies (and (fn-lace-p cands) (consp cands))
           (fn-stmt-p (fn-pol-latest cands))))

(defthm fn-pol-latest-is-consp-or-nil
  (implies (fn-lace-p cands)
           (iff (consp (fn-pol-latest cands))
                (consp cands))))

(verify-guards fn-pol-latest)

(defun fn-pol-same-slot-conflictp (s cands)
  (declare (xargs :guard (and (fn-stmt-p s) (fn-lace-p cands))))
  (if (consp cands)
      (or (and (not (equal (car cands) s))
               (fn-lace-same-slotp (car cands) s))
          (fn-pol-same-slot-conflictp s (cdr cands)))
    nil))

(defthm fn-pol-candidates-are-lace
  (implies (fn-lace-p lace)
           (fn-lace-p (fn-pol-candidates lace keyring group authority)))
  :hints (("Goal" :in-theory (disable fn-pol-candidatep fn-stmt-p))))

(defthm fn-pol-latest-is-member-or-nil
  (implies (consp cands)
           (member-equal (fn-pol-latest cands) cands)))

; The policy in force: the latest candidate, unless the authority has two
; distinct candidates at that slot.
(defun fn-pol-current (lace keyring group authority)
  (declare (xargs :guard (and (fn-lace-p lace) (fn-prin-keyringp keyring))))
  (let* ((cands (fn-pol-candidates lace keyring group authority))
         (latest (fn-pol-latest cands)))
    (if (and (consp latest)
             (not (fn-pol-same-slot-conflictp latest cands)))
        latest
      nil)))

; -----------------------------------------------------------------------------
; Authorization

(defun fn-pol-authorized-set (p)
  (declare (xargs :guard (fn-stmt-p p)))
  (let ((policy (fn-pol-statement-policy p)))
    (cons (fn-stmt-creator p)
          (if (consp policy) (fn-pol-policy-members policy) nil))))

(defthm fn-pol-authorized-set-is-true-list
  (true-listp (fn-pol-authorized-set p))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pol-policy-p)
                           (fn-pol-policy-decode-exact fn-stmt-p
                            fn-stmt-creator fn-stmt-payload)))))

(defthm fn-pol-current-is-stmt-or-nil
  (implies (fn-lace-p lace)
           (or (null (fn-pol-current lace keyring group authority))
               (fn-stmt-p (fn-pol-current lace keyring group authority))))
  :rule-classes nil)

(defun fn-pol-authorizedp (lace keyring group authority principal action)
  (declare (xargs :guard (and (fn-lace-p lace) (fn-prin-keyringp keyring))
                  :guard-hints (("Goal" :use fn-pol-current-is-stmt-or-nil
                                 :do-not-induct t
                                 :in-theory (disable fn-pol-current
                                                     fn-pol-authorized-set
                                                     fn-pol-statement-policy
                                                     fn-pol-policy-decode-exact
                                                     fn-pol-candidates
                                                     fn-pol-latest
                                                     fn-pol-same-slot-conflictp
                                                     fn-stmt-p fn-stmt-id
                                                     fn-stmt-creator)))))
  (cond ((equal action :policy)
         (equal principal authority))
        ((equal action :post)
         (let ((cur (fn-pol-current lace keyring group authority)))
           (and (consp cur)
                (if (member-equal principal (fn-pol-authorized-set cur))
                    t nil))))
        (t nil)))

; Admission of a cross-post `s` to `group`: a verified :article by a
; principal the policy in force authorizes.
(defun fn-pol-admitp (lace keyring group authority s)
  (declare (xargs :guard (and (fn-lace-p lace) (fn-prin-keyringp keyring))))
  (and (fn-stmt-p s)
       (equal (fn-stmt-kind s) :article)
       (fn-prin-verifiedp s keyring)
       (fn-pol-authorizedp lace keyring group authority
                           (fn-stmt-creator s) :post)))

; -----------------------------------------------------------------------------
; The policy term and receipts

(defun fn-pol-evidence (keyring authority s)
  (declare (xargs :guard (and (fn-prin-keyringp keyring) (fn-stmt-p s))
                  :guard-hints
                  (("Goal" :do-not-induct t
                    :use ((:instance fn-stmt-encoding-bound))
                    :in-theory (disable fn-stmt-p fn-stmt-items
                                        fn-stmt-encode-items-of-cons fn-stmt-encode-items-of-atom fn-stmt-encode-items-when-consp
                                        fn-stmt-encoding-bound
                                        fn-prin-key-for fn-stmt-creator
                                        fn-cbor-octet-listp)))))
  (let ((ak (fn-prin-key-for authority keyring))
        (ck (fn-prin-key-for (fn-stmt-creator s) keyring)))
    (if (and (fn-sig-public-key-p ak) (fn-sig-public-key-p ck))
        (fn-stmt-encode-items (list (cons :bytes ak)
                                    (cons :bytes ck)
                                    (cons :bytes (fn-stmt-encode s))))
      nil)))

; Everything below treats the codec, the seam and the parsed statement as
; opaque: the shapes come from the lemmas above and in statement-invariants.
(local (in-theory (disable fn-stmt-verifiedp fn-prin-verifiedp
                           fn-stmt-encode-items-of-cons fn-stmt-encode-items-of-atom fn-stmt-encode-items-when-consp fn-stmt-decode-items
                           fn-stmt-items fn-stmt-decode-exact
                           fn-cbor-encode fn-cbor-decode
                           fn-digest-tagged fn-digest-tagged-preimage
                           fn-stmt-header-encode fn-stmt-content-id
                           fn-stmt-receipt-encode fn-stmt-receipt-decode-exact
                           fn-stmt-receipt-items fn-stmt-receipt-p
                           fn-pol-current fn-pol-authorizedp fn-pol-admitp
                           fn-pol-candidates fn-pol-latest
                           fn-pol-same-slot-conflictp fn-pol-authorized-set
                           fn-pol-statement-policy fn-pol-policy-decode-exact
                           fn-pol-evidence)))

(defthm fn-pol-evidence-is-octet-list
  (fn-cbor-octet-listp (fn-pol-evidence keyring authority s))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-stmt-encoding-bound))
           :in-theory (e/d (fn-pol-evidence)
                           (fn-stmt-p fn-stmt-items fn-stmt-encode-items-of-cons fn-stmt-encode-items-of-atom fn-stmt-encode-items-when-consp
                            fn-stmt-encoding-bound fn-prin-key-for
                            fn-stmt-creator fn-cbor-octet-listp)))))

(defun fn-pol-evidence-digest (keyring authority s)
  (declare (xargs :guard (and (fn-prin-keyringp keyring) (fn-stmt-p s))))
  (fn-digest-tagged *fn-pol-evidence-tag* (fn-pol-evidence keyring authority s)))

; (policy statement id . evidence digest), or NIL when nothing is in force.
(defun fn-pol-term (lace keyring group authority s)
  (declare (xargs :guard (and (fn-lace-p lace) (fn-prin-keyringp keyring)
                              (fn-stmt-p s))
                  :guard-hints (("Goal" :use fn-pol-current-is-stmt-or-nil
                                 :do-not-induct t
                                 :in-theory (disable fn-pol-current
                                                     fn-pol-authorized-set
                                                     fn-pol-statement-policy
                                                     fn-pol-policy-decode-exact
                                                     fn-pol-candidates
                                                     fn-pol-latest
                                                     fn-pol-same-slot-conflictp
                                                     fn-stmt-p fn-stmt-id
                                                     fn-stmt-creator)))))
  (let ((cur (fn-pol-current lace keyring group authority)))
    (if (consp cur)
        (cons (fn-stmt-id cur) (fn-pol-evidence-digest keyring authority s))
      nil)))

(defun fn-pol-make-receipt (lace keyring group authority s obligation)
  (declare (xargs :guard (and (fn-lace-p lace) (fn-prin-keyringp keyring)
                              (fn-stmt-p s))
                  :guard-hints (("Goal" :use fn-pol-current-is-stmt-or-nil
                                 :do-not-induct t
                                 :in-theory (disable fn-pol-current
                                                     fn-pol-authorized-set
                                                     fn-pol-statement-policy
                                                     fn-pol-policy-decode-exact
                                                     fn-pol-candidates
                                                     fn-pol-latest
                                                     fn-pol-same-slot-conflictp
                                                     fn-stmt-p fn-stmt-id
                                                     fn-stmt-creator)))))
  (if (fn-pol-admitp lace keyring group authority s)
      (let ((term (fn-pol-term lace keyring group authority s)))
        (fn-stmt-make-receipt (fn-stmt-id s) obligation (car term) (cdr term)))
    nil))

; Re-resolve a receipt's term against a lace: the policy statement it names
; must be present and must be a verified policy of `authority` for `group`.
(defun fn-pol-receipt-groundedp (receipt lace keyring group authority)
  (declare (xargs :guard (and (fn-lace-p lace) (fn-prin-keyringp keyring)
                              (fn-stmt-receipt-p receipt))
                  :guard-hints (("Goal" :do-not-induct t
                                 :in-theory (enable fn-stmt-receipt-p)))))
  (let ((p (fn-lace-lookup lace (fn-stmt-receipt-policy-id receipt))))
    (and (consp p)
         (fn-pol-candidatep p keyring group authority))))

; A receipt statement: the receiver principal signs the receipt payload.
(defun fn-pol-sign-receipt (sk receiver incarnation sequence preds receipt)
  (declare (xargs :guard (fn-stmt-receipt-p receipt)
                  :guard-hints (("Goal" :do-not-induct t
                                 :use ((:instance fn-stmt-receipt-items-are-items
                                                  (r receipt)))
                                 :in-theory (e/d (fn-stmt-receipt-encode)
                                                 (fn-stmt-receipt-p
                                                  fn-stmt-receipt-items
                                                  fn-stmt-encode-items-of-cons fn-stmt-encode-items-of-atom fn-stmt-encode-items-when-consp
                                                  fn-stmt-receipt-items-are-items))))))
  (fn-stmt-sign sk receiver incarnation sequence preds :receipt
                (fn-stmt-receipt-encode receipt)))

; Statements no member of which is a verified statement by `authority`:
; the delta an adversary outside the authority can produce.
(defun fn-pol-delta-without-authority-p (delta keyring authority)
  (declare (xargs :guard (fn-prin-keyringp keyring)))
  (if (consp delta)
      (and (not (and (fn-stmt-p (car delta))
                     (equal (fn-stmt-creator (car delta)) authority)
                     (fn-prin-verifiedp (car delta) keyring)))
           (fn-pol-delta-without-authority-p (cdr delta) keyring authority))
    t))

; -----------------------------------------------------------------------------
; Record lemmas (docs/proof-style.md section 1).  Accessor of constructor,
; one per field, so nothing above this book opens a record.

(defthm fn-pol-policy-group-of-fn-pol-make-policy
  (equal (fn-pol-policy-group (fn-pol-make-policy group members terms))
         group))
(defthm fn-pol-policy-members-of-fn-pol-make-policy
  (equal (fn-pol-policy-members (fn-pol-make-policy group members terms))
         members))
(defthm fn-pol-policy-terms-of-fn-pol-make-policy
  (equal (fn-pol-policy-terms (fn-pol-make-policy group members terms))
         terms))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2).
;
; The policy record, the codec, resolution of the policy in force and
; receipt construction are withdrawn; the candidate and conflict scans stay.
;
; Only the `:definition' rune is withdrawn, so type prescriptions and
; executable counterparts still decide ground terms.  A book inside this
; cluster that must open one of these enables `fn-pol-internals' locally.

; The `true-listp'/`consp' backchaining rules below are withdrawn with the
; definitions: an includer that inherits them pays for them on every goal
; shaped like a list (docs/proof-style.md section 8).

(deftheory fn-pol-internals
  '(
    (:d fn-pol-namep)
    (:d fn-pol-termsp)
    (:d fn-pol-make-policy)
    (:d fn-pol-policy-group)
    (:d fn-pol-policy-members)
    (:d fn-pol-policy-terms)
    (:d fn-pol-policy-p)
    (:d fn-pol-policy-items)
    (:d fn-pol-policy-of-items)
    (:d fn-pol-policy-encode)
    (:d fn-pol-policy-decode-exact)
    (:d fn-pol-statement-policy)
    (:d fn-pol-candidatep)
    (:d fn-pol-slot-lessp)
    (:d fn-pol-current)
    (:d fn-pol-authorized-set)
    (:d fn-pol-authorizedp)
    (:d fn-pol-admitp)
    (:d fn-pol-evidence)
    (:d fn-pol-evidence-digest)
    (:d fn-pol-term)
    (:d fn-pol-make-receipt)
    (:d fn-pol-receipt-groundedp)
    (:d fn-pol-sign-receipt)
    fn-pol-authorized-set-is-true-list))

(in-theory (disable fn-pol-internals))
