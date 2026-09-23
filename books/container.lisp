; fn C2-05: a portable object container and its validation-to-acceptance
; composition.
;
; A container is `(version articles unknowns)`.  An article is
; `(msgid content-id octets dependencies)`: the Message-ID as a string, the
; declared content identity in the `fn-id-subject` grammar, the exact source
; octets, and the content identities it depends on.  An unknown is
; `(tag octets)`: an object this profile does not interpret.  Under ENC-004 it
; is carried inside its size bound and never consulted; no theorem or
; decision below reads a tag or an unknown's octets.
;
; Validation of one article, all of it before anything is allocated:
;   shape and sizes against the profile (`fn-ct-article-shapep`);
;   identity: the declared content id equals `fn-id-subject` of the digest of
;     the article's subject preimage (`fn-ct-identity-okp` with the host's digest;
;     `fn-ct-identity-spec-okp` against the constrained `fn-frame-digest`, the
;     two agree when the digest is the constrained one);
;   dependencies: each resolves in the local store (an input set of content
;     ids) or to a sibling in the container whose own identity validates and
;     whose dependencies resolve in turn, with a fuel of one step per article
;     so that a cycle exhausts the fuel and never validates.
;
; Acceptance of one validated article is exactly
;   (fn-node-complete (fn-node-prepare s generation msgid octets groups
;                                      obligation-id subject evidence charge)
;                     (fn-state-next-txid (fn-node-acceptance s))
;                     generation completion)
; with subject the content id, obligation-id `fn-id-obligation` of the host's
; obligation digest, and charge `fn-charge-for-payload`.  The receipt
; `(:accepted msgid content-id obligation-id)` is produced only when the
; article validated and the completion was `:durable`; every other path
; returns the input node state or the node's own refusal, and no receipt.
; Articles of one container are published one at a time by `fn-ct-publish-list`;
; an article that fails validation is skipped with the state its siblings see
; unchanged.  Two articles with one Message-ID and different content ids are
; returned as conflict evidence (OBJ-004); the node itself refuses the second.
;
; Not here: a byte grammar for the container (D08/D15; `specs/container.md`
; proposes one), signatures, authorization, and the dependency list as part
; of the identified bytes (it is container metadata in this profile, which
; `specs/container.md` names as a limitation).

(in-package "ACL2")
; `node-invariants`, not `node`: `fn-node-prepare` and `fn-node-complete` now
; carry `(fn-node-statep s)` as their guard (BOARD, 2026-09-19 core), so the
; caller discharges it from the preservation keystones and never re-checks the
; recognizer (docs/proof-style.md §4).
(include-book "node-invariants")
(include-book "identity")
(include-book "records")
(local (include-book "arithmetic/top" :dir :system))

; The core, identity, record and frame clusters withdraw their vocabularies at
; their export theories.  This book opens exactly what its own guard proofs
; need, and only locally.
(local (in-theory (enable fn-id-definitions fn-record-guard-vocabulary)))

(defconst *fn-ct-version* 1)

; -----------------------------------------------------------------------------
; Profile: (max-articles max-article-octets max-dependencies max-unknowns
;           max-unknown-octets)

(defun fn-ct-max-articles (p) (declare (xargs :guard t)) (fn-frame-item 0 p))
(defun fn-ct-max-article-octets (p)
  (declare (xargs :guard t)) (fn-frame-item 1 p))
(defun fn-ct-max-dependencies (p)
  (declare (xargs :guard t)) (fn-frame-item 2 p))
(defun fn-ct-max-unknowns (p) (declare (xargs :guard t)) (fn-frame-item 3 p))
(defun fn-ct-max-unknown-octets (p)
  (declare (xargs :guard t)) (fn-frame-item 4 p))

(defun fn-ct-make-profile (max-articles max-article-octets max-dependencies
                                        max-unknowns max-unknown-octets)
  (declare (xargs :guard t))
  (list max-articles max-article-octets max-dependencies max-unknowns
        max-unknown-octets))

(defun fn-ct-profilep (p)
  (declare (xargs :guard t))
  (and (true-listp p)
       (equal (len p) 5)
       (natp (fn-ct-max-articles p))
       (natp (fn-ct-max-article-octets p))
       (natp (fn-ct-max-dependencies p))
       (natp (fn-ct-max-unknowns p))
       (natp (fn-ct-max-unknown-octets p))))

; The profile recognizer is a carried invariant (docs/proof-style.md §4): it
; is checked once by the caller and every guard proof below discharges it
; from its own hypothesis.  Opening it destructured `profile` into six
; variables inside the guard conjecture of `fn-ct-deps-resolvep` and left a
; goal (`(not (natp profile9))`) with no induction scheme (measured here).
; What opacity takes away it exports back as forward-chaining, never rewrite
; (docs/proof-style.md §1): the five field facts the guard proofs below used
; to get by opening the recognizer.  (Measured after that: the conjecture
; never needed the profile at all.  Its two checkpoints were `(integerp fuel)`
; and `(<= 0 fuel)`, the guard of `zp` on `fuel`; `(natp fuel)` in the guard
; of the three fuel-carrying validators closes it in 0.03 s.)
(defthm fn-ct-profilep-forward-fields
  (implies (fn-ct-profilep p)
           (and (true-listp p)
                (natp (fn-ct-max-articles p))
                (natp (fn-ct-max-article-octets p))
                (natp (fn-ct-max-dependencies p))
                (natp (fn-ct-max-unknowns p))
                (natp (fn-ct-max-unknown-octets p))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-ct-profilep))))

; The accessors go opaque with it, so the guard goals and the exported facts
; stay in the same vocabulary (docs/proof-style.md §1): with the readers open
; the forward-chained `(natp (fn-ct-max-dependencies p))` did not meet the
; goal's `(rationalp (fn-frame-item 2 profile))`.
(in-theory (disable fn-ct-profilep
                    (:d fn-ct-max-articles) (:d fn-ct-max-article-octets)
                    (:d fn-ct-max-dependencies) (:d fn-ct-max-unknowns)
                    (:d fn-ct-max-unknown-octets)))

; -----------------------------------------------------------------------------
; Articles, unknowns, containers

(defun fn-ct-article-msgid (a) (declare (xargs :guard t)) (fn-frame-item 0 a))
(defun fn-ct-article-content-id (a)
  (declare (xargs :guard t)) (fn-frame-item 1 a))
(defun fn-ct-article-octets (a) (declare (xargs :guard t)) (fn-frame-item 2 a))
(defun fn-ct-article-deps (a) (declare (xargs :guard t)) (fn-frame-item 3 a))

(defun fn-ct-make-article (msgid content-id octets deps)
  (declare (xargs :guard t))
  (list msgid content-id octets deps))

(defun fn-ct-id-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-id-subjectp (car xs)) (fn-ct-id-listp (cdr xs)))
    (null xs)))

(defun fn-ct-article-shapep (a profile)
  (declare (xargs :guard (fn-ct-profilep profile)))
  (and (true-listp a)
       (equal (len a) 4)
       (stringp (fn-ct-article-msgid a))
       (fn-id-subjectp (fn-ct-article-content-id a))
       (fn-cbor-octet-listp (fn-ct-article-octets a))
       (<= (len (fn-ct-article-octets a)) (fn-ct-max-article-octets profile))
       (fn-ct-id-listp (fn-ct-article-deps a))
       (<= (len (fn-ct-article-deps a)) (fn-ct-max-dependencies profile))))

(defun fn-ct-article-list-shapep (as profile)
  (declare (xargs :guard (fn-ct-profilep profile)))
  (if (consp as)
      (and (fn-ct-article-shapep (car as) profile)
           (fn-ct-article-list-shapep (cdr as) profile))
    (null as)))

(defun fn-ct-unknown-tag (u) (declare (xargs :guard t)) (fn-frame-item 0 u))
(defun fn-ct-unknown-octets (u) (declare (xargs :guard t)) (fn-frame-item 1 u))

; Bounded, not interpreted: the tag is any natural and the octets any octets
; within the profile's bound.
(defun fn-ct-unknown-okp (u profile)
  (declare (xargs :guard (fn-ct-profilep profile)))
  (and (true-listp u)
       (equal (len u) 2)
       (natp (fn-ct-unknown-tag u))
       (fn-cbor-octet-listp (fn-ct-unknown-octets u))
       (<= (len (fn-ct-unknown-octets u)) (fn-ct-max-unknown-octets profile))))

(defun fn-ct-unknown-listp (us profile)
  (declare (xargs :guard (fn-ct-profilep profile)))
  (if (consp us)
      (and (fn-ct-unknown-okp (car us) profile)
           (fn-ct-unknown-listp (cdr us) profile))
    (null us)))

(defun fn-ct-unknowns-okp (us profile)
  (declare (xargs :guard (fn-ct-profilep profile)))
  (and (fn-ct-unknown-listp us profile)
       (<= (len us) (fn-ct-max-unknowns profile))))

(defun fn-ct-version (c) (declare (xargs :guard t)) (fn-frame-item 0 c))
(defun fn-ct-articles (c) (declare (xargs :guard t)) (fn-frame-item 1 c))
(defun fn-ct-unknowns (c) (declare (xargs :guard t)) (fn-frame-item 2 c))

(defun fn-ct-make-container (version articles unknowns)
  (declare (xargs :guard t))
  (list version articles unknowns))

(defun fn-ct-containerp (c profile)
  (declare (xargs :guard (fn-ct-profilep profile)))
  (and (true-listp c)
       (equal (len c) 3)
       (equal (fn-ct-version c) *fn-ct-version*)
       (true-listp (fn-ct-articles c))
       (<= (len (fn-ct-articles c)) (fn-ct-max-articles profile))
       (fn-ct-unknowns-okp (fn-ct-unknowns c) profile)))

; -----------------------------------------------------------------------------
; Identity

(defun fn-ct-identity-okp (a digest)
  ; The executable check: `digest` is the host's SHA-256 of the article's
  ; subject preimage (`fn-id-subject-preimage` of the octets).
  (declare (xargs :guard t))
  (and (fn-id-digestp digest)
       (equal (fn-ct-article-content-id a) (fn-id-subject digest))))

(defun fn-ct-identity-spec-okp (a)
  ; The same check against A-CRYPTO.  Not executable.
  (declare (xargs :guard (fn-cbor-octet-listp (fn-ct-article-octets a))
                  :verify-guards nil))
  (equal (fn-ct-article-content-id a)
         (fn-id-subject-of-payload (fn-ct-article-octets a))))

; -----------------------------------------------------------------------------
; Dependencies.  `articles` and `digests` are the container's articles and,
; in the same order, the host's digest of each one's subject preimage.

; The first sibling that declares `content-id` and whose identity checks.  A
; sibling that merely claims the identity provides nothing.
(defun fn-ct-find-provider (content-id articles digests)
  (declare (xargs :guard t))
  (if (and (consp articles) (consp digests))
      (if (and (equal (fn-ct-article-content-id (car articles)) content-id)
               (fn-ct-identity-okp (car articles) (car digests)))
          (cons (car articles) (car digests))
        (fn-ct-find-provider content-id (cdr articles) (cdr digests)))
    nil))

(defun fn-ct-deps-resolvep (deps articles digests store profile fuel)
  (declare (xargs :guard (and (fn-ct-profilep profile) (true-listp store)
                              (natp fuel))
                  :measure (make-ord 1 (+ 1 (nfix fuel)) (len deps))))
  (if (consp deps)
      (and (or (member-equal (car deps) store)
               (and (not (zp fuel))
                    (let ((found (fn-ct-find-provider (car deps) articles
                                                      digests)))
                      (and found
                           (fn-ct-article-shapep (car found) profile)
                           (fn-ct-deps-resolvep
                            (fn-ct-article-deps (car found))
                            articles digests store profile (- fuel 1))))))
           (fn-ct-deps-resolvep (cdr deps) articles digests store profile
                                fuel))
    t))

; One dependency, for stating membership facts.
(defun fn-ct-dep-resolvep (dep articles digests store profile fuel)
  (declare (xargs :guard (and (fn-ct-profilep profile) (true-listp store)
                              (natp fuel))))
  (or (member-equal dep store)
      (and (not (zp fuel))
           (let ((found (fn-ct-find-provider dep articles digests)))
             (and found
                  (fn-ct-article-shapep (car found) profile)
                  (fn-ct-deps-resolvep (fn-ct-article-deps (car found))
                                       articles digests store profile
                                       (- fuel 1)))))))

; The whole validation of one article.  Nothing is allocated here; the node
; is not even an argument.
(defun fn-ct-article-validp (a digest articles digests store profile fuel)
  (declare (xargs :guard (and (fn-ct-profilep profile) (true-listp store)
                              (natp fuel))))
  (and (fn-ct-article-shapep a profile)
       (fn-ct-identity-okp a digest)
       (fn-ct-deps-resolvep (fn-ct-article-deps a) articles digests store
                            profile fuel)))

; -----------------------------------------------------------------------------
; Conflict evidence (OBJ-004): every article whose Message-ID another article
; of the container also carries with a different content id.

(defun fn-ct-has-rivalp (a articles)
  (declare (xargs :guard t))
  (if (consp articles)
      (or (and (equal (fn-ct-article-msgid (car articles))
                      (fn-ct-article-msgid a))
               (not (equal (fn-ct-article-content-id (car articles))
                           (fn-ct-article-content-id a))))
          (fn-ct-has-rivalp a (cdr articles)))
    nil))

(defun fn-ct-conflict-evidence (candidates articles)
  (declare (xargs :guard t))
  (if (consp candidates)
      (if (fn-ct-has-rivalp (car candidates) articles)
          (cons (car candidates)
                (fn-ct-conflict-evidence (cdr candidates) articles))
        (fn-ct-conflict-evidence (cdr candidates) articles))
    nil))

; -----------------------------------------------------------------------------
; Acceptance composition.  Result: (status state receipt).

(defun fn-ct-result-status (x) (declare (xargs :guard t)) (fn-frame-item 0 x))
(defun fn-ct-result-state (x) (declare (xargs :guard t)) (fn-frame-item 1 x))
(defun fn-ct-result-receipt (x) (declare (xargs :guard t)) (fn-frame-item 2 x))

(defun fn-ct-receiptp (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 4)
       (equal (fn-frame-item 0 x) :accepted)))

(defun fn-ct-subject-string (a)
  (declare (xargs :guard t))
  (fn-record-octets-string (fn-ct-article-content-id a)))

(defun fn-ct-obligation-string (obligation-digest)
  (declare (xargs :guard (fn-id-digestp obligation-digest)))
  (fn-record-octets-string (fn-id-obligation obligation-digest)))

(defun fn-ct-charge (a)
  (declare (xargs :guard t))
  (fn-charge-for-payload (len (fn-ct-article-octets a))))

; The exact composition.  `completion` is the host's storage observation for
; this transaction, as it is for `fn-node-complete`.
(defun fn-ct-publish-article (s a digest articles digests store profile
                                generation groups evidence obligation-digest
                                completion stamp)
  (declare (xargs :guard (and (fn-node-statep s) (fn-ct-profilep profile)
                              (true-listp store))))
  (if (not (fn-ct-article-validp a digest articles digests store profile
                                 (len articles)))
      (list :invalid s nil)
    (if (not (fn-id-digestp obligation-digest))
        (list :invalid s nil)
      (let* ((msgid (fn-ct-article-msgid a))
             (subject (fn-ct-subject-string a))
             (obligation-id (fn-ct-obligation-string obligation-digest))
             (txid (fn-state-next-txid (fn-node-acceptance s)))
             (prepared (fn-node-prepare s generation msgid
                                        (fn-ct-article-octets a) groups
                                        obligation-id subject evidence
                                        (fn-ct-charge a) stamp)))
        (if (equal prepared s)
            (list :refused s nil)
          (let ((done (fn-node-complete prepared txid generation completion)))
            (if (equal completion :durable)
                (list :accepted done
                      (list :accepted msgid (fn-ct-article-content-id a)
                            obligation-id))
              (list :not-durable done nil))))))))

; The node invariant the fold carries (docs/proof-style.md §4): publication of
; one article answers with a node state whenever it was given one, so
; `fn-ct-publish-list` never re-runs `fn-node-statep` on its own recursion.
(defthm fn-ct-publish-article-preserves-node-statep
  (implies (fn-node-statep s)
           (fn-node-statep
            (fn-ct-result-state
             (fn-ct-publish-article s a digest articles digests store profile
                                    generation groups evidence
                                    obligation-digest completion stamp))))
  :hints (("Goal" :in-theory (e/d (fn-ct-publish-article fn-ct-result-state
                                   fn-frame-item)
                                  (fn-ct-article-validp fn-node-prepare
                                   fn-node-complete fn-node-statep
                                   fn-ct-subject-string fn-ct-obligation-string
                                   fn-ct-charge fn-id-digestp)))))

; Every article of a container in order.  Each article carries its own host
; digest, obligation digest and completion observation, in parallel lists.
; Result: (state outcomes) with one (msgid status receipt) per article.
(defun fn-ct-publish-list (s candidates digests obligation-digests completions
                             articles all-digests store profile generation
                             groups evidence stamp)
  ; The measure is named: ACL2's first guess is over the node state, and
  ; refuting it opens the acceptance and retention kernels inside the
  ; termination proof.
  (declare (xargs :guard (and (fn-node-statep s) (fn-ct-profilep profile)
                              (true-listp store))
                  :measure (acl2-count candidates)))
  (if (consp candidates)
      (let* ((one (fn-ct-publish-article
                   s (car candidates)
                   (if (consp digests) (car digests) nil)
                   articles all-digests store profile generation groups
                   evidence
                   (if (consp obligation-digests) (car obligation-digests) nil)
                   (if (consp completions) (car completions) nil) stamp))
             (rest (fn-ct-publish-list
                    (fn-ct-result-state one) (cdr candidates)
                    (if (consp digests) (cdr digests) nil)
                    (if (consp obligation-digests) (cdr obligation-digests) nil)
                    (if (consp completions) (cdr completions) nil)
                    articles all-digests store profile generation groups
                    evidence stamp)))
        (list (fn-frame-item 0 rest)
              (cons (list (fn-ct-article-msgid (car candidates))
                          (fn-ct-result-status one)
                          (fn-ct-result-receipt one))
                    (fn-frame-item 1 rest))))
    (list s nil)))

; The container entry point.  Result: (:refused reason) for a container
; outside the profile, else (:ok state outcomes conflicts).
(defun fn-ct-publish-container (s c digests obligation-digests completions
                                  store profile generation groups evidence stamp)
  (declare (xargs :guard (and (fn-node-statep s) (fn-ct-profilep profile)
                              (true-listp store))))
  (if (not (fn-ct-containerp c profile))
      (list :refused :container)
    (let ((run (fn-ct-publish-list s (fn-ct-articles c) digests
                                   obligation-digests completions
                                   (fn-ct-articles c) digests store profile
                                   generation groups evidence stamp)))
      (list :ok (fn-frame-item 0 run) (fn-frame-item 1 run)
            (fn-ct-conflict-evidence (fn-ct-articles c) (fn-ct-articles c))))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md §2).  What leaves this book enabled: the
; list-recursive vocabulary the proofs induct on (`fn-ct-id-listp`,
; `fn-ct-article-list-shapep`, `fn-ct-unknown-listp`, `fn-ct-find-provider`,
; `fn-ct-has-rivalp`, `fn-ct-conflict-evidence`) and the node-invariant
; keystone above.  The accessors lose their definition rune only; the
; recognizers, the validation predicates and the three publication
; transitions are withdrawn under one name.

(in-theory (disable (:d fn-ct-max-articles) (:d fn-ct-max-article-octets)
                    (:d fn-ct-max-dependencies) (:d fn-ct-max-unknowns)
                    (:d fn-ct-max-unknown-octets) (:d fn-ct-make-profile)
                    (:d fn-ct-article-msgid) (:d fn-ct-article-content-id)
                    (:d fn-ct-article-octets) (:d fn-ct-article-deps)
                    (:d fn-ct-make-article) (:d fn-ct-unknown-tag)
                    (:d fn-ct-unknown-octets) (:d fn-ct-version)
                    (:d fn-ct-articles) (:d fn-ct-unknowns)
                    (:d fn-ct-make-container) (:d fn-ct-result-status)
                    (:d fn-ct-result-state) (:d fn-ct-result-receipt)
                    (:d fn-ct-subject-string) (:d fn-ct-obligation-string)
                    (:d fn-ct-charge)))

(deftheory fn-ct-vocabulary
  '(fn-ct-profilep fn-ct-article-shapep fn-ct-unknown-okp fn-ct-unknowns-okp
    fn-ct-containerp fn-ct-receiptp fn-ct-identity-okp
    fn-ct-identity-spec-okp fn-ct-deps-resolvep fn-ct-dep-resolvep
    fn-ct-article-validp fn-ct-publish-article fn-ct-publish-list
    fn-ct-publish-container))

(in-theory (disable fn-ct-vocabulary))
