; fn C2-05: what the container composition proves.
;
; Keystones (witness and per-hypothesis teeth in tests/acl2/container-tests.lisp):
;   fn-ct-identity-okp-is-spec-okp             host digest check = A-CRYPTO statement
;   fn-ct-receipt-implies-validated            no receipt shape without validation
;   fn-ct-accepted-is-complete-of-prepare      the exact node composition
;   fn-ct-invalid-article-leaves-node-unchanged
;   fn-ct-store-resolved-verdict-ignores-siblings
;   fn-ct-self-dependency-never-validates      a cycle exhausts the fuel
;   fn-ct-conflict-is-evidence                 OBJ-004
;   fn-ct-invalid-head-does-not-block-siblings
;   fn-ct-accepted-article-is-in-the-node      the receipt names a published article
;   fn-ct-unknowns-are-never-consulted         ENC-004

(in-package "ACL2")
(include-book "container")
(include-book "node-invariants")
(local (include-book "arithmetic/top" :dir :system))

; This book opens the container definitions, the node one layer at a time and
; the identity rule; all three are withdrawn at their export theories (the
; export theory of `books/container.lisp`; BOARD, 2026-09-19 core and
; substrate).  Every enable is local: no includer inherits a definition rune.
(local (in-theory (enable fn-ct-vocabulary fn-id-definitions)))

; -----------------------------------------------------------------------------
; Identity: the executable check with the constrained digest is the
; specification.

; `digest` is the host's SHA-256 of the article's subject preimage
; (`fn-id-subject-preimage` of the octets), which is what `fn-id-subject`
; renders and what `fn-id-subject-of-payload` hashes (`books/identity.lisp`);
; the hypothesis names that preimage, not the bare octets.
(defthm fn-ct-identity-okp-is-spec-okp
  (implies (equal digest (fn-frame-digest
                          (fn-id-subject-preimage (fn-ct-article-octets a))))
           (equal (fn-ct-identity-okp a digest)
                  (fn-ct-identity-spec-okp a)))
  :hints (("Goal" :in-theory (enable fn-ct-identity-okp fn-ct-identity-spec-okp
                                      fn-id-subject-of-payload fn-id-digestp))))

; -----------------------------------------------------------------------------
; The acceptance composition, from the receipt inward.

(defthm fn-ct-receipt-implies-validated
  (implies (fn-ct-receiptp
            (fn-ct-result-receipt
             (fn-ct-publish-article s a digest articles digests store profile
                                    generation groups evidence
                                    obligation-digest completion)))
           (fn-ct-article-validp a digest articles digests store profile
                                 (len articles)))
  :hints (("Goal" :in-theory (e/d (fn-ct-publish-article fn-ct-result-receipt
                                   fn-ct-receiptp fn-frame-item)
                                  (fn-ct-article-validp fn-node-prepare
                                   fn-node-complete fn-ct-subject-string
                                   fn-ct-obligation-string fn-ct-charge
                                   fn-id-digestp)))))

(defthm fn-ct-accepted-is-complete-of-prepare
  (implies (equal (fn-ct-result-status
                   (fn-ct-publish-article s a digest articles digests store
                                          profile generation groups evidence
                                          obligation-digest completion))
                  :accepted)
           (and (fn-ct-article-validp a digest articles digests store profile
                                      (len articles))
                (equal completion :durable)
                (not (equal (fn-node-prepare
                             s generation (fn-ct-article-msgid a)
                             (fn-ct-article-octets a) groups
                             (fn-ct-obligation-string obligation-digest)
                             (fn-ct-subject-string a) evidence (fn-ct-charge a))
                            s))
                (equal (fn-ct-result-state
                        (fn-ct-publish-article s a digest articles digests
                                               store profile generation groups
                                               evidence obligation-digest
                                               completion))
                       (fn-node-complete
                        (fn-node-prepare
                         s generation (fn-ct-article-msgid a)
                         (fn-ct-article-octets a) groups
                         (fn-ct-obligation-string obligation-digest)
                         (fn-ct-subject-string a) evidence (fn-ct-charge a))
                        (fn-state-next-txid (fn-node-acceptance s))
                        generation :durable))))
  ; A `:use` fact, not a rewrite rule: the conjunct `(equal completion
  ; :durable)` would rewrite a variable, which ACL2 refuses, and the trigger
  ; would carry six free variables.  The statement is the keystone.
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ct-publish-article fn-ct-result-status
                                   fn-ct-result-state fn-frame-item)
                                  (fn-ct-article-validp fn-node-prepare
                                   fn-node-complete fn-ct-subject-string
                                   fn-ct-obligation-string fn-ct-charge
                                   fn-id-digestp)))))

(defthm fn-ct-invalid-article-leaves-node-unchanged
  (implies (not (fn-ct-article-validp a digest articles digests store profile
                                      (len articles)))
           (and (equal (fn-ct-result-status
                        (fn-ct-publish-article s a digest articles digests
                                               store profile generation groups
                                               evidence obligation-digest
                                               completion))
                       :invalid)
                (equal (fn-ct-result-state
                        (fn-ct-publish-article s a digest articles digests
                                               store profile generation groups
                                               evidence obligation-digest
                                               completion))
                       s)
                (equal (fn-ct-result-receipt
                        (fn-ct-publish-article s a digest articles digests
                                               store profile generation groups
                                               evidence obligation-digest
                                               completion))
                       nil)))
  :hints (("Goal" :in-theory (e/d (fn-ct-publish-article fn-ct-result-status
                                   fn-ct-result-state fn-ct-result-receipt
                                   fn-frame-item)
                                  (fn-ct-article-validp fn-node-prepare
                                   fn-node-complete)))))

; -----------------------------------------------------------------------------
; Independence: an article whose dependencies all resolve in the local store
; has the same verdict in any container, so no sibling can block it.

(defun fn-ct-all-in-store (deps store)
  (declare (xargs :guard (true-listp store)))
  (if (consp deps)
      (and (member-equal (car deps) store)
           (fn-ct-all-in-store (cdr deps) store))
    t))

(defthm fn-ct-store-resolved-deps-resolve
  (implies (fn-ct-all-in-store deps store)
           (fn-ct-deps-resolvep deps articles digests store profile fuel))
  :hints (("Goal" :induct (fn-ct-all-in-store deps store)
           :expand ((fn-ct-deps-resolvep deps articles digests store profile
                                         fuel))
           :in-theory (e/d (fn-ct-all-in-store)
                           (fn-ct-find-provider fn-ct-article-shapep)))))

(defthm fn-ct-store-resolved-verdict-ignores-siblings
  (implies (fn-ct-all-in-store (fn-ct-article-deps a) store)
           (equal (fn-ct-article-validp a digest articles digests store
                                        profile fuel)
                  (fn-ct-article-validp a digest nil nil store profile fuel)))
  :hints (("Goal" :in-theory (e/d (fn-ct-article-validp)
                                  (fn-ct-article-shapep fn-ct-identity-okp
                                   fn-ct-deps-resolvep)))))

; -----------------------------------------------------------------------------
; Cycles: the article the container provides for a content id, when it itself
; depends on that id and the local store lacks it, never validates at any
; fuel.  (A provider exists whenever the membership hypothesis holds: the
; dependency list of `(car nil)` is empty.)

(local
 (defthm fn-ct-deps-resolvep-member
   (implies (and (fn-ct-deps-resolvep deps articles digests store profile fuel)
                 (member-equal dep deps))
            (fn-ct-dep-resolvep dep articles digests store profile fuel))
   :hints (("Goal" :induct (member-equal dep deps)
            :expand ((fn-ct-deps-resolvep deps articles digests store profile
                                          fuel))
            :in-theory (e/d (fn-ct-dep-resolvep)
                            (fn-ct-find-provider fn-ct-article-shapep))))))

(local
 (defun fn-ct-fuel-induct (fuel)
   (if (zp fuel) 0 (fn-ct-fuel-induct (- fuel 1)))))

(local
 (defthm fn-ct-provider-self-dependency-never-resolves
   (implies (and (not (member-equal id store))
                 (member-equal id (fn-ct-article-deps
                                   (car (fn-ct-find-provider id articles digests)))))
            (not (fn-ct-deps-resolvep
                  (fn-ct-article-deps (car (fn-ct-find-provider id articles digests)))
                  articles digests store profile fuel)))
   ; ACL2 refuses `:induct` and `:use` on one subgoal; the membership
   ; instance is attached to each case of the fuel induction instead.
   :hints (("Goal" :induct (fn-ct-fuel-induct fuel)
            :in-theory (e/d (fn-ct-dep-resolvep)
                            (fn-ct-find-provider fn-ct-article-shapep
                             fn-ct-deps-resolvep fn-ct-deps-resolvep-member)))
           ("Subgoal *1/2" :use ((:instance fn-ct-deps-resolvep-member
                                  (deps (fn-ct-article-deps
                                         (car (fn-ct-find-provider id articles digests))))
                                  (dep id))))
           ("Subgoal *1/1" :use ((:instance fn-ct-deps-resolvep-member
                                  (deps (fn-ct-article-deps
                                         (car (fn-ct-find-provider id articles digests))))
                                  (dep id)))))))

(defthm fn-ct-self-dependency-never-validates
  (implies (and (not (member-equal id store))
                (member-equal id (fn-ct-article-deps
                                  (car (fn-ct-find-provider id articles digests)))))
           (not (fn-ct-article-validp (car (fn-ct-find-provider id articles digests))
                                      digest articles digests store profile
                                      fuel)))
  :hints (("Goal" :in-theory (e/d (fn-ct-article-validp)
                                  (fn-ct-find-provider fn-ct-article-shapep
                                   fn-ct-deps-resolvep fn-ct-identity-okp)))))

; -----------------------------------------------------------------------------
; OBJ-004: a Message-ID carried with two content ids is returned as evidence.

(local
 (defthm fn-ct-rival-is-found
   (implies (and (member-equal b articles)
                 (equal (fn-ct-article-msgid a) (fn-ct-article-msgid b))
                 (not (equal (fn-ct-article-content-id a)
                             (fn-ct-article-content-id b))))
            (fn-ct-has-rivalp a articles))
   :hints (("Goal" :induct (member-equal b articles)
            :in-theory (disable fn-ct-article-msgid fn-ct-article-content-id)))))

(defthm fn-ct-conflict-is-evidence
  (implies (and (member-equal a candidates)
                (member-equal b articles)
                (equal (fn-ct-article-msgid a) (fn-ct-article-msgid b))
                (not (equal (fn-ct-article-content-id a)
                            (fn-ct-article-content-id b))))
           (member-equal a (fn-ct-conflict-evidence candidates articles)))
  :hints (("Goal" :induct (member-equal a candidates)
           :in-theory (disable fn-ct-has-rivalp fn-ct-article-msgid
                               fn-ct-article-content-id))))

; -----------------------------------------------------------------------------
; The publishing fold: an invalid head is skipped and its siblings see the
; same node state they would have seen without it.

(defthm fn-ct-invalid-head-does-not-block-siblings
  (implies (and (consp candidates)
                (not (fn-ct-article-validp
                      (car candidates) (if (consp digests) (car digests) nil)
                      articles all-digests store profile (len articles))))
           (equal (fn-frame-item
                   0 (fn-ct-publish-list s candidates digests obligation-digests
                                         completions articles all-digests store
                                         profile generation groups evidence))
                  (fn-frame-item
                   0 (fn-ct-publish-list
                      s (cdr candidates)
                      (if (consp digests) (cdr digests) nil)
                      (if (consp obligation-digests) (cdr obligation-digests) nil)
                      (if (consp completions) (cdr completions) nil)
                      articles all-digests store profile generation groups
                      evidence))))
  :hints (("Goal" :do-not-induct t
           :expand ((fn-ct-publish-list s candidates digests obligation-digests
                                        completions articles all-digests store
                                        profile generation groups evidence))
           :in-theory (e/d (fn-frame-item)
                           (fn-ct-publish-article fn-ct-article-validp
                            fn-ct-publish-list)))))

; -----------------------------------------------------------------------------
; The receipt names an article the node published.  These lemmas open the
; node one layer at a time and never revalidate a whole state.

(local
 (defthm fn-ct-node-statep-acceptance
   (implies (fn-node-statep s)
            (fn-statep (fn-node-acceptance s)))
   :hints (("Goal" :in-theory (enable fn-node-statep)))))

(local
 (defthm fn-ct-prepare-on-non-state-by-definition
   (implies (not (fn-node-statep s))
            (equal (fn-node-prepare s g m p gr o sub e c) s))
   :hints (("Goal" :in-theory (enable fn-node-prepare)))))

(local
 (defthm fn-ct-prepare-changed-means-acceptance-changed
   (implies (not (equal (fn-node-prepare s g m p gr o sub e c) s))
            (not (equal (fn-accept-prepare (fn-node-acceptance s) g m p gr)
                        (fn-node-acceptance s))))
   :hints (("Goal" :in-theory (e/d (fn-node-prepare)
                                   (fn-node-statep fn-retain-admissiblep
                                    fn-accept-prepare fn-retain-admit
                                    fn-node-make-state fn-node-make-stage))))))

(local
 (defthm fn-ct-prepare-acceptance
   (implies (not (equal (fn-node-prepare s g m p gr o sub e c) s))
            (equal (fn-node-acceptance (fn-node-prepare s g m p gr o sub e c))
                   (fn-accept-prepare (fn-node-acceptance s) g m p gr)))
   :hints (("Goal" :in-theory (e/d (fn-node-prepare fn-node-make-state
                                    fn-node-acceptance)
                                   (fn-node-statep fn-retain-admissiblep
                                    fn-accept-prepare fn-retain-admit
                                    fn-node-make-stage))))))

(local
 (defthm fn-ct-prepare-stage
   (implies (not (equal (fn-node-prepare s g m p gr o sub e c) s))
            (consp (fn-node-stage (fn-node-prepare s g m p gr o sub e c))))
   :hints (("Goal" :in-theory (e/d (fn-node-prepare fn-node-make-state
                                    fn-node-stage fn-node-make-stage)
                                   (fn-node-statep fn-retain-admissiblep
                                    fn-accept-prepare fn-retain-admit))))))

(local
 (defthm fn-ct-accept-prepare-changed
   (implies (not (equal (fn-accept-prepare s g m p gr) s))
            (and (equal (fn-state-fenced (fn-accept-prepare s g m p gr)) nil)
                 (fn-pending-matchesp (fn-state-pending
                                       (fn-accept-prepare s g m p gr))
                                      (fn-state-next-txid s) g)
                 (equal (fn-pending-msgid
                         (fn-state-pending (fn-accept-prepare s g m p gr)))
                        m)))
   :hints (("Goal" :in-theory (e/d (fn-accept-prepare fn-make-state
                                    fn-state-fenced fn-state-pending
                                    fn-state-next-txid fn-make-pending
                                    fn-pending-txid fn-pending-generation
                                    fn-pending-msgid fn-pending-matchesp)
                                   (fn-statep fn-selection-validp fn-acceptedp
                                    fn-allocate-memberships fn-octet-listp))))))

(local
 (defthm fn-ct-durable-complete-installs
   (implies (and (fn-statep s)
                 (equal (fn-state-fenced s) nil)
                 (fn-pending-matchesp (fn-state-pending s) txid g))
            (equal (fn-state-articles (fn-accept-complete s txid g :durable))
                   (cons (fn-article-from-pending (fn-state-pending s))
                         (fn-state-articles s))))
   :hints (("Goal" :in-theory (e/d (fn-accept-complete fn-install-pending
                                    fn-make-state fn-state-articles)
                                   (fn-statep fn-advance-nexts
                                    fn-article-from-pending
                                    fn-pending-matchesp))))))

(local
 (defthm fn-ct-node-durable-complete-acceptance
   (implies (fn-node-pending-matchesp s txid g)
            (equal (fn-node-acceptance (fn-node-complete s txid g :durable))
                   (fn-accept-complete (fn-node-acceptance s) txid g :durable)))
   :hints (("Goal" :in-theory (e/d (fn-node-complete fn-node-make-state
                                    fn-node-acceptance)
                                   (fn-node-pending-matchesp
                                    fn-accept-complete))))))

(local
 (defthm fn-ct-prepared-pending-matches
   (implies (and (fn-node-statep s)
                 (not (equal (fn-node-prepare s g m p gr o sub e c) s)))
            (fn-node-pending-matchesp (fn-node-prepare s g m p gr o sub e c)
                                      (fn-state-next-txid (fn-node-acceptance s))
                                      g))
   :hints (("Goal" :in-theory (e/d (fn-node-pending-matchesp)
                                   (fn-node-prepare fn-node-statep
                                    fn-accept-prepare fn-pending-matchesp))))))

(local
 (defthm fn-ct-article-from-pending-msgid
   (equal (fn-article-msgid (fn-article-from-pending p))
          (fn-pending-msgid p))
   :hints (("Goal" :in-theory (enable fn-article-from-pending fn-make-article
                                       fn-article-msgid)))))

(defthm fn-ct-prepare-then-durable-complete-accepts
  (implies (not (equal (fn-node-prepare s g m p gr o sub e c) s))
           (fn-acceptedp
            m
            (fn-state-articles
             (fn-node-acceptance
              (fn-node-complete (fn-node-prepare s g m p gr o sub e c)
                                (fn-state-next-txid (fn-node-acceptance s))
                                g :durable)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-acceptedp)
                           (fn-node-prepare fn-node-complete fn-node-statep
                            fn-accept-prepare fn-accept-complete fn-statep
                            fn-pending-matchesp fn-node-pending-matchesp
                            fn-article-from-pending))
           :use ((:instance fn-ct-prepare-on-non-state-by-definition)
                 (:instance fn-ct-prepared-pending-matches)
                 (:instance fn-node-prepare-preserves-state
                            (generation g) (msgid m) (payload p) (groups gr)
                            (obligation-id o) (subject sub) (evidence e)
                            (charge c))
                 (:instance fn-ct-node-statep-acceptance
                            (s (fn-node-prepare s g m p gr o sub e c)))
                 (:instance fn-ct-accept-prepare-changed
                            (s (fn-node-acceptance s)))
                 (:instance fn-ct-durable-complete-installs
                            (s (fn-accept-prepare (fn-node-acceptance s) g m p gr))
                            (txid (fn-state-next-txid (fn-node-acceptance s))))))))

; KEYSTONE: an :accepted result names an article the node has published.
(defthm fn-ct-accepted-article-is-in-the-node
  (implies (equal (fn-ct-result-status
                   (fn-ct-publish-article s a digest articles digests store
                                          profile generation groups evidence
                                          obligation-digest completion))
                  :accepted)
           (fn-acceptedp
            (fn-ct-article-msgid a)
            (fn-state-articles
             (fn-node-acceptance
              (fn-ct-result-state
               (fn-ct-publish-article s a digest articles digests store
                                      profile generation groups evidence
                                      obligation-digest completion))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-ct-publish-article fn-node-prepare
                               fn-node-complete fn-acceptedp
                               fn-ct-article-validp)
           :use ((:instance fn-ct-accepted-is-complete-of-prepare)
                 (:instance fn-ct-prepare-then-durable-complete-accepts
                            (g generation) (m (fn-ct-article-msgid a))
                            (p (fn-ct-article-octets a)) (gr groups)
                            (o (fn-ct-obligation-string obligation-digest))
                            (sub (fn-ct-subject-string a)) (e evidence)
                            (c (fn-ct-charge a)))))))

; -----------------------------------------------------------------------------
; ENC-004: unknown objects within the bound are carried and never consulted.

(defthm fn-ct-unknowns-are-never-consulted
  (implies (and (fn-ct-unknowns-okp us profile)
                (fn-ct-unknowns-okp us2 profile))
           (equal (fn-ct-publish-container
                   s (fn-ct-make-container v as us) digests obligation-digests
                   completions store profile generation groups evidence)
                  (fn-ct-publish-container
                   s (fn-ct-make-container v as us2) digests obligation-digests
                   completions store profile generation groups evidence)))
  :hints (("Goal" :in-theory (e/d (fn-ct-publish-container fn-ct-containerp
                                   fn-ct-make-container fn-ct-version
                                   fn-ct-articles fn-ct-unknowns fn-frame-item)
                                  (fn-ct-publish-list fn-ct-conflict-evidence
                                   fn-ct-unknowns-okp)))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md §2).  The ten keystones leave this book
; enabled, together with `fn-ct-all-in-store`, the list-recursive glue
; predicate the independence keystone is stated in.  The two composition
; lemmas are proof vocabulary and are withdrawn under one name.

(deftheory fn-ct-invariants-vocabulary
  '(fn-ct-store-resolved-deps-resolve
    fn-ct-prepare-then-durable-complete-accepts))

(in-theory (disable fn-ct-invariants-vocabulary))