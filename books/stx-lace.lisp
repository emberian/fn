; fn: the lace as the store projected, and the bridge lemma that makes
; inbound transit a lace merge.
;
; specs/substrate-transport.md sections 2.1 to 2.3 (packets S2 and S3).
;
; The spine, mechanically: fn-stx-delta is a singleton exactly when the
; article's own octets verify under this node's keyring, and nil otherwise.
; An article whose statement is missing, malformed, unverifiable or signed by
; an unknown creator is still in the store -- it contributes bytes and no
; authority.  There is exactly one durable copy of every statement, the
; article that carries it, so fn-stx-lace is a PROJECTION of the store and
; never a second store; books/stx-index.lisp carries the incremental twin the
; served path uses, with the agreement theorem as its licence (D3).
;
; The store is newest-first (fn-accept-prepare conses), so the projection
; recurses on the cdr and appends the head's delta LAST: the lace is in
; acceptance order, oldest first, which is the order fn-lace-lookup and
; fn-pol-latest read.

(in-package "ACL2")
(include-book "stx-verify")
(include-book "lace-invariants")
(include-book "node")

(local (in-theory (enable (:d fn-lace-hasp) (:d fn-lace-same-slotp)
                          (:d fn-lace-slot-conflictp) (:d fn-lace-equivocatorp))))

(local (defthm fn-stx-member-of-append
         (iff (member-equal x (append a b))
              (or (member-equal x a) (member-equal x b)))))

(local (defthm fn-stx-ids-of-append
         (equal (fn-lace-ids (append a b))
                (append (fn-lace-ids a) (fn-lace-ids b)))))

(local (defthm fn-stx-stmt-is-consp
         (implies (fn-stmt-p s) (consp s))
         :hints (("Goal" :in-theory (enable fn-stmt-p)))))

(local (defthm fn-stx-verified-is-a-statement
         (implies (fn-prin-verifiedp s keyring) (fn-stmt-p s))
         :hints (("Goal" :in-theory (enable fn-prin-verifiedp)))))

(local (defthm fn-stx-nil-is-not-verified
         (not (fn-prin-verifiedp nil keyring))
         :hints (("Goal" :in-theory (enable fn-prin-verifiedp fn-stmt-p)))))

; -----------------------------------------------------------------------------
; The parsed article behind stored octets

; NIL unless the received octets parse and the parse is a syntax article.
; Every caller below reaches fn-stx-verdict only through this, so no guard
; obligation of the verdict escapes to the host.
(defun fn-stx-parse (octets)
  (declare (xargs :guard t))
  (let ((r (fn-article-parse octets)))
    (if (not (and (true-listp r) (fn-article-result-okp r)))
        nil
      (let ((a (fn-article-result-article r)))
        (if (fn-article-syntax-p a) a nil)))))

(defthm fn-stx-parse-is-syntax-article
  (implies (fn-stx-parse octets)
           (fn-article-syntax-p (fn-stx-parse octets))))

(in-theory (disable (:d fn-stx-parse)))

; -----------------------------------------------------------------------------
; The verified predicate, and its equation with the recorded verdict

(defun fn-stx-verifiedp (article keyring)
  (declare (xargs :guard (and (fn-article-syntax-p article)
                              (fn-prin-keyringp keyring))))
  (fn-prin-verifiedp (fn-stx-statement-of article) keyring))

; The evidence slot records a verdict; the lace projection tests a predicate.
; This is the equation that stops them being two authorities.
(defthm fn-stx-verifiedp-is-the-verified-verdict
  (iff (fn-stx-verifiedp article keyring)
       (equal (fn-stx-verdict-token (fn-stx-verdict article keyring generation))
              :verified))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable (:d fn-stx-verdict) (:d fn-stx-statement-of)
                                     (:d fn-stx-verifiedp)))))

; -----------------------------------------------------------------------------
; The delta one accepted article contributes

(defun fn-stx-delta (octets keyring)
  (declare (xargs :guard (fn-prin-keyringp keyring)))
  (let ((a (fn-stx-parse octets)))
    (if (and a (fn-stx-verifiedp a keyring))
        (list (fn-stx-statement-of a))
      nil)))

(defthm fn-stx-delta-is-lace
  (fn-lace-p (fn-stx-delta octets keyring))
  :hints (("Goal" :in-theory (enable (:d fn-stx-verifiedp)))))

(defthm fn-stx-delta-is-true-list
  (true-listp (fn-stx-delta octets keyring)))

(defthm fn-stx-delta-is-nil-or-singleton
  (not (consp (cdr (fn-stx-delta octets keyring)))))

; The unverified article contributes bytes and nothing else: the spine
; sentence, as an equation rather than a comment.
(defthm fn-stx-unverified-contributes-no-authority
  (implies (not (fn-stx-verifiedp (fn-stx-parse octets) keyring))
           (equal (fn-stx-delta octets keyring) nil)))

(in-theory (disable (:d fn-stx-delta) (:d fn-stx-verifiedp)))

; -----------------------------------------------------------------------------
; The store, and the lace it projects to

(defun fn-stx-store (node)
  (declare (xargs :guard t))
  (fn-state-articles (fn-node-acceptance node)))

(defun fn-stx-lace-of-store (articles keyring)
  (declare (xargs :guard (fn-prin-keyringp keyring)))
  (if (consp articles)
      (append (fn-stx-lace-of-store (cdr articles) keyring)
              (fn-stx-delta (fn-article-payload (car articles)) keyring))
    nil))

(defthm fn-stx-lace-of-store-is-true-list
  (true-listp (fn-stx-lace-of-store articles keyring)))

(defthm fn-stx-lace-of-store-is-lace
  (fn-lace-p (fn-stx-lace-of-store articles keyring)))

(defun fn-stx-lace (node keyring)
  (declare (xargs :guard (fn-prin-keyringp keyring)))
  (fn-stx-lace-of-store (fn-stx-store node) keyring))

(defthm fn-stx-lace-is-lace
  (fn-lace-p (fn-stx-lace node keyring)))

; -----------------------------------------------------------------------------
; The bridge: accepting a transit article is a lace merge of its delta
;
; fn-stx-acceptedp is the OBSERVATION that the transaction completed durably:
; the store of the next node is the store of this one with the accepted
; article at its head.  It is not a second acceptance path.
;
; Until 2026-09-21 this comment said that `books/stx-transit.lisp' names the
; composition and proves it satisfies this predicate, and that
; `tests/acl2/stx-lace-tests.lisp' exhibits a run.  NEITHER FILE HAS EVER
; EXISTED.  So the observation was assumed, and every keystone below that
; hypothesises it -- fn-stx-lace-of-accept-is-merge, fn-stx-transit-ids-are-
; union, fn-stx-transit-equivocation-survives-later-merges, and
; fn-stx-index-invariant-preserved-by-accept in books/stx-index.lisp -- was
; preservation under a hypothesis nothing established.  The theorem after the
; definition establishes it, at the transition the host actually calls.

(defun fn-stx-acceptedp (node next article)
  (declare (xargs :guard t))
  (and (consp article)
       (equal (fn-stx-store next)
              (cons article (fn-stx-store node)))))

; THE SUBJECT OF THE OBSERVATION (AGENTS.md, "the theorem subject is the
; function the host calls").  The host line is
; `host/store-node-host.lisp' `fn-store-sn-finish' (line 402), whose only node
; step is `fn-sn-finish' (books/store-node.lisp line 200), whose only node step
; is `(fn-node-complete (fn-sn-node s) txid generation :durable)' (line 204);
; `fn-snrt-new-success-is-actual-matching-durable-completion'
; (books/store-node-resolution.lisp line 414) already proves that no other step
; adds an acknowledgement.  Those books sit ABOVE this one in the include order
; -- books/stx-lace.lisp includes books/node.lisp -- so they are named here and
; the theorem is stated about `fn-node-complete' itself.
;
; The accepted article is named, not existentially claimed: it is the one
; `fn-install-pending' (books/acceptance.lisp line 236) conses onto the store.
; So the S3 keystones' hypothesis is discharged by the durable branch of the
; node transition, with the article that branch publishes.
(defthm fn-stx-durable-completion-is-an-acceptance
  (implies (fn-node-pending-matchesp s txid generation)
           (fn-stx-acceptedp
            s
            (fn-node-complete s txid generation :durable)
            (fn-article-from-pending
             (fn-state-pending (fn-node-acceptance s)))))
  :hints (("Goal"
           :in-theory (enable fn-stx-acceptedp fn-stx-store
                              fn-node-complete fn-node-pending-matchesp
                              fn-accept-complete fn-install-pending
                              fn-node-statep))))

; A delta is fresh when the lace does not already hold its content id.  The
; hypothesis is not decoration: two articles with different Message-IDs can
; carry the same statement, and then the store grows while the lace's ids do
; not.  fn-stx-transit-ids-are-union below holds either way.
(defun fn-stx-delta-freshp (lace delta)
  (declare (xargs :guard (and (fn-lace-p lace) (fn-lace-p delta))))
  (if (consp delta)
      (not (fn-lace-hasp lace (fn-stmt-id (car delta))))
    t))

(defthm fn-stx-merge-of-fresh-short-delta
  (implies (and (true-listp lace)
                (true-listp delta)
                (not (consp (cdr delta)))
                (fn-stx-delta-freshp lace delta))
           (equal (fn-lace-merge lace delta)
                  (append lace delta))))

(defthm fn-stx-lace-of-accept-is-merge
  (implies (and (fn-stx-acceptedp node next article)
                (fn-stx-delta-freshp
                 (fn-stx-lace node keyring)
                 (fn-stx-delta (fn-article-payload article) keyring)))
           (equal (fn-stx-lace next keyring)
                  (fn-lace-merge (fn-stx-lace node keyring)
                                 (fn-stx-delta (fn-article-payload article)
                                               keyring))))
  :hints (("Goal" :in-theory (disable fn-stx-delta-freshp fn-lace-merge
                                      fn-stx-delta))))

; -----------------------------------------------------------------------------
; S3-1 (corollary of fn-lace-merge-ids-are-union and the bridge above)

(defthm fn-stx-transit-ids-are-union
  (implies (and (fn-stx-acceptedp node next article)
                (fn-stx-delta-freshp
                 (fn-stx-lace node keyring)
                 (fn-stx-delta (fn-article-payload article) keyring)))
           (iff (member-equal h (fn-lace-ids (fn-stx-lace next keyring)))
                (or (member-equal h (fn-lace-ids (fn-stx-lace node keyring)))
                    (member-equal h (fn-lace-ids
                                     (fn-stx-delta (fn-article-payload article)
                                                   keyring))))))
  :hints (("Goal"
           :use ((:instance fn-stx-lace-of-accept-is-merge))
           :in-theory (disable fn-stx-lace-of-accept-is-merge fn-stx-lace
                               fn-stx-acceptedp fn-stx-delta-freshp
                               fn-stx-delta fn-lace-merge))))

; -----------------------------------------------------------------------------
; S3-2 (corollary of fn-lace-distinct-same-slot-is-equivocation and the
; bridge).  Note the two membership conjuncts: NEITHER FORK IS DROPPED, which
; is the substantive half and does not follow from the equivocator predicate.

(defthm fn-stx-transit-equivocation-is-detected
  (implies (and (fn-stx-acceptedp node next article)
                (fn-stx-delta-freshp
                 (fn-stx-lace node keyring)
                 (fn-stx-delta (fn-article-payload article) keyring))
                (member-equal s1 (fn-stx-lace node keyring))
                (equal (list s2) (fn-stx-delta (fn-article-payload article)
                                               keyring))
                (not (equal s1 s2))
                (fn-lace-same-slotp s1 s2))
           (and (fn-lace-equivocatorp (fn-stx-lace next keyring)
                                      (fn-stmt-creator s1)
                                      (fn-stmt-incarnation s1))
                (member-equal s1 (fn-stx-lace next keyring))
                (member-equal s2 (fn-stx-lace next keyring))))
  :hints (("Goal"
           :use ((:instance fn-stx-lace-of-accept-is-merge)
                 (:instance fn-stx-merge-of-fresh-short-delta
                            (lace (fn-stx-lace node keyring))
                            (delta (fn-stx-delta (fn-article-payload article)
                                                 keyring)))
                 (:instance fn-lace-distinct-same-slot-is-equivocation
                            (lace (append (fn-stx-lace node keyring)
                                          (list s2)))))
           :in-theory (disable fn-stx-lace-of-accept-is-merge
                               fn-stx-merge-of-fresh-short-delta
                               fn-lace-distinct-same-slot-is-equivocation
                               fn-stx-lace fn-stx-acceptedp fn-stx-delta
                               fn-stx-delta-freshp fn-lace-merge
                               (:d fn-lace-equivocatorp)
                               (:d fn-lace-same-slotp)))))

; Evidence of a fork cannot be erased by a later merge: the wire form of
; fn-lace-merge-preserves-equivocation (corollary).
(defthm fn-stx-transit-equivocation-survives-later-merges
  (implies (and (fn-stx-acceptedp node next article)
                (fn-stx-delta-freshp
                 (fn-stx-lace node keyring)
                 (fn-stx-delta (fn-article-payload article) keyring))
                (fn-lace-equivocatorp (fn-stx-lace node keyring) p i))
           (fn-lace-equivocatorp (fn-stx-lace next keyring) p i))
  :hints (("Goal"
           :use ((:instance fn-stx-lace-of-accept-is-merge)
                 (:instance fn-lace-merge-preserves-equivocation
                            (lace (fn-stx-lace node keyring))
                            (delta (fn-stx-delta (fn-article-payload article)
                                                 keyring))))
           :in-theory (disable fn-stx-lace-of-accept-is-merge
                               fn-lace-merge-preserves-equivocation
                               fn-stx-lace fn-stx-acceptedp fn-stx-delta
                               fn-stx-delta-freshp fn-lace-merge
                               (:d fn-lace-equivocatorp)))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2).  The projection's recursion
; and the store accessor stay open for stx-index and stx-policy above; the
; record vocabulary of the lace is not re-exported here.

(in-theory (disable (:d fn-stx-acceptedp) (:d fn-stx-delta-freshp)))
