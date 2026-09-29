; fn: the statement lace of the RETAINED node -- its handles read through the
; arena (PKT-892, lane stx-model, 2026-09-29).
;
; Since the records flip (PKT-635) a retained article's payload is an arena
; HANDLE (books/payload-kinds.lisp fn-payload-handle-p): the octets it denotes
; are fn-handle-bytes of the handle (books/payload-arena.lisp), nil outside the
; arena.  books/stx-lace.lisp's lace (fn-stx-lace-of-store) and
; books/stx-index.lisp's index (fn-stx-index-of-store) are the OCTET model:
; each reads (fn-article-payload a) as octets, and both are declared :wire.
; Until this book the node lace `fn-stx-lace' applied that model to the node's
; handle articles, so it read no statement from any node the composed machine
; produces, and every keystone stated over it was satisfied by the empty lace
; (planning/evidence/stx-vacuity-2026-09-29.md: sixteen witnesses, found by
; tools/payload_kind_check.py's one-hop rule).
;
; Here the model receives the octets the handles denote.  ALPHA of the
; acceptance articles (fn-articles-wire-of: each handle replaced by its bytes,
; the reading books/store-intern.lisp's duplicate verdict and
; books/owner-feed-article.lisp's feed already use) is the octet model's
; article list, and the node lace and the carried-index invariant are the octet
; model over ALPHA.  The keystones are the S3 rows with the arena threaded;
; each names ONE arena for the node before and after the acceptance, which is
; the composed order (the intern that seals the accepted article's bytes
; precedes the completion, and a seal appends -- fn-arena-seal-list-is-append
; -- so every earlier handle denotes the same bytes).
;
; No assumption enters: the abstract arena is the list of its payloads and
; fn-handle-bytes reads `nth' (fn-arena-payload-is-nth).  The equality of the
; node lace with the retained ROWS' lace is books/stx-lace-rows.lisp
; fn-stx-lace-of-node-is-the-rows-lace (PRF-995).
(in-package "ACL2")
(include-book "stx-index")
(include-book "payload-arena")

; The same local vocabulary books/stx-lace.lisp gives its own proofs (its
; locals are not visible here under certification).
(local (defthm fn-stx-node-member-of-append
         (iff (member-equal x (append a b))
              (or (member-equal x a) (member-equal x b)))))

(local (defthm fn-stx-node-ids-of-append
         (equal (fn-lace-ids (append a b))
                (append (fn-lace-ids a) (fn-lace-ids b)))))

(local (defthm fn-stx-node-stmt-is-consp
         (implies (fn-stmt-p s) (consp s))
         :hints (("Goal" :in-theory (enable fn-stmt-p)))))

(local (defthm fn-stx-node-verified-is-a-statement
         (implies (fn-prin-verifiedp s keyring) (fn-stmt-p s))
         :hints (("Goal" :in-theory (enable fn-prin-verifiedp)))))

(local (defthm fn-stx-node-nil-is-not-verified
         (not (fn-prin-verifiedp nil keyring))
         :hints (("Goal" :in-theory (enable fn-prin-verifiedp fn-stmt-p)))))

; -----------------------------------------------------------------------------
; ALPHA of the acceptance articles: each article's handle replaced by its
; bytes (a handle outside the arena reads as no bytes, as fn-row-bytes).
; Defined here, beside the model that reads it, since 2026-09-29; it was
; books/store-intern.lisp's, whose duplicate/conflict verdict still reads it.

(defun fn-articles-wire-of (articles fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (if (atom articles)
      nil
    (let ((a (car articles)))
      (cons (fn-make-article (fn-article-msgid a)
                             (fn-handle-bytes (fn-article-payload a) fn-arena)
                             (fn-article-groups a) (fn-article-memberships a)
                             (fn-article-pin a) (fn-article-stamp a))
            (fn-articles-wire-of (cdr articles) fn-arena)))))

(verify-guards fn-articles-wire-of)

; -----------------------------------------------------------------------------
; The node lace: the octet model over ALPHA

(defun fn-stx-lace (node keyring fn-arena)
  (declare (xargs :stobjs fn-arena :guard (fn-prin-keyringp keyring)))
  (fn-stx-lace-of-store (fn-articles-wire-of (fn-stx-store node) fn-arena)
                        keyring))

(defthm fn-stx-lace-is-lace
  (fn-lace-p (fn-stx-lace node keyring fn-arena)))

(defthm fn-stx-lace-is-true-list
  (true-listp (fn-stx-lace node keyring fn-arena)))

; The handle-side lace IS the octet-side lace of ALPHA, named as the unfolding
; it is (assurance rule: cite keystones; a restatement says so in its name).
(defthm fn-stx-lace-is-the-wire-lace-of-alpha-by-definition
  (equal (fn-stx-lace node keyring fn-arena)
         (fn-stx-lace-of-store (fn-articles-wire-of (fn-stx-store node) fn-arena)
                               keyring))
  :rule-classes nil)

; The delta one accepted article contributes: its bytes read through the
; arena, then books/stx-lace.lisp's delta of those octets.
(defun fn-stx-article-delta (article keyring fn-arena)
  (declare (xargs :stobjs fn-arena :guard (fn-prin-keyringp keyring)))
  (fn-stx-delta (fn-handle-bytes (fn-article-payload article) fn-arena) keyring))

(defthm fn-stx-article-delta-is-lace
  (fn-lace-p (fn-stx-article-delta article keyring fn-arena)))

(defthm fn-stx-article-delta-is-true-list
  (true-listp (fn-stx-article-delta article keyring fn-arena)))

(defthm fn-stx-article-delta-is-nil-or-singleton
  (not (consp (cdr (fn-stx-article-delta article keyring fn-arena)))))

; -----------------------------------------------------------------------------
; The bridge: accepting a transit article is a lace merge of its delta.
; fn-stx-acceptedp (books/stx-lace.lisp) is the observation that the
; transaction completed durably, established at the transition the host calls
; by fn-stx-durable-completion-is-an-acceptance there.

(defthm fn-stx-lace-of-accept-is-merge
  (implies (and (fn-stx-acceptedp node next article)
                (fn-stx-delta-freshp
                 (fn-stx-lace node keyring fn-arena)
                 (fn-stx-article-delta article keyring fn-arena)))
           (equal (fn-stx-lace next keyring fn-arena)
                  (fn-lace-merge (fn-stx-lace node keyring fn-arena)
                                 (fn-stx-article-delta article keyring fn-arena))))
  :hints (("Goal" :in-theory (e/d ((:d fn-stx-acceptedp) fn-articles-wire-of)
                                  (fn-stx-delta-freshp fn-lace-merge fn-stx-delta
                                   fn-handle-bytes)))))

; -----------------------------------------------------------------------------
; S3-1 (corollary of fn-lace-merge-ids-are-union and the bridge above)

(defthm fn-stx-transit-ids-are-union
  (implies (and (fn-stx-acceptedp node next article)
                (fn-stx-delta-freshp
                 (fn-stx-lace node keyring fn-arena)
                 (fn-stx-article-delta article keyring fn-arena)))
           (iff (member-equal h (fn-lace-ids (fn-stx-lace next keyring fn-arena)))
                (or (member-equal h (fn-lace-ids (fn-stx-lace node keyring fn-arena)))
                    (member-equal h (fn-lace-ids
                                     (fn-stx-article-delta article keyring
                                                           fn-arena))))))
  :hints (("Goal"
           :use ((:instance fn-stx-lace-of-accept-is-merge))
           :in-theory (disable fn-stx-lace-of-accept-is-merge fn-stx-lace
                               fn-stx-acceptedp fn-stx-delta-freshp
                               fn-stx-article-delta fn-lace-merge))))

; -----------------------------------------------------------------------------
; S3-2 (corollary of fn-lace-distinct-same-slot-is-equivocation and the
; bridge).  Note the two membership conjuncts: NEITHER FORK IS DROPPED, which
; is the substantive half and does not follow from the equivocator predicate.

(defthm fn-stx-transit-equivocation-is-detected
  (implies (and (fn-stx-acceptedp node next article)
                (fn-stx-delta-freshp
                 (fn-stx-lace node keyring fn-arena)
                 (fn-stx-article-delta article keyring fn-arena))
                (member-equal s1 (fn-stx-lace node keyring fn-arena))
                (equal (list s2) (fn-stx-article-delta article keyring fn-arena))
                (not (equal s1 s2))
                (fn-lace-same-slotp s1 s2))
           (and (fn-lace-equivocatorp (fn-stx-lace next keyring fn-arena)
                                      (fn-stmt-creator s1)
                                      (fn-stmt-incarnation s1))
                (member-equal s1 (fn-stx-lace next keyring fn-arena))
                (member-equal s2 (fn-stx-lace next keyring fn-arena))))
  :hints (("Goal"
           :use ((:instance fn-stx-lace-of-accept-is-merge)
                 (:instance fn-stx-merge-of-fresh-short-delta
                            (lace (fn-stx-lace node keyring fn-arena))
                            (delta (fn-stx-article-delta article keyring fn-arena)))
                 (:instance fn-lace-distinct-same-slot-is-equivocation
                            (lace (append (fn-stx-lace node keyring fn-arena)
                                          (list s2)))))
           :in-theory (disable fn-stx-lace-of-accept-is-merge
                               fn-stx-merge-of-fresh-short-delta
                               fn-lace-distinct-same-slot-is-equivocation
                               fn-stx-equivocatorp-of-one-more
                               fn-stx-lace fn-stx-acceptedp fn-stx-article-delta
                               fn-stx-delta-freshp fn-lace-merge
                               (:d fn-lace-equivocatorp)
                               (:d fn-lace-same-slotp)))))

; Evidence of a fork cannot be erased by a later merge: the wire form of
; fn-lace-merge-preserves-equivocation (corollary).
(defthm fn-stx-transit-equivocation-survives-later-merges
  (implies (and (fn-stx-acceptedp node next article)
                (fn-stx-delta-freshp
                 (fn-stx-lace node keyring fn-arena)
                 (fn-stx-article-delta article keyring fn-arena))
                (fn-lace-equivocatorp (fn-stx-lace node keyring fn-arena) p i))
           (fn-lace-equivocatorp (fn-stx-lace next keyring fn-arena) p i))
  :hints (("Goal"
           :use ((:instance fn-stx-lace-of-accept-is-merge)
                 (:instance fn-lace-merge-preserves-equivocation
                            (lace (fn-stx-lace node keyring fn-arena))
                            (delta (fn-stx-article-delta article keyring fn-arena))))
           :in-theory (disable fn-stx-lace-of-accept-is-merge
                               fn-lace-merge-preserves-equivocation
                               fn-stx-equivocatorp-of-one-more
                               fn-stx-lace fn-stx-acceptedp fn-stx-article-delta
                               fn-stx-delta-freshp fn-lace-merge
                               (:d fn-lace-equivocatorp)))))

; -----------------------------------------------------------------------------
; The carried index (books/stx-index.lisp) over the node: the invariant, the
; agreement, the preservation

(defun fn-stx-index-invariantp (index node keyring fn-arena)
  (declare (xargs :stobjs fn-arena :guard (fn-prin-keyringp keyring)))
  (equal index
         (fn-stx-index-of-store (fn-articles-wire-of (fn-stx-store node) fn-arena)
                                keyring)))

; S3-3, in the vocabulary of the served path.
(defthm fn-stx-index-agrees-with-lace
  (implies (fn-stx-index-invariantp index node keyring fn-arena)
           (and (equal (fn-stx-index-lookup index id)
                       (fn-lace-lookup (fn-stx-lace node keyring fn-arena) id))
                (iff (fn-stx-index-equivocatorp index p i)
                     (fn-lace-equivocatorp (fn-stx-lace node keyring fn-arena) p i))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-stx-index-bindings-agree
                                   (articles (fn-articles-wire-of (fn-stx-store node)
                                                                  fn-arena)))
                        (:instance fn-stx-index-equivocators-agree
                                   (articles (fn-articles-wire-of (fn-stx-store node)
                                                                  fn-arena))))
           :in-theory (disable fn-stx-index-bindings-agree
                               fn-stx-index-equivocators-agree
                               fn-stx-index-of-store fn-stx-lace-of-store
                               fn-articles-wire-of
                               fn-stx-index-lookup fn-stx-index-equivocatorp))))

; The durable record is a proved twin of the lace, not a second authority.
(defthm fn-stx-recorded-equivocation-agrees-with-lace
  (implies (fn-stx-index-invariantp index node keyring fn-arena)
           (iff (fn-stx-recorded-equivocationp index p i)
                (fn-lace-equivocatorp (fn-stx-lace node keyring fn-arena) p i)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-stx-index-agrees-with-lace))
           :in-theory (e/d (fn-stx-recorded-equivocationp)
                           (fn-stx-index-invariantp fn-stx-lace
                            fn-stx-index-equivocatorp)))))

; The invariant is carried, not recomputed: one cons per accepted article.
(defthm fn-stx-index-invariant-preserved-by-accept
  (implies (and (fn-stx-index-invariantp index node keyring fn-arena)
                (fn-stx-acceptedp node next article))
           (fn-stx-index-invariantp
            (fn-stx-index-add index (fn-stx-article-delta article keyring fn-arena))
            next keyring fn-arena))
  :hints (("Goal" :in-theory (e/d ((:d fn-stx-acceptedp) fn-articles-wire-of)
                                  (fn-stx-index-add fn-stx-delta fn-handle-bytes)))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2).  fn-stx-lace and ALPHA stay
; open, as the projection did in books/stx-lace.lisp and ALPHA did in
; books/store-intern.lisp; the delta and the invariant are closed.

(in-theory (disable (:d fn-stx-article-delta) (:d fn-stx-index-invariantp)))
