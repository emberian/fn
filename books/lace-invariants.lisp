; Merge, canonicity, equivocation and closure invariants for books/lace.lisp.
;
; Keystones, each named for the dregg/minidregg theorem it rebuilds:
;   fn-lace-merge-ids-are-union            laceIds_mergeLace / ids_merge
;   fn-lace-merge-idempotent               merge_idem (here an equality)
;   fn-lace-merge-commutative-ids          merge_comm
;   fn-lace-merge-associative-ids          merge_assoc
;   fn-lace-merge-monotone                 merge_monotone
;   fn-lace-merge-lub                      merge_lub
;   fn-lace-lookup-of-member               lookup_of_mem
;   fn-lace-cross-canonical-self           crossCanonical_self
;   fn-lace-canonical-append-iff           canonical_append_iff
;   fn-lace-same-view-of-cross-canonical   sameView_of_canonical_eq_ids
;   fn-lace-merge-preserves-canonical      (merge keeps Canonical)
;   fn-lace-merge-drops-at-collision       merge_drops_at_collision
;   fn-lace-distinct-same-slot-is-equivocation   EquivocationProof (lib.rs)
;   fn-lace-reissue-is-equivocation        the D10 restore/fork fact
;   fn-lace-merge-preserves-closure        insert's causal-closure invariant
; The cross-canonical gap itself (crossCanonical_is_the_gap) is exhibited in
; tests/acl2/lace-tests.lisp under a colliding digest realiser.

(in-package "ACL2")
(include-book "lace")
(include-book "statement-invariants")

(local (in-theory (disable fn-stmt-id fn-stmt-p fn-stmt-creator
                           fn-stmt-incarnation fn-stmt-sequence fn-stmt-preds
                           fn-stmt-payload fn-stmt-header fn-stmt-kind
                           fn-stmt-sign fn-stmt-payload-ref
                           fn-stmt-signing-preimage)))

; -----------------------------------------------------------------------------
; List facts

(defthm fn-lace-member-of-append
  (iff (member-equal x (append a b))
       (or (member-equal x a) (member-equal x b))))

(defthm fn-lace-ids-of-append
  (equal (fn-lace-ids (append a b))
         (append (fn-lace-ids a) (fn-lace-ids b))))

(defthm fn-lace-member-implies-id-in-ids
  (implies (member-equal s lace)
           (member-equal (fn-stmt-id s) (fn-lace-ids lace))))

(defthm fn-lace-new-is-sublist
  (implies (member-equal s (fn-lace-new lace delta))
           (member-equal s delta)))

(defthm fn-lace-new-ids-are-new
  (implies (member-equal s (fn-lace-new lace delta))
           (not (member-equal (fn-stmt-id s) (fn-lace-ids lace)))))

(defthm fn-lace-member-of-new
  (iff (member-equal s (fn-lace-new lace delta))
       (and (member-equal s delta)
            (not (member-equal (fn-stmt-id s) (fn-lace-ids lace))))))

(defthm fn-lace-member-of-merge
  (iff (member-equal s (fn-lace-merge lace delta))
       (or (member-equal s lace)
           (and (member-equal s delta)
                (not (member-equal (fn-stmt-id s) (fn-lace-ids lace)))))))

(defthm fn-lace-new-is-true-list
  (true-listp (fn-lace-new lace delta)))

(defthm fn-lace-new-is-lace
  (implies (fn-lace-p delta)
           (fn-lace-p (fn-lace-new lace delta))))

(defthm fn-lace-merge-is-lace
  (implies (and (fn-lace-p lace) (fn-lace-p delta))
           (fn-lace-p (fn-lace-merge lace delta))))

; -----------------------------------------------------------------------------
; The join law

(defthm fn-lace-member-ids-of-new
  (iff (member-equal h (fn-lace-ids (fn-lace-new lace delta)))
       (and (member-equal h (fn-lace-ids delta))
            (not (member-equal h (fn-lace-ids lace))))))

(defthm fn-lace-merge-ids-are-union
  (iff (member-equal h (fn-lace-ids (fn-lace-merge lace delta)))
       (or (member-equal h (fn-lace-ids lace))
           (member-equal h (fn-lace-ids delta)))))

; -----------------------------------------------------------------------------
; Id-set order: pick-a-point

(defthm fn-lace-ids-subsetp-elim
  (implies (and (fn-lace-ids-subsetp a b)
                (member-equal h (fn-lace-ids a)))
           (member-equal h (fn-lace-ids b))))

(defthm fn-lace-ids-subsetp-elim-member
  (implies (and (fn-lace-ids-subsetp a b)
                (member-equal s a))
           (member-equal (fn-stmt-id s) (fn-lace-ids b))))

(defthm fn-lace-ids-witness-is-member-or-nil
  (implies (not (fn-lace-ids-subsetp a b))
           (and (member-equal (fn-lace-ids-witness a b) a)
                (not (member-equal (fn-stmt-id (fn-lace-ids-witness a b))
                                   (fn-lace-ids b))))))

(defthm fn-lace-ids-subsetp-by-witness
  (implies (implies (member-equal (fn-lace-ids-witness a b) a)
                    (member-equal (fn-stmt-id (fn-lace-ids-witness a b))
                                  (fn-lace-ids b)))
           (fn-lace-ids-subsetp a b))
  :hints (("Goal" :use fn-lace-ids-witness-is-member-or-nil
           :in-theory (disable fn-lace-ids-witness-is-member-or-nil
                               fn-lace-ids-witness fn-lace-ids-subsetp))))

(defthm fn-lace-ids-subsetp-reflexive
  (fn-lace-ids-subsetp a a)
  :hints (("Goal" :use ((:instance fn-lace-ids-subsetp-by-witness (b a)))
           :in-theory (disable fn-lace-ids-subsetp-by-witness
                               fn-lace-ids-witness fn-lace-ids-subsetp))))

(defthm fn-lace-ids-subsetp-transitive
  (implies (and (fn-lace-ids-subsetp a b)
                (fn-lace-ids-subsetp b c))
           (fn-lace-ids-subsetp a c))
  :hints (("Goal" :use ((:instance fn-lace-ids-subsetp-by-witness (b c)))
           :in-theory (disable fn-lace-ids-subsetp-by-witness
                               fn-lace-ids-witness fn-lace-ids-subsetp))))

; -----------------------------------------------------------------------------
; CRDT laws

(defthm fn-lace-new-of-included-delta-is-nil
  (implies (fn-lace-ids-subsetp delta lace)
           (equal (fn-lace-new lace delta) nil)))

(defthm fn-lace-new-of-self-is-nil
  (equal (fn-lace-new lace lace) nil))

(defthm fn-lace-merge-idempotent
  (implies (true-listp lace)
           (equal (fn-lace-merge lace lace) lace)))

(defthm fn-lace-merge-monotone
  (fn-lace-ids-subsetp lace (fn-lace-merge lace delta))
  :hints (("Goal" :use ((:instance fn-lace-ids-subsetp-by-witness
                                   (a lace) (b (fn-lace-merge lace delta))))
           :in-theory (disable fn-lace-ids-subsetp-by-witness
                               fn-lace-ids-witness fn-lace-ids-subsetp
                               fn-lace-merge))))

(defthm fn-lace-merge-absorbs-delta
  (fn-lace-ids-subsetp delta (fn-lace-merge lace delta))
  :hints (("Goal" :use ((:instance fn-lace-ids-subsetp-by-witness
                                   (a delta) (b (fn-lace-merge lace delta))))
           :in-theory (disable fn-lace-ids-subsetp-by-witness
                               fn-lace-ids-witness fn-lace-ids-subsetp
                               fn-lace-merge))))

(defthm fn-lace-merge-lub
  (implies (and (fn-lace-ids-subsetp lace u)
                (fn-lace-ids-subsetp delta u))
           (fn-lace-ids-subsetp (fn-lace-merge lace delta) u))
  :hints (("Goal" :use ((:instance fn-lace-ids-subsetp-by-witness
                                   (a (fn-lace-merge lace delta)) (b u)))
           :in-theory (disable fn-lace-ids-subsetp-by-witness
                               fn-lace-ids-witness fn-lace-ids-subsetp
                               fn-lace-merge))))

(defthm fn-lace-merge-commutative-ids
  (fn-lace-same-idsp (fn-lace-merge a b) (fn-lace-merge b a))
  :hints (("Goal"
           :use ((:instance fn-lace-merge-lub
                            (lace a) (delta b) (u (fn-lace-merge b a)))
                 (:instance fn-lace-merge-lub
                            (lace b) (delta a) (u (fn-lace-merge a b))))
           :in-theory (disable fn-lace-merge-lub fn-lace-ids-subsetp
                               fn-lace-merge))))

(defthm fn-lace-merge-associative-ids
  (fn-lace-same-idsp (fn-lace-merge (fn-lace-merge a b) c)
                     (fn-lace-merge a (fn-lace-merge b c)))
  :hints (("Goal"
           :use ((:instance fn-lace-merge-lub
                            (lace (fn-lace-merge a b)) (delta c)
                            (u (fn-lace-merge a (fn-lace-merge b c))))
                 (:instance fn-lace-merge-lub
                            (lace a) (delta b)
                            (u (fn-lace-merge a (fn-lace-merge b c))))
                 (:instance fn-lace-merge-lub
                            (lace a) (delta (fn-lace-merge b c))
                            (u (fn-lace-merge (fn-lace-merge a b) c)))
                 (:instance fn-lace-merge-lub
                            (lace b) (delta c)
                            (u (fn-lace-merge (fn-lace-merge a b) c)))
                 (:instance fn-lace-ids-subsetp-transitive
                            (a b) (b (fn-lace-merge b c))
                            (c (fn-lace-merge a (fn-lace-merge b c))))
                 (:instance fn-lace-ids-subsetp-transitive
                            (a c) (b (fn-lace-merge b c))
                            (c (fn-lace-merge a (fn-lace-merge b c))))
                 (:instance fn-lace-ids-subsetp-transitive
                            (a a) (b (fn-lace-merge a b))
                            (c (fn-lace-merge (fn-lace-merge a b) c)))
                 (:instance fn-lace-ids-subsetp-transitive
                            (a b) (b (fn-lace-merge a b))
                            (c (fn-lace-merge (fn-lace-merge a b) c)))
                 (:instance fn-lace-merge-monotone (lace a) (delta b))
                 (:instance fn-lace-merge-monotone
                            (lace (fn-lace-merge a b)) (delta c))
                 (:instance fn-lace-merge-monotone (lace b) (delta c))
                 (:instance fn-lace-merge-monotone
                            (lace a) (delta (fn-lace-merge b c)))
                 (:instance fn-lace-merge-absorbs-delta (lace a) (delta b))
                 (:instance fn-lace-merge-absorbs-delta
                            (lace (fn-lace-merge a b)) (delta c))
                 (:instance fn-lace-merge-absorbs-delta (lace b) (delta c))
                 (:instance fn-lace-merge-absorbs-delta
                            (lace a) (delta (fn-lace-merge b c))))
           :in-theory (disable fn-lace-merge-lub fn-lace-ids-subsetp
                               fn-lace-merge fn-lace-merge-monotone
                               fn-lace-merge-absorbs-delta
                               fn-lace-ids-subsetp-transitive))))

; -----------------------------------------------------------------------------
; Canonicity

(defthm fn-lace-no-conflictp-elim
  (implies (and (fn-lace-no-conflictp s lace)
                (member-equal x lace)
                (not (equal x s)))
           (and (not (equal (fn-stmt-id x) (fn-stmt-id s)))
                (not (equal (fn-stmt-id s) (fn-stmt-id x))))))

(defthm fn-lace-cross-canonicalp-elim
  (implies (and (fn-lace-cross-canonicalp a b)
                (member-equal x a)
                (member-equal y b)
                (equal (fn-stmt-id x) (fn-stmt-id y)))
           (equal x y))
  :rule-classes nil
  :hints (("Goal" :induct (fn-lace-cross-canonicalp a b))))

(defthm fn-lace-no-conflictp-of-member-of-cross
  (implies (and (fn-lace-cross-canonicalp a b)
                (member-equal y b))
           (fn-lace-no-conflictp y a))
  :hints (("Goal" :induct (fn-lace-cross-canonicalp a b))))

(local (defun fn-lace-sublistp (x y)
         (if (consp x)
             (and (member-equal (car x) y)
                  (fn-lace-sublistp (cdr x) y))
           t)))

(local (defthm fn-lace-sublistp-cons
         (implies (fn-lace-sublistp x y)
                  (fn-lace-sublistp x (cons z y)))))

(local (defthm fn-lace-sublistp-reflexive
         (fn-lace-sublistp x x)))

(local (defthm fn-lace-cross-canonicalp-symmetric-aux
         (implies (and (fn-lace-cross-canonicalp a b0)
                       (fn-lace-sublistp b b0))
                  (fn-lace-cross-canonicalp b a))
         :hints (("Goal" :induct (fn-lace-sublistp b b0)))))

(defthm fn-lace-cross-canonicalp-symmetric
  (implies (fn-lace-cross-canonicalp a b)
           (fn-lace-cross-canonicalp b a))
  :hints (("Goal" :use ((:instance fn-lace-cross-canonicalp-symmetric-aux
                                   (b0 b))))))

(defthm fn-lace-cross-canonical-self
  (equal (fn-lace-cross-canonicalp lace lace)
         (fn-lace-canonicalp lace))
  :rule-classes nil)

(defthm fn-lace-no-conflictp-of-append
  (equal (fn-lace-no-conflictp s (append a b))
         (and (fn-lace-no-conflictp s a)
              (fn-lace-no-conflictp s b))))

(defthm fn-lace-cross-canonicalp-of-append-left
  (equal (fn-lace-cross-canonicalp (append a b) c)
         (and (fn-lace-cross-canonicalp a c)
              (fn-lace-cross-canonicalp b c))))

(defthm fn-lace-cross-canonicalp-of-append-right
  (equal (fn-lace-cross-canonicalp a (append b c))
         (and (fn-lace-cross-canonicalp a b)
              (fn-lace-cross-canonicalp a c))))

(defthm fn-lace-canonical-append-iff
  (iff (fn-lace-canonicalp (append a b))
       (and (fn-lace-canonicalp a)
            (fn-lace-canonicalp b)
            (fn-lace-cross-canonicalp a b)))
  :hints (("Goal" :in-theory (enable fn-lace-canonicalp))))

; Lookup

(defthm fn-lace-lookup-is-member-with-id
  (implies (member-equal h (fn-lace-ids lace))
           (and (member-equal (fn-lace-lookup lace h) lace)
                (equal (fn-stmt-id (fn-lace-lookup lace h)) h))))

(defthm fn-lace-lookup-absent
  (implies (not (member-equal h (fn-lace-ids lace)))
           (equal (fn-lace-lookup lace h) nil)))

(defthm fn-lace-lookup-of-member
  (implies (and (fn-lace-canonicalp lace)
                (member-equal s lace))
           (equal (fn-lace-lookup lace (fn-stmt-id s)) s))
  :hints (("Goal"
           :use ((:instance fn-lace-cross-canonicalp-elim
                            (a lace) (b lace)
                            (x (fn-lace-lookup lace (fn-stmt-id s))) (y s)))
           :in-theory (disable fn-lace-lookup))))

; Two laces with the same id set that are cross-canonical present the same
; statement at every id.  The ACL2 lookup returns the first match, so the two
; per-lace canonicity premises of the Lean statement are not needed here; the
; cross-canonical premise is the one that does the work, and
; tests/acl2/lace-tests.lisp shows the conclusion fails without it.
(defthm fn-lace-same-view-of-cross-canonical
  (implies (and (fn-lace-same-idsp a b)
                (fn-lace-cross-canonicalp a b))
           (equal (fn-lace-lookup a h) (fn-lace-lookup b h)))
  :rule-classes nil
  :hints (("Goal"
           :cases ((member-equal h (fn-lace-ids a)))
           :use ((:instance fn-lace-cross-canonicalp-elim
                            (x (fn-lace-lookup a h)) (y (fn-lace-lookup b h)))
                 (:instance fn-lace-ids-subsetp-elim (a a) (b b))
                 (:instance fn-lace-ids-subsetp-elim (a b) (b a)))
           :in-theory (disable fn-lace-lookup fn-lace-ids-subsetp
                               fn-lace-ids-subsetp-elim
                               fn-lace-cross-canonicalp
                               fn-lace-no-conflictp-elim))))

; Merge and canonicity

(defthm fn-lace-no-conflictp-of-new-when-present
  (implies (member-equal (fn-stmt-id s) (fn-lace-ids lace))
           (fn-lace-no-conflictp s (fn-lace-new lace delta))))

(defthm fn-lace-cross-canonicalp-lace-new
  (fn-lace-cross-canonicalp lace (fn-lace-new lace delta)))

(defthm fn-lace-no-conflictp-of-sublist
  (implies (fn-lace-no-conflictp s delta)
           (fn-lace-no-conflictp s (fn-lace-new lace delta))))

(defthm fn-lace-cross-canonicalp-new-right
  (implies (fn-lace-cross-canonicalp a delta)
           (fn-lace-cross-canonicalp a (fn-lace-new lace delta))))

(defthm fn-lace-cross-canonicalp-new-left
  (implies (fn-lace-cross-canonicalp delta b)
           (fn-lace-cross-canonicalp (fn-lace-new lace delta) b)))

(defthm fn-lace-merge-preserves-canonical
  (implies (and (fn-lace-canonicalp lace)
                (fn-lace-canonicalp delta))
           (fn-lace-canonicalp (fn-lace-merge lace delta)))
  :hints (("Goal"
           :use ((:instance fn-lace-cross-canonicalp-symmetric
                            (a lace) (b (fn-lace-new lace delta))))
           :in-theory (e/d (fn-lace-canonicalp)
                           (fn-lace-cross-canonicalp-symmetric)))))

; The damage at a collision: a delta statement whose id is already present
; is discarded even when it differs from the statement holding that id.
(defthm fn-lace-merge-drops-at-collision
  (implies (and (member-equal b lace)
                (equal (fn-stmt-id d) (fn-stmt-id b))
                (not (member-equal d lace)))
           (not (member-equal d (fn-lace-merge lace delta)))))

; -----------------------------------------------------------------------------
; Equivocation

(defthm fn-lace-slot-conflictp-intro
  (implies (and (member-equal s2 lace)
                (not (equal s1 s2))
                (fn-lace-same-slotp s2 s1))
           (fn-lace-slot-conflictp s1 lace)))

(defthm fn-lace-equivocator-scan-intro
  (implies (and (member-equal s1 rest)
                (equal (fn-stmt-creator s1) principal)
                (equal (fn-stmt-incarnation s1) incarnation)
                (fn-lace-slot-conflictp s1 lace))
           (fn-lace-equivocator-scan rest lace principal incarnation)))

(defthm fn-lace-distinct-same-slot-is-equivocation
  (implies (and (member-equal s1 lace)
                (member-equal s2 lace)
                (not (equal s1 s2))
                (fn-lace-same-slotp s1 s2))
           (fn-lace-equivocatorp lace (fn-stmt-creator s1)
                                 (fn-stmt-incarnation s1)))
  :hints (("Goal"
           :use ((:instance fn-lace-slot-conflictp-intro)
                 (:instance fn-lace-equivocator-scan-intro
                            (rest lace)
                            (principal (fn-stmt-creator s1))
                            (incarnation (fn-stmt-incarnation s1))))
           :in-theory (disable fn-lace-slot-conflictp-intro
                               fn-lace-equivocator-scan-intro
                               fn-lace-slot-conflictp
                               fn-lace-equivocator-scan))))

(defthm fn-lace-slot-conflictp-monotone
  (implies (fn-lace-slot-conflictp s lace)
           (fn-lace-slot-conflictp s (append lace x))))

(defthm fn-lace-equivocator-scan-monotone-lace
  (implies (fn-lace-equivocator-scan rest lace p i)
           (fn-lace-equivocator-scan rest (append lace x) p i)))

(defthm fn-lace-equivocator-scan-monotone-rest
  (implies (fn-lace-equivocator-scan rest lace p i)
           (fn-lace-equivocator-scan (append rest x) lace p i)))

(defthm fn-lace-merge-preserves-equivocation
  (implies (fn-lace-equivocatorp lace p i)
           (fn-lace-equivocatorp (fn-lace-merge lace delta) p i)))

; The restore/fork fact.  Fields of a signed statement:
(defthm fn-lace-sign-fields
  (and (equal (fn-stmt-creator (fn-stmt-sign sk c i n preds k p)) c)
       (equal (fn-stmt-incarnation (fn-stmt-sign sk c i n preds k p)) i)
       (equal (fn-stmt-sequence (fn-stmt-sign sk c i n preds k p)) n)
       (equal (fn-stmt-payload (fn-stmt-sign sk c i n preds k p)) p))
  :hints (("Goal" :in-theory (enable fn-stmt-sign fn-stmt-creator
                                      fn-stmt-incarnation fn-stmt-sequence
                                      fn-stmt-payload fn-stmt-header))))

(defthm fn-lace-reissue-statements-differ
  (implies (not (equal p1 p2))
           (not (equal (fn-stmt-sign sk1 c i n preds1 k1 p1)
                       (fn-stmt-sign sk2 c i n preds2 k2 p2))))
  :hints (("Goal" :use ((:instance fn-lace-sign-fields
                                   (sk sk1) (preds preds1) (k k1) (p p1))
                        (:instance fn-lace-sign-fields
                                   (sk sk2) (preds preds2) (k k2) (p p2)))
           :in-theory (disable fn-lace-sign-fields))))

; A node restored from an old snapshot reissues (incarnation, sequence) with
; different content: any lace holding both statements shows it equivocating,
; whatever the two signatures, predecessors or kinds are.  Structural half of
; PRF-017 / OBJ-004; that the two statements have distinct ids so that a lace
; can hold both is A-CRYPTO (fn-lace-merge-drops-at-collision).
(defthm fn-lace-reissue-is-equivocation
  (implies (and (not (equal p1 p2))
                (member-equal (fn-stmt-sign sk1 c i n preds1 k1 p1) lace)
                (member-equal (fn-stmt-sign sk2 c i n preds2 k2 p2) lace))
           (fn-lace-equivocatorp lace c i))
  :hints (("Goal"
           :use ((:instance fn-lace-distinct-same-slot-is-equivocation
                            (s1 (fn-stmt-sign sk1 c i n preds1 k1 p1))
                            (s2 (fn-stmt-sign sk2 c i n preds2 k2 p2))))
           :in-theory (disable fn-lace-distinct-same-slot-is-equivocation
                               fn-lace-equivocatorp))))

(defthm fn-lace-reissue-detected-after-merge
  (implies (and (not (equal p1 p2))
                (not (equal (fn-stmt-id (fn-stmt-sign sk c i n nil :article p1))
                            (fn-stmt-id (fn-stmt-sign sk c i n nil :article p2)))))
           (fn-lace-equivocatorp
            (fn-lace-merge (list (fn-stmt-sign sk c i n nil :article p1))
                           (list (fn-stmt-sign sk c i n nil :article p2)))
            c i))
  :hints (("Goal"
           :use ((:instance fn-lace-reissue-is-equivocation
                            (sk1 sk) (sk2 sk) (preds1 nil) (preds2 nil)
                            (k1 :article) (k2 :article)
                            (lace (fn-lace-merge
                                   (list (fn-stmt-sign sk c i n nil :article p1))
                                   (list (fn-stmt-sign sk c i n nil :article p2))))))
           :in-theory (disable fn-lace-reissue-is-equivocation
                               fn-lace-equivocatorp fn-lace-merge))))

; -----------------------------------------------------------------------------
; Causal closure

(defthm fn-lace-ids-presentp-monotone
  (implies (and (fn-lace-ids-presentp ids a)
                (fn-lace-ids-subsetp a b))
           (fn-lace-ids-presentp ids b)))

(defthm fn-lace-closed-inp-monotone
  (implies (and (fn-lace-closed-inp stmts a)
                (fn-lace-ids-subsetp a b))
           (fn-lace-closed-inp stmts b)))

(defthm fn-lace-closed-inp-of-append
  (equal (fn-lace-closed-inp (append a b) lace)
         (and (fn-lace-closed-inp a lace)
              (fn-lace-closed-inp b lace))))

(defthm fn-lace-closed-inp-of-new
  (implies (fn-lace-closed-inp delta lace)
           (fn-lace-closed-inp (fn-lace-new x delta) lace)))

(defthm fn-lace-merge-preserves-closure
  (implies (and (fn-lace-causally-closedp lace)
                (fn-lace-causally-closedp delta))
           (fn-lace-causally-closedp (fn-lace-merge lace delta)))
  :hints (("Goal"
           :use ((:instance fn-lace-closed-inp-monotone
                            (stmts lace) (a lace)
                            (b (fn-lace-merge lace delta)))
                 (:instance fn-lace-closed-inp-monotone
                            (stmts (fn-lace-new lace delta)) (a delta)
                            (b (fn-lace-merge lace delta)))
                 (:instance fn-lace-closed-inp-of-new (x lace) (lace delta)))
           :in-theory (e/d (fn-lace-causally-closedp)
                           (fn-lace-closed-inp-monotone
                            fn-lace-closed-inp-of-new
                            fn-lace-closed-inp fn-lace-ids-subsetp)))))
