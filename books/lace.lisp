; fn: laces, finite sets of statements keyed by content id, and their merge.
;
; A lace mirrors the dregg blocklace as a replica holds it: a map from content
; id to block (~/dev/breadstuffs/blocklace/src/lib.rs `Blocklace`, Lean
; `Lace := List Block` at Dregg2/Authority/Blocklace.lean:66).  Here a lace is
; a list of statements (books/statement.lisp) and its observable is the set of
; their content ids.
;
; `fn-lace-merge` is the skip-if-present join of
; Dregg2/Distributed/LaceMerge.lean `mergeLace` (finality.rs:690, the
; `contains_key` continue) and ~/dev/minidregg/Theory/LaceMerge.lean `merge`:
; append to the lace every delta statement whose id is not already present.
; Its id set is the union (books/lace-invariants.lisp).
;
; `fn-lace-canonicalp` is `Lace.Canonical` (Blocklace.lean:80): no two
; distinct statements share an id.  `fn-lace-cross-canonicalp` is
; `CrossCanonical` (LaceMerge.lean:247, minidregg LaceMerge.lean §3): the two
; laces resolve every shared id to the same statement.  Canonicity is the
; diagonal of cross-canonicity, exactly as `crossCanonical_self` says.  Both
; are explicit structural hypotheses a node can CHECK on the statements it
; holds; neither is a digest-collision axiom (A-CRYPTO).
;
; `fn-lace-equivocatorp` is the `EquivocationProof` shape of lib.rs (two
; distinct blocks at one (creator, sequence)), refined by fn's incarnation.
; `fn-lace-causally-closedp` is `Blocklace::insert`'s causal-closure invariant
; (lib.rs "Key Invariants" 2).

(in-package "ACL2")
(include-book "statement")


;; Convergence: the codecs cluster withdraws its proof vocabulary on export;
;; re-open it locally (agreed on the deputy board, codecs ANSWER to substrate).
(local (in-theory (enable fn-cbor-codec-vocabulary fn-cbor-invariants-vocabulary fn-record-record-vocabulary fn-record-codec-vocabulary fn-record-guard-vocabulary fn-record-invariants-vocabulary)))

; cluster-local theory: this book is inside the substrate cluster and opens
; the definitions its neighbours withdraw at export (docs/proof-style.md 2).
(local (in-theory (enable fn-crypto-seam-internals
                          fn-stmt-internals)))

(local (in-theory (disable fn-stmt-id fn-stmt-p fn-stmt-creator
                           fn-stmt-incarnation fn-stmt-sequence fn-stmt-preds
                           fn-stmt-payload fn-stmt-header fn-stmt-kind
                           fn-stmt-sign fn-stmt-payload-ref
                           fn-stmt-signing-preimage)))

; -----------------------------------------------------------------------------
; Laces and ids

(defun fn-lace-p (lace)
  (declare (xargs :guard t))
  (if (consp lace)
      (and (fn-stmt-p (car lace))
           (fn-lace-p (cdr lace)))
    (null lace)))

(defthm fn-lace-p-implies-true-listp
  (implies (fn-lace-p lace) (true-listp lace)))

(defthm fn-lace-member-is-stmt
  (implies (and (fn-lace-p lace) (member-equal s lace))
           (fn-stmt-p s)))

(defthm fn-lace-p-of-append
  (implies (true-listp a)
           (equal (fn-lace-p (append a b))
                  (and (fn-lace-p a) (fn-lace-p b)))))

(defun fn-lace-ids (lace)
  (declare (xargs :guard (fn-lace-p lace)))
  (if (consp lace)
      (cons (fn-stmt-id (car lace))
            (fn-lace-ids (cdr lace)))
    nil))

(defthm fn-lace-ids-is-true-list
  (true-listp (fn-lace-ids lace)))

(defun fn-lace-hasp (lace id)
  (declare (xargs :guard (fn-lace-p lace)))
  (if (member-equal id (fn-lace-ids lace)) t nil))

; The content-address dereference: the first statement carrying `id`.
; Mirrors `Lace.lookup` (Blocklace.lean:70) and minidregg `lookup`.
(defun fn-lace-lookup (lace id)
  (declare (xargs :guard (fn-lace-p lace)))
  (if (consp lace)
      (if (equal (fn-stmt-id (car lace)) id)
          (car lace)
        (fn-lace-lookup (cdr lace) id))
    nil))

; -----------------------------------------------------------------------------
; Merge

; The delta statements whose id is new to `lace`: `newBlocks` / `newEvents`.
(defun fn-lace-new (lace delta)
  (declare (xargs :guard (and (fn-lace-p lace) (fn-lace-p delta))))
  (if (consp delta)
      (if (member-equal (fn-stmt-id (car delta)) (fn-lace-ids lace))
          (fn-lace-new lace (cdr delta))
        (cons (car delta) (fn-lace-new lace (cdr delta))))
    nil))

(defun fn-lace-merge (lace delta)
  (declare (xargs :guard (and (fn-lace-p lace) (fn-lace-p delta))))
  (append lace (fn-lace-new lace delta)))

; -----------------------------------------------------------------------------
; Id-set order.  `a` is id-included in `b` when every statement of `a` has
; its id among the ids of `b`.  Same-ids is inclusion both ways: the CRDT
; observable of LaceMerge.lean (`laceIds`) compared as sets.

(defun fn-lace-ids-subsetp (a b)
  (declare (xargs :guard (and (fn-lace-p a) (fn-lace-p b))))
  (if (consp a)
      (and (member-equal (fn-stmt-id (car a)) (fn-lace-ids b))
           (fn-lace-ids-subsetp (cdr a) b))
    t))

(defun fn-lace-same-idsp (a b)
  (declare (xargs :guard (and (fn-lace-p a) (fn-lace-p b))))
  (and (fn-lace-ids-subsetp a b)
       (fn-lace-ids-subsetp b a)))

; Pick-a-point witness: the first statement of `a` whose id is not in `b`.
(defun fn-lace-ids-witness (a b)
  (declare (xargs :guard (and (fn-lace-p a) (fn-lace-p b))))
  (if (consp a)
      (if (member-equal (fn-stmt-id (car a)) (fn-lace-ids b))
          (fn-lace-ids-witness (cdr a) b)
        (car a))
    nil))

; -----------------------------------------------------------------------------
; Canonicity

; Every statement of `lace` that shares s's id IS s.
(defun fn-lace-no-conflictp (s lace)
  (declare (xargs :guard (and (fn-stmt-p s) (fn-lace-p lace))))
  (if (consp lace)
      (and (or (not (equal (fn-stmt-id (car lace)) (fn-stmt-id s)))
               (equal (car lace) s))
           (fn-lace-no-conflictp s (cdr lace)))
    t))

(defun fn-lace-cross-canonicalp (a b)
  (declare (xargs :guard (and (fn-lace-p a) (fn-lace-p b))))
  (if (consp a)
      (and (fn-lace-no-conflictp (car a) b)
           (fn-lace-cross-canonicalp (cdr a) b))
    t))

(defun fn-lace-canonicalp (lace)
  (declare (xargs :guard (fn-lace-p lace)))
  (fn-lace-cross-canonicalp lace lace))

; -----------------------------------------------------------------------------
; Equivocation: two distinct statements at one (creator, incarnation, sequence)

(defun fn-lace-same-slotp (a b)
  (declare (xargs :guard (and (fn-stmt-p a) (fn-stmt-p b))))
  (and (equal (fn-stmt-creator a) (fn-stmt-creator b))
       (equal (fn-stmt-incarnation a) (fn-stmt-incarnation b))
       (equal (fn-stmt-sequence a) (fn-stmt-sequence b))))

(defun fn-lace-slot-conflictp (s lace)
  (declare (xargs :guard (and (fn-stmt-p s) (fn-lace-p lace))))
  (if (consp lace)
      (or (and (not (equal (car lace) s))
               (fn-lace-same-slotp (car lace) s))
          (fn-lace-slot-conflictp s (cdr lace)))
    nil))

(defun fn-lace-equivocator-scan (rest lace principal incarnation)
  (declare (xargs :guard (and (fn-lace-p rest) (fn-lace-p lace))))
  (if (consp rest)
      (or (and (equal (fn-stmt-creator (car rest)) principal)
               (equal (fn-stmt-incarnation (car rest)) incarnation)
               (fn-lace-slot-conflictp (car rest) lace))
          (fn-lace-equivocator-scan (cdr rest) lace principal incarnation))
    nil))

(defun fn-lace-equivocatorp (lace principal incarnation)
  (declare (xargs :guard (fn-lace-p lace)))
  (fn-lace-equivocator-scan lace lace principal incarnation))

; The D10 scenario as a function: the same key, restored from a snapshot
; taken before `sequence` was used, issues two statements at one slot.
(defun fn-lace-reissue (sk creator incarnation sequence payload1 payload2)
  (declare (xargs :guard (and (fn-cbor-octet-listp payload1)
                              (fn-cbor-octet-listp payload2))))
  (list (fn-stmt-sign sk creator incarnation sequence nil :article payload1)
        (fn-stmt-sign sk creator incarnation sequence nil :article payload2)))

; -----------------------------------------------------------------------------
; Causal closure

(defthm fn-lace-stmt-preds-are-true-list
  (implies (fn-stmt-p s)
           (true-listp (fn-stmt-preds s)))
  :hints (("Goal" :in-theory (enable fn-stmt-p fn-stmt-headerp fn-stmt-predsp
                                      fn-stmt-preds))))

(defun fn-lace-ids-presentp (ids lace)
  (declare (xargs :guard (and (true-listp ids) (fn-lace-p lace))))
  (if (consp ids)
      (and (member-equal (car ids) (fn-lace-ids lace))
           (fn-lace-ids-presentp (cdr ids) lace))
    t))

(defun fn-lace-closed-inp (stmts lace)
  (declare (xargs :guard (and (fn-lace-p stmts) (fn-lace-p lace))))
  (if (consp stmts)
      (and (fn-lace-ids-presentp (fn-stmt-preds (car stmts)) lace)
           (fn-lace-closed-inp (cdr stmts) lace))
    t))

(defun fn-lace-causally-closedp (lace)
  (declare (xargs :guard (fn-lace-p lace)))
  (fn-lace-closed-inp lace lace))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2).
;
; The derived predicates (canonicality, equivocation, slot conflict)
; are withdrawn; the list recursions merge and closure induct on stay.
;
; Only the `:definition' rune is withdrawn, so type prescriptions and
; executable counterparts still decide ground terms.  A book inside this
; cluster that must open one of these enables `fn-lace-internals' locally.

; The `true-listp'/`consp' backchaining rules below are withdrawn with the
; definitions: an includer that inherits them pays for them on every goal
; shaped like a list (docs/proof-style.md section 8).

(deftheory fn-lace-internals
  '(
    (:d fn-lace-hasp)
    (:d fn-lace-same-idsp)
    (:d fn-lace-canonicalp)
    (:d fn-lace-same-slotp)
    (:d fn-lace-slot-conflictp)
    (:d fn-lace-equivocatorp)
    (:d fn-lace-reissue)
    (:d fn-lace-causally-closedp)
    fn-lace-p-implies-true-listp
    fn-lace-ids-is-true-list
    fn-lace-stmt-preds-are-true-list))

(in-theory (disable fn-lace-internals))
