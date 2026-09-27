; Composite acceptance grows both the real Store and the carried statement
; index.  The statement bytes below come from the signed article witness;
; the hybrid observations exercise the Store codec and replay route, not the
; native cryptographic primitives.
(in-package "ACL2")
(include-book "store-node-index-tests")
(include-book "../../books/hybrid-store")
(include-book "std/testing/must-fail" :dir :system)

(defconst *sni-hybrid-principal* (make-list 32 :initial-element 7))
(defconst *sni-hybrid-ed-key* (make-list 32 :initial-element 11))
(defconst *sni-hybrid-ml-key* (make-list 1952 :initial-element 13))
(defconst *sni-hybrid-keys*
  (list (cons :ed25519 *sni-hybrid-ed-key*)
        (cons :ml-dsa-65 *sni-hybrid-ml-key*)))
(defconst *sni-hybrid-signatures*
  (list (cons :ed25519 (make-list 64 :initial-element 17))
        (cons :ml-dsa-65 (make-list 3309 :initial-element 19))))
(make-event
 `(defconst *sni-hybrid-snapshot*
    ',(fn-hsig-keyring-snapshot *sni-hybrid-principal* *sni-hybrid-keys*)))
(make-event
 `(defconst *sni-hybrid-enrollment*
    ',(fn-hsig-keyring-event 0 0 0 1 *sni-hybrid-principal* *sni-hybrid-keys*)))

(defun fn-sni-commit-identity (s event)
  (fn-sn-finish
   (fn-sni-publish (fn-sn-prepare-identity (fn-sni-reserve s) event))))

(make-event
 `(defconst *sni-composite-enrolled*
    ',(fn-sni-commit-identity (fn-sn-initial *sni-groups* 32)
                               *sni-hybrid-enrollment*)))
(make-event
 `(defconst *sni-composite-keyed*
    ',(fn-sni-set-keyring *sni-composite-enrolled* *sni-keyring*
                          (list *sni-hybrid-enrollment*))))
(assert-event (fn-sn-indexedp *sni-composite-keyed*))

(make-event
 `(defconst *sni-composite-record*
    ',(fn-record-make 1 1 1 "<sni@example>" *sni-octets* *sni-groups*
                      "sni-pin" "sni-content" "sni-release" 2 841000000)))
(make-event
 `(defconst *sni-composite-event*
    ',(fn-hsig-authorized-article-event
       1 1 1 1 *sni-hybrid-snapshot* "<sni@example>"
       (fn-record-string-octets "sni-content")
       (fn-record-encode-impl *sni-composite-record*)
       *sni-hybrid-principal* *sni-hybrid-keys* *sni-octets*
       *sni-hybrid-signatures* *sni-hybrid-ml-key*
       :verified :verified)))
(assert-event (fn-stxa-bindsp *sni-composite-event*))
(assert-event (equal (fn-stx-delta *sni-octets* *sni-keyring*)
                     (list *sni-stmt*)))

; The store retains the composite ROW (records-flip): the entry interns the
; wire composite after the enrollment under the store's keyring and
; generation, its article at handle 0 of this run's arena
; (tests/acl2/store-node-index-tests fn-sni-row, over store-intern's
; fn-intern-event); the keyring above went in through the entry
; fn-store-set-keyring over the same arena.
(defconst *sni-composite-prior* (list *sni-hybrid-enrollment*))
(make-event
 `(defconst *sni-composite-row*
    ',(fn-sni-row *sni-composite-prior* *sni-composite-event*
                  (fn-sn-keyring *sni-composite-keyed*)
                  (fn-sn-keyring-generation *sni-composite-keyed*))))
(assert-event (fn-hstxa-p *sni-composite-row*))
(assert-event (equal (fn-hstxa-stxa *sni-composite-row*) *sni-composite-event*))
(make-event
 `(defconst *sni-composite-completing*
    ',(fn-sni-publish
       (fn-sn-prepare-identity (fn-sni-reserve *sni-composite-keyed*)
                               *sni-composite-row*))))
(assert-event (fn-sn-completion-enabledp *sni-composite-completing*))
(assert-event (fn-sn-indexedp *sni-composite-completing*))
(assert-event
 (equal (fn-sn-statement-lookup *sni-composite-completing*
                                (fn-stmt-id *sni-stmt*))
        nil))
(make-event
 `(defconst *sni-composite-finished*
    ',(fn-sn-finish *sni-composite-completing*)))
(assert-event (fn-sn-indexedp *sni-composite-finished*))
(assert-event (equal (len (fn-stx-store (fn-sn-node *sni-composite-finished*)))
                     1))
; by specification: the flip: the accepted article's payload is its handle
; (0, the run's first sealed payload); the bytes under it are the signed
; article's octets.
(assert-event
 (equal (fn-article-payload
         (car (fn-stx-store (fn-sn-node *sni-composite-finished*))))
        0))
(assert-event
 (equal (fn-sni-bytes (list *sni-hybrid-enrollment* *sni-composite-event*)
                      (fn-article-payload
                       (car (fn-stx-store (fn-sn-node *sni-composite-finished*)))))
        *sni-octets*))
(assert-event
 (equal (fn-stx-index-bindings (fn-sn-index *sni-composite-finished*))
        (fn-stx-index-bindings (fn-sn-index *sni-finished*))))
(assert-event
 (equal (len (fn-stx-index-bindings (fn-sn-index *sni-composite-finished*)))
        1))
(assert-event
 (equal (fn-sn-statement-lookup *sni-composite-finished*
                                (fn-stmt-id *sni-stmt*))
        *sni-stmt*))
; by specification: the flip: the node's articles hold handles, so the lace
; of the store's bytes is read through the arena (fn-sni-lace), as in
; store-node-index-tests.
(assert-event
 (equal (fn-sn-statement-lookup *sni-composite-finished*
                                (fn-stmt-id *sni-stmt*))
        (fn-lace-lookup (fn-sni-lace *sni-composite-finished*
                                     (fn-sn-keyring *sni-composite-finished*)
                                     (list *sni-hybrid-enrollment* *sni-composite-event*))
                        (fn-stmt-id *sni-stmt*))))

; The indexedp premise matters: a completing state with a well-shaped index
; that already includes an unrelated second statement remains stale.
(make-event
 `(defconst *sni-composite-stale*
    ',(fn-sn-update-indexed
       *sni-composite-completing*
       (fn-sn-files *sni-composite-completing*)
       (fn-sn-node *sni-composite-completing*)
       (fn-sn-index *sni-forked*))))
(assert-event (fn-sn-statep *sni-composite-stale*))
(assert-event (not (fn-sn-indexedp *sni-composite-stale*)))
(assert-event (not (fn-sn-indexedp (fn-sn-finish *sni-composite-stale*))))
(must-fail
 (assert-event (fn-sn-indexedp (fn-sn-finish *sni-composite-stale*))))

; -----------------------------------------------------------------------------
; PRF-023's served queries over the arena (books/store-intern.lisp
; fn-store-statement-lookup-is-the-lace-lookup and
; fn-store-equivocatorp-is-the-lace-equivocator).  Each has two hypotheses:
; the carried index (fn-sn-indexedp) and the context invariant of the indexed
; rows over the arena (fn-rows-contexts-okp at the store's keyring and a
; generation).  The store below is reached by the entries: the composite run
; above, then a second signed article at the same slot (the fork of
; store-node-index-tests, *sni-octets-2*) interned after it as a held row at
; handle 1.  So the history holds a COMPOSITE row and an ARTICLE row, and the
; equivocator question is true on it, not NIL on both sides.

(make-event
 `(defconst *sni-composite-fork-record*
    ',(fn-record-make 2 2 2 "<sni3@example>" *sni-octets-2* *sni-groups*
                      "sni-pin-3" "sni-content-3" "sni-release-3" 2 841000000)))
(assert-event (fn-record-p *sni-composite-fork-record*))
(defconst *sni-composite-arena-prior*
  (list *sni-hybrid-enrollment* *sni-composite-event*))
(make-event
 `(defconst *sni-composite-forked*
    ',(fn-sn-finish
       (fn-sni-publish
        (fn-sni-prepare (fn-sni-reserve *sni-composite-finished*)
                        *sni-composite-arena-prior* *sni-composite-fork-record*)))))
(defconst *sni-composite-fork-prior*
  (append *sni-composite-arena-prior* (list *sni-composite-fork-record*)))
(assert-event (equal (fn-sf-phase (fn-sn-files *sni-composite-forked*)) :ready))
(assert-event (equal (len (fn-sf-records (fn-sn-files *sni-composite-forked*))) 3))
(assert-event (fn-hstxa-p (nth 1 (fn-sf-records (fn-sn-files *sni-composite-forked*)))))
(assert-event (fn-held-p (nth 2 (fn-sf-records (fn-sn-files *sni-composite-forked*)))))
(assert-event (equal (fn-record-payload (nth 2 (fn-sf-records (fn-sn-files *sni-composite-forked*))))
                     1))

; Both keystones' sides over an arena: the arena is the one holding the
; payloads of PRIOR (the run's interns, in order); the generation is the
; store's.  One call answers the two hypotheses and both sides of each
; conclusion.
(defun fn-sni-served-in (s prior id creator incarnation fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (rows fn-arena)
    (fn-intern-events prior nil 0 fn-arena)
    (declare (ignore rows))
    (let ((articles (fn-rows-articles-newest-first (fn-sn-indexed-rows s) fn-arena)))
      (mv (list (fn-sn-indexedp s)
                (fn-rows-contexts-okp (fn-sn-indexed-rows s) (fn-sn-keyring s)
                                      (fn-sn-keyring-generation s) fn-arena)
                (fn-sn-statement-lookup s id)
                (fn-lace-lookup (fn-stx-lace-of-store articles (fn-sn-keyring s)) id)
                (fn-sn-equivocatorp s creator incarnation)
                (fn-lace-equivocatorp (fn-stx-lace-of-store articles (fn-sn-keyring s))
                                      creator incarnation))
          fn-arena))))

(defun fn-sni-served (s prior id creator incarnation)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (out fn-arena)
      (fn-sni-served-in s prior id creator incarnation fn-arena)
      out)))

; REACHABLE POSITIVE WITNESS (both keystones).  Antecedent: the carried
; index and the context invariant hold.  Conclusion: the lookup answers the
; second statement, which only the arena's handle 1 carries, on both sides;
; the equivocator question is T on both sides.
(make-event
 `(defconst *sni-served*
    ',(fn-sni-served *sni-composite-forked* *sni-composite-fork-prior*
                     (fn-stmt-id *sni-stmt-2*) *sni-creator* 1)))
(assert-event (equal (nth 0 *sni-served*) t))
(assert-event (equal (nth 1 *sni-served*) t))
(assert-event (equal (nth 2 *sni-served*) *sni-stmt-2*))
(assert-event (equal (nth 3 *sni-served*) *sni-stmt-2*))
(assert-event (equal (nth 4 *sni-served*) t))
(assert-event (equal (nth 5 *sni-served*) t))
; The composite's statement too, on both sides.
(make-event
 `(defconst *sni-served-1*
    ',(fn-sni-served *sni-composite-forked* *sni-composite-fork-prior*
                     (fn-stmt-id *sni-stmt*) *sni-creator* 1)))
(assert-event (and (nth 0 *sni-served-1*) (nth 1 *sni-served-1*)
                   (equal (nth 2 *sni-served-1*) *sni-stmt*)
                   (equal (nth 3 *sni-served-1*) *sni-stmt*)))

; HYPOTHESIS REMOVAL, fn-sn-indexedp (CORRUPTED STATE: the forked store with
; its carried index replaced by the empty one; no transition reaches it).
; Retained: the context invariant still holds (the rows are unchanged).
; Omitted: fn-sn-indexedp fails.  Conclusion: fails for both keystones (the
; store answers NIL where the lace answers the statement and T).
(make-event
 `(defconst *sni-composite-forked-stale*
    ',(fn-sn-update-indexed *sni-composite-forked*
                            (fn-sn-files *sni-composite-forked*)
                            (fn-sn-node *sni-composite-forked*)
                            (fn-stx-index-empty))))
(make-event
 `(defconst *sni-served-stale*
    ',(fn-sni-served *sni-composite-forked-stale* *sni-composite-fork-prior*
                     (fn-stmt-id *sni-stmt-2*) *sni-creator* 1)))
(assert-event (fn-sn-statep *sni-composite-forked-stale*))
(assert-event (equal (nth 1 *sni-served-stale*) t))
(assert-event (equal (nth 0 *sni-served-stale*) nil))
(assert-event (equal (nth 3 *sni-served-stale*) *sni-stmt-2*))
(assert-event (equal (nth 5 *sni-served-stale*) t))
(must-fail
 (assert-event (equal (nth 2 *sni-served-stale*) (nth 3 *sni-served-stale*))))
(must-fail
 (assert-event (iff (nth 4 *sni-served-stale*) (nth 5 *sni-served-stale*))))

; HYPOTHESIS REMOVAL, fn-rows-contexts-okp (MIS-PAIRED ARENA: the reachable
; forked store read through the arena as it stood BEFORE the fork's seal, so
; handle 1 is outside it; the host never pairs a store with an older arena).
; Retained: fn-sn-indexedp holds.  Omitted: the context invariant fails (the
; article row's context is of bytes the arena does not hold).  Conclusion:
; fails for both keystones (the store answers the second statement and T; the
; lace, without handle 1's bytes, answers NIL and NIL).
(make-event
 `(defconst *sni-served-short*
    ',(fn-sni-served *sni-composite-forked* *sni-composite-arena-prior*
                     (fn-stmt-id *sni-stmt-2*) *sni-creator* 1)))
(assert-event (equal (nth 0 *sni-served-short*) t))
(assert-event (equal (nth 1 *sni-served-short*) nil))
(assert-event (equal (nth 2 *sni-served-short*) *sni-stmt-2*))
(assert-event (equal (nth 4 *sni-served-short*) t))
(must-fail
 (assert-event (equal (nth 2 *sni-served-short*) (nth 3 *sni-served-short*))))
(must-fail
 (assert-event (iff (nth 4 *sni-served-short*) (nth 5 *sni-served-short*))))
