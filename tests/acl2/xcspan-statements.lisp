; p-xc-span, ROUND 1 / AUDIT INPUT ONLY. No proof hints, no certification claim.
; Load books/extent-cache (including the new guard-verified definitions) first.
; Canonical review copy: tests/acl2/xcspan-statements.lisp.
(in-package "ACL2")

; K1. The subject executes lookup(kind 2), slot-token, the exact four-way
; end clamp, cached-span copy, and touch on success. The host supplies the
; selected slot's plan/window under one extent lock. The backing relation is
; the SAME PLAN/FN-EW-BUFFER in both sides; it is not inferred from a slot
; number. Its plan/token and cached ledger binding are checked by the call.
; LEDGER is the current cached ledger. RETURNED-LEDGER/WORKER describe the
; earlier returned job, before fn-pwc-cache moves its row to :cached.
; Do not use the cached ledger as RETURNED-LEDGER: :returned and :cached
; are different states. No theorem here authenticates arbitrary host memory.
;
; A positive COUNT and in-range K already imply :span; a separate :span
; antecedent would be redundant and have no hypothesis-removal witness.
(defthm fn-xc-span-at-is-the-returned-bytes
  (let* ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           fn-xcs fn-xcc fn-ew-buffer fn-ew-span))
         (token (fn-xc-slot-token (mv-nth 2 r) fn-xcs)))
    (implies
     (and (natp k)
          (< k (mv-nth 1 r))
          (equal (fn-pwr-outcome returned-ledger worker token plan) :ready))
     (and (equal (mv-nth 0 r) :span)
          (posp (mv-nth 1 r))
          (<= (mv-nth 1 r) *fn-ew-span-capacity*)
          (<= (+ p (mv-nth 1 r)) end)
          (<= (+ p (mv-nth 1 r)) plen)
          (<= (+ p (mv-nth 1 r))
              (+ (fn-prl-nth 7 token) (nth 5 plan)))
          (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan
                                          file eoff elen poff plen trailer
                                          (+ p k) fn-ew-buffer))
                 :byte)
          (equal (nth k (nth 0 (mv-nth 3 r)))
                 (mv-nth 1 (fn-pwr-byte-at returned-ledger worker token plan
                                          file eoff elen poff plen trailer
                                          (+ p k) fn-ew-buffer))))))
  :rule-classes nil)

; Owed-hit companion: a live cached candidate whose FIRST scalar octet is
; owed must produce a nonempty span. The clamp establishes the far endpoint;
; requiring that endpoint separately would hide an off-by-one clamp bug.
(defthm fn-xc-span-at-answers-an-owed-hit
  (let* ((hit (fn-xc-lookup from 2 file eoff elen poff plen 0 0 trailer p fn-xcs fn-xcc))
         (token (fn-xc-slot-token (mv-nth 1 hit) fn-xcs))
         (r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                           fn-xcs fn-xcc fn-ew-buffer fn-ew-span)))
    (implies
     (and (equal (mv-nth 0 hit) :hit)
          (fn-pwc-cachedp ledger token)
          (natp end)
          (< p end)
          (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token plan
                                          file eoff elen poff plen trailer p fn-ew-buffer))
                 :byte))
     (and (equal (mv-nth 0 r) :span)
          (posp (mv-nth 1 r))
          (equal (mv-nth 2 r) (mv-nth 1 hit)))))
  :rule-classes nil)

; Exact effects include the host's recency update, not merely the copied byte.
(defthm fn-xc-span-at-hit-touches-only-the-selected-slot
  (let ((r (fn-xc-span-at from ledger plan file eoff elen poff plen trailer p end
                         fn-xcs fn-xcc fn-ew-buffer fn-ew-span)))
    (implies (equal (mv-nth 0 r) :span)
             (and (equal (mv-nth 4 r)
                         (mv-nth 1 (fn-xc-touch (mv-nth 2 r) fn-xcs fn-xcc)))
                  (equal (mv-nth 5 r)
                         (mv-nth 2 (fn-xc-touch (mv-nth 2 r) fn-xcs fn-xcc))))))
  :rule-classes nil)

; K1 teeth sketch (round 2 will make these ground assertions):
; P = pwrtest-ready from tests/acl2/page-window-read-tests.lisp. T = (nth 0 P),
; returned-ledger = (nth 2 (nth 2 P)), worker = (nth 1 (nth 2 P)),
; plan = (nth 1 (nth 3 P)), buffer = (nth 3 (nth 3 P));
; ledger = mv-nth 2 of fn-pwc-cache(returned-ledger,worker,T,plan,*pwrtest-keep*).
; Initialize NE=0,NW=2; fn-xc-install-window T installs slot 0. Use from=0,
; file=11,eoff=100,elen=3,poff=100,plen=3,trailer=(nth 8 T),p=1,end=99,k=0.
; Assert EVERY antecedent of BOTH K1 forms, result :span,count=2,slot=0,
; dst[0]=2,dst[1]=3, the scalar results (:byte 2)/(:byte 3), all three
; endpoint bounds, capacity bound, and the exact touch effects together.
; Control: p=3 gives count=0/:miss (no byte at the exclusive window end).
; Repeat with pwrtest-request offset=1, same authenticated archive, p=1:
; source-relative zero must be copied; this catches using p as buffer index.
;
; Removal for is-the-returned-bytes (one per antecedent):
; - natp k: positive setup with p=0,k=-1; k<count and ready remain true,
;   scalar(-1) refuses while the conclusion demands :byte.
; - k<count: use k=2 with p=1,count=2; scalar(3) refuses.
; - ready: use returned-ledger=nil, retain the valid cached LEDGER;
;   span still succeeds, reference scalar returns :stale-job.
; Removal for answers-an-owed-hit (one per antecedent):
; - hit: from=1 skips sole slot 0. Logical slot-token(nil,table) is slot 0's
;   token (generated nth semantics); all other antecedents hold, result misses.
; - cachedp: use ledger before caching; returned scalar remains :byte, miss.
; - natp end: end=3/2,p=1; remaining antecedents hold, composition rejects.
; - p<end: end=p=1; remaining antecedents hold, empty request misses.
; - scalar :byte: p=3,end=99 with same candidate/cached row; lookup finds it
;   (lookup checks START, not the window end) but composition must miss.
; Additional clamp control: a published window [0,capacity), plen=capacity+1,
; p=1,end=plen, using the same return/cache/install protocol. Removing ONLY
; the window-end clamp makes fn-pwc-span-at refuse and violates the owed hit.
; Mutations refuted: remove the window-end clamp and bypass span's bounds
; (count reaches 3 when p=1; k=2 fails K1), copy from buffer[p] for an offset-1
; window, omit touch (effects), or always miss (owed-hit companion).

; K2. fn-xc-token-disjointp excludes NIL tokens and compares the actual
; slot-token projections, across ALL rows, not merely a kind's region.
; fn-xc-holds includes a non-NIL token and valid slot index. Consequently
; two distinct live/tokp slots cannot bind the same cached ledger row.
(defthm fn-xc-held-token-has-one-slot
  (implies (and (fn-xc-token-disjointp fn-xcs)
                (fn-xc-holds i token fn-xcs)
                (fn-xc-holds k token fn-xcs))
           (equal i k))
  :rule-classes nil)

(defthm fn-xc-touch-preserves-token-disjointp
  (implies (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc)
                (fn-xc-token-disjointp fn-xcs))
           (fn-xc-token-disjointp (mv-nth 1 (fn-xc-touch i fn-xcs fn-xcc))))
  :rule-classes nil)

(defthm fn-xc-free-preserves-token-disjointp
  (implies (and (fn-xcsp fn-xcs) (natp i) (fn-xc-token-disjointp fn-xcs))
           (fn-xc-token-disjointp (mv-nth 2 (fn-xc-free i fn-xcs))))
  :rule-classes nil)

(defthm fn-xc-yield-preserves-token-disjointp
  (implies (and (fn-xcsp fn-xcs) (fn-xccp fn-xcc)
                (fn-xc-token-disjointp fn-xcs))
           (fn-xc-token-disjointp (mv-nth 3 (fn-xc-yield fn-xcs fn-xcc))))
  :rule-classes nil)

; FALSE: well-formed table alone implies disjointness, and FALSE: the current
; fn-xc-install / fn-xc-write preserve it. These exact ground counterexamples
; are theorem statements of the FAILURE, not knowingly false preservation.
; row order: kind tokp tid tcid file eoff elen a b c d start trailer stamp.
(defthm fn-xc-install-can-duplicate-a-charged-window
  (let* ((before '((2 t 7 0 11 100 3 100 3 0 0 0 77 0)
                   (0 nil 0 0 0 0 0 0 0 0 0 0 0 0)))
         (cells '(1 0 2))
         (r (fn-xc-install 2 t 7 0 11 100 3 100 3 1 0 0 77 before cells)))
    (and (fn-xcsp before) (fn-xccp cells) (fn-xc-readyp before cells)
         (fn-xc-token-disjointp before)
         (equal (mv-nth 0 r) :installed) (equal (mv-nth 1 r) 1)
         (fn-xcsp (mv-nth 3 r)) (fn-xc-readyp (mv-nth 3 r) (mv-nth 4 r))
         (equal (fn-xc-slot-token 0 (mv-nth 3 r)) '(:window 7 11 100 3 100 3 0 77))
         (equal (fn-xc-slot-token 1 (mv-nth 3 r)) '(:window 7 11 100 3 100 3 0 77))
         (not (fn-xc-token-disjointp (mv-nth 3 r)))))
  :rule-classes nil)

(defthm fn-xc-write-can-duplicate-a-charged-window
  (let* ((before '((2 t 7 0 11 100 3 100 3 0 0 0 77 0)
                   (0 nil 0 0 0 0 0 0 0 0 0 0 0 0)))
         (after (fn-xc-write 1 2 t 7 0 11 100 3 100 3 0 0 0 77 1 before)))
    (and (fn-xcsp before) (fn-xc-token-disjointp before)
         (fn-xc-write-okp 1 2 t 7 0 11 100 3 100 3 0 0 0 77 1 before)
         (fn-xcsp after)
         (equal (fn-xc-slot-token 0 after) (fn-xc-slot-token 1 after))
         (not (fn-xc-token-disjointp after))))
  :rule-classes nil)

; K2 teeth sketch:
; Positive: the BEFORE table above, token '(:window 7 11 100 3 100 3 0 77),
; i=k=0 satisfies all three antecedents and equality. Add a second charged
; row with tid=8,start=1 and assert invariant and unequal tokens at slots 0 and 1;
; both tokens are held, so this is not an empty-table witness.
; Removal disjointp: AFTER from either ground counterexample, i=0,k=1.
; Removal holds(i): positive before, i=1,k=0 (slot 1 free).
; Removal holds(k): positive before, i=0,k=1.
; Mutation: make install compare the full descriptor (current behavior)
; instead of excluding a duplicate charge; the ground counterexample trips.
; Preservation controls: touch each live slot, free a live slot, free an
; already-free slot, yield with whole-entry priority then window priority,
; and yield an empty table. Assert the invariant BEFORE and AFTER each.
;
; MINIMAL FIX FOR ROUND 2 (not implemented in this statement round):
; At install's write branch, reject a non-NIL proposed token already held in
; ANY slot other than the selected victim. Keep the ordinary :present path.
; Use :refused for a token conflict, preserving existing non-refused lookup
; statements; do not treat a different descriptor as :present. This must
; use slot-token's encoding, not introduce a parallel token codec.
; fn-xc-write is an unchecked primitive: its preservation contract needs the
; same "new token absent outside I" precondition, carried by install; either
; strengthen its guard/callers or keep it internal and prove the conditional
; theorem. No unconditional preservation theorem is true for today's write.
; Checking only c=d=0 on new raw-window installs is NOT sufficient for the
; stated domain: an existing well-formed row may already have c=1, or be in
; the wrong region. A stronger canonical/partition invariant is an alternate
; design, not an implicit property of fn-xcsp/fn-xc-readyp.

; Round-1 evaluation (persvati, p-xc-span-defs): the four new definitions
; admitted, with verify-guards confirming each already guard-verified.
; K2's exact install/write transitions above were evaluated: invariant T
; before, NIL after; table/cells remain well-formed and ready, both tokens
; (:window 7 11 100 3 100 3 0 77). A second token with tid=8,start=1 instead
; preserves disjointness and is held at slot 1 (nonempty positive control).
; K1's joint satisfiability was also evaluated with a synthetic model fixture:
; token = (:window 7 11 100 3 100 3 0 77),
; plan = (:verified 11 100 3 0 3 77 0 7 47 TOKEN 100 3 0),
; worker = (0 7 :returned TOKEN), buffer prefix = (1 2 3),
; returned-ledger = (nil nil nil ((TOKEN (16 0 0 0 0) :window :returned 0)) nil),
; cached-ledger = (nil nil nil ((TOKEN (16 0 0 0 0) :cached nil)) nil).
; Slot 0 holds TOKEN. p=1,end=99: outcome :ready, cachedp T, lookup (:hit 0),
; scalars (:byte 2)/(:byte 3), composition (:span 2 0 ...), destination (2 3).
; p=3,end=99: (:miss 0 0 ...). This evaluates the model predicate, NOT an
; authenticated publication; the pwrtest-ready teeth above supply that path.
; No proposed defthm in this file has been submitted for proof.
