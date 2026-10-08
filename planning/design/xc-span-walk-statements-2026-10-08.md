# fn-xc-span-at walks the candidates in one call: statements (lane p-xc-span round 4)

Statements before proofs. Admitted shapes (REPL xcs5, persvati, no certificate): the stobjs, fn-xc-span-row and the walking fn-xc-span-at. Everything under "Statements" is owed.

## Stobj shape (books/extent-cache-span.lisp; fn-xcs and its statements untouched)

    (defstobj fn-xcw-win                                  ; one slot's backing window
      (fn-xcw-win-bytes :type (array (unsigned-byte 8) (262144)) :initially 0)   ; profile :read-window-octets
      :inline t :congruent-to fn-ew-buffer)             ; so fn-pwc-span-at and every fn-pwr-* theorem apply to it unchanged
    (defstobj fn-xcw                                      ; the host's (plan . window) per slot, now ACL2's
      (fn-xcw-plans :type (array t (8)) :initially nil)   ; profile :extent-cache-windows
      (fn-xcw-wins  :type (array fn-xcw-win (8))))

Row of slot s is (- s NE) = (fn-xc-row s fn-xcc), the window region [NE, NE+NW). Premise "rows cover the region": NW <= (fn-xcw-plans-length fn-xcw); the host's init must hold it (fn-xc-init already refuses NW above 32; the row count is the profile figure 8). Logical readers: (fn-xcw-plan row fn-xcw) = (nth row (nth 0 fn-xcw)), (fn-xcw-window row fn-xcw) = (nth row (nth 1 fn-xcw)).

## Signatures

    (fn-xc-span-at from ledger file eoff elen poff plen trailer p end
                   fn-xcs fn-xcc fn-xcw fn-ew-span)
      -> (mv word count slot fn-ew-span fn-xcs fn-xcc)       ; word :span or :miss. PLAN and FN-EW-BUFFER arguments are gone (ACL2 reads the slot's row).
    (fn-xc-install-window-bytes token plan fn-xcs fn-xcc fn-xcw fn-ew-buffer)
      -> (mv word slot evicted fn-xcs fn-xcc fn-xcw)         ; fn-xc-install-window, then on :installed or :replaced: row plan := PLAN, window prefix := the first min(plan[5], 262144) octets of fn-ew-buffer (the staging window the cold read just filled)

fn-xc-install, fn-xc-install-window, fn-xc-free, fn-xc-yield are unchanged. Yield and free leave their rows: lookup selects only live slots and install rewrites the pair, so a stale row is unreachable (stated as a theorem, below).

The walk: lookup from FROM selects slot s; try s (plan row, token, j = min(end, plen, p+capacity, token start + plan[5]), then fn-pwc-span-at on the slot's own window); on :span touch s and answer; otherwise continue from s+1; measure = slot count - from; :miss only when no later candidate exists.

## Statements (all with ATLAS fields: satisfiable witness, removal witness per hypothesis, in tests/acl2/extent-cache-span-tests.lisp)

Let R = (fn-xc-span-at from ledger file eoff elen poff plen trailer p end slots cells wins dst), S = (mv-nth 2 R), row = (fn-xc-row S cells), token = (fn-xc-slot-token S slots), plan = (fn-xcw-plan row wins), window = (fn-xcw-window row wins).

C1 `fn-xc-span-at-answers-a-covered-slot` (completeness). Premises: (fn-xc-readyp slots cells); i natp, from <= i, NE <= i < NE+NW; (fn-xc-slot-matchp i nil 2 file eoff elen poff plen 0 0 trailer p slots); with token_i, plan_i, window_i the slot i's: (fn-pwc-cachedp ledger token_i); (natp p) (natp end) (< p end) (natp plen) (natp from); (<= NW (fn-xcw-plans-length wins)); (equal (mv-nth 0 (fn-pwr-byte-at returned-ledger worker token_i plan_i file eoff elen poff plen trailer p window_i)) :byte). Conclusion: word :span, count posp, from <= S <= i, and S is a live kind-2 slot matching the descriptor at p.

C2 `fn-xc-span-at-is-the-returned-bytes` (soundness, the old statement for the slot that answered). Premises (natp k) (< k count) (equal (fn-pwr-outcome returned-ledger worker token plan) :ready); conclusion exactly the old one with plan and window read from S's row: word :span, count posp and <= capacity, p+count <= end, <= plen, <= token start + plan[5], byte-at :byte at p+k, and (nth k (nth 0 (mv-nth 3 R))) = that byte. The old three-argument statement is this one with PLAN and WINDOW equal to S's row, so it follows by instantiation.

C2b `fn-xc-span-at-answers-from-a-matching-slot`: word :span implies from <= S < (fn-xcs-count slots), (fn-xc-slot-matchp S nil 2 file eoff elen poff plen 0 0 trailer p slots), and the slot's token is cached in LEDGER.

C3 `fn-xc-span-at-hit-touches-only-the-selected-slot` (unchanged): word :span implies slots' and cells' are (mv-nth 1/2 (fn-xc-touch S slots cells)). New companion `fn-xc-span-at-miss-changes-nothing`: word :miss implies slots' = slots, cells' = cells.

I1 `fn-xc-install-window-bytes-installs-the-table-decision`: (mv-nth 0..4) equal fn-xc-install-window's, so every fn-xc install statement applies to the table unchanged.
I2 `fn-xc-install-window-bytes-stores-the-pair`: word :installed or :replaced implies row(slot) plan = PLAN, window octet j = fn-ew-buffer octet j for j < min(plan[5],capacity), every other row's plan and window untouched. Otherwise (:present :refused :duplicate) fn-xcw is unchanged.
I3 `fn-xc-freed-or-yielded-row-is-unreachable`: after fn-xc-free or fn-xc-yield of s, fn-xc-lookup of kind 2 never answers s (the row's stale pair cannot be selected).

## Teeth (tests/acl2/extent-cache-span-tests.lisp)

Positive: S's counterexample (window [0,C) at slot 0, [C,C+3) at slot 1, request p=C) answers :span from slot 1 in one call; end-to-end through fn-xc-install-window-bytes then fn-xc-span-at. One removal witness per C1 hypothesis (cached, byte, p<end, region, row cover, matching descriptor). Must-fail mutation: fn-xc-span-at-first-candidate-only (no continuation) answers :miss on that witness, checked with must-fail-checked.
