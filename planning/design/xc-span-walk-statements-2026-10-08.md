# fn-xc-span-at walks the candidates in one call (lane p-xc-span round 4)

Present state, certified on persvati (run-20261008T170104Z-4746). The statements below are in books/extent-cache-span.lisp; the teeth are in tests/acl2/extent-cache-span-tests.lisp.

## Stobj shape

    (defstobj fn-xcw-win (fn-xcw-win-bytes (array (unsigned-byte 8) (262144)) :initially 0) :inline t :congruent-to fn-ew-buffer)
    (defstobj fn-xcw (fn-xcw-plans (array t (8))) (fn-xcw-wins (array fn-xcw-win (8))))

Sizes are the profile figures (:read-window-octets, :extent-cache-windows). Row of slot s is (fn-xc-row s cells) = s - NE. fn-xcs and every earlier fn-xc statement are unchanged.

## Exports

    (fn-xc-span-at from ledger file eoff elen poff plen trailer p end fn-xcs fn-xcc fn-xcw fn-ew-span)
      -> (mv word count slot fn-ew-span fn-xcs fn-xcc)       ; :span or :miss
    (fn-xc-install-window-bytes token plan fn-xcs fn-xcc fn-xcw fn-ew-buffer)
      -> (mv word slot evicted fn-xcs fn-xcc fn-xcw)         ; the table decision of fn-xc-install-window, then plan and staged window stored with the slot
    (fn-xc-init-windows ne nw fn-xcs fn-xcc) -> (mv word fn-xcs fn-xcc)   ; :refused-window-rows when nw exceeds the fn-xcw row count

The walk: lookup from FROM selects slot s; try s's own plan and window (fn-xc-span-row); on :span touch s and answer; otherwise continue from s+1; :miss with slot nil when no later candidate exists. Measure: slot count - from.

## Keystones

- C1 fn-xc-span-at-answers-a-covered-slot: any live kind-2 slot i >= from matching the descriptor at p, token cached, plan a true list, supplying the octet at p, with p < end and NW within the row count, makes the call answer :span from a slot in [from, i].
- C2 fn-xc-span-at-is-the-returned-bytes: the old statement with plan and window read from the answering slot's row.
- fn-xc-span-at-answers-from-a-matching-slot: :span implies the slot matches the descriptor, is at or after FROM, is cached, and its row plan matches its token.
- fn-xc-span-at-hit-touches-only-the-selected-slot: stamps and clock are those of touching the answered slot (a miss names no slot and touches none); fn-xc-span-at-miss-changes-nothing.
- fn-xc-span-at-answers-an-owed-hit: the first-candidate case of C1, answered slot equal to the first candidate.
- fn-xc-span-at-never-answers-a-freed-slot.
- fn-xc-install-window-bytes-installs-the-table-decision, -stores-the-pair, -leaves-other-rows, -keeps-the-rows-unless-it-installs.
- fn-xc-init-windows-refuses-more-windows-than-rows, fn-xc-init-windows-readies-the-rows (its admitted state implies C1's NW bound).

Premises the host path discharges: readiness and the NW bound by fn-xc-init-windows; the stored plan by fn-xc-install-window-bytes; the installed slot lies in the window region (fn-xc-install-placement).

## Round 5 — all backing kinds, statements and signatures (5a)

Candidate definitions: `books/extent-cache-storage.lisp`. This round admits
representations, functions, termination and guards only. The keystones below
are **statements for P/S review, not proved events or certification claims**.
Every round-4 statement and `books/extent-cache.lisp` is unchanged. No native
file changes. The two window kinds share the same NW slots and backing rows;
allocating a second NW bank would double the window reservation unnecessarily.

### The host values being replaced

`host/native/extent.lisp:1411,1528,1770-1819`: kind 1 holds an unsigned-byte-8
vector of **ELEN + 32** bytes: the verified entry prefix followed by its frame
trailer. Consumers read payload byte `POFF - EOFF + i`, successive bytes of a
span, or the whole payload. There is no independent entry-size ceiling in
this design. The new read exports bounded spans; scalar requests use END=p+1,
and full-payload consumers resume at p+count. They must consume ACL2's count,
not rederive coordinates or truncate the payload to one span.

`host/native/extent-decoded.lisp:185-253`: kind 3 currently moves job child 7
(the decoded `fn-ew-buffer`), drops the controller and inserts PLAN=NIL.
Capture **Z = fn-dwa-controller of the job's fn-pww-carry before retirement**.
Z is the full decoded controller, not `(nth 1 z)`, which is its raw controller.
`fn-pwz-token-window-length` defines its readable extent (currently at most
16384); buffer storage remains the profile's 262144 octets. The existing
owner cache copier at `host/page-decoded-window-host.lisp:176` calls exactly
`fn-pwz-cache-span-at` with the live owner ledger; the proposed row copier
calls that same book function. No owner/host book is included by this book.

### Exact representation declarations

Existing declarations remain, with no new `def-representation` table and no
hand-written replacement for S's generated `fn-xcs`/`fn-xcc`:

```lisp
(defstobj fn-xcw-win
  (fn-xcw-win-bytes :type (array (unsigned-byte 8) (262144)) :initially 0)
  :inline t :congruent-to fn-ew-buffer)
(defstobj fn-xcw
  (fn-xcw-plans :type (array t (8)) :initially nil)
  (fn-xcw-wins :type (array fn-xcw-win (8))))

(def-buffer fn-xce-entry :view t)
(def-buffer fn-xce-stage :view t)
(defmacro fn-xce-define ()
  `(defstobj fn-xce
     (fn-xce-keys :type (array t (,(fn-profile-limit :extent-cache-entries))) :initially nil)
     (fn-xce-entries :type (array fn-xce-entry (,(fn-profile-limit :extent-cache-entries))))))
(fn-xce-define)
```

The first two forms show the existing profile expansion; their source macros
read `:read-window-octets` and `:extent-cache-windows`. New entry rows are
exactly `:extent-cache-entries` (8). Each generated buffer is congruent to
`fn-octets`: growable octet array plus fill, logically an octet list. It starts
empty rather than reserving the maximum entry size in each row. Entry row is
slot s; window row is s-NE. Entry key is `(list 1 file eoff elen trailer token)`;
including the descriptor is essential because offline entries have NIL tokens.
Kind 2 stores its raw plan; kind 3 stores Z in the same plans array. A decoded
hit requires `fn-xc-decoded-planp Z slot-token`: true-list shapes, full token
match, publication, and decoded count equal to the token window length within
the profile buffer. Thus a leftover raw plan or NIL cannot produce a decoded
hit. The existing raw hit continues to check its own plan/token relation.

### Exact exports and words

```lisp
(fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end
                       fn-xcs fn-xcc fn-xcw fn-ew-span)
  ; -> (mv word count slot fn-ew-span fn-xcs fn-xcc) ; :span | :miss
(fn-xc-entry-span-at from file eoff elen poff plen trailer p end
                     fn-xcs fn-xcc fn-xce fn-ew-span)
  ; -> (mv word count slot fn-ew-span fn-xcs fn-xcc) ; :span | :miss
(fn-xc-install-decoded-bytes token z fn-xcs fn-xcc fn-xcw fn-ew-buffer)
  ; -> (mv word slot evicted fn-xcs fn-xcc fn-xcw)
(fn-xc-install-entry-bytes file eoff elen trailer token fn-xcs fn-xcc fn-xce fn-xce-stage)
  ; -> (mv word slot evicted fn-xcs fn-xcc fn-xce fn-xce-stage)
(fn-xc-init-all ne nw fn-xcs fn-xcc)
  ; -> (mv word fn-xcs fn-xcc)
```

Reads walk increasing slot indices from FROM (host passes 0), visit each once,
continue after a non-covering or stale row, and touch only the answering slot.
Count is positive and at most `*fn-ew-span-capacity*`. Entry payload bounds
are checked in ACL2. Decoded J is `fn-xc-span-end p end decoded token-start
(fn-pwz-token-window-length token)`. Entry J is `min(end,plen,p+capacity)`.
No candidate hit is a promise that the backing row can answer.

Installs preserve the table's words (`:installed`, `:replaced`, `:present`,
`:duplicate`, `:refused`, as reachable from its current decision).
Extra preflight words: `:refused-entry-rows`, `:refused-entry-length`,
`:refused-window-rows`, `:refused-decoded-plan`. Preflight failures return
NIL slot/victim and every input state unchanged. Only installed/replaced
stores backing. Decoded installation copies exactly the token's decoded
window length, keeps the staged buffer, and stores Z. Entry installation
swaps the entire staged buffer into the chosen row in constant work; the
stage receives that row's previous buffer, and the existing table result
names the victim charge. Present/duplicate/refused leaves backing and stage
untouched. **Neither installation authenticates arbitrary supplied bytes**:
its theorem preserves the already verified producer's bytes.

Init refuses NE above entry rows first, then NW above the shared window rows;
otherwise it returns `fn-xc-init`'s `:initialized`, `:already` or `:refused`.
Nonnaturals are refused by the table. No separate decoded count exists because
kind-2 and kind-3 occupancy share NW. Fresh backing must be paired with fresh
tables. Init changes only the tables; stale backing is harmless under the
row checks, but S must not replace backing under an already live table.

### Exact keystone statements for the next round

Notation here is textual substitution, not additional hypotheses. `R3` is
the full decoded export call above using logical variables `slots cells wins
dst` for its four stobjs; `R1` is the entry export call using `slots cells
entries dst`. `s = (mv-nth 2 Rk)`, `n = (mv-nth 1 Rk)`, `out = (mv-nth 3 Rk)`.
`T(i) = (fn-xc-slot-token i slots)`, `W(i) = (fn-xcw-window
(fn-xc-row i cells) wins)`, `Z(i) = (fn-xcw-plan (fn-xc-row i cells) wins)`;
`E(i) = (nth i (nth 1 entries))`, `K(i) = (nth i (nth 0 entries))`.
`G3` is `(and (fn-xcsp slots) (fn-xccp cells) (fn-xc-readyp slots cells)
(fn-xcwp wins) (natp from) (natp p) (natp end) (natp decoded))`.
`G1` replaces win recognizer by `(fn-xcep entries)` and adds natural EOFF,
ELEN, POFF, PLEN instead of DECODED. All displayed implications are universally
quantified ACL2 `implies` statements with `:rule-classes nil`.

* **fn-xc-decoded-span-at-answers-a-covered-slot**:
  G3, natp i, FROM <= i, NE <= i < NE+NW, NW <= window-row-count,
  `(fn-xc-slot-matchp i nil 3 file eoff elen poff compressed decoded dict-id trailer p slots)`,
  `(fn-xc-decoded-planp Z(i) T(i))`, p < end, and
  `(equal (mv-nth 0 (fn-pwz-cache-byte-at ledger T(i) file eoff elen poff compressed trailer decoded dict-id p W(i))) :byte)`
  imply `(and (equal (mv-nth 0 R3) :span) (posp n) (<= from s) (<= s i))`.
  This owes an actual answer even when earlier matching candidates decline.
* **fn-xc-decoded-span-at-is-the-cached-bytes**:
  G3, `(equal (mv-nth 0 R3) :span)`, natp k, k<n imply
  `(and (equal (mv-nth 0 (fn-pwz-cache-byte-at ledger T(s) file eoff elen poff compressed trailer decoded dict-id (+ p k) W(s))) :byte)
  (equal (nth k (nth 0 out)) (mv-nth 1 (fn-pwz-cache-byte-at ledger T(s) file eoff elen poff compressed trailer decoded dict-id (+ p k) W(s)))))`.
* **fn-xc-decoded-span-at-is-the-returned-bytes**:
  the preceding antecedent plus `(equal (fn-pwz-outcome returned-ledger worker T(s) Z(s)) :ready)`
  implies the same two conclusions with `fn-pwz-byte-at returned-ledger worker
  T(s) Z(s)` replacing `fn-pwz-cache-byte-at ledger T(s)` and remaining arguments
  identical. This explicitly connects installed decoded storage to its producer.
* **fn-xc-decoded-span-at-answers-from-a-matching-slot**:
  G3 and a :span answer imply natp s, FROM<=s, NE<=s<NE+NW, the kind-3
  slot-matchp above at s, `(fn-pwz-cachedp ledger T(s))`, and
  `(fn-xc-decoded-planp Z(s) T(s))`. Also p<p+n<=min(end,decoded),
  p+n<=token-start+token-window-length, and n<=span-capacity.
* **fn-xc-entry-span-at-answers-a-covered-slot**:
  G1, natp i, FROM<=i<NE, NE<=entry-row-count, the kind-1 slot-matchp
  `(fn-xc-slot-matchp i nil 1 file eoff elen 0 0 0 0 trailer 0 slots)`,
  `K(i)=(fn-xc-entry-key file eoff elen trailer T(i))`,
  `(len E(i))=elen+*fn-frame-trailer-octets*`, EOFF<=POFF,
  POFF+PLEN<=EOFF+ELEN, p<end and p<plen imply a :span answer with
  posp n and FROM<=s<=i. Backing premises are established by the install
  consistency contract, not assumed from an unrelated candidate lookup.
* **fn-xc-entry-span-at-is-the-entry-bytes**:
  G1, a :span answer and natp k<n imply
  `(equal (nth k (nth 0 out)) (nth (+ (- poff eoff) p k) E(s)))`.
  Its stale-row companion **fn-xc-entry-span-at-answers-from-a-matching-slot**
  implies kind-1 slot-matchp at s, FROM<=s<NE, exact K(s) above, exact entry
  length, payload bounds, p<p+n<=min(end,plen), n<=span-capacity.
* For each `k` in {entry, decoded}, **fn-xc-k-span-at-miss-changes-nothing**:
  `(not (equal (mv-nth 0 Rk) :span))` implies
  `(equal Rk (list :miss 0 nil dst slots cells))`.
  **fn-xc-k-span-at-hit-touches-only-the-selected-slot**: Gk and :span imply
  `(equal (mv-nth 4 Rk) (mv-nth 1 (fn-xc-touch s slots cells)))` and
  `(equal (mv-nth 5 Rk) (mv-nth 2 (fn-xc-touch s slots cells)))`;
  output indices j>=n equal the original destination. Backing is read-only.
  **fn-xc-k-span-at-never-answers-a-freed-slot**: fn-xcsp slots, natp i below
  slot count and live kind at i imply that any :span from Rk with slots
  replaced by `(mv-nth 2 (fn-xc-free i slots))` has returned slot unequal i.

Old per-kind statements are preserved, not weakened: for decoded soundness
instantiate `fn-pwz-cache-span-at-is-the-cached-bytes` with token=T(s),
i=p, j=p+n and buffer=W(s). The row-to-walk bridge must state equality of the
entire destination to that per-slot call, including unchanged suffix; at the
owner boundary substitute ledger=`fn-owner-page-read-ledger pool` to obtain
`fn-owner-page-decoded-window-cache-span-at-is-the-cached-bytes`. The returned
bridge uses the existing `fn-pwz-a-hit-is-the-published-window` contract.
For entry soundness instantiate `fn-xc-lookup-hit-is-the-descriptor` at kind=1,
a=b=c=d=pos=0, and pair it with the exact nth equality above: this is precisely
the current scalar/loop vector access. No claim is made that arbitrary entry
bytes satisfy the durable digest; the producer's verifier remains required.
Round-4 raw completeness and soundness need no restatement or new premise.

Install keystones (write I3/I1 for each complete install result, Q3 for
`fn-xc-install-window token slots cells`, Q1 for `fn-xc-install-entry file
eoff elen trailer token slots cells`, and s=`mv-nth 1 Ik`):

* **fn-xc-install-decoded-bytes-installs-the-table-decision**: recognized,
  ready tables, NW<=row-count and `(fn-xc-decoded-planp z token)` imply
  `(equal (take 5 I3) Q3)`. **-stores-the-pair**: those premises and an
  installed/replaced answer imply new Z(row)=z and, for every natp j below
  `fn-pwz-token-window-length token`, new W(row)[j]=staged buffer[j].
* **fn-xc-install-entry-bytes-installs-the-table-decision**: recognized,
  ready tables, NE<=row-count, natp elen and stage length=elen+32 imply
  `(equal (take 5 I1) Q1)`. **-stores-the-pair**: those premises and an
  installed/replaced answer imply new K(s)=the full entry key, new E(s)=the
  complete original stage, and returned stage=old E(s). All octets, including
  the trailer, are preserved; this is not merely a prefix equality.
* For both installs, **-leaves-other-rows** states exact key/plan and buffer
  equality at every other row; **-keeps-the-rows-unless-it-installs** says any
  answer outside installed/replaced preserves the whole backing and entry
  stage. **-refusal-changes-nothing** states the complete preflight results
  enumerated above, including table, victim and stage equality.
* **fn-xc-init-all-refuses-more-entries-than-rows**: natp ne and ne>entry rows
  imply `(equal (fn-xc-init-all ne nw slots cells) (list :refused-entry-rows slots cells))`.
  **-refuses-more-windows-than-rows**: not(natp ne and ne>entry rows), natp nw,
  nw>window rows imply the analogous `:refused-window-rows` equality.
  **-readies-all-rows**: fn-xcsp slots, fn-xccp cells, both counts zero,
  natp ne/nw and ne<=entry rows, nw<=window rows imply initialized, recognized
  and ready returned tables with NE=ne and NW=nw; hence every entry/window
  row of an active kind is in its respective backing bank.

### Host premises S must connect

Keep E from lookup through final copy and every install/free/yield; reads
use the live SAME ledger, and no cached token can be settled away during its
borrow. Capture Z before decoded job retirement clears its carry and associate
it with that job's actual decoded buffer. Do not feed NIL to the decoded
install. Route kinds 2 and 3 to their respective installers, so the old raw
installer never writes a kind-3 slot. Whole-entry staging must contain the
actual verified vector including its trailer; the adoption result hands the
victim buffer back to staging. Release a victim charge only after no physical
borrow/alias remains. :present/:duplicate retains the old row and the new
stage, so S must preserve its existing new-token settlement/release ordering.
Before native array deletion, replace all three entry consumers (scalar,
span, whole payload) and drop/free/yield cleanup with these owned buffers;
unused growable capacity remains resident and must be accounted for or
explicitly released, never refunded as if it had disappeared.

The following closed forms pin the principal statement shapes (no hints and
not submitted as proof events in round 5a). The remaining effect/frame schemas
above use the same R1/R3 substitutions and are obligations of the same exports.

```lisp
(defthm fn-xc-decoded-span-at-answers-a-covered-slot
  (let* ((token (fn-xc-slot-token i slots))
         (z (fn-xcw-plan (fn-xc-row i cells) wins))
         (window (fn-xcw-window (fn-xc-row i cells) wins))
         (r (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst)))
    (implies
     (and (fn-xcsp slots) (fn-xccp cells) (fn-xcwp wins) (fn-xc-readyp slots cells)
          (natp from) (natp i) (<= from i) (<= (fn-xc-ne cells) i)
          (< i (+ (fn-xc-ne cells) (fn-xc-nw cells)))
          (<= (fn-xc-nw cells) (fn-xcw-plans-length wins))
          (natp p) (natp end) (natp decoded) (< p end)
          (fn-xc-slot-matchp i nil 3 file eoff elen poff compressed decoded dict-id trailer p slots)
          (fn-xc-decoded-planp z token)
          (equal (mv-nth 0 (fn-pwz-cache-byte-at ledger token file eoff elen poff compressed trailer decoded dict-id p window)) :byte))
     (and (equal (mv-nth 0 r) :span) (posp (mv-nth 1 r))
          (<= from (mv-nth 2 r)) (<= (mv-nth 2 r) i))))
  :rule-classes nil)

(defthm fn-xc-decoded-span-at-is-the-cached-bytes
  (let* ((r (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst))
         (s (mv-nth 2 r)) (n (mv-nth 1 r))
         (token (fn-xc-slot-token s slots))
         (window (fn-xcw-window (fn-xc-row s cells) wins))
         (old (fn-pwz-cache-byte-at ledger token file eoff elen poff compressed trailer decoded dict-id (+ p k) window)))
    (implies (and (fn-xcsp slots) (fn-xccp cells) (fn-xcwp wins) (fn-xc-readyp slots cells)
                  (natp from) (natp p) (natp end) (natp decoded)
                  (equal (mv-nth 0 r) :span) (natp k) (< k n))
             (and (equal (mv-nth 0 old) :byte)
                  (equal (nth k (nth 0 (mv-nth 3 r))) (mv-nth 1 old)))))
  :rule-classes nil)

(defthm fn-xc-decoded-span-at-is-the-returned-bytes
  (let* ((r (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst))
         (s (mv-nth 2 r)) (n (mv-nth 1 r))
         (token (fn-xc-slot-token s slots))
         (z (fn-xcw-plan (fn-xc-row s cells) wins))
         (window (fn-xcw-window (fn-xc-row s cells) wins))
         (old (fn-pwz-byte-at returned-ledger worker token z file eoff elen poff compressed trailer decoded dict-id (+ p k) window)))
    (implies (and (fn-xcsp slots) (fn-xccp cells) (fn-xcwp wins) (fn-xc-readyp slots cells)
                  (natp from) (natp p) (natp end) (natp decoded)
                  (equal (mv-nth 0 r) :span) (natp k) (< k n)
                  (equal (fn-pwz-outcome returned-ledger worker token z) :ready))
             (and (equal (mv-nth 0 old) :byte)
                  (equal (nth k (nth 0 (mv-nth 3 r))) (mv-nth 1 old)))))
  :rule-classes nil)

(defthm fn-xc-decoded-span-at-answers-from-a-matching-slot
  (let* ((r (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst))
         (s (mv-nth 2 r)) (n (mv-nth 1 r)) (token (fn-xc-slot-token s slots)))
    (implies (and (fn-xcsp slots) (fn-xccp cells) (fn-xcwp wins) (fn-xc-readyp slots cells)
                  (natp from) (natp p) (natp end) (natp decoded) (equal (mv-nth 0 r) :span))
             (and (natp s) (<= from s) (<= (fn-xc-ne cells) s)
                  (< s (+ (fn-xc-ne cells) (fn-xc-nw cells)))
                  (fn-xc-slot-matchp s nil 3 file eoff elen poff compressed decoded dict-id trailer p slots)
                  (fn-pwz-cachedp ledger token)
                  (fn-xc-decoded-planp (fn-xcw-plan (fn-xc-row s cells) wins) token)
                  (posp n) (<= (+ p n) end) (<= (+ p n) decoded)
                  (<= (+ p n) (+ (fn-pwz-nth 7 token) (fn-pwz-token-window-length token)))
                  (<= n *fn-ew-span-capacity*))))
  :rule-classes nil)

(defthm fn-xc-decoded-span-at-is-the-per-slot-span
  (let* ((r (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst))
         (s (mv-nth 2 r)) (n (mv-nth 1 r))
         (old (fn-pwz-cache-span-at ledger (fn-xc-slot-token s slots) file eoff elen poff compressed trailer decoded dict-id
                                     p (+ p n) (fn-xcw-window (fn-xc-row s cells) wins) dst)))
    (implies (and (fn-xcsp slots) (fn-xccp cells) (fn-xcwp wins) (fn-xc-readyp slots cells)
                  (natp from) (natp p) (natp end) (natp decoded) (equal (mv-nth 0 r) :span))
             (and (equal (mv-nth 0 old) :span) (equal (mv-nth 3 r) (mv-nth 1 old)))) )
  :rule-classes nil)

(defthm fn-xc-entry-span-at-answers-a-covered-slot
  (let ((r (fn-xc-entry-span-at from file eoff elen poff plen trailer p end slots cells entries dst)))
    (implies
     (and (fn-xcsp slots) (fn-xccp cells) (fn-xcep entries) (fn-xc-readyp slots cells)
          (natp from) (natp i) (<= from i) (< i (fn-xc-ne cells))
          (<= (fn-xc-ne cells) (fn-xce-keys-length entries))
          (natp eoff) (natp elen) (natp poff) (natp plen) (natp p) (natp end)
          (<= eoff poff) (<= (+ poff plen) (+ eoff elen)) (< p end) (< p plen)
          (fn-xc-slot-matchp i nil 1 file eoff elen 0 0 0 0 trailer 0 slots)
          (equal (nth i (nth 0 entries)) (fn-xc-entry-key file eoff elen trailer (fn-xc-slot-token i slots)))
          (equal (len (nth i (nth 1 entries))) (+ elen *fn-frame-trailer-octets*)))
     (and (equal (mv-nth 0 r) :span) (posp (mv-nth 1 r))
          (<= from (mv-nth 2 r)) (<= (mv-nth 2 r) i))))
  :rule-classes nil)

(defthm fn-xc-entry-span-at-is-the-entry-bytes
  (let ((r (fn-xc-entry-span-at from file eoff elen poff plen trailer p end slots cells entries dst)))
    (implies
     (and (fn-xcsp slots) (fn-xccp cells) (fn-xcep entries) (fn-xc-readyp slots cells)
          (natp from) (natp eoff) (natp elen) (natp poff) (natp plen) (natp p) (natp end)
          (equal (mv-nth 0 r) :span) (natp k) (< k (mv-nth 1 r)))
     (equal (nth k (nth 0 (mv-nth 3 r)))
            (nth (+ (- poff eoff) p k) (nth (mv-nth 2 r) (nth 1 entries))))))
  :rule-classes nil)

(defthm fn-xc-entry-span-at-answers-from-a-matching-slot
  (let* ((r (fn-xc-entry-span-at from file eoff elen poff plen trailer p end slots cells entries dst))
         (s (mv-nth 2 r)) (n (mv-nth 1 r)))
    (implies
     (and (fn-xcsp slots) (fn-xccp cells) (fn-xcep entries) (fn-xc-readyp slots cells)
          (natp from) (natp eoff) (natp elen) (natp poff) (natp plen) (natp p) (natp end)
          (equal (mv-nth 0 r) :span))
     (and (natp s) (<= from s) (< s (fn-xc-ne cells))
          (fn-xc-slot-matchp s nil 1 file eoff elen 0 0 0 0 trailer 0 slots)
          (equal (nth s (nth 0 entries)) (fn-xc-entry-key file eoff elen trailer (fn-xc-slot-token s slots)))
          (equal (len (nth s (nth 1 entries))) (+ elen *fn-frame-trailer-octets*))
          (<= eoff poff) (<= (+ poff plen) (+ eoff elen))
          (posp n) (<= (+ p n) end) (<= (+ p n) plen) (<= n *fn-ew-span-capacity*))))
  :rule-classes nil)

(defthm fn-xc-decoded-span-at-miss-changes-nothing
  (let ((r (fn-xc-decoded-span-at from ledger file eoff elen poff compressed trailer decoded dict-id p end slots cells wins dst)))
    (implies (not (equal (mv-nth 0 r) :span))
             (equal r (list :miss 0 nil dst slots cells))))
  :rule-classes nil)
(defthm fn-xc-entry-span-at-miss-changes-nothing
  (let ((r (fn-xc-entry-span-at from file eoff elen poff plen trailer p end slots cells entries dst)))
    (implies (not (equal (mv-nth 0 r) :span))
             (equal r (list :miss 0 nil dst slots cells))))
  :rule-classes nil)

(defthm fn-xc-install-decoded-bytes-installs-the-table-decision
  (implies (and (fn-xcsp slots) (fn-xccp cells) (fn-xc-readyp slots cells)
                (<= (fn-xc-nw cells) (fn-xcw-plans-length wins)) (fn-xc-decoded-planp z token))
           (equal (take 5 (fn-xc-install-decoded-bytes token z slots cells wins buf))
                  (fn-xc-install-window token slots cells)))
  :rule-classes nil)
(defthm fn-xc-install-entry-bytes-installs-the-table-decision
  (implies (and (fn-xcsp slots) (fn-xccp cells) (fn-xc-readyp slots cells)
                (<= (fn-xc-ne cells) (fn-xce-keys-length entries)) (natp elen)
                (equal (len stage) (+ elen *fn-frame-trailer-octets*)))
           (equal (take 5 (fn-xc-install-entry-bytes file eoff elen trailer token slots cells entries stage))
                  (fn-xc-install-entry file eoff elen trailer token slots cells)))
  :rule-classes nil)
(defthm fn-xc-install-decoded-bytes-stores-the-pair
  (let* ((r (fn-xc-install-decoded-bytes token z slots cells wins buf))
         (row (fn-xc-row (mv-nth 1 r) (mv-nth 4 r))) (new (mv-nth 5 r)))
    (implies (and (fn-xcsp slots) (fn-xccp cells) (fn-xcwp wins) (fn-xc-readyp slots cells)
                  (<= (fn-xc-nw cells) (fn-xcw-plans-length wins))
                  (member-equal (mv-nth 0 r) '(:installed :replaced)))
             (and (equal (fn-xcw-plan row new) z)
                  (implies (and (natp j) (< j (fn-pwz-token-window-length token)))
                           (equal (nth j (nth 0 (fn-xcw-window row new))) (nth j (nth 0 buf)))))))
  :rule-classes nil)
(defthm fn-xc-install-entry-bytes-stores-the-pair
  (let* ((r (fn-xc-install-entry-bytes file eoff elen trailer token slots cells entries stage))
         (s (mv-nth 1 r)) (new (mv-nth 5 r)))
    (implies (and (fn-xcsp slots) (fn-xccp cells) (fn-xcep entries) (fn-xc-readyp slots cells)
                  (<= (fn-xc-ne cells) (fn-xce-keys-length entries))
                  (member-equal (mv-nth 0 r) '(:installed :replaced)))
             (and (equal (nth s (nth 0 new)) (fn-xc-entry-key file eoff elen trailer token))
                  (equal (nth s (nth 1 new)) stage)
                  (equal (mv-nth 6 r) (nth s (nth 1 entries))))))
  :rule-classes nil)

(defthm fn-xc-init-all-refuses-more-entries-than-rows
  (implies (and (natp ne) (< (fn-profile-limit :extent-cache-entries) ne))
           (equal (fn-xc-init-all ne nw slots cells) (list :refused-entry-rows slots cells)))
  :rule-classes nil)
(defthm fn-xc-init-all-refuses-more-windows-than-rows
  (implies (and (not (and (natp ne) (< (fn-profile-limit :extent-cache-entries) ne)))
                (natp nw) (< (fn-profile-limit :extent-cache-windows) nw))
           (equal (fn-xc-init-all ne nw slots cells) (list :refused-window-rows slots cells)))
  :rule-classes nil)
(defthm fn-xc-init-all-readies-all-rows
  (let ((r (fn-xc-init-all ne nw slots cells)))
    (implies (and (fn-xcsp slots) (fn-xccp cells) (equal (fn-xcs-count slots) 0) (equal (fn-xcc-count cells) 0)
                  (natp ne) (natp nw) (<= ne (fn-profile-limit :extent-cache-entries))
                  (<= nw (fn-profile-limit :extent-cache-windows)))
             (and (equal (mv-nth 0 r) :initialized)
                  (fn-xcsp (mv-nth 1 r)) (fn-xccp (mv-nth 2 r))
                  (fn-xc-readyp (mv-nth 1 r) (mv-nth 2 r))
                  (equal (fn-xc-ne (mv-nth 2 r)) ne) (equal (fn-xc-nw (mv-nth 2 r)) nw)
                  (<= ne (fn-xce-keys-length entries)) (<= nw (fn-xcw-plans-length wins)))) )
  :rule-classes nil)
```

### Round 5a admission evidence

On persvati, `python3.12 tools/proof_repl.py start pxc5a books/extent-cache-span
--host persvati --certify-missing --certify-jobs 2 --lane p-xc-span` loaded all
70 existing forms. The candidate closure was then prepared by `start
pxc5a-shapes books/extent-cache-storage` with the same flags. Eight missing
dependencies certified successfully; the candidate book itself was not
certified. Its first admission exposed a three-argument MIN (fixed to nested
MIN); its first decoded-install guard check required retaining NE before the
table mutation (now done, without revalidating the returned table).

The final command was:

```
timeout 90 python3.12 tools/proof_repl.py resync pxc5a-shapes books/extent-cache-storage --from fn-xce-entry --host persvati
```

It admitted **22/22 declaration/definition/guard forms, zero refusals**, ACL2
1.08 s, 191855 prover steps; all seven explicit `verify-guards` events passed.
The control is the unchanged round-4 book at abb716d8f and its 70-form load.
The process was pinned to cores 0-11 (`/proc/3489000/status`). Evidence logs:
`/tmp/p-xc-span-r5-repl-start.log` and
`/tmp/p-xc-span-r5-final-admission.log` on the laptop. The REPL status retains
its initial-load MIN refusal even after successful resync; the final per-form
resync log is the admission evidence. The 17 closed contract forms above were
parsed structurally with `tools/lisp_rewrite.py`; none was submitted to the
prover. No candidate keystone certification, native qualification, or host
array deletion is claimed in round 5a.
