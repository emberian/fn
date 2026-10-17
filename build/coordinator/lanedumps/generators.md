# Lane generators (Fable, a40d1d349359f3f48), 2026-10-04

Worktree `build/lanes/generators`, branch `lane/generators` from `origin/integrate/20261004@ec2c1b3da`
(the assembler's base; origin/dev d4e53323c + 14 wave-0 commits). READYs go to the assembler
(af2c7accc6871ee99), copy the integrator (a5616a62b81a6c9b5).

## Coordinates

| what | where |
|---|---|
| brief | `scratchpad/fn-briefs/COMMON.md`; plan `~/dev/redregg/work/FN-SWARMPLAN-20261004.md` §3, §4 wave 4 |
| design | `planning/design-store-representation-2026-10-01.md` §3 (generators), §4 stage 1 |
| state read | `scratchpad/fn-scout/codex-week/generators.md`; `planning/handoff-2026-10-03/generators-2.md` (c09) |
| REPL | laptop slot pool (`proof_repl.py --host laptop`); cache certs are toolchain fcedce7e, laptop ACL2 is bf681d75, so every laptop session needs `--certify-missing` (immutable-list certified locally 10-04) |

## What the brief assumed vs what dev has (read 10-04)

- `def-cursor` is NOT "designed, not built": books/def-cursor.lisp (153) + def-cursor-batch.lisp (96), Codex era-2,
  three instances (fn-nnw-meta, fn-lst, fn-nnw-stream /output + /batch), fn-cur-split guards verified at f6361a46f.
  The DEPENDENCY slot / :suspended status is dead: no fn-cur-make on dev passes a non-nil dependency.
- `def-loop` (863) and `def-representation` (1,215 + lib/paged/tree/tree-walk) are already in books/ with the
  library-theorem + functional-instance scheme and the attachment check at expansion (rep-attached-ancestors);
  def-representation still includes books/proto/adt (reuses its generator function). 50 def-loop forms in the tree;
  387 hand bridges (`*-loop-is-*`) remain in 89 books. def-buffer: no book, no call site anywhere (prose only).
- Teeth generator: c09 must-fixes 1,2,4,5,6,7,8,9 done on dev per generators-2.md; fix 3's gap open
  (`:derived-by RECORD` accepted as any symbol, not checked to be a def-cost row).

## Strand 1: def-cursor for cursor quanta (with cold-line ad0b669196cd8f862)

Messages: 10-04 — sent "today / will emit / need"; cold-line answered: the host runs the quantum under
`*fnn-extent-no-io*`, a miss is a THROW (fnn-extent-cold), the mux polls the read and re-runs the same quantum
warm; no receipt reaches ACL2, so a raise/resume surface is wrong. The bound that matters is READS PER QUANTUM.
Agreed surface: `:demand-metric D` / `:demand-proof THM` on def-cursor (one call raises (nfix D) by <= 1, world-
checked); NAME-STEP-DEMAND-BOUND; def-cursor/batch with :demand-proof takes a DEMAND budget after BYTES, yields on
zero, stops when the step's demand reaches the budget; NAME-BATCH-DEMAND-BOUND (<= rise (nfix demand)). Budget-free
batch keeps its arity (fn-nnw-stream untouched). Their hand version (fn-ovw source := nil | xref | (:hdr ...)) in
books/over-window.lisp + cold-line-quanta.lisp; they send file+sha when it builds; I convert it to the first instance.

State (10-04, wind-down): LANDED on the branch. books/def-cursor.lisp: `:demand-metric D :demand-proof THM` on
def-cursor and def-cursor/output (world check: THM is literally (<= (- (nfix D[progress := (mv-nth 1 CALL)])
(nfix D)) 1)); emits NAME-STEP-DEMAND-BOUND (:linear) and records :demand-metric/:demand-proof/:demand-bound in
the fn-cursor row. books/def-cursor-batch.lisp: with :demand-metric/:demand-proof (the step's demand bound,
world-checked) the batch is (NAME-BATCH cur visits bytes DEMAND . FORMALS): yields on (zp demand), continues past
an empty :candidate step only while (NAME-BATCH-DEMAND-OF cur next) < demand (a generated :guard t function, the
rise of (nfix D); disabled), recursing with (- demand d); proves NAME-BATCH-DEMAND-BOUND
(<= (- (nfix D[out]) (nfix D[cur])) (nfix demand)) via local -DEMAND-OF-SELF/-SPLIT/-BOUND lemmas. Without the
keywords the batch is byte-for-byte today's (fn-nnw-stream untouched). Test book tests/acl2/def-cursor-tests.lisp:
43 forms admitted in a laptop REPL (ACL2 0.58 s, 148k steps): the dtest instance, exact theorem statements, batch
budgets 2 / 0 / 9, three refusals (:unchecked, as def-loop-tests does), the budget-free batch keeps arity
(cur visits bytes). NOT yet certified; the affected closure (def-cursor -> newnews-metadata-cursor,
list-metadata-cursor, newnews-stream-cursor, served-plan-*) owes `farm.py submit hbox --affected-by
books/def-cursor.lisp` + `--affected-by books/def-cursor-batch.lisp`.
Constraint for consumers: D must be guard-total over any progress (the batch evaluates it).
What COLD-LINE still needs: (1) their fn-ovw :hdr source step as the first :demand instance (D = numbers consumed
when the source reads payload heads, else 0) and fn-nnw-stream's batch converted to :demand (D = candidates visited)
with fn-splan-rest-cursor-step / fn-qplan-cursor-step passing demand = q (q = 4 = cache/2, or any natp <
fn-arx-read-cache-entries) -- that is in their files; (2) their consumer-side claim in books/cold-line-quanta.lisp
that heads read by a step <= its rise of D. Nothing of the host changes: the demand budget is chosen in ACL2.
Also fixed here: integrate@ec2c1b3da's mechanical must-fail -> must-fail-checked in this test book had left it red
(a generator refusal is a translation-time soft error and needs :unchecked "reason"); other generator test books
converted the same way should be checked by the next lane (def-loop-tests already uses :unchecked).

## Strand 2: ST1 (def-loop instances; def-representation)

Candidates (one hand twin each, in the image closure, 0 direct host refs, unowned per ROSTER, named by def-loop's own
worked examples): books/snoc-list.lisp fn-sl-append1 (:map :tail; 4 includers), books/cancel-lock.lisp fn-cl-ring-keys
(:map, 1 includer), books/refused-offers.lisp fn-rof-first (:take, 1 includer); spare: books/hybrid-store.lisp
fn-hsig-octet-fields-to-strings (8 includers).

## Strand 3: teeth c09 fix 3 gap

Plan: fn-dt-world-problem refuses a bound whose :derived-by RECORD is not a key of (table-alist 'fn-cost w), or whose
V does not mention that row's :route-twin / :cons-route-twin; refusal keyword :underived-record; positive + two
must-fail-checked in tests/acl2/defkeystone-tests.lisp (def-cost'd toy).

## Strand 4: def-carried-view / def-keyset-check

def-keyset-check: 2 consumers in the image (store-files, retention) — exists, wired. def-carried-view: 2 pilots
(fn-nnw newnews-cursor, fn-wix withdrawal-index-carried), neither in the image closure; consumers are cold-line's
and the carrier's files. Decision pending (leave with a note unless a consumer appears).

## Continuation (exact), for the Opus that takes this lane

1. Certify: `farm.py submit hbox --affected-by books/def-cursor.lisp` (and -batch); cite the manifest; then READY
   `| sha | def-cursor | 0 instances converted / 0 twins deleted | manifest |` to the assembler; convert cold-line's
   first :demand instance when they send file+sha (they own the file; hand it back).
2. ST1 (nothing started in code): convert, one commit each with the twin deleted and `(include-book "def-loop")`
   added: books/snoc-list.lisp `(def-loop fn-sl-append1 (x r) :shape :map :elt e :body e :tail (list r))`;
   books/cancel-lock.lisp `(def-loop fn-cl-ring-keys (ring account msgid) :shape :map :elt e :body (fn-cl-key e
   account msgid))`; books/refused-offers.lisp `(def-loop fn-rof-first (n xs) :shape :take :count n :over xs
   :while (consp xs) :elt e :body e :guard (natp n))` (the :take logic's conjunct order differs from the hand one;
   fn-rof-first-len / -of-short in the same book re-prove by induction). Announce each file to the assembler before
   pushing. def-representation: already promoted with the attachment check (rep-attached-ancestors, refusal names
   the attached ancestor); the remaining "promotion" is that it still includes books/proto/adt for its generator
   function -- a move of proto/adt* under books/def-representation-* with the proto twins deleted is the honest
   ST1 close, not started; def-buffer has no spec anywhere (prose only in the design table) -- ask ember what it is
   before building it. Generic library-theorem check: every def-loop instance owes only defining equations +
   :functional-instance (true today, fn-dl-fn).
3. Teeth c09 fix 3 gap: in books/defkeystone.lisp fn-dt-world-problem, refuse a :visits/:allocation entry whose
   :derived-by RECORD is not (assoc-eq RECORD (table-alist 'fn-cost w)) or whose V does not mention that row's
   :route-twin (:cons-route-twin for :allocation); new refusal keyword + text in fn-dk-refusal-text; tests in
   tests/acl2/defkeystone-tests.lisp (include ../../books/def-cost for the positive case; two :unchecked refusals).
   Must-fixes 1,2,4-9 are in code per generators-2.md; 10 n/a; nothing re-audited here.
4. def-carried-view: leave with a note until a served consumer exists (both pilots outside the image; cold-line /
   carrier own them). def-keyset-check: done and wired (store-files, retention).

## Log

- 10-04 ~T+0: worktree, base ec2c1b3da; cold-line messaged; assembler acked.
- 10-04 ~T+2h: :demand surface agreed with cold-line (their THROW/rerun account replaced my :raise); generator,
  batch and test book green in the laptop REPL; ember's wind-down for Fable lanes received -- committed, pushed.
