# Experiment E1 manifest

Premeasurement design for revision `137695dfc` (fn2/squares). The final freeze
hash table below must be filled before any timed campaign. Qualification and
harness debugging are separate, untimed development evidence.

- Runtime: laptop ACL2 8.7/SBCL through `tools/acl2`, shared existing
  `/tmp/fn2-a4-acl2-slots`, six slots, 8,000 MiB heaps. One certification job
  controller at a time, two cert workers; at most two campaign processes.
- Profile: `*fn2-profile-tiny*` with `:c=1`, `:accept-credits=1`; trace enabled.
  The scribe runs alongside the listener and echo, as in the baseline.
- Explicit domain: fault codes `(26 0 1 2 3 14 25)` = no fault, fragmentation,
  short send, delay, reset, fail slow, release order; word values `(0 1)`.
  At any boundary choose a legal `(:turn)`, `(:take word)`, `(:client word)`
  or full `(:land slot generation active kind cap nonce fault word range terminal)`.
  `active=2` denotes release cell 1; active 1/3 denotes terminal cell 0.
  Any active flight may be chosen, regardless of due-time order. An earlier
  armed wake can intercept that selection and is reported as a wake boundary.
  The selected flight is retained, not silently consumed.
- Handoff word chooses initial latency 1 or 2 ticks. The original registration
  helper's only random effect, due time, is overwritten; its four PRNG words
  are restored. No explicit run consumes PRNG state after initialization.
- `:client` word uses the unchanged echo client oracle and its message function.
  For capability index 0 the creation input is `mix32(word+1)`, with
  length `1+(input mod 1024)` and bytes `fn2-echo-message(length,input)`.
  Thus the domain contains exactly these two generated messages, not arbitrary
  byte strings. Client feed chunk is `1+(input mod 127)`; deliberate drops
  and disconnect deadlines follow that same existing record constructor.
- Enumeration: depth first, choices in order turn, take 0, take 1, client 0,
  client 1, then flight slots ascending, faults in the order above, words 0,1.
  Initialization horizon **4 explicit environment/turn/handoff/client choices**,
  including every prefix of lengths 0 through 4. No state deduplication, no POR,
  no pruning from successful diamonds. States reached means legal prefix
  endpoints visited, not a count of distinct core states.
- Seeds, for each random configuration and each ORIGINAL/M1..M6 campaign:
  **1, 20261028, 314159265**. Random explicit lists use the stated 32-bit LCG
  `x := (1664525*x+1013904223) mod 2^32`, selecting `x mod choice-count`.
  Runs have at most 128 choices, then restart from initialization.
- Budgets: **120 seconds measured wall time and 200,000 core+reference
  transitions combined**, including G1 copies and replayed prefixes/both G2
  routes. Stop at the first failure or first exhausted budget. Outer process
  timeout is 600 seconds, including loading. Load excluded from campaign time
  and reported separately. A timeout/budget stop is censored, never a finding.
- Configuration 1 calls existing `fn2-sim-run-echo` (2 safety connections, its
  unchanged 200-connection liveness phase). It retains the broad 26-class
  random environment and native cadence. Its environment is consequently
  **broader than configurations 2/3**, not an equal-domain search comparison.
  Configuration 2 versus 3 is the equal-domain comparison.
- All configurations share TRACE per turn, OWN, WORK, client byte oracle,
  allocator free-chain partition/count monitor at each turn, and the explicit
  adapter class-latency monitor. The latter checks delay=100 and fail slow
  in {1000,10000,100000}, indexed by word mod 3. It is added instrumentation,
  not credit for systematic reachability. Configuration 2/3 additionally check
  G1 at each transition and G2 for all admitted completion pairs at each
  reached search endpoint. Delay operations and earlier-wake interceptions
  are not coenabled completion pairs.
- G1 normalizes only reference turn bytes/steps, accumulating them independently
  from reference returns; compares all 5 transition returns, representation
  difference, shape invariant, continuation/stop conditions and turn totals.
  TRACE remains a separate composed turn on the original states.
- G2 contract `E1-CLIENT-OWN-STOP-v1`: per-(cap index,nonce) actual ordered client
  bytes, close results, client terminal markers, OWN verdict, core stop reason.
  Identifier correspondence is identity, with no renaming. A deterministic
  observing continuation settles turns/handoffs and completes pending closes.
  This finite continuation can refute a declaration; equality does not prove
  future congruence. No hash is used as semantic equality.
- Declarations: `different-capability` compares full (index,nonce), omitting
  shared effects. `different-capability-and-allocator-disjoint` also names
  posted FIFO, shared operation counts, clock mailbox and, for accept/close,
  allocator free head, active/connection counts and principal 0 FIFO. This
  conservative declaration may admit zero pairs: rejected is not passing.
- The supplied listener/reclamation prefix and both orders are a separate
  negative control; reaching it by construction is not search coverage.
- A second enumeration rotation is omitted in this demonstrator.

## Freeze hashes

Frozen before timed campaigns at 2026-10-29T03:42:45.332722+00:00. All six files were
read in full by the builder and loaded in fresh ACL2 processes.

| File | SHA-256 |
|---|---|
| `M1.lsp` | `b040e6428c98825ca38e0c98353b0e24edc8bef907e43ce8aad0b2fdb89fdcfc` |
| `M2.lsp` | `5425be2f7c822167e8b36959c23e2db19aded90d38d36bdfe41c5677d9fd3518` |
| `M3.lsp` | `4afc0e3e8631bcc0ef9026d4d3a008fbac1db98679ef8924ff55216d377b4bf0` |
| `M4.lsp` | `4203329fe052be79b381d4dda32121cbf43876a622f7558d7327d48f2acf5f30` |
| `M5.lsp` | `6e8fec7ea0dc4a58d50c4acf877c34abacbaa2a4127f5cb60312c32c20120174` |
| `M6.lsp` | `94fd42b724ee97bea73e9c734ec78449fc072cdc1eb8fe33ea06b04539f11e0f` |

The baseline also checks the existing A4 final live-phase accepted=echoed 200,
dropped 0 assertion. Its failure on ORIGINAL is reported separately and is not
a mutation hit. Baseline campaigns repeat complete driver runs with the same
LCG successor seed until the first failure/budget stop. Every raw result retains
the initial campaign seed.

The exact two byte payloads are saved in `results/domain-payloads.sexp`.
Adapter calls (complete/echo-accept/delay) are counted separately; the transition
cap counts the four core/reference categories, including replay.

Postmeasurement reporting clarification: baseline boundaries count TRACE turns;
explicit boundaries count choices in the current list. A G2 finding's boundary
is the end of the second observing route; its common-prefix length and both
full routes are retained separately. A budget-triggering transition attempt
is included in the cap counter before execution stops. Prefix enumeration
counts an attempted prefix before replay, while states-reached counts only
successful replay endpoints; a failure during replay can make those differ.
Replay-reporting fixes after measurement did not change search semantics or
any frozen mutation. Their failed attempts and invalid-prefix retries remain
in the result directory.

Final endpoint correction: review found that the first random driver skipped
G2 after its 128th choice. All 21 random campaigns were rerun after adding that
check. Earlier records are preserved under results/superseded-random-endpoint/
and excluded from the final 49-run table. Baseline/exhaustive code and all six
frozen mutations are unchanged; seeds, budgets and enumeration order stayed
fixed. Process metadata for the replacement runs is in
control-processes-random.json and mutant-processes-random.json under results/.
