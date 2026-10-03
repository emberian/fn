# Lane def-entry (Fable deputy), 2026-10-03

Worktree build/lanes/def-entry, branch lane/def-entry from origin/dev 4aa332295.
Scope: `def-entry` (one declaration per host-called entry) and its first concrete
piece `def-owner-writer` for STAGE-5B. Composes with def-carried (rows, completeness,
D40), definterface (the fn-interfaces row), GENERATORS' defteeth (teeth and the
visits theorem; lanedumps/generators-2.md), DEF-COMMAND, DEF-HOLDER and cost-gate.

## Interface sketch (sent to the coordinator 2026-10-03)

Rule inherited from def-carried: every statement is GENERATED from the declaration
and the WORLD; the user's theorems are only `:use`d. Macros expand to ordinary events.

### The form

    (def-entry NAME (FORMAL ...)          ; = the world's formals (or emitted, with :body)
      :class :common-lisp-compliant | :program
      :kinds ((FORMAL RECOGNIZER) ...)    ; exact: what fnn-entry-guard evaluates (definterface's check)
      [:exempt ... :keystones ... :root ... :direct ...]   ; as definterface today
      :carries ROW                        ; a def-carried or def-carried-view row; NAME becomes its transition
      :via (THM | (THM (VAR TERM) ...) ...) ; the model keystones the preservation is proved FROM
      :opens (FN ...)                     ; callees the generated proof unfolds
      :writes (GLOBAL ...)                ; the globals the body writes; checked = the world
      :effects :none | (:durable PROGRAM) ; crash points = PROGRAM's cuts (books/byte-store-programs)
      :cost (:per-call | :per-quantum Q)
            :sizes ((S TERM) ...)         ; named sizes over the formals and the profile
            :visits (V-TERM BOUND)        ; V-TERM: a visit model over the formals; BOUND over :sizes
            :allocation (A-TERM BOUND) | (:none "why")   ; octets; never silent
            :guard (:kinds-only | (:carried C ... :paid | :skipped))   ; the counterpart guard's cost
            :rests-on (A-NAME ...)        ; host cost facts, named rows of specs/failures.md
      :witness (T ...)                    ; one term per formal: the teeth's reachable positive
      :bench (:fixture curve :at (1000 10000 100000))
      [:body BODY])                       ; emits the defun; guard = kinds AND ROW's concluded
                                          ; conjuncts at the carried formal AND :guard-extra

### Generated, in order, each an ordinary event

(a) the fn-interfaces row: `(definterface NAME :class ... :kinds ... [:raw-with (:carried ROW)])`;
    raw-with only when the row backs NAME in this world (definterface refuses otherwise).
(b) `NAME-preserves-ROW`: `(implies (and (R s) G) (R RET))`, s and RET from stobjs-in/-out
    (def-carried's derivation), proved in minimal-theory + {NAME, :opens, the row's frame
    lemmas, mv-nth nth zp car-cons cdr-cons} with `:use` of every :via at the carried
    state; the row's transition list is completed from the table (def-carried's
    completeness still refuses an unlisted writer).
(c) the writes check, at expansion, from the world: the put-global keys reachable from
    NAME's body through :opens must equal :writes, and a write to a carried global must go
    through the row's installer whose argument a :via covers -- refused by KEY before any
    proof runs (the 30-minute guard-proof hang of stage-5 was this class).
(d) the cost obligation: `(table fn-teeth-owed NAME-preserves-ROW '(:visits ((V-TERM BOUND))
    :allocation ...))`. The theorem is GENERATORS' `defteeth :visits` in the test/image
    world (NAME-...-visits-K: (implies G (<= V B)) plus the ATTAINS witness);
    `(defteeth-check)` refuses an owed keystone with no teeth or teeth whose :visits
    differ from the owed pair (ask to GENERATORS: the owed row carries the pair).
    :guard (:carried C :paid) makes V-TERM = C's visits + the body's; :skipped is
    accepted only when the row backs raw dispatch of NAME (fn-cd-raw-problem nil).
(e) the benchmark hook: `(table fn-bench NAME ROW)` -> tools/interface_emit.py writes
    planning/cost-hooks.json rows {entry, formals, sizes, bound, order (degree per size,
    from BOUND), theorem, at}; the cost-gate lane runs them at 1k/10k/100k on the curve
    fixture and refuses a measured order above the declared one. Two independent
    checks: the theorem is about the visit model; the gate ties the model to the bytes.
(f) crash points, generated once and read twice (the DEF-HOLDER boundary, decided):
    :effects (:durable PROGRAM) -> CUTS are PROGRAM's `(:cut "name")` steps read from its
    defun in the world; :effects (:release HOLDER) -> CUTS are DEF-HOLDER's
    `fn-holder-cuts` row for HOLDER (def-holder owns the names; def-entry mints none);
    :effects :none -> no cuts, and interface_emit refuses it when the entry's raw caller
    performs a durable syscall (harness_check's reading). The per-entry enumeration is
    `(table fn-entry-cuts NAME CUTS)`, a projection, never a second source.
(g) teeth: `(table fn-teeth-owed ...)` for each generated keystone; :witness feeds defteeth.

### What a VISIT is

One read of one element of a sized collection: a cdr step over a list (a formal or a
carried list), one row or page read of a def-representation stobj (an export call), one
record of the store. Fixed-size scalar work is not a visit. A step's `equal`/`member`
over structure is O(1) only under a NAMED host fact (:rests-on A-SBCL-EQUAL-SHARED, the
eq-first behaviour on shared structure; generators-2's finding); unnamed, it is a walk
and counts against the bound. Allocation is a second figure, never folded into visits.

### Fail closed

A dispatched entry with no def-entry: interface_emit --check against a shrink-only
baseline planning/entry-baseline.json (the tree's ratchet pattern). A :cost with no
admitted theorem: defteeth-check. :writes not the world's: expansion. :class :program:
the row only, registry-marked, no theorem claimed. A :bench with no cost row: refused.

### First piece, now: def-owner-writer (STAGE-5B's tiers B and C)

    (def-owner-writer FN :opens (...) :via (...) [:step (EVENT-TERM KEYSTONE)] [:writes (...)])

= (b)+(c) specialised to fn-owner-retain-statep: the frame set fn-orh-retain-statep-of-
{other-global-put, install-ocfg, install-served-effects, put-credits}, `:use` at
(oc (fn-owner-ocfg state)) plus fn-owner-retain-statep-implies-lgoc; `:step` emits the
fn-owner-step-at-EVENT lemma from the ocfg keystone first; a row in `fn-owner-writers`.
`(def-owner-writers-carried ROW :from fn-owner-retain-carried)` emits the image-world
def-carried row (invariant, open and bridges copied from the pilot row; transitions =
the pilot's + the table), with the interface_emit mirror. Tier A's 229 hand lines
become ~40 declarations with the same theorem names.

### Boundaries

GENERATORS: I call defteeth / fn-teeth-events; :carries accepts a def-carried-view row;
def-keyset-check is what fn-sf-success-listp-shaped guards become (their cost rows then
read O(n) once, not per call). DEF-COMMAND: a command names its entries; a command's cost
is the registry's sum of its entries' rows (composition, not a theorem). DEF-HOLDER: owns the cut names and
the fn-holder-cuts row for every holder release; def-entry reads that row for an entry
declared `:effects (:release HOLDER)` and emits no cut of its own; def-entry says nothing
about handles. cost-gate: consumes planning/cost-hooks.json. STAGE-5B: writes
def-owner-writer forms in host/owner-retain-host.lisp; I do not edit that file.

### Amendments from the siblings (2026-10-03, after the sketch)

- COST-GATE: `:bench (:fixture served [:axis SIZE])` -- the gate's `served` fixture (a
  live node with N commits since open, pins/releases, cancels, reclaim, a lagging reader,
  peers; windows after reclaim / checkpoint reload / restart-recovery), never
  tools/fixtures.py `curve` (zero successes since open: the trap that hid the quadratic
  guard). The gate builds no arguments from :formals/:witness: an entry is measured only
  where the workload makes the host call it, and a :bench the workload never reaches is
  REFUSED (not exercised), so a new :bench may need a workload step. `:sizes` names come
  from the fixed vocabulary {articles, commits_since_open, pins, releases, withdrawals,
  groups, connections, peers, verdicts}; the fitted exponent is the total degree over the
  sizes that scale together, and naming one size runs that axis alone.
- GENERATORS: the owed row is `(table fn-teeth-owed 'NAME '(:by MACRO [:visits ((V B
  [:rests-on (A ...)]) ...)] [:allocation (...)]))`; defteeth-check refuses an owed
  keystone with no row or whose teeth do not state every owed bound with the SAME terms
  and the SAME :rests-on set. :rests-on names are constrained functions of
  books/assumptions-*.lisp; A-SBCL-EQUAL-SHARED lives in GENERATORS'
  books/assumptions-host-cost.lisp (cited, never created here).
- STAGE-5B (from admitting tier A; designed to): the carried formal and RET are the
  world's (stobjs-in/-out), never `state` or (mv-nth 2 ...) by hand; the frame set is a
  PROFILE ROW the macro reads (:installers, :carried-globals for the legacy state carrier,
  :frame), so the declarations survive the carrier move unchanged; the statement is
  def-carried's exactly, (implies (and (R s) G) (R RET)); the macro emits
  `(verify-guards FN)` under minimal-theory + :opens + the profile's and the writer's
  :guard-theory (the expensive part: fn-owner-take 192 s / 21.9M steps in the default
  theory, a goal that closes in 706 steps under eight named rules); definterface's two
  rules are checked at EXPANSION (a guard conjunct over a per-call argument that is not a
  kind is refused; every other non-kind conjunct is (R s) or has a bridge in the pilot
  row's :concludes or the writer's :bridges); :via covers each installer's value (the
  retention carry's put needs fn-prc-carryp-of-refresh beside the lgoc keystone).
  Two kinds out of the macro's reach, and how def-entry treats them: a two-stobj premise
  (fn-owner-finish's (fn-hist-of-storep fn-hist store)) is RECORDED as :uncovered on the
  writer's row -- the preservation is proved under it as a guard conjunct, and the entry
  stays on the counterpart path (fn-cd-uncovered-conjunct refuses raw dispatch) until a
  multi-stobj row can state it, its cost row then :guard :paid; an establishing producer
  (fn-owner-recover-from-store-open) is def-carried's :established entry, read from the
  pilot row by def-carried-writers-row, never a writer.
- DEF-HOLDER: owns cut names and fn-holder-cuts; def-entry reads, never mints (above).
- KNOWN INSTANCE for the effect/outcome part (Astra r71 item 15, via the coordinator):
  host/native/owner.lisp fnn-owner-prepare-refusal-word maps prepare results to outcome
  words (:invalid -> :malformed) in HOST code, a decision AGENTS.md says ACL2 owns. In
  def-entry the outcome word is part of the declared entry's ACL2 result (:outcomes, the
  words the entry answers, checked against the body's result alphabet), so no host line
  computes one; the registry row lists them and interface_emit refuses a dispatch site that
  maps a word.

## Round two: the derived cost semantics (DRAFT for the coordinator; after the READY)

The rule (c04, c06, the coordinator): a cost is DERIVED from the executed body with primitive
and callee summaries; a declared bound is a theorem about that derived cost; an unknown
callee is UNACCOUNTED, never zero; a benchmark is regression evidence, never the claim.

1. THE COST TWIN, BY CONSTRUCTION. `(def-cost NAME)` reads NAME's translated body from the
   world, takes the EXECUTED arm (the :exec of `return-last 'mbe1-raw`, the attachment of a
   constrained function, a def-representation export's :exec) and emits `NAME-visits` and
   `NAME-octets`, two definitions with the SAME control structure as the body (if -> if;
   a lambda -> the same let; a call -> its contract applied to the same actuals), each
   leaf a contract: car/cdr/consp/eq/arithmetic on fixnums = 0 visits; cons = 0 visits, 16
   octets; nth/len/member/assoc/append/revappend over a list = (len L) visits (append's
   octets 16 (len L)); equal over structures = (min size) visits unless both operands are
   STAMPED (a stamp predicate in the logic, GENERATORS' domain), then 1; a def-representation
   export = 1 visit (get) or 0 (count); a def-loop shape = the library's twin (its visits
   theorem per shape, by functional instance: :map = (len xs), :take = (min n (len xs)));
   a callee WITH a def-cost row = its NAME-visits applied to the actuals (a summary); a
   callee WITHOUT one = `(fn-cost-unaccounted 'callee actuals)`, a constrained natural with
   no axiom, so no bound over it is provable and the registry says `unaccounted: callee`.
   Recursion: a function whose SCC has no def-cost rows is unaccounted; one with rows gets
   the recurrence (the twin is recursive like the body, with the body's measure).
   The twin is REGENERATED at every def-cost-check from the current body and compared by
   formula (def-carried's rule): a changed body changes the twin or refuses.
2. THE BOUND. `:visits (BOUND :sizes ((S TERM) ...))` makes `NAME-visits-bound: (implies G
   (<= (NAME-visits args) BOUND[sizes]))`, proved by the generator for straight-line twins
   (arithmetic), by the loop library for def-loop shapes, by the user's :hints otherwise;
   BOUND is a typed term over the size vocabulary {articles, commits_since_open, pins,
   releases, withdrawals, groups, connections, peers, verdicts} plus the profile's fields,
   with a declared class :worst-case | :amortized (an amortized bound names its potential).
   Teeth via defteeth :visits (the attains witness on the `served` dimensions).
3. THE ROUTE. The entry's dispatched cost = guard cost + body cost on the route the FINAL
   WORLD selects (fn-interfaces: :raw-with accepted -> kinds only; else the whole guard,
   derived the same way as a term; the fixed-callback ABI listed separately). `:skipped`
   is never declared; it is read.  A guard whose derived cost mentions a whole-state size
   on a served route is refused outright (AGENTS.md), not charged.
4. EFFECTS, FAIL-CLOSED. :writes/:reads derived over EVERY reachable translated definition
   to a fixed point (never through proof hints), stobj field/index regions included,
   a computed key = the whole region, exhaustion = incomplete (refused), a raw-host caller's
   durable syscalls collected transitively by harness_check's reading with callbacks as
   summaries; :effects :none refused on any unknown. The OUTCOME WORDS the entry answers are
   part of its ACL2 result (:outcomes, checked against the body's result alphabet); a host
   site that maps a word (fnn-owner-prepare-refusal-word) is refused by interface_emit.
5. COMMANDS (DEF-COMMAND's): a command's cost is a fold over its fuel-bounded trace with
   multiplicities and size substitutions at each call (the served drain's N rounds), never
   a registry sum; each entry's cost row exports NAME-visits for that fold.
6. EXCEPTIONS: planning/cost-obligations.json, one row per dispatched entry {name, class
   (compliant|ideal|program), cost: proved|unaccounted(callees)|none}, compared BY NAME with
   origin/dev's copy: an unaccounted row may only vanish or become proved; a new dispatched
   entry must carry a row; :program and :ideal are counted, never silently exempt.
7. BENCH: `served` only, one axis per named size, the measured exponent against BOUND's
   degree in that size; a :bench the workload never reaches is NOT EXERCISED and refused.
First instances for round two: fn-splan-cursor-step (the catalog guard per quantum: the
derived guard cost is (fn-cat-count fn-cat) visits per call, which rule 3 refuses on the
served route until the catalog relation is carried), fn-reader-chunk (visits = (len
octets) + the served step's), fn-owner-close (0 visits beyond the connection list: a
walk of (connections)).

## Tier A as declarations (for STAGE-5B; the frozen f98e1ff1b statements, 1:1)

host/owner-retain-host.lisp keeps its header and the two hand lemmas that are not the
writer shape (fn-owner-idrp-install-preserves-lgoc; fn-owner-io-refuses-an-unsafe-
observation with its two assert-events); the five frame lemmas and the bridge move to
books/owner-retain-frame.lisp (included); the ten writers become:

    (include-book "../books/owner-retain-frame")
    (include-book "../books/owner-host-relation")
    (def-owner-writer fn-owner-install-effects)
    (def-owner-writer fn-owner-close :opens (fn-owner-callback-close)
      :via (fn-ohr-step-close-preserves-carried-relation fn-owner-callback-close-branch-unfolds))
    (def-owner-writer fn-owner-fault :opens (fn-owner-callback-fault)
      :via (fn-ohr-fault-preserves-carried-relation))
    (def-owner-writer fn-owner-open-peer :opens (fn-owner-callback-open-peer)
      :via ((fn-ohr-open-peer-preserves-carried-relation
             (peer (fn-store-octets->string peer-octets)) (acfg (fn-owner-auth state)))))
    (def-owner-writer fn-owner-install-node-secret
      :opens (fn-owner-replace-core fn-owner-core fn-owner-ocfg)
      :via ((fn-ohr-with-node-secret-preserves-carried-relation (secret ring))))
    (def-owner-writer fn-owner-apply-limit-profile
      :opens (fn-owner-replace-core fn-owner-core fn-owner-ocfg)
      :via ((fn-ohr-osb-install-preserves-carried-relation (profile values))))
    (def-owner-writer fn-owner-take :opens (fn-owner-put-credits)
      :step (fn-owner-step (list :take) fn-ohr-step-take-preserves-carried-relation)
      :bridges ((fn-ocfg-eventp <THM: (implies (fn-owner-retain-statep x)
                                         (fn-ocfg-eventp (fn-owner-ocfg x) (list :take)))>)))
      ; the macro names this bridge: take's guard applies fn-ocfg-eventp to the state alone
    (def-owner-writer fn-owner-control-submit
      :step (fn-owner-step (list :control-submit msgid-octets group-octets payload)
             fn-ohr-step-control-submit-preserves-carried-relation))
    (def-owner-writer fn-owner-prepare-retention :lemmas (fn-owner-idrp-install-preserves-lgoc))
    (def-owner-writer fn-owner-io :opens (fn-owner-io-safep fn-sbud-oc-store)
      :via (fn-lgoc-log-reserve-preserves-invariant fn-lgoc-log-order-preserves-invariant
            fn-lgoc-rcon-io-preserves-invariant))
    ; later, in the image world after host/interfaces.lisp: the owed report, then the row
    (def-carried-writers-owed fn-owner-retain :from fn-owner-retain-carried)
    ; (def-carried-writers-row fn-owner-retain-carried-host :profile fn-owner-retain
    ;    :from fn-owner-retain-carried)   ; refuses until every state-returning entry is
    ;                                     ; listed: the carrier move's purpose

Each form also emits (verify-guards FN) under minimal-theory + :opens + the profile's
:guard-theory when FN was admitted :verify-guards nil, so the defuns in owner-host.lisp
say :verify-guards nil and a writer adds :guard-theory (RUNE ...) where its guard proof
needs more than the profile's eight (their 662/791/286-step budgets are the target).

## CONTINUATION (wind-down 2026-10-03; resume here)

Branch lane/def-entry, head 67ee29e37 (pushed; sent to the runner a8c1198f67920c411
under ember's everything-onto-dev directive). Worktree build/lanes/def-entry; one
untracked file, tools/cost-prefix.lisp (44 host lds through host/interfaces.lisp for an
image-world REPL; regenerate from tools/extract/world-host.lisp). No REPL session live.
Ledger (build/coordinator/repair/repair.py): X06, L01, L02 = ready 67ee29e37; DE-R2 =
in-progress (round two); r71-F15 open (design in "Amendments"). First: `git fetch`, base
on origin/dev once the runner has merged; if the merge head's `make check` fails on
cost_obligations (interfaces.json changed), `python3 tools/cost_obligations.py --write`
(+ `--baseline` for a new undeclared compliant entry) and commit the regen.

Background jobs left running at wind-down (not acted on; their boxes survive the harness):
- farm run-20261003T023049Z-2490 on hbox (the six X06/L01/L02 roots); the local wait was
  harness task br5hxb96t. Read with `python3 tools/farm.py wait hbox run-20261003T023049Z-2490`.
- the image-world `--certify-missing` of REPL session iw (harness task blxvknno8; its log
  /tank/fn/gates/def-entry-repl/build/proof-repl/iw.certify.log; the session's serve was
  stopped, the certify_books.py it spawned may still be finishing: its pairs land in
  /tank/fn/certcache and are reused by the next start).
Ledger items X06, L01, L02: ready at 67ee29e37 (sent to the runner; nothing else owed by
the lane until their certify verdict is cited).

NEXT, exact:
1. CERTIFY VERDICT of the X06/L01/L02 roots: `python3 tools/farm.py wait hbox
   run-20261003T023049Z-2490` (6 roots: definterface, def-carried-writer, definterface-tests,
   def-carried-tests, def-carried-writer-tests, owner-retain-frame-tests). On pass:
   `python3 tools/evidence_manifests.py add <certify id>`, commit, push, ledger X06/L01/L02
   stay ready at the new sha. On red: the REPL runs were green from source; the difference
   is a certificate-world one -- fix forward in the named book.
2. def-cost's own certify: `python3 tools/farm.py submit hbox books/def-cost
   tests/acl2/def-cost-tests`; cite; DE-R2 note.
3. THE fn-reader-chunk INSTANCE (the coordinator's one end-to-end row): image-world REPL
   `proof_repl.py start iw books/image-world --host hbox --acl2
   /tank/fn/toolchains/w28/acl2-literal-4g-tls64k --certify-missing --certify-jobs 8
   --limit 600 --load-timeout 1800` (the session certifies the image world's changed
   closure first, ~25 min; the last attempt was stopped at wind-down with its serve held);
   then send `(ld "../tools/cost-prefix.lisp" :ld-error-action :error)`, then
   `(ld "../books/def-cost.lisp")` -- or include it in books/image-world.lisp beside
   def-carried -- then `(fn-cost-derive 'fn-reader-chunk (w state))`: read the route
   (:served), the kinds term (binary-+ '1 (len octets)), the body term and the unaccounted
   list (expect fn-served-step; fn-reader-install-result should inline). Then write
   host/cost-host.lisp: `(include-book "../books/def-cost")` + `(def-cost fn-reader-chunk
   :visits (+ 1 request-octets) :sizes ((request-octets (len octets))) :unaccounted
   (fn-served-step))` (adjust the constant to the derived term) + `(def-cost-check
   fn-reader-chunk)`; ld it in host/native/build.lisp AFTER host/interfaces.lisp (the route
   is read from fn-interfaces) and regenerate tools/extract/world-host.lisp
   (tools/extract/world.py); teeth in a test book over the host world are not certifiable:
   put the positive/attains witnesses as assert-events in host/cost-host.lisp (; GEN:
   defteeth); `python3 tools/cost_obligations.py --write` (the row becomes `partial`,
   unaccounted fn-served-step); READY with the derivation printed in the message.
   The refusal tooth on the real catalog entry: `(must-fail-checked (def-cost
   fn-splan-cursor-step))` is not expressible in a host ld (must-fail-checked is a test
   book's); assert `(fn-cost-mentions (caddr (fn-cost-derive ...)) *fn-cost-whole-state-sizes*)`
   = fn-cat-count instead, and note SERVED-CATALOG-LIVE is removing that guard.
4. After 3: STAGE-5B (ab43abe34a71e8522) takes def-owner-writer over the stobj carrier
   (their tiers B and C); answer their questions directly; the profile for the stobj
   carrier is theirs to write (books/owner-retain-frame.lisp's :invariant/:installers/:at
   /:frame change, no declaration does).
5. Then the owed pieces of round two, each its own READY: contract witnesses (one
   micro-benchmark per *fn-cost-contracts* row under the toolchain record; the registry's
   `unwitnessed` 48 -> 0, shrink-only), the :stamped rule (generators' NAME-fresh /
   NAME-stampedp as one visit under the row's named hypotheses), allocation (:octets twin),
   r71-F15 (:outcomes), then def-entry proper (the fn-interfaces row + (b)-(g) from one form).

## State
- 2026-10-03: worktree build/lanes/def-entry (lane/def-entry from 4aa332295); sketch
  sent; c06 applied (the stronger hand statement, :put-keys a diagnosis, :hyps = guard
  conjuncts, :ideal handled, the v1 teeth owed row, :step (STEP EVENT THM) for a host
  step function, an existing step lemma reused by formula).
- Delivered on lane/def-entry (pushed): books/def-carried-writer.lisp (def-carried-profile,
  def-carried-writer, def-carried-writers-row, def-carried-writers-owed);
  books/owner-retain-frame.lisp (the owner's legacy-state profile fn-owner-retain: the five
  frame lemmas + the retention-carry installer's, from host/owner-retain-host.lisp into a
  book; def-owner-writer); tests/acl2/def-carried-writer-tests.lisp (a stobj carrier, the
  carrier move's target; REPL hbox 108/108: writers through an installer + :via, frame-only,
  :step through the profile's and a named step, :bridges, a two-stobj :hyps whose absence
  makes the theorem false; one expansion pinned literally; every refusal by its words; the
  row from the table; def-carried-check; owed 0 then 1 once an entry is declared, and the
  row's completeness then refuses); tests/acl2/owner-retain-frame-tests.lisp (REPL hbox
  31/31: fn-owner-callback-close/-fault/-open-peer as def-owner-writer -- the tier-A
  proofs minus the one-line wrappers, 301/335/400 prover steps; the legacy carrier's
  refusals; the row over the pilot 1,873 steps); tools/interface_emit.py carried_rows
  mirrors def-carried-writers-row from the same forms (tests/test_interface_emit.py
  26/26); Makefile roots; regen (ledger, current view, hot-path stale) at af42f4e9c.
- Certified: hbox run-c569 certify-20261002T225009Z-1315949 4/0 (cited, 96eb1d3df);
  owner-retain-frame 12.5 s at 2 jobs under load 12.2 (D26: the include chain
  owner-retain-carried + owner-connection-callbacks, not the frame's ~100-step proofs).
  check-lane on hbox at bf4553265: ledger / teeth_check / null_witness_lint / interface_emit
  / host_check --books,--load / reach_check / secrets ok; the reds (must_fail_check on
  bp-native-app-replay-bridge-tests, depth_check native-operator-host, evidence_size
  commit-map, cite/spec_cite, keystone_emit feed-connection-teeth, coverage HST-045,
  alphabet, premise_audit adt-pg-pokp, hot_path, host_check hash tables, main_last_check,
  test_build_lists_check) are dev's, none in a file this lane touches.
- STAGE-5B's frozen tier A: f98e1ff1b (fn-owner-io R-only; the :unsafe-observation and
  idrp lemmas stay hand lemmas, :lemmas); their guard budgets to beat: take 662,
  control-submit 791, apply-limit-profile 286 steps.
- READY SENT 2026-10-03: lane/def-entry c1d69fb6a (run-093b certify-20261002T233525Z-2380119
  2/0 cited; no book over 10 s). Liaison: LAND, with X06 (definterface) + L01 + L02.
- 2026-10-03 later: ember's directive (everything onto dev; fix forward): lane/def-entry
  67ee29e37 sent to the runner. In it: X06 (books/definterface.lisp: only
  *fn-di-fail-loud-primitives* = (boundp-global boundp-global1) are exempt from the
  raw-with bridge rule, both paths; teeth definterface-tests fn-dit-r-bounded and
  def-carried-tests r72), L01 (argument check before the primitive skip), L02 (the mirror
  raises on duplicates/conflicting bridges) -- REPL green (93/216/108/31), certify of those
  roots in flight (farm, hbox); ledger X06/L01/L02 = ready 67ee29e37.
  ROUND TWO LANDED AS WIP: books/def-cost.lisp (the twins NAME-visits / NAME-route-visits
  from the translated body; contracts = the trusted base *fn-cost-contracts*, 48 rows;
  stobj primitives one op; small non-recursive callees inlined; else fn-cost-unaccounted,
  a constrained natural; the bound theorem over the route twin, partial over the named
  unaccounted; a served guard over a whole-state size refused; def-cost-check re-derives),
  tests/acl2/def-cost-tests (REPL hbox 49/49: fn-id-hex-octets served, bound 1 + n proved
  and attained; internal; unaccounted + partial; refusals; the catalog-guard fixture;
  the stale-row tooth), tools/cost_obligations.py (+4 tests; planning/cost-obligations.json
  1,377 rows all `none`, cost-contracts.json 48/48 unwitnessed, cost-baseline.json 713
  undeclared compliant, shrink-only; `make check` step added -- the runner's regen must
  run --write after interfaces.json changes).
  NOT DONE: the fn-reader-chunk instance (host/cost-host.lisp, ld'd after host/interfaces.lisp
  in build.lisp; tools/extract/world-host.lisp regenerated by tools/extract/world.py): the
  image-world REPL session `iw` is certifying the changed closure on hbox
  (/tank/fn/gates/def-entry-repl, iw.certify.log); then: send `(ld "../tools/cost-prefix.lisp")`
  (untracked, 44 lds through host/interfaces.lisp), `(ld "../books/def-cost.lisp")`, then
  `(fn-cost-derive 'fn-reader-chunk (w state))` to read the unaccounted list and the
  constant, then the def-cost form with :visits (+ K request-octets) :sizes
  ((request-octets (len octets))) :unaccounted (fn-served-step ...); expect fn-served-step
  unaccounted (too large to inline, recursive below), fn-reader-install-result inlined.
  Also owed: contract witnesses (48 micro-benchmarks under the toolchain record), the
  :stamped rule (generators' NAME-fresh / NAME-stampedp), allocation (:deferred),
  r71-F15 (:outcomes in the entry's ACL2 result; ledger item r71-F15, open).

## Astra's view (consultation c06, gpt-6-astra, read-only at 4aa332295, 879 s)

### Liaison fact-check (codex-liaison-11, 2026-10-03)
Checked in source myself (worktree build/lanes/codex-c06-entry):
- CONFIRMED historical case A: books/store-files.lisp:480-487 records the O(POSTs since open x log length) guard
  (23.2 s / 802 MB at S = n = 10k), fixed by an :exec keyset (:542-545).
- CONFIRMED case B, and it is LIVE in the code on dev: fn-splan-cursor-step's guard is
  (fn-cat-handles-inp (fn-cat-count fn-cat) ...) (books/served-plan-cursor.lisp:161-164), a walk of every catalog row
  (books/catalog-commit.lisp:776-779); the host calls it per OVER quantum under the owner mutex
  (host/native/owner.lisp:515-523); the image runs guard-checking t (host/native/io.lisp:8606) and NO entry is
  raw-dispatched on dev (planning/interfaces.json raw_dispatched [], 0 rows with raw_with). So each quantum is Theta(N)
  and a whole OVER Theta(N^2/W) -- once the cursor arm is reachable (served-catalog-live's "cursor-step guard" item).
- CONFIRMED: the curve fixture "varies N alone"; nothing POSTed past the seed (tools/scale_curve.py:22-29), so neither
  historical quadratic would show on the proposed 1k/10k/100k gate.
- CONFIRMED: dispatched classes 713 common-lisp-compliant / 525 program / 139 ideal (planning/interfaces.json);
  the sketch's class list omits :ideal.
- CONFIRMED: tools/owner_globals_check.py's baseline writer refuses a raise only for paths already present
  (:128-130) and reads the baseline from the working file: not a protected shrink-only ratchet.
- CONFIRMED: fnn-entry-guard checks kind recognizers only, "at most linear in the argument" (io.lisp:1260-1267).
- CONFIRMED: host/owner-retain-host.lisp is not in the tree at 4aa332295; the 229-line version exists at 398f4bfbd.
- NOT CHECKED by me: the def-carried.lisp line citations (:453-559, :1171-1277), definterface.lisp:281-290's fuel,
  throughput_gate.py:699-736, the tier-A statement table (398f4bfbd / f98e1ff1b lines).
Liaison's reading: Astra says BUILD WITH CHANGES, and the changes are large: (1) visit costs DERIVED from the executed
body (primitive/callee summaries, unknown = unaccounted, never zero), not a user V-TERM tied only by a benchmark slope;
(2) stamps/generations carried in the logic instead of a named SBCL EQUAL fact; (3) :writes/effects from a full
fail-closed effect closure, never through :opens; (4) command cost as a trace fold with multiplicities, not a registry
sum; (5) exception sets compared by name against a protected base. For STAGE-5B now: freeze the exact tier-A theorem
statements and generate R+G row theorems FROM the stronger hand theorems rather than renaming them.

### Astra's answer (verbatim)

BUILD WITH THESE CHANGES, in this order:
1. Derive execution costs, including executed guards and callees; an arbitrary visit model plus a slope gate is not a bound on the entry.
2. Make write/effect closure independent of proof hints; check the final image world and exact dispatch route.
3. Compose command traces with multiplicities, size substitutions and progress; never advertise a sum of distinct entry rows as command cost.
4. Make exceptions explicit, counted and compared with a protected prior baseline; include :ideal as well as :program.
Q1 ruling: use maintained stamps/lengths/generations in the logic; a named SBCL EQUAL fact does not establish sharing at a call site.
Q2 ruling: model-plus-slope is insufficient; minimum addition is a body-derived cost semantics with checked primitive/callee summaries and an executable-path correspondence.
Before STAGE-5B writes forms: freeze the historical theorem ABI and source coordinate, settle guard-hypothesis treatment, frame/effect closure, and event ordering (§7–8).

Scope and evidence convention: this is a design consultation, not an implementation or certification. Unqualified paths below refer to the supplied checkout, 4aa332295c85f03f5a97d7b0ac2228f9b95ab1e9. `REV:path:line` identifies a different historical source explicitly. Proposed changes and adversarial constructions below are recommendations, not claims that the constructed defect already exists. Quotes are local source excerpts. The requested tier-A file is absent at the pinned coordinate; I recovered its 229-line version at 398f4bfbd and its revised 243-line version at f98e1ff1b through read-only git history. The exact original r67 review text was not recovered: attribution to its numbered F1 is UNVERIFIED independently of the brief, but the described executed guard walk is established directly below.

## 1. VISIT, the historical quadratics, and sharing — HOLE

**HOLE: the definition leaves the cost of executing a “step” unenforced.** The sketch says “One read of one element of a sized collection” and “Fixed-size scalar work is not a visit” (`build/codex/c06/SKETCH.md:72–77`), followed by the EQUAL/MEMBER exception. That is a potentially useful unit, not yet a semantics for all operations. In particular, a fixed number of operations is not fixed-size work.

### The two real regressions

**Historical case A: success-list guard, commits since open × log length.** The pinned source itself records the regression: `books/store-files.lisp:480–487`, “S = n = 10k cost 23.2 s and 802 MB per evaluation” and “every completed commit appends a success … O(POSTs since open x log length).” The nested logical calls are explicit at `:534–540`: `(fn-sf-record-has-pairp (car successes) records)` followed by `(fn-sf-success-listp (cdr successes) records)`. The record search recurses at `:498–504`. Git history independently locates the repair at 6a7535b37, “fn-sf-success-listp and fn-sf-record-has-pairp in O(S + n), no per-compare consing.” This is not a claim that the old quadratic still executes: the current `:exec` calls `fn-sf-ks-success-listp`, and `:542–545` explicitly says “Reopen has no successes: do not allocate or fill a local keyset.”

**Historical case B: catalog guard per cursor quantum.** The actual boundary is `host/native/owner.lisp:515–523`: “One quantum … under the owner mutex” and `(fnn-call 'fn-splan-cursor-step …)`. The subject's guard is `books/served-plan-cursor.lisp:161–164`: `(fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)`. The recognizer reads one catalog row and recurses down the count, `books/catalog-commit.lisp:776–779`: `(fn-cat-at (- n 1) fn-cat)` and `(fn-cat-handles-inp (- n 1) fn-arena fn-cat)`. Consequently N catalog rows are checked per quantum; a full N-row traversal in fixed Q-sized quanta incurs Θ(N ceil(N/Q)) guard-row reads. This is a derivation from that code, not a fresh timing measurement. The NEWNEWS integration was present on e79d0c0ad; its `books/served-plan-cursor.lisp:99–105` says the plan may carry NEWNEWS and “fn-nnwp-step: at most (max 1 W) articles read.” History commit 6c6066cbd explicitly says “NEWNEWS e79d0c0ad NOT taken (Codex r67).” The specific original F1 wording remains UNVERIFIED; the mechanism does not depend on trusting that report.

| Regression | Expansion as sketched | Visit theorem as sketched | Gate as sketched |
|---|---|---|---|
| Success guard, S commits since open and N records | No cost derivation to reject the omitted nested scan. `:paid` helps only if its guard model is complete. | Can prove a body-only or zero V; an accurate guard-inclusive V would expose Θ(SN), but it is user supplied. | Can miss it: S=0 after reopen, or a fixed small S at each N, does not test S≈N. |
| Catalog guard per quantum | No enforced rejection of the walk; paying it is not the same as enforcing a Q-sized scheduling bound. | A body-only V≤Q misses it; an accurate V has an N term per call. It still needs call multiplicity to expose total Θ(N²/Q). | A whole-command guard-enabled cursor probe can expose it. A helper/body probe, missing cursor workload, or a declared N-dependent per-call bound can pass. |

The fixture blind spot is concrete: `tools/scale_curve.py:22–29` says “nothing is POSTed past the seed” and “the curve varies N alone”; the POST probe at `:297` runs `range(50)`. Neither description supplies the independent S≈N dimension. The proposed benchmark hook only says “runs them at 1k/10k/100k on the curve fixture” (`SKETCH.md:56–61`), so neither historical case is guaranteed to be caught at any of its three layers.

### Primitive and hidden-call constructions

**HOLE: structural EQUAL and MEMBER.** Take a carried list L and a separately allocated, equal copy L′ after reload. `equal(L,L′)` must distinguish all relevant elements despite both values satisfying logical equality and the carry invariant. Repeat that comparison at each of N steps. Naming A-SBCL-EQUAL-SHARED does not make L and L′ share storage. Worse, even if each MEMBER element comparison were constant-time, MEMBER still searches the list. An eq-first EQUAL fact does not make MEMBER O(1) except under an additional bound on search distance. The sibling reader actually generates `(equal WS (NAME-WS C))` (`generators-2.md:90`) before FAST, and its supposed structural restriction only refuses “a :fast term that mentions WS” (`:92–94`). FAST can traverse `(NAME-WS C)` or an alias, and the precondition/probe can traverse it even if FAST does not. Require a transitive read/cost analysis of the entire executed reader, not a lexical ban on one formal.

**HOLE: ordinary list primitives inside scalar steps.** A loop whose step uses `(nth i xs)`, `(update-nth i v xs)`, `(len xs)`, `(assoc k xs)`, `(member k xs)`, `(remove k xs)`, `(append xs ys)` or `(revappend xs ys)` can perform Θ(N) hidden work per iteration. Charge each traversed cell, comparison substructure, and copied cell; include allocation separately. “One record read” must not hide recursively checking or serializing a variable-length record.

**WEAK: hash tables, arrays and numerics.** A scalar array access can be one memory visit under a declared fixed-width index/runtime representation. That does not charge resizing, initialization, hashing a long key, collision chains, page faults or allocation. Distinguish worst-case bounds from expected/amortized bounds and specify any adversary assumptions. A bignum is not fixed-size; addition, comparison and decimal formatting need bit/digit sizes. Count string/octet-vector scanning, copying, comparing and rendering by inspected/written units, not one library call. A byte bound on allocation alone also misses allocating many tiny objects, zeroing/reinitialization, retention and GC work. Recommended resource vector: reads by representation, writes, scalar/limb operations, allocation bytes/objects, and I/O operations/bytes; visits alone remain one named component.

**HOLE: hidden callees, interface recursion and guards.** A helper outside `:opens` can do the entire walk. A recursive interface call with its own cost row must contribute its instantiated bound at EACH executed call, not merely possess a separate row. The same applies to guards, `mbt`, attachments and selected `mbe :exec` implementations. `:opens` is described as “callees the generated proof unfolds” (`SKETCH.md:22`); proof unfolding permissions must never determine runtime accounting.

### Named host fact or stamp?

**Ruling: stamp, with a proved maintained relation.** Carry an identity/incarnation, generation or prefix position and length with the indexed data; prove what equal stamps imply about the relevant contents and what each mutation does to the stamp. A length alone is insufficient: two different lists can have the same length. Prevent reuse/ABA across recovery, copying and replacement. For prefix refresh, prove lineage/position and fold only the new range; a current-version stamp alone does not prove a new list is an extension. Charge stamp creation/update, fixed fields per carry, delta maintenance, and the cold rebuild once. If counters are arbitrary naturals, expose their bit-width cost; if fixed-width, prove profile representability and an explicit rollover/incarnation protocol rather than truncation. This fits D27's requirement that codec widths “never cap[] below any profile the operator can write” (`planning/decisions.md:1194–1203`).

**HOLE if a spec row is used as a proof assumption.** `AGENTS.md:90–92` says “A named assumption is an encapsulate … and the theorems that use it mention it.” An encapsulated EQUAL-cost function over an explicit heap and sharing predicate could constrain a *model* of shared comparison, with a local witness. It would not prove SBCL obeys that model, and every use would still need the sharing premise. ACL2 value equality by itself does not specify physical cons identity or runtime cost. An encapsulate over an unrelated cost oracle would merely hide the desired conclusion.

There is already an explicit distinction in the project: `specs/failures.md:25` describes A-SBCL-RUNTIME as “a trust-boundary entry … not an ACL2 constraint, and no theorem cites it”; `:34` says an encapsulate over an uninterpreted evaluator “would constrain nothing a theorem uses.” In contrast, `books/assumptions-pgs-host-io.lisp:83–103` supplies actual constrained functions, local witnesses, and `(equal (fn-pgs-fill-realize file addr) (fn-pgs-page-words file addr))`. Keep runtime/toolchain facts in a separate qualification category. Do not present a runtime fact string as a discharged logical hypothesis. A qualified shared-EQUAL optimization may supplement the stamped design; it cannot be the unchecked foundation of the visit proof.

## 2. V-TERM, the benchmark tie and ATTAINS — HOLE

**HOLE: a true theorem about an unrelated model.** The declared pair is explicitly “V-TERM: a visit model over the formals” (`SKETCH.md:27`); the generated theorem is `(implies G (<= V B))` (`:50–51`). Choose V=0, B=0 for a body that traverses a list twice nested. The theorem, its full-antecedent positive, and the attainment witness can all be true. Matching the owed pair against teeth only ensures two declarations agree. Alternatively choose a plausible hand model counting one outer traversal and omit its inner membership walk. Nothing in the proposed preservation theorem connects those counters to execution. The sketch acknowledges the separation: “the theorem is about the visit model; the gate ties the model to the bytes” (`:60–61`). That empirical tie is insufficient for a universal worst-case claim.

**HOLE: finite slopes cannot supply the missing universal premise.** Constructions that pass a small fit include:

- T(N)=aN+εN² with crossover above the sampled range; fitting a near-linear slope below 100k says nothing about larger supported profiles.
- A quadratic only when pins/releases, commits since open, withdrawals, group count, connections or long identifiers grow. Holding that dimension at zero or a constant hides it.
- A costly last-match, collision, cache-miss, refusal, cancellation or recovery branch absent from the fixture.
- Guard-disabled or raw helper timing for a counterpart-dispatched boundary that actually checks guards; warm-cache measurements for a cold-read claim.
- B(N,P)=NP with only N=P points: the diagonal cannot determine the separate exponents or validate the size substitutions at each call. Conversely a term independent of the varied dimension can look constant while unbounded in another.

These are mathematical counterexamples, not observations of new runtime failures. The actual fixture's “curve varies N alone” quote above makes the second construction immediately relevant. The existing throughput tool is not a substitute for the proposed fail-closed gate: `tools/throughput_gate.py:699–702` prints “NOT MEASURED” and returns 0 when no ancestor run exists; `:723–725` reports STALE, and `:734–736` permits a named regression cause. Preserve those meanings if useful, but a cost-claim gate must separately reject missing/inapplicable evidence rather than inherit that success exit.

**Minimum sound addition: derived costs for a deliberately small executable language.** Replace free V with an automatically generated companion from the executed body/IR. Keep B user-written as the theorem to prove. Start with admitted primitives and the loop library, not a general interpreter for all ACL2:

1. Every allowed primitive has a cost/effect contract tied to its representation. Unknown primitives/callees cause `unaccounted`, never zero.
2. Derive sequential sums, branch-selected costs, loop recurrences and allocation from the body, including costs of size extraction and tests. Use a proved callee summary with actual arguments substituted, or expand it. Recursive SCCs require a joint recurrence/measure; no opaque recursive “summary” that assumes its own bound.
3. Generate the value/state projection correspondence and cost recurrence together. Value equality alone does not establish a cost correspondence: a clone returning the same value can have a different algorithm. Reuse exactly the same control/data-flow representation, with a checked derivation or small verified interpretation, and account for the compiler/runtime boundary explicitly.
4. Instrument the selected execution closure: actual `mbe` arm, attachments/stobj exports, dispatch mode and the guards evaluated there. A def-loop iteration counter suffices only if the step's nested primitive/callee costs are also derived.
5. Prove `derived-cost(args) <= B(sizes(args))` under stated domains; distinguish valid-entry cost from host refusal cost on malformed inputs. Hash/digest the body, guard, representations and callee summaries used so a changed closure invalidates the certificate and hook.

This is the cheapest honest version because unsupported functions remain visible migration debt, while a small approved vocabulary gains a real argument. An instrumented clone for arbitrary forms is more ambitious, especially for stobjs, callbacks, attachments and raw host effects. Do not pretend the restricted implementation covers those until its lowering rules do.

**WEAK: “order from BOUND's degree.”** Arbitrary ACL2 terms need not be polynomials; max/min, logarithms, piecewise costs and amortized potentials have no single useful syntactic degree. Require a typed bound DSL with explicit units, domain, size dependencies and worst-case/amortized classification. A runtime gate should record exact counters where available, guard/dispatch settings, body and image digests, independent dimension sweeps, cold/warm conditions, mixed live histories and worst-case witnesses. Slopes remain regression evidence, not proof.

**SOUND for a narrow purpose: ATTAINS establishes one tight example in the model.** The sibling says `(HYPS and (equal V B))` and also permits `:none "why"` (`generators-2.md:25,37–41`). It can reject some gratuitously loose bounds. It cannot establish that V describes the body, worst-case coverage over sizes, asymptotic tightness, or reachability from initialization. V=B=0 attains everywhere; V=N and B=N² attains at N=0 and N=1. Require a positive, nondegenerate witness and, if claiming asymptotic tightness, a parameterized family/lower-bound result. Do not reject every safe but unattained upper bound: rounded budgets can be valid. Label its tightness status separately and count `:none` exceptions.

## 3. Guard accounting and raw dispatch — HOLE in the proposed cost contract; SOUND reusable row checks

**The current paths are different.** `host/native/io.lisp:1354–1370` makes `fnn-entry-guard` check arity and call each recognized kind predicate: `(unless (funcall recognizer value) …)`. `:1300–1307` selects unary conjuncts over non-stobj formals from `*fn-entry-guard-kinds*`. The header is precise: kind predicates are “at most linear in the argument” (`:1260–1263`), while other guard conjuncts are “never evaluated here” (`:1265–1267`). Therefore `:kinds-only` does not mean constant-time or free.

`fnn-call` first executes that boundary check, then applies `fnn-dispatch-function` (`io.lisp:1378–1384`). The selector chooses the raw function only when its table has an entry and the counterpart selector is off, otherwise `fnn-counterpart` (`:1249–1255`). The current committed registry has `"raw_dispatched": 0`, `"raw_dispatched": []`, `"raw_guarded": []` (`planning/interfaces.json:4–12`); the generated raw declaration file contains only the three direct checker declarations (`host/interfaces-raw.lisp:1–7`). Thus **no declared entry at this source coordinate is configured to skip the counterpart guard through this table**. This is a source/registry conclusion, not a statement about a separately deployed image. The code supports skipping, but that support is not activation.

D40 explicitly preserves this distinction: `planning/decisions.md:1597–1605` says “The entry guard (arity and kind checks) still runs before either dispatch” and requires every other relevant conjunct to be over “stobj formals alone.” The decision is a guard-preservation rule, not a declaration that kind checks or all interior work are free.

**HOLE: paying “C's visits” is not necessarily paying the executed guard.** For non-raw entries the counterpart evaluates the full guard, not merely the carried relation selected by the declaration. The runtime's own description says “evaluates the entry's whole guard and then runs the raw definition” (`io.lisp:1170–1183`). The carry recognizer is not always the literal guard, and kinds can be checked at the host boundary and again in the counterpart. Account for both when executed; do not double-count a skipped guard. Include stobj recognition, relation checks and boot-strap checks where they actually run. Cost-producing an expression such as `(len xs)` to define a size is also work if the host evaluates it at runtime.

**HOLE: :paid must not legalize a served whole-state walk.** `AGENTS.md:95–96` says “No whole-state revalidation on a served path.” The carried owner relation is itself marked “Proof-only … Never called by native serving code or used as an executable guard” (`books/owner-retain-transitions.lisp:48–54`). Adding its whole-state cost to V would make accounting more truthful, but would not satisfy that architectural rule. Require a separate served-path exclusion: carried whole-state predicates are proof-only there, established at an allowed boundary and preserved. `:paid` is appropriate only for admissible bounded local checks or explicitly classified cold/open work.

**WEAK: `fn-cd-raw-problem=nil` is necessary row evidence, not the complete dispatch condition.** Its actual checks are substantial:

- `books/def-carried.lisp:1257–1277` requires a listed transition, a stobj carrier, and a regenerated valid row.
- The requirement table at `:1171–1175` requires transitions `:no-hyps`, and opens `:witnessed-reaches :hyps-iff-produced :producers-exact :not-an-interface :not-attached :produced-formal :no-unproduced-caller`.
- `:1186–1189` rejects extra transition hypotheses because “the host does not check them.” `:1212–1238` checks the produced-open boundary and scans world callers.
- Completeness derives from **all declared entries returning the carrier**, `:753–759` and `:786–808`, not from a list of global keys or just the functions a proof opens.

But coverage of every omitted guard conjunct is a separate check. `books/definterface.lisp:540–580` invokes both `fn-cd-raw-problem` and `fn-cd-uncovered-conjunct`, checks `:common-lisp-compliant`, and refuses a conjunct constraining an unchecked host-passed argument. Merely quoting the first predicate misses those obligations and the actual route selection. Image installation also checks function availability/class and rejects macros (`io.lisp:1220–1241`). Proposed change: `:skipped` is derived from the fully validated final-world interface route, never freely asserted; require the complete `fn-di-problem` checks plus runtime mode in the cost coordinate. Counterpart developer runs need their own costs.

**WEAK: interior guards and alternate paths.** Do not assume every callee guard executes, nor assume none do. `specs/failures.md:34` explicitly distinguishes “inside an invariant-risk :program body each call checks its callee's guard” from an interior proved guard obligation that “is not checked.” Model the selected route. Inspect `mbt` and `mbe` under actual execution rules, including `ec-call`/counterpart crossings; do not count a logical arm that never executes or omit an executed check. The fixed-callback route is another distinct boundary: `io.lisp:1394–1408` returns a startup-selected raw callback and refuses counterpart mode; `:1411–1414` says it preserves scalar MVs “without an argument or result container.” A one-entry declaration needs a route list covering this ABI as well as `fnn-call`.

## 4. Writes derived “through :opens” — HOLE

**Construction.** Define an entry returning state that calls `hidden-writer(state)`, where the helper performs `(f-put-global 'fn-owner forged state)`. Leave the helper out of `:opens` and declare `:writes ()`. A traversal limited by those hints has nothing to compare with the declaration. If the generic invariant-preservation theorem rejects a corrupt owner, that protects one invariant; it does not establish the promised complete write set. The helper can instead change another global while preserving R, and the preservation proof passes. The relevant promise is literally “put-global keys reachable from NAME's body through :opens must equal :writes” (`SKETCH.md:44–47`).

| Escape/test | Assessment | Required behavior |
|---|---|---|
| Unopened callee receiving state | HOLE | Follow the complete effect closure or consume a checked effect summary, irrespective of proof hints. |
| :program helper | HOLE for program entries; logic admissibility may already reject particular logic→program calls | Treat program bodies as effectful inspectable code, not opaque purity. If unresolved, mark unknown and refuse an exact claim. |
| Macro expanding to f-put-global/assign/updater | HOLE for a surface token scan | Expand in the ACL2 world and inspect translated operations, including generated accessors/updaters. |
| Computed key `(f-put-global key …)` | HOLE | Derive/prove a finite key set or declare a conservative region/all-globals effect. Never silently ignore a non-quoted key. |
| `with-local-state`/local stobj | WEAK | Track fresh local regions and escape; account for local work/allocation even when no persistent state escapes. Do not label every local write a live global write. |
| Stobj field/array update | HOLE in global-only vocabulary | Region/field/index-range effects over the actual carrier; include resizes, abstract exports and backing implementations. |
| Raw host caller/callback mutation | HOLE outside the ACL2 world | Separate host effect contract and complete host closure, bound to that entry's callers/routes. |
| make-event/generated definitions | WEAK | Check after event expansion in the final world; compile-time state effects are a separate phase from served runtime effects. Recheck later additions. |

**Source tools do not already provide the promised analysis.** `tools/owner_globals_check.py:16–22` explicitly counts tokens ending in `-global` “followed by the quoted name,” “Source-level, no ACL2”; its `ACCESSOR` regex is at `:43–44`. It scans `host/` (`:42,84–90`), not every translated callee or stobj update. The existing world walk in `books/def-carried.lisp:1119–1128` does use `'unnormalized-body`, but its purpose is finding calls with unproduced actual arguments, not collecting writes. The returning-carrier completeness test quoted in §3 is conservative coverage of interface entries, not write-set extraction.

**Concrete replacement.** Let `:opens` remain solely a proof hint. Derive `:writes`/`:reads` from an effect analysis over all reachable translated definitions, closures resolved to a fixed point, with unknown effects failing closed. Carry symbolic actual-argument substitutions, alias/region information and abstract-stobj summaries. Define “writes” as a conservative MAY-write footprint; exact feasible write sets are generally too expensive to infer. If exactness is desired, state separately whether it means exact syntactic union or exact reachable effects, and prove reductions of the conservative set.

`unnormalized-body` gives useful translated terms but is not, by itself, a guarantee that a generic tree walk follows executed semantics. It must handle lambda applications, `return-last` encodings, `mbe :exec`, `ec-call`, attachments and stobj export realizations. For effect safety, a conservative union of alternatives is acceptable; for runtime cost, selecting the executed arm matters. The existing call-closure helper has an explicit fuel `N` (`books/definterface.lisp:281–290`: “at most N functions,” returning `seen` when `zp n`). Do not copy a silent truncation into a fail-closed effect checker: exhaustion must report incomplete analysis.

**WEAK: installer provenance needs a contract, not a named theorem nearby.** The sketch says the installer argument is one “a :via covers” (`SKETCH.md:46–47`). Require an instantiated theorem that establishes the invariant of the exact value installed on every installation path, including refusal/error paths; a theorem merely mentioning the installer or another computed value is insufficient. Local state rebinding and multiple installs are useful negative tests. Preserve frame facts for everything outside the may-write region.

## 5. Fail-closed claims — mostly HOLE

### (a) Shrink-only baseline — HOLE

The sketch invokes “the tree's ratchet pattern” (`SKETCH.md:81–84`). One concrete existing ratchet is `tools/owner_globals_check.py`: it reads the baseline from the current working file (`:119,127`), compares counts (`:94–108`), and its writer refuses increases only for paths already present (`:128–135`: `if p in baseline and len(n) > baseline[p]`). It does not compare with a trusted git ancestor. Thus hand-editing the baseline to a larger value defeats the check; adding a new file is also accepted by that writer despite the prose “only shrinks.” This is enforcement against the supplied baseline plus a partly guarded regeneration path, not historical monotonicity.

**Change:** compare the exception NAME SET against a coordinator-selected protected base/merge-base outside candidate control; require `new ⊆ old`, retaining identity and reason, not just a count. Prevent exchanging one exception for a different one at the same count. A disappeared dispatched function should retire its exception. Regeneration must use the same comparison, and CI must own the base revision. A documented, separately reviewed exception can remain possible without falsely calling the ordinary path shrink-only.

### (b) :program and the omitted :ideal class — HOLE

The sketch says “:class :program: the row only, registry-marked, no theorem claimed” (`SKETCH.md:83–84`) and its syntax lists only `:common-lisp-compliant | :program` (`:17`). Actual `definterface` accepts `(:common-lisp-compliant :ideal :program)` (`books/definterface.lisp:102`) and checks the declared class against the world (`:657–659`). The committed registry reports 1,411 declarations, 1,377 declared-and-dispatched, 742 guard-verified (`planning/interfaces.json:4–9`: `"declared": 1411`, `"declared_and_dispatched": 1377`, `"guard_verified": 742`). Counting its literal `entries[].class`, restricted by nonempty `dispatched_from`, gives:

| Class | All declared | Dispatched |
|---|---:|---:|
| common-lisp-compliant | 742 | 713 |
| program | 530 | 525 |
| ideal | 139 | 139 |
| Total | 1,411 | 1,377 |

Reproduce the derived numbers using stdlib JSON and `Counter(r["class"] for r in doc["entries"] if r["dispatched_from"])`; row fields come from `tools/interface_emit.py:370–385`, specifically `"class": d["class"]` and `"dispatched_from": sorted(...)`. Three further program entries are direct-only, so the dispatched-or-direct program union is 528; the three named build checkers are visible in `host/interfaces-raw.lisp:5–7`. Do not call those three served work. The dispatched program population spans owner, admin/operator, store, control, peer/feed, BP, NNTP/served and web in that registry; this is entry coverage, **not a measured percentage of runtime**.

525/1,377 = 38.1% of dispatched entries would receive no cost theorem under the explicit program exception. Another 139/1,377 = 10.1% have no class path in the sketch. Hence 48.2% are outside its guard-verified class, not “roughly a program half” as a precise count. Per-entry class is visible today; an explicit `program-dispatched`, `ideal-dispatched`, `cost-proved`, `cost-unaccounted` subtotal is not in the emitted coverage dictionary (`interface_emit.py:395–401`, whose fields are declared, declared_and_dispatched, guard_verified, with_keystone, raw_dispatched).

**Change:** accept all current classes as migration records, but emit distinct claim status; no command gets a proved complete bound through an unaccounted entry. Require program/ideal exceptions to shrink by identity and identify affected command routes. A :program wrapper can eventually delegate to a proved logic subject, but value/effect/cost correspondence and guard behavior must be established; a row alone is not that result.

### (c) Allocation (:none "why") — HOLE

The syntax permits `:allocation … | (:none "why")` (`SKETCH.md:28`) while the prose says “Allocation is a second figure, never folded into visits” (`:77`). A textual reason is not proof of zero allocation and is not a complete allocation bound. Construction: cons a list and supply “temporary only”; the claimed visit theorem says nothing about those bytes.

**Change:** distinguish `:zero` with a derived zero-allocation proof, `:bounded` with units and a proved bound, and `:unaccounted` with an exception ID. Count and ratchet the last category. Include ephemeral allocations, result/argument containers, backing-store growth and error paths; separately report peak live storage, retained storage and reserved capacity. `:none` must not disappear from totals or mean both “none spent” and “no claim.”

### (d) Durable effects and harness_check — HOLE

The sketch relies on “harness_check's reading” to reject `:effects :none` for a durable raw caller (`SKETCH.md:65–68`). The actual reused reader in `tools/interface_emit.py:325–346` calls `harness_check.raw_applications`, records quoted dispatches and direct calls, and returns `{dispatched, direct, defined, entries}`. It supplies call inventory, not an effect proof. `tools/harness_check.py:63–74` describes entry-guards, test-stubs and test-harness-reach; none is a durable-syscall summary.

Construction: raw caller A dispatches E and calls helper B, which fsyncs/renames, possibly via a callback. A lexical scan of A admits `:none`. The more relevant existing checker, `tools/native_program_check.py:16–18`, expands called io.lisp functions, but explicitly cannot decide callbacks, definitions outside io.lisp or callers (`:35–43`). Its `PROGRAM_HOSTS` maps only finish and staging cleanup (`:75–78`); it points to a separate log-route check at `:70–74`. None is an all-host transitive effect inventory.

**Change:** declare the host route/caller relation and collect durable primitive effects transitively, including callbacks or explicit validated summaries. Unknown effects reject `:none`. Bind declared programs/cuts to actual reachable effect traces and all error arms; cutting a list out of a program definition does not prove the host follows it. Retain a distinct crash-relevant process-local/rebuild category. The model's own requirement is stronger than just listing preexisting injection points: `books/byte-store-programs.lisp:15–20` says “a :cut follows every durable syscall, not only the host's present faults.at sites.”

**SOUND ownership boundary, incomplete enforcement:** one holder-owned cut source is the right way to avoid divergence. `SKETCH.md:104–106` says def-entry “reads that row … and emits no cut of its own”; `def-holder.md:162–169` generates holder cuts and refuses a durable CUT absent from PROGRAM. Keep that single source, but require host-site coverage, unique names and exact holder/program/phase association. The def-entry top-level grammar at `SKETCH.md:24` lists only `:none | (:durable PROGRAM)` while its later text uses `(:release HOLDER)`; fix the grammar before consumers implement it.

### (e) :rests-on spec rows — HOLE if treated as logical assumptions

A named row in prose is not an encapsulate. `SKETCH.md:30` describes `:rests-on` as “host cost facts, named rows of specs/failures.md”; `AGENTS.md:90–92` demands the encapsulate and actual theorem use. As §1 shows, the spec deliberately contains both formal assumptions and runtime trust-boundary facts.

**Change:** separate `:assumes ((CONSTRAINED-PRED actuals…) …)` from `:runtime-facts (FACT-ID …)`. Validate formal provenance and literal theorem use against the world, and runtime facts against a qualified toolchain/representation record. `books/def-carried.lisp:565–573` already makes provenance explicit: “the innermost book on the include-book path … never its spelling.” Do not invent a fake encapsulate to satisfy the spelling of the rule.

## 6. Command cost as a SUM — HOLE

The stated boundary is unambiguous: “a command's cost is the registry's sum of its entries' rows (composition, not a theorem)” (`SKETCH.md:103–104`). A sum of distinct rows is generally not even a correct estimate of a command's resource use.

**Constructions:** an entry costing B is called N times for a range; a Q-cost entry runs ceil(N/Q) quanta; an early refusal repeats after each incoming chunk; a retry loop invokes an entry without progress; an entry maintains a growing list so its kth call costs k. Summing one copy loses multiplicity and state evolution. Summing `B_i(N)` also silently equates incompatible N's: catalog rows, group members, bytes, releases and available credits are different measures. Host dispatch, kind checks, rendering, synchronization and syscall work between entries do not belong to any body row unless explicitly assigned. Summing inclusive callee costs and then adding those callees again double-counts them; summing exclusive costs without multiplicities undercounts them.

The catalog case is a concrete composition counterexample: `books/served-plan-cursor.lisp:24–27` describes `fn-splan-cw-drain` as “N rounds, each a cursor quantum … or a window of W octets.” Its host counterpart quoted in §1 repeatedly enters the full catalog guard. A correct per-call O(N+Q) row cannot become a command bound merely by appearing once in the command registry.

**Smallest honest theorem:** start with a fuel-bounded trace of the composed command machine, including boundary and adapter steps. Define total cost as the fold of derived step costs, prove that the executable command's trace refines that machine, and prove an upper bound for every prefix of at most K scheduled steps. Use size-map invariants to instantiate each entry's bound at the state where it is called. This provides a real per-prefix/per-quantum safety result without claiming the socket eventually drains.

Then add a separate potential/progress theorem for productive quanta: nonterminal internal work either decreases a well-founded remaining-work potential by a quantified amount, or yields with its continuation intact; waiting/retries consume a separately bounded budget or remain explicitly unbounded in total. A theorem saying merely “at most Q items” does not lower-bound progress. For an exact ceil(N/Q) count, show full productive quanta consume Q except the terminal one; decreasing by at least one proves only at most N productive quanta. Charge scanning nonmatching candidates as work. Include emitted bytes and their rendering quanta, not only article selection.

**Change:** command rows carry a proved trace-cost expression with call multiplicities and argument/size substitutions, or are explicitly labeled an unproved inventory with unknown total. Never expose the latter as admission accounting. Carry the principal/budget through continuation, cancellation and error transitions. This implements the existing requirement `AGENTS.md:41–45`, “Bound work and allocation per scheduling step … exhausting a work quantum yields or resumes, it never silently truncates data.” Total latency and eventual completion additionally require environment assumptions, not a visit theorem alone.

## 7. def-owner-writer and the 229 hand lines — WEAK generator scope; HOLE in the same-statement promise

### Establish the coordinate before migration

The sketch promises “Tier A's 229 hand lines become ~40 declarations with the same theorem names” (`SKETCH.md:96–97`). That source is not in the pinned tree. Read-only history gives an exact 229-line file at `398f4bfbd:host/owner-retain-host.lisp`; f98e1ff1b revises it to 243 lines. Those are different theorem contracts, not interchangeable copies. At 398f4bfbd `:214–218`, `fn-owner-io-preserves-retain-state` assumes both R and `(fn-owner-io-safep … operation result)`; at f98e1ff1b `:214–216`, it assumes only R. The latter also adds `:234–239`, the refusal word and unchanged-state theorem. Freeze the intended coordinate; the later strengthened version is the sensible migration target, but this consultation does not integrate it.

The named tier-A events are not found in the pinned `planning/proofs.json`: read-only exact-string searches for `fn-orh-`, `fn-owner-close-preserves-retain-state`, `fn-owner-prepare-identity-preserves-retain-state`, and `fn-owner-retain-carried` returned zero. Consequently **the brief's claim that PRF IDs currently cite those particular hand names is UNVERIFIED** at this coordinate; I will not invent IDs. The registry association for the later lane must be supplied/generated before migration. This limitation does not prevent inspecting the actual statements.

### What fits and what does not

The historical file describes each writer statement as `(implies (fn-owner-retain-statep state) (fn-owner-retain-statep STATE-RETURNED))` (`398f4bfbd:host/owner-retain-host.lisp:15–16`). Many writer leaves really have that shape:

| Historical source (398f4bfbd unless noted) | Quoted shape | Generator assessment |
|---|---|---|
| `host/owner-retain-host.lisp:71–74` | R of `(fn-owner-install-effects effects state)` | Direct state result fits. |
| `:77–89` | R of `(mv-nth 2 (fn-owner-close id fn-arena state))`; `:use … (oc (fn-owner-ocfg state))` | Fits if the actual stobj result slot, formal names and explicit substitutions are preserved. |
| `:106–120` | open-peer result at mv-nth 2; substitutions `(peer (fn-store-octets->string peer-octets))` and `(acfg (fn-owner-auth state))` | Requires these substitutions, not just default `oc`. |
| `:148–154`, `:165–172` | R of `(fn-owner-step (list :take) …)` / `(list :control-submit msgid groups octets)` | Specialized event lemmas need `:step` to preserve exact event term and historical name. |
| `:189–196` | `(and (fn-lgoc-invariantp oc) (mv-nth 3 (fn-idrp-prepare-retention …)))` implies invariant of `mv-nth 1` | Not an R(state) preservation theorem: keep as a hand/another-schema lemma. |
| `:214–218` | R AND `fn-owner-io-safep` | Old extra premise cannot be erased by choosing a convenient schema; use the later proved strengthening, explicitly. |
| `f98e1ff1b:host/owner-retain-host.lisp:234–239` | `(and (equal (mv-nth 1 …) :unsafe-observation) (equal (mv-nth 2 …) state))` | Outcome plus frame equality, not merely preservation. Keep separately. |

The four frame lemmas are not all the generic writer shape either. `398f4bfbd:host/owner-retain-host.lisp:30–34` is an **equality** between R before/after an arbitrary other-global put, under `(not (equal key 'fn-owner))` and `(not (equal key 'fn-owner-retain-carry))`. `:46–49` needs the extra `(fn-lgoc-invariantp oc)` for install-ocfg. `:55–66` gives the two simpler preserve-R frames. `:40–44` makes `fn-owner-retain-statep-implies-lgoc` `:rule-classes nil`; the ordinary writer defthms above omit that override. Keep the frame library and nonuniform lemmas; “one writer declaration” need not mean forcing every auxiliary theorem into its schema.

### Exact statements, guards, variables and rule classes

**HOLE: `(and R G)` is not the old R-only statement.** The proposed generator emits `(implies (and (R s) G) (R RET))` (`SKETCH.md:39–43`). Existing `def-carried` deliberately builds guard-plus-extra hypotheses: `books/def-carried.lisp:453–461`, “FN's guard then the declared :hyps”; `:516–527` adds R for a carries theorem. Historical writer keystones above are often stronger, with R alone. Even if R implies G, adding G changes the literal theorem and its teeth, and can lose useful rewriting applicability. Do not silently reuse the old name for the weaker statement.

Recommended split: preserve the original stronger hand-name theorem exactly, use it to prove the generated row theorem with R+G, and only collapse names after explicitly deciding which is the keystone and updating all consumers. If a new stronger theorem removes a redundant guard, prove it and give that theorem the teeth. This also resolves a generator conflict: `generators-2.md:40` refuses “a hypothesis with no break.” If R implies a generated G, there cannot be a witness retaining R while failing G. Automated insertion of redundant guard hypotheses is incompatible with demanding an independent removal witness for every literal hypothesis. Such derived row obligations should not be mistaken for independently toothed keystones.

**SOUND existing return-slot derivation, within its domain.** `books/def-carried.lisp:469–490` derives the output of the SAME input stobj, rejects multiple congruent input slots, and selects `(mv-nth K call)` only when the function has multiple outputs. Reuse this; never hard-code mv-nth 2. The existing open illustrates another needed shape: `books/owner-retain-carried.lisp:131–140` establishes R at `mv-nth 5` conditional on `mv-nth 1 = :recovering`, with a separate premise; its row records `:ok`, `:hyps`, `:produced` and a witness at `:189–203`. A preservation-only macro must not absorb an establishing transition by accident.

**WEAK: “same names” does not preserve theorem ABI.** Preserve formal variable names used by `:instance`, event term shape, hypothesis/conjunct order for literal tooling, and rule classes/enabledness. Logical implication is insensitive to conjunction order; ordinary named `:instance` binds variables, not positional hypotheses. Thus do not claim ACL2 :use semantically depends on hypothesis order. Literal teeth labels do depend on positions (`generators-2.md:31–34`), and syntactic statement comparison/hints may distinguish forms. The sketch's new `fn-owner-step-at-EVENT` naming (`SKETCH.md:92–93`) also differs from the old `fn-owner-step-take-preserves-retain-state`; offer an explicit preserved-name field or deterministic compatibility naming.

**What already detects statement drift:** `books/def-carried.lisp:558–563` compares the world's formula with the regenerated statement using `(not (equal formula statement))`. This protects generated row names against the current schema, not a historical hand theorem against a changed schema. `books/defkeystone.lisp:27–30` emits a world formula equality only with `:restates`. `tools/ledger.py:1498–1520` hashes theorem statements to invalidate suspect-analysis caches; its comment says that is “everything suspect_reasons reads,” not a historical theorem-contract ratchet. Event association at `:4002–4006` looks up names. No frozen cross-revision contract check for these hand names was established by the inspected files; a claim that some separate global redundancy check supplies it is UNVERIFIED.

**Before writing STAGE-5B forms:** capture each migrated theorem's actual world/source statement, rule classes and variable spelling at the selected source; pin exact expected expansions; compare before/after in a source/image migration test; retain nonuniform helpers; instantiate all existing :via substitutions; specify the new carrier/field effect vocabulary before moving globals into a stobj. Measure the whole old versus generated proof family, including its consumers. The brief permits no ACL2 here, so this report makes no admission or proof-cost claim.

## 8. Missing obligations and integration order — HOLE unless made explicit

**HOLE: the charged principal and reservation lifecycle.** The form's cost fields name sizes, visits, allocation, guard, runtime facts and fixture (`SKETCH.md:26–33`), but not who is charged or when a reservation is consumed/refunded. Add principal/request identity, resource account, reservation/funding precondition, per-step debit, ownership transfer, exact release/refund, and outcome semantics. Maintenance, shared caches, speculative work, recovery and malformed-input handling need a policy for attribution. A numerical bound is not full up-front accounting until the system checks and reserves the resource before spending it. This recommendation applies the consultation's express requirement: “full up-front accounting of every resource spent for a user is a founding goal” (`build/codex/c06/CONSULT.md:13–14`).

**HOLE: visits do not bound latency, blocking or mutex occupancy.** The cursor literally runs “under the owner mutex” (`host/native/owner.lisp:515–518`). A memory visit count says nothing about fsync, page-in delay, lock contention, sleeping, queueing, retries or scheduler fairness. The byte-program vocabulary explicitly includes `:write-all`, `:fsync-file`, `:fsync-dir`, rename and unlink (`books/byte-store-programs.lisp:40–49`). Give I/O requests/bytes/page faults their own counters and execution contexts; distinguish CPU service cost, blocking time and maximum non-yielding critical-section work. Any latency theorem must name environment assumptions. Cancellation must bound work to the next observation and charge cleanup/remaining holds; cancellation is not permission to refund resources still used by an in-flight worker.

**HOLE: only good-input costs leave hostile/error paths uncovered.** The cost theorem's G scopes its guarantee (`SKETCH.md:50–51`). A malformed argument may be rejected before G, after an expensive kind walk or during diagnostic construction. `host/native/io.lisp:1335–1350` calls its error description bounded, but a list diagnostic still loops up to 1,000,000 cells and integer formatting prints `~d`. That is real boundary work absent from a valid-input body theorem. Include invalid-kind, refused, uncertain, crash/recovery, cancellation and partial-output paths in the boundary machine. Preserve distinct outcomes as required by `AGENTS.md:97–98`, “Uncertain, refused and accepted stay distinct.”

**WEAK: “reachable” currently means less than command reachability.** The sketch calls a supplied argument tuple a “reachable positive” (`SKETCH.md:31`). `books/def-carried.lisp:530–555` generates the guard, extra premises and success test under witness substitution. That establishes an inhabited boundary condition, not necessarily a trace from initialization through the composed host machine. `books/defkeystone.lisp:31–44` similarly checks antecedent and conclusion under guards. Add a named initialization/producer trace and the connection/holder/dispatch invariant for a reachable witness; label arbitrary valid-state and corrupted-state tests separately. Cost worst-case witnesses also need the live-history dimensions described in §1–2.

**HOLE: source/test/image event ordering is not settled.** The sketch says generate the raw-with interface first, then preservation and row completion (`SKETCH.md:38–43`), while `definterface` immediately checks the world and carried row (`books/definterface.lisp:540–580,651–668`). A new transition cannot already have the generated theorem/complete row it will emit later. The final completeness check needs all interfaces (`books/def-carried.lisp:1072–1082`: “in the image world … completeness check bites”). The sibling deliberately puts teeth in a later test/image world (`generators-2.md:43–46`). Define a staged dependency graph:

1. Admit body, execution representation/guards, primitive/callee summaries and exact stronger writer lemmas.
2. Accumulate declarations as data, then generate the carried/holder/command obligations with stable names; consume holder cuts only after their row exists.
3. Install interfaces/raw annotations only when the required theorems/rows exist, and run final-world completeness and dispatch validation after all declarations. If a non-raw preliminary interface phase is needed, make its finalization explicit and refuse unfinished rows.
4. Build teeth in test worlds from the same theorem statements and owed records. Produce a content-addressed satisfaction manifest; validate coverage of the final production closure. Do not require production runtime to load test macros merely to know its obligations were certified.
5. Emit registries and cost hooks only from that finalized declaration/statement set; reject duplicate owners, stale rows and missing class/route/teeth/effect/cost records. Bind certification, benchmark and qualified-image coordinates separately.

There is a related missing shape: the form requires `:carries ROW` (`SKETCH.md:20`), yet a pure entry need not return any state. Existing `fn-cd-parts` refuses a function that “does not return the carried stobj” (`books/def-carried.lisp:485–488`), and raw eligibility refuses value-state rows (`:1270–1272`). Add explicit pure/read-only/transition/open cases and their different obligations. A value `def-carried-view` is not automatically a raw-dispatch row. Otherwise “one declaration per host-called entry” stalls well before program migration.

**WEAK: preserve existing interface capabilities.** The current accepted keyword set includes `:delegates`, `:raw-with`, and `:raw-guarded` (`books/definterface.lisp:99–100`); the new optional keyword list at `SKETCH.md:19` does not expose all of them. Preserve the exact delegation check—body equal to callee on formals, `books/definterface.lisp:323–337`—and fixed callback ABI metadata rather than silently dropping them. One final authoritative row per entry is sound; during migration forbid divergent definterface/def-entry duplicates and compare emitted fields before replacement. Enumerate declarations even when cost is unaccounted, but do not turn census completeness into a whole-dispatch cost claim.

**WEAK: proof cost can erase the macro's benefit.** The existing generator already records a concrete hazard: `books/def-carried.lisp:1013–1015`, “a :use of every arm at once is a 4^n clausification”; `:1025–1034` uses a small functional instantiation to avoid reopening transition bodies. Keep generic cost/loop lemmas and bounded per-entry proof theories, cache effect/cost closures, and require net reduction in total and critical-path certification cost. The existing tooling distinguishes prover-step regressions, scoped wall time and failed certification (`tools/proof_cost.py:11–37`: “Prover steps are the ratchet”; “A failed certification measures no cost”). Add generated obligation counts and per-family proof cost to review evidence; do not infer faster proof from fewer handwritten lines.

**SOUND direction, conditional completion criteria.** Ordinary generated events, world-derived carried statements, one cut owner and owed-teeth records are useful foundations (`SKETCH.md:11–12`: “Macros expand to ordinary events”; `books/def-carried.lisp:558–563`: exact generated-statement comparison). Build the small writer generator after §7's contract decisions. Build a cost claim only for a closed execution subset whose derivation, guard route, primitive costs, effects, principal accounting and command composition are actually covered. Keep everything else visibly unaccounted until migrated. That reaches the intended whole system without passing off a declaration inventory or finite benchmark as a resource bound.

Consultation actions: read-only source/history inspection and small stdlib counting; wrote only this ANSWER.md. No implementation, tracked-file edits, commits, ACL2, builds, make, ssh or box commands. Open evidentiary limits: original r67 report text, later-lane PRF associations, and any runtime/proof result not present at the stated source coordinates are UNVERIFIED here.
