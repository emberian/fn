# peer-carriage: the opaque-carriage budget and the refusal classes (PRF-099)

Dev lane `lane/peer-carriage` from `534a68d3`, theorems 4 and 5 of the
peering spike record (`spike/mega:planning/evidence/spike-peering-2026-09-25.md`),
re-implemented in `:logic` mode with verified guards; no `;; SPIKE` marks,
no host sidecar. Requirement NNT-015, scenario SCN-054.

## What changed in behaviour

- **A carrying boundary with no budget carries nothing.** Under D23 as first
  implemented, a principal on a boundary's `carries-principal` list was
  carried without bound. Now the carried arm's event is built only within
  the boundary's budget, and without budget rows it is refused
  `carried-budget-unset`. Operators must add `peer budget NAME OCTETS COUNT`
  to every carrying boundary. Under D27 the budget belongs to the operator;
  it is not a constant.
- **NNTP transit refusals of a present carrier are named by class.** The
  transit log `detail=` was the plan reason (`local-enrollment`,
  `carrier`, `signature`, ...). It is now one of `no-local-binding`,
  `unsupported-profile`, `signature-failed` or `malformed`. The served POST
  keeps its own words, and BP transit keeps the plan reason.
- **`peer carries NAME HEX ...` and `peer budget NAME OCTETS COUNT`** are new
  operator verbs. They extend an existing boundary over the live table, so a
  carried list grows across requests. The admin argv bound stays 16. It is a
  per-request work bound; the spike raised it to 32.

## Definitions (books)

- `books/peer-carriage-rows.lisp`: the budget as two typed rows,
  `(NAME "carried-budget-charge" "" CHARGE)` and
  `(NAME "carried-budget-count" "" COUNT)`. The naturals sit in the rows'
  uint32 slot, the width of the Store's own charge capacity. CHARGE is in
  Store charge units (4096-octet pages), floor(OCTETS/4096), so an octet
  budget over 4 GiB is expressible (tested: 8 GiB is accepted; 2^44 octets
  is refused as past a uint32 of pages). The file also defines
  `fn-pcb-peer-budget` and the extension `fn-pcb-extend-rows` /
  `fn-pcb-extend-delta`.
- `books/peer-carriage.lisp`:
  - `fn-pcb-event-carriage` is a committed event's `(EVIDENCE . CHARGE)`
    when it is a carried kind-4 composite.
  - `fn-pcb-usage` is the projection over committed records.
  - `fn-pcb-tally-records` / `fn-pcb-usage-extend` are the owner's
    `(K . TALLY)` cache, extended by the records committed since K.
  - `fn-pcb-admission`, `fn-pcb-carried-event` (the gated constructor),
    `fn-pcb-admitted-from` (the trace predicate) and
    `fn-pcb-refusal-class`.
- `books/native-admin-peer.lisp` (`fn-native-admin-peer-extend-plan`) and
  `books/native-admin.lisp` (`fn-native-admin-plan-deltas-over`) define the
  two verbs.

## Host lines that call the subjects

- `host/native/owner.lisp:907` `fnn-owner-attempt-transit` calls
  `fn-owner-peer-carried-relay-event`.
  - `host/owner-host.lisp:1496` defines it. It calls `fn-pcb-carried-event`
    over the budget global and the usage from `fn-owner-carried-usage`
    (`:1480`, which calls `fn-pcb-usage-extend` and keeps the cache).
  - A `(:refused NAME)` answer is relayed as the transit refusal.
  - The budget global is written in `fn-owner-transit-decide` beside the
    carried list, from the same peer and configuration.
  - The cache is reset at open (`fn-owner-install-profile`, `:246`).
- `host/native/owner.lisp:831` `fnn-owner-transit-class` calls
  `fn-owner-transit-refusal-class` (`host/owner-host.lisp:1526`), which calls
  `fn-pcb-refusal-class`. It is used at the carrier-form refusal (`:873`),
  the plan refusal (`:931`) and the primitive failure (`:956`), on NNTP
  transit.
- `host/native-admin-host.lisp:37` (live owner) and `:51` (offline) call
  `fn-native-admin-plan-deltas-over`.

## Theorems (all in books/peer-carriage.lisp unless noted)

- **Usage is the projection.** `fn-pcb-carried-usage-is-the-projection`:
  `(fn-pcb-cache-validp cache records)` implies
  `(fn-pcb-tally-get ev (fn-pcb-usage-extend cache records)) = (fn-pcb-usage records ev)`.
  `fn-pcb-extended-cache-is-valid` shows the cache the owner stores is valid.
  `fn-pcb-cache-valid-after-commit` shows it stays valid as records are
  appended.
- **Trace bound (theorem 4).** `fn-pcb-carried-history-within-budget`:
  `(fn-pcb-budgetp budget)` and
  `(fn-pcb-admitted-from records (0 . 0) budget ev)` imply that the carried
  charge sum is at most `(car budget)` and the count at most
  `(cadr budget)`.
  - `fn-pcb-carried-event-keeps-history-admitted` covers the host step:
    given the projection as usage, appending whatever the constructor
    returns keeps the history admitted.
  - `fn-pcb-other-record-keeps-history-admitted` covers any other record.
  - `fn-pcb-no-budget-history-carries-nothing` covers the no-budget case.
- **Each exhaustion by name.** `fn-pcb-admission-without-a-budget-admits-nothing`,
  `fn-pcb-admission-names-count-exhaustion` and
  `fn-pcb-admission-names-octet-exhaustion`.
- **Admission of the operator's rows.** `fn-pcb-budget-after-extension` and
  `fn-pcb-peer-budget-after-extend-delta` (books/peer-carriage-rows.lisp):
  after the extension delta applies to a configuration value that has the
  peer, the budget reads exactly `(CHARGE COUNT)`.
- **Classes (theorem 5).** `fn-pcb-present-carrier-not-accepted-has-a-class`:
  a present carrier (carrier kind not `:absent`) that is neither carried nor
  `:ok` under both `:verified` observations has a class among the four.
  - `fn-pcb-bound-carrier-with-a-failed-primitive-is-signature-failed`,
    `fn-pcb-refused-carrier-is-never-signature-failed` and
    `fn-pcb-absent-carrier-has-no-class` complete the picture.
  - The class is a pure function of the received octets, the snapshots,
    the boundary's list and the two observations.

## Teeth (tests/acl2/peer-carriage-tests.lisp; admin in tests/acl2/native-admin-tests.lisp)

Each keystone has a reachable witness over the D23 fixtures:
- `*pat-carried-event*`, an enrolled composite and a forged composite;
- a two-step history gated through `fn-pcb-carried-event`;
- one witness per class, including an unsupported-profile carrier whose
  items name suite 2.

The `must-fail` cases, one per hypothesis:
- the cache is stale (it skips the carried record it claims to cover);
- the history is not admitted (the carried record appears twice under a
  one-article budget);
- the budget is not a budget (`(-1 -1)`);
- the usage passed in is a stale zero instead of the projection (a second
  event is then built and the history is no longer admitted);
- the peer does not exist (no delta);
- the budget value is not a natural;
- the carrier is absent, carried, or accepted under both observations (no
  class);
- a failed observation on an unbound carrier (no-local-binding, not
  signature-failed).

## Finding

The spike's unsupported-profile class could not be reached.
`fn-hc-received-plan` reports a carrier whose items decode but name another
profile as `:carrier`, not `:profile`, so the spike's test of `(cadr parsed)`
was never true. The dev class reads the field's own decode
(`fn-pcb-unsupported-profilep`). The spike's budget also compared a page
charge with an "octets" budget; dev states the budget in charge pages.

## Certification and native runs

| run | box | what | result |
| --- | --- | --- | --- |
| `run-20260925T102736Z-e097` at `4a612f9f` | persvati, w25, 2 jobs, 300 s | `--affected-by` peer-carriage-rows, peer-carriage, native-admin-peer: 13 certified, 158 installed | passed; manifest `planning/evidence/manifests/certify-20260925T102823Z-3910071.json`; slowest books/native-admin 9.4 s, books/peer-carriage 3.4 s, tests 2.3 s |
| `run-20260925T103417Z-576c` at `8c38c762` | hbox, w28, 2 jobs | same roots: 20 certified | passed; `certify-20260925T103454Z-3166493.json` |
| `run-20260925T103728Z-cc22` at `8c38c762` | hbox, w28, 2 jobs | the 140 default image roots (not `--closure`): 49 certified, 286 installed | passed; `certify-20260925T103759Z-3173050.json` |

Native, hbox, tree `git archive 8c38c762` in
`/tank/fn/scratch/peer-carriage/tree`, production image built with
`proof_artifacts acquire/validate --profile default` (artifact set
`b8c507b7…`, 335 books, rejected 0) and `tools/build_native_host.sh` under
`swarm-build`, OpenSSL 3.5.8. `build/fn-host` sha256
`868abf22f2fceed03e941f795733056d53342ddb3661ccc99c3568aafd788cd6`, core
`fa64003beb21b5730939c6d50cbea6ff7694a3ee316375794cdf68621e88f583`, build log
`d6f6187c5364eeab646fbbdf49ae919c8f073f26c749700741bce3acc5388b14`.

`python3 -m unittest` of five cases of tests/test_native_hybrid_author.py
under `systemd-run --user --scope -p MemoryMax=24G` with
`FN_RUN_HYBRID_E2E=1`: 5 of 5 ok in 15.5 s, log `build/native/tests2.log`
sha256 `12f02fc45af3ff8e7842ffaa59d204b5f351d9391eeec478d91dabf9b800df9e`.

- `test_carried_budget_and_refusal_classes`:
  - The carried list arrives by `peer carries` and the budget by
    `peer budget author 1048576 1`.
  - The first signed article is carried (`HDR :fn-verified` = `carried HEX`).
    The second is refused `detail=carried-count-exhausted`.
  - An IHAVE from the author's address with the carrier's suite item set to
    2 draws 437 with `detail=unsupported-profile`. This is the row the spike
    lacked.
  - One with a principal byte flipped draws 437 with
    `detail=no-local-binding`.
- `test_carrying_boundary_without_budget_carries_nothing`: a listed
  principal with no budget is refused with `detail=carried-budget-unset`
  and is not stored.
- The three existing D23/D02 transit cases pass with the budget added and
  the class as the detail (`no-local-binding`).

There is no signature-failed row natively. The ACL2 witness covers it; a
native row needs a relay that enrolled the author and a tampered transit
body.

## Not done, and why

- **The durable `:unverified` verdict for held articles.** On dev, no
  present-carrier article that is refused is ever stored. The four classes
  arise only on refusal, and the carried arm records `:carried`. Recording a
  class durably would need either a policy to hold refused signed articles
  (a D02/D23 decision, not in this brief) or a new kind-4 composite and its
  replay branch. So the class is the transit refusal's log detail, and
  `fn-stx-reason-token` is unchanged. Adding reason tokens with no caller
  would be an unreachable branch.
- The trace theorem fixes one budget. An operator who lowers a budget gets
  refusals from then on, but the theorem is not restated over a budget
  sequence.
- BP transit keeps the plan reason as its detail (the carried arm is NNTP
  only).
- `peer list` does not render the budget.
