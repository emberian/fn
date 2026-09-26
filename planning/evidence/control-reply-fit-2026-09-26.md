# control-reply-fit (2026-09-26)

Lane control-reply-fit, branch `lane/control-reply-fit` from dev 12f447e8.
Brief: build/coordinator/queue/done/w4-control-reply-fit.txt. Ids: PRF-178,
SCN-107, PKT-470, PKT-471. PKT-467 retired; PKT-466 (a) narrowed.

## What now works

- A store profile whose record bound R the consumer poll reply cannot carry
  is refused by name, `max-record-octets-above-the-poll-reply`, at `init` and
  at `store upgrade-profile` (exit 1, nothing written), instead of being
  admitted and discovered at the first oversized article. At the ceiling
  (R = 4,294,966,940) the profile is written and served.
- The live-status reply (FNLS, `status`, `pins`, `peers`, `obligations`,
  `control`, `health`) refuses a report its u32 total cannot say by name,
  `:report-past-the-total-width`, and the operator prints
  `live status refused: report-past-the-total-width`, exit 1. Before, the
  refusal was bare.
- The sweep (below) found no control reply whose encoder can be handed a
  value past its ceiling on the FNCT path under a valid profile.

## 1. PKT-467: the validator arm (the coordinator's ruling)

The ruling: "D27's own rule ('profile validation, representation and format
evolution must agree') means profile validation must refuse a record bound
the consumer poll reply cannot carry ... that is the rule applied, not a new
cap: take consumer-exchange's default with a theorem that every admitted
record fits a poll reply under a valid profile, the refusal NAMED in the
profile validator; no wire change."

The inequality, from the encoder. `fn-ncl-poll-reply-encode` (books/consumer-
local-control.lisp) accepts a report only when `fn-ncl-poll-event-bytesp`
holds, `(<= (len report) *fn-stxa-max-octets*)`; the payload is
`1 + 4 + len(cursor) + 4 + len(report)` with `len(cursor) <= 346`, so
`*fn-ncl-poll-max-payload* = 9 + 346 + *fn-stxa-max-octets*` and
`*fn-stxa-max-octets* = *fn-cbor-max-uint* - 355 = 4,294,966,940`. The arm,
`books/byte-store-frame.lisp` `fn-bs-profile-invalid-reason`, right after
`:max-record-octets-above-codec`:

    ((< *fn-stxa-max-octets* r) :max-record-octets-above-the-poll-reply)

One reason arm, as announced in the LANEDUMP before the first edit; no field,
constant or wire changes. `*fn-stxa-max-octets*` was already in the book's
include closure (stx-accept-records).

Theorems (PRF-178):

- `fn-bs-profile-valid-record-fits-a-poll-reply` (byte-store-frame): for any
  value, `fn-bs-profile-max-record-octets` is at most `*fn-stxa-max-octets*`;
  and every payload `fn-bs-publication-admissiblep` admits is within it. Host
  lines: `fn-store-publication-admissibility` (host/store-host.lisp) for
  `fnn-publish` (host/native/io.lisp); `init` through
  `fn-store-profile-init-verdict`; `store upgrade-profile` through
  `fnn-command-upgrade-profile` -> `fn-hmr-upgrade-verdict` ->
  `fn-profile-upgrade-verdict` -> `fn-bs-profile-resolve`, whose `:invalid`
  reason the verb prints (`store profile upgrade refused: ~a`).
- `fn-col-poll-report-of-an-admitted-payload-fits`
  (consumer-owner-local-progress): a page whose event encoding is a payload
  the publication gate admits under any profile is served by
  `fn-col-poll-report` (host/owner-host.lisp `fn-owner-consumer-local-poll`)
  as that page, never `:oversize`.
- `fn-bs-profile-v1-valid-stays-valid` (byte-store-profile-v1) gains the
  hypothesis `R <= *fn-stxa-max-octets*`, and
  `fn-bs-profile-v1-valid-above-the-poll-reply-is-refused-by-name` says the
  excluded window fails the new relation by exactly the new name. This is the
  saved-profile keystone the arm necessarily narrows; the two theorems
  together say which profiles the image before this arm admitted still open.
  The presets, the defaults and both format-7 translations are far below the
  ceiling (R 17,138,486 and 67,108,864), witnessed in the test books.

The `:oversize` arm of `fn-col-poll-report` is NOT marked
unreachable-in-composition: it is reachable for a served event whose
encoding exceeds its own store's R. The open refuses a transaction file
above R plus the frame overhead (`fn-store-profile-read-bound`), but that the
served event re-encodes to its file's octets is not stated as a theorem
(PKT-470 (1)). It stays as the named refusal for that corrupted state.

Consequence (PKT-471, a decision): a store saved with R in the window
before this arm no longer opens, and the open's refusal is the host's
generic `ACL2 rejected durable configuration frame` fault (exit 4), not the
name; `store upgrade-profile` cannot lower R. No such store is known.

Teeth:
- tests/acl2/byte-store-frame-tests.lisp: `*fn-stxa-max-octets*` is
  4,294,966,940; R one octet past it and R at the codec's u32 are each refused
  by the new name (`bsft-refuses`); R at the ceiling is valid. Keystone:
  reachable and tight (the profile at the ceiling admits a payload of exactly
  the ceiling); the presets, the defaults and both format-7 tuples witnessed;
  the hypothesis dropped (`must-fail` at a payload one past the ceiling), and
  the gate refuses that payload even under a profile asking for R one past
  the ceiling.
- tests/acl2/byte-store-profile-v1-tests.lisp: a profile the old relation
  admits with R one past the ceiling is refused by the new name, not
  admitted (`must-fail` of the conclusion without the new hypothesis); at the
  ceiling the old relation's profile stays admitted.
- tests/acl2/consumer-owner-local-progress-tests.lisp: the reachable page's
  encoding is admitted by the development profile's gate and the report is
  the page (the full antecedent); the page hypothesis dropped fails on the
  scope refusal (`must-fail`); the admission hypothesis dropped is proved to
  fail for every page past the ceiling (`colp-admitted-payload-fits-needs-the-admission`:
  such a page is the `:oversize` refusal, not the page) and to be what
  excludes it (`colp-past-the-ceiling-is-not-admitted`); no 2^32-octet
  report is constructible concretely.

## 2. The sweep: every control-socket reply

Survey of each reply's encoder, ceiling, what the host can hand it under a
valid profile, and what an encoder refusal does. What `:bad` does on the
FNCT path today: `fnn-control-reply-octets` (host/native/control.lisp) calls
`fnn-fault` ("ACL2 refused a local-control reply status") inside
`fnn-control-send-reply`, whose own `(error () nil)` swallows it: no bytes
are sent, the socket closes, the owner lives, and the client's decoder turns
the missing reply into `:after-submission`, uncertain, exit 3. Not a crash;
a lost word. No reachable row produces it today.

| # | reply | encoder | ceiling | largest value under a valid profile | outcome today |
| --- | --- | --- | --- | --- | --- |
| 1 | FNCT kind 2 status reply (answers kinds 1 submit and 3 admin) | `fn-native-control-reply-encode` (native-control) | one enum word | a status in `*fn-nctrl-statuses*`; submit results checked against `*fn-nctrl-owner-control-results*` | fits by construction |
| 2 | hybrid kinds 4-8 (enroll, author, revoke, enroll-next, revoke-next) | kind 2's | as 1 | a status word; the author reply carries no payload (`fn-nhc-author-refusal-is-a-named-refusal`) | fits by construction |
| 3 | peer-invite kinds 9-11 | kind 2's | as 1 | a status word; the invitation octets are in the request, never the reply | fits by construction |
| 4 | keys redecide kind 12 | kind 2's | as 1 | `:accepted` / `:refused` | fits by construction |
| 5 | topic-history reply | `fn-thlc-reply-encode` | 1 octet | a status code | fits by construction |
| 6 | consumer kind 5 reply | `fn-ncl-reply-encode` | 513 | a cursor from `fn-cp-cursor-encode`, at most 346 | fits by construction (no named theorem: PKT-470 (3)) |
| 7 | consumer kind 9 status reply | `fn-ncl-status-reply-encode` | 13 | ack, frontier, gap; the frontier u32 by `fn-cp-statep` | fits by invariant (`fn-ncl-status-accepted-reply-roundtrip`; the served-state link unnamed: PKT-470 (3)) |
| 8 | consumer kind 6 poll reply | `fn-ncl-poll-reply-encode` via `fn-col-poll-report` | `*fn-stxa-max-octets*` report | before: R in the 355-octet window; now: at most the ceiling | refused by name (`:oversize`, PRF-177) and now fits by theorem under a valid profile (PRF-178) |
| 9 | FNLS page (live status codes 1-6) | `fn-nls-page` over `fn-nls-buffer` (native-live-status) | 131,136 per page (paged); the report total u32 | grows with retained state: grant rows, peers, pins, obligations, up to the profile counts (2^32-1) | before: bare `:refused` past the u32 total, after a whole render; now: refused by name (`:report-past-the-total-width`), render still whole (PKT-470 (2)) |
| 10 | `peer list` / `control list` | live: FNLS codes 3 and 5 (row 9); offline: stdout, no codec | as 9 | as 9 | as 9 |

Counts: fits by construction or theorem 8 (rows 1-8), refused by name 1 at
the start (row 8) and 2 now (rows 8, 9 and its alias 10), `:bad` turned into
a fault reachable 0, unbounded 1 class (rows 9-10: the render, not the
reply). `tools/fn_client.py` is an NNTP client and decodes no control frame.

### Row 9 repaired: the named width refusal

In fn-col-poll-report's shape, ACL2 decides and the host carries the word:

- `books/native-live-status.lisp`: `fn-nls-reply` and `fn-nls-page` answer,
  for an octet report (buffer string) longer than 2^32-1, the refused reply
  whose chunk is `*fn-nls-refusal-past-the-total-width*` (the octets of
  `report-past-the-total-width`); every other refusal keeps its empty chunk.
  No layout change: status 2, total 0, no digest and a byte-string chunk are
  what every refused reply already framed, and a client before this reads
  `:refused`. `fn-nls-client-step` reads the word back as
  `(:refused :report-past-the-total-width)`.
- `host/native/control.lisp` `fnn-control-live-status` returns the named
  step as it came (a bare refusal stays `:refused`);
  `host/native/operator.lisp` `fnn-operator-status-once` and
  `fnn-operator-health-report` refuse with `live status refused: WORD`
  (`fnn-refuse`, a refusal, exit 1).

Keystone `fn-nls-page-refuses-exactly-past-the-total-width`: for an octet
report and any offset, the client's step on the owner's buffered page is the
named refusal exactly when the report is longer than 2^32-1 octets (the
exact-bound shape). The offset hypotheses of a first draft were redundant
(the width refusal does not read the offset; within the width a bad offset is
the unnamed refusal) and the theorem was proved without them. Teeth
(tests/acl2/native-live-status-tests.lisp): the exact refused frame the
owner sends past the width decodes to the named refusal; the pre-existing
unnamed refusal does not; the full antecedent within the width on the status
report of a real owner state is not the named refusal; an offset past the
report is the unnamed refusal; the one hypothesis dropped is proved to fail
for every non-octet report past the width (`nlst-width-refusal-needs-octets`).
The past-the-width antecedent is not witnessed concretely (2^32 octets).

What it does not fix (PKT-470 (2), told to hot-path-checker through the
LANEDUMP): the owner renders the whole report as octet lists and one string
under its mutex before this decision, so a report near 4 GiB exhausts the
heap before the refusal is reached. The repair is to bound the render per
request or stream rows per page from an index.

## Assurance chain

- PKT-467: native entry `fnn-command-upgrade-profile` / init
  (`fnn-command-init`) -> executed ACL2 subject `fn-bs-profile-resolve` ->
  `fn-bs-profile-invalid-reason` (the arm) -> maintained relation: the
  store's profile is admitted at every open (`fnn-metadata-config-decode`)
  and every published payload is within its R (`fnn-publish`'s gate) ->
  behavioural theorems `fn-bs-profile-valid-record-fits-a-poll-reply`,
  `fn-col-poll-report-of-an-admitted-payload-fits` -> observed: SCN-107.
  init establishes the relation; upgrade preserves it (it writes only a
  valid profile, `fn-profile-upgrade-verdict-writes-only-upgrades`).
- FNLS: native entry `fnn-control-live-status-answer` -> `fn-nls-page` over
  `fn-nls-buffer` -> `fn-nls-page-of-buffer-is-reply` (the refinement to the
  octet-list page) -> `fn-nls-client-step` in `fnn-control-live-status` ->
  `fn-nls-page-refuses-exactly-past-the-total-width` -> observed: not driven
  natively (2^32 octets); the host carriage is checked statically.

## Certification (persvati, 2 jobs, 300 s)

- r1 `run-20260926T121551Z-b559`, manifest
  `certify-20260926T121554Z-1588164`: passed, 4 certified (byte-store-frame
  2.08 s, byte-store-profile-v1 0.97 s, their tests 1.02 s and 0.97 s).
- r2 `run-20260926T121846Z-eb0b` (`--affected-by` byte-store-frame,
  consumer-local-control, native-control, native-live-status: 279 to
  certify, the seam's whole closure), manifest
  `certify-20260926T121934Z-1622002`: 273 passed, 6 failed. Causes, both
  this lane's: `fn-nls-page-refuses-exactly-past-the-total-width` (a case
  split that left the width unknown in the offset case; 4 books failed by
  including it) and a combined teeth theorem in
  consumer-owner-local-progress-tests that ran past 300 s. Slowest passing
  books: native-admin 9.38 s, native-operator 8.83 s (untouched here),
  byte-store-k0-step-bridge 7.28 s.
- Both fixed in the REPL on persvati (the keystone 0.15 s; the teeth split
  into two theorems, each 0.0 s), then r3 `run-20260926T123517Z-a911`
  (`--affected-by` native-live-status, consumer-owner-local,
  byte-store-profile-v1), manifest `certify-20260926T123544Z-1783646`:
  passed, 13 certified, none over 10 s (native-live-status 4.23 s,
  consumer-owner-local-progress 3.78 s, its tests 1.47 s, native-live-status
  tests 2.22 s). r2's passes and r3 together cover every book the lane's
  changes reach.

## Native (hbox, developer image)

- r2 (632c228f; `tools/hbox_native.sh --label r2 --env
  FN_NATIVE_HOST=$T/build/fn-host-developer`),
  `/tank/fn/scratch/control-reply-fit/native-r2`, status 0; developer image
  `e0f65bb4...`, core `faed8bd5...`.
  `tests.test_native_control_reply_fit` 3 OK (log `168c07eb...`, committed
  as planning/evidence/control-reply-fit/test_native_control_reply_fit.r2-632c228f.log):
  `init` one octet past the ceiling: `refused operator init
  MAX-RECORD-OCTETS-ABOVE-THE-POLL-REPLY`, exit 1, no config.json; at the
  ceiling written and the owner takes a POST (240). `store upgrade-profile`
  one octet past: `store profile upgrade refused:
  max-record-octets-above-the-poll-reply`, exit 1, config.json
  byte-identical, the owner serves after it; the upgrade to the ceiling
  exits 0, status reads R 4,294,966,940, the owner serves.
  `NativeOperatorInitTests` OK (`9441fa86...`), `NativeOperatorCapacityTests`
  OK (`04b9e322...`).
- r1 (976ffd83) is not evidence: its first pass ran every module against the
  production image path the lane had not built (all skipped); the rerun on
  the developer image showed both refusals by name on the wire, but two
  assertions of this module were harness defects (the init reason is
  printed upper-cased; a helper was missing), fixed in 632c228f; and
  `tests.test_native_control` pointed at the developer image through
  FN_NATIVE_HOST exercises its production-selector cases against the wrong
  image (errors of the invocation, not the host); the lane stopped that run.
- The FNLS width refusal is not driven natively (a 2^32-octet report);
  its host carriage is checked statically by the module's source test.

## Not done

- PKT-399 (a sweep row the deputy added mid-lane, from keys-and-accounts-3's
  trace): the XREDEEM admission's used count `(len creds)` and TAKENP are
  computed on the HOST in host/native-admin-host.lisp
  `fn-acct-host-owner-redeem-stage` (friends-accounts-2), while
  `fn-acct-redeem-bounded-plan-refuses-exactly-past-the-operator-bound`
  states the bound over what the host hands it. The repair: the count moves
  into the redeem plan (`fn-auth-account-creds` over the live table plus
  the credential file's table, the profile's max-credentials the bound),
  the exact-bound theorem restated over the ACL2-computed count with a
  must-fail, binding rows (mark 2) not counted, the host passing tables not
  numbers. NOT done here: that code is not on this lane's base (dev
  12f447e8 has no `fn-acct-host-owner-redeem-stage`), and the lane was at
  its farm budget; PKT-399 stays open with this trace.

- PKT-470: (1) the `:oversize` arm's reachability through a store whose
  event exceeds its own R; (2) the whole-report render before the FNLS
  width decision (hot-path-checker's class); (3) no named fits theorem over
  the served state for the consumer kind-5 and kind-9 replies; (4) the FNCT
  reply-encoder fault is swallowed, not logged (unreachable today); (5) the
  FNLS width refusal is not driven natively.
- PKT-471 (ember): a store saved with R in the window faults at open and
  cannot be lowered.
