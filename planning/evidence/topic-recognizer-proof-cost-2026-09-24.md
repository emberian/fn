# Topic event recognizer proof cost, 2026-09-24

This is a proof-cost repair with unchanged definitions and theorem
statements. Topic events joined `fn-store-event-p`, the Store event
accessors and the replay/Store dispatchers (`15f4fb19`, `702d6ef1`, carried
into `books/store-events` and `books/replay`), but
`books/topic-history-store-events` left `fn-th-topic-eventp` enabled, where
`books/consumer-store-events` withdraws its sibling `fn-cpe-eventp`. Every
proof that only dispatches on an event kind then unfolded the topic
anchor/admission shape (`fn-th-local-admin-eventp`, `fn-th-auth-ref-p`,
`fn-th-source-id-p`, `fn-th-at`, `fn-th-exact-octets-p`) into its case
split. The ledger's include-hygiene check had already flagged the missing
withdrawal for `books/store-events`.

In the before run the slowest event of each regressed book had
`(:DEFINITION FN-TH-TOPIC-EVENTP)` among its rules. Examples: the unchanged
`fn-replay-apply-record-non-nil-is-node-state` took 51.5 s and 27.2 million
steps (0.32 s when the replay comment was written);
`fn-sn-finish-identity-arm-keeps-the-store-and-index` took 28.6 s;
`fn-sis-finish-enabled-files` took 19.5 s; and
`fn-csi-finish-advances-projection-by-definition` took 19.0 s.

`books/topic-history-store-events` now exports the forward-chaining
`fn-th-topic-event-shape-by-definition`, which gives a true list and
natural counters 1 to 3, and then disables `(:d fn-th-topic-eventp)`. Four
proofs that read the definition enable it by name: three in
`books/topic-history-identity-disjoint` and `fn-replay-record-is-a-true-list`.
Two proofs that split on the stx recognizers keep them closed in their hints.
They are the guard of `fn-sn-completion-core-enabledp`, 20.6 s before and
0.02 s in the REPL, and `fn-ceis-prepare-identity-preserves-related`,
45.5 s before and 0.07 s in the REPL.

All runs used persvati, ACL2 8.7 with toolchain
`/home/ember/fn-gates/toolchains/w25/acl2-literal` (identity
`1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`), two
jobs, a 300 s per-book cap, and gate `/home/ember/fn-gates/proof-cost-46f2660d`.

| Book | Before (s) | After (s) |
| --- | ---: | ---: |
| `books/store-node-invariants` | 85.00 | 17.59 |
| `books/consumer-event-index-store-invariants` | 74.53 | 28.06 |
| `books/replay` | 58.11 | 2.52 |
| `books/store-node-traces` | 50.49 | 20.25 |
| `books/topic-history-store-invariants` | 48.32 | 13.04 |
| `books/store-identity-sequence-invariants` | 46.64 | 2.97 |
| `books/consumer-store-invariants` | 41.98 | 8.33 |
| `books/store-node` | 23.16 | 2.57 |

The before run was `run-20260924T084451Z-58c8` at `46f2660d`
([manifest](manifests/certify-20260924T084459Z-2414753.json)). The after run
was `run-20260924T090348Z-92f1` at `ad0bbfb5`
([manifest](manifests/certify-20260924T090352Z-2580961.json)). The
dependent run `run-20260924T090548Z-876b`
([manifest](manifests/certify-20260924T090604Z-2599989.json)) certified
every Makefile root that includes `books/topic-history-store-events`: 332
books certified and 329 passed. The three failures are the known reds from
the wind-down handoff. `books/bp-node-progress-guards` hit the 300 s cap in
`VERIFY-GUARDS FN-BPNP-ISSUED-DEBT-DELTA`, the known missing premise.
`books/bp-node-progress-selection-invariants` failed at
`fn-bpnp-step-progress-preserves-held-and-issued`.
`tests/acl2/bp-node-machine-teeth-tests` could not load its uncertified
include. The first two logs do not mention `FN-TH-TOPIC`.

These runs certify books and tests at these bytes. They do not certify an
integrated image or qualify the runtime.
`books/consumer-event-index-store-invariants` is still over 10 s, because
`fn-ceis-finish-keeps-index` (14.2 s) and `fn-ceis-finish-keeps-records`
(11.1 s) split on `fn-sn-finish` and `fn-sn-finish-identity`, not on the
recognizers. `books/store-node-traces` (20.3 s), `books/store-node-invariants`
(17.6 s) and `books/topic-history-store-invariants` (13.0 s) also stay above
10 s.
