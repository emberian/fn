# Ten-second books, 2026-09-24

Nine of the twelve books in `planning/proof-cost-baseline.json` now measure
under ten seconds at two jobs on persvati. The fixes are proof work: one book
split and hint repairs. No theorem statement changed, and no moved event was
renamed. Each expensive event was found with the proof REPL on persvati:
per-event `Time` from a loaded session and
`(show-accumulated-persistence :frames)`.

Both runs used persvati, ACL2 8.7, toolchain
`/home/ember/fn-gates/toolchains/w25/acl2-literal` (identity
`1b4169e9…a286`), two jobs, a 300 s per-book cap, the cache
`/home/ember/fn-certcache`, and no `--closure`.

- `run-20260924T213346Z-8966` ([manifest](manifests/certify-20260924T213414Z-815439.json)):
  the twelve changed roots, source `514d3132`. 56 certified, 0 failed.
- `run-20260924T213635Z-0a7d` ([manifest](manifests/certify-20260924T213702Z-842604.json)):
  every Makefile root affected by a changed book (188 roots), source
  `09048883`. 164 certified, 0 failed.

`green_check --changed-since 00d291d0 --summary`: 11 changed books, 178
books include one, and none is not green at the bytes a merge would carry.

| Book | Before (s, run) | Expensive event and fix | After (s) |
| --- | ---: | --- | ---: |
| `byte-store-record-provenance` | 13.0 persvati `183858Z`; 18.9 hbox 4 jobs | No single event: 250 events and four heavy includes. The book is split into `-bytes` (6.08), `-node` (4.52) and `-owner` (7.38). The original includes all three. The 30 local proof steps that a later part uses (read from the certify log's Rules and Hint-events) are exported. 19 of them are disabled at the end of their part and enabled locally downstream. The other 11 are `:rule-classes nil` | 4.02 |
| `consumer-store-invariants` | 8.49 persvati; 17.3 hbox | `fn-csi-prepare-topic-…` (2.2 s) and `fn-csi-prepare-identity-…` (0.75 s) tried `fn-csi-live-ready-exact-replay` and `fn-csi-ready-full-replay` about 2,500 times. Both rules are now withdrawn in these hints | 8.03 |
| `byte-store-scan` | 7.50 persvati; 16.1 hbox | `fn-bs-crash-select-names-are-an-outcome` opened `fn-bs-tear-write` before the existing names-after lemmas applied. It is now kept closed (1.4 s → 0.1 s) | 6.56 |
| `bp-node-fragment-family` | 5.46 persvati; 12.3 hbox | The fragment query theorem and its receive-preservation theorem opened the active set and the fragment recognizers. They now open only the query and use the held-list lemma (2.8 s and 1.6 s → 0.0 s) | 1.68 |
| `nntp-auth-invariants` | 8.53 persvati; 11.5 hbox | The refused-POST dispatch theorem and `fn-auth-effects-carry-no-submission` backchained through `fn-auth-nntp-effects-are-auth-effects` into `fn-nntp-article-idp-is-consp` and the response-text recognizers. Those rules are disabled in the two hints (4.6 s and 2.2 s → 0.1 s and 0.0 s) | 3.82 |
| `byte-store-k0` | 8.03 persvati; 11.2 hbox 4 jobs | Unchanged. It is re-measured because its provenance include changed. It never refers to the owner part, but narrowing its include would change what its dependents see, so the include stays | 8.48 |
| `bp-node-progress-bridge` | 8.70 persvati; 10.3 hbox | Three local lemmas opened the fragment and cp-id recognizers through `true-listp`. They now run in minimal theories (1.8, 1.3 and 0.6 s → 0.0 s) | 5.07 |
| `bp-handoff-status` | 10.26 persvati | `fn-bpah-job-match-binds-carrier` opened the found job's accessors. It now opens only its two definitions (4.3 s → 0.0 s) | 4.87 |
| `bp-report-deletion` | 8.92 persvati; 10.1 hbox | The guards of `fn-bpn-report-deleted-term` and `-payload` backchained `true-listp` through `fn-cp-idp-true-listp` and the NNTP response-text rules. Those rules are disabled in the guard hints (1.8 s and 2.5 s → 0.2 s and 0.6 s) | 5.58 |

Three books stay in the baseline with their earlier numbers. Their bytes did
not change, so the earlier hbox measurements still apply:
`store-node-invariants` (17.2 hbox; 9.24 persvati), `store-node-traces`
(13.8 hbox; 9.82 persvati) and `owner-invariants` (10.7 hbox 4 jobs; 9.91
persvati). Their persistence profiles are flat, with no rule that searches.
The slowest events are case splits of 1 to 1.6 s that earlier lanes already
tuned. In `owner-invariants`, 3.3 s is the include of `owner`. Bringing these
three under ten seconds with margin needs structural work: a split, or fewer
case splits in the relation theorems. A hint does not do it.

These runs certify books at these bytes. They do not certify an integrated
image. The ten-second rule's job count (decision 7) is still open; every
"after" figure is at two jobs.
