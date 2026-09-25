# Fan-in packets 1, 2 and 4 (2026-09-25)

Lane `lane/fanin-packets`, from dev `91c7dc24`. It carries out packets 1, 2 and 4 of
[the twins and fan-in audit](../audit-2026-09-25-twins-fanin.md). No theorem statement
changed, no theorem was added and nothing was registered. The moved theorems kept their
names.

## Dependent counts

Each count is the number of Makefile roots that `python3 tools/certify_books.py --affected-by books/<b> --dry-run`
prints, including the book itself. "Before" is at `91c7dc24` and "after" is at this lane's head.

| book | before | after | audit's expectation |
|---|---:|---:|---:|
| `injection` | 423 | 204 (packet 1 alone: 204) | 216 |
| `injection-shape` (new) | - | 427 | - |
| `hybrid-store-injected` (new) | - | 4 | - |
| `owner` | 158 | 78 | 78 |
| `node-config` | 213 | 80 (packet 1 alone: 202) | 87 |
| `native-admin` | 16 | 5 | 5 |
| `native-admin-shape` (new) | - | 18 | - |
| `native-admin-peer` (new) | - | 6 | - |

The shape books count slightly more than the old book did (427 against 423, 18 against 16) because each one adds itself and, where applicable, its sibling as roots.
- **injection:** the count is 204, not 216, because `poster-bytes` now includes `injection` directly (see findings below).
- **node-config:** the count is 80, not 87. peer-inbound includes node-config's own includes instead of node-config. peer-inbound-invariants now includes node-config itself. With both changes the count comes out 7 below the audit's figure.

## What moved

- **Packet 1.**
  - `books/injection-shape.lisp` holds the audit's 13 names: five field-name constants, `fn-inj-car`, `-cdr` and `-nth`, `-single-fieldp`, `-absentp`, `-from-validp`, `-mandatory-reason` and `-proto-reason`.
  - Those names are disabled at export through `fn-inj-shape-vocabulary`, as `fn-inj-vocabulary` disabled them before. `books/injection.lisp` includes the shape book and enables that theory locally, so its own proofs see the same theory as before.
  - `hybrid-carrier` and `hybrid-store` now include only the shape book.
  - `books/hybrid-store-injected.lisp` holds `fn-hsig-injected-carrier-plan`, `-octets` and `fn-hsig-authorized-injected-carried-submission-event`. It is included by `hybrid-store-invariants`, `host/native/build.lisp` (in place of `books/hybrid-store`) and `host/native/build-dtn.lisp`.
- **Packet 2.** `bp-native-app` and `peer-inbound` include the includes of `owner` and `node-config` instead of those two books.
- **Packet 4.**
  - `books/native-admin-shape.lisp` holds the argv bound, the decimal parser, the result record and the configuration record name, with `-config-name-of-one` and `-refuses-overflow`.
  - `books/native-admin-peer.lisp` holds the peer and bp-boundary parsers, the `peer list` codec, the peer and boundary theorems and the report.
  - `books/native-admin.lisp` keeps the group-name rules, `fn-native-admin-plan`, the plan's deltas, the theorems that read the plan, and publication.
  - `native-control`, `native-hybrid-control` and `native-config-observation` include only the shape book.

## Findings: names reached only through the removed edges

The audit's static scan checked only whether the direct includer uses a name. A closure check went further: for every book, test and host file, every `def*` name it mentions must be defined somewhere in its new include closure. That check found six edges the audit missed. Each is now an explicit include:

- `books/poster-bytes.lisp` uses `fn-inj-source-of`, `-strip`, `-take`, `-path-line` and `*fn-inj-path-field*`. It had reached them only through `hybrid-store`. It now includes `injection`.
- `books/peer-inbound-invariants.lisp` uses `fn-cnode-node-prepare-stages-the-offered-groups` in a `:use` hint. It had reached it through `peer-inbound` -> `node-config`. It now includes `node-config`.
- `host/bp-native-app-host.lisp` calls `fn-own-clock`, which it had reached through `bp-native-app` -> `owner`. It now includes `books/owner`. The host root is `tests/acl2/owner-log-tests` (in the run).
- `books/native-config-observation.lisp` uses the configuration codec (`fn-cfg-decode-exact`, `-record-generation`, `-recordp`). It now includes `config`.
- `books/native-admin-peer.lisp` uses `fn-nntp-decimal-field` and includes `nntp-syntax`.

With these includes, the check reports 77 unresolved (file, name) pairs, the same number as at `91c7dc24`. None of those pairs is new.

The run found no proof that silently relied on a rule from a removed edge: every one of the 446 books certified. The run did not exercise a pcert Convert wave.

## Certification

- Run: `run-20260925T021750Z-7692`.
- Certify id: `certify-20260925T021807Z-3342179`.
- Host: persvati. Toolchain: `/home/ember/fn-gates/toolchains/w25/acl2-literal` (ACL2 8.7, toolchain identity `1b4169e9`).
- Settings: 2 jobs, 300 s per-book timeout, incremental (not `--closure`), cache `/home/ember/fn-certcache`.
- Tree: `/home/ember/fn-gates/fanin-539c0d37` at commit `539c0d37`.
- Scope: 427 roots, the union of `--affected-by` over the 16 changed books. 130 books were installed from the cache, and 446 certified, all passed.
- Wall: **806.3 s**. Book walls sum to 1608.5 s. The largest is `store-node-traces` at 11.0 s.
- Manifest: `planning/evidence/manifests/certify-20260925T021807Z-3342179.json`.
- One run covered all three packets. At the audit's calibration of about 1.9 s per book at 2 jobs, 427 roots fit the budget.
- `python3 tools/green_check.py --changed-since 91c7dc24`: `16 changed books, 416 books include one; 0 not green at the bytes a merge would carry.`

Book walls in this run, in seconds, at 2 jobs:

| book | wall |
|---|---:|
| `native-admin-shape` | 2.1 |
| `native-admin-peer` | 8.2 |
| `native-admin` (was 9.8 at persvati `certify-20260925T010501Z`) | 5.1 |
| `injection-shape` | 0.6 |
| `injection` | 0.6 |
| `hybrid-store` | 2.2 |
| `hybrid-store-injected` | 1.9 |
| `bp-native-app` | 4.4 |
| `peer-inbound` | 8.8 |

The native-admin chain is serial (shape, then peer, then admin): 15.4 s of certification in three books, each under 10 s. A verb change to `native-admin` now recertifies 5 roots. A change to the peer or boundary parser recertifies 6.

The old book's slowest events are now in `native-admin-peer`: `fn-native-admin-peer-plan-base-kind` took 1.95 s, one `encapsulate` 2.42 s (the log does not name which of the two that moved here) and the `bp-boundary-plan` defun 1.62 s. So that book, not `native-admin`, is the next place to look for time.

## Limitations

- The dependent counts are dry-run root counts, not measured edit-to-verdict times.
- The run did not build the native image. The two build scripts gained or changed one `include-book` each, and their ACL2 prefix was not translated here.

## Registry and baseline edits the run required

- **PRF-032.** `tools/certified_claims.py` failed PRF-032 because the include closure of `books/store-files-invariants` now contains `injection-shape`. The row now cites this run's manifest, which certified that book at its current digest. The row's statement and events are unchanged.
- **Proof-cost baseline.**
  - `tools/proof_cost.py --write-baseline --allow-regression` removed `native-admin` (11.4 s -> 5.1 s) and `bp-node-progress-guards` (10.1 s -> 8.3 s).
  - It added `owner-invariants` at 10.9 s and `store-node-invariants` at 10.6 s, both at persvati at 2 jobs. Their earlier 2-job persvati walls were 9.7 to 10.2 s and 9.7 to 10.0 s. Their slowest events are `include-book` of `owner` (3.6 s) and of `store-node` (2.0 s).
  - This lane measured them once, so it does not claim the split caused the added 0.7 s. It does not claim the load on the box caused it either.
- `make check` passed with the ledger and current view regenerated. Both generated files were then restored and are not committed.
