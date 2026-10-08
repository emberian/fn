# Pipeline code-phase evidence — 2026-10-08

Status: code and narrow certificate closure complete; not READY for integration.
N owns the native POST p50/p99 gate. No image was built, no commit or push made.

## Proofs and connection to execution

The host calls derived entries in `books/owner-commit-durability-steps.lisp`.
Each calls its `fn-ocp-gc-host-step` arm; its unconditional `-by-definition`
equation includes the returned state and effect packet. START's real drain is
split into begin/reserve/take/member/seal; each I/O effect has a separate receipt.
The existing kernel, OCP admission and OCVM reader vocabulary remain the model.
The counted dispatcher projection commutes unconditionally, including effects.
Guards are verified without testing the full semantic invariant on the served path.

Proved signed keystones: `fn-lgk-append-behind-safe`, `fn-lgk-pipe-fence-safe`,
`fn-ocp-gc-linkedp-initially`, `fn-ocp-gc-linkedp-preserved`,
`fn-ocp-gc-reveals-are-durable`, `fn-ocp-gc-failure-fences-both-batches`, and
`fn-olr-gc-membership-and-profile-bounds`. The reveals claim is a corollary.
Effect/drain preservation lemmas are separate local proof-book dependencies;
there is still only one dispatcher. Held coherence is additional, not a narrower
LINKEDP hypothesis. Physical prefix-fsync and promotion proofs retain the original
byte-store semantics and restore the existing single-inflight relation.

REPL on persvati: seven signed defteeth declarations bind to the actual formulas;
all positive/removal witnesses pass, and five early-release mutants are rejected.
Seven additional physical/refinement declarations pass. The crash-image witness
uses ACK=1 and proves its positive/removal ground lemmas because crash-imagep is
quantified; it is not presented as ordinary executable predicate evaluation.
Other teeth: original nine positives/eight must-fails and event matrix; 1,728 drain
cases; physical prefix/failure/promotion; exact encoded profile fit and removal;
held zero-record frames, stop/no-submit; wake/append-return races; role-bank receipts.
All 348 heap witnesses pass with the explicit extra worker (+5 MiB reservation).
No signed theorem, lock rule or ratchet ceiling was weakened.

## Certificate gates

`farm.py submit persvati --lane --affected-by` every book in `changed-books.txt`,
plus the two registered teeth books, `--images off --jobs 2`:

- `run-20261008T121143Z-7b0a` included the umbrella needed for host load:
  24 books passed, zero ACL2 Error lines across all 25 logs; umbrella failed.
  Triage: OTHER, SBCL thread-local storage exhausted at `bp-listener-set` under
  the configured certifying `acl2-literal-4g-tls64k` launcher.
- `run-20261008T122416Z-09fc` is the narrow lane verdict: exit 0, manifest
  `certify-20261008T122443Z-3190801` passed, all 551 exact-form books cached,
  33 roots. This run certified nothing afresh; it does not erase timing debt.
- D26 remains red in the fresh run: drain/concrete 10.1 s each, host/store-host
  18.9 s; broader required umbrella dependencies also exceed ten seconds.
  The held-seal proof fell from 793,274 to 72,856 steps; take representation
  fell from 545,689 to 194,319. Formula strength is unchanged.

The farm's TLS256k launcher is explicitly load-only (tools/farm.py:108–114),
with a different toolchain identity; it was not used to certify or publish.
The remaining full-world certificate blocker needs the coordinator/toolchain lane.

## Host and static gates

- Requested `host_check.py --load` on persvati exits 0: 58/58 raw files,
  zero findings, 3.7 s, but explicitly BARE fallback. `--require-world` exits 2
  NOT RUN because the current umbrella certificate is missing. Interface/world
  validation is therefore not claimed complete.
- `interface_emit.py --check`: 1,850 declared, 1,801/1,801 dispatched, zero findings
  and zero class/kinds disagreements. The existing output-tariff unresolved name
  is reported by the tool and is not counted as a failure.
- `keystone_emit.py --check`: 14 defkeystone forms in four books, zero findings.
  Fourteen new bound defteeth rows are in the generated obligations manifest;
  PRF-272/245/1245 describe their subjects. No ceiling or baseline was changed.
- `lock_discipline_check.py --check`: global RED, 69 new finding rows, four stale,
  plus four pre-existing BP callback audit moves. ZERO additional finding keys
  against read-only train31 control; see `LOCK-CONTROL.json`. The requested
  `tools/lock_discipline.py` filename does not exist in this tree.
- `native_program_check.py`: zero mismatches over two programs; three log arms,
  cut map, statement route, holder cuts and 15-log/7-segment cut inventory pass.
  Its 29 focused Python tests and the scheduler source test pass.

## Native change and retirement

Both queued and held callers use the same off-owner pipeline. A separate funded
append actor writes B while A's barrier runs; both physical and operation receipts
retain custody through escape. Each bank is retained before mutating installation.
Reader captures remain at durable boundaries. Profile preflight precedes dequeue.
The inline queued helper/action/classifier, hidden :full wait/flush fallback and
optional old batch-job branch are deleted. LOCK-R2-COMMIT-INLINE-LOG-IO is marked
ready with this scoped retirement. Shared fdatasync/pwrite-under-O keys remain
on other direct bound commits; deleting this route cannot erase those global keys.

Raw persvati fixtures: BP identity and bound settlement pass; actual pipeline
post-launch escape passes 12 schedules, plus torn-consumption custody/no retry.
The recording custody fixture includes second-bank install escape retention.
Typed custody passes actual producer/receipt checks and six actual typed
abandonment schedules, using the real ACL2 world and judged dispatch verdicts.
The final harness raw-arity check has zero findings; its three unrelated stale
hand stubs (cold poll, output window, extent window) remain reported.
The generator refreshed affected shared raw harness blocks, rather than hand-
editing their signatures. Existing unrelated harness stub findings stay visible.
