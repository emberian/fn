# operator-daily (wave 4, lane 5), 2026-09-26

Brief: build/coordinator/queue/done/w4-operator-daily.txt (mandate section
11: health that distinguishes the states). Base dev 7e62ed3e; branch
lane/operator-daily. Ids: PRF-172, HST-010, SCN-102, PKT-453, PKT-454.

## What an operator now reads

- `health` while a restarted owner recovers its store (the writer lock held,
  a control socket configured, nothing answering yet):
  `health exit=20 state=fenced reason=starting (a process holds the store
  lock and nothing answers on the control socket yet: an owner starting or
  recovering, or an offline command; retry)`. Before: `state=fenced` and a
  second line `reason=store-held`, the words of a stuck lock (PKT-283; the
  operator walk's item 4). `store-held` remains for a lock with no socket
  configured (no owner would ever answer) or a lock the probe could not read.
- After a SIGKILL, `control list` (and every offline `control`/`peer` verb)
  prints `stale control socket removed (...)` and answers offline; before,
  the mutating verbs were refused until the operator deleted the node by hand
  (PKT-344). With no socket node and a held lock the mutating verbs refuse
  `store-held` without starting the offline executor.
- The owner's log names the class of a control request it refused on a
  store, OS or socket error (`control request refused (store-error): ...`);
  before, those three were silent (PKT-264 (2), the logging part only).

## Theorems (PRF-172) and the host lines that call their subjects

- `fn-nh-exit-code-is-zero-or-past-the-outcome-codes` (books/native-health.lisp),
  no hypothesis: `(fn-nh-exit-code v)` is 0 or at least 19, and
  `(fn-outcome-codep code)` iff `code = (fn-outcome-code :accepted)`.
  `fn-outcome-codep` reads `*fn-outcome-codes*` (books/outcome-class.lisp), so
  an outcome code added at 19 or above breaks the proof: the tables cannot
  drift. Subject called: `fnn-operator-execute-health` returns
  `fn-native-health-host-exit` of the report, which equals `fn-nh-exit-code`
  of the verdict (`fn-nh-report-exit-of-render`). PKT-329 (1) retired.
- `fn-nh-exit-code-cases` exported (was local): at most eight outcomes, the
  code is in (0 19 20..27).
- `fn-nh-fence-of-starting-iff`: with no clone fence and a route that did not
  reach an owner, `fn-nh-fence-of` is `:starting` exactly when the lock is
  `:held` and an owner would listen; a free or absent lock is never fenced.
  Host: `fnn-operator-health-report` (host/native/operator.lisp) calls
  `fn-native-health-host-fenced` (host/native-live-status-host.lisp) with the
  fourth observation, `(and control-path (not (fnn-image-omits-p :control)) t)`.
  `fn-nh-fence-of-route` restated over the four observations.
- `fn-native-control-liveness-decides` (books/native-control.lisp): the offline
  executor starts (`fn-native-control-liveness-offlinep`) exactly when the lock
  was seen `:free` or `:absent`; the decision is `:stale` exactly when a socket
  node is present and the lock is free or absent; it is one of `:live :stale
  :offline :held`. Host: `fnn-operator-execute-admin` calls
  `fn-native-control-host-liveness` (host/native-control-host.lisp); `livep`
  is now `(eq liveness :live)`, not the file-type check. The host performs a
  `:stale` removal with `fnn-control-remove-stale-offline`
  (host/native/control.lisp) under the ACL2-derived control-path lease, as
  `fnn-control-listen` does, so an owner that starts meanwhile (it takes the
  lease before it binds) is never unlinked; the executor still takes the
  exclusive writer lock itself, so a race with a starting owner is refused by
  the lock.

Teeth: tests/acl2/native-health-tests.lisp (a positive `:starting` witness
whose rendered first line and exit 20 are asserted; must-fails without the
no-clone and the route hypotheses; the held/clear/unobserved witnesses 23, 0,
19 with `fn-outcome-codep` of each; `fn-nh-exit-code-cases` without the
length bound fails, `*nht-long*` exits 100); tests/acl2/native-control-tests.lisp
(one witness per arm; the pre-PKT-344 node-alone rule refuted on a stale
node; must-fails without the lock and without the node). Both books and
test books were loaded in persvati REPLs before the farm run.

## Assurance chain

native entry `fn operator CONFIG health` / `control VERB` -> host observations
(lstat of the socket node, `fnn-store-owner-observation`'s non-blocking
shared flock, the clone fence file, the configured path) -> ACL2 subject
(`fn-nh-fence-of`, `fn-native-control-liveness`) -> rendered words
(`fn-nh-fence-words`, `fn-native-control-liveness-note`) and exit
(`fn-nh-exit-code`, `fn-native-control-status-exit-code`) -> keystones above ->
native cases (SCN-102). No state is carried between invocations: each verb
takes its observations once, so there is no maintained relation to preserve.

## Decision (PKT-454)

`starting` is a reason of the fenced state (exit 20), not a ninth state with
its own code. Trace: the verdict's eight states and codes 20..27 are
monitored (HST-007) and the fenced state is exactly "the store cannot be
served now"; a ninth code would change the scale monitors read. Default
taken: exit 20, first line `state=fenced reason=starting`. Rejected
alternative: a state `starting` at index 0 (every other code shifts by one)
or at 28 (out of priority order: a starting owner would rank below
receipt-debt); cost: a monitor contract change. What continues without it:
everything; the words are ACL2's either way.

## Certification

- r1: persvati run-20260926T105331Z-c89c (`--affected-by` native-health,
  native-control, native-live-status, native-operator, outcome-class): 18
  books certified, 269 from the cache, none over 10 s; manifest
  planning/evidence/manifests/certify-20260926T105358Z-645186.json.
- r2: persvati run-20260926T105609Z-b19e after 9f760025 (native-operator's
  comment, native-health, native-control): 8 certified, 206 from the cache,
  none over 10 s; manifest
  planning/evidence/manifests/certify-20260926T105642Z-673835.json.
- r3: persvati run-20260926T110333Z-bd99, the regenerated
  tests/acl2/docs-operator-grammar-tests.lisp (docs/operator.md's line numbers
  moved): 1 certified, none over 10 s; manifest
  planning/evidence/manifests/certify-20260926T110357Z-754509.json.

## Native (hbox, tools/hbox_native.sh, source 9f760025, images developer and production)

hbox:/tank/fn/scratch/operator-daily/native-n2; fn-host
ca94a502e09bdf34a499add1829f23c3fdac4e1114717ce697c7c5144d98b22d,
fn-host-developer 11ee7757220ebd0ebb87cb2d3c27eeb68cf60ce91158bfff68467e04e7b71316
(SHA256SUMS in planning/evidence/operator-daily/SHA256SUMS-n2).

| module | result | log (SHA-256) |
|---|---|---|
| tests.test_native_control (16 cases, both SCN-102 cases among them) | OK | operator-daily/native-control.log 9dbb6021e0ce70cc71b3da6c6ef025b12a3b989cb566def5957cb6f5c9705199 |
| tests.test_native_operator_verdicts (FN_NATIVE_HOST set; the one skip is the hybrid E2E's OpenSSL gate) | OK (skipped=1) | operator-daily/native-operator-verdicts.log 44c9c484e2d17f988b54df8b61ed7b3b29c8219d51bb957f7b9d022565031f4a |
| tests.test_native_operator_cli | OK | 1e6a697f219e9d12fe77b5df1aa25e2de3e30e60392a40fe139f0d5e0db0340e (on hbox) |

The first run (n1, the dirty tree at 2da298d9) found one failure outside
this lane's change: test_native_operator_cli read books/native-operator.lisp
as ASCII and a section sign in a comment (85f35331) raised
UnicodeDecodeError. Classification: implementation (a non-ASCII byte in a
book). Repaired in 9f760025; green in n2.

## Not done (PKT-453)

- PKT-264 (2) and PKT-209, the reason on the wire: the FNCT reply is one enum
  and the injection reasons are open-ended (fn-inj-proto-reason passes the
  article parser's error words), so appending an enum value per reason does
  not close. Owed: a refusal reply carrying ACL2's reason word as a bounded
  field after the status, used by the operator post
  (fnn-owner-control-submit-serialized, fn-native-control-refusal-status) and
  the live reconfiguration (fnn-owner-live-admin-serialized returns bare
  :refused while fn-cfg-delta-reason has the word), with the theorem that the
  printed word is the decision's reason; `control evidence`, `control log`;
  the carrier-render theorem. Done: the owner's log names the class of the
  three refusals control.lisp swallowed.
- PKT-264 (1) `bp-node health`; PKT-220 live `bp-obligation status` and `store
  retention` (no control request kind was taken); PKT-098 alerts and
  `--explain`; PKT-016 `[acl2] heap_mb`; PKT-286 the walk as tests.
- PKT-269: the report functions stay `:verify-guards nil`, and so does the
  chain beneath them (books/store-budget.lisp fn-sbud-bytes-used,
  fn-sbud-headroom-at, fn-sbud-bytes-extend), which must be verified first.
- The seconds since the lock was taken: flock does not touch the lock file,
  so its mtime is not an observation of the holder.
- Include hygiene: native-health now includes outcome-class, which ends with
  no theory withdrawal (warn; PKT-329 item 4).
