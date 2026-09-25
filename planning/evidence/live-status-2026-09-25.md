# Live status: the running owner answers — 2026-09-25

Lane `lane/live-status`. Closes the spike deferral "live status, obligations,
pins" (planning/evidence/spike-operator-2026-09-25.md on `spike/mega`): with an
owner running, `operator CONFIG status`, `pins`, `obligations` and `peer list`
answered `store is already locked`.

## What changed

- **One renderer, in ACL2.** `fn-nls-report` (books/native-live-status.lisp)
  renders every word of the four reports from the Store state, the persisted
  profile, the committed record octets, the configuration, the open
  connections' configuration pins and the answering process's open
  observation (staging orphans, `open=`). `fn-nls-offline-report` is it over
  the replayed Store, with every record re-encoded once and no connection;
  `fn-nls-live-report` is it over what the owner carries, with the carried
  (K . SUM) octet sum extended (not stored).
- **Offline path**: host/native/io.lisp `fnn-command-live-report` →
  host/native-live-status-host.lisp `fn-native-live-status-host-offline`.
  `store ROOT status` and `operator CONFIG status` both use it, so the
  offline `status` words are now ACL2's (they were `format` in io.lisp).
  `transactions=` is `fn-sbud-used` (the committed Store records), the same
  count as `headroom transactions-used`.
- **Owner path**: FNLS frames (magic `FNLS`) on the existing control socket.
  host/native/control.lisp `fnn-control-handle-client` → `fnn-control-live-status-answer`
  (under the owner mutex) → `fn-native-live-status-host-reply` →
  `fn-nls-reply (fn-nls-live-report ...)`. The wrapper takes `state` and
  returns one value, so it cannot update what it reads.
- **Client**: `fnn-control-live-status` folds pages (≤ 128 KiB each; a work
  bound per request, no bound on the report) through `fn-nls-client-step`;
  a report that changes between pages (digest or total differ) restarts, at
  most 8 times.
- **Route** (`fn-nls-route`): no control socket, or one nothing accepts on
  (failure before submission) → offline, whose shared lock refuses behind a
  live owner; owner refusal → 1; anything else → 3.
- **Grammar** (books/native-operator.lisp): `status [--watch SECONDS]`
  (1..86400), `pins`, `obligations`; `peer list` (an admin query plan)
  routes the same way with kind `:peers`.
- BP forwarding obligations are not in these reports: the NNTP owner carries
  no BP node; the DTN image's `bp-obligation status` is the equivalent.

## Theorems (books/native-live-status.lisp)

- KEYSTONE `fn-nls-live-report-is-the-offline-report`: when
  `(fn-sbud-octets-cache-validp cache (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))`
  and `(not (consp (fn-ocfg-pins oc)))`,
  `(fn-nls-live-report kind profile oc cache obs)` =
  `(fn-nls-offline-report kind profile (fn-own-store (fn-ocfg-owner oc)) (fn-ocfg-config oc) obs)`.
  Built on `fn-sbud-bytes-used-is-kernel-sum`.
- KEYSTONE `fn-nls-client-step-of-owner-reply`: for an octet `report` with
  `(fn-record-uint32p (len report))`, `(<= (len acc) (len report))`,
  `(equal acc (take (len acc) report))`, and (for a non-empty `acc`)
  `total = (len report)`, `digest = (fn-frame-trailer report)`:
  the client's step on `(fn-nls-reply report (len acc))` is `(:done report)`
  when one chunk reaches the end, else `(:next (take (+ (len acc) chunk) report) (len report) (fn-frame-trailer report))`.
- Supporting: `fn-nls-open-of-seal`, `fn-nls-reply-decode-of-encode`,
  `fn-nls-request-decode-of-encode`, `fn-nls-reply-decode-of-reply`.
- **Not a theorem**: "answering changes no state" is the wrappers'
  signature (one value, no `state`), which ACL2 enforces; there is no ACL2
  statement of it. The multi-page join trusts the SHA-256 frame digest to
  name one report (A-CRYPTO).

## Teeth (tests/acl2/native-live-status-tests.lisp)

Witness: owner-store-budget-tests' host-shaped owner with one committed
article (bytes-used > 0, one retention pin), the owner's full cache. Live
equals offline for `:status` and `:obligations`; the words begin
`transactions=1 articles=1` and `obligations=1 reserved=2`.
Per hypothesis: stale sum (+5 octets) → different words (assert + must-fail);
a connection pin → the `:pins` words differ (assert + must-fail); non-octet
report → `(:refused)`; non-prefix `acc` → `(:done (1 3))`; `acc` past the
report → `(:refused)`; wrong total → `(:restart)`; the uint32 total has only
a must-fail under the keystone's hints (no report that long can be
evaluated) — `teeth_check` flags 4 witnesses for 5 hypotheses for this
reason. A two-page report (chunk + 1 octets) joins to itself.
native-operator-tests: `--watch 5`, `86400` accepted; `0`, `86401`,
`pins x` usage (5); `pins`/`obligations` are `:status` actions.

## Certification

persvati, ACL2 8.7 w25 (`/home/ember/fn-gates/toolchains/w25/acl2-literal`),
2 jobs, timeout 300 s:
- run-20260925T085652Z-9026, manifest
  `planning/evidence/manifests/certify-20260925T085736Z-2917237.json`:
  books/native-live-status 7.98 s, books/native-operator 6.83 s,
  host/native-operator-host, native-operator-host-tests passed; the two test
  books failed (a help-text assertion; a ground must-fail that did not
  return in 300 s).
- run-20260925T090430Z-61da, manifest
  `planning/evidence/manifests/certify-20260925T090503Z-3006124.json`:
  tests/acl2/native-live-status-tests 6.13 s, tests/acl2/native-operator-tests
  5.68 s, passed. `green_check --changed-since 24591e11`: 4 changed, 1
  dependent, all green.
hbox (w28 `acl2-literal-4g`, 4 jobs, `swarm-build`): the default image
closure's 82 uncached books certified in
`/tank/fn/scratch/live-status/cert-d73908ee` (certify-20260925T085945Z-2983751,
all passed, including native-live-status and native-operator).

## Native (hbox)

Developer image built from d73908ee (host sources unchanged since) in
`/tank/fn/scratch/live-status/cert-d73908ee/build/fn-host-developer.core`,
SHA-256 `cb37b918989a2b3787a17db7ef9e06f9a94c77cb3b17ce47af981299f739d8f3`.
Owner under `systemd-run --user -p MemoryMax=24G`, loopback port 11961,
store in `/tank/fn/scratch/live-status/run`. Script and outputs:
[live-status-2026-09-25/](live-status-2026-09-25/) (`native.sh`,
`summary.txt`, `SHA256SUMS`).

- A running owner answered `status`, `pins`, `obligations`, `peer list`
  (after a live `peer add`), each exit 0 in ~0.07 s; no `already locked`.
- With one NNTP connection held open, `pins` answered
  `connections=1` / `connection id=1 config-generation=2`.
- `status --watch 1` under `timeout 3.6`: 4 reports, 4 tagged lines.
- POST burst: 60 `operator post` through the control socket while 20
  `status` ran: 60/60 accepted, 20/20 statuses exit 0, status latency
  min 0.075 s, median 0.26 s, max 0.55 s (it waits for the owner mutex
  behind a commit); the burst took 20.36 s against 18.38 s for 60 posts
  with no status (about 11 % slower wall).
- After `systemctl --user stop` (unit inactive), the offline `status`,
  `pins`, `obligations`, `peer list` equal the owner's last answers byte for
  byte (status SHA-256 `065642b4…5716` both; 123 transactions, 123
  obligations). Offline takes ~0.73 s (full record re-encode); live ~0.07 s.

## Limitations

- Octet lists end to end (D27 concrete twin open for the FNLS codec and the
  renderer), like the FNCT codec.
- The owner renders the whole report per page; a large `obligations` report
  costs one render per 128 KiB page under the mutex.
- The `open=` and orphan fields are each process's own open observation;
  they matched here but need not after a crash.
- Run on a developer image only; no production image, no qualification.
