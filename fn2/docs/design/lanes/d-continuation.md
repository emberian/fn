# fn2 layer D continuation (present state, rewritten whole; 2026-10-30, the fifth Opus seat)

Seat: Opus, layer D (machines, scheduler over principals, accounting, NNTP over them). The seat WRITES
the code; Codex (second account) takes only bounded pieces with real signatures pasted, every line read;
Astra (`codex exec -m gpt-6-astra -s read-only -C /Users/ember/dev/fn`) reviews designs as a peer before
code. Brief: `build/coordinator/briefs/FN2-LAYER-D-MACHINES-NNTP.md` over `FN2-SEAT-COMMON.md`. Layer
doc: `fn2/docs/d-machines-nntp.md` on dev: §4 D3 as built, §13 D7, **§14 D4+D5 (design, Astra-reviewed,
`build/d-seat/d45/astra-1.md`)**, §10 open items, §12 quests.

## Tree
- Shared tree `/Users/ember/dev/fn` on `dev`: D's own books (upload-scan, later upload/txn/conn edits that
  touch no foundation) are edited and committed there by pathspec (`git commit --no-gpg-sign -F <msg> --
  <paths>`, new files `git add -N` first; never stage). Messages in `build/d-seat/d45/*.msg`.
- Foundation edits (assembly includes, A's machines.lisp/pool-ranges for A-S7/A-S8 if main lets D write
  them) go in the worktree `build/lanes/fn2/d7` (branch `fn2/d7`, behind dev now: merge origin/dev first),
  whole-tree gate, then ff dev.
- Forge clone `/build/lanes/d7` (branch `lane`) is the D gate tree (at D7 3/n). No setsid on the Mac: use
  `python3 build/d-seat/bin/detach.py PIDFILE LOG -- cmd...` (setsid + group-leader pid written).
- Stuck processes to report (not ours, no PID file): forge pid 427111 (old accounts-unit certify in
  /build/lanes/d3b); laptop pid 80380/80382 (`timeout 180 acl2-literal-4g-tls64k`, 1 d 23 h at 99%).

## Done (this seat)
| quest | commit | one line |
|---|---|---|
| D4 1/n | 92a31a6dd | `fn2/books/upload-scan.lisp`: bounded header scan (fn1 header syntax, limits, Message-ID/Newsgroups/Path ranges, SEEN bits) and the definite verdict in H's model order; `tests/upload-scan-unit.lisp` 33 fixtures x every split point |
| D4 1/n input | 228a59645 | `fn2/books/upload-feed.lisp`: streaming 5-state unstuffing feed RX (conn owner) -> chunk (upload owner), octet by octet; framing per framing.py; `tests/upload-feed-unit.lisp`; A-S8 now perf-only |
| D5 1/n library | a8ead74eb | `fn2/books/claims.lisp` (fn2-claims stobj: begin / walk with stamp restart / release with FIFO hand-off), `tests/claims-unit.lisp`; layer doc takes C's amended C-S2 |
| D4+D5 design | b416f0308 | layer doc §14 with Astra's six changes; seams A-S7, A-S8, B-S1, B-S2, C-S1, C-S2 sent to main (READY + seam message 2026-10-30) |
Earlier seats: D0, D1a, D2a-c, D3, D7 1/n-3/n (layer doc §12, §13).

## D4/D5 key decisions (read §14 for the whole)
- Rulings received 2026-10-30: C agreed C-S1; C amended C-S2 (in :ready: `fn2-identity-stage d` before
  `fn2-commit-admit-txn`, `fn2-identity-bind d batch article binding principal` after its :ok, infallible;
  commit kind calls `fn2-identity-publish batch` / `fn2-identity-drop batch`); DSL seat: D writes A-S7
  (taken kinds) as a foundation commit ON TOP OF S1 (main sends S1's sha; S1 adds
  fn2-machine-admission-books-p and copies principal-slot/account-ref), whole-tree gate (every unit book,
  A's seven drivers with the 113 A4 blocks identical, B's units), DSL seat reads the diff first; S1's
  refused booking admits unbooked and renders 400 (no parking): accepted.
- Owed in claims: waiter cancellation (an aborting upload's txn waiting in a FIFO).
- Three machines: conn frames blocks + copies (fn2-upload-feed, cost 1024 framed + 1024 rescanned + 1024
  copied), upload hashes/scans (B's fn2-b3 row 2+window), txn claims/decides/stages/commits.
- Transaction row taken at the upload's :identity, then claim (txn :reserve holds no claim); POST without
  Message-ID generates one before claiming.
- Identity facts staged into the batch's private successor overlay at :prepare (C-S2), exposed at publish.
- Evidence of conflicting content is its own operation; C-S1 answers :evidence vs :duplicate.
- Posting capability (greeting 200, CAPABILITIES POST, 340) stays OFF until D5 2/n's durable POST; the
  interim path runs under profile key `:posting-interim t` in tests only.
- Outcome words posted to the conn row with generation AND request ordinal; TAKETHIS token kept in a
  reserved TX tail.

## D7 as built (for the next slice)
- Ledger rows: P+1 (row P = system). Dimension-major arrays; holdings `:connection-row
  :principal-reservation`; charges `:rx-octets :tx-octets :requests :run-steps :run-bytes`. Readers
  `fn2-account-{hold,reserve,limit,charged,committed,capacity}`; core readers
  `fn2-account-core-{hold,charged,limit,reserve,rows,conservedp}`.
- Seam entry points (names A wires; all in macro `fn2-account-events`, `fn2/books/accounts-core.lisp`,
  materialized today in `assembly-callbacks-d.lisp`; A moves the materialization before its own callers):
  `(fn2-account-book p fn2-core) -> (mv code fn2-core)` (S1), `(fn2-account-charge-run principal bytes
  steps fn2-core) -> (mv code fn2-core)` (S2), `(fn2-account-grant-ready-p fn2-core)` and
  `(fn2-account-grant-one fn2-core) -> (mv id fn2-core)` (S5; no grants until 4/n). Also
  `fn2-account-unbook`, `-book-admitted (refused p)`, `-unbook-ref (ref)`, `-charge-core (p k a)`.
  Each wrapper has frame lemmas `<op>-FRAME-<child>` over every other core child.
- fn2-conn: `account-ref` (common field) is the booked ledger row or `*fn2-none*`; greet books via
  `fn2-account-book-admitted`, refused -> 400 like the partition reserve; frame-run charges `:requests`
  before answering; observe-receive/-send charge octets; release unbooks via `-unbook-ref`.
- ACCOUNT (`fn2/sim/check-account.lisp`): `fn2-account-check rows records capacity`, controls
  `fn2-account-controls` (third control `:n/a` without reserves).

## Certify times (forge, merged tree b587be19f + 3/n; laptop for upload-scan)
| book | s |
|---|---:|
| books/assembly-access (A) | 48.4 |
| tests/runs-assembly (C) | 43.7 |
| books/assembly-callbacks-d | 22.6 |
| books/accounts | 9.6 |
| tests/conn-unit | 7.4 |
| books/owed-conn | 6.3 |
| books/conn | 4.7 |
| accounts-core, accounts-unit, check-account | < 1 each |
| books/upload-scan, tests/upload-scan-unit (laptop) | 2.0, 1.0 |
| books/upload-feed, tests/upload-feed-unit (laptop) | 1.4, 0.6 |
| books/claims, tests/claims-unit (laptop) | 5.7, 0.5 |
| tests/sim-layer-d.lsp (LD, 18 runs) | about 3 min |

## In flight (uncommitted, worktree `build/lanes/fn2/d-taken`, branch `fn2/d-taken` = fn2/a-seams6 (S1-S5) + dev)
- A-S7 in `fn2/books/machines.lisp`: defmachine `:taken (:phase :rows :ranges :copy :clear)`,
  `fn2-machine-taken`/`-partitioned`, `*fn2-machine-partitioned*` (directory uses it), generated
  `fn2-machine-take-K (waiter COPIES fn2-core) -> (mv code id fn2-core)` (parks the waiter on the
  partition FIFO with the row kind as wait reason) and `fn2-machine-reclaim-K`; the observation router now
  keeps any row parked on a resource kind parked (was: operation/storage-window/connection-row only).
- `fn2/books/upload.lisp`: fn2-input-config core child (`:posting-interim`, `:article-max`), fn2-upload
  kind (capacity 0 unless `:posting-interim`; hasher row 2+slot needs `:format-slots` >= 2+windows),
  ops (hash begin/step/end, scan step, verdict, `fn2-conn-post-word`, `fn2-upload-input`,
  `fn2-upload-advance`), arms (work, release/drain, abort). Words refined by field
  (`fn2-upload-word-by-field`).
- conn.lisp: new fields (upload upload-gen rule request feed-mode feed-discard word outcome-ready posting),
  arms open-block, block-input, feed-step, block (replacing unreached for :article-input), release
  notifies its upload; conn-answer: `posting` arg to fn2-answer/-ok/-greeting, POST -> :article-input,
  `fn2-answer-block-open`, `fn2-answer-post-reply`, `fn2-answer-outcome`. Test callers updated
  (conn-answer-unit, grammar-fuzz-export). owed-conn: `fn2-conn-wire-run-in profile`.
- tests/upload-unit.lisp: POST transcripts under `*fn2-uu-profile*`.
- Chain certify: `python3 build/d-seat/bin/detach.py build/tN.pid build/tN.log -- sh fn2/tools/certify.sh
  -j 8 books/assembly-callbacks-d.lisp` in the worktree. Then the whole-tree gate (A's seven drivers with
  113 A4 blocks identical, all unit books, sim-layer-d) and the DSL seat reads the diff before landing,
  once S1 is on dev.

## Next
1. **D4 2/n ingestion** (§14.8; first A-S7 on S1 in the d7 worktree): fn2-upload declared (needs A-S7: write the declaration and arms now,
   land when A-S7 lands or when main lets D write A-S7 as a foundation commit); fn2-conn fields (upload,
   upload-gen, rule, word, outcome-ready, request, token-off/len), the `:block` answer code in conn-answer,
   `fn2-conn-block` replacing fn2-conn-unreached for :article-input over `fn2-upload-feed` (landed), BLAKE3 over the window (fn2-b3-init/-update/-finalize, result into the
   row via fn2-digest-store), conn-unit POST transcripts under `:posting-interim t`.
2. D5 1/n (fn2-txn, fn2-txn-claims core child, the claim FIFO, generated Message-ID, lookup via C-S1),
   D5 2/n (one durable POST through B-S2/C-S2, posting on, regenerate fn2_conn_interim.json), D5 3/n
   (transit with request/reply queuing, evidence ops, scenario 5), D4 3/n (extents).
3. **Queued after D5 (main, 2026-10-30): D6**, the query cursor (ARTICLE/HEAD/BODY/STAT, NEXT/LAST,
   GROUP/LISTGROUP, OVER/XOVER, NEWNEWS; 15,028 interims in H's M1a). C3a on dev 654d1fd39: schemas in
   fn2/books/ordered.lisp (fn2-article id 2 latest-only, fn2-overview id 3 key (group, number), fn2-addr
   id 4), range.lisp `fn2-range-start` / `fn2-range-step` (:entry rows at fn2-ranges-out, :end :more
   :miss), read contract `fn2-read-plan (strength p fallback cov append) -> (mv outcome position limit)`.
   C3b on dev b44d74417: Seek(stream, after = p) via the fn2-seeks table (`fn2-seek-start`,
   `fn2-seek-step`), a bisection over the stream key's last field (each probe a one-entry range read)
   answering the number from which a read delivers exactly the entries after p. XOVER needs only C3a;
   NEWNEWS-by-position and D8's wait positions use C3b.
4. D7 4/n on S1 (main sends the sha), 5/n timers, 6/n TLS admission; prove fn2-account-ops-conserve.

## Commands that work
- Forge certify (PID file!): `ssh forge 'cd /build/lanes/d7 && (nohup swarm-build sh
  fn2/tools/forge-certify.sh -j 12 > build/cN.out 2>&1 & echo $! > build/cN.pid)'`; wait in a background
  `until ssh forge '! kill -0 $(cat .../cN.pid)'`. Times: `python3 fn2/tools/certify-times.py .
  build/certify-closure.log`. To stop a swarm-build job: its scope from `/proc/$(cat cN.pid)/cgroup`,
  `XDG_RUNTIME_DIR=/run/user/$(id -u) systemctl --user stop <scope>`.
- LD runs with a stoppable PID: `(nohup sh -c "exec tools/acl2 < X.lsp > build/X.log 2>&1" & echo $! >
  build/X.pid)`; stop by killing the sbcl child of that PID (`ps -o pid= --ppid $(cat build/X.pid)`).
- REPL over certified callbacks-a (events only; declaration changes need recert):
  `sh build/d-seat/d7-repl.sh`.
- Drivers: `sh fn2/tools/forge-driver.sh NAME` (A's six, `SECS=7200 ... sim-layer-b`); verdict = no
  "ACL2 Error"/"HARD ACL2" in the log; A4 blocks: copy the a4 log to `build/d-seat/a4-d7/` and
  `python3 build/seat-ad/compare.py build/d-seat/a4-d7 build/seat-ad/baseline-r5e2-a4.log`.
- OWED: `swarm-build sh fn2/tools/certify.sh --export-owed` in the forge tree, copy OWED.md back.
- ld a library + unit quickly: `build/accu-ld.lsp` in d3b (`(ld "fn2/books/accounts.lisp")` ...).

## Pitfalls hit
- A stobj helper whose preservation is proved inline in a big function costs minutes (claims walk:
  286 s): factor each multi-setter step into its own defun with `(TABLE-preserves f args :position k
  :raw-rows t)`; each helper must check its own indices so preservation needs no guard hyps.
- upload-scan: guard proofs over pool-reading helpers explode unless the helpers are disabled and
  every computed index is `nfix`ed; `min` disabled breaks linear facts (use an explicit `if`); a
  recursive driver over a 13-value line function needs the line function disabled for termination and
  `nfix` on every recursive argument.
- REPL a D library fast: `tools/acl2 < drv.lsp` with `(include-book "fn2/books/grammar")` then
  `(ld "fn2/books/X.lisp")`; test bodies: `ld` the unit with include lines stripped.
- A defun over stobj arrays: element facts must be rewrite rules (natp/rationalp/acl2-numberp) plus a
  typed reader (`nfix` of the element, disabled) so guards stay linear; index-in-range lemmas stated
  over the normalized `(nth *X-rows* st)` form, rule-classes rewrite and linear.
- Lemmas about `(fn2-X-rows st)` never fire: the accessor opens to `nth`; state them on `nth`.
- An arm that branches on the core (`(if c (mv :ok core) (op core))`) doubles every later subgoal
  (release went 7 s -> 29 s): put the branch inside a wrapper op.
- A recursive driver whose body is big: factor the body into a disabled non-recursive helper, or the
  termination proof grinds for many minutes.
- `cw` takes ~0..~9 only. ACL2 has no lambda arguments. `b*` needs std/util/bstar in sim books.
- defmachine declaration changes (uses/tables) are in conn.lisp's declaration, not the events macro:
  the REPL path cannot test them; recertify from conn.
- Background waits: never `sleep` in a foreground command; use a background until-loop.
