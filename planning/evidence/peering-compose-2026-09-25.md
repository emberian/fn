# peering-compose: one confirm configures the peer; declines stay declined (PRF-124, 2026-09-25)

Dev lane `lane/peering-compose` from `dev` 483987b1, brief
`build/coordinator/queue/w2-peering-compose.txt` (mandate §5.4, §12 packets 4,
5, 7, 8). Ids: PRF-124, NNT-022, SCN-069, PKT-173. Everything is `:logic`
with verified guards; no skip-proofs, defaxiom or trust tag.

## What now works (user-visible)

- **Two strangers become peers with one confirm.** `peer confirm ACCEPTANCE
  INVITATION` publishes ONE configuration record: the invitation's
  consumption and the invitee's peer record (`:set-peer`), bound
  `(:principal ACCEPTOR)`. There is no state with the invitation consumed and
  no peer (the developer stop after the record shows the peer already
  listed before the enrolment).
- **A declined key statement stays declined across a restart.** Native trace
  (packet 7, below): on the pre-packet image a statement declined for want
  of a `keys` grant ACTS at the next open once a grant was added live; on
  this lane's image it declines again at every open.
- **The admission verdict names its class** (packet 4) as a pure function:
  seven names, `:verified` only under both observations, `:carried` only on
  the D23 arm.
- **Pull cursor cuts** (packet 5): a developer selector kills the owner at
  each write of the FNPL publication, and a native campaign checks no
  skipped work and bounded duplicate replay at all six cuts.

NOT done: **packet 8 (pull over TLS with a principal binding)** -- design
below, no code. The pull client is still clear-text; no general secure
peering claim is made.

## Assurance chains

1. Confirm. native entry `fnn-pinv-control-handle` (control request 11, two
   blobs, `fn-pinv-confirm-request-decode`) -> `fnn-pinv-owner-confirm` ->
   ACL2 subject `fn-pinv-confirm-record-plan` (through
   `host/peer-invite-host.lisp fn-pinv-host-confirm-record-plan`, with the
   live invitations slot, snapshots and peers table) -> `(:configure DELTAS)`
   -> `fnn-owner-live-reconfigure-locked` -> `fn-owner-reconfigure-deltas`
   stages ONE record whose change is DELTAS -> on durable completion
   `fn-cfg-apply-record` runs the fold `fn-cfg-apply` -> behavioural keystone
   `fn-pinv-confirm-record-fold-consumes-and-configures` (row consumed by
   exactly this acceptance; peers table holds exactly the peer's rows; the
   crash point after the record resumes as `:enrol`) -> observed: `peer
   list` shows the invitee with `auth=principal <B>`. The maintained relation
   (the invitations slot and peers table ARE the replayed configuration) is
   the existing configuration replay's (`fn-pinv-consumed-stays-consumed-across-replay`,
   config-crash-replay); this lane adds no new relation.
2. Reopen of a key statement. native entry `fnn-owner-install` ->
   `fnn-owner-key-statement-recover` -> `fnn-owner-key-statement ... at-open`
   -> `fn-owner-key-statement-plan/-event` with AT-OPEN -> rows from
   `fn-owner-key-statement-rows` = `fn-ks-reopen-rows *fn-ks-reopen-policy*`
   over the Store's configuration journal `fn-sn-config-history` -> model
   `fn-ks-recover-recorded` -> keystones below -> observed log lines and key
   history. The relation used, "the configuration journal the open holds is
   the durable journal and each record applies before every event whose txid
   is not below its own", is C3's (`fn-ctl-config-at`, `fn-cpr-config-firstp`).
3. Admission verdict: `fn-pcb-admission-verdict` has NO host caller yet (the
   transit refusal detail still prints `fn-pcb-refusal-class`); it is the
   packet's definition, stated and proved, not a served-path claim.

## Theorems (all over the functions named; the book has them exactly)

books/peer-invite.lisp:
- `fn-pinv-confirm-record-configures-the-issued-invitations-peer`: a
  `(:configure DELTAS)` plan has the consumption plan `:consume`, the row
  pending, the presented invitation of kind invitation whose authored-source
  identity is exactly the pending row's (the invitation this node issued),
  the confirmed peer `fn-cfg-peerp` with auth `(:principal ACCEPTOR-HEX)` and
  a name no configured peer has, and DELTAS = (consume, set-peer).
- `fn-pinv-confirm-record-fold-consumes-and-configures`: over `fn-cfg-apply
  V GEN STAMP DELTAS` from the live value: invitation row = `(NONCE ACCEPTOR
  ASID 1)`; `fn-cfg-rows-with-key peers name = fn-cfg-peer-rows peer`; and,
  when the acceptor is not yet enrolled, the next confirm plan is `:enrol`.
- supporting: `fn-pinv-confirm-plan-never-configures`,
  `fn-pinv-confirm-record-plan-passes-the-other-plans`,
  `fn-pinv-confirmed-peer-auth`, `fn-pinv-invitation-row-after-consumption`,
  `fn-pinv-peers-of-consume-delta`, `fn-pinv-invitations-of-set-peer-delta`.

books/key-statements.lisp (packet 7):
- `fn-ks-reopen-is-blind-to-later-configuration`: configuration records all
  later than the pending statement's txid do not change
  `fn-ks-recover-recorded`.
- `fn-ks-a-decline-replays-as-a-decline`: a statement whose plan declined
  under the grants in force at its txid is left exactly as the acceptance
  left it by the recorded recovery over that journal plus any later records,
  at any recovery coordinates (same observations: the primitive over the
  same stored bytes, A-CRYPTO).
- `fn-ks-recorded-recovery-completes-the-cut`: every configuration record
  through the txid and the journal replaying, the recorded recovery of the
  cut equals the uninterrupted acceptance under the live (replayed) grants.
- supporting: `fn-ks-plan-needs-a-statement`,
  `fn-ks-declining-plan-executes-nothing`,
  `fn-ks-recover-without-a-pending-record`.

books/peer-carriage.lisp (packet 4): `fn-pcb-admission-verdict-names-its-class`
and `fn-pcb-absent-carrier-plan-is-absent`.

## Teeth

- tests/acl2/peer-invite-tests.lisp: the reachable `:configure` witness with
  every conjunct asserted (the peer is exactly `nodeB b.example (:nntp 1
  "127.0.0.1" 11190 (:clear)) ("fn.*" max 16) nil (:principal B)`); the fold
  witness from the issued value (row consumed, rows present, `peer-find`
  answers the peer, resumed plan `:enrol`, and `fn-cfg-admissiblep` of the
  record); must-fail per case: another invitation of this node
  (`another-invitation`, the sid conjunct fails), name taken
  (`peer-name-taken`), the acceptance in the invitation's place
  (`invitation-kind`), B already enrolled (resume not `:enrol`), and no
  `nodeB` before the fold. Control codec: kind 11 two-blob round trip, a
  single-blob kind-11 encode is `:bad`, cross-kind decodes are nil.
- tests/acl2/key-statements-tests.lisp: the declined acceptance (no grant
  through the txid), the later grant record, recovery leaves the state;
  must-fail with the grant AT the txid (the recovery acts); the pre-packet
  `fn-ks-recover` under live rows acts on the decline (the trace in ACL2);
  must-fail for the decline hypothesis (a plan that acts but whose event
  could not be built at the acceptance's coordinates is completed by the
  recovery); blindness reached with a later record and broken by one at
  the txid; the recorded cut recovery equals the acting acceptance.
- tests/acl2/peer-carriage-tests.lisp: one witness per verdict (seven);
  must-fail: an absent carrier is `:unsigned`; one refused observation is not
  `:verified`; a carried input is never `:verified`.

All forms admitted in persvati `proof_repl` sessions before certification.

## Certification

| run | host | roots | result |
| --- | --- | --- | --- |
| `run-20260925T235848Z-4125`, manifest `certify-20260925T235912Z-4066344` | hbox, 2 jobs, 300 s, w28 | `--affected-by` peer-invite, key-statements, peer-carriage, native-operator: 11 roots, 12 certified, 152 installed | passed, no failures; certify wall 27.3 s; slowest native-operator 6.6 s, peer-invite-tests 5.4 s, peer-invite 4.2 s, peer-carriage 4.2 s, key-statements 3.8 s; every book under 10 s |

## Native (hbox)

Tree: the r1 gate root `/tank/fn/gates/peering-compose-r1` (the lane at
4b710f03 plus the two fixes committed with this record: `FN_PULL_TEST_KILL`
registered in `+fnn-developer-selectors+`, and the key-statements carried
case given the `peer budget` PRF-099 requires). Script
`peering-compose-2026-09-25/image.sh` (w28, OpenSSL 3.5.8): acquire +
validate `roots=156 result=loaded`, developer image under `swarm-build`,
undefined lines 0; tests under `systemd-run --user -p MemoryMax=24G`.

| file | SHA-256 |
| --- | --- |
| `build/fn-host-developer` | `784ceb5c61ef4ed8c8b5bc5642fa98a6e098cbc5f71cdd32047f8ff61650ce4c` |
| `build/fn-host-developer.core` | `76d2ff381a30a830c6b1505d12ca65d8f0baf7a971821c8fbc282ccd2d9d87f4` |
| `native-build-developer.log` (left on hbox) | `29c09cd28bcae07baaeb77216b5b305c22eb48b0eed828c02b7f81e0e68e1cb1` |
| `native-peer-invite.log` (3 tests OK) | `0b4e4585de860f1b9f7d69dfc99b99607c3959d1c6ab1059500d415f74f1fcd8` |
| `native-key-statements.log` (3 tests OK) | `14264419f1ba6d6adc99d045d1d785b813609d83a128659fa16a5d35b2eeb8d1` |
| `native-peer-pull.log` (the three PRF-100 cases OK; the cut case errored on a harness bug, below) | `f28896e1d28fe984cf8e6a17cd5c400165d1b0c3aa82c07419668a74a352f2c0` |
| `native-pull-cuts.log` (the cut campaign after the harness fix, OK) | `66e0ed77a547244e31b6b696d6520cfc686541912d0442e206dbd91b4b09559e` |
| `native-ks-trace-old.log` (pre-packet image, the trace) | `6867f88832fa0d465d92a4947df0c0264fe8067f69e43bb977acdc69681f7a4f` |

The logs are copied beside this record.

- Invite/confirm: A confirms with `peer confirm ACC INV`; `peer list` at A
  shows `nodeB ... auth=principal <B>`; another invitation of A's presented
  with ACC is refused `another-invitation` and lists no nodeB; after the
  developer stop behind the one record, A2 already lists nodeB2 before the
  enrolment, the retry enrols once.
- Packet 7 on this image: `key-statement declined no-grant` at acceptance;
  grant added live; restart: `key-statement declined no-grant at-open`,
  history `gen 1 active`; second restart: the same line again, history
  unchanged. On the pre-packet image the same test (`FN_KS_REOPEN_EXPECT=acts`)
  shows `enrol-successor committed at-open` and gen 2 active.
- Packet 5 cut campaign (two articles at A, B pulls, SIGKILL at the cut,
  restart without the fault): every article stored exactly once at B at all
  six cuts. Begin record (append 1) cut before-write/after-write/after-fsync:
  the restarted round asks the one-day-back instant and fetches both
  articles (nothing had been fetched). Close record (append 2) cut
  before-write: the restarted round asks the dead round's instant again
  (`NEWNEWS fn.* 20260925 ...`), re-offers both ids to itself, both draw 435,
  zero ARTICLE commands: the bounded duplicate replay. after-write and
  after-fsync: the next round asks a later instant. after-write survived
  because a process kill keeps the page cache: this is not a power-loss
  observation.
- Failures classified: the first image run failed every pull case because
  the new selector was not registered (`fnn-developer-selector` faults on an
  unregistered name, so every FNPL append became uncertain): implementation,
  fixed; the key-statements carried case got 437 because PRF-099 (merged
  after PRF-098) requires a carrying budget and the test had none: stale
  test, repaired by adding `peer budget` (the contract, not the expectation);
  the cut test queried a killed node: harness, fixed.

## Packet 7 (PKT-173 a): declined key statements at reopen

- **Trace.** Pre-packet image (lane/peer-keys, tree 81a2c7b6, core
  `2cc00890...7a78`): enrol P, POST a succession with no `keys` grant ->
  240, log `key-statement declined no-grant`; `control grant P keys fn.keys`
  live; restart -> log `key-statement enrol-successor committed at-open`,
  history `gen 2 active, gen 1 retired`. The grant was added AFTER the
  statement; the restart turned an old decline into new authority. Log
  `native-ks-trace-old.log` SHA-256
  `6867f88832fa0d465d92a4947df0c0264fe8067f69e43bb977acdc69681f7a4f`.
- **Constraints.** §5.4: recovering a decision must not silently turn an old
  decline into new authority. C3 already binds a withdrawal's decision to
  the configuration in force at its cancel's txid (`fn-ctl-config-at`).
  Configuration records live in their own journal, so the statement stays
  the newest Store record across a live grant.
- **Default implemented.** The recorded disposition: the open decides the
  statement under the configuration in force at its own txid. The decline
  is not a new record: the statement record plus the durable configuration
  journal determine it, which is what "replayed as such" needs, and it costs
  no Store record family. Re-evaluation under today's grants is an explicit
  new statement.
- **Rejected alternative.** A durable decline record (a new Store event or
  configuration slot): a new record kind reopens replay dispatch in about 25
  books and a tenth configuration slot touches every `fn-cfg-value-make`;
  it would record what is already derivable. A `keys redecide MSGID` operator
  verb is the explicit re-evaluation if ember wants one; not built.
- **ember's switch.** `books/key-statements.lisp`
  `(defconst *fn-ks-reopen-policy* :recorded)`; `:current` restores the old
  behaviour (the native trace above).
- **Affected.** host/owner-host.lisp `fn-owner-key-statement-rows`,
  host/native/owner.lisp; theorems above; no format change.

## Packet 4 (PKT-173 b): refused signed evidence

- **Now.** The verdict names the class (`fn-pcb-admission-verdict`); a refused
  signed input produces no event and no charge (holds nothing); the transit
  log detail names the four refusal classes (PRF-099).
- **Question.** Hold `:unenrolled` / `:unsupported-profile` evidence as a
  charged durable record so a later enrolment can verify it?
- **Recommended default: do not hold (keep refusing).** Holding is a new
  record kind with its own admission charge (D27: charge before promise),
  retention (D03: kept until an authorized release, so every held refusal is
  a permanent capacity claim an unenrolled stranger can make), and a replay
  branch; and a held input must never turn into acceptance by itself (a
  later enrolment would have to re-offer it through the served path, i.e. a
  new decision). The peer that holds it can offer it again after the
  enrolment; that is the cheap path.
- **Alternative and cost.** A bounded, per-boundary charged hold of
  `:unenrolled` evidence (the D23 budget's shape: `peer budget` for held
  refusals): one Store family, a verdict token `:held` distinct from
  `:carried`, the replay branch, the budget theorem again. Estimated one lane.
- **Continues without it.** Everything; D23 carriage is unchanged.

## Packet 5 (PKT-173 c): pull cursor files vs a Store record family

- **Semantics (proved + native).** `fn-pull-journal-is-the-cursor-at-every-cut`
  and `fn-pull-recovery-asks-the-dead-rounds-newnews` (PRF-100) plus the
  native cut campaign `test_cursor_publication_cuts` (kill before write,
  after write, after fsync of the begin record and of the close record): see
  Native. No accepted work is skipped because the cursor moves only past a
  fully answered round and the close is journaled after the answers; the
  duplicate replay after any cut is at most the dead round's listing, each
  answered 435 by the node's own duplicate history (no state change).
- **Recommended default: keep the FNPL files.** Identity scope is per peer
  (the file name), write ordering is local (the file is fenced before the
  round continues), recovery is a prefix scan, and the model is PRF-100's.
  A cursor moves every round; a Store record family would put a record per
  round per peer into the Store's replay and retention (D03) forever, and the
  configuration history is bounded by `max-config-generations`.
- **Rejected alternative.** A Store record family: about 25 books (store
  events, replay, the invariants, records-concrete, checkpoint) and a
  permanent record per round; its only gain is one fsync domain instead of
  two, which no correctness property here needs (the cursor lagging the
  Store only costs duplicate 435s).
- **Continues without it.** Everything.

## Packet 8 (PKT-173 d, NOT implemented): pull over TLS with a principal binding

- **Now.** `fn-pull-plans` pulls only clear NNTP transports; the round is
  plaintext; no credential is ever sent (the pull machine has no AUTHINFO).
  So no credentials or private traffic go over a plain peer, but a pull is
  not protected and binds no principal.
- **Design (next lane).** Reuse the feed's proved session machine
  `fn-fc-step`/`fn-fc-after-tls` (books/feed-connection.lisp, PRF-047/051:
  `fn-fc-offers-and-credentials-wait-for-tls-and-login`) as the pull's
  preamble with `streamingp` nil: greeting -> STARTTLS -> 382 -> host TLS
  (`fnn-tls-open-client-context` + `fnn-tls-connect` against the peer's
  `server-name` and trust anchor) -> AUTHINFO USER/PASS from the peer's
  outbound auth profile -> 281 -> `:ready`; then the round begins in phase
  `:date` (a `fn-pull-begin-ready` whose only difference from
  `fn-pull-begin` is the phase, with a cursor-fields lemma so PRF-100's cut
  theorem carries over). `fn-pull-plans` admits `(:tls ...)` transports and
  carries the security and auth policy; a credential on `(:clear)` is refused
  by `fn-fc-begin-auth-or-mode` unless the profile allows clear (the
  loopback lab exception, which must be named in the spec and never claimed
  in general). The serving side's binding is the existing reader port:
  `[auth] protected_only`, the AUTHINFO principal. Native gate: two hbox
  nodes, A serving STARTTLS + auth, B pulling from A over TLS as B's
  principal, plus a wrong-principal and a clear-with-credential refusal.
- **Obstruction.** Budget: this lane spent its run on the confirm, packet 7
  and the certification/native gates.

## Not done, and why

- Packet 8 (above). The confirm's peer is clear-transport; TLS for it is
  `peer add` of the same name.
- The accepting side (`peer accept`) configures no peer: the invitation does
  not carry the inviter's address. Adding `Inviter-Host`/`Inviter-Port` body
  lines is a small follow-up.
- `fn-pcb-admission-verdict` is not yet what the transit log prints.
- No explicit re-evaluation verb for key statements.
