# friends-peer: a friend's node from the release tarball, peered both ways over TLS (PRF-160, 2026-09-26)

Dev lane `lane/friends-peer` from `dev` 0d211647, brief
`build/coordinator/queue/w3-friends-peer.txt` (mandate §11, §15 "Protected
ordinary use"). Ids: NNT-030, PRF-160, SCN-090, PKT-400 to PKT-403.
Commits: 8fb3768e (the accept configures the inviter; the release tarball),
and the commit carrying this record (help texts, docs, registry). Everything
is `:logic` with verified guards; no skip-proofs, defaxiom or trust tag.

## What now works (user-visible)

- **A release tarball.** `packaging/release-tarball.sh FROZEN_DIR REV OUT`
  makes `fn-REV12-linux-x86_64.tar.gz`: the install tree of one frozen image
  with its SBCL runtime, OpenSSL 3.5 and libsodium beside it, the operator
  documents and `SHA256SUMS`. Before this lane there was no downloadable
  artifact at all: every node was installed from a gate tree on hbox.
- **A node on a second real machine from the tarball alone.** persvati
  (Ubuntu 25.10, glibc 2.42; the image was built on hbox, Ubuntu 24.10, glibc
  2.40) ran `fn-8fb3768e8439` unpacked under `/home/ember/fn-node-friends`
  with no fn checkout: sums verified, mission, TLS pair, init, path
  identity, login, node keys, `run` under `systemd-run --user -p
  MemoryMax=8G`. The laptop's `tools/node_probe.py` against it over the LAN:
  every assertion held, TLSv1.3 (on bbf52159, the first walk).
- **One invitation each way configures both peers.** `peer invite ... MY-HOST
  MY-PORT` signs the inviter's address into the invitation; the friend's
  `peer accept` configured the inviter (`hbox-scratch.friends.fn.invalid
  ... address=192.168.50.39 port=11991 ... auth=principal:70fc9ddc...`) in
  one record before enrolling it; the inviter's `peer confirm` configured
  the friend (`persvati ... auth=principal:60779285...`).
- **Articles flow both ways over STARTTLS, each node logging in as the
  other's principal.** After each side's `peer add` of the same name with
  `starttls`, the other's certificate as the only anchor, a login bound to
  the other's principal and `peer pull NAME 20`: pushes (`accepted feed ...
  code=239`, TAKETHIS) and pulls (`pull ... round=done cursor=advanced
  transport=tls`) in both directions; a post on either node is read on the
  other.
- **Identity across the machines.** Seven articles: each Message-ID on both
  nodes exactly once, the same authored-source digest on both (the served
  article minus Path, Xref, Injection-Date, Injection-Info, FN-Authorship,
  specs/identity.md step 3), local numbers each node's own
  ([identity-after-restart.txt](friends-peer-2026-09-26/identity-after-restart.txt)).
- **Clock skew and restart.** persvati's owner ran with its clock +10 min
  (libfaketime `FAKETIME=+10m` preloaded into the owner process only: the
  box is shared with the farm, so its system clock was not moved; the
  node's `DATE` answered `111 20260926073935` at 07:29:35 UTC). Each owner
  was stopped (exit 0) while the other posted, and restarted. No article was
  skipped or stored twice; duplicates offered by the push after the pull had
  fetched them were answered `438` (and `435`/`235` on the pull's own
  re-offer). The pull cursor is kept in the remote's clock (the round asks
  `DATE` first), so the skew does not move it.
- **A withdrawal on one side is visible on the other**, once the peers'
  wildmats name `control.cancel`: persvati authored a signed article and its
  signed cancel through its own owner (`hybrid-sign`, `hybrid-author`, the
  node principal enrolled at persvati); hbox verified the article under the
  keyring generation the confirm enrolled (`HDR :fn-verified` = `0 verified
  60779285... keyring 1`) and answered `430 withdrawn` after the cancel
  arrived. With `local.*` alone the first cancel never left persvati and
  the target stayed visible on hbox (PKT-400).

## Assurance chain (PRF-160)

native entry `fnn-pinv-control-handle` (hybrid control request 10) ->
`fnn-pinv-owner-accept` (host/native/peer-invite.lisp) -> ACL2 subject
`fn-pinv-accept-record-plan` through `fn-pinv-host-accept-record-plan`
(host/peer-invite-host.lisp), over the live peers table
(`fn-pinv-host-owner-peers`) and keyring (`fn-owner-hybrid-snapshots`) ->
`(:configure DELTAS)` -> `fnn-owner-live-reconfigure-locked` ->
`fn-owner-reconfigure-deltas` stages ONE record -> on durable completion
`fn-cfg-apply-record` runs the fold `fn-cfg-apply` -> behavioural keystones
below -> then `fn-pinv-accept-step` (PRF-097's enrolment, unchanged) ->
observed: `peer list` at the invitee, the cut test. The maintained relation
("the peers table IS the replayed configuration") is the configuration
replay's, as for PRF-124; this lane adds no relation. The invitation's words
come from `fnn-pinv-invite` -> `fn-pinv-host-invitation-source` ->
`fn-pinv-invitation-source` (two new body lines, signed).

## Theorems (books/peer-invite.lisp)

- `fn-pinv-accept-record-configures-the-verified-inviter` (KEYSTONE): a
  `(:configure DELTAS)` plan has the invitation bound
  (`fn-pinv-bound-document-p`: its carrier verifies under the key set its
  body names, the inviter being their genesis principal), the inviter not
  enrolled with those keys, an Inviter-Port that is a port, the peer
  `fn-pinv-inviter-peer` well-formed (`fn-cfg-peerp`) with auth
  `(:principal INVITER-HEX)` of the verified carrier's principal, no row of
  the peers table under its name, and DELTAS = `(fn-cfg-set-peer-delta
  peer)`.
- `fn-pinv-accept-record-fold-configures-the-inviter` (KEYSTONE, over the
  fold the host calls): after `fn-cfg-apply V GEN STAMP DELTAS` the peers
  table holds exactly the peer's rows under its name, and the accept record
  plan over the folded table is the accept plan, which is `:enrol` -- the
  crash point after the record resumes as the enrolment, never a second
  record.
- supporting: `fn-pinv-accept-plan-enrols-only-a-bound-invitation`,
  `fn-pinv-accept-plan-never-configures`, `fn-pinv-inviter-peer-auth`.

Not proved: the TLS words and the outbound half (the operator's `peer add`
of the same name replaces the record); that the signed address is
reachable; the signature primitives (A-CRYPTO).

## Teeth (tests/acl2/peer-invite-tests.lisp, "PRF-160")

Reachable witness: B's accept of A's addressed invitation is `:configure`;
every conjunct asserted, and the peer is exactly `a.example a.example
(:nntp 1 "192.0.2.7" 11191 (:clear)) ("fn.*" max 16) nil (:principal A)`.
Fold witness from the empty value: the rows, `peer-find` answers the peer,
the resumed plan is the accept plan, the resumed step enrols A, the record
is admissible; a must-fail that the rows were there before the fold.
Hypothesis removal, each with a `must-fail` of the guarded conjunct: an
invitation naming `-` (enrol only, `fn-pinv-inviter-addressedp` fails); A
already enrolled (`already-enrolled`); the name taken by another record
(`peer-name-taken`); a tampered invitation (`unverified`, the binding
fails). Every must-fail's inner expression evaluated to NIL in a persvati
`proof_repl` session over the uncertified book before the farm run; all 126
book forms and 151 test forms were admitted there first.

## Certification (hbox, w28 `acl2-literal-4g`, 2 jobs, 300 s)

| run | manifest | roots | result |
| --- | --- | --- | --- |
| `run-20260926T071806Z-393e` (tree 8fb3768e) | [certify-20260926T071830Z-739340](manifests/certify-20260926T071830Z-739340.json) | `--affected-by` peer-invite, native-operator: 8 certified, 149 installed | passed; peer-invite 2.5 s, peer-invite-tests 4.5 s, native-operator 8.3 s |
| `run-20260926T073924Z-d074` (help texts) | [certify-20260926T073947Z-853113](manifests/certify-20260926T073947Z-853113.json) | `--affected-by` native-operator: 6 | passed; native-operator 7.4 s |

Every book under 10 s.

## Native (hbox and persvati)

Images from the r1 gate tree (`/tank/fn/gates/friends-peer-r1`, 8fb3768e)
by `tools/runbooks/hbox-image-build.sh`: validate default `roots=166
result=loaded`, dtn 151; frozen under `build/images/8fb3768e.../`.

| file | SHA-256 |
| --- | --- |
| `fn-host` | `432622d29a28d59455e01f3e5b426036c5862db21d5f7d1205a9304ab11e3505` |
| `fn-host.core` | `7d58345ef1e7581e77d199b8ad7a2e7a3b2a4b622724dbb756ac9507523c70d4` |
| `fn-host-developer` | `e4eeefd290450e7497dade96e2c4089e0caacfa88f72c737f51a92b2f3b2ba18` |
| `fn-host-developer.core` | `474ad73cfe2cf4260a6ece6fc3afcdab485a4b69539d701e5f0ae702daf14ac7` |
| `fn-8fb3768e8439-linux-x86_64.tar.gz` (the release) | `8bbaa4f71abb6fa0433008832c5795b9ffb617ab92e86a75244a7cc4cc5655cd` |
| `fn-bbf52159dcab-linux-x86_64.tar.gz` (first walk, the deployed image) | `db532e40a049cdcd0acc359544e5fd8959ac3e7f9f349e5942f95286bf24370f` |

`tests.test_native_peer_invite` on the developer image under
`systemd-run --user -p MemoryMax=24G`: 4 tests OK in 20.0 s, the new
`test_accept_configures_the_inviter_and_resumes_after_a_cut` among them
(the accept under `FN_PEER_TEST_STOP_AFTER_CONFIGURE` exits 3 and the owner
137; after the restart `peer list` already shows `a3.example ...
auth=principal:41c672f5...`, no enrolment in the key history; the retry
enrols once and leaves `peer list` byte-identical; a third accept is
`already-enrolled`). The two-machine session ran the production image from
the tarball. Logs beside this record,
[SHA256SUMS](friends-peer-2026-09-26/SHA256SUMS):

| file | SHA-256 |
| --- | --- |
| `native-peer-invite.log` | `f8961b4c2c6caf75ed9d395058a4997717957db66558a6961f9565a2b4e696f4` |
| `persvati-fn.log` (the friend's owner log, whole session) | `e0acd5c393ec4f5f9543eeb84bd4510166f10c351a4a12dd2c5fdaafd570e85c` |
| `hbox-scratch-fn.log` | `cdd9408d8234c2795500b522e949905dfb89c2eea0c3b9d1fa264cfb04cca31b` |
| `persvati-walk.log` / `hbox-scratch-walk.log` | `c59a4fa6...039d` / `3531ac14...a467` |
| `identity-after-restart.json` | `1a5427a287876846e601e728a23988eee66c3fc4a9fa52ab8994980887f2e4c9` |
| `image-build-r1.log` | `c2afa0b5b10ca4ca61c4d83c6f40d9125738e0c356b0535f072559d340646acc` |

The walk script is the runbook's section 1; the identity table is
`friends-peer-2026-09-26/identity_table.py` (a test client: it decides
nothing for the node).

## The stranger's walk: findings

| # | step | finding | class | now |
| --- | --- | --- | --- | --- |
| 1 | download | no release artifact existed; nodes were installed from gate trees on hbox | packaging | `packaging/release-tarball.sh`; the frozen directory already carried runtime, OpenSSL 3.5.8 and libsodium, so the tarball needs no system library |
| 2 | read the docs | operator.md's "Install", "Initialize", "Require a login" describe the Python service (`fn --config ... init --store`), which the tarball's `bin/fn` refuses | docs | a pointer at the top and "From the release tarball" |
| 3 | TLS | `mission` writes TLS paths and makes no pair; no page said how to make one | docs | the command, with the subjectAltName the peer verifies |
| 4 | keys | `peer genesis` reads a key directory whose format no page gave | docs | the openssl commands; a verb is PKT-402 |
| 5 | login | `principal set-password` with one piped line: `password input ended before a value`, exit 1 | docs | help and pages say "twice, or two lines of stdin" |
| 6 | help | `help peer` showed the old 10-word `peer add` (no `principal`, profile, `starttls`), no `peer pull`/`budget`; `help policy` no `posting-policy`; `help principal` no `bind`/`unbind` | implementation | books/native-operator.lisp help texts |
| 7 | accept | the invitee got no peer record for the inviter | implementation | PRF-160 |
| 8 | withdrawal | a cancel whose Newsgroups is `local.general` is not fed under `local.*` | implementation | PKT-400 (documented workaround) |
| 9 | `fn` | bare `fn` prints `missing arguments`; `fn --version` is `unknown verb` (5) | implementation | PKT-403 |

Other observations, classified: persvati's first pull round failed
`at=preamble` because hbox's owner was stopped at that instant
(environment; the next round was `done`); hbox accepted the friend's
article whose `Date` was 10 minutes in its future (RFC 5537 §3.4 leaves a
future-date check to local policy; fn has none).

## Not done, and why

- **Task 3, accounts for strangers** (PKT-401): not built. Credentials live
  in `auth.toml`, written offline by `principal set-password` and loaded
  once at start; a code redeemed over the reader port needs a live
  credential path the owner does not have. Design below.
- The two-machine session is a hand run, not a module: its commands are the
  runbook and its logs are here; no harness replays it.
- `peer add` is offline: turning the accept/confirm's clear record into a
  TLS one stops each node once.

## Packets

**PKT-400 (implementation, RFC 5537 §5.3 and §3.5): feed a cancel by its
Newsgroups.** Trace: persvati's `<friends-c1@persvati.invalid>`
(`Newsgroups: local.general`, `Control: cancel <friends-t1@...>`) was
accepted `path=control` and withdrew the target locally, and was never
offered to hbox under wildmats `local.*` (neither by push nor by pull);
hbox kept serving the target. With `local.*,control.cancel` the second
pair travelled and both nodes answered `430 withdrawn`. Constraint: a
relaying agent selects by the article's Newsgroups; fn selects by the group
it filed the article under (`control.cancel`). Default: the feed selection
(books/owner-feed, the queueing decision) matches a control article's
wildmat against its Newsgroups as well as its filed group. Rejected: the
doc workaround as the fix (every operator must know it; a peer of an INN
node is not told). Affected: feed selection and its invariants; pull's
NEWNEWS wildmat. Continues without it: everything, with the wildmat
workaround in docs/peering-with-a-friend.md.

**PKT-401 (task 3, design): account invitation codes.** `operator CONFIG
account invite [--posting] [--expires DAYS]` draws a 128-bit code from the
CSPRNG and publishes a configuration record (a tenth slot `accounts`, rows
keyed on the code's digest, never the code: `(DIGEST ISSUER EXPIRY 0)`
pending, `(DIGEST LOGIN PRINCIPAL 1)` redeemed), printing the code once.
Redemption over the reader port is fn's extension, not an RFC 3977/4643
verb: after STARTTLS, `AUTHINFO USER NAME` then `AUTHINFO PASS
code:CODE:NEWPASSWORD` would overload RFC 4643 §2.3; a separate `XREDEEM
CODE NAME` (continuation 381 for the password, 281 bound, 482 refused) is
cleaner and is the default. ACL2 decides: the code's digest names a pending
row, the name is free, the verifier is derived (books/auth-secret.lisp);
the owner publishes ONE record consuming the row and adding the credential
to a live credential table (today the credential file is loaded once; the
live table is the prerequisite). Theorem: the fold leaves the row redeemed
by exactly one (login, principal) and a second redemption of the same code
is refused (the invitations slot's `fn-pinv-consumed-stays-consumed`
shape). Cost: a config slot (every `fn-cfg-value-make`), the live
credential table (host/native/auth.lisp and the reader session's
credential snapshot), one NNTP verb in books/nntp.lisp's dispatch. About
two lanes.

**PKT-402: `peer keygen KEYDIR`.** The tarball carries OpenSSL 3.5's
libraries but no `openssl` command; a stranger on a distribution with
OpenSSL 3.0 cannot make an ML-DSA-65 key. A host verb drawing both pairs
through the image's own libcrypto/libsodium and writing the directory
`peer genesis` reads. No ACL2 decision beyond the layout.

**PKT-403: the remaining stranger frictions.** `mission` could make the TLS
pair it names (a self-signed pair for the listener address); bare `fn`
should print the operator's help, and `fn --version` the source revision
the tarball's `share/fn/source-revision` holds; a live `peer add`
replacement through the owner, as `group create` has.
