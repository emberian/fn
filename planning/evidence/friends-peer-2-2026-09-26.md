# friends-peer-2: a friend's node receives the cancel through its ordinary feed (PRF-163, 2026-09-26)

Dev lane `lane/friends-peer-2` from `dev` 8e27c115, brief
`build/coordinator/queue/w3-friends-peer-2.txt` (the continuation of
friends-peer; its record is `friends-peer-2026-09-26.md`). Ids: the launch
message named none; by WAVE-STATE's continuation rule this lane took
PRF-163, NNT-033, SCN-093 (the coordinator renumbers at merge if another
lane took them). Packets PKT-400 (retired), PKT-402 (retired), PKT-403
(narrowed), PKT-401 (design, below). Everything is `:logic` with verified
guards; no skip-proofs, defaxiom or trust tag.

## What a friend can now do

- **Receive a cancel through an ordinary feed.** A node that feeds its
  friend `local.*` now offers the author's signed cancel of a
  `local.general` article to that friend, and the friend withdraws the
  target (`430`). Before, the cancel was offered under `control.cancel`
  alone and never left the origin unless both wildmats named
  `control.cancel` (the workaround the runbook carried).
- **Make its keys with the tarball alone.** `fn operator CONFIG peer keygen
  KEYDIR` makes a new directory (0700; every file 0600, created O_EXCL)
  with an Ed25519 pair from the image's libsodium and an ML-DSA-65 pair
  from its OpenSSL 3.5, then runs `peer genesis` and prints the principal.
  No `openssl` 3.5 command is needed; an existing KEYDIR is refused. No key
  is ever an argument, an environment value or a URL.
- **Type `fn` and `fn --version`.** Bare `fn` is `fn operator - help` (the
  ACL2 usage text, exit 0); `fn --version` prints `fn REV40`, the source
  revision the installer (packaging/install-native.sh) or the freeze
  (tools/runbooks/hbox-image-build.sh) recorded beside the core, and exit 1
  with "records no source revision" for an image with none.
- **Add a peer to a running node.** `peer add` reaches a running owner
  through the control socket (the live-reconfiguration path,
  `fnn-owner-live-admin-serialized`); the native witness below replaces
  the accept/confirm records with both halves while both owners run and
  the feed flows without a restart.

## Assurance chain (PRF-163)

native entry `fnn-owner-take` / `fn-owner-submission-intent`
(host/owner-host.lisp) and the durable enqueue in `fn-owner-outcome`,
`fn-owner-control-outcome`, `fn-owner-transit-outcome` -> ACL2 subject
`fn-own-submission-targets` (books/owner.lisp; the intent calls
`fn-icar-submission-targets`, equal to it under `fn-icar-carryp`,
books/owner-intent-carried.lisp) -> `fn-own-feed-targets` over
`fn-own-sub-feed-groups` -> for a control article, the base groups plus
`fn-own-feed-control-groups-of` (the Newsgroups names and the filing group,
one parse) -> behavioural keystones below -> observed: the friend's `STAT`
of the target turns 430. The relation `fn-own-feed-tablep` is the one
books/owner-feed.lisp carries; this lane adds no relation and changes no
transition's shape, only the groups a submission is matched under.

## Theorems (books/owner-feed-subject.lisp)

- `fn-own-submission-offers-a-control-article-under-its-newsgroups-and-filing-group`
  (KEYSTONE): a submission in flight whose octets classify `:control`
  (`fn-own-feed-control-of`); a peer of the table with an outbound half
  whose wildmat matches a group of the article's Newsgroups
  (`fn-own-feed-groups-of`) or its filing group (`fn-ctl-filing-group` of
  the verb); its path-identity not in Path; not the origin; its queue
  without the Message-ID  =>  a member of `fn-own-submission-targets`.
- `fn-own-submission-target-of-a-control-article-is-in-its-scope`
  (KEYSTONE, the other direction): every target of a control article
  matches its base groups, its Newsgroups names or its filing group.
- `fn-own-sub-feed-groups-of-an-ordinary-article` (KEYSTONE): an article
  that does not classify `:control` keeps exactly its base groups.
- supporting: `fn-own-feed-control-of-is-the-filing-classification` (the
  classification equals `fn-ctl-classify-octets`, the one
  `fn-pa-filing-plan` files by, whenever the article parses),
  `fn-ctl-classify-control-has-a-verb`,
  `fn-own-feed-control-groups-of-names-newsgroups-and-filing-group`,
  `fn-own-sub-feed-groups-match-of-a-control-article`,
  `fn-own-feed-any-matchp-of-append`, `-of-true-list-fix`,
  `fn-own-feed-new-targets-keeps-an-unqueued-name`. All are disabled at the
  end of the book (a includer must not see the parser open).

The two new functions (`fn-own-feed-control-of`,
`fn-own-feed-control-groups-of`) are closed in books/owner.lisp and kept out
of `fn-own-vocabulary`: with them in it, owner-invariants'
`fn-own-connection-events-keep-store-bound-and-ledger` opened the article
grammar and ran past 60 s in the REPL; closed, the whole book replays in
18 s.

Cost: one article parse per evaluation of the groups, where transit already
paid one. Measured in the persvati REPL: ten evaluations over a 64 KiB
ordinary article, 0.00 s and 131,008 bytes. Not carried in the intent's
carry (`fn-icar-carry-of`); a later representation lane may.

Not proved: the pull side (a friend pulling with `local.*` asks NEWNEWS,
which serves by the filed group `control.cancel`; RFC 3977 section 7.4); the
receiving node's acceptance and honouring of the cancel (PRF-097, C3); that
a cancel's Newsgroups equals its target's (RFC 5537 section 5.3's SHOULD, the
author's).

## Teeth (tests/acl2/owner-tests.lisp, "PKT-400 (PRF-163)")

Every owner is reached through the real control submission and take over
`*own-after-post*` with a replayed configuration. Positive witnesses, each
with the keystone's complete antecedent asserted literal by literal
(`own-pkt400-antecedent`) and its conclusion:
A. a cancel filed `control.cancel` whose Newsgroups is `fn.letters`, peer
`out` (`fn.*`): targets `("out")`; a `must-fail` that the base groups alone
matched (the pre-PKT-400 scope); the carried intent names `("out")` too
(tests/acl2/owner-intent-carried-tests.lisp).
B. Newsgroups `local.general`, peer `ctl` asking for `control.cancel`:
targets `("ctl")`, through the filing group alone (a `must-fail` that the
Newsgroups matched). A transit cancel from `p` reaches `ctl` too.
Hypothesis removal, each owner reachable, the omitted literal false, the
others checked, the conclusion failing: the match (Newsgroups
`local.general` under `fn.*`), control (an ordinary article whose
Newsgroups matches, submitted under `local.general`: groups unchanged, no
target), the Path (`out.example!x`), the origin (the cancel arriving from
`out`), the queue (after the durable enqueue), nothing in flight. The table
entry and the outbound literal fail together for a name outside the table
(`q`); labelled structural. Developed form by form in a persvati
`proof_repl` session over owner, owner-invariants, owner-fault,
owner-feed-subject and owner-tests.

## Certification (hbox, w28 `acl2-literal-4g`, 2 jobs, 300 s)

| run | manifest | roots | result |
| --- | --- | --- | --- |
| `run-20260926T092325Z-00ed` (64698f30) | [certify-20260926T092407Z-1115236](manifests/certify-20260926T092407Z-1115236.json) | `--affected-by` owner, owner-feed-subject, peer-feed, peer-invite: 144 | 131 passed; owner-tests red (an assertion naming `fn-icar-submission-targets`, outside its includes; the REPL harness missed a translate error); 12 test books waiting on it |
| `run-20260926T093042Z-f78f` (37c6b311) | [certify-20260926T093114Z-1141563](manifests/certify-20260926T093114Z-1141563.json) | same plus native-operator: 19 afresh, 571 from the cache | passed; no book over 10 s |
| `run-20260926T093512Z-57fc` (ba61acd7) | [certify-20260926T093542Z-1162878](manifests/certify-20260926T093542Z-1162878.json) | native-operator (bare help), docs-operator-grammar-tests, owner: 7 afresh, 413 from the cache | passed; no book over 10 s |

Every row PRF-163's change moved off `certified` (40, their event books
owner.lisp and native-operator.lisp at new digests) cites these manifests
again; `ledger.py --write` leaves all of them certified.

## Native (hbox)

`tools/hbox_native.sh --images developer,production --label n2 ba61acd7
tests.test_native_friends_feed` (tree `git archive` of ba61acd7): certify,
validate, both images, then the module: **OK, 2 tests, no skip**. Images:

| file | SHA-256 |
| --- | --- |
| `fn-host` (production) | `e4bbb3d808a3780e962f92fb53dec8831edf6655e484ebcf0fde5df11b2afcf1` |
| `fn-host.core` | `feef3c698df1a64c66aad222fea47cd72fadfedc50d6accd620dd0ab59967098` |
| `fn-host-developer` | `bb9daa518b8923b89d2b82dc3f9949be667fc5da69fd67f81319e8e693a5cb88` |
| `fn-host-developer.core` | `bb16fc00c8d50a6fc7a59f825b4619f4ec338c963035cbcb1063bb5c5cb72edb` |
| `fn-ba61acd72080-linux-x86_64.tar.gz` (the release `tests/friends_tarball.sh` made) | `0af33c957a4de562f4953038433ca4822e18a65197c9924ede057d688a4e0e72` |

Then `tests/friends_tarball.sh TREE ba61acd7... /tank/fn/scratch/friends-peer-2/tarball-t2`
in the same tree: freeze, `packaging/release-tarball.sh`, the friend's
install step exactly as the runbook's section 1 (the sum, unpack,
`SHA256SUMS`), and the module with the friend F on the tarball's `bin/fn`
(no checkout, no `FN_NATIVE_HOST`) and the author A on the frozen developer
image: **OK, 2 tests**. What it observed (the log):

- `peer keygen` on both: 0; a second keygen of A's directory: 1 ("exists;
  keygen never overwrites keys"); directory 0700, the four key files 0600,
  `ed-secret.bin` 64 octets, `principal.bin` the printed principal.
- invite (A's address signed in), accept, confirm: 0; then a live `peer
  add` on each running owner: 0 (A feeds F `local.*`, F takes `local.*`
  from A; neither names `control.cancel`).
- A authors signed T in local.general: F `STAT` 223 after `accepted feed
  peer=f ... code=239`. A authors signed cancel C: A `430 withdrawn`, F
  `430 withdrawn` for T and `223` for C, pushed as `code=239` one second
  after T. The whole case: 4.3 s.
- bare `fn` on both images: exit 0, the command list; `fn --version` on the
  tarball's `bin/fn`: `fn ba61acd72080bcedfc599e1316f6c2ae5d30a050`; on the
  frozen image with no recorded revision: exit 1, "records no source
  revision".

A first run (t1) had the friend's `bin/fn` inherit `FN_NATIVE_HOST` and so
run the author's image (packaging/fn honours that variable first; harness
defect, fixed in the module: the friend's environment drops it). The n1
tree's first runs: skipped (hbox_native sets no `FN_NATIVE_HOST`; the module
now takes `build/fn-host-developer`), then `token.bin` 0644 (a public word
the invitation carries; the assertion was too strict), then `hybrid-enroll`
of A's principal after the confirm had taken generation 1 (moved before the
invite). None was an fn defect.

Logs beside this record ([SHA256SUMS](friends-peer-2-2026-09-26/SHA256SUMS)):

| file | SHA-256 |
| --- | --- |
| `friends-tarball-t2.log` (the tarball session) | `ace5ad5258e6aeb761d4da2c954221241d7df49b9af8d79f7329521d68fff0a0` |
| `native-n2-friends-feed.log` | `1b27f53d9c8fccfcf9b05910651ffaff4a8e012a4ef910af28790c0ecfbb6053` |
| `native-n2-run.log` | `a8d2579bd561f8693614dced3a2e57a82d18c4e67936f9d2ea4eb5e39eb4ae18` |
| `native-n2-SHA256SUMS` (images and build logs) | `08c5ed9425e9f9935f84c70fd89061a1b9843e31e94782d92ee79cd9665ed091` |
| `native-n1-friends-feed-r4.log` (the first green, n1 tree) | `15827c794fd48a1e06bae7e1fc4e37570ae2e5c3566f5ca5bae088bfb90e6c15` |

Not run: a negative control on the pre-PKT-400 image (the ACL2 must-fail
on the base groups is the control; friends-peer's session observed the
old behaviour on two machines).

## PKT-401: invitation-code accounts (design, not built)

The friends-peer design stands (its record, "PKT-401"), with three
refinements from reading the code this lane touched:

1. **The live login table is a configuration slot, not a host table.** The
   configuration value already carries principals' credentials only
   through `auth.toml` read at start; the prerequisite is a tenth
   configuration slot `accounts` whose rows are `(DIGEST ISSUER EXPIRY 0)`
   pending and `(DIGEST LOGIN PRINCIPAL VERIFIER 1)` redeemed, published by
   `fnn-owner-live-reconfigure-locked` exactly as `peer add` is, and read by
   the reader session's credential snapshot at login. The code itself is
   never stored: the row is keyed on SHA-256 of it.
2. **Once-only across a crash** is PRF-097's pattern
   (`fn-pinv-consumed-stays-consumed`): the redeem plan is a pure function
   of the configuration value and the request; a crash after the record is
   published resumes as "already redeemed by this login" (idempotent for
   the same login, refused for another), never a second row. The theorem
   to prove: over `fn-cfg-apply`, a redeemed row stays redeemed and a
   second redeem plan of the same digest is `:refused` unless it names the
   same login and verifier.
3. **The wire verb** is fn's extension `XREDEEM CODE NAME` (381 for the
   password, 281 bound, 482 refused), only after STARTTLS on a protected
   listener; RFC 4643 section 2.3's AUTHINFO is not overloaded.

Cost: the slot touches every `fn-cfg-value-make` and the configuration
codec (a format bump with an upgrade), the reader's credential snapshot and
books/nntp.lisp's dispatch. It is a lane of its own; nothing here depends
on it.

## Packets

- **PKT-400 retired**: PRF-163 and the native session above.
- **PKT-402 retired**: `peer keygen`.
- **PKT-403 narrowed** to one item, the mission's TLS pair (X.509
  creation through the image's OpenSSL); bare `fn`, `fn --version` and the
  live `peer add` are done (live `peer add` was already the admin path's;
  this lane observed it on two running owners and the runbook no longer
  stops the node).
- **PKT-401 open**: invitation-code accounts, design above.

## Not done, and why

- PKT-403's TLS pair from `mission`: not built (it needs X.509 creation
  through the image's OpenSSL: about fifteen more FFI entry points). The
  runbook keeps the one `openssl req` command.
- PKT-401: design above.
- The two-machine form of the session: `tests/friends_tarball.sh` scripts the
  install step and runs the friend from the tarball's `bin/fn` on the same
  box (see Native); a second machine adds the LAN, not a decision.
- The pull side of a cancel (NEWNEWS by filed group), above.
