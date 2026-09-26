# friends-accounts (PKT-401), 2026-09-26

Lane friends-accounts, launched by deputy 3 from dev 17ff24aa (dev 474fa50a
merged at d5fc8912). Ids PRF-164, NNT-034, SCN-094, PKT-439, PKT-440.

## What a friend can do now, and what not yet

Built and proved: the configuration can hold invitation-code accounts, the
redeem decision is ACL2's and redeems a code at most once across a crash, and
a connection's credential table includes every redeemed account, so a friend
whose code was redeemed logs in with AUTHINFO as that account without an
auth.toml edit or a restart. Not built: the wire verb `XREDEEM` and its
publication, the operator's `account invite`/`account list`, and the native
session (PKT-439). Until PKT-439 lands no user can make a redeemed row, so the
user-visible result is not reached; nothing here changes a served reply today
(the snapshot of a configuration without redeemed rows is auth.toml's table,
by definition of `fn-auth-config-with-accounts`).

## The codec decision (no format bump; PKT-440 for the rollback)

The configuration is persisted as its change records (books/config.lisp
`fn-cfg-encode` of a record's deltas), never as a value, so the tenth slot
needs no value codec: a history that never carried an account delta replays
to a value whose `accounts` is nil, and every one of the fourteen old delta
kinds encodes byte-identically. Witness: tests/acl2/accounts-tests.lisp asserts
the encoding of one record carrying one delta of each old kind equals the
279-octet literal computed at 17ff24aa, and that applying those deltas leaves
the slot empty. `*fn-cfg-schema-version*` stays 0. Consequence (PKT-440): an
image before this change (bbf52159, the deployed node) reading a store whose
configuration log holds a code-15 or code-16 delta refuses the record at
decode (`:delta-kind`) and the node does not open; a store that never issued a
code is unaffected. Rollback across the first `account invite` therefore
needs the records removed or a newer image.

## Proved (PRF-164)

Subject and host lines:
- `fn-cfg-apply` / `fn-cfg-delta-reason` / `fn-config-replay-loop`
  (books/config.lisp): the records host/owner-host.lisp
  `fn-owner-reconfigure-complete` publishes through `fn-ocl-publish` and the
  owner replays at open.
- `fn-acct-redeem-plan` (books/accounts.lisp): the plan the XREDEEM arm will
  call (PKT-439; no host line yet).
- `fn-auth-config-with-accounts` (books/nntp-auth.lisp): called by
  books/owner-config.lisp `fn-ocfg-open` / `fn-ocfg-open-peer`, host-called by
  host/owner-host.lisp `fn-owner-open` and `fn-owner-open-peer`.

Keystones (books/accounts.lisp, books/nntp-auth.lisp):
- `fn-acct-redeemed-row-stays-across-replay`: over `fn-config-replay-loop`, a
  redeemed row is the same row after every later acceptable record (so the
  login and verifier bound to a code never change). Per delta list:
  `fn-acct-redeemed-row-stays` (hypothesis `fn-cfg-admissiblep`).
- `fn-acct-redeemed-refuses-another-redeem`: a redeem of a redeemed digest is
  refused unless it carries exactly the redeemed row (same login and
  verifier).
- `fn-acct-redeem-plan-is-admitted-and-redeems`: a :redeem plan's delta is
  admitted at every generation and ledger, and after it the code's row is
  (DIGEST LOGIN VERIFIER-TEXT 1) with the `fn-authsec-enrol` verifier.
- `fn-acct-redeem-plan-after-its-redeem-is-already-redeemed`: the crash cut
  after `fn-ocl-publish`'s root barrier and before the reply: the same code,
  login and password plan `(:already-redeemed)` under any later stamp, salt
  and snapshot, so a retry answers 281 and binds nothing new.
- `fn-acct-redeem-plan-refuses-another-login`,
  `fn-acct-redeem-plan-of-an-unknown-code-stages-nothing`.
- `fn-acct-text-verifier-of-verifier-text`: the representation boundary (the
  row keeps the verifier as 96 hex characters; the text is the verifier).
- `fn-auth-config-with-accounts-finds-the-redeemed-credential`,
  `-keeps-the-operators-credential`, `-is-a-config`,
  `fn-auth-account-creds-find-the-row`: one credential table, auth.toml first;
  composed with `fn-auth-step-principal-login-binds-exactly-the-unique-match`
  (cited) a redeemed account's 281 installs the login's local principal
  `fn-acct-local-principal`, which books/native-auth-admin.lisp now also uses
  for a login enrolled without --principal (one function).

Assumptions: that a code the operator did not print finds no row is the
crypto seam's preimage resistance (A-CRYPTO, books/crypto-seam.lisp), not a
theorem here. Expiry is policy against the record's clock observation: a
stamp without a wall clock, or whose error interval reaches the expiry,
refuses (fail closed).

Teeth (tests/acl2/accounts-tests.lisp): reachable witnesses from the empty
value through invite, redeem, resume and replay from the initial
configuration; hypothesis removals: a refused plan's "delta" is not admitted;
an expired plan stages nothing so the next plan is not a resume; while
pending another login redeems; the same login with its password resumes; the
identical redeem is admitted; a pending row is changed by a redeem; another
kind naming the digest is admitted; an inadmissible re-invite overwrites the
row under `fn-cfg-apply`; the replay faults on it.

Assurance chain for the slice: native entry (host/owner-host.lisp
`fn-owner-open`) -> executed ACL2 `fn-ocfg-open` -> `fn-auth-config-with-accounts`
over the pinned configuration's `fn-cfg-accounts` -> the snapshot relation
(`-finds-the-redeemed-credential`) -> the binding keystone (cited) -> observed
result: none yet (no redeemed row can be made until PKT-439).

## Runs

- REPL (persvati /home/ember/fn-gates/friends-accounts-repl): books/config 243
  forms, books/config-invariants 46, books/accounts 47, tests/acl2/accounts-tests
  75, all admitted.
- Farm r1: see "Manifests" below.

## Manifests

(filled at harvest)

## Packets

- PKT-439 (what remains of PKT-401; narrows it). (1) The wire verb in
  books/nntp-auth.lisp `fn-auth-step`: `XREDEEM CODE NAME` -> 381 and a session
  state awaiting the password; 483 before TLS when the listener is
  protected-only (the AUTHINFO rule, fn-auth-authinfo's second arm); 502 when
  authenticated; `fn-auth-restricted-keywordp` untouched (XREDEEM is not a
  reader command). The password line calls `fn-acct-redeem-plan` (TAKENP from
  `fn-auth-find-cred` over the session's snapshot) and answers nothing yet on
  :redeem: it emits a served effect `(:account-redeem D)` (the POST
  `:submit` pattern, books/served.lisp `fn-served-submission`), answers 281 on
  :already-redeemed and 482 on :refused with the reason class for the log.
  (2) The host: host/native/owner.lisp after `fn-owner-chunk` selects the
  effect and runs `fnn-owner-live-reconfigure-locked` with a stage that
  applies D (the host/native/peer-invite.lisp:111 shape); an ACL2 completion
  event `(:account-outcome id :accepted|:refused)` decides the 281/482 line so
  281 follows only the durable publication. The salt: the same /dev/urandom
  read `fnn-native-auth-admin-csprng-salt` performs, passed with the chunk.
  (3) `operator CONFIG account invite [--expires SECONDS]`: the host reads 16
  octets from the CSPRNG, prints the code once (base32 or hex; stdout only),
  ACL2 builds `fn-cfg-account-invite` from `fn-acct-code-digest-text` with the
  expiry from the invite's clock observation, staged live through
  `fnn-owner-live-reconfigure-locked` or offline into the configuration as
  `peer add` does; `account list` prints logins and state only. Grammar in
  books/native-operator.lisp and docs/operator.md (tools/docs_check.py
  --write). (4) tests/test_native_friends_accounts.py (SCN-094's steps; the
  friend from tests/friends_tarball.sh) and docs/peering-with-a-friend.md
  section 2's account step. (5) An admission limit for the slot's size (the
  profile's max-credentials over auth.toml plus redeemed rows; D27: a profile
  limit, not a code ceiling).
- PKT-440 (FOR EMBER, rollback): see "The codec decision". Default: accept
  (fail closed on an old image; the operator rolls back only a store that
  never issued a code). Rejected alternative: carrying accounts in a second
  file or a schema-1 record family so old images skip it -- costs a second
  persistence path and its crash model for a rollback case. Affected:
  books/config.lisp's codec only; nothing waits on it.
