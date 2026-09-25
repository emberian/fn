# spike/peering: peering with strangers (2026-09-25)

(Copied to dev from spike/mega by the night deputy because dev books and briefs cite it; the spike is the specification, never merged into dev. Its logs and scripts stay on spike/mega.)

Spike lane under D28 on `spike/peering` from `spike/mega` (`0e2173ab`). It
builds invite/accept enrollment, key succession, revocation with a new
verdict token, NEWNEWS pull feeds, and a stranger scenario with INN. It also
adds the two review items the coordinator assigned (gpt-6 direction review,
2026-09-24): an opaque-carriage budget per boundary, and three distinct
refusal classes for signed articles that are not verified. This is spike
evidence. It is not a dev claim. Every host-side decision is marked
`;; SPIKE` / `SPIKE:` in the source and listed below.

## Result

The native three-node lab on hbox passed 60 of 60 checks: two fn nodes on
this branch's image and INN 2.7.4.

| item | value |
| --- | --- |
| lab driver | `tools/spike_peering_lab.py` (sha256 `8c0a58fb9e18cb9472113a756c0343e22f1ee7f038ff5abe44e355f2490b5b1c`), run under `systemd-run --user --scope -p MemoryMax=24G` |
| image | production profile, `build/fn-host` sha256 `6df6a17e0308dc69bf69163885e21c9937616351a3faebab91ece24d20ee7c89`, core `3accdea1fe8f0b051b582a44358467dd2ef9c63e7878fb5f6736735e7f1b8fa1`, built at books `a1ba0fda` with `FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8` and `/tank/fn/toolchains/w28/acl2-literal-4g` |
| scratch | `/tank/fn/scratch/spike-peering/lab-final/` |
| lab log | `lab-final.log` sha256 `6d5cfbe2a45ff6f44dd5c0c8411fd83cd63f63132d66642f57dc117d321bcf5a` |
| node A log | `lab-final/A/fn.log` sha256 `f2de2b499634065e003890b3f46adc25368323d50bda48ebc3eb9fdb203557d1` |
| node B log | `lab-final/B/fn.log` sha256 `acf175e23975dac8cca1f42f1c62ca67da29ca27aa804da7dcc21fe255606c73` |
| summary | `lab-final/summary.json` sha256 `00983e80039c5be1b51cc1ea31b79fc858591183e8aaf061c27b659a8231fbe0` (60 passed, 0 failed) |
| peering tool | `tools/fn_peering.py` sha256 `8f37f100335068c23b51e91b0bd0471adc23c97492d855e552a120c18758a174` |

Ten earlier runs (`lab-1` to `lab-11`) found the defects fixed in the
commits: the 16-word admin argv bound, INN's missing `control.cancel`, the
`N` in nnrpd's access string, nnrpd's load limit, and an nnrpd that forked
away from its PID.

### Certification

| run | host | books | result |
| --- | --- | --- | --- |
| `run-20260925T075338Z-6807` at `ed4ee5ad` | persvati, 2 jobs, 300 s | image roots and four test books; 186 certified, 140 from cache | exit 0 |
| `run-20260925T080333Z-24a7` at `29c8cf10` | persvati | 6 certified (peer-authored-accept, native-admin-peer, native-admin, native-operator, two test books) | exit 0 |
| `run-20260925T081633Z-dffd` at `a1ba0fda` | persvati | 17 certified (native-admin-shape and dependents, native-admin-tests, native-operator-tests) | exit 0 |
| image closure at `a1ba0fda` | hbox, `swarm-build`, w28, 8 jobs, incremental from `/tank/fn/certcache` | 194 certified, evidence `certify-20260925T081720Z-2867044` | exit 0 |

hbox certified the closure again because its toolchain is a different SBCL
and ACL2 install from persvati's. The spike added no `skip-proofs` and no
`:program` book code. Every new ACL2 definition is guard-verified. Every new
theorem was proved.

## What works (each row is a lab check)

**Invite, accept, confirm.** `fn peer invite B` (A) writes an article signed
by `hybrid-sign-carrier` with the inviter's node principal. The invitation
carries that principal's Ed25519 and ML-DSA-65 keys, the offered groups, a
nonce, the carried authors and their keys. `fn peer accept FILE` (B) checks
it with `hybrid-verify-source` against the ML key it claims. It requires the
claimed principal and Ed25519 key to be the verified ones. It then enrols the
inviter and the author the operator named (`--enrol-author`), adds peer A
through the ACL2-planned `operator peer add` (live over the control socket,
generation bumped) with `carries-principal` rows and a budget, and writes a
signed acceptance. The acceptance names the nonce, the inviter's principal
and the invitation's ACL2 authored-source identity. `fn peer confirm FILE`
(A) checks the acceptance the same way and requires all three bindings. It
then enrols B and adds peer B. B had no reachable address, so A's record has
no outbound feed. The following were refused: a tampered invitation
(`unverified SIGNATURE`), a replayed invitation, and a second confirm.

**Pull feed (RFC 3977 §7.4).** B is behind NAT and pulls from A with `DATE`,
`NEWNEWS fn.* …`, `ARTICLE` and `IHAVE`. It injects from the address its peer
record for A names (127.0.0.2), so B treats the articles as A's transit. The
cursor advances only when every listed article drew 235, 435 or 437. A 436
or a broken connection keeps the article pending. A also pulls from INN's
nnrpd the same way.

**Verdicts at B.** B returned `verified alice` for an introduced author,
`carried carol` for a carried author, and `verified nodeA keyring 2` for the
inviter's node key.

**Succession.** `fn keys succession --old --new` produces a statement in
`fn.keys` signed by the old key. It holds a proof of possession: a second
carrier signed by the new key over the principal, both Ed25519 keys and the
statement's Message-ID. `fn keys process` acts only when the node's own
`HDR :fn-verified` says `verified P` for the statement's principal. A carried
statement is refused, with the log reason "carrying is not authority".

- A and B each enrolled nodeA's successor key. After that, A refused a post
  by the superseded key.
- B returned `verified nodeA keyring 4` for the successor key. It still
  returned `verified … keyring 2` for the old-key article.
- B declined carol's succession because its verdict was `carried`.

**Revocation.** alice's self-signed revocation was pulled by B. A and B each
revoked alice.

- Article R1 was signed before the revocation. It was delivered by transit
  after the revocation (by hand IHAVE, as B to A and as A to B). A stored it
  as `revoked alice keyring 7` and B as `revoked … keyring 5`.
- A served POST of R1 was refused with 441 `local-enrollment`.
- X1, accepted before the revocation, stays `verified` on both nodes.
- `fn_verify` returned exit 0 on X1. On R1 it returned exit 1, "revoked: …
  the signature checks under the pinned keys".

**Opaque-carriage budget.** B's boundary to A carries carol with a count of
3. y1, y2 and carol's succession statement used the three. The fourth
carried article (y3) was refused with 437, `detail=carried-count-exhausted`.

**Three refusal classes.** An article from an unenrolled, unlisted stranger
was refused with 437 `detail=no-local-binding`. A tampered body under an
enrolled key was refused with 437 `detail=signature-failed`. Both are named
in the owner log.

**INN, a stranger.** A's peer record for INN was added by hand; INN cannot
take an invitation. A pulled `fn.*,control.*` from nnrpd by NEWNEWS. INN's
`Control: cancel` and `Control: newgroup` articles were filed on A: A's
`control.cancel` holds 1 and the newgroup message is stored. Neither was
executed: the cancelled j1 is still on A, and `fn.innnew` does not exist. A's
IHAVE and A's own outbound feed both reached INN. nnrpd serves X1 with
`FN-Authorship` intact.

**What INN itself did.** INN did not execute the transit cancel: j1 stayed on
nnrpd. This INN's nnrpd spooled local POSTs to `spool/incoming` rather than
handing them to innd, so the lab injected INN-side articles into innd by
IHAVE.

## Every SPIKE deferral

| where | deferral: what dev must own or prove |
| --- | --- |
| `books/stx-verify.lisp` `*fn-stx-verdicts*`, `fn-stx-verified-item` | the fifth token `:revoked`, rendered `revoked HEX keyring G`; dev proves the separation theorem over five tokens (`fn-stx-verified-item-of-revoked` is the spike's one-token lemma) |
| `books/stx-evidence-records.lisp` | token code 5 and its codec round trip |
| `books/hybrid-store.lisp` `fn-hsig-article-event-revoked-bindsp` | the binding theorem for the `:revoked` composite (the analogue of `fn-hsig-article-event-carried-bindsp-facts`) |
| `books/replay.lisp` `fn-replay-apply-revoked-verdict` | replay records a `:revoked` verdict only over a tombstone of exactly that principal at that generation; dev proves it and re-certifies the replay invariants over the new branch |
| `books/peer-authored-accept.lisp` `fn-pa-revoked-plan`, `fn-pa-revoked-event` | fold the revoked arm into `fn-pa-current-plan` as a fifth outcome with its keystones. The host now asks it after `:local-enrollment` on NNTP transit only. Bind the two primitive observations into the event: the host requires both verified before it asks (`host/native/owner.lisp`) |
| `books/peer-authored-accept.lisp` `fn-pa-carried-budget-decision`, `fn-pa-peer-carried-budget` | the budget read from string rows; dev gives it typed peer-config slots |
| `host/native/owner.lisp` `fnn-carried-usage-*` | per-boundary carried usage is a host sidecar (`<store>.carried-usage`) written after each carried commit, which can undercount by one article per crash. Dev derives it at replay from the carried composites' release evidence (`peer-transit:NAME`), carries it in owner state and proves it preserved |
| `books/peer-authored-accept.lisp` `fn-pa-signed-refusal-class`, `host/native/owner.lisp` `fnn-owner-transit-class` | the class names only the transit refusal (the owner log `detail=`). Dev records it in a durable `:unverified` verdict for held articles (with `fn-stx-reason-token` entries) and proves the class is a function of the carrier and the snapshots |
| `books/native-admin-peer.lisp` `budget OCTETS COUNT` words | typed slots and the admission theorem |
| `books/native-admin-shape.lisp` argv bound 16 → 32 | a per-request work bound. Dev should let a carried list grow across requests instead of in one argv |
| `host/native/hybrid-control.lisp`, `host/owner-host.lisp` `fn-owner-hybrid-next-generation` | generation 0 means "next" on `hybrid-enroll`/`hybrid-revoke`; dev needs an ACL2-owned next-generation request in the control codec |
| `tools/fn_peering.py` invitation state | pending and accepted invitations are JSON beside the config. Dev: a Store record kind with once-only consumption |
| `tools/fn_peering.py` key generation | the principal is 32 random octets with no genesis binding (`fn-prin-genesis-bindsp`) to its first key |
| `tools/fn_peering.py` `keys-process` | the statement executor is a reader-side poller that trusts the node's `HDR :fn-verified`. Dev: C2's `fn-ctl-authorize` shape, run by the owner at acceptance (a verified verdict, a grant covering `fn.keys`, and a PoP check in ACL2) |
| `tools/fn_peering.py` `pull` | the pull schedule and cursor are a JSON file. Dev: the owner scheduler (`books/scheduler-peers.lisp`) with an ACL2 cursor record and the ack-bounded advance as a theorem |
| `bin/fn` | `peer invite|accept|confirm`, `keys …` and `pull` go to the Python tool; dev: native operator verbs planned by ACL2 |
| `tools/fn_verify.py` | the `revoked` claim. It agrees (exit 1) when the independent check verifies the same principal |

## Theorems the dev version must prove

1. **Invitation binding.** `accept` enrols principal P with key set K only if
   the invitation's carrier verifies under K. The body must name P and K.
   `confirm` enrols the acceptor only if the acceptance verifies under the
   key set it names and names (a) a nonce this node issued and has not
   consumed, (b) this node's principal and (c) the ACL2 authored-source
   identity of that invitation. The invitation is consumed exactly once,
   including across a crash. Teeth: a tampered body, a replayed nonce, a
   second confirm, and an acceptance of another invitation.
2. **Succession over the acceptance plan.** When a succession statement for
   P is admitted as `:ok` by `fn-pa-current-plan`, the old key was P's
   current enrollment. The resulting enrollment then makes
   `fn-hl-current-enrollment` select the new keys. After that, the old keys
   give `:refused :local-enrollment` for new articles. Every verdict stored
   before is unchanged: evidence is never rewritten (the replay projection
   over kind-4 records). A carried or revoked statement never changes a
   keyring. The PoP binds the new key to the statement by Message-ID.
3. **Revocation over the acceptance plan.** After P's tombstone at G, no plan
   for P is `:ok`. A carrier under keys once enrolled for P is `:revoked`
   with generation G, and only on transit. Verdicts stored before G are
   unchanged. The rendered item is never `verified`. Replay admits a
   `:revoked` composite exactly when G names a tombstone of that principal.
4. **Opaque-carriage budget.** Across any trace, the sum of carried charges
   stored through boundary B is at most B's octet budget. Their count is at
   most B's count budget. Each exhaustion is refused by its own name. A list
   with no budget admits nothing. The usage in owner state equals the replay
   projection.
5. **Three refusal classes.** For a present carrier, the refusal class is one
   of no-local-binding, unsupported-profile, signature-failed or malformed.
   It is a function of the carrier, the snapshots and the observation. None
   of them is `verified`. None falls to the carrier-absent arm
   (`fn-pa-carrier-form` never returns `:absent` for a present field). A held
   article records its class in its durable verdict.
6. **Pull cursor.** The cursor advances past a round only when every
   NEWNEWS-listed Message-ID drew 235, 435 or 437 from the local node.

## Limitations

- No lab row exercises the unsupported-profile class. The ACL2 tests exercise
  no-local-binding, signature-failed and malformed.
- The revoked article reached each node by hand IHAVE from the peer's
  address, standing in for a delayed relay. The owner feed did not deliver it.
- The key-statement executor is a Python poller over the reader port. Nothing
  about it is owner-side.
- A connects to INN over loopback with source-address authentication, and to
  B without TLS.
