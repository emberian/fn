# w11/auth-live: the credential that was written, loaded, and pinned into nobody

Branch `w11/auth-live`, worktree `build/lanes/w11-auth-live`, from dev
`4732ace`.

## The finding, in one line

`books/served.lisp fn-served-open-peer` pinned the literal
`(fn-auth-open-config)` where `fn-served-open` pinned the operator's, and the
owner opens a connection with that branch whenever its SOURCE ADDRESS matches
a peer record — which, on a box where a configured peer answers on loopback,
is every client. So the operator's AUTHINFO configuration reached no
connection on either node of the v0 matrix.

That one fact is all three of the matrix's F-AUTH findings: no credential in
the pinned configuration means `AUTHINFO PASS` is `481` whatever the secret,
means `fn-auth-capability-lines` advertises no `AUTHINFO USER`, and means
`fn-auth-config-requiredp` is `nil` so `POST` is not gated.

## How it was found, and it was measured

One script, three runs, one variable at a time; the whole record is
[`planning/evidence/auth-live-2026-09-21.md`](../evidence/auth-live-2026-09-21.md).

| run | difference | result |
| --- | --- | --- |
| 1 | `fn init`, `fn principal set-password`, `fn run` | `AUTHINFO USER` advertised; the credential reached the listener |
| 2 | run 1 **plus one `peer add --source-address 127.0.0.1`** | no AUTHINFO label; `AUTHINFO PASS <the secret just written>` → `481`; `POST` → `340` |
| 3 | run 2 on the repair, with `[auth] required = true` | `201` greeting, `AUTHINFO USER` advertised, `POST` → `480`, `281`, label gained, `POST` → `340`, AUTHINFO withdrawn |

The other four candidates the brief named were checked and are all clean: the
CLI writes a well-formed verifier (run 1 proves it end to end), `bin/fn run`
does pass `--auth-file` when the file exists, `load_credentials` and
`fn-owner-set-auth` accept it, and the salt and encoding agree — run 1 logs
in with them.

## What changed

**The model.** `fn-served-open-peer`, `fn-own-open-peer` and
`fn-owner-open-peer` take and pass the operator's `acfg`. In
`host/owner-host.lisp` the AUTHINFO block moved above the transit port so
`fn-owner-open-peer` can read it. Under the default policy nothing changes,
because the default IS `(fn-auth-open-config)`.

**PRF-039**, first half: two theorems in `books/served.lisp`, both false of
the old definition: `fn-served-open-peer-pins-the-configuration`, and the keystone
`fn-served-peer-and-reader-open-under-the-same-policy`. Teeth in
`tests/acl2/served-tests.lisp` drive `fn-served-step` over two connections
differing in that one argument and get `281` against the operator's policy
and `481` against the empty one.

Both theorems are unconditional equalities, so there is no hypothesis to
`must-fail`: what the teeth rule asks for here is the reachable
non-degenerate witness and the separating one, and both are there --- a
policy with a real credential, a real `required` bit and a real certificate
(`fn-auth-configp` asserted of it), and the same two reads against the
value the old definition pinned, which separate by every reply they draw
and not by a weakest clause.

**The greeting (RFC 3977 §5.1.2).** `fn-served-greeting` read the injection
configuration alone, so a connection under `required = true` greeted `200`
and then answered `POST` `480`. It now takes the opened session and reads the
same value the POST capability label and `fn-auth-postingp` read.
`fn-served-open-greets-200-exactly-when-the-connection-may-post` is the
keystone (PRF-039's second half); `fn-served-open-greeting-agrees-with-the-post-label` is the
sentence `specs/nntp.md` makes, over the octets.

**One principal registry.** `fn principal list` read
`<store>/principals/*.principal`, a directory nothing has ever written —
`fn principal new` prints its derivation and returns — so it answered
"nothing" on every store that has ever existed. **The single registry is the
credential file**: `[auth] path`, else `<store>/auth.toml`, which is the file
the running service loads. `list` prints the login, its principal and its
posting flag, never the verifier. `principal new` derives an FN-Statement
signing identity and is not a registry at all.

**The policy is reachable from the operator surface.** `fn init` gains
`--auth-required`, `--auth-protected-only` and `--auth-file` and writes
`[auth]`. Before this there was no way to set `fn-auth-config-requiredp`
through `bin/fn` at all — which is the second reason the matrix's nodes were
ungated, and why `V0-AUTH-GATED` could not have passed however the model
behaved. `packaging/fn.toml.example` and `docs/operator.md` document it.

**The log said `reader` for every connection**, including the ones ACL2
opened with `fn-own-open-peer`. It now says the role and `peer=<name>`. That
line is how an operator will notice this class of confusion next time.

**The boundary test.** `tests/test_auth.py ServedCredentialTests`: a node
started with `bin/fn run` over an `fn.toml` written by `fn init
--auth-required`, a peer record on 127.0.0.1, and a credential the CLI writes
in the same test. Every test above it starts `tools/run_owner.py` directly
with an explicit `--auth-file` and no peer table, and **none of them can
reach the peer branch**. That is the whole reason a certified feature was
broken in production.

## Certification

Farm, persvati, `--affected-by books/served.lisp --closure --jobs 6`, remote
root `/home/ember/fn-lanes/w11-auth-live`:

| run | verdict |
| --- | --- |
| `run-20260921T015401Z-ec5c` | **passed**, 0 failures, 196 s (the `acfg` change): `books/served`, `books/owner`, `books/owner-invariants`, `books/owner-config`, `books/nntp-auth`, `books/nntp-auth-invariants`, `books/peer-inbound`, `tests/acl2/owner-tests`, `tests/acl2/served-tests` |
| `run-20260921T020122Z-d422` | **passed**, `tests/acl2/served-tests` with the PRF-039 teeth, 112 assertions, 0 errors |
| `run-20260921T021107Z-808e` | **failed** at one form, recorded because it is the only one: `fn-auth-capability-lines-offer-post-by-definition` was stated with `fn-nntp-capability-lines` disabled, so `member-equal` over the append had no law. Made `local` with `:rule-classes nil` and both definitions open |
| `run-20260921T021603Z-e2e8` | **passed**, 0 failures, 266 s, with the greeting keystones: `books/served`, `books/owner`, `books/owner-invariants`, `books/owner-config`, `books/nntp-auth`, `books/nntp-auth-invariants`, `books/ideal`, `tests/acl2/served-tests`, `tests/acl2/owner-tests`, `tests/acl2/owner-config-tests` |
| `run-20260921T022610Z-355a` | **passed**, 0 failures, 212 s, on the tree AFTER merging dev, over the closure of `books/served.lisp` AND `books/owner.lisp` (`--jobs 8`, installed 46 kept 100 uncached 133). **This is the certification of record for the lane.** |

## The v0 matrix re-run: six of the eight F-AUTH rows moved

`python3 tools/v0_matrix.py HEAD --host persvati --jobs 8` at `6fb30ca`,
1336 s, written by the tool into
[`planning/v0-matrix.json`](../v0-matrix.json) and
[`planning/evidence/v0-matrix-2026-09-21.md`](../evidence/v0-matrix-2026-09-21.md);
`make check` validates the rows against their sha256.

| | `c3b99f8` (before) | `6fb30ca` (after) |
| --- | --- | --- |
| F-AUTH accepted / refused | 9 / 8 | **15 / 2** |
| F-AUTH disagreements | 8 | **2** |
| whole matrix | 111 accepted, 25 refused, 2 uncertain, 29 not-exercised, 23 not-built, 10 disagreed | 145 accepted, 29 refused, 2 uncertain, 13 not-exercised, 1 not-built, 17 disagreed |

The six that moved, each `refused` before and `accepted` now:

| row | before | after |
| --- | --- | --- |
| `V0-AUTH-ADVERTISED-A/B` | `VERSION, READER, POST, OVER, HDR, LIST, IMPLEMENTATION` | the same **plus `AUTHINFO`** |
| `V0-AUTH-LOGIN-A/B` | `481 authentication failed` | `281 authentication accepted` |
| `V0-AUTH-LIST-A/B` | `rc=0 lists matrix: False` | `rc=0 lists matrix: True` |

The two that did not are `V0-AUTH-GATED-A/B`, `340` where the row expects a
refusal, for the configuration reason in the next section and not for a
model reason.

**An independent client saw the login.** `V0-CLIENT-NNTPLIB-A/B`:
`nntplib 3.12.13` on persvati's `uv`-installed CPython 3.12 drove
`CAPABILITIES, AUTHINFO USER/PASS, GROUP, STAT, ARTICLE, HEAD, BODY, OVER,
LIST, ARTICLE (absent), QUIT` against both nodes and reported
`login=accepted authinfo-advertised=True`. The standard library's own NNTP
implementation, not fn's, framed and parsed every one of those. The driver
did not attempt a login before this lane; it does now, and the row fails if
the login does.

**Not this lane's, and the re-run makes them visible for the first time.**
The matrix's `not-built` count fell from 23 to 1 because node B survived the
first `IHAVE` this time, so F-TRANSIT, F-FEED and F-CRASH ran instead of
being blocked behind a dead process. Twelve of the seventeen disagreements
are theirs and every one is a new observation rather than a regression:
`V0-TRANSIT-DUPLICATE-AB/BA` answer `335` where a second offer of a held
Message-ID should be `435`; `V0-TRANSIT-LOOP-AB/BA` answer `235` and
`V0-TRANSIT-LOOP-ABSENT-AB/BA` then serve the article, so the Path loop test
is not refusing; `V0-TRANSIT-CHECK-DUP-AB/BA` answer `238` where RFC 4644
wants `438`; `V0-TRANSIT-INDEPENDENT-A/B` no longer hold, because by the
time they run the feed has crossed. `V0-FEED-JOURNAL`, `V0-CRASH-RESTART`
and `V0-BP-IMAGE` are the other three. The owner feed itself WORKS both ways
at this commit, octets identical to the source, which is in the facts table.
None of that is touched by this lane and none of it is reported here as
this lane's result.

## Open, named, not weakened

- **`V0-AUTH-GATED-A/B` cannot pass on the v0 matrix's topology, and it is
  not a model defect.** The row asks that `POST` before a login be refused;
  that is true exactly under `[auth] required = true`, and the matrix's two
  nodes do not set it. They cannot: `fn-auth-restricted-keywordp` gates the
  reader verbs (`GROUP`, `ARTICLE`, `LIST`, `OVER`, …) and `IHAVE`/`CHECK`/
  `TAKETHIS` alike, so a node that required a login would answer `480` to the
  50 accepted `F-READ` rows and to every transit offer. The same question
  asked of a node that DOES set the policy is
  `ServedCredentialTests.test_post_is_gated_by_the_configured_policy`, and it
  passes. Resolving the matrix row needs the decision below.
- **ASK, on the board, to the peering owner: is a peer record's
  `auth-source-address` an authentication for RFC 4643's purposes?** If it
  is, `fn-auth-gatedp` should not gate a connection the owner resolved to a
  peer, and that claim belongs in `books/assumptions.lisp` beside A-PEER, not
  in a branch test. If it is not, a node that both serves authenticated
  readers and takes a feed needs two policies. This lane deliberately changed
  neither: it made the policy REACH the peer connection, which strengthens
  the gate, and stopped there.
- **OB-AUTH-FOLD** (PRF-031) is untouched and still open.
- **The outbound feed tolerates the 201 greeting** (`tools/run_owner.py:910`
  tests `startswith(b"20")`), so a node that requires a login still feeds a
  peer it dials. Checked, not assumed.
- The independent client (`V0-CLIENT-NNTPLIB`) now performs the login through
  the standard library's own `nntplib`, so the 281 is observed by something
  that is not fn — but only on persvati, where a Python 3.12 exists. On a box
  with only 3.13 the row still skips and says so.

## The next global step

**One ASK, then one harness.** The ASK is the one above: whether a peer
record's `auth-source-address` authenticates for RFC 4643's purposes. Until
it is answered, `[auth] required = true` is a policy an operator can set and
a peered node cannot use, and `V0-AUTH-GATED-A/B` is the only F-AUTH row the
matrix cannot make an outcome. It is a one-afternoon packet for whoever owns
`books/peer-inbound`: the cheap half is a theorem that a session with NO
peer is already refused `502` for the three transit verbs, which makes their
place in `fn-auth-restricted-keywordp` demonstrably load-bearing or not.

The harness is **not** another auth harness. The matrix at `6fb30ca` says
F-NODE, F-OUT, F-GROUP, F-AUTH, F-POST and F-READ are whole features that
work between two peered nodes, the owner feed crosses both ways with
identical octets, and the frontier has moved to **transit correctness**:
twelve of the seventeen disagreements are peering decisions reaching the
wire wrongly (`335` for a duplicate offer, `235` for a Path loop, `238` for
a duplicate `CHECK`), and every one of them has a certified model theorem
that says otherwise. That is the same shape as the defect this lane fixed —
a model that is right and a served path that does not consult it — and it is
where the next measurement belongs.

Last: this lane is merged with dev at `9010d01` and `make check` passes,
including `w11/lab-gate`'s new caller-signature lint (0 findings over 25766
calls). The three `acl2-arity` findings it reports are pre-existing
spellings in `tests/test_teeth_check.py` and are not this lane's.
