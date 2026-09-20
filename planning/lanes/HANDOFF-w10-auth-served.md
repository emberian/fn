# w10/auth-served: AUTHINFO, STARTTLS and posting permission on the served path

Branch `w10/auth-served`, worktree `build/lanes/w10-auth-served`, from dev
`92e4a40` and merged with dev at `3e1b184` (w9/digest, w9/records).

| | |
| --- | --- |
| `e1159a7` | `books/peer-inbound` admits clean (six proof defects) |
| `3c953b6` | guard verify the peer chain (nine `verify-guards`) |
| `6da93c1` | AUTHINFO, STARTTLS and the 440 wired into `fn-auth-step` |
| `c6ba0a9` | `books/served` and `books/owner` admit on the wired chain |
| `dfd2b55` | the host side, `tests/test_auth.py`, the live evidence |
| `307e007` | `books/nntp-auth-invariants`, the teeth, the registries, the audit |

## Post-merge state (read this first)

The lane merged dev at `f730c24` after the farm runs below. dev had landed
the inbound lane's own repair of `books/peer-inbound.lisp` (better than
this lane's: `:rule-classes nil` facts cited by `:use`, and
`fn-peer-session-consistentp-forward` exported as a strict superset of
this lane's bridge), the clock seam's arity fixes in `books/owner.lisp`,
the owner's thirteenth field and six feed step arms. The merge commit
records every resolution and why.

**The post-merge tree is NOT certified and the laptop cannot certify it.**
`tools/certs.py install` put pairs beside `books/node`, `books/config` and
others whose `book-hash` no longer matches the merged source, so
`certify-book` refuses at the first `include-book` with
`book-hash-mismatch`. That is a cache fault, not a proof fault, and the
cure is the farm, which installs the box's own consistent cache first. The
post-merge farm submission was still mirroring when this lane ended.

**What IS certified post-merge, locally**: `books/nntp-auth-invariants`
and `tests/acl2/nntp-auth-tests` (120 assertions), because their closures
happened to hold consistent pairs.

**What the pre-merge farm proved, and it still stands as evidence about
that revision**: run `run-20260920T202606Z-a8dd` certified
`books/peer-inbound`, `books/nntp-auth`, `books/served`, `books/owner`,
`books/nntp-auth-invariants`, `books/ideal` and
`tests/acl2/nntp-auth-tests`. Run `run-20260920T205732Z-45b6`, after the
served-tests fix, left only `books/owner-invariants`,
`books/owner-config` and `tests/acl2/owner-tests` failing --
`tests/acl2/served-tests` passed.

**The next lane's first action** is one farm run over the closure on the
merged tree:

    python3 tools/farm.py submit persvati --jobs 6 \
        --remote-root /home/ember/fn-lanes/w10-auth-served \
        --affected-by books/nntp-auth.lisp --closure

## Certification table

**Update, and it is the headline: the served chain CERTIFIES.** Farm run
`run-20260920T202606Z-a8dd` on persvati (`--jobs 6`, `--remote-root
/home/ember/fn-lanes/w10-auth-served`, `--affected-by books/nntp-auth.lisp
--closure`, installed 39 kept 79 uncached 146) produced real certificates
for **`books/peer-inbound`, `books/nntp-auth`, `books/served`,
`books/owner`, `books/nntp-auth-invariants`, `books/ideal` and
`tests/acl2/nntp-auth-tests`**, plus `sha256`, `crypto-seam`,
`crypto-attach`, `auth-secret` and `nntp-post`.  That is the first verdict
above `books/nntp-effects` since the peer port merged.  It failed exactly
four roots, all of them this lane's arity ripple:
`books/owner-invariants`, `books/owner-config`,
`tests/acl2/served-tests`, `tests/acl2/owner-tests`.  Commits `2152437`
and later chase those; the state at the end of the lane is below.

**`books/owner-invariants` is still open, and it is the lane's one
unfinished root.** It went from failing at its FIRST served form to
failing at `fn-own-advanced-session-is-bounded`, roughly forty forms in,
with three dependents behind it (`fn-own-advance-repins-the-connection`,
`fn-own-durable-outcome-repins-the-poster`,
`fn-own-durable-reply-names-a-durable-record`).  The remaining checkpoint
wants `fn-post-sessionp` of the post session the re-pin builds; the
wrapper-preservation lemmas either side of it
(`fn-own-peer-with-base-is-a-session`,
`fn-own-auth-with-base-is-a-session`,
`fn-own-auth-sessionp-forward-bases`) are proved and in place.
`books/owner-config` and `tests/acl2/owner-tests` are cascades of it.

**The two real defects that chase uncovered, both fixed here**:
`fn-own-advance` rebuilt the connection's session as a BARE post session,
throwing away the peer wrapper (and, after this lane, the login); the
rebuilt connection then failed `fn-own-conn-boundedp` and the advance was
silently refused, so **ADVANCE has been a no-op since the peer port**.
And `fn-own-open-peer-preserves-relation` did not exist, so
`fn-own-step-preserves-relation`'s `:open-peer` arm had nothing to use.

The table below is the LOCAL admission record, which is what the lane had
before the farm run and is still the fastest way to re-check a single
book.

**The rest of this section was written before the farm run and is kept
because the reasoning still applies to a laptop `certify-book`.** Every ACL2 result below is an
ADMISSION: the book's own source processed by `tools/acl2 --timeout <n>`
under `(set-ld-error-action :continue)` with a 2,000,000-step prover limit,
ACL2 8.7 on this laptop, 2026-09-20. An admission proves every form in the
book; it does not produce a certificate and it trusts the `include-book`s
below it, which for `peer-inbound` and above are themselves uncertified.

| root | verdict | evidence |
| --- | --- | --- |
| `books/sha256` | **certified** | `build/acl2/certify-20260920T190515Z-17214` |
| `books/crypto-seam` | **certified** | same run |
| `books/crypto-attach` | **certified** | same run |
| `books/auth-secret` | **certified before this lane's edit**; the `fn-authsec-verifier` constructor was added after, so the certificate is stale and the book is ADMITTED only (through `nntp-auth`'s include) | same run + `ld-auth19.log` |
| `books/nntp-post` | **certified** | `build/acl2/certify-20260920T190156Z-13225` |
| `books/peer-config` | **certified** (installed from the cache; not re-run here) | `tools/certs.py install` |
| `books/peer-inbound` | admitted, 0 errors, guards included | `ld-peer15.log` |
| `books/nntp-auth` | admitted, 0 errors, guards included | `ld-auth19.log` |
| `books/served` | admitted, 0 errors | `ld-served7.log` |
| `books/owner` | admitted, 0 errors | `ld-owner2.log` |
| `books/nntp-auth-invariants` | admitted, 0 errors | `ld-inv2.log` |
| `tests/acl2/nntp-auth-tests` | admitted, **120 assertions passed, 0 failed** | `ld-autests5.log` |
| `books/owner-invariants`, `books/owner-config`, `books/ideal`, `tests/acl2/served-tests`, `tests/acl2/owner-tests` | **NOT RUN** | — |

The logs are in this session's scratchpad
(`/private/tmp/claude-501/-Users-ember-dev-fn/990cbaad-.../scratchpad/w10-auth/`),
which does not survive the machine. What survives is the source: each log
can be regenerated by
`tools/acl2 --timeout 1500 < driver.lsp` with a driver of three lines,

    (set-ld-error-action :continue state)
    (set-prover-step-limit 2000000)
    (ld "books/<root>.lisp" :ld-error-action :continue)

run from the worktree root, and `grep -c "ACL2 Error"` on the output.

### Why nothing is certified, and it is not a proof gap

`certify-book` refuses below `peer-inbound` for a CACHE reason, not a proof
reason. The installed certificate cache mixes two origin roots: `books/config`'s
certificate names its sub-books by absolute path under
`/home/ember/fn-lanes/w9-reconfig-cs`, while the `clock`, `records`, `cbor`
certificates installed beside it come from `/tank/fn/lanes/w9-records`.
`include-book` only warns about that; `certify-book` refuses. The exact
message is in `build/acl2/certify-20260920T192444Z-32051/books--peer-inbound.certify.log`.

The fix is a farm run over the closure, which installs one box's own
consistent cache first:

    python3 tools/farm.py submit persvati --jobs 6 \
        --remote-root /home/ember/fn-lanes/w10-auth-served \
        --affected-by books/nntp-auth.lisp --closure

That run is **the certification of record for this lane and has not
completed**. Whoever picks this up: run it, and do not read the admissions
above as certificates.

### Open, named, not weakened

- **OB-AUTH-FOLD** (`planning/proofs.json` PRF-031, and the header of
  `books/nntp-auth-invariants.lisp`). The fold-level statement — no read of
  a connection under a configuration that grants posting to no one emits a
  submission — is not proved. It is an induction over `fn-served-feed`
  carrying three facts and two do not exist:
  1. `fn-auth-step-preserves-the-config`, true by inspection of five
     branches, nobody has stated it — **books/nntp-auth**;
  2. in command mode `fn-wire-feed-byte` emits only `(:command ...)` events
     and leaves the mode `:command` or `:closed` — **books/wire-invariants**;
  3. `fn-nntp-post-step` emits a submission only from an `(:article ...)`
     event — **books/nntp-post**.
  With those three it is the append law plus
  `fn-served-dispatch-of-a-refused-post-leaves-the-wire-in-place`.
- **The independent client.** `tests/test_auth.py`'s `nntplib` round trip
  SKIPS: the module was removed from the standard library in Python 3.13.
  Every transcript in `planning/evidence/auth-w10-2026-09-20.md` is fn's own
  client talking to fn. `specs/nntp.md` has asked for a real newsreader
  since it was written and this lane did not deliver one.
- **RFC 4642 §5.** A general "restricted command" set gated on TLS rather
  than on authentication is still not implemented; `fn-auth-restricted-keywordp`
  gates on authentication only. Unchanged by this lane, still recorded in
  `specs/nntp-audit.md`.
- **`books/nntp-auth.lisp` is 1,340 lines** with three hand-written records.
  It wants `fn-defrecord` and a split at its seam. The ASK is on the board.

## What this lane found that was not its own

Every one of these was on dev and invisible, because no root above
`books/nntp-effects` could be admitted at all.

| where | what |
| --- | --- |
| `books/peer-inbound` | six forms did not admit: a closed `binary-append` hiding the status-line digits and the length bound; `fn-nntp-result-effects` left ENABLED by `books/nntp-session` so `fn-nntp-effects-single`/`-multi` stopped matching; a `:use` naming a one-argument `fn-peer-capability-lines`; a missing block-text lemma; a 2,000,000-step `:expand` of `fn-post-session-consistentp`; a `("Subgoal *1/1" ...)` hint for an induction the form no longer does |
| `books/peer-inbound` | **no function was guard verified**, and `fn-served-dispatch` has `:guard t`, so `books/served` could not be admitted |
| `books/served` | `fn-served-open-peer-is-a-connection` stated with eight arguments against a nine-argument function |
| `books/served` | `fn-served-submission-of-append` was FALSE for a list carrying `(:submit nil)` |
| `books/served` | `fn-wire-article-event-resumes-command-mode` named `fn-wire-event-article`, which is not a rule, so its theory expression could not be evaluated |
| `books/owner` | `fn-own-open-peer` called `fn-served-open-peer` with eight arguments and `fn-own-transit-outcome` called `fn-served-make-conn` with five; both defuns died, taking `fn-own-step`, `fn-own-run` and `fn-own-vocabulary` with them |
| `books/owner` | **`fn-own-conn-boundedp` read the served session as a bare post session.** It has been a PEER session since the peer port, so `fn-post-sessionp` was false on every connection and `fn-own-read` removed each one after its first read: the reply went out and the next command met a closed socket. **The reader path has not survived two commands on dev since that merge.** |
| `books/nntp-auth` | `fn-inj-nth` was never enabled, so no accessor-of-constructor lemma closed; the record lacked the `accessor-forward-consp` facts `fn-defrecord` generates; `fn-auth-starttls-effect-is-typed` was FALSE, because `(:starttls)` is not an `fn-nntp-effectp` |

The general lesson, and it is worth a lint: **`fn-nntp-result-effects` is
exported enabled by `books/nntp-session.lisp`**, and every effects-well-formed
lemma in the tree is stated over it. Each such lemma is one `(:definition
fn-nntp-result-effects)` away from silently not matching. `books/nntp-auth`
closes it book-locally; the right fix is in `nntp-session`'s export theory.

## The host, and where the trust boundary is

`tools/run_owner.py` performs the TLS handshake with Python's `ssl` in
`Owner.upgrade`, named so it can be found. No theorem in this tree says
anything about it. ACL2 decides that a handshake is owed (`(:starttls)`,
only from the branch that also answered 382 and entered the handshake), that
the octets behind the command line are not NNTP (`fn-served-tls-handshakingp`
stops the fold), and when the layer is recorded (`(:tls-established)`, the
only transition that sets `tlsp`). The host owns the socket and nothing else.

`fn principal set-password` derives the verifier in one ACL2 session through
`tools/auth_secret.py`. There is no `hashlib` on that path and `bin/fn` no
longer imports the module. Measured: two `set-password` runs, each its own
session, complete inside 5.3 s; the session start dominates and the digest
is five SHA-256 compression blocks.

## Coordination

- `books/peer-inbound.lisp` belongs to the inbound lane. If it lands its own
  repair, take that one and drop `e1159a7` and `3c953b6`; the statements are
  untouched in both commits.
- `books/owner.lisp` and `tools/run_owner.py` are shared with `w10/owner-feed`
  and `w9/runtime`. The board names every function this lane touched.
- `books/auth-secret.lisp` gained `fn-authsec-verifier` (the constructor that
  rebuilds the stored shape from the two fields the operator's file holds)
  with `fn-authsec-enrol-is-a-verifier-of-its-fields` pinning it to enrolment.
  That is the digest lane's book; the addition is small and additive.
