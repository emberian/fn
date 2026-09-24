# The hybrid_author "feed storm": no storm, a fixture without receiver enrollment, and two silent refusals

Native subsets on 1a9dd747 ([record](native-subsets-1a9dd747-2026-09-24.md),
failure 8) reported that `tests.test_native_hybrid_author`'s peering case
never delivered the authored carrier, that "the sending node opened 437
connections in 45 s", and that neither owner wrote anything to stderr. This
lane reproduced the case, found the cause, fixed the fixture, and made both
sides log a refused peer transfer. Artifacts are in
[`hybrid-feed-storm/`](hybrid-feed-storm/) with a `SHA256SUMS`; the hbox
scratch is `/tank/fn/scratch/hybrid-feed-storm/`.

## Reproduction on 1a9dd747

The 1a9dd747 developer image (launcher `5d42db2d…`, read-only from
`/tank/fn/gates/qual-1a9dd747-20260924`) ran the one failing case under
[`hyb_diag2.py`](hybrid-feed-storm/hyb_diag2.py). The script keeps the temporary
root, tees both owners' stderr, and runs the sending owner under
`strace -f -e trace=connect,read,write,...`. The case failed as before, after 45 s.

- **Sender (strace, [excerpt](hybrid-feed-storm/repro-1a9dd747-sender-network.txt)):**
  one `connect(AF_INET 127.0.0.1:<receiver>)` in the whole run. On it:
  `MODE STREAM` → `203`, `CHECK <msgid>` → `238`, `TAKETHIS <msgid>` + article
  → **`439`**. The feed journal (FNFD) recorded the outcome. The connection then
  sat idle until teardown closed it 45 s later. There was no second dial, no
  re-offer and no retry. The full strace is `diag/repro2/owner0.strace`
  (SHA-256 `c7c06189…`). The SIGSEGV line in it is SBCL's normal
  write-barrier signal.
- **Receiver:** 445 lines of `accepted peer connection=N peer=other`
  ([summary](hybrid-feed-storm/repro-1a9dd747-receiver-summary.txt)). These
  lines are the test's own `read_article` polls, which open a new
  `ARTICLE` connection from 127.0.0.1 every 0.1 s for 45 s. The receiver's owner
  maps each one to peer `other` because that peer's configured source address is
  127.0.0.1. The "437 connections" count was these probes. The feed did not
  make them.
- **Why 439:** since [receiver-local authorship at transit
  ingress](peer-authored-ingress-2026-09-24.md), `fnn-owner-attempt-transit`
  (host/native/owner.lisp) stores a signed carrier only when
  `fn-pa-current-plan` (books/peer-authored-accept.lisp:52) finds the
  **receiver's own** current enrollment of the carried principal. Otherwise it
  returns `(:refused :local-enrollment)`. The test enrolled the author only
  at the sender. Its docstring said it "does not claim a receiver-local enrolled
  verdict", which was written before that change made local enrollment
  mandatory. The [two-Store join](two-store-join-1a9dd747-2026-09-24.md)
  provisions reciprocal enrollment, and signed peering worked there.
- **Outcome classification is correct:** 439 is a refusal. The sender's feed
  machine drops the entry, with no retry and no backoff to apply. Refused,
  uncertain and accepted stayed distinct on this path. Nothing in the retry or
  backoff decision was at fault. `fn-owner-feed-backoff-ms` (1000 ms here) and
  the feed's retry bound `*fn-own-feed-retry-bound*` = 3 were never exercised.

**The article's actual blocker was the fixture** (no receiver enrollment).
**The real defect was the silence:** the receiver refused a peer transfer, and
the sender recorded a 439, with no log line on either side. For served POST,
control POST and connection opens, `fn-olog-*` renders the line. For a
transit outcome or a feed reply, nothing did.

## Fix

| commit | change |
| --- | --- |
| `7837416e` | `books/owner-log.lisp`: `fn-olog-transit-line` (receiver) and `fn-olog-feed-reply-line` (sender, nil for a 335/238 prompt); host wiring (`fn-owner-transit-log-line`, `fnn-owner-transit-complete`, `fn-owner-feed-octets` → `fn-owner-feed-log-line`, `fnn-feed-reply-step`); `fnn-owner-attempt-transit` records which check refused (ACL2's keyword where ACL2 names one); the peering fixture enrolls the receiver and checks the receiver's own `HDR :fn-verified` after restart |
| `f71f4ecb` | `let*` for the feed log binding (the image build refused the `let`; `make check` does not `ld` the host); the unenrolled-receiver saved-image case; manifests; cost baseline |
| `3d34eb6a` | the feed Message-ID is octets, not a string (the first image printed `message-id=` empty) |
| `287c38ed` | a comment correction in the test book |

**Theorems** (books/owner-log.lisp; teeth in tests/acl2/owner-log-tests.lisp):

- `fn-olog-transit-line-says-refused-iff-rejected`: a transit line's first
  word is `refused` exactly when the completion is not uncertain and
  `fn-peer-transit-code` is 437/439. That is the same code, over the same decision and
  completion, that `fn-own-transit-outcome` sends on the wire. Host line:
  `fnn-owner-transit-complete` calls `fn-owner-transit-log-line` (owner-host.lisp)
  before `fn-owner-transit-outcome`, from all three transit branches of
  `fnn-owner-drain-one`. Teeth: a failure-8 witness line, plus accepted, uncertain,
  deferred, reject-by-decision and unconsumed-durable witnesses;
  `must-fail` `olt-transit-line-echoes-the-host-word` (a `:defer` with host word `:refused`
  logs `deferred`) and `olt-transit-line-refused-unless-accepted` (the code clause is load-bearing).
- `fn-olog-feed-reply-line-says-the-code-class`: a sender line exists
  exactly for a reply that is not a 335/238 prompt, and its first word is the
  class of the ACL2-parsed code. Host line: `fn-owner-feed-octets` installs
  it and `fnn-feed-reply-step` writes it. Teeth: 439/431/438/239 witnesses,
  238 → none, and `must-fail` `olt-feed-line-always-classed`.
- `fn-olog-transit-line-is-one-line` and `fn-olog-feed-reply-line-is-one-line`.

Certification (hbox, w28 ACL2 8.7, 2 jobs, gate
`/tank/fn/gates/hybrid-feed-storm-7837416e`):
`certify-20260924T153733Z-1502951` (owner-log + test, passed, 7.6 s / 7.8 s),
`certify-20260924T154012Z-1507829` (the 108 default image roots at
`7837416e` bytes, 21 certified, passed), and later runs
`run-20260924T154537Z-fd9b`, `-154641Z-7122` and `-154903Z-abc0` (manifests `certify-20260924T154542Z-1523360`, `certify-20260924T154647Z-1534343` and `certify-20260924T154917Z-1550410`). Those three
covered owner-log at `3d34eb6a` and its test at `287c38ed`, then the image
closure again, and all passed. Four books this branch does not change measured
over 10 s at hbox load ~10: bp-handoff-status 10.9, config-owner-live 11.4,
peer-inbound 15.0 and store-node-traces 16.6. They are admitted to
`planning/proof-cost-baseline.json` as `b6d8d714` did: defect entries,
not allowances.

## Reruns on a developer image built from this branch

Image built in the gate tree after `validate --profile default` loaded all
108 roots. Launcher `d4a147dcc535ed7c…`, core `5024546d36153e72…`, build log
`331d598a…`. The books are at `3d34eb6a`/`287c38ed` bytes and the host is at `f71f4ecb`.

| run | result | log SHA-256 (first 16) |
| --- | --- | --- |
| peering case (enrolled receiver), diag | pass, 3.7 s; sender strace in an earlier run of the same image: 1 outbound connection | `063306c4514ffeda` |
| unenrolled receiver, diag | pass, 6.2 s (includes a 4 s no-re-offer wait); 1 outbound connection | `b4ae2a19922bb301` |
| `tests.test_native_hybrid_author` (`FN_RUN_HYBRID_E2E=1`) | 5/5, 12.6 s | `fb358d280db85282` |
| `tests.test_native_peering` (source-matched hashes set) | 4/4, 6.1 s | `730edc025beeaea9` |
| `tests.test_native_protected_peering` | 5/5, 44.6 s | `731248da0e0e0d1a` |

The unenrolled case's lines, verbatim
([sender](hybrid-feed-storm/fix-unenrolled-sender-service.log),
[receiver](hybrid-feed-storm/fix-unenrolled-receiver-service.log)):

    refused feed peer=other message-id=<hybrid-unenrolled-relay@example.invalid> code=439 time=…
    refused transit connection=0 message-id=<hybrid-unenrolled-relay@example.invalid> code=439 decision=want reason=none detail=local-enrollment time=…

Local: `make check` green; `tests/native_feed_service_raw.lisp` (one reply
log offer, none for connection-phase words) and
`tests/native_peer_authored_accept_raw.lisp` (the relayed detail is `:carrier`,
`:local-enrollment` or `:signature`) pass under SBCL.

## What this does not establish

- **No theorem says a refused offer is never re-offered.** The observation
  covers one 439 and no second line in 4 s. The feed book's drop-on-439 has
  not been re-examined here, and no retry or backoff bound was added,
  because nothing in this failure needed one.
- `detail` names are host tags except where ACL2 named the refusal
  (`fn-pa-carrier-form` and `fn-pa-current-plan`). The detail is a log field
  and never feeds a decision.
- A loss of connection with an entry in flight (`fn-owner-feed-lost`) still
  requeues silently. A peer-side `436` is logged `deferred` at the sender,
  but the retry-bound drop has no line of its own.
- Design question for ember: an fn relay that has not enrolled an author
  refuses that author's signed carriers outright (439), so signed articles
  cannot transit fn nodes that do not verify them. That follows from
  peer-authored ingress. It is not a defect found here.
- A developer image built in a lane gate, not a qualification cut or the deployed node.
