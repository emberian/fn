# w4/post — POST and RFC 5537 injection

Branch `w4/post` from `dev` at `ca66782`. Packet C1-06.

## What landed

| File | What it is |
| --- | --- |
| `books/injection.lisp` | RFC 5537 §3.5 injection: `fn-inj-decide` of (source octets, clock observation, configuration record) to an opaque decision record. Generates Path, Injection-Date, Injection-Info, and Message-ID and Date when absent. |
| `books/injection-invariants.lisp` | What injection preserves and generates. |
| `books/nntp-post.lisp` | `fn-nntp-post-step` and `fn-nntp-post-outcome`: the functions the serving host calls. |
| `tests/acl2/injection-tests.lisp` | Ground witnesses and one violating article per implemented clause. |
| `tests/acl2/nntp-post-tests.lisp` | The 340/440/441/240 transcript through `fn-nntp-post-step`. |
| `tests/test_post.py`, `tests/interop_post_nntplib.py` | Raw-socket transcripts and an independent `python3.12` nntplib client. |

Existing books touched, minimally: `books/nntp.lisp` gained one branch in
`fn-nntp-session-command` (POST is archive-free); `books/nntp-responses.lisp`
gained `fn-nntp-begin-article-effect` and `fn-nntp-post-offer`;
`books/nntp-effects.lisp` gained one disjunct in `fn-nntp-effectp`. The
w3/reader-profile lane adds its commands to the same `cond` and the same
`deftheory`; those are the only overlapping lines.

## The shape of the decision

`fn-nntp-step` answers POST with 340 and one `:begin-article` effect and
decides nothing else: it has no configuration argument and no clock. The
existing keystones `fn-nntp-step-effects-well-formed` and
`fn-nntp-step-preserves-consistent-session` now cover that branch with their
statements unchanged (both books re-certified).

`fn-nntp-post-step` is the served function (`host/reader-host.lisp`
`fn-reader-chunk`). It wraps `fn-nntp-step`, returns every non-POST result
unchanged, turns the offer into 440 when posting is not configured, reassembles
the `(:article lines)` event into octets (`fn-post-body-octets`), and calls
`fn-inj-decide`. An acceptance emits no reply — it emits a *submission*. The
host carries that through `durable_post` (the same function `tools/run_store.py
post` now calls) and reports `:durable`, `:refused` or `:uncertain` to
`fn-nntp-post-outcome`, which is the only place 240 exists.

Proved of the composed step: `fn-post-step-preserves-consistent-session`,
`fn-post-step-effects-well-formed`, `fn-post-outcome-effects-well-formed`,
`fn-post-submission-is-an-injected-article`,
`fn-post-refused-body-submits-nothing`,
`fn-post-disallowed-posting-does-not-await`,
`fn-post-outcome-240-only-for-a-durable-observation`.

Proved of injection: `fn-inj-refusal-produces-no-octets`,
`fn-inj-refusal-names-a-reason`,
`fn-inj-injected-article-retains-the-source-octets` (the supplied octets are a
verbatim suffix, which is how §3.5 item 6 holds structurally),
`fn-inj-injected-article-is-within-the-configured-bound`,
`fn-inj-decision-uses-only-the-two-clock-readings`,
`fn-inj-supplied-message-id-is-retained-exactly`,
`fn-inj-supplied-identity-survives-a-different-clock`,
`fn-inj-generated-identity-is-the-clock-identity`, `fn-inj-year-of-inverts`,
`fn-inj-month-of-inverts`, their two injectivity corollaries,
`fn-inj-date-decode-inverts-the-rendering` and
`fn-inj-date-octets-separate-different-instants`.

Two design notes that constrain callers, both stated in `specs/nntp.md`: a
supplied Message-ID gives an exact retry identity and a generated one does
not; and a proto-article carrying Path or Injection-Date is refused rather
than rewritten, which is what makes the verbatim-suffix theorem true.

## Open, recorded rather than weakened

1. `(fn-af-message-idp (fn-inj-generated-message-id obs config))` for every
   valid configuration. Witnessed in `tests/acl2/injection-tests.lisp`, not
   proved: the proof needs `fn-af-msg-id-closep`'s accumulating scan reasoned
   over a five-way concatenation.
2. `(implies (and (natp a) (natp b) (< (floor a 86400000) 146097)`
   `(< (floor b 86400000) 146097) (equal (fn-inj-instant-of a)`
   `(fn-inj-instant-of b))) (equal (floor a 1000) (floor b 1000)))`. The two
   calendar inverse lemmas and the rendering injectivity are proved; this last
   arithmetic step, which would turn "different instant" into "different clock
   reading", is not. Witnessed instead.
3. RFC 5537 §3.5 item 1 (trusted source) and item 3 (the Date/Injection-Date
   freshness window) are not implemented. Item 7 (moderated groups) is out of
   this profile.
4. The greeting is still a fixed 201 and does not vary with the configured
   posting permission; POST is not advertised in CAPABILITIES.

## The host arrangement this lane leaves behind

`tools/run_reader.py --post` takes the **exclusive writer lock** and serves
POST from the same process, because the reader and the store bridge already
share one ACL2 image. A store served with `--post` therefore cannot also be
served read-only by another process, and the served projection is re-selected
(`fn-reader-use-store`, which re-runs the whole-archive recognizer) after each
durable post; a refusal there is fatal to the process rather than served from
a stale snapshot. The mutable-owner lane (C1-05) replaces this whole
arrangement with a separate owner. One clock observation is taken per
connection, so two posts on one connection can carry the same Injection-Date.

## Composition with the served path (2026-09-19, integration lane)

`git merge dev` (d83dea5) into this branch conflicted in `host/reader-host.lisp`
and `tools/run_reader.py`: the served-path lane had rewritten the host around
`books/served.lisp` while this lane had wired POST into the old per-event
`fn-reader-chunk`. The composition, not the union:

- **`books/served.lisp` owns framing and article mode.** `fn-served-step` is
  now a fold over the read's octets (`fn-served-feed`: `fn-wire-feed-byte` per
  byte, which is what `fn-wire-drive` computes by
  `fn-wire-drive-is-feed-proper`), and `fn-served-dispatch` runs
  `fn-nntp-post-step` on each framed event *before the next byte is framed*.
  On the 340 offer's `:begin-article` effect it switches the wire with
  `fn-wire-begin-article`, so the article body is framed in article mode inside
  the same read and comes back as one `(:article lines)` event that the fold
  hands to the injection path. The connection record gained the posting
  configuration and the clock observation (`fn-served-conn-config`,
  `fn-served-conn-observation`), pinned at `fn-served-open archive line-limit
  body-limit config observation`; its session is the `fn-post-session`.
- **A submission is an effect, the outcome is one more input.** An injected
  article leaves the step as `(:submit decision)` (`fn-served-submit-effect`);
  `fn-served-submission` projects it for the host, which carries it through
  `durable_post` and answers with `fn-served-post-outcome conn completion`,
  whose reply is `fn-nntp-post-outcome`'s (`fn-served-post-outcome-effects-by-
  definition`). The host never writes a reply octet.
- **Host.** `host/reader-host.lisp`: one include (`../books/served`; served
  includes `nntp-post`), one open, one step (`fn-served-step`), one outcome
  entry (`fn-reader-outcome` → `fn-served-post-outcome`);
  `fn-reader-install-result` stores the connection opaquely and the
  submission's octets/msgid/groups off `fn-served-submission`.
  `tools/run_reader.py:serve_client` is the served path's one `reader.chunk`
  per `recv` followed by this lane's `submission()`/`owner.accept`/`outcome()`.
- **Theorems.** Every served keystone keeps its name and statement
  (`fn-served-step-preserves-connp`, `-partition-independence`,
  `fn-served-run-is-the-concatenated-step`,
  `fn-served-reply-stream-is-partition-independent`,
  `fn-served-step-nntp-steps-is-bounded`); their proofs now come from
  `fn-wire-feed-byte-preserves-statep`, `fn-wire-begin-article-preserves-
  statep`, `fn-post-step-preserves-consistent-session` and the append law of
  the byte fold, `fn-served-feed-of-append`, which needs no wire lemma at all.
  The one statement that changed: `fn-served-step-effects-are-typed` concludes
  `fn-served-effectsp`, the enumeration with the `:submit` disjunct
  (`fn-served-typed-effect-enumeration-by-definition` reads it off), because a
  submission is not an `fn-nntp-effectp` and saying so would misdescribe the
  dispatcher. Every nntp and nntp-post keystone is untouched.

Open, recorded rather than weakened:

5. The byte fold makes the `fn-wire-octet-listp` hypotheses of
   `fn-served-step-preserves-connp` and `fn-served-step-partition-independence`
   and the `fn-served-connp` hypothesis of `fn-served-step-nntp-steps-is-
   bounded` unnecessary; they are kept as stated and should be deleted with
   the served-tests probes that record them.
6. RFC 3977 section 3.5 forbids pipelining after POST's article until its
   response; a client that does so anyway gets the pipelined replies before
   the 240/441, because the read is consumed whole and the outcome is a later
   input. The session has no awaiting-outcome state to refuse such commands.
7. `fn-served-dispatch` acts on the offer only if `fn-wire-begin-article`
   admits it; after a framed command line the wire is always quiesced, so the
   refused branch is unreachable in the composition and is not a theorem.

Evidence (this worktree, ACL2 8.7 / SBCL, `ACL2_BOOK_HASH_ALISTP=NIL`,
`FN_ACL2_TIMEOUT_SECONDS=1800`): the sixteen dependency books of the served
closure (acceptance-alloc through nntp-effects) recertified in place in
`build/acl2/certify-20260919T235414Z-24220`; then, in one invocation in
Makefile order, `build/acl2/certify-20260919T235949Z-29450` certifies
`books/injection`, `books/nntp-post`, `tests/acl2/nntp-post-tests`,
`books/served`, `tests/acl2/served-tests` and `books/ideal`, every
`assert-event` of the two test books passing under real ACL2 (the POST
transcript 340 / article / submission, the cut inside the body equal to the
whole read, 240 from `:durable` and two distinct 441s, the From-less refusal,
the 440 for a closed configuration). `books/injection.lisp` needed one local
enable of `fn-clock-observationp`, which `books/clock.lisp` withdraws since
8983f24 (the guard of `fn-inj-decide` reads the wall clock through it).
Not recertified here and therefore open on the merged tree:
`books/injection-invariants` and `tests/acl2/injection-tests` (their
certificates are from ca66782; the same local enable is the likely fix).
Python: PYTHON-PENDING
