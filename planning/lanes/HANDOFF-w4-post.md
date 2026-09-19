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
