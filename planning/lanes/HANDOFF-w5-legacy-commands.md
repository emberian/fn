# w5/legacy-commands: XOVER, XHDR, HDR and the LIST variants

Worktree `build/lanes/w5-legacy-commands`, branch `w5/legacy-commands` off
`dev` 7a9e89a. Goal: what slrn, tin and older Thunderbird actually send.

## What shipped

Response builders at the end of `books/nntp-responses.lisp`, one dispatcher
line each in `books/nntp.lisp`, per-command theorems in the new
`books/nntp-legacy.lisp` (between `nntp-overview` and `nntp-invariants`),
transcripts in `tests/acl2/nntp-legacy-tests.lisp` and `tests/test_reader.py`.

| Command | Function the dispatcher calls | Notes |
| --- | --- | --- |
| XOVER (RFC 2980 §2.8) | `fn-nntp-xover-response` | OVER's renderer; 420 for an empty range, no message-id form |
| HDR (RFC 3977 §8.5) | `fn-nntp-hdr-response` | any header, plus `:bytes`/`:lines` |
| XHDR (RFC 2980 §2.6) | `fn-nntp-xhdr-response` | `fn-nntp-hdr-command` with `legacyp` t: 221, 420, message-id label |
| LIST HEADERS (§8.6) | `fn-nntp-list-headers` | `:`, `:bytes`, `:lines`; was 503 |
| LIST ACTIVE.TIMES (§7.6.4) | `fn-nntp-list-active-times` | from `fn-nntp-env-facts`; was 503 |
| LIST NEWSGROUPS (§7.6.6) | `fn-nntp-newsgroup-lines` | `name TAB (no description)` -- a marker, not an invented description |
| LIST SUBSCRIPTIONS (RFC 2980 §2.1.8) | `fn-nntp-list-unmaintained-response` | 503, §2.1.8's own code; slrn sends it every connection |
| LIST DISTRIBUTIONS (RFC 2980 §2.1.4) | `fn-nntp-list-unmaintained-response` | 503, new arm |
| LIST ACTIVE wildmat | already existed | RFC 2980 §2.1.2; now tested and audited |

`fn-nntp-list-command (session archive env args)` is new and is what
`books/nntp.lisp` calls for LIST: the variant keyword is split there so
ACTIVE.TIMES can read the environment without giving `fn-nntp-list-response`
an `env` parameter. The ACTIVE.TIMES arm of `fn-nntp-list-unmaintained-
response` was **removed**, not left unreachable.

## Proved (`books/nntp-legacy.lisp`)

- `fn-nntp-xover-agrees-with-over-on-a-nonempty-range`,
  `fn-nntp-xover-with-no-argument-is-over-with-no-argument`: the legacy
  spelling is the modern one wherever the two RFCs assign the same response.
- `fn-nntp-hdr-content-is-clean`, `fn-nntp-hdr-line-is-a-clean-field`,
  `fn-nntp-hdr-lines-for-numbers-are-clean`,
  `fn-nntp-hdr-numbered-line-is-clean`, `fn-nntp-hdr-labelled-line-is-clean`:
  no HDR line carries TAB, CR, LF or NUL, with no hypothesis.
- `fn-nntp-hdr-of-a-missing-field-is-empty` (RFC 3977 §8.5.2).
- `fn-nov-scrub-is-the-identity-on-a-printable-token`: the XHDR message-id
  label is the client's own octets.
- `fn-nntp-active-times-lines-are-clean`, `fn-nntp-newsgroup-lines-are-clean`,
  `fn-nntp-hdr-field-lines-are-clean`.

Dot-stuffing and the terminating sequence are not restated here: they are
`fn-nntp-step-effects-well-formed` in `books/nntp-effects.lisp`, whose
statement is **unchanged** and now covers these branches through the new
`fn-nntp-effects-*` lemmas. `fn-nntp-step-preserves-consistent-session` is
likewise unchanged; the ten new `-preserves-session` lemmas in
`books/nntp-invariants.lisp` and the global disable that follows them are
what carry the new commands through it.

## Evidence

- ACL2, certified on the current source
  (`build/acl2/certify-20260920T033846Z-34487`, this worktree, one
  invocation): `books/nntp-responses`, `books/nntp`, `books/nntp-overview`,
  `books/nntp-legacy`, `books/nntp-invariants`,
  `tests/acl2/nntp-teeth-tests`. `fn-nntp-step-preserves-consistent-session`
  is in `nntp-invariants` with its statement untouched.
- ACL2, **no verdict yet**: `books/nntp-effects` (which carries the other
  keystone, `fn-nntp-step-effects-well-formed`) and
  `tests/acl2/{nntp-legacy-tests,nntp-tests,nntp-reader-profile-tests}`.
  They were not refused: the invocation above was cut off by its own wall
  clock while three of them were still queued for one of the four ACL2 slots
  (`1560s` of waiting in its log) and `nntp-effects` was mid-proof at
  `fn-nntp-effects-xover-response` with no error of any kind. A detached
  rerun of exactly those four is in
  `build/acl2/certify-20260920T043702Z-30304`, log at
  `<scratchpad>/tail-certify.log`. **Harvest it before believing anything
  about those four**; nothing in this lane claims them.
- `python3 -m unittest tests.test_reader -v`: **14 of 14 pass in 41 s**,
  including the three new raw-socket transcripts
  (`test_legacy_commands_transcript_over_a_real_socket`,
  `test_list_variants_transcript_over_a_real_socket`,
  `test_help_lists_every_dispatched_command`).
- `tests/interop_nntplib.py` under Python 3.12 (`uv run --no-project --python
  3.12`; 3.14 has no `nntplib`): **passed**, now exercising `xover`, `xhdr`
  in the range and message-id forms, `LIST HEADERS`, `LIST ACTIVE.TIMES` and
  `descriptions`.
- `tests/interop_slrn.py`: **passed**. slrn 1.0.3 sent `MODE READER`,
  `XOVER`, `XHDR Path`, `LIST OVERVIEW.FMT`, `LIST`, `LIST SUBSCRIPTIONS`,
  got codes 201/215/412/503 and no 500 or 501, and wrote a newsrc naming
  `fn.letters`.

## Two findings the probes produced, and what changed because of them

- **An empty LIST NEWSGROUPS description makes the group disappear.** Python
  nntplib strips the line and then requires name + white space + text, so
  `fn.letters TAB` is dropped from `descriptions()` rather than mapped to
  `""`. The description is now the fixed marker `(no description)`.
- **slrn sends LIST SUBSCRIPTIONS on every connection.** It was answered
  `501 unsupported LIST variant`; RFC 2980 §2.1.8's own response list is 215
  or 503, so it is now `503 data item not stored`, like DISTRIBUTIONS.

## Traps this lane paid for

- **A queued certify and a looping proof look identical.** The laptop's four
  ACL2 slots (`~/.cache/fn-acl2-slots`) were fully held by other lanes; a
  queued `certify_books.py` writes its evidence directory and `version.log`
  and then waits with NO `certify.log`. Check the slot directory first. When
  the run finally started, `books/nntp-legacy` really was over budget too, so
  both diagnoses were live at once: `ld` on a two-line driver found the form
  in 3.35 s, which certification could not have told us in half an hour.
- **`certify_books.py` does not recertify a stale dependency.** Naming
  `books/nntp-effects` after editing `books/nntp-responses` fails at
  `include-book` with a book-hash mismatch and reports nothing about the
  book you changed. Name the whole chain on one invocation.
- **Three proofs in `books/nntp-legacy.lisp` blew the 2,000,000 step limit
  and all three for the same reason**: a goal that mentions a renderer twice
  (`fn-nntp-xover-range` against `fn-nntp-over-range`) or once inside an
  induction (`fn-nntp-active-times-lines`) must keep every sub-term closed.
  `e/d` the two top functions open and disable the range walk, the overview
  fold, `fn-nntp-decimal-field`, `fn-nntp-string-octets`, the seconds
  conversion (it drags in `floor`) and `fn-nntp-group-factp` (it drags in
  `fn-clock-observationp`). Each then proves in under a second.
- `tools/farm.py --remote-root ~/...` expands `~` **locally**. persvati is
  Linux (`/home/ember`), the laptop is macOS (`/Users/ember`), so the rsync
  fails with `mkdir ... No such file or directory` and a stack trace. Pass an
  absolute remote path: `--remote-root /home/ember/fn-lanes/<lane>`. The
  remote directory must also exist first (`ssh persvati mkdir -p`).
- `--affected-by books/nntp.lisp` did **not** pick up the newly added root
  `books/nntp-legacy`, although it is in the Makefile list and its closure
  contains `books/nntp.lisp`; `books/nntp-effects` then failed on
  `(include-book "nntp-legacy")` with "no certificate on file". Name a brand
  new root explicitly on the submit line.
- A `verify-guards` at the end of `books/nntp-responses.lisp` must come after
  its callees': `fn-nntp-list-unmaintained-response` failed for want of
  `(verify-guards fn-nntp-list-headers)` two lines earlier.
- `fn-nntp-list-response-preserves-session` disables the whole responses
  vocabulary and re-enables exactly six LIST functions by name. A new
  function called from `fn-nntp-list-unmaintained-response` must get its own
  `-preserves-session` lemma **and** a global disable, or that theorem breaks.

## Open

- **LIST ACTIVE.TIMES is empty on the served path.** `books/nntp-post.lisp`
  builds `(fn-nntp-env observation nil)`, so the served connection has no
  creation facts. The stamps exist: they are in the node's configuration,
  reachable as the created stamp of each entry of `(fn-cnode-config cn)`
  (`books/node-config.lisp`, w5-config-groups). Wiring them into the served
  conn is the mutable-owner lane's, and it is the same seam NEWGROUPS needs.
- **LIST NEWSGROUPS descriptions.** The group table has no description field.
  R5 should add one; until then the description is empty and the audit says so.
- **XPAT (RFC 2980 §2.9) is deferred with a reason**, not merely unimplemented:
  fn's wildmat matcher is specified and bounded for group names, and pointing
  it at an arbitrary header value needs the UTF-8 decode and the DP target
  bound re-argued. XGTITLE, XINDEX, XROVER and XTHREAD are deferred;
  XPATH is refused permanently (it would expose the store layout).
- **slrn's own UI was not driven.** The probe stops at the group list: slrn
  opens a full-screen buffer and waits, so article reading, threading and
  posting through a real client are still unexercised. tin and Thunderbird
  are untried. One client at one version is not an RFC audit.
