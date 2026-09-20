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
| LIST NEWSGROUPS (§7.6.6) | `fn-nntp-newsgroup-lines` | `name TAB` -- empty description, not an invented one |
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

- `books/nntp-responses`, `books/nntp`: certified locally
  (`build/acl2/certify-20260920T030059Z-55483`,
  `certify-20260920T030112Z-55553`).
- `books/nntp-overview`: certified locally
  (`certify-20260920T030121Z-55594`).
- `books/nntp-invariants`: certified on the farm, run
  `run-20260920T031818Z-2f1d` (`persvati`,
  `build/acl2/certify-20260920T031820Z-1849413` on that host). The two
  keystones are in it with their statements untouched.
- `books/nntp-legacy`, `books/nntp-effects`, `tests/acl2/nntp-legacy-tests`,
  `tests/acl2/nntp-tests`, `tests/acl2/nntp-reader-profile-tests`: **IN
  FLIGHT, no verdict yet.** The explicit-root farm run is
  `persvati:~/fn-lanes/w5-legacy-commands/build/acl2/certify-20260920T032319Z-1893328`
  (`tests/acl2/nntp-teeth-tests` in the same run is already green). Harvest
  it with `ssh persvati 'cd ~/fn-lanes/w5-legacy-commands && grep -n "ACL2
  Error \[Failure\]" build/acl2/certify-20260920T032319Z-1893328/certify.log'`
  and bring the certificates home with `tools/farm.py wait`. Nothing in this
  lane's report claims these five are certified.
- `tests/test_reader.py`, `tests/interop_nntplib.py` and `tests/interop_slrn.py`
  were written but **not run**: each needs a reader process, which needs one
  of the four ACL2 slots.

## Traps this lane paid for

- **The laptop's four ACL2 slots were fully held by other lanes for the whole
  session.** Two local `certify_books.py` runs of `books/nntp-legacy` sat
  queued for over twenty minutes with no `certify.log` -- which looks exactly
  like a looping proof and is not one. Check `~/.cache/fn-acl2-slots` before
  concluding a proof hangs, and go to the farm early.
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
- **slrn.** `brew install slrn` succeeded (1.0.3a_1, under two minutes) and
  `tests/interop_slrn.py` drives it against a running reader in its
  `--create` mode with `--debug`; it was written but not yet run green, so the
  real-client claim is the deploy gate's until it is.
