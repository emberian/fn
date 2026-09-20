# Handoff: w9/server-polish

Branch `w9/server-polish` from dev `52eb0db`, worktree `build/lanes/w9-server-polish`.
Certification on **hbox** (`/tank/fn/lanes/w9-server-polish`), per the
coordinator's redirection mid-lane; persvati was at load 11 with fifteen ACL2
processes. One earlier run (`run-20260920T175727Z-82d1`) was left running on
persvati rather than killed.

## What landed

**1. Pipelining after POST (RFC 3977 §3.5).** `books/served.lisp`.
Partition independence already covered byte boundaries. The new content is the
framing boundary POST introduces: `fn-wire-article-event-resumes-command-mode`
says the byte that completes an article leaves the wire in command mode in the
same call, so an octet arriving after the terminator in the same read is framed
as a command. `fn-served-pipelined-read-is-the-sequential-reply` and
`fn-served-pipelined-read-submission-is-the-post-block-submission` compose that
with partition independence; both are corollaries and are named as such in the
audit. Teeth: `tests/acl2/served-tests.lisp`, a transcript where a GROUP
pipelined behind the POST body earns its 211 inside the one read and the
session carries the selected group afterwards.

**2. The greeting (RFC 3977 §5.1.1).** A real defect: `fn-served-open` emitted
a fixed 201 even where the pinned configuration allowed posting, while
`fn-served-open-peer` already varied. `tests/test_owner.py` had expected 200
all along. Fixed; both spellings witnessed.

**3. XPAT (RFC 2980 §2.9).** `fn-nntp-xpat-response`, one dispatcher line.
The bound the earlier deferral asked for was already there: `fn-wildmat-decode`
refuses a target over 497 octets before any DP work. Parity keystone
`fn-nntp-xpat-lines-are-hdr-lines` (a `subsetp-equal`) plus
`fn-nntp-xpat-with-a-total-filter-is-the-hdr-block`.

**4. AUTHINFO and STARTTLS.** New book `books/nntp-auth.lisp` (612 lines
before theorems) with `tests/acl2/nntp-auth-tests.lisp` (418 lines). It has
exactly `fn-peer-step`'s signature and exports the three facts the served fold
needs. Keystones: `fn-auth-gated-command-is-refused-and-not-performed`,
`fn-auth-starttls-is-not-advertised-under-tls`,
`fn-auth-authinfo-is-not-advertised-once-authenticated`,
`fn-auth-second-starttls-is-refused`, `fn-auth-starttls-effect-only-with-382`,
`fn-auth-pass-accepts-only-a-matching-secret`.

**5. The audit matrix.** `specs/nntp-audit.md` gains complete RFC 4643 and
RFC 4642 clause matrices and closes the RFC 2980 XPAT and AUTHINFO rows.
`specs/nntp.md` gains "Transport security, and what is trusted".

Host: `tools/run_owner.py --tls-cert/--tls-key` (implicit TLS at accept, with
`tests/test_owner.py` driving it under a self-signed certificate);
`bin/fn principal set-password`, writing 0600.

## Open, each with its cause and the exact next step

**OB-AUTH-DIGEST.** The credential holds the secret in the clear.
`fn-digest` (`books/crypto-seam.lisp`) is an `encapsulate`d constrained
function with **no attachment**, so it cannot be evaluated; calling it on the
served path would make `fn-served-step` non-executable and the reader would
stop serving. Deriving the digest in Python is refused by the one-owner rule.
Next step: a `defattach` for `fn-digest`, or an ACL2 definition of a real hash.
Owner: the substrate cluster. Nothing in `books/nntp-auth.lisp` changes.

**`books/nntp-auth.lisp` is NOT wired into `books/served.lisp`.** The book is
a Makefile root of its own and certifies (or fails) standalone; the served fold
still calls `fn-peer-step`. The wiring is mechanical and was scoped out when
the lane's ACL2 budget went to the XPAT chain. Exactly:
- `books/served.lisp`: `(include-book "peer-inbound")` -> `"nntp-auth"`;
  every `fn-peer-step` -> `fn-auth-step`; every
  `fn-peer-session-consistentp` -> `fn-auth-session-consistentp`;
  `fn-peer-open-session-is-consistent` -> `fn-auth-open-session-is-consistent`;
  `(fn-peer-open-session archive nil nil nil)` ->
  `(fn-auth-open-session archive nil nil nil (fn-auth-open-config) nil)`;
  `fn-served-open-peer` gains `acfg` and `tlsp` and passes them through;
  `fn-served-post-outcome`'s `(fn-peer-session-base (fn-served-conn-session c))`
  gains an `fn-auth-session-base` inside it; and
  `fn-served-typed-effect-enumeration-by-definition` (`:rule-classes nil`)
  gains the `(fn-auth-starttls-effect)` disjunct.
- A new `fn-served-open-access` taking `acfg` and `tlsp` keeps `fn-served-open`'s
  seven call sites (owner.lisp:591, owner-invariants.lisp:399, owner-tests
  420/452/492, served-tests 67/373) untouched.
No served keystone STATEMENT changes; the proofs need `fn-peer-step` renamed in
their hints, which is what `books/peer-inbound.lisp` already did to
`books/nntp-post.lisp` when it was inserted.

**The owner bridge does not carry the STARTTLS effect.** `fn-owner-chunk`
publishes `fn-owner-closep` and `fn-owner-submittedp`; it needs a third,
`fn-owner-starttlsp`, set from `(fn-served-submission ...)`-style inspection of
the effect list in `host/owner-host.lisp` (`:program` mode, no proof), and
`tools/run_owner.py` then calls `sock = context.wrap_socket(sock, server_side=True)`
after flushing the 382. Until then the only TLS on the wire is the implicit
listener, which is what `tests/test_owner.py` exercises. **AUTHINFO is
therefore not reachable over a socket yet**: the credentials also need to reach
`fn-served-open-access` through the same bridge.

**`fn-served-feed` has one stopping condition.** RFC 4642 §2.2 makes STARTTLS
un-pipelineable and the handshake begin at the first octet after the 382's
CRLF, so octets after the command line in the same read are TLS bytes. The fold
would frame them as NNTP. `tools/run_owner.py` discards the remainder, which
§2.2 permits, but that is a host decision about octets. The fix is a second
stopping condition carried in the connection exactly as the closed wire is; the
effect to key on already exists. Recorded in `specs/nntp.md`.

**SASL (RFC 4643 §2.4) is deferred**, answered 502, never advertised. PLAIN
over a protected channel is USER/PASS with a base64 wrapper and adds no
property fn can state; SCRAM needs OB-AUTH-DIGEST; EXTERNAL needs certificate
material the book does not see.

**`books/nntp-effects.lisp` is open at `fn-nntp-hdr-labelled-line-is-block-text`
on dev** (board, w5/owner-followups, "nntp-effects, FINAL"), not because of
this lane. This lane's XPAT message-id effect lemma was deliberately rerouted
off it: `fn-nntp-xpat-msgid-lines` is its own function and
`fn-nntp-xpat-msgid-block-is-block-text` goes through the clean-field-list
route the range form uses. Nothing new is built on the failing form.

**RFC 4642 §5's 483 for a restricted command on an unprotected connection** is
implemented for AUTHINFO only; `fn-auth-restricted-keywordp` gates on
authentication, not on TLS.

## For whoever picks this up cold

The lane's own farm runs are in `/tank/fn/lanes/w9-server-polish/build/acl2/`
on hbox, newest last. Resubmit with
`python3 tools/farm.py submit hbox --jobs 10 --remote-root /tank/fn/lanes/w9-server-polish --affected-by books/served.lisp --affected-by books/nntp-responses.lisp --affected-by books/nntp-auth.lisp --closure`;
the closure is warm in hbox's cache (184 of 239 installed on the last run), so
a resubmit runs about 55 books. Two defect classes cost this lane three runs
and are worth knowing: `books/nntp-responses.lisp` verifies guards **eagerly**,
so a new `defun` with `:guard t` must carry `:verify-guards nil` and an
explicit `verify-guards` after the HDR block; and a new branch in
`fn-nntp-archive-command` needs a `-preserves-session` rewrite rule plus a line
in the `in-theory (disable ...)` of `books/nntp-invariants.lisp`, or
`fn-nntp-archive-command-keeps-projection` fails after 85 s.
