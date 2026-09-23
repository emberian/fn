# T2b implementation brief: NEWNEWS from durable acceptance stamps

T2b starts after the combined T2a image is frozen.  The selected contract is
[`specs/acceptance-stamp.md`](../specs/acceptance-stamp.md) §2.6 and §3.  The
served subject is `fn-nntp-newnews-response`: native and Python readers call
`fn-served-step`, which reaches it through `fn-served-dispatch`, `fn-auth-step`,
`fn-peer-step`, `fn-nntp-post-step`, and `fn-nntp-archive-command`.  Keep and
recertify `fn-nntp-step-dispatches-newnews-to-the-newnews-response` as that
composition's named dispatch link.

In `books/nntp-responses.lisp`, remove payload parsing by
`fn-nntp-newnews-field-value` and `fn-nntp-newnews-stamp`, the 256-candidate
fuel and its 503 path.  Scan the committed article list once, newest first.
A natural article stamp `s` qualifies when `threshold_ms <= 1000*s`.  A
`:legacy` article uses the nearest later-accepted natural stamp; if none,
the pinned reader observation's whole wall second; if neither exists, it
qualifies at every threshold.  Advance that horizon at every stamped article,
including those outside matched groups.  Emit the Message-ID only when
`fn-nntp-newnews-candidatep` confirms availability at a number in a matching
group.  The scan reads no payload octets.  Keep date/time/wildmat grammar,
501 syntax, 503 for a two-digit year without reader wall, and complete 230
blocks.  There is no NEWNEWS size refusal.  Pessimistic cost for one request
is `O(A * G')` for `A` committed articles and `G'` matched groups, with at
most `C` lines for `C` candidates, bounded by Store `max_transactions`.

Replace the old parse/fuel lemmas in `books/nntp-newnews.lisp` with an
independent quadratic `fn-nntp-newnews-accepted-since` specification and the
keystone equality `fn-nntp-newnews-scan-is-the-acceptance-filter` (soundness
and completeness).  Prove payload erasure, lines at most candidate count,
and clean lines.  Restate `fn-nntp-newnews-block-is-block-text` in
`books/nntp-effects.lisp` without fuel and recertify the session preservation
proof in `books/nntp-invariants.lisp`.  Keep codec openings local to hints.
Certify changed books, teeth and their affected closure incrementally.

Rewrite `tests/acl2/nntp-newnews-tests.lisp` teeth around: boundary second
`T` and `T+1`; malformed/undated 32 KiB payload still included and erasure
equivalence; mixed stamped/legacy horizon; lone legacy with reader horizon
and with no wall; 300 candidate-free articles yielding an empty 230 block.
Remove old 503 budget expectations.  Update `tests/test_reader.py` (undated
seed and header-date expectations), `tests/interop_nntplib.py` (undated
seed), `tests/scenarios/catalog.json`, and `tools/v0_matrix.py`'s
`V0-READ-NEWNEWS`, `-FUTURE`, `-SYNTAX` rows plus new `-STAMP` and `-LEGACY`
rows.  Audit `tools/inn_lab.py` for date-based expectations.  Update the
polling contract in `specs/nntp.md`, NNT-008 in
`planning/requirements.json`, and PRF-052 in `planning/proofs.json`; generate
the ledger.  The DATE-to-NEWNEWS no-miss theorem across a reader pin and an
in-flight prepare is T6 under A-CLOCK, not part of T2b.
