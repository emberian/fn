# w7/substrate-s1 — the FN-Statement carrier and the verdict

Branch `w7/substrate-s1`, worktree `build/lanes/w7-substrate-s1`, from `dev`
`547fd52`. Packet S1 (and the S2 half that does not need K1's transit path) of
[substrate transport](../../specs/substrate-transport.md); SUB-001, SUB-002;
PRF-019, and PRF-020 in part.

## What landed

- **`books/stx-carrier.lisp`** — the detached encoding as a projection of
  `fn-stmt-encode` (`fn-stx-detached-encode-is-fn-stmt-encode-without-the-payload`
  relates the two literally: the detached octets are the full octets with the
  payload item's octets removed, and nothing below `fn-stmt-encode-items`
  changes); base64 over octets, RFC 4648 §4, alphabet by range rather than by
  table so the two inverse laws are linear arithmetic; `fn-stx-header-value`
  from a statement and `fn-stx-parse-header` back, over one opaque result
  record; and the payload projection by kind — `fn-stx-authored-source`
  subtracts Path, Xref, Injection-Date, Injection-Info, `FN-Statement` and
  `FN-Policy` from the received octets.
- **`books/stx-verify.lisp`** — `fn-stx-verdict (article keyring generation)`,
  total, three-valued, never a refusal; `fn-stx-statement-of` (a function of
  the article alone — no keyring, no peer); `fn-stx-verified-item` rendering
  the HDR `:fn-verified` line, with `fn-stx-verified-item-is-printable` as the
  fact the HDR renderer needs.
- **`books/stx-invariants.lisp`** — S1-1 (`fn-stx-field-round-trip`,
  `fn-stx-field-accepted-input-is-canonical`), the grounding theorem
  `fn-stx-verified-implies-signature-over-own-octets`, `fn-stx-verdict-is-typed`,
  `fn-stx-verdict-records-its-keyring-generation`, and
  `fn-stx-payload-ignores-the-carrier-field`.
- **`tests/acl2/stx-tests.lisp`** — RFC 4648 §10 golden vectors (digest
  independent), a signed article round-tripped through the field and verified
  under the toy realiser, one witness per verdict outcome, and one concrete
  violating value per S1-1 hypothesis.
- **`tools/stx.py`** and **`tests/test_stx.py`** — the host signs, attaches and
  verifies *through an ACL2 session*; no encoder in Python. Exit codes 0/3/4
  keep the three outcomes distinct out to the shell (D13).

## Certification evidence

Farm, persvati, ACL2 8.7. Four runs; the closure (cbor, records,
crypto-seam, statement, statement-invariants, principal, article and the
rest) is certified and cached there.

| Root | State | Evidence |
| --- | --- | --- |
| `books/stx-carrier` | **certified** | `run-20260920T052853Z-b82b`, `build/acl2/certify-20260920T052855Z-*/books--stx-carrier.certify.log`, zero failures |
| `books/stx-verify` | **certified** (w7/substrate-s1-2) | `run-20260920T173829Z-2510`, `build/acl2/certify-20260920T173833Z-1235046` |
| `books/stx-invariants` | **certified** (w7/substrate-s1-2) | `run-20260920T174338Z-6891`, `build/acl2/certify-20260920T174341Z-1287238` |
| `tests/acl2/stx-tests` | **certified** (w7/substrate-s1-2) | `run-20260920T174716Z-9575`, `build/acl2/certify-20260920T174721Z-1322621`, exit code 0 |

Summary of evidence and its limits: `tests/evidence/2026-09-20-substrate-s1.md`.

**w7/substrate-s1-2 closed the three open roots.** Four defects, none a change
of statement: (1) `fn-stx-verified-item-is-printable` needs the renderer's
callees closed and their printability lemmas cited by `:use`, because an open
`fn-stx-decimal-octets` exposes `(revappend d nil)` and the std/lists `rev`
rules turn it into `(rev d)`; (2) `fn-stmt-encode`'s item list closes with a
nil tail, so the detached-encoding theorem met `(append A B C nil)` against
`(append A B C)`; (3) `fn-stx-detached-round-trip` could not reach
`(fn-cbor-valuep (cons :bytes sig))` from `(fn-sig-signature-p sig)` without
both definitions enabled; (4) `fn-stx-detached-accepted-input-is-canonical`
needed the rebuilt signature item `(cons :bytes (cdr (car i1)))` to be the
one-item list `i1` under that branch's own tests. In the test book, ten
`defconst`s that reach an attached function through the toy realiser became
`make-event` (:DOC `ignored-attachment`); no assertion or tooth changed.

`tests/test_stx.py` ran on persvati in
`/home/ember/fn-lanes/w7-substrate-s1-2` with
`FN_ACL2=$HOME/fn-tools/acl2-8.7/saved_acl2`: **5 tests, 0 skipped, OK**.

**PRF-019 and PRF-020 are now `in-progress`**, not `planned` and not closed:
S1-1 and the grounding theorem are certified, and PRF-020's host-line
companion `fn-stx-transit-verdict-is-fn-stx-verdict` still needs K1's transit
path.

**Removed and recorded open, never weakened**: `fn-stx-authored-source-is-octet-list`
and `fn-stx-payload-for-is-octet-list`. They do not follow from
`fn-article-syntax-p`: the projection walks `fn-article-field-raw-lines`,
which `books/article.lisp` constrains to `true-listp` only. Closing them
needs a parser theorem about a parsed article's raw lines, or a projection
written over the unfolded values. The reason is written where they stood.

**PRF-019 and PRF-020 stay `planned`**: S1-1 and the grounding theorem live
in `books/stx-invariants`, which has no certificate.

Five defect classes the farm named, all mechanical, none a false claim:
`true-listp` guards on the article-record accessors (three functions), an
in-induction sextet enable, a missing `len`-of-`append`, a missing `consp`
for the keyring-membership step, and `fn-stx-printablep-of-append` stated as
an equality (false when the first argument is not a true list).

## Three deliberate departures from the design text, each a strengthening

1. **Canonicality is stated about the whitespace-stripped value.** RFC 5536
   §2.2 folding is legal, a 6 kB field will be folded, and
   `fn-article-field-unfolded-value` retains the continuation WSP. So
   `fn-stx-parse-header` strips WSP and
   `fn-stx-field-accepted-input-is-canonical` concludes about
   `(fn-stx-strip-wsp v)`. Every accepted value still has exactly one canonical
   form; what varies is only the folding the RFC already permits.
2. **The canonical form is payload free.** §6's
   `fn-stx-field-accepted-input-is-canonical` has a free `payload` variable and
   re-encodes through `fn-stx-reattach`, which is `nil` unless the ref binds
   that payload — so as written it is false. The book states it over
   `fn-stx-header-value-parts (header, signature)`, which is what the field
   actually carries.
3. **The verdict locates its own payload.** The lane prompt's
   `fn-stx-verdict (fields, located-payload, generation)` would make the
   verdict a function of a caller-supplied value and break "a function of the
   article's own octets". `fn-stx-verdict` takes `(article keyring generation)`
   and calls `fn-stx-payload-for` itself.

## Open, recorded rather than weakened

- **PRF-020 stays `planned`.** The companion
  `fn-stx-transit-verdict-is-fn-stx-verdict` names `fn-peer-transfer`, which
  needs K1's transit path; without it the grounding theorem has no named host
  line, and the assurance rule "the theorem subject is the function the host
  calls" is not met. The grounding theorem itself is proved and is cited in the
  ledger as an event of PRF-020 only when S2 lands the equation.
- **`HEAD` returns `FN-Statement` byte-identical** is half proved here (the
  statement layer has no transition; the field survives the article parser,
  asserted in the test book) and half owed by the nntp cluster: a theorem that
  `HEAD` emits the retained header octets unchanged. Board CHANGE.
- **The `:article` payload projection is this lane's.** w4/post owns the
  injector's side of the same subtraction; when it lands, a named theorem must
  equate `fn-stx-authored-source` with it, or one of the two must go.
- **The 76-column base64 body wrapping** of §1.3 for non-`:article` kinds is
  not implemented: `fn-stx-body-payload` strips WSP and decodes, and CRLF is
  not WSP, so a wrapped body is refused today. S5 or a follow-up adds the
  canonical unwrap.
- **The deployed realiser.** `tools/stx.py` runs under the toy realisers of
  `tests/acl2/crypto-seam-tests.lisp` and says so on every line. Wiring
  `tools/crypto_host.py`'s Ed25519 into an ACL2 verdict needs a digest ACL2 can
  execute; that is D09 and the design lists it as undecided.

## The two hook lines a later packet applies

- **HDR.** `books/nntp-responses.lisp:1322` `fn-nntp-hdr-metadata-tokenp` gains
  `(fn-nntp-keywordp token ":FN-VERIFIED")`, and `fn-nntp-hdr-content`
  (`:1341`) gains a branch returning
  `(list :ok (fn-stx-verified-item <the recorded verdict>))`. The cleanliness
  theorems discharge from `fn-stx-verified-item-is-printable`. No nntp book is
  edited by this lane.
- **Injection.** `books/injection.lisp` `fn-inj-prefix` is where a posting
  principal's `FN-Statement` line is added, on the same path that adds Path and
  Injection-Date — but *before* them in the subtraction sense: the field is in
  `fn-stx-injected-namep`, so adding it anywhere leaves the authored source
  unchanged (`fn-stx-payload-ignores-the-carrier-field`).
