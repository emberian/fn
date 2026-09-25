# The signed path: data caps and a quadratic copy (2026-09-25)

Lane `signed-path`, branch `lane/signed-path` from dev `595c8db2`. The
large-article lane left two defects on signed POSTs
(`large-article-2026-09-25.md` §4.3 and §5): three literal data caps in
the kind-4 composite, and a signed ingress that took 47 s at 215 KB.

## 1. The caps

`books/stx-accept-records.lisp` capped the composite's authored source
at 32,768, its article record at 65,538 and the whole composite at
196,608. Past them `fn-hsig-authorized-carried-submission-event-base`
(books/hybrid-store.lisp) returned nil. The node then answered `441
posting failed; the article was refused`, which names no reason.

The new sources of the bounds:

| Bound | Was | Now | Where it comes from |
| --- | --- | --- | --- |
| authored source | 32,768 | `*fn-cbor-max-uint*` (u32) | the v2 carrier's own width. `fn-stxa-authored-source-bound-is-the-v2-carrier-width` equates it to `*fn-hsig-v2-max-source*`. `fn-stxa-holds-every-signable-source` proves every source that `fn-hsig-subject-at-p` admits (v1 up to 65,535, v2 up to u32) fits. |
| article record | 65,538 | `*fn-record-max-octets*` (u32) | the record codec's width (books/records-shape) |
| composite | 196,608 | `(- *fn-cbor-max-uint* 355)` | the u32 frame payload, less the consumer poll reply's 9 header octets and its widest cursor (346), so that `*fn-ncl-poll-max-payload*` is exactly u32 and every composite is a poll report the frame carries |
| CBOR item budget | 65,538 (decode) and 196,608 (encode) | `*fn-stxa-max-item*` = u32 | every item a u32 head can carry. The encoder is `fn-cbor-encode-bounded` and the decoder `fn-stmt-decode-items-bounded`. An item that fit the old budget encodes to the same octets, so the version-0 bytes are unchanged. |

**The operator's bounds.** The profile's A still bounds the received
article at `fn-sbud-post-boundary`, the same call the unsigned path
makes. The profile's R now bounds the encoded composite. The new
function `fn-sbud-signed-event-boundary` (books/store-budget-naming.lisp)
returns:

- `:event` when no composite was formed;
- `:signed-record` when `fn-store-event-encode` of the composite exceeds
  `fn-bs-profile-max-record-octets`;
- `:ok` otherwise.

The host calls it through `fn-owner-signed-event-boundary`
(host/owner-host.lisp) at both event sites in
host/native/owner.lisp `fnn-owner-attempt-transit`: the carried relay
and the authorized event. Both calls come before
`fnn-owner-identity-commit`.

**The refusal names its reason.** `:event` and `:signed-record` are
now in `fn-post-store-refusalp` (books/nntp-post.lisp) and in
`*fn-pa-served-reasons*` (books/peer-authored-accept.lisp). Each has its
own 441 text:

- `the signed article did not form a Store event (event)`;
- `the signed article with its authored source exceeds the configured record size (signed-record)`.

The generic owner-signed-post keystones
(`fn-osp-served-refusal-renders-its-reason` and its transit twin)
therefore cover both words without restatement.

**The publication figure.** `fn-store-publication-ceiling` for
`:accepted-statement` read `*fn-stxa-max-octets*`. That value feeds
`*fn-bs-profile-min-record-octets*` and every profile's budget. It now
reads the named figure `*fn-store-accepted-statement-publication-figure*`,
set to 196,608 like the article figure, so no profile's minimum R and no
budget moves. The figure limits no article: the actual composite is
checked against R above. The history pre-check therefore still uses a
figure rather than the composite's actual size, as the article path
already does. That is recorded as a finding.

### Theorems (every one guard-verified where it is a function)

- `fn-sbud-signed-event-boundary-refuses-exactly-past-the-record-field`
  (KEYSTONE, PRF-016 and PRF-026). For every `fn-stxa-p` event, the
  boundary answers `:ok` exactly when the framed composite is within the
  profile's R, and `:signed-record` otherwise.
- `fn-sbud-signed-event-boundary-ok-is-publishable` (KEYSTONE, PRF-026).
  Hypotheses: the boundary returned `:ok`, the profile is admitted, and
  `count` is a natural below T. Then `fn-bs-publication-admissiblep`
  holds at `(len (fn-store-event-encode event))`.
- `fn-sbud-store-event-encode-of-composite`: for a composite,
  `fn-store-event-encode` is `fn-stxa-encode`. This is proof support and
  is not cited.
- `fn-stxa-holds-every-signable-source` (PRF-048), stated above.
- `fn-ncl-poll-reply-past-the-composite-is-bad` (in the test book): a
  report longer than the composite ceiling is refused before a frame is
  built. It replaces an `assert-event` over a u32-long list, which can no
  longer be built.

No existing theorem statement changed. The recognizer's bounds are
constants, and every proof over them went through unchanged. The image
closure was certified on hbox (build/acl2/certify-20260925T072827Z-2756548,
in the after-tree), and the persvati run is recorded below.

**Teeth.**

- tests/acl2/store-budget-naming-tests.lisp builds a composite past
  every old cap: a 300,000-octet record, a 220,000-octet source, and an
  encoding over 196,608. That composite gives:
  - `:ok` under an admitted operator profile whose R is its exact
    length, and `:signed-record` at R minus 1;
  - `:ok` under the defaults;
  - `:event` for nil;
  - publish-gate admissibility at R, and its refusal at R minus 1.
- One `must-fail` per hypothesis of each keystone, plus evaluated
  counterexamples.
- The stx-accept-records and consumer-local-control tests re-witness
  the composite past the old caps: `fn-stxa-p`, encoding over 196,608,
  an exact round trip through `fn-store-event-decode-exact`, and a poll
  reply that encodes.
- hybrid-store-tests has a 70,000-octet v2 subject for the
  source-bound theorem, and a `must-fail` without its hypothesis.
- control-tests shows `fn-pa-served-word` carries both new words.

## 2. The quadratic

Profiling used sb-sprof at 1 ms on the developer image, with the hook
from the served-path-cost lane.

- **Before** (`fn-host-developer-prof` from 595c8db2, images in
  `base-image.sha256`):
  - the signed 215,386-octet POST: 47,262 of 47,440 samples (99.6%) in
    `ELT`, all under `FNN-CRYPTO-OCTETS` (`post-base-flat.txt`);
  - the first 60 s of `hybrid-sign-carrier` on a 207,861-octet source:
    59,953 of 60,000 (99.9%), the same pair (`sign-base-flat.txt`).
- **The function**: host/native/crypto.lisp `fnn-crypto-octets`, the copy
  of an ACL2 octet list into the `(unsigned-byte 8)` vector that
  libsodium and OpenSSL read. It read element `index` with `(elt value
  index)`. On a list that walks from the head, so one copy of an
  n-octet preimage costs n(n+1)/2 steps: **exponent 2 from the
  definition**.
  - Signing copies the preimage four times: Ed25519 sign, ML-DSA sign,
    and one verification of each.
  - The POST copies it twice: one verification of each.
  - That matches the measured ratios. At 3.1x the size, the POST's time
    grew 9.4x and signing's 9.1x.
- **The fix**: the copy walks a list by its conses, one pass, with the
  same bound check and the same octet check. A vector still goes through
  `elt`, which is O(1) for a vector.
- **No ACL2 twin was needed.** The quadratic was in host raw Lisp, in a
  copy that decides nothing. The ACL2 preimage builder
  (`fn-hsig-signed-preimage-at`, an `append`) is linear: `APPEND2` has 18
  samples. The signed preimage is never digested. Ed25519 and ML-DSA-65
  take the whole message, so the "digest the string" route does not
  apply here. The digests on this path, `fn-hsig-authored-source-id` and
  the received content subject, go through `fn-sha256-stobj` in one
  linear pass.

**After** (the after-tree: this branch's books and host, images in
`after-image.sha256`). The signed 215,386-octet POST is 578 samples.
Whole-value recognizers are what remain:

- `FN-CBOR-OCTET-LISTP` 38.6% total;
- `FN-STXA-P` 29.8%, of which 14.5% is called from
  `fn-store-event-sequence` and `fn-store-event-txid`;
- `FN-RECORD-PAYLOADP` 16%.

All of these are linear (`post-after-flat.txt`, `post-after-graph.txt`).

### Walls (hbox, one run each, plain NNTP unless noted)

| Case | Before | After | Unsigned, same size |
| --- | --- | --- | --- |
| signed POST 74,203 octets (64 KiB body) | 5.07 s, then refused (`441 … the article was refused`) | 0.37 s, 240 | 0.22 s before, 0.27 s after: 1.4x |
| signed POST 215,386 octets (200 KiB body) | 47.45 s, then refused | 0.76 s, 240 | 0.28 s before, 0.34 s after: **2.2x** |
| over TLS: v1 70,040 octets | 4.53 s (large-article) | 0.24 s, 240 | not measured |
| over TLS: v2 215,384 octets | 48.02 s (large-article) | 0.57 s, 240 | 0.15 s: **3.8x** |
| `hybrid-sign-carrier`, 66,678-octet source | 16.03 s | 0.29 s | |
| `hybrid-sign-carrier`, 207,861-octet source | 145.29 s | 0.09 s | |

**The 2x target is not met at 200 KiB.** The ratio is 2.2x on plain
NNTP and 3.8x over TLS. The remainder is the linear revalidation listed
above: the dispatchers `fn-store-event-sequence` and `-txid` run the
full `fn-stxa-p` recognizer to read one field. Carrying the recognized
kind with the event would remove it, and that is a separate packet.

## 3. Native proof (the after image)

- **P4's cases.** Run: `FN_VERIFY_LARGE=1 FN_VERIFY_INIT_FLAGS='--max-article-octets 4194304' python -m unittest -v tests.test_fn_verify`
  (`verify-large.log`). Result: 27 run, OK, 1 skipped (the old-image
  case). Details:
  - `verify-v1-60k` (70,040 octets): 240. HDR is `0 verified 5555… keyring 1`.
    fn_verify exits 0 with carrier-version 1 and 62,515 source octets.
  - `verify-v2-200k` (215,384 octets): 240. HDR verified. fn_verify exits
    0 with carrier-version 2 and 207,859 source octets.
  - `verify-v2-tampered`: `441 posting failed; the author signature does not verify`.
    It is not stored, and fn_verify exits 3.
  - The default-bound run (`verify-default.log`): 27 run, OK, 3 skipped.
- **The named record refusal** (`refusal.log`). The profile is A 220,000,
  G 1, name 64 and R 240,000.
  - The signed 215,386-octet article is within A, but its composite
    (record plus source) is past R. It gets `441 posting failed; the
    signed article with its authored source exceeds the configured
    record size (signed-record)` in 0.17 s. `DATE` then answers on the
    same connection.
  - The 74,203-octet signed article is accepted (240) under the same
    profile.
  - The owner is alive at the end.

## 4. Certification

The hbox image closure (w28 `acl2-literal-4g`, 8 jobs, incremental,
after-tree = this branch's sources) passed: 77 books installed from the
cache and 243 certified (`certify-20260925T072827Z-2756548`), with both
developer images built.

Persvati (w25 `acl2-literal`, 2 jobs, 300 s, `--affected-by` the six
changed books; 447 roots and 604 books, 457 certified):

| Run | Rev | Result | Manifest |
| --- | --- | --- | --- |
| run-20260925T073356Z-fdb1 | 4979f0a3 | 454 of 457 passed, 1,115 s wall. Failed: hybrid-store-tests (a three-argument `<`), consumer-poll-projection-tests (it includes the former), and store-budget-naming-tests (the must-fails ran into `fn-store-event-encode` for 300 s) | `certify-20260925T073426Z-2114563.json` |
| run-20260925T075604Z-779a | 7d299cb6 | the three: hybrid-store-tests 2.4 s and store-budget-naming-tests 5.6 s passed; consumer-poll-projection-tests failed on an assertion pinning the old 196,608 | `certify-20260925T075620Z-2315318.json` |
| run-20260925T075745Z-ff8f | 75c6482b | the full `--affected-by` set again: 447 roots and 604 books. 603 were installed at these bytes from the two runs above and the cache, 1 certified (2.5 s); exit 0 | `certify-20260925T075816Z-2333086.json` |

Books over 10 s at 2 jobs in the first run:

- `owner-invariants` 12.1 s and `store-node-invariants` 11.7 s. Both were
  already over 10 s in earlier runs (large-article: 10.8 and 10.5;
  before that 13.9 and 11.4).
- `config-owner-live` 10.3 s, `native-admin-peer` 10.3 s and
  `peer-inbound` 10.1 s. Of these, only `peer-inbound` includes a book
  this lane changed (nntp-post, whose change is one refusal-text
  branch).

No book this lane wrote is over 10 s. The slowest is
store-budget-naming-tests at 5.6 s.

`books/hybrid-signature.lisp` is unchanged by this lane. By a static
include scan it has 451 dependents across books/ and tests/acl2/. The
changed books' dependents are:

| Book | Dependents |
| --- | --- |
| stx-accept-records | 444 |
| hybrid-store | 443 |
| store-events | 422 |
| nntp-post | 202 |
| store-budget-naming | 16 |
| peer-authored-accept | 4 |

## 5. Findings

- **Whole-value revalidation on the served signed path.**
  `fn-store-event-sequence` and `fn-store-event-txid` (books/store-events)
  dispatch through `fn-stxa-p`, which walks every octet of the record and
  the source to read one integer. Together they are 14.5% of the after
  POST, and the recognizers are about 60% in all. The AGENTS rule "no
  whole-state revalidation on a served path" applies; this is what holds
  the ratio above 2x.
- **The history pre-check uses a figure.** `fn-sbud-verdict-at` presents
  196,608 for kind 4, as it presents 65,538 for an article. A composite
  larger than the figure is admitted by R, and the aggregate history
  check then relies on the publish path's own accounting. This is
  unchanged from before, and it is now reachable, since composites
  larger than 196,608 exist.
- The developer `owner run` path's unnamed 441 (large-article §5) is not
  touched here.

## Logs (planning/evidence/signed-path-2026-09-25/)

| File | sha256 |
| --- | --- |
| prof-base.log / prof-after.log | `2d26226c…` / `118d2072…` |
| post-base-flat.txt / sign-base-flat.txt | `bcbcff06…` / `9fa58642…` |
| post-after-flat.txt / post-after-graph.txt | `80f3bc4c…` / `710c058e…` |
| refusal.log | `04a83abe…` |
| verify-large.log / verify-default.log | `7905fe3a…` / `4c3f13d8…` |
| native-after.log | `0511caeb…` |
| base-image.sha256 / after-image.sha256 | `8b96d720…` / `bf4d0335…` |
| prof_signed.py / refusal_check.py | `b10a184b…` / `4f7f100e…` |
| build-dev.sh / run-prof.sh / native-after.sh | `9cf59012…` / `5a243f82…` / `7e9f92b5…` |
