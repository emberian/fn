# D25: duplicate versus conflict keys on the poster's bytes — 2026-09-24

Lane `d25-dup-conflict` (branch `lane/d25-dup-conflict`, from dev `0e4b318e`).
This record covers the ACL2 change, its certification, and the native
before/after on hbox. The native part is a scratch run under
`/tank/fn/scratch/d25-dup/`. It is not a deployed node, and it is not a
full matrix run.

## The decision, before and after

| | function | compares |
| --- | --- | --- |
| before | `fn-sn-existing-action` (`books/store-node.lisp:65`) | the whole stored payload with the submission, octet for octet, and the groups |
| after | `fn-pb-existing-action` (`books/poster-bytes.lisp:155`) | `fn-pb-poster-bytes` of each (`books/poster-bytes.lisp:145`, the projection `fn-pb-project` at `:115`), and the groups |

The host calls the new function at all four sites that called the old one:
`host/owner-host.lisp:364` (`fn-owner-prepare`) and `:1288`
(`fn-owner-existing-action`, which `host/native/owner.lisp`
`fnn-owner-attempt` and `fnn-owner-attempt-transit` call), and
`host/store-node-host.lisp:472,599`. `fn-sn-existing-action` is kept
unchanged. Editing `store-node.lisp` would have recertified 263 dependents,
and the new decision refines the old one
(`fn-pb-existing-action-refines-the-byte-identity-decision`: the same
Message-IDs are answered, and a byte-identical resend is still a duplicate).

**The poster's bytes.** The projection drops the fields the node injects
(D25): Path, Xref, Injection-Date and Injection-Info. The names are
`books/hybrid-carrier.lisp`'s constants, the same four that
`fn-hc-authored-source` excludes. Each field is dropped with its
continuation lines. The empty line and the body are kept verbatim. The
projection also drops **a Date the node generated**. The poster that sent no
Date gets one from the clock (RFC 5537 §3.5 item 5; `fn-inj-prefix`), and
that Date is as much an injection as Injection-Date is. The v0 matrix posts
without a Date, so dropping only D25's four named fields would have left its
duplicate row timing-dependent. A generated Date is recognised as a Date line
inside the injected block (after an Injection-Date, with no poster field but
Message-ID in between) whose value equals that Injection-Date's value. This
is exactly the line `fn-inj-prefix` writes. FN-Authorship, FN-Statement and
FN-Policy stay in the key: on a served POST the poster supplies them, and
two articles that differ only in a carried signature stay a conflict.

**Scope limit.** A poster's own Date that *opens* the source (before any
field but Message-ID) and equals fn's rendering of the injection second octet
for octet is also read as generated. `fn-pb-opens-with-a-date` excludes this
case from the invariance theorems, and a test shows the key moving there. It
needs a client that renders RFC 5322 dates exactly as fn does (`+0000`, not
`GMT`) in the same second as the injection.

The projection is octet-level and does not call the article parser. The
parser's bounds on header lines and octets make a parse-level projection of
`prefix ++ source` depend on more than the source's parse. The projection
runs only when the Message-ID is already held, over the submission and that
one article, linear in their length. It never walks the store.

## Theorems (`books/poster-bytes-invariants.lisp`)

| theorem | line | statement |
| --- | --- | --- |
| `fn-pb-same-poster-bytes-is-answered-already-stored` | 320 | over `fn-own-outcome` (host: `fn-owner-outcome`) with the word `fn-pb-existing-action` returns: a held article whose poster's bytes and groups are the submission's is answered with the duplicate line, while no completion has been consumed |
| `fn-pb-different-poster-bytes-is-answered-conflict` | 346 | the same with different poster's bytes or groups: the conflict line |
| `fn-pb-a-resent-injection-has-the-same-poster-bytes` | 236 | one proto-article with a supplied Message-ID, injected by `fn-inj-decide` under any two clock readings, has one poster's bytes when it sends no Date or does not open with one |
| `fn-pb-a-resend-at-a-later-second-is-answered-already-stored` | 373 | composition: the held article is the source injected at clock A, and the resend of that source at clock B is answered with the duplicate line |
| `fn-pb-project-of-an-injection-prefix` | 130 | the projection of `fn-inj-prefix ++ source` is the generated Message-ID line (if any) followed by the source's projection, for every date |
| `fn-pb-existing-action-refines-the-byte-identity-decision` | 289 | the answered Message-IDs are the same, and byte-identical is still duplicate |

The two `-by-definition` case equations (lines 265 and 275) are not
registry events.

**Teeth** (`tests/acl2/poster-bytes-tests.lisp`, 17 `must-fail`). The
witness is one source injected by the real `fn-inj-decide` at two clock
readings 37 s apart and committed through the real Store at the first. The
two injected articles are unequal, have one length, and agree once their
Injection-Date lines are replaced. So **only Injection-Date differs**. On
this store, `fn-sn-existing-action` answers the resend `:conflict` (K1) and
`fn-pb-existing-action` answers `:duplicate`. The owner's reply is the
duplicate line. A second witness sends no Date: its two injections also
differ in the generated Date, and the reply is still the duplicate line. One
`must-fail` per hypothesis:

- **Outcome:** no connection with that id, nothing in flight, another
  connection's submission, a consumed completion (uncertain line), no held
  article, different bytes (conflict), and different groups (conflict).
- **Conflict theorem:** same bytes (duplicate), and a consumed completion.
- **Invariance:** a source that opens with a Date equal to clock A's
  rendering; a generated Message-ID; and a refused decision on either side.
- **Prefix lemma:** a source that opens on a continuation line, a source
  that opens with the injection's Date, and a date carrying an LF.

## Certification

The toolchain was persvati `w25/acl2-literal` (identity `1b4169e9…`), run at
2 jobs with `--timeout-seconds 300`. Each run's roots were `books/poster-bytes`,
`books/poster-bytes-invariants`, `tests/acl2/poster-bytes-tests`,
`books/store-node-existing-invariants` and `tests/acl2/store-node-existing-tests`,
which is the `--affected-by` set of every changed book.

| run | source | result | per book | manifest |
| --- | --- | --- | --- | --- |
| `run-20260924T221838Z-a1a2` | `1d489d63` (four-field projection) | passed, 5 of 5 | 2.4 / 4.2 / 3.8 / 2.3 / 2.4 s | [`certify-20260924T221853Z-1225854`](manifests/certify-20260924T221853Z-1225854.json) |
| `run-20260924T222729Z-b599` | `4d9fe411` (current books) | passed; the three changed roots were certified, and the two store-node-existing books were installed at the bytes run a1a2 certified (`e23bb0da…`, `44f506ff…`) | poster-bytes 2.4 s, invariants 4.9 s, tests 4.2 s | [`certify-20260924T222741Z-1305984`](manifests/certify-20260924T222741Z-1305984.json) |

Every changed book is under 10 s. `books/poster-bytes` was also certified on
hbox (w28, `d5f2b9f0…`) for the image. The image closure certified 35 more
books that the hbox cache lacked at dev `0e4b318e`. They are the bp-* books
of the M4 merge, `native-admin`, `native-control`, `consumer-local-control`,
`native-config-observation`, `native-hybrid-control`, `native-operator` and
`topic-history-local-control`, and they all passed
([`image-build.log`](d25-dup-conflict-2026-09-24/image-build.log)).

## Native, hbox

**Images.** Built from `git archive 9cb82454` in
`/tank/fn/scratch/d25-dup/img`, 22:30:52Z to 22:33:29Z
([`img2.sh`](d25-dup-conflict-2026-09-24/img2.sh)). `proof_artifacts.py
acquire/validate --profile default` loaded 121 roots (292 books, artifact set
`87e50b2c…`). Then `build_native_host.sh` ran under `swarm-build` for both
profiles. The four hashes are in
[`image.sha256`](d25-dup-conflict-2026-09-24/image.sha256): `fn-host`
`afdeee2b…`, `fn-host.core` `b7c74362…`, `fn-host-developer` `cb936e79…` and
`fn-host-developer.core` `c699f08e…`.

**The matrix's duplicate-POST rows.** Each run drove the matrix's own
`postcycle` phase, the node-side driver that `tools/v0_matrix.py` ships as
`matrix.py` beside `drive.py`
([`matrix-driver.sha256`](d25-dup-conflict-2026-09-24/matrix-driver.sha256)).
It ran three times, 2 s apart, against one fresh developer owner with the
same Message-ID and no Date, as the matrix posts. The first cycle's POST is
the original. Every later POST, and every cycle's "DUPLICATE" (a fresh
connection that sends the same octets), is a resend. The script is
[`native2.sh`](d25-dup-conflict-2026-09-24/native2.sh).

| image | cycle 1 COMMIT / DUPLICATE | cycles 2 and 3 COMMIT and DUPLICATE (2 s and 4 s later) | owner log |
| --- | --- | --- | --- |
| before: 47bdb9a4 developer | `240` / `441 … a different article with this Message-ID is stored here` (accepted 22:35:39Z, resend 22:35:40Z) | all four: the conflict line | [`pc-before/owner.err`](d25-dup-conflict-2026-09-24/pc-before/owner.err) `24bbc5bf…` |
| after: this branch, developer | `240` / `441 posting failed; this article is already stored here` | all four: `this article is already stored here` (22:35:50Z and 22:35:52Z against the 22:35:48Z original) | [`pc-after/owner.err`](d25-dup-conflict-2026-09-24/pc-after/owner.err) `ba810303…` |

DATE after each duplicate answered `111` on both images, so no clock was
lost. The original `240` was followed by six resends, and every one was
`already stored here`, at 0, 2 and 4 s.

**The NNTP probe's resubmission rows.** This lane tightened the judge
(`tests/campaign/native_nntp_post_probe.py` `_repost_ok`): a repost of a
present article must now be the duplicate line. Before, either line was
accepted.

| run | result | reposts of a present article |
| --- | --- | --- |
| before: the 47bdb9a4 record (`planning/evidence/campaign-47bdb9a4/nntp-probe.json.gz`), re-judged by this judge | 31 of 40 ([`before-47bdb9a4-probe-rejudged.txt`](d25-dup-conflict-2026-09-24/before-47bdb9a4-probe-rejudged.txt) `22de184f…`) | 9 `a different article …`, 9 `already stored here` |
| after: this branch's image pair, `python3 -m tests.campaign.native_nntp_post_probe --images img/build`, 22:33:52Z to 22:34:53Z | **40 of 40** ([`nntp-probe.log`](d25-dup-conflict-2026-09-24/nntp-probe.log) `e564525b…`, [`nntp-probe.json.gz`](d25-dup-conflict-2026-09-24/nntp-probe.json.gz)) | 18 `already stored here`, 0 conflict |

The other reposts were 20 `240` on absent articles, one `From is required`
(a control), and one none (a half-sent article). The hashes of every
harvested file are in
[`SHA256SUMS`](d25-dup-conflict-2026-09-24/SHA256SUMS).

## What this does not show

- It is not a full v0 matrix run, and not the operator campaign of K1. The
  matrix row was driven by its own phase script against one owner, not by
  `tools/v0_matrix.py --backend native-operator` with two peered nodes.
- Transit uses the same decision, so a peer offering an article fn already
  holds with a different Path is now a duplicate (435, 438 or 439) rather
  than a conflict. No transit row was run here.
- `make check` reports the ledger stale. This lane does not edit
  `planning/ledger.*`, so the coordinator regenerates it.
