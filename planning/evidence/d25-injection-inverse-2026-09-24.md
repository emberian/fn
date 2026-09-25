# D25: the injection inverse, and RFC 5537 §3.5 item 11 — 2026-09-24

Lane `d25-injection-inverse` (branch `lane/d25-injection-inverse`, from dev
`19709182`). It covers outcome A of the next cycle, "normal posting has stable
retry semantics" (planning/review-2026-09-24-gpt6-direction.md, D25). It
replaces the four-field projection of lane `d25-dup-conflict`. The native part
is a scratch run under `/tank/fn/scratch/d25b/`. It is not a deployed node,
and it is not a full two-node matrix run.

## The comparison, as implemented

Three values are kept apart: the poster's source, the accepted record (the
source with its injected block), and a relayed projection (not used here).

- **Injection recipe v2** (`books/injection.lisp:628` `fn-inj-prefix`). The
  block is the Path line. Then, when anything is generated, come
  Injection-Date, the generated Message-ID and the generated Date, in that
  order. The Injection-Info line comes last and closes the block. Every octet
  after it is the poster's.
- **The inverse** (`books/injection.lisp:712` `fn-inj-source-of`, `:696`
  `fn-inj-source-after-stamp`). It returns `(t . source)` or nil. It reads
  which fields were generated from the block and returns the octets after
  the block. A recipe v1 record (before this lane: Path, Injection-Date,
  Injection-Info, generated lines, source) is recognised by its Injection-Info
  line directly after the Injection-Date line, which v2 never writes. It is
  read only where v1 is unambiguous. When the octets after its Injection-Info
  line open with a Date line of the injection's date, or with the record's own
  Message-ID line, the inverse gives nil. `fn-inj-reinjectionp` (`:733`), the
  operator retry test, is now exactly this inverse.
- **The decision** (`books/poster-bytes.lisp:80` `fn-pb-existing-action`,
  through `:64` `fn-pb-same-articlep` and `:55` `fn-pb-subject`). The
  submission's agent is read from its own Path line (`:43`
  `fn-pb-path-agent`), and the held article is read under that agent. When
  both articles give back a source, the sources are compared, and the groups
  too. Otherwise the payloads are compared octet for octet. This covers
  another agent, a relayed copy and an ambiguous v1 record. Nothing is
  dropped from either side. The Store comparator `fn-sn-existing-action` is
  unchanged. The host call sites are unchanged too: `host/owner-host.lisp:364,1328`
  and `host/store-node-host.lisp:497,624`.

**The provenance decision.** The prefix shape determines what was generated.
No field is added to the Store record. The record's own octets carry the
provenance, and `fn-inj-source-of-inverts-the-injection` is the proof. That
theorem covers every clock reading and all four generated-field cases.

## RFC 5537 §3.5 item 11

| case | RFC | fn | theorem (`books/injection-invariants.lisp`) |
| --- | --- | --- | --- |
| Injection-Date supplied | MUST NOT be modified or replaced | **refused**, `:injection-date-present`. This is a local acceptance policy, not an RFC requirement: nothing is modified when nothing is injected. The reasons are that §3.5 item 3 would have fn judge that date's age with no date-time parser, and that fn's generated Date is recognised against the Injection-Date fn wrote | `fn-inj-a-supplied-injection-date-is-never-replaced` (:867) |
| Date and Message-ID both supplied | MUST NOT add an Injection-Date | none added: the article is the Path line, the Injection-Info line and the source, at every clock reading | `fn-inj-no-injection-date-when-date-and-message-id-are-supplied` (:881) |
| otherwise | MUST add one with the current time | added, carrying this clock reading's date, directly after Path | `fn-inj-injection-date-is-the-clock-otherwise` (:912) |

Before this lane, fn added an Injection-Date unconditionally. That violated
the second case.

## Theorems

`books/injection-invariants.lisp`:
- `fn-inj-source-of-inverts-the-injection` (:811), the keystone. It uses
  `fn-inj-injected-octets-are-the-block-and-the-source` (:783) and
  `fn-inj-injected-article-is-a-reinjection-of-its-source` (:843, re-proved).
- `fn-inj-source-of-a-v1-record` (:741) and
  `fn-inj-source-of-an-ambiguous-v1-record` (:762).

`books/poster-bytes-invariants.lisp`. The first four are over `fn-own-outcome`
with the word `fn-pb-existing-action` returns:
- `fn-pb-a-resend-at-any-clock-is-answered-already-stored` (:318). One source
  injected at clocks A and B, under one Message-ID and one set of groups, gets
  the duplicate line. There is no hypothesis on the Date.
- `fn-pb-a-changed-source-is-answered-conflict` (:350). A different source
  under the held Message-ID gets the conflict line. That covers one changed
  authored byte and an authored Date changed or removed.
- `fn-pb-same-article-is-answered-already-stored` (:266) and
  `fn-pb-different-article-is-answered-conflict` (:291).
- `fn-pb-an-existing-action-writes-nothing` (:384). Whatever
  `fn-pb-existing-action` answers, the outcome leaves the owner's Store and
  feeds as they were and writes no outcome record. The held record and its
  local number stay, and no second obligation is written.
- `fn-pb-one-source-at-two-clocks-is-one-article` (:122) and
  `fn-pb-two-sources-are-two-articles` (:142).
- `fn-pb-a-v1-record-is-read-under-v1` (:179) and
  `fn-pb-an-ambiguous-v1-record-is-compared-exactly` (:202).
- `fn-pb-existing-action-refines-the-byte-identity-decision` (:227).
- The `-by-definition` equations (:214, :239) are not registry events. :239 is
  the new-Message-ID row: a Message-ID the Store does not hold is never
  answered from the Store.

**Teeth.** `tests/acl2/poster-bytes-tests.lisp` has 13 `must-fail`s and
ground witnesses through the real Store and owner. The rows are these:
- Date present and Date absent at two clocks 37 s apart. The byte decision
  says `:conflict` for the Date-less resend, and this one says `:duplicate`.
- A changed byte, a changed Date and a removed Date.
- A poster's Date equal to the one fn generated at A. It is a conflict, never
  ignored. The old projection's scope limit is gone.
- Another agent, which is compared as octets.
- A v1 dated record read back, and a v1 generated-Date record compared as
  octets.
- A new Message-ID.
- One `must-fail` per outcome hypothesis: connection, in-flight, other
  connection's, consumed, held, same source, groups.

`tests/acl2/injection-tests.lisp` adds 4 `must-fail`s, the four inverse cases,
item-11 witnesses on the INN lab's own article, and the lab's actual v1 octets
read back. `tests/acl2/owner-operator-tests.lisp` now expects the v2 octets.
Its clock-separating witnesses use a Date-less article, because a dated one no
longer depends on the clock.

## Certification (persvati, `w25/acl2-literal`, identity `1b4169e9…`, 2 jobs, 300 s)

`--affected-by books/injection.lisp` has **416 roots** (429 books with
uncached dependencies).

| run | source | result | manifest |
| --- | --- | --- | --- |
| `run-20260924T230752Z-fb60` | `eee4f54a` | 427 passed, 2 failed (`books/poster-bytes-invariants` and its tests; `fn-pb-path-agent-of-a-path-line` lacked `fn-inj-strip`) | [`certify-20260924T230829Z-1666590`](manifests/certify-20260924T230829Z-1666590.json) |
| `run-20260924T235558Z-82c1` | `d5844754` | timed out at 300 s in `fn-pb-path-agent-of-an-injection`, which opened the parser (536 s in the REPL) | [`certify-20260924T235616Z-2086986`](manifests/certify-20260924T235616Z-2086986.json) |
| `run-20260925T001140Z-0021` | `0e23ee53` | **passed**, 2 of 2 | [`certify-20260925T001158Z-2227754`](manifests/certify-20260925T001158Z-2227754.json) |

The two books run 1 failed are the only books that changed afterwards. So
runs 1 and 3 together cover the whole `--affected-by` set at `0e23ee53`.
Every book this lane touched is under 10 s: injection 0.6 s,
injection-invariants 1.3 s, injection-tests 0.8 s, poster-bytes 2.3 s,
poster-bytes-invariants 3.9 s, poster-bytes-tests 3.9 s and
owner-operator-tests 4.7 s. Two untouched dependents are at their usual
~10 s: owner-invariants 10.2 s and store-node-traces 10.3 s.

## Native, hbox (scratch `/tank/fn/scratch/d25b/`)

**Image.** Built from `git archive eee4f54a`, whose `books/` and `host/`
content equals the head's for the image closure. Only
poster-bytes-invariants changed after it, and that book is not an image
root. The build ran from 23:14:48Z to 23:19:40Z
([`img.sh`](d25-injection-inverse-2026-09-24/img.sh)), incremental over
`/tank/fn/certcache` with w28. It produced `fn-host-developer` `d1038649…` and
`fn-host` `38953f01…` ([`image.sha256`](d25-injection-inverse-2026-09-24/image.sha256)).

**The review's matrix**, [`d25b_matrix.py`](d25-injection-inverse-2026-09-24/d25b_matrix.py).
The result is **21 of 21**
([`matrix.log`](d25-injection-inverse-2026-09-24/matrix.log) `d1f7e014…`,
[`mx2/rows.json`](d25-injection-inverse-2026-09-24/mx2/rows.json) `1cf698f2…`).

| row | reply |
| --- | --- |
| U1 Date present, resend 1.2 s later | already stored here; the group count is unchanged |
| U2 Date absent, resend 1.2 s later | already stored here |
| U3 one changed authored byte | a different article … |
| U4 authored Date changed / U5 removed | a different article … |
| U6 identical text, new Message-ID | 240; the group goes from 2 to 3 |
| S1 signed (FN-Authorship carrier), resend | already stored here |
| S3 signed, changed byte, same Message-ID | a different article … |
| S2 signed, Date absent | `hybrid-sign-carrier` refuses the source ("outside the portable FN-Authorship profile"), so every signed row carries a Date |
| R1 POST without reading the reply, SIGKILL the owner, restart, retry | already stored here; the group count is 5 before the kill, 5 after the restart and 5 after the retry |
| R2 / R3 Date-absent and signed resends after the restart | already stored here |
| I1 / I2 after `policy set path-identity other-agent.example.invalid` | a different article … (another injecting identity is compared as octets, never widened) |
| V0 → V1 v1 record (written by the d25-dup image `/tank/fn/scratch/d25-dup/img/build/fn-host-developer`), Date present, resent on this image | already stored here (read under v1) |
| V0 → V2 v1 record, Date absent (a generated Date line where the source begins) | a different article … (ambiguous under v1, compared as octets) |

Owner logs: [`mx2/owner-*.err`](d25-injection-inverse-2026-09-24/mx2/).

**The matrix's duplicate rows.** The matrix's own `postcycle` phase ran three
times, 2 s apart, against one fresh owner on port 11396
([`native.sh`](d25-injection-inverse-2026-09-24/native.sh); drivers in
[`matrix-driver.sha256`](d25-injection-inverse-2026-09-24/matrix-driver.sha256)).
Cycle 1 answered COMMIT 240 and DUPLICATE "already stored here". Cycles 2 and
3 answered "already stored here" for both COMMIT and DUPLICATE, and the group
count stayed 1 ([`pc-after/pc1-3.json`](d25-injection-inverse-2026-09-24/pc-after/)).

**The NNTP probe.** `python3 -m tests.campaign.native_nntp_post_probe --images img/build`
ran from 23:59:34Z to 00:00:37Z. It gave **40 of 40**, with 18 of 18 reposts
of a present article answered "already stored here" and 0 conflicts
([`nntp-probe.log`](d25-injection-inverse-2026-09-24/nntp-probe.log) `e564525b…`,
byte-identical to the d25-dup record's, and
[`nntp-probe.json.gz`](d25-injection-inverse-2026-09-24/nntp-probe.json.gz)).

Hashes of every harvested file are in
[`SHA256SUMS`](d25-injection-inverse-2026-09-24/SHA256SUMS).

## What this does not show, and findings

- **Transit is back to octet equality.** A relayed copy whose Path differs
  from the held one is a conflict again (the transit refusal at
  `host/native/owner.lisp:836`), as before D25. d25-dup had made it a
  duplicate through the four-field projection. A relay projection (Path and
  Xref only, RFC 5537 §3.6) belongs to the relayed-workflow outcome. No
  transit row was run here.
- **Changing path-identity makes every earlier post's resend a conflict**
  (rows I1 and I2). This is by design: never widen across injecting
  identities. Operators should know it.
- **v1 records posted without a Date answer conflict on resend after the
  upgrade** (row V2). The deployed node's store holds such records. Retries
  that straddle the upgrade will be told "a different article". That is the
  strict reading the review asked for, and it only affects retries across the
  upgrade.
- **An article that supplies Date and Message-ID now has no Injection-Date.**
  NEWNEWS and peers that key on Injection-Date fall back to Date (RFC 5536
  §3.1.1, `437 … no Injection-Date or Date`). No such row was run.
- **A Date-less signed source is outside the FN-Authorship profile.** Signed
  retries are always Date-present, so they are byte-identical.
- This is not a full two-node `tools/v0_matrix.py` run, and it is not the
  operator campaign.
- `make check` will report the ledger stale. This lane does not edit
  `planning/ledger.*`.
