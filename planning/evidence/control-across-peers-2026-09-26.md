# control-across-peers (wave 4, lane 11), 2026-09-26

Lane `lane/control-across-peers` from dev `17ff24aa`; brief
`build/coordinator/queue/done/w4-control-across-peers.txt` (PKT-210, PKT-147,
PKT-208, PKT-154; ids PRF-170, NNT-037, SCN-100, PKT-443, PKT-444).

## Summary

- **PKT-210, the two-node matrix: no disagreement.** 48 node observations
  (2 bases x 3 grant placements x 2 orders x 2 kill modes x 2 receivers),
  each the D29 answer, with pinned readers on both nodes and a revoke plus
  SIGKILL that changes no decision.
- **PKT-147: named.** A signed article naming a group the node does not
  serve answers `refused hybrid-author UNKNOWN-GROUP` (exit 1); every other
  refusing arm of the signed-author ingress names its word. PRF-170.
- **PKT-208:** `:control-signed` removed from both reason tables. The
  nil-group-index view is **reachable** (two cancels naming each other) and
  still answers the plain `430 no article with that message-id`: PKT-443.
- **PKT-154:** the BP v3 path files natively; a pre-C1 signed control does
  **not** replay (a fault at open); the repair path is PKT-444.

## 1. The matrix (PKT-210)

`tests/test_native_control_across_peers.py`. Three loopback nodes: H
authors every target and cancel (signed through `hybrid-author`, unsigned
through POST) and the harness fetches their octets before relaying, so it
controls the order in which A and B receive each pair over IHAVE (Path
prefixed with the configured peer's name). P and Q are enrolled on all
three; Q holds `cancel` over `fn.ga.*` on A only, `fn.gb.*` on B only and
`fn.gab.*` on both. Per basis, the twelve cases are {target in fn.ga.t,
fn.gb.t, fn.gab.t} x {target then cancel, cancel then target} x {no kill,
both receivers SIGKILLed and restarted between the two arrivals}. Readers
are opened on A and on B after every first arrival; after the second
arrivals they read every target-first target again, then POST (their 240
re-pins them) and read again. Then every grant is revoked on both nodes and
both are SIGKILLed and restarted.

| Basis | Target group | A (both orders, both kill modes) | B (same) | after revoke + SIGKILL |
| --- | --- | --- | --- | --- |
| author (P cancels P's signed target) | fn.ga.t / fn.gb.t / fn.gab.t | 430 withdrawn | 430 withdrawn | unchanged |
| authority (Q cancels unsigned) | fn.ga.t (grant on A) | 430 withdrawn | 220 | unchanged |
| authority | fn.gb.t (grant on B) | 220 | 430 withdrawn | unchanged |
| authority | fn.gab.t (grant on both) | 430 withdrawn | 430 withdrawn | unchanged |

Pinned readers, both bases, both nodes: 220 for every target seen before
the second arrivals, still 220 after them; after their own POST (240) the
fresh answer. Every relay `335 / 235`. Disagreements: **none**.

The theorems these cases witness are cited, not restated (the host line is
the one C3 names, `fn-own-refresh` through `fn-own-read`):
`fn-ctl-visible-is-arrival-order-independent` (the two orders),
`fn-ctl-cancel-executes-only-for-author-or-authority` (grant placement),
`fn-ctl-pinned-view-keeps-its-archive` (the pinned readers),
`fn-ctl-replay-is-the-fold` and `fn-ctl-revoke-changes-decisions-not-records`
(the kill and the revoke), books/control-authority.lisp.

Two further cases in the module: a cancel naming its own Message-ID is
declined (`(:decline :self-target)`, books/control-authority.lisp
`fn-ctl-withdrawal-plan`): 220 before and after a SIGKILL; and the empty
view (section 3), an expected failure.

Assurance chain: native entry `hybrid-author` / POST / IHAVE -> ACL2 filing
(`fn-owner-control-filing` -> `fn-pa-filing-plan`) and the Store acceptance
-> `fn-own-refresh`'s withdrawal decision under the configuration at the
cancel's txid (`fn-ctl-refresh-withdrawals`, the journal) -> the owner
relation carrying the visible list -> `fn-own-read`'s served answer
(`fn-nntp-withdrawn-article-answers-430-withdrawn`) -> observed 430
withdrawn / 220. Recovery (`fn-cpo-open-observed`, the refresh after
reopen) re-establishes the relation; every refresh preserves it.

## 2. PKT-147: the unserved group, named (PRF-170)

Cause found: the spike's refusal was the **carrier arm** of
`fnn-hybrid-control-author` (host/native/hybrid-control.lisp), whose
`fn-hsig-injected-carrier-octets` runs the injecting agent
(`fn-hsig-injected-carrier-plan` -> `fn-inj-decide`), which refuses
`:unknown-group` for a Newsgroups name outside the configuration's served
groups; the arm returned a bare `:refused`. The inferred fault at the group
code lookup is not reached for an unserved group (the carrier arm refuses
first, before any bound submission). The owner of the decision is therefore
the injection decision, not `fn-own-control-decision`, which is unchanged.

- `fn-hsig-injected-carrier-reason` (books/hybrid-store-injected.lisp): the
  plan's reason; the host calls it when the octets are nil.
- `fn-inj-decide-served-groups-choose-only-unknown-group`: a source admitted
  under a served list G1 is, under G2 (same agent, bound and clock), the
  identical decision when every group it names is in G2, else
  `(fn-inj-refuse :unknown-group)`.
- KEYSTONE `fn-hsig-injected-carrier-unserved-group-is-refused-by-name`
  (`:rule-classes nil`), over the host-called pair: same octets and no
  reason when served; nil octets and `:unknown-group` otherwise. Host line:
  hybrid-control.lisp `fnn-hybrid-control-author`, the `(unless received`
  arm.
- `fn-nhc-author-refusal (arm reason)` (books/native-hybrid-control.lisp):
  the word of each refusing arm (`author-not-enrolled`, `source-malformed`,
  `unknown-group`, `carrier-refused`, `article-exceeds-profile-bound`,
  `control-not-filed`, `control-malformed`, `signed-event-not-formed`);
  `fn-nhc-author-refusal-is-a-named-refusal` (every word a control status,
  class `:refused`, exit 1) and `fn-nhc-author-refusal-names-an-unserved-group`.
  The seven new words are appended to `*fn-nctrl-statuses*` (every earlier
  status keeps its octet). The operator post's words are unchanged.

Teeth: tests/acl2/hybrid-store-tests.lisp (a reachable witness of each
branch with both hypotheses asserted; without the first, posting
disallowed: the reason is `:posting-disallowed` and the `:unknown-group`
assertion must-fail; without the second, a non-name in G2: `:config-invalid`,
must-fail), tests/acl2/native-hybrid-control-tests.lisp (every arm's word,
the reply round trip with codec-attach, two must-fails).

Native (hbox, developer image `f10414e9` at `f9b91cde`):
`test_unserved_group_and_every_refusal_are_named` ok: fn.unserved only,
fn.test,fn.unserved and a cancel naming fn.unserved each `refused
hybrid-author UNKNOWN-GROUP`; fn.test `accepted`; generation 7
`AUTHOR-NOT-ENROLLED`; a damaged ML-DSA signature `SIGNED-EVENT-NOT-FORMED`
(log native-m2-manual-h1.log; its second test errored on the harness's
missing FN_ACL2 and was rerun as manual-bp2).

## 3. PKT-208

`:control-signed` removed from `*fn-pa-served-reasons*`,
`fn-post-store-refusalp`'s list and `fn-post-store-refusal-text` (nothing
produces it since c3, b94f1015; no book depends on the constants' shape);
`fn-post-outcome-store-refusal-kinds-are-distinct` still holds; teeth in
control-tests and nntp-post-tests (it is no longer a served reason; the two
filing words are).

The nil-group-index view: **reachable**. `fn-own-refresh` builds the group
index as `fn-gidx-build` of the visible list, nil when nothing is visible;
`fn-served-conn-pinned-index` then pins the bare trie without the control
pin. A self-cancel does not reach it (declined), but two signed cancels by
one author naming each other withdraw each other, leaving nothing visible:
both answer `430 no article with that message-id` (fresh and after a
SIGKILL; `GROUP control.cancel` 211 0 3 2). Classified: implementation (the
served answer), not fixed here: the fix changes books/served.lisp's pin
shape and what GROUP answers over nil buckets, a served-closure change with
a reader-visible decision; PKT-443 (1). The native case stays with the
served guarantee as its expectation, marked expected failure.

## 4. PKT-154

Reach: `fn-owner-app-plan-install-legacy` is called only from
`fn-owner-app-plan-install` when the recovered request intent is the old
`:request-intent` form, which no current node writes; the lab and every
fresh node take the v3 path (`fn-bpaj-transit-plan` ->
`fnn-owner-attempt-transit`). Run natively on the v3 path:
`test_control_article_over_bp_is_filed_in_its_control_group` ok: without
control.cancel the receiver refuses (exit 1) and nothing is stored; with it,
the article is in control.cancel (211 1) and not in fn.test (211 0). Finding:
the refusal line reads `reason=none` (PKT-443 (2); expected-failure case
`test_bp_filing_refusal_names_its_reason`). Log native-m2-manual-bp2.log.

Pre-C1 replay: the pre-C1 developer image (`19cf7397`, 9ffef4ac's first
parent; image `f358dbac`, core `2a5ddae2`) authored a signed target and a
signed cancel (Newsgroups fn.test) into a fresh store: both stored in
fn.test, control.cancel empty. The current image (`f10414e9`) refuses to
open a copy: `fault operator run ACL2 replay rejected committed transaction
history or configuration history`. Control: the same procedure without the
cancel opens and serves the target. So the clause does not retire: the
refusal is a generic fault; PKT-444 names the repair path (a named refusal,
a migration, or declared unsupported). Script prec1_replay.py (`0f96f871`;
the control-article run used the version before its `ordinary-only`
switch, `5991ec3e`), logs prec1-replay-control.log, prec1-replay-ordinary.log.
The live node was not touched.

## Certification

persvati `run-20260926T102038Z-baf2`, manifest
`planning/evidence/manifests/certify-20260926T102113Z-288651.json`:
`--affected-by` control-authority, control-served, peer-authored-accept,
nntp-post, native-control, native-hybrid-control, hybrid-store-injected;
329 certified, 0 failed, 291 from the cache. This lane's books: hybrid-store-
injected 2.0 s, native-hybrid-control 2.1 s, native-control 2.1 s, nntp-post
4.6 s, peer-authored-accept 9.9 s, their test books 1.2 to 1.7 s. Over ten
seconds, not this lane's books (recertified because nntp-post is below
them): owner-invariants 15.3 s (10.9 s at the last merge certification,
under load both times), public-exposure 10.9 s. The REPL on persvati
(control-across-peers-repl) loaded each changed book and its test book first.

## Native runs and SHA-256

- m1 (dev `17ff24aa`, developer image `aee18e71`, core `3c49c5b2`):
  native-m1-across-peers.log `193dda9c...` (2 tests OK, 25.2 s).
- m2 (`f9b91cde`, developer `f10414e9`, core `8ed4ede6`; production
  `f36b5732`, core `c8048830`): SHA256SUMS in native-m2-SHA256SUMS;
  native-m2-test-tests.test_native_control_across_peers.log `53710d0d...`
  (the self-cancel probe before it became the mutual one: failed, 220);
  native-m2-manual-ev2.log `57e3625f...` (the mutual-cancel view);
  native-m2-manual-m3-across-peers.log `434436f2...` (the module as
  committed: 4 tests, OK, 1 expected failure, 31.1 s);
  native-m2-manual-h1.log `56646c4e...`; native-m2-manual-bp2.log
  `ef1c2748...`.
- prec1: prec1-replay-control.log `1c7b10de...`,
  prec1-replay-ordinary.log `56d8a925...`.

The manual runs used the m2 tree's images with the test files copied in
(tests only; the images are the commit's).

## Not done

- PKT-443: the empty-view answer; the BP refusal reason; the pull side.
- PKT-444: the pre-C1 replay repair (ember's choice among a/b/c).
- A signed control through BP (the BP case above is unsigned; C1 filing is
  by the Control field alone).
