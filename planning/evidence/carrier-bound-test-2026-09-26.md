# carrier-bound-test (2026-09-26): the oversize-carrier case follows the selected bound

Lane `lane/carrier-bound-test` from dev 2b905687; PKT-485. Found by
keys-and-accounts-3 (classified a dev defect at 7f3e77af: identical on dev
1770d687's image, hbox /tank/fn/scratch/keys-and-accounts-3/classify/).

## The red

`tests/test_native_hybrid_author.py`
`test_portable_carrier_verifies_exact_source_and_keyset` signed a source of
the fixture article plus 26,000 octets and expected `hybrid-sign-carrier` to
exit 1: "the source alone is under the article cap, but adding the required
carrier would exceed it. The ACL2 total bound refuses emission." The image
emits the carrier and exits 0.

## Which side was wrong: the test (option (a))

The selected contract (D27; bounds design 2026-09-25 section 2.3; the P2 and
P4 records):

- `*fn-article-max-octets*` (books/article.lisp:25) is the record codec's
  ceiling, 4,261,412,864, since P2 (ed648b6b, merged 3169d50b). The
  operator's article bound is the Store profile's `max-article-octets`
  (default 32,768), applied at injection.
- The signer reads its source up to `fn-hsig-host-max-source-octets` =
  `*fn-hsig-v2-max-source*` (P4, e2b17943: "the node's article bound stays
  the store profile's, applied at injection") and renders through
  `fn-hsig-host-render-carrier` = `fn-hc-render-at-most
  *fn-article-max-octets*` (host/hybrid-signature-host.lisp:11), the same cap
  `hybrid-verify-carrier` reads (`fn-hsig-host-max-received-octets`).
- The signer is an offline author tool with no Store and no profile
  argument; P4's own large cases (tests/test_fn_verify.py, 60 KiB v1 and
  200 KiB v2) require it to sign past 32 KiB.

So the signer still checks a bound, the codec's, and the ACL2 refusal
(`fn-hc-render-at-most-emitted-bound-by-definition`, books/hybrid-carrier.lisp)
still holds at it. The test's premise, "the article cap" = 32,768, is the
Store profile's default, which the contract decides at the node, not at the
signer. The red therefore dates from P2's merge 3169d50b (after P4's 6166adc1,
`fn-hc-render-at-most` was still at 32,768 and the case passed), not from
carrier v2. No book and no host code changed; no cap was added.

## The fix (test only, plus one spec sentence)

The case keeps its regression, moved to where the contract places the bound:
it reads this Store's bound from `operator CFG status`
(`max-article-octets=N`), asserts the source is within it and the signed
carrier past it (the original premise, now measured rather than assumed),
starts the owner, enrolls the principal, POSTs the carrier and asserts
exactly `441 posting failed; the article exceeds the configured size`
(test_native_owner's oversize line), then POSTs the in-bound carrier with the
same Message-ID and asserts 240 (the refusal stored nothing and was the size
alone) and that the owner is still running. specs/identity.md now says which
cap the signer's render refuses at and that a carrier over a node's profile is
refused by that node.

What no longer holds, stated: the signer does not refuse a carrier some node's
profile would refuse; it cannot know the target node. A signer option naming
the target's bound (fn-hc-render-at-most already takes one) would be a new
feature, not this fix; it is left to a decision, not taken here.

## Native evidence

hbox, `tools/hbox_native.sh --label r1` over this worktree (2b905687 plus
these edits), developer image `tree/build/fn-host-developer` sha256
`f095e7ade8bf306ee3271844cc1366aa2b4e0cb03fc816f80766dd5074097fe7`, with
`--env FN_RUN_HYBRID_E2E=1 FN_TEST_OPENSSL=/tank/fn/toolchains/openssl-3.5.8/bin/openssl
FN_NATIVE_HOST=$T/build/fn-host-developer`: tests.test_native_hybrid_author
whole, **Ran 11 tests in 44.076s, OK, none skipped**, log
`logs/test-tests.test_native_hybrid_author.log` sha256
`84f6e93a60182320815997ea6f01f476dbf5662d6773cdff7d3c26665d773d8d`
(hbox:/tank/fn/scratch/carrier-bound-test/native-r1).

Harness note: the first pass without `FN_NATIVE_HOST` skipped all eleven
("build/fn-host is required"): hbox_native.sh builds `build/fn-host-developer`
and this module defaults to `build/fn-host`. A skipped module reports OK; the
rerun (`--no-build`, same image) set it by hand. No book changed, so no
certification run; `make check-lane` green.

Assurance chain: native entry `hybrid-sign-carrier`
(host/native/signature-command.lisp fnn-command-hybrid-sign-carrier) ->
`fn-hsig-host-render-carrier` -> `fn-hc-render-at-most` at the codec ceiling
(`fn-hc-render-at-most-emitted-bound-by-definition`); the operator bound is
the node's injection bound on the served POST (test_native_owner's oversize
case names its model reply, books/nntp-post.lisp fn-nntp-post-step); observed:
signer exit 0 with the carrier past the Store's 32,768, node 441 size line,
in-bound same Message-ID 240.
