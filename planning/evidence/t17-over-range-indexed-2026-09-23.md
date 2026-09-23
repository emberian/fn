# T17 pinned OVER/XOVER range lookup

At the source represented by hbox ACL2 8.7 manifests
`certify-20260923T232820Z-480447.json` and
`certify-20260923T233149Z-493160.json` (toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`),
the actual `fn-nntp-archive-command-pinned` takes valid one-argument OVER and
XOVER numeric ranges through `fn-nntp-over-range-indexed`. The host's
`fn-own-read` reaches that dispatcher through the carried served/auth path;
no owner, view or connection field was added.

`fn-gidx-number-article-of-build` proves that a valid article list's built
group bucket and Message-ID trie resolve a local number to the same first
article as `fn-nntp-available-article`. The proof carries the RFC local-number
and renderable Message-ID gates, and uses accepted article-list uniqueness for
the trie step. `fn-nntp-over-range-indexed-equals-fold` equates the complete
response under a valid accepted state, typed session, and parsed natural range
bounds. `fn-nntp-parse-range-ok-has-natural-bounds` discharges the parser
premise. The called-subject theorem
`fn-nntp-carried-over-range-equals-archive-command` adds the actual maintained
bucket and trie correspondence for a tagged pin and proves the pinned archive
dispatcher equals the original archive command for valid OVER/XOVER ranges.
XOVER's empty range remains 420; OVER's remains 423. The command does not
evaluate either whole-archive correspondence predicate at serve time.

The selected bucket is found once. With G bucket headers, M entries in that
group, S selected output numbers and maximum Message-ID length L, the
structural work outside article rendering is O(G + M + S·M + S·L + S²): the
existing insertion sort remains quadratic. The old response searched A
archived articles for every one of S numbers, O(A + S·A + S²). This is a
structural count, not a wall-time measurement or tree range claim. Opaque
article payload rendering retains the existing bounded parser/refusal policy.

The new test book constructs sparse numbers 2 and 100, a crosspost, an
unrelated group, and an older pinned view. It checks the actual pinned step
against the original step, both empty-range codes, and concrete wrong-answer
counterexamples for stale buckets and a missing trie. Each counterexample is
paired with a `must-fail` theorem after the corresponding relation is
removed. The final assertion edit passed in the otherwise red mixed run
`certify-20260923T232942Z-484654.json`; that run failed downstream at the
new effect-typing branch. `fn-nntp-effects-over-range-indexed` and the
archive-command effect proof then passed, and the affected `nntp-auth`,
`peer-inbound`, `served` and `owner` roots passed in
`certify-20260923T233149Z-493160.json`. The combined root/image and native
socket workload remain to be qualified after integration. HDR/XHDR, GROUP,
NEXT, LAST, and NEWNEWS retain their archive folds.
