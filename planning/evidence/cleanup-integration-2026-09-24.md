# Integration after worktree cleanup, 2026-09-24

Source `4b2304b2` combined historical ADVANCE, indexed OVER, allocator-frontier
correspondences, the pure consumer event index and shared poll definitions,
and the human reader's historical server-verdict display. The consumer index
is not yet the called Store/owner poll implementation. The extracted poll
book initially duplicated existing definitions; `a8b349fb` moved the exact
old selector into one shared book before this qualification.

The hbox incremental run `run-20260924T005859Z-9c7d`, gate
`/tank/fn/gates/cleanup-integration-4b2304b2-20260924`, used the existing w28
ACL2 8.7 launcher `/tank/fn/toolchains/w28/acl2-literal-4g`, shared cache and
four jobs. It reused 494 matching certificates and attempted 101 books.
[The original manifest](manifests/certify-20260924T005919Z-653679.json)
records 99 successful attempts and failures in `owner-prepare-correspondence`
and its dependent test. The configured-owner theorem needs the new ADVANCE
result API connected to its existing preservation lemma. No image was built
from this failed qualification.

`make check` passed, and the standalone human-client test suite passed ten
tests. These are distinct from ACL2 certification and native qualification.
The current source still has expensive books: this run measured
`byte-store-record-provenance` at 34.945 seconds, `owner-invariants` at 28.223,
and `owner-config` at 17.001. These are book wall times in this shared four-job
run, not per-event prover times or like-for-like performance regressions.

## Bounded Luna experiments

The reader task produced a working historical verdict display. Root review
found that its first version derived the HDR lookup identity from the article
header, rather than the selected server article. Luna corrected it to query
the selected numeric slot on the same connection and reject a mismatched HDR
row. A separating socket fixture now puts a conflicting Message-ID in the
article header. The correction landed as `0eaef5b2`; ten client tests passed.
The display reports the server's historical verdict, not independent crypto
verification or present authority. This Python client is separate from fn's
native server process.

A second read-only Luna audit of the exact `4b2304b2` books found no further
duplicate top-level named definition events across distinct book files in its
literal include graph. It did not analyze test-book worlds, generated events,
or arbitrary ACL2 macros, and is not an ACL2 world-composition proof. Its
script was temporary and no source was changed.

The [proof-cost trial](owner-config-proof-cost-luna-2026-09-24.md) found a
specific expansion problem but initially produced only failed target attempts.
A failed proof running faster is not a proof speedup. These tasks support using
Luna for bounded client changes and investigation with concrete review; this
small sample does not establish general theorem-development capability.
