# T17 pinned LISTGROUP group buckets, 2026-09-23

`fn-own-read` is the native owner's ACL2 entry point. Its retained connection
archive, Message-ID trie, and group buckets pass through `fn-served-step` to
`fn-nntp-archive-command-pinned`; the LISTGROUP arm selects the group bucket.
The host does not enumerate memberships or decide the answer. An owner refresh
builds the bucket once from the current committed article projection, and an
older connection keeps its historical archive/bucket pair. There is no disk
index or changed acceptance authority.

The keystone `fn-gidx-bucket-of-build` says the selected bucket is precisely
the group filter of the existing `fn-index-build` entries. Under
`fn-nntp-projectionp archive`, `fn-gidx-listgroup-command-of-build` equates the
complete indexed command result, including next session, with the original
archive command. This is not an arbitrary-index theorem: the proof-side
`fn-own-relation` and `fn-served-connp` now carry exact bucket-to-archive
correspondence, preserved by owner build/open/refresh/read traces and served
feed. `fn-own-read-is-served-step-on-pinned-prefix` relates the actual host
entry point to that served call. Other group commands retain their current
archive implementations. The repository's independent proof of
`fn-midx-correspondencep` receives the trie projection of the tagged pin,
not the tagged bundle as if it were a raw trie.

`tests/acl2/owner-tests.lisp` drives an actual committed POST, retains a
version-0 reader, opens a version-1 reader, and sends identical LISTGROUP
range octets through `fn-own-read`. The former is empty and the latter gives
one correctly framed local number. A forged tagged pin retains the correct
Message-ID trie but drops the group bucket: it fails correspondence and
changes the command result. `tests/acl2/group-bucket-index-tests.lisp` covers
crosspost and sparse numbers, empty group, historical prefix, and `must-fail`
attempts dropping the range theorem's article-list, group and bound types and
the full command theorem's archive projection premise.

`fn-gidx-range-work` counts group headers inspected plus selected entries,
at most G + S for G buckets and S selected memberships. A 24-distinct-group
fixture evaluates 2 inspected units for a head bucket against 24 entries in
the flat baseline, a 12-fold difference in that structural count. The bucket
list can still take G header comparisons for a tail group. This count excludes
number sorting and rendering; it is not an elapsed-time or end-to-end
complexity bound. Bucket construction occurs at view refresh, not per query.

Scoped ACL2 8.7 / SBCL 2.6.8 hbox jobs-2 manifests record the source-digest
proofs: group component/test
[`certify-20260923T202914Z-45131.json`](manifests/certify-20260923T202914Z-45131.json),
served book [`certify-20260923T212512Z-190407.json`](manifests/certify-20260923T212512Z-190407.json),
owner and owner-invariant books
[`certify-20260923T220432Z-279598.json`](manifests/certify-20260923T220432Z-279598.json),
owner configuration/TLS dependents
[`certify-20260923T215315Z-256793.json`](manifests/certify-20260923T215315Z-256793.json),
and owner-call test plus the final index test in the cached-green pair
[`certify-20260923T220024Z-271470.json`](manifests/certify-20260923T220024Z-271470.json).
The last test-only source edit adds the complete-command negative attempt;
its focused certification passed in
[`certify-20260923T220135Z-274155.json`](manifests/certify-20260923T220135Z-274155.json).
The first
mixed test run had a wrong expected bucket order in the new cost fixture; that
fixture was corrected, and the subsequent test passed. No native image was
built on this lane. Root still owes combined-source closure and image regression
before a native qualification claim.

`python3 tools/green_check.py --changed-since 4788be6a --summary` reports
18 changed books/test roots green at their source bytes; 39 of 49 inclusive
roots are not green at the merged bytes, largely because independently moving
dependencies are outside this isolated source cut. This is a bounded lane
packet, not a claim that the integrated closure passed. `make check` passed
locally after the registry and generated ledger update.
