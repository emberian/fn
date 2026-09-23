# Archive and closure audit, 2026-09-23

The archived manifest `certify-20260923T160252Z-1438589` came byte for byte
from `build/lanes/acceptance-stamp/build/acl2/` (SHA-256
`ed54a099dc6bf65a43ed9998ec12522a9a2ece3a9d15f419697270c2ed7bdbad`).
The overall run failed, but its per-book records say
`tests/acl2/nntp-post-tests` and `tests/acl2/records-teeth-tests` passed with
fresh success markers, certificate digests, and exit code zero. Their recorded
source and include-closure digests matched the tree at the archive audit.
This is evidence for those books only; the manifest's other failures remain
failures. The independent passed manifest
`certify-20260923T150413Z-82196` came from
`build/lanes/stamp-canonicality/build/acl2/` (SHA-256
`a8198cba2cf77bc63c115b506c47160fb747ffc515a14cff0fc20e5dff64f4e1`)
and also covers `tests/acl2/records-teeth-tests` at that closure. These
manifests are archival copies of completed runs, not new certification.

The two passing Store sequence manifests cited by
`planning/evidence/store-identity-sequence-t4-2026-09-23.md` are also now in
the archive: `certify-20260923T170608Z-2002708` (SHA-256
`e47008654dc70e2b844145d48dd52e08cd87aba40dfff0e9d9eae1a11a37d786`)
and `certify-20260923T170852Z-2027792` (SHA-256
`a71148d89ab88384effe98f0eaf78a227689f763177aecbabd6c971f2e27d0b6`).
These are copies of the qualified persvati results named in that note.

The gate had a separate selection defect. It chose the newest passing run at
the book's own digest before checking dependencies, so a later pass over a
different include closure could hide an earlier pass over the current full
closure. `books/byte-store-observation-scan` exposed this: the archived
`certify-20260923T164920Z-1846190` matched its current closure, while the
later `certify-20260923T165309Z-3945188` had different `books/store-node.lisp`
bytes. The gate now prefers a pass matching the entire current closure and
does not let a later failure over a known different closure refute it. A later
failure at the exact current closure still wins. A failure without enough
closure digests remains a conservative red; a pass without them cannot claim
an exact match. This changes evidence selection only, not the runner's
per-book success criteria.
