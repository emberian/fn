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

The NNTP lane's initial runs were later reused by its aggregate certification
and had not all been copied into the archive. The following byte-for-byte
copies came from `build/lanes/newnews-stamp/build/acl2/`. At the audit of the
integrated tree, each named passed book had its current source and full include
closure in the manifest. These are the original runs, not new certifications:

| Run | Passed books relevant to the gate | Manifest SHA-256 |
| --- | --- | --- |
| `certify-20260923T165705Z-1918381` | `books/nntp-responses` | `f2523d672d182c3841e10006c7d48d2e208117ed9bbc613f3847b1a469b870b4` |
| `certify-20260923T165752Z-1925070` | `books/nntp`, `books/nntp-legacy`, `books/nntp-overview` | `8b6b7db2cbb03fe73bda8679e6e28da0d967e3b85deaa12880753adb293aef1d` |
| `certify-20260923T170345Z-1979977` | `books/nntp-newnews` | `6899e745ebd033817e63fb99109a7d3087c0c693f06953c2f9cfbe4c80f199d8` |
| `certify-20260923T170527Z-1995317` | `books/nntp-invariants` | `41d20129380381e71b2f90da2568bbab0332dbc32a5eef3c57a0853120d232f6` |
| `certify-20260923T170720Z-2013548` | `books/nntp-effects`, `tests/acl2/nntp-newnews-tests` | `224cb67e2deff913c3690186f7ffee4a7e2f06def491666b2a7a9c6c69f0f0fa` |

The `165752` and `170527` aggregate runs failed on other requested books;
their per-book success markers, certificate digests and exit codes support
only the passed books named above. Their other failures remain recorded.
