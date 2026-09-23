# T17 group bucket component, 2026-09-23

`books/group-bucket-index.lisp` builds ordered group buckets from the existing
`fn-index-build` membership entries. It makes no new local-number decision.
`fn-gidx-bucket-of-build-entries` proves each bucket is exactly the filter of
those entries for its group. Under `fn-article-listp configured articles`,
string group, and natural range bounds,
`fn-gidx-range-of-build-equals-archive-fold` proves its range answer equals
the current NNTP archive fold through `books/nntp-index.lisp`'s existing
correspondence. The test has a crosspost, sparse numbers, an empty group and
an older pinned prefix; `must-fail` attempts remove each theorem hypothesis.

This component checkpoint is superseded for the actual served path by
[`t17-group-bucket-served-2026-09-23.md`](t17-group-bucket-served-2026-09-23.md).

`fn-gidx-range-work` counts the bucket headers inspected plus selected
entries visited. `fn-gidx-lookup-work-at-most-bucket-count` proves the first
term is at most the number of distinct buckets. This is a structural count,
not elapsed time or a claim about the served path. Building buckets traverses
the archive-derived entries and is intended for view refresh/open, not a
command. The actual served LISTGROUP switch and pin maintenance remain open
after this component checkpoint.

Hbox ACL2 8.7 run `run-20260923T202908Z-d8bd`, manifest
[`certify-20260923T202914Z-45131.json`](manifests/certify-20260923T202914Z-45131.json),
passed the new book and its test with jobs 2, exact per-book source digests and
toolchain identity recorded in the manifest.
