; The reclaim-aware history invariant (books/filed-history.lisp
; FN-O1-FILES-INVP) carried through the owner's lifecycle beyond the Store
; transitions: the arena's release of unnamed handles, the fresh handle of an
; intern then stage, the content-reclaim swap (which rewrites payloads to
; tombstones and keeps groups), reopen from the full journal and from a
; checkpoint, and the catalog every install loads.  Each keystone premises
; filed-or-reclaimed articles, never filed-only: a legitimate reclaim makes
; the filed-only form false, and the served path already refuses a reclaimed
; article (FN-NNTP-ARTICLE-TOMBSTONEP) where the header fact would fail.

(in-package "ACL2")

(include-book "filed-history")
(include-book "arena-forget")
(include-book "owner-reclaim-pass")
(include-book "owner-reclaim-seal")
(include-book "store-checkpoint-arena")
(include-book "owner-checkpoint-open")
(include-book "history-pages-owner")
(include-book "served-catalog-owner")
(include-book "catalog-availability-owner-load")
