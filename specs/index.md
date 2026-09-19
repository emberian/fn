# Rebuildable group/number index (PRF-010 logical scope)

This integrated logical experiment derives a list of `(group, local-number, message-id)`
entries from the committed `fn-state-articles` memberships. `fn-index-rebuild`
materializes every membership. `fn-index-query-range` scans only that materialized
list and preserves authoritative article/membership order; it never merges local
numbers across groups.

`fn-index-soundp` requires every index entry to correspond to an actual
`(group . number)` membership recorded by some article in the source list
(`fn-index-entry-sourcedp`, which scans `fn-article-memberships` directly, never
`fn-index-build`), while `fn-index-completep` requires every such membership of
every source article to appear as an entry in the index. These are separate
subset directions stated against the authoritative memberships, not against the
index build's own output. The certified `fn-index-build-sound` and
`fn-index-build-complete` theorems prove, by induction over the source article
list, that a fresh `fn-index-build` satisfies both directions; an omitted entry
fails completeness and a fabricated entry fails soundness, independent of
whether the rest of the index is correct. The range theorem equates the
materialized query to an independent source-membership enumeration.

The public query is total: malformed index, group, or range inputs return `nil`.
Valid calls are guard verified and traverse only the derived index.

This is an executable logical algorithm and proof scope only. It has no persisted
index format or ABI, no host adoption claim, and no physical storage/rebuild or
performance qualification. Source state remains authoritative.
