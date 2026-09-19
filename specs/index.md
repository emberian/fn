# Rebuildable group/number index (PRF-010 logical scope)

This integrated logical experiment derives a list of `(group, local-number, message-id)`
entries from the committed `fn-state-articles` memberships. `fn-index-rebuild`
materializes every membership. `fn-index-query-range` scans only that materialized
list and preserves authoritative article/membership order; it never merges local
numbers across groups.

The source membership relation is exposed by `fn-index-entry-sourcedp`.
`fn-index-soundp` requires every returned entry to be a member of the complete
source materialization, while `fn-index-completep` requires every source entry to
be present in the index. These are separate subset directions. The certified
`fn-index-build-sound`, `fn-index-build-complete`, and
`fn-index-build-correspondence` theorems establish both directions for rebuilds.
The range theorem equates the materialized query to an independent
source-membership enumeration. Thus an omitted entry can remain individually
well typed and sound while failing completeness and changing its range.

The public query is total: malformed index, group, or range inputs return `nil`.
Valid calls are guard verified and traverse only the derived index.

This is an executable logical algorithm and proof scope only. It has no persisted
index format or ABI, no host adoption claim, and no physical storage/rebuild or
performance qualification. Source state remains authoritative.
