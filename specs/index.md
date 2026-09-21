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

## Host adoption: a generation-bound cache (C1-09)

`books/nntp-index.lisp` adopts the index above as a cache for the NNTP number
projection. `books/nntp.lisp` answers GROUP with three single-pass folds over
`fn-state-articles` (`fn-nntp-group-count`, `-low`, `-high`), LISTGROUP with a
fourth (`fn-nntp-group-range-numbers`), and NEXT/LAST with
`fn-nntp-group-next-number` / `-last-number`. Each has an index-backed twin
that traverses only the materialized entries, and each twin is proved equal to
the fold it replaces whenever the article list is consistent:
`fn-nntp-index-group-count-equals-fold` and its five siblings, all citing
`fn-index-range-query-correct` through
`fn-nntp-index-numbers-of-query-range`. The equality is what licenses a call
site to change; no separate performance argument is part of it.

The cache is bound to a generation and a configuration. `fn-nntp-index-cache-open`
tags a fresh `fn-index-build` with the generation the archive was recovered at
— the store's durable record count — and with `fn-nntp-index-config-digest`,
which ACL2 computes from the archive's group list, watermarks and article
count. `fn-nntp-index-cache-query` answers only when the caller's generation
and digest both equal the cache's; otherwise it returns `(:stale)`, a result
distinct from every answer. A query kind the cache does not serve returns
`(:unknown)`. `fn-nntp-index-cache-open-answers-group`, `-cursor` and `-range`
state that its `:ok` answers are the corresponding `books/nntp.lisp` folds over
the same archive.

`host/index-host.lisp` is the caller. `fn-index-host-observe` reads the
selected archive's configuration once per selection/recovery;
`fn-index-host-open` builds the cache at an observed generation;
`fn-index-host-query` (line 74 of that file) calls `fn-nntp-index-cache-query`
and installs its result. The host holds no enumeration logic:
`fn-index-host-fold` exists only as the measurement baseline and test oracle,
and is not a served path.

The served path is not yet switched. `fn-nntp-group-result` and
`fn-nntp-listgroup-result` reach the archive through their arguments, so a
cache cannot be handed to them without widening `fn-nntp-make-session` and
`fn-nntp-step`, which this wave's nntp.lisp owner holds. The equality theorems
above are exactly what makes that a call-site substitution when the session
carries the index.

## Persistent Message-ID lookup (W30)

`books/msgid-index.lisp` provides a separate index for exact Message-ID lookup.
It is a persistent trie over the source string's characters, with a distinct
keyword slot for the article at the end of a key. Character edges and terminal
slots cannot alias. Extending the trie copies the modified path and preserves
older roots, so connection pins can retain their original committed view.
The trie is derived state; it never assigns identities, changes local article
numbers, or supplies recovery authority.

`fn-midx-lookup-of-build-is-find-article` states equality with the existing
`fn-find-article` scan for a string query and an ordered list of articles whose
Message-IDs are strings. The builder preserves the scan's first-match behavior
even for synthetic duplicate lists. `fn-midx-build-has-unique-branches` states
recursive branch uniqueness for those builder inputs. These events and their
witnesses have source-evaluation evidence; fresh focused certification and
complete hypothesis teeth remain open. Their presence does not establish a
performance bound for arbitrary malformed tries.

The live-owner integration is in progress. Recovery will build from the
recovered article projection, durable acceptance will extend the committed root,
and readers will pin the matching archive and root together. Served commands
must call the indexed function under a maintained correspondence; they must not
rebuild the trie or recheck correspondence across the whole archive per command.
The currently integrated primitive alone changes no served lookup path. Group
and local-number indexing above has a different key and query contract and is
not replaced by the Message-ID trie.
