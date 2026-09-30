# Typed rows between the index writer and reader

PRF-1168 is a conditional source proof component. It establishes the current
held16 row domain at the actual list and buffer interns, carries it through the
actual bounded numbering producer, and preserves a physical row-page prefix
through writes, copies and sealing. It does not establish a complete publisher
or activate a reader.

`fn-ibrc-row-domainp` requires the exact 16-element held shape, its real
`fn-held-binding` field's `fn-ab-p` domain, valid withdrawal metadata, a natural
payload handle below the associated arena prefix, and either absent NOV or
`fn-hnov-p` NOV. The prefix belongs to an immutable captured arena coordinate.
A larger current arena count does not establish that an old handle denotes the
same payload in another incarnation. The predicate and recursive prefix relation
are proof vocabulary, never a served-time row or whole-state validator.

`fn-cat-intern-list` and `fn-cat-intern` construct the row from the actual input
and assign the old arena count as handle while extending that same arena. The
constructor establishes the domain when the actual input binding is valid.
`fn-cat-assign`, `fn-held-with-numbers` and valid withdrawal updates preserve it.
The actual `fn-gns-pending-begin` carries the prepared held pointer; every
`fn-gns-assign-step` preserves its cursor/domain relation. On `:done`, field 5 of
`fn-gns-pending-result` is the actual assigned held row with the same domain.
That is the assigned8 field selected by `fn-ipa-row-copy-one`, not a second
assignment interpreter.

`fn-ibrc-prefixp` describes the filled prefix of the actual row-page cells.
The actual `fn-ibp-row-set` extends it with a typed row;
`fn-ibp-row-copy-span` extends a destination prefix from a carried source
prefix; `fn-ibp-row-seal` preserves it; and `fn-ibp-row` returns a typed row at a
selected in-prefix slot. No theorem infers typing from a seal, page identifier,
incarnation or filled cursor. The fixed 256-cell page and bounded physical copy
quantum are existing representation sizes, not a new bound on stored history.

The literal fixtures use modern held16 and a valid acceptance binding. One
complete witness starts at the actual intern, runs the actual bounded
assignment to completion, writes its exact result, seals the page and selects
that same row. Separate removal witnesses negate each cited theorem's producer
hypotheses while affirming its other hypotheses. Corrupted-state cases show
that the existing header-only seal accepts a row with a bad payload handle;
independent mutations remove the binding, NOV type, withdrawal type, prefix
bound or sixteenth field. Those are not reachable acceptance claims.

## Actual publisher entry and recursive read boundary

The successor leaf `index-backing-publication-row-carry` uses the actual
`fn-cat-prepare` definition, mechanically extracted unchanged from canonical
catalog-commit SHA `7453903f4d2a48a3b2e549efa5ee1cde12251018968555bf7af367c484640d4b`.
Its returned prepared row has the domain against the count of that SAME returned
arena. Pending refusal and invalid binding have literal negative witnesses.

Successful `fn-igr-reserve` debits the shared pool and retains the exact prepared
commit in reservation field 6; the builder carries its token and expected count.
`fn-igr-register` preserves this relation, including missing-child refusal. The
actual `fn-ibp-writer-assignment-begin` attaches its cursor to that retained PC,
and `fn-ibp-writer-assignment-one` publishes the typed assigned8 field 5.
The fixture's capacity and child installation are explicitly synthetic;
no installer or operation-allocation authority is inferred.

`fn-iprc-node-prefixp` is a non-executable proof relation over the actual
selected recursive child path. It reuses `fn-ibrc-prefixp` on the reached row
page. With that carry, an in-prefix ordinal and actual `:row` result,
`fn-ibp-node-row-read` returns a row satisfying the domain. The positive fixture
runs the actual recursive right-child write, seal and read; each of the three
hypothesis removals checks all retained hypotheses. This is a conditional read
boundary, not establishment of the prefix by the full writer.

`fn-held-with-context` preserves this row domain, as required by re-decide and
policy updates. Withdrawal uses the existing valid-withdrawal preservation
lemma. Event coverage remains explicit: article appends, cancellation that
changes an existing target and appends a row, direct withdrawal, re-decide,
bounded policy ranges, and events proved to preserve rows. Advancing Store F
or visibility V on an append-only proof cannot establish current publication.

## Required publication composition

The following is an exact remaining producer construction, not a proposal to
validate every row during a read:

1. Join the proven actual prepare/reserve/register relation to the actual
   owner-held PreparedCommit and same-arena capture. The modern PC shape alone
   does not imply source authenticity or arena incarnation.
2. Associate the pending/assigned row and every copied or shared page with the
   generation's retained arena incarnation and prefix. Generation row fields
   9/10 and publication fields identify the coordinate; numerical equality
   alone does not establish provenance.
3. Establish/preserve the existing prefix relation under actual recursive
   row write/copy and row-sharing transitions, and tie each descriptor to the
   published row root and selected ordinal. The conditional reader theorem is
   ready to consume that maintained relation.
4. Join actual durable event completion to publication for the complete event
   roster above. Catalog C, Store F and visibility V are distinct; appending
   articles alone is not a current Store/publication invariant.
5. Establish cold preserved pages from the authenticated held16 loader and its
   retained arena. Neither header seals nor historical held15 evidence suffice.

Until these composition obligations are established,
`fn-ibr-held-install-ready-p` remains a caller obligation for OVER's install/ONE
path. Funding, installed source/runtime, captured lifetime and native activation
remain separate requirements.

## Actual recursive copy progress

The mapping successor establishes the existing prefix relation through actual
`fn-ibp-node-row-write`. A typed write preserves an existing prefix; a successful
write exactly at its end extends it. Sealing preserves the cells. Actual
`fn-ibp-node-page-owner-action` and `fn-ibp-node-row-owner-filled` update a separate
metadata child, preserving the row relation on every selected path.

`fn-ibp-row-copy-cell` reads the CURRENT owner row to select its position. Under
the destination prefix at that position, a typed assigned row, the retained old
source prefix and natural Catalog C, its actual `:copied` or `:appended` result
extends the destination prefix by one. It uses the actual recursive old-row
reader; a seal or owner filled count is not substituted for source typing.
Existing destination prefixes are also preserved through refusal or uncertainty.

Literal tests prepare two rows into the same successive arena, commit the first
reference row and run actual bounded group-number assignment for the second.
They execute recursive physical copy and append with those held16 pointers.
Physical child installation and ownership setup remain explicit fixture inputs,
not genuine admission or durable publication. Each successful-copy hypothesis
has a literal removal witness; malformed rows and nonnatural Catalog C are
corrupted-state witnesses. The five cases retain all other hypotheses and show
failure of the extended prefix. This is source proof, not native execution.

The served owner actually publishes `fn-cat-prepare-sealed` through
`fn-owner-cat-prepare-sealed`. The existing
`fn-cat-prepare-is-seal-then-prepare-sealed` equation connects it to reference
prepare under its literal buffer/row premises. A production join must retain
those premises and the SAME arena incarnation through generation registration;
neither the reference proof nor a PC header supplies the absent caller hook.

The actual `fn-ipa-row-copy-one` caller derives its assigned row, count and old
descriptor from the retained builder and page receipt. Its `:appended` result
establishes the complete partial-page prefix under the carried layout relation,
including the already-copied idempotent branch. Literal carry/status removals
are separate from the source scenario that calls CopyOne twice, actual RowSeal,
two actual RowRootOne steps, and the recursive row reader through the resulting
descriptor. That scenario observes the same assigned pointer and retained old
descriptor; it does not establish publication of that root or source authenticity.
