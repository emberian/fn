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

## Required publication composition

The following is an exact remaining producer construction, not a proposal to
validate every row during a read:

1. Carry the intern's arena result through the actual `fn-cat-prepare` pending
   record and into the writer's registered builder. The modern `fn-pc-p` shape
   alone does not imply typed optional NOV or association with a source arena.
2. Associate the pending/assigned row and every old copied or shared page with
   the actual generation's retained arena incarnation and prefix. The existing
   generation row fields 9 and 10 and publication arena fields identify that
   coordinate; matching numbers alone do not establish its provenance.
3. Establish/preserve the page prefix relation under the actual recursive
   `fn-ibp-node-row-write`/`fn-ibp-row-copy-cell` and row sharing transitions.
   A builder's filled count only records progress; it is not the invariant.
4. Make successful actual writer publication carry that relation for its
   retained row-root/descriptor/ordinal mapping, then discharge the reader's
   `fn-ibp-node-row-read` boundary at the SAME captured generation and arena.
   Catalog C, Store F and visibility V remain distinct coordinates.
5. Cold preserved pages require establishment from the actual authenticated
   held16 loader and its retained arena. A header-only seal cannot bootstrap
   the relation; historical held15 certificates cannot be transferred.

Until this composition and the source-publication correspondence are proved,
`fn-ibr-held-install-ready-p` remains a caller obligation for OVER's actual
install/ONE path. This packet supplies the intern/assignment/page facts needed
by that obligation. Funding, installed source/runtime, captured lifetime and
native activation remain separate requirements.
