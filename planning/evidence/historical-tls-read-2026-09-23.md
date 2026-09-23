# Historical configured-owner TLS read, 2026-09-23

`host/owner-host.lisp` calls `fn-ocfg-read-tls-prefix` in `fn-owner-chunk`.
The direct theorem `fn-ocfg-read-tls-prefix-is-full-read` equates its effects
and returned configured-owner state with `fn-ocfg-read` whenever the selected
connection's wire satisfies `fn-wire-statep`; it does not assume the obsolete
static `fn-ocfg-statep`. The TLS constructor carries the historical verdict
and Message-ID trie from that selected connection. The real accepted composite
HDR test separates the fixed constructor from the old six-argument one.

`fn-ocri-host-tls-read-refines-historical-read` is the called-function theorem
under proof-only `fn-ocri-relation`: `fn-ocl-relation` plus wire validity and
trie/archive correspondence for each connection, typed historical verdicts,
and view trie/verdict conditions. Its live-configuration test opens readers on
opposite sides of a group creation and shows different served results from
their pinned archives. A forged wire with a valid fast spine and an invalid
retained octet separates the outer result from the full read when the carried
wire premise is removed. The [qualified w25 book manifest](manifests/certify-20260923T203139Z-3991514.json)
and [test manifest](manifests/certify-20260923T203201Z-3996161.json) cover
this local source with two jobs on persvati.

Preservation of the full historical relation across ordinary read remains
open in this checkpoint. In the branch where `fn-own-finish-read` removes a
connection for an invalid next session, the configured-owner wrapper retains
the old pin. `fn-ocfg-read` and the TLS wrapper must remove that pin together
before this relation can be claimed invariant. The proof-only relation is not
an executable per-command validation.
