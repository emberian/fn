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

The later [qualified open/read book manifest](manifests/certify-20260923T204332Z-4118198.json)
and [test manifest](manifests/certify-20260923T204501Z-4134528.json)
cover `fn-ocri-open-preserves-historical-reader-relation` for the actual
configured-owner open and `fn-ocri-own-read-preserves-reader-pins` for the
actual owner read. The read theorem handles both replacement and removal of
the selected connection. Its configured-owner composition is explicitly
conditional on the base `fn-ocl-relation` after read. A reachable third open
pins the current view trie, while an existing malformed wire remains malformed
after an unrelated open; the test's failed theorem shows why carried reader
validity is needed.

The called `fn-ocfg-read` and `fn-ocfg-read-tls-prefix` now share
`fn-ocfg-with-read-owner`: if a read closes its connection, the corresponding
config pin is removed; otherwise it is retained. The direct outer equality
and both test books pass in the [post-cleanup w25 manifest](manifests/certify-20260923T204844Z-4173382.json).
Preservation of the base `fn-ocl-relation` across ordinary read is still being
proved in the config lane, so this packet does not yet claim unconditional
preservation of the full `fn-ocri-relation`. The proof-only relation is not an
executable per-command validation.

`fn-own-finish-read` and its event-step sibling now require a surviving
connection's selected group to be valid in both the existing current Store
domain and that connection's pinned archive domain. The
[owner invariant and test manifest](manifests/certify-20260923T210136Z-108821.json)
certifies this actual called-path change with w25 on persvati. The second
check can add one linear group-membership scan on a selected read; it does not
walk the whole Store. Proving current/archive domain correspondence for the
static owner relation would let a future implementation eliminate the
duplicate check. The live old/new reader witness establishes that an old
connection refuses a group created after it opened, while a new connection
selects it; there is no claim that a valid old reader previously selected a
new group.
