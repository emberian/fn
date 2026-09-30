# Bounded authenticated checkpoint source reader

PRF-1107 / SCN-1017. This is the planned replacement for eager
`fn-hrs-open-pgs`/`fn-hrc-phys` in the captured snapshot source path.
No bounded reader, authentication, funding or host-composition completion is
claimed merely by this contract or by its independent mapping components.

The controller supplies a captured, selected root record from the existing
`(:hrs-handle file rootrec salt N lens starts np)` handle. Root slot selection
and root self-check are prior obligations; an arbitrary caller-supplied record
is not a trusted root. The exact checkpoint file incarnation is pinned through
all census/emission passes and every outstanding page borrow. Physical ownership
uses a fixed `(:file-pin ticket file)` token; the reader compares its scalar
ticket, not the file path. The source epoch is the captured Store frontier.

The agreed request is
`(:read-page ticket epoch serial phase physical-page relative-byte-offset 16384 logical-page)`.
ACL2 derives the region-relative byte offset as `16384 * physical-page`.
The physical core validates and adds the registered region base, including the
actual runtime offset domain, before native positional I/O. The existing
registration base already skips the 16384-byte FNSI wrapper; the reader must
not add that wrapper twice. Page 0 is zero; the root comes from the captured
checkpoint F binding, never from a guessed root slot on page 0. Host code performs
I/O only. Exactly one request may be outstanding. Completion must match the
fixed ticket/epoch/serial/phase/page and buffer lease; stale completion cannot
advance a new request. Cancellation does not release an outstanding borrow or
file pin until physical completion/join and final borrower release.

For logical page P, the selected table index is floor(P/341) and its entry is
P mod 341. The directory stores contiguous six-u64 entries and can span many
16KiB pages; an entry may cross a page boundary. Each entry is physical address,
txid, then four big-endian digest words. Table pages hold 341 entries and two
padding words, with more padding on the final partial table. The directory has
one entry per table and pads its complete page run with zeros.

The reader hashes the complete directory run, including padding, with one
`pgs-dc-begin` over 256*M blocks. It validates every directory entry txid and
padding word incrementally, retaining only the selected six-word entry. No
selected table request is released before the root's directory digest and
canonical form agree. It then hashes and validates the selected table, retaining
its selected data entry; only then may it request and authenticate the data page.
The data buffer remains borrowed after `:verified-page` until the decoder has
finished using it. No logical/physical page-number identity is assumed.

The digest client sends a fixed 16-u32 block (eight u64 words low32 then high32)
or one digest continuation tick. The source reader never materializes all
entries, a directory word list, full table arrays or an image-sized pgsmem.
The existing concrete directory domain M<2^32 is explicit, along with root u64
fields and the registered file-region/runtime offset domain. These existing
representation checks do not silently create a new supported-profile ceiling.

Canonical shape and digest failure remain distinct. The directory/table scan
may latch malformed txids or padding, but digest mismatch takes the existing
priority before malformed data is reported. Short/ambiguous I/O is reported to
the controller as a recovery event; it cannot become an authenticated page.
A digest match authenticates the observed stream under the selected root's
commitment. It is not a theorem that no distinct bytes collide: the crypto
assumptions and their pessimistic collision scope remain explicit.

Decoder ownership remains `history_decode_cursor`: pool offsets, row framing,
node/span inverse and byte parsing. Physical ownership remains `physical_lifetime`:
file pin, baseline funding, fixed page-buffer leases and positional I/O. The
producer joins captured Store/root/source tokens. Astra owns the private output
image. This reader owns only the bounded input mapping/authentication chain.

The first admitted component is `fn-hsr-scan-begin/word/entry`. Its fixed nine-cell
state contains five scalar coordinates, at most six selected u64 words, a
malformed flag and two opaque identities. A word tick preserves the logical
invariant, advances by one, and conserves both the exact selected stream and
the accumulated per-word validity predicate. The selected-stream theorem
refines `pgs-decode-table` directly. This extraction is not authenticated; the
whole canonical verdict bridge and real digest/request continuation are open.
`hsread2` clean source admission and literal witnesses are recorded separately
from future certification in the committed source evidence.

`history-page-reader-verdict` now proves the incremental stream predicate
equal to the current decoder's txid check plus canonical zero padding. Its
guarded `fn-hsr-page-verdict` agrees with the existing directory/table logical
verdicts, including digest-damage priority. The initial sufficient-word-count
premise was proved redundant and removed: the old logical decoder pads absent
words with zeros. This fact never licenses short physical reads; complete
16KiB read validation remains a separate continuation obligation. The observed
digest parameter is component vocabulary until the real digest cursor is
composed; this component alone cannot authenticate a source page.

The guarded `fn-hsr-io-*` continuation has nine cells: mode, root ticket, epoch,
next serial, pending request, held discovery ID, capture, lease and cancel bit.
It begins once per pinned capture and survives every logical seek/source pass.
An issued request consumes a fresh monotone serial in ACL2; a completed read
binds its physical discovery ID. IDs include zero, so only `nil` denotes no
held buffer. `:observed` is not an authentication verdict. The mapping/auth
controller alone may choose physical requests and expose verified contents.

Cancellation retains both pending request and held buffer identity. Short or
ambiguous completion becomes uncertain and cannot be downgraded by release or
cancellation. `fn-hsr-io-joined-failure` is called only after native unwind/join
has completed, cleared local aliases and settled its own unreturned token; an
unresolved join retains the pending request and physical charge. Release in
the logical continuation is an acknowledgement after physical settlement and
alias clearance, never a refund operation. Every transition preserves captured
root ticket, epoch and opaque capture/lease references.

The pending request recognizer checks exactly nine scalar fields, including
phase, length and ACL2-computed offset. Completion equality therefore compares
a fixed flat packet under the executable outer guard; it cannot walk nested
caller data retained as a malformed pending request. Opaque capture and lease
references are carried, never traversed by that comparison.

The composed `fn-hsr-auth-*` library now executes actual current-format root →
directory → table → data authentication with the real digest cursor and fixed
19-cell state. Guard admission and literal whole-chain tests include physical
17/18/91/304 and a straddling directory entry341. Initial shape and nested I/O
invariant, and shortread uncertainty with retained borrow, have source-admitted
lemmas. A second logical selection preserves the pin and advances serials; an
old completion cannot adopt a buffer. These source results do not close the
universal composed authentication/invariant/refinement/progress theorem,
physical funding or host activation. PRF-1107 stays planned with no events.
