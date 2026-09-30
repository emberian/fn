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

The ref-aware checkpoint cursor may issue fixed child demand
`(:need-byte absolute-pool-position :mid-character child-index)`. The actual
outer provider retains that request and applies the same source4, current child
coordinate, pool extent, reader serial and buffer identity fences as other
borrowed-byte phases. Unknown kinds and stale coordinates refuse. This route
adds no whole-string conversion; actual op3 lineage and paired independent
reader/resource authority remain separate producer obligations.
