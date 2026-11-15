
## Connected controller source — November 15

The actual upload identity arm now enters bounded stream initialization. C0
retains the checked header; the actual C1 fill and global FED determine the
resident source origin. SOURCE hashing and LF counting use that origin. The
stored-stream context hashes each selected span before the same span is copied
into the retained block stage. One stage call consumes at most the existing
derived 2036-byte stage quantum: one hash read plus copy read/write, four
header-tail reads and a 32-byte final digest write fit the existing 6144-byte
run budget. SOURCE hashing retains its separate 2048-byte quantum.

A partial block can be written repeatedly, retaining its page prefix, until
complete. Only a complete block or final tail receives a canonical provisional
entry. Each body-window return follows an actual DONE Fence, zero pending I/O,
an owned page workspace, exact live feeding owner/FED and checked C1 workspace.
The same pool reset clears only C1 fill; global offsets and lease generations
remain unchanged. Issued non-DONE or malformed completion enters the existing
uncertain stop with all tuples and bytes retained.

PEXT is the immutable first payload allocation and generated Message-ID source.
At EOF, SOURCE is finalized directly into its retained page slot. Above the
three-unit raw threshold, a distinct ROOT is reserved and the final header and
entries are encoded with the existing codecs into a disjoint region. Final ROOT
writes and Fence precede SEALED. Transaction location and accepted extent
closure select the actual raw PEXT or promoted ROOT; the manifest's group-zero
entry accounts for first PEXT exactly once.

This is source, not runtime qualification or activation. Actual 32 KiB repeated
window and threshold controls are being connected to the existing CW driver.
The full served resource envelope must consume the same provisional-page
geometry before integration. Definitive refusal drains the remaining framing,
then issues a real Fence before giving the word to the transaction. Owner
departure also waits for the covering Fence. After the child releases its
reference, a separate drain decodes one retained provisional entry per turn,
settles only physical group leaders, then the unreferenced CFREE handle and
separate ROOT once each, and finally returns the page. It never independently
cancels first PEXT a second time. Query or borrowed workspaces postpone cleanup;
failed or malformed Fence enters uncertainty instead. Actual abort-cut controls
and execution of the new 32 KiB/threshold assertions remain required. No claim
of recovery-byte equality or general upload completion has been executed yet.

The byte-cost followup also accounts for each block hash/full CV/location
hash reading one unit and writing 32 pool digest octets (4128), and digest
copy reading/writing 32 octets (64). Final manifest repack is bounded by two
codec-max spans plus the 64 referenced digest/CV octets. The original SOURCE
finalization writes only its 32-octet result into the retained page.

The header verdict is its own stream-init transition. Its Path POSTED worker
uses one read per byte, with a named equality to the original per-start
predicate and actual pool controls; that theorem and those controls are
unrun. The actual verdict entry checks MID/Path ranges against the physical
line bound before reading. Four line spans plus three Message-ID spans and
four delimiter reads give the separate 4746-byte bound, below the unchanged
6144-byte run budget. Invalid scan statuses return their verdict before any
additional header pool read. None of these source checks certifies a byte
refinement or runtime execution.
