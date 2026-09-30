# The extent read as a protocol, not a value access (row proposal)

Lane extent-identity (Fable), 2026-09-29, for GPT-6's
`warranty-quality-proof-engineering.md` section 3 ("Stop hiding fallible
I/O inside total logical value access").  A ROW proposal with its books
and readers: nothing here is built by this lane.  The readers belong to
A4/A5's async-fault discipline and to paged-history-3; coordination is by
LANEDUMP.  Row A11 (the identity repair, PRF-994) is landed separately and
is the premise of section 4 below.

## 1. The problem, in the code as it is

`A-DURABLE-EXTENT` (books/assumptions-durable.lisp) constrains

    (fn-durable-realize-octet  file eoff elen poff plen trailer i)
    (fn-durable-realize-octets file eoff elen poff plen trailer)
    (fn-durable-realize-lz     file eoff elen poff plen trailer n dict)

to equal `fn-durable-octets` (or its LZ decoding) of the extent.  The host's
raw definitions (host/native/extent.lisp) take the realizer mutex
(`*fnn-extent-lock*`), consult a cache, `pread` an entry, ask ACL2 for a
verdict, allocate an `(unsigned-byte 8)` array of ELEN+32 and a list of PLEN
conses, and may signal `fnn-extent-fault` (a store fault: the owner stops).
That is a partial-correctness abstraction: WHEN the call returns a value, it
is the durable value.  It says nothing about blocking, allocation, fairness
between readers, cancellation, or what a late completion owns.

Three concrete consequences, traced (this lane, 2026-09-29):

1. **The mutex is held across the miss.**  `fn-durable-realize-octets`
   holds `*fnn-extent-lock*` from the cache lookup through the `pread` and
   the ACL2 verdict (a BLAKE3 over ELEN octets).  Every other reader of any
   extent -- and `fnn-extent-register`, called by the log's batch finish --
   waits on one entry's disk read.
2. **The single-octet realizer takes the mutex per access.**
   `fn-durable-realize-octet` locks once per octet; a reader that walks a
   payload by index (`fn-arena-get`) locks PLEN times.
3. **The compressed cache is one list, read by `fn-oct-nth`.**  For an LZ
   extent `fn-arena$x-get` is `(fn-oct-nth i (fn-durable-realize-lz ...))`:
   a hit answers the last decoded payload as a list and octet I is reached
   by walking I conses.

### The two regression questions the review asks

**Sequential byte reads: is fn-oct-nth's quadratic traversal realized by
the served consumer?**  The per-octet readers of the arena (`fn-arena-get`
outside books/payload-arena*.lisp, at the head cec3c55c9) are exactly:

| Reader | Book | Octets read per call | Realized cost on an LZ extent |
|---|---|---|---|
| `fn-nntp-arena-prefixp` (the tombstone test) | article-arena-reads.lisp (served through nntp-responses) | the tombstone's fixed head (a constant) | constant |
| `fn-rcl-arena-prefixp` (the reclaim counts) | store-reclaim-holders.lisp | a fixed head | constant |
| `fn-bphh-octets-at-p` (the BP receipt's byte comparison by handle) | bp-held-payload.lisp | the WHOLE article, one `fn-arena-get` per octet | quadratic: sum of i for i < n = n^2/2 cons steps, plus n mutex acquisitions |
| the commit's window compare (`fn-arx-arena-find`) | payload-commit-extent.lisp | a window before the record's end | staged page, not an extent (the handle is :staged until the reseat) |

So the served ARTICLE path is NOT quadratic: it reads the payload in one
call (`fn-arena-payload`, one decode, one list).  The quadratic traversal
IS realized by the BP receiver's acceptance of a compressed article
(`fn-bpaj-request-acceptable-fast` and its twins compare the request's
octets with the committed payload in place, one `fn-arena-get` per octet):
for an n-octet compressed article that is n^2/2 list steps and n mutex
holds, i.e. a 64 KiB article costs about 2 * 10^9 cons steps per receipt.
The named cost: **O(n^2) per BP receipt of a compressed article; O(1) per
octet for a plain extent (an `aref` under the mutex).**

**Alternating readers defeating the one-entry decompression cache.**
`*fnn-extent-lz-last*` holds ONE decoded payload.  Two readers (two BP
receipts, or a receipt and an ARTICLE) alternating between two compressed
articles octet by octet decode on EVERY access: the cost of one receipt
becomes n decodes of the block (each O(block) work and O(n) allocation) --
**O(n * block) work and O(n^2) allocation per receipt**, against O(block)
for the same receipt alone.  A one-entry cache is an interface that is cheap
for one reader and catastrophic under an interleaving the model does not
see.

Measure at convergence (ember, 2026-09-28: no measurement campaigns in
dev), as two regression tests of the convergence checklist:

* `test_native_bp_receipt_compressed_cost` (proposed): one BP receipt of a
  compressed article at n = 4, 16, 64 KiB; the time per receipt must fit a
  linear curve (the cursor of section 3), not a quadratic one.
* `test_native_lz_cache_alternation` (proposed): two connections alternating
  ARTICLE and a BP receipt over two compressed articles; the decode count
  (a counter on the stats line, `fnn-extent-stats-line` gains `decodes=`)
  must be 2, not 2n.

Both are refuted today by the trace above; neither needs a run to be named.

## 2. Keep the denotation, separate the execution

The logical denotation stays:

    Payload(h) = the immutable octet sequence the extent names
               = (fn-durable-octets file poff plen), or its LZ decoding.

Nothing in books/payload-arena*.lisp, the served columns or the catalog
changes: every theorem about what a handle DENOTES keeps its statement.
What changes is how the host EXECUTES a read: not as a function that
returns the value, but as a protocol of bounded steps whose successful
completion is proved to produce the denoted value.

## 3. The read_step protocol

    (fn-xrp-step lease cursor budget resident)
      -> (:bytes chunk next)        ; CHUNK a slice of the payload, NEXT the cursor after it
       | (:need-page request)       ; the reader must wait for REQUEST (an identity) to complete
       | (:done)                    ; the cursor is at the payload's end
       | (:fault reason)            ; refused by name; the lease is released

with

* **LEASE**: the reader's hold on one handle in one arena generation
  (`(handle generation reader)`); it pins the extent's file id against the
  retirement close (`fn-xrt-close-set` counts leases, not "off-mutex
  readers"), and it names the owner of every outstanding request.
* **CURSOR**: `(offset . resident-slot)`: the next payload offset and,
  when the entry (or the decoded block) is resident, the slot that holds it.
* **BUDGET**: octets the step may hand out and cons cells it may allocate;
  a step never exceeds it (obligation 5).
* **RESIDENT**: the reader's view of the page/entry cache: which
  `(file eoff elen trailer)` identities are resident, each with its
  verified array.  A miss is NOT read inside the step: the step answers
  `:need-page` with the request identity, and the I/O happens off the
  mutex, owned by the request.
* **REQUEST identity**: `(file-incarnation eoff elen trailer generation
  lease)`: the durable file incarnation (device . inode, recorded by
  `fnn-extent-register`), the entry, its commitment (PRF-994) and the
  lease.  A completion carries the identity; a completion whose identity
  names no outstanding request, or a lease already released, is DROPPED
  with its buffer (obligation 3), never installed.

The compressed extent is the same protocol with the decoded block as the
resident object (`resident-slot` names a decoded block keyed by the whole
descriptor identity and the dictionary), and a decode is a step of its own
(`:need-page` for the block's entry, then a `:decode` step bounded by the
block's declared length, ACL2's `fn-lzr-lz-read`).

### The five obligations (each a theorem, each with teeth)

1. **Concatenation.**  Over any run of steps from the lease's first cursor
   to `:done`, the `:bytes` chunks concatenate to `Payload(h)`, without
   omission or duplication: `fn-xrp-run-concatenates`.  Its hypothesis is
   the resident view's faithfulness (every resident array passed the
   verdict against its identity: PRF-994's keystone), never the host's
   behaviour.
2. **Yield/resume.**  A run interrupted at any step and resumed from its
   cursor is observationally the uninterrupted run: `fn-xrp-resume-is-run`
   (a cursor is the whole state of a read; no hidden host state).
3. **Completion ownership.**  A page completion installs a resident entry
   only when its request identity is outstanding under a live lease of the
   same generation: `fn-xrp-complete-installs-only-outstanding`; a late
   completion (the client timed out and released the lease) frees its
   buffer and installs nothing; a lease released with a request outstanding
   keeps the request's accounting until the completion arrives (no buffer
   is freed while an I/O owns it).
4. **Cancellation and failure.**  `:fault` and lease release preserve the
   ownership and accounting invariants: no lease pins after release (no
   immortal reader pin: `fn-xrp-release-unpins`), no resident entry without
   an identity, the cache's byte budget (not entry count: decompressed size
   and dictionary ownership included) never exceeded:
   `fn-xrp-invariant-preserved` over every step and every completion.
5. **Bounded step.**  Each step's work and allocation are bounded by
   BUDGET and a constant: `fn-xrp-step-bounded` -- including the helpers
   (a chunk slice is bounded by BUDGET; a verdict is one BLAKE3 over one
   entry, charged to the request, not the step).

## 4. Where it lands (the row's books and readers)

| Piece | Book / file | Owner |
|---|---|---|
| The protocol and its five obligations | `books/extent-read-protocol.lisp` (prefix `fn-xrp-`, to register in docs/prefixes.md) | this proposal's row |
| Resident view, request identity, byte budget | `books/extent-read-resident.lisp` | same row |
| Host: the request queue, the off-mutex reader thread, the completion install, the lease table | host/native/extent.lisp (the realizer becomes a step driver; the cache becomes the resident view) | same row (host half) |
| Readers moved to the protocol | `fn-arena-payload` consumers (served columns: one `:bytes` run per ARTICLE), `fn-bphh-octets-at-p` (the BP receipt compares chunk by chunk, not octet by octet: removes the quadratic cost of section 1), the tombstone/reclaim prefix tests (a bounded first chunk) | A4/A5's async-fault discipline (timeouts, the late completion), paged-history-3 (the page cache and its budget are shared with the history pages' fill: `fn-pgs-fill-realize` becomes the same protocol) |
| The two regression tests of section 1 | tests/test_native_bp_receipt_compressed_cost.py, tests/test_native_lz_cache_alternation.py | the convergence checklist (planning/release-v6.6.0.md section 2b) |

The premise every reader needs is PRF-994's: a resident entry is the
verified read of an identity, never a re-read.  Without it the protocol's
obligation 1 has no hypothesis to name.

## 5. What is NOT proposed

* Changing `A-DURABLE-EXTENT`'s statement: the denotation is right; it is
  the execution that was hidden.
* mmap: `pread` into owned buffers keeps the fault a named refusal; a
  SIGBUS is not a verdict.
* A whole-store revalidation on any served path (AGENTS.md): the resident
  view carries its verdicts in state.


## Distinct decoded request in the shared physical lifetime

The raw token remains (:window ticket file eoff elen poff plen offset trailer).
The decoded token is (:decoded-window ticket file eoff elen poff C decoded-offset trailer N dictionary-ID). The logical descriptor permits decoded offset beyond C and no arbitrary machine ceiling; the actual decoded issue path must separately establish supported physical spans and funding before construction or pread. Dictionary-ID selects the actual shipped immutable dictionary. The shared retained row kind remains :window, with the full token binding immutable coordinates and dictionary identity.

Shared cancellation, actual return and exact final settlement apply to both types. Raw plan publication and raw scalar access require raw kind and descriptor7 explicitly. Native decoded-first discrimination currently core-refuses execution before the raw runner/destructuring. This is an executable staged type/lifetime boundary, not decoded semantic trajectory, profile adequacy or activation.
