# C source observation and replacement

The shared source protocol is an ephemeral actor lifetime protocol. It does not
replace physical operation pins, immutable catalog leases, or the persistent
C-base closure promise. Its source books are `c-source-observer-state.lisp`,
`c-source-observer.lisp`, and `c-source-observer-adapters.lisp`.

One observer row belongs to each actual global machine id. Admission derives its
kind and relative slot from the actual directory, checks the global kind-base
relationship, and reads its generation and live phase from the actual typed
transaction, authority, CNS, query cursor, or sealer table. The caller cannot
borrow another actor's generation or supply a readiness assertion.

A reader admission is idempotent for the exact live owner. The first admission
increments the aggregate count; release clears that exact row and decrements it
once. The maintained invariant is that this count equals the number of live
observer rows. Operations do not rescan the directory or all installed sources.

A writer request belongs to the actual checkpoint master. It generates a new
monotonic session and changes IDLE to PENDING before waiting for existing readers.
PENDING and EXCLUSIVE refuse new readers. The last exact reader release returns
only the retained writer's actual current id and generation as a wake target.
A stale writer closes the protocol as UNCERTAIN; it never silently opens new
admissions. Poll enters EXCLUSIVE only after the reader count reaches zero.

The adopter keeps that exclusive session across bounded old-state retirement,
source installation, and uncertainty. Terminal end and pre-exclusive cancellation
are internal helpers without public core faces. The actual adopter terminal or
owned abort constructor must establish permission to call them. A caller-supplied
completion boolean is not an authority to reopen the protocol. Uncertainty cannot
use either terminal path.

Consumer boundaries are part of this contract:

- A query acquires before source or page admission and releases after its actual
  source references and catalog/page continuations have drained, before actor
  generation reuse.
- Transaction, authority, and CNS resolution retain observation across MORE and
  physical MISS. They release only after actual owned/scalar materialization or
  bounded cancellation. A stage attempt is a separate observation; HELD/adoption
  refusal happens before acquisition, and no source observation remains parked
  behind stage FULL or B admission.
- A sealer paused behind a held checkpoint must finish or cancel its actual
  source continuation before releasing. Releasing only a counter while retaining
  resumable old source references would violate the contract.

The shared primitive cannot infer whether a caller finished copying a source.
Those boundaries must be connected to the actual actor continuations and their
proofs. The prepared lower controls exercise actual protocol transitions under
explicit synthetic actor premises. They do not establish a full live handoff,
source overwrite safety, ACL2 admission, or durable acceptance. Source-only work
must not activate checkpoint/FREE or physical adoption from these controls alone.

## D cursor admission and drain

The D cursor acquires the actual observer before reading the maintained global
installed physical-source count. Under that observer, zero selects the resident
path: metadata-only requests reserve no run-page bundle. Article and stored
header requests reserve their single article workspace before the first reply;
ordinary pool refusal releases the observer and wakes the actual waiting writer
before returning the preheader refusal. They never park on pool capacity while
holding a source observer. A nonzero count retains the existing physical-query
bundle admission and article-page borrowing.

The cursor's storage conditional hold represents the union of the standalone
article lease and physical bundle. Standalone article handles release their
actual pool window; borrowed handles only clear the alias. Final physical
member/catalog cleanup precedes the last bundle-window release. Only then does
the cursor release its observer and advance toward generation reclamation.
MORE, physical MISS, pending I/O, response handoff, and continuation yields do
not release the observer. The writer must hold actual EXCLUSIVE authority
before changing the physical source set; the count is not lifetime permission.

`tests/test_cursor_source_observer_source.py` checks the connected admission,
refusal, union, and final cleanup source. These source checks do not establish
ACL2 admission or execute the request/adoption interleaving.
