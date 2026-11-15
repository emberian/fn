# Live C source replacement barrier

The source implementation closes new semantic admissions before waiting for
existing observations. It does not enable live physical adoption. The typed
adopter must still establish its real persisted root, source hold, loader
capability, coherent replacement terminal, and exact publication receipt.

`fn2-c-source-control` stores writer kind, owner, generation, actual snapshot
token, and both cut positions. `fn2-c-source-readers` stores an exact monotone
receipt for each operation endpoint. READ and successor endpoints are distinct,
including when the same actor uses both. The sealer endpoint covers its complete
merge through input retirement. Profile admission reserves these endpoints and
one additional endpoint per actual query cursor response and CNS metadata
operation; existing indices stay unchanged. No article size or stored-history bound is added.

A writer BEGIN closes admission first. PENDING permits existing exact endpoints
to resume. It also permits a new nested READ only under an exact live request
receipt, so a response can finish later lookups without deadlocking the writer.
EXCLUSIVE and UNCERTAIN do not admit new endpoints. Writer polling is bounded
and must self-yield while waiting; code-only READ release retains a wake
notification, rather than relying on a scalar wake result the API cannot expose.
There is no generic exclusive END. Only the typed coherent adopter may reopen.

READ releases references before dropping its receipt. Successor resolution keeps
its receipt across MORE/MISS and closes after scalar materialization, before
stage or HELD/B admission waits. Group, principal and identity lookup bypasses
must use that same successor endpoint lifetime. The actual sealer can drain
while the snapshot is CLOSING; HELD waits for lower IDLE, no held window, no
receipt, and no live sealer endpoint.

The LIVE-count equality is a carried model invariant, with initialization and
actual transition preservation statements. It is not a served whole-table scan.
WFP alone does not imply that equality. The exclusive/no-live-endpoint statement
requires the invariant explicitly. The prepared removed-hypothesis witness
forges count0 with a live endpoint and is outside reachable initialized state.

The existing public READ and successor APIs name an exclusively owned operation
row. Generation-validated machine transitions invoke them synchronously; queued
read-result observers only record results and wake. They do not queue delayed
READ release calls. Public release(x) is not claimed to authorize arbitrary stale
external callers. Lower release takes the caller's saved exact receipt and
rejects an old receipt after endpoint reuse.

This packet is based on coherent cold f0e1a6132. It must be projected as named
observer and caller hunks onto current ROOT, preserving newer CNS, query,
allocation, pool, columns, compiler, and RELEASE work. Current ROOT 5cd87bca6811
has the same original machines-c-read source, but lacks the cold c-snapshot
book and differs in other C/sealer providers. A whole cold file overwrite is not
an integration recipe.

All current checks are source controls, structure, include-graph and arity
checks. Prepared ACL2 positive, refusal, drain and hypothesis-removal assertions
have not been executed or certified. No runtime activation or compute is granted
by this source packet.


The current source milestone includes whole cursor-response protection. CNS
metadata admission is being joined by its sole actor owner: PAGE's existing
MORE means page termination and must not be reused for a pending writer. FETCH
must finish its real Message-ID comparison while holding the metadata parent,
then use the independent exact E*N source promise through physical preflight,
streaming and terminal handback. PAGE must not drop metadata protection before
its copied body/descriptor has an independent lifetime. No pending-writer
refusal may become a missing article, page end, or a fabricated successful
identity result.

The root comparison and donor raw hashes are in the packet receipt. Named
production hunk groups are: machines-c registration/geometry; READ declaration,
shared parent helpers, actual child/core faces and effect tables; successor
receipt, resolver/release/stage boundaries; directory/identity wrappers; sealer
receipt/drain and snapshot poll; cursor declaration, request callbacks, start
retry and terminal handback. Newly added observer and cursor helper books can
be imported whole. Existing C, cursor and snapshot files must be projected by
these named groups. No existing CNS, pool, columns, compiler, allocator,
physical-loader or RELEASE file is replaced by this donor.
