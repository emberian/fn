# Owned bank evidence

The runtime writer now retains the exact installation member event, containing
commit J, cut C and cut event before reusable commit-directory/checker storage
can change. C and J remain distinct; no adjacency is required. The actual
persisted member success stamps `installation-event`; preparation clears stale
installation authority.

`checkpoint-bank-evidence.lisp` owns four fixed physical protocol roles inside
the publication carrier: bank0, bank1, current attempt and displaced debt. Each
contains the candidate/checkpoint/history/incarnation tuple, C/C-event/J/J-event,
and five independent hashes: seal J, seal C, seal J-1, previous descriptor and
current descriptor. These four roles are not a stored-data admission ceiling.

Actual writer BEGIN derives all directory locations with tagged lookup. It
checks the exact installation event belongs to J, copies evidence, and binds
the attempt's full descriptor hash. Only the matching successful covering Fence
callback transfers attempt evidence into a bank and preserves displaced evidence
in debt. A failed/ambiguous Fence retains the old banks; a stale operation
notification changes no bank evidence.

The B readers `fn2-checkpoint-bank-evidence-snapshot`, `-event`, and `-word`
consult only owned publication storage. Snapshot returns code, candidate,
checkpoint, history, incarnation, C, C-event and J. Event returns the exact
J-event. Word accepts `:installation-seal`, `:cut-seal`,
`:installation-predecessor`, `:previous-descriptor`, or `:descriptor` and index
0..7. Slots0/1 are banks and slot3 is debt; the unpersisted attempt is refused.
Full descriptor identity is checked, so matching numbers cannot alias a
conflicting descriptor.

Cold bank reconstruction remains required from authenticated anchor/descriptor,
installation-record and verified root3/root4 evidence. Runtime capture alone
does not authorize directory deletion, candidate recycling or allocator FREE.
The candidate-scoped debt owner must copy every identity/hash before clearing
the singleton debt; all physical promises and durable protectors survive that
transfer. The typed callback fixture is unexecuted and seeds installed/issued
premises explicitly; it is not a physical durability or cold-recovery witness.
