# Portable author succession and recovery: decision still open

The operator-local lifecycle in `specs/identity.md` is a durable configuration
choice by one Store's same-owner control path. Its kind-3 enrollment and
revocation history governs only new `hybrid-author` requests on that Store.
It neither proves that an author consented to rotation nor commands another
Store to revoke a portable signature. Accepted kind-4 verdicts remain pinned
to the exact earlier enrollment; independent portable signature verification
continues to report what the signed bytes prove.

Three concrete authority choices remain for D09:

1. **Local admission only.** Each receiving operator explicitly enrolls and
   retires principals on its own Store. This is implemented for local author
   submission, but remote sites can disagree until their operators act.
   There is no portable key-holder succession claim or recovery from lost keys.
2. **Predecessor-signed portable succession.** The current enrolled Ed25519
   and ML-DSA-65 key pair signs a versioned statement naming the principal,
   previous generation and exact next ordered key set. A receiver applies
   only an unbroken prior-key chain. This gives a portable key-holder move
   but cannot recover after both signing keys are lost; compromise of the old
   pair before observation needs an explicit conflict rule. The abstract
   `books/principal.lisp` chain is a shape precursor, not this concrete
   two-suite record or native authorization path.
3. **Designated recovery authority.** A separately provisioned recovery key
   or threshold set, bound at principal creation, signs an emergency move.
   It provides a loss path at the cost of durable custody, compromise and
   social governance rules. No such authority or primitive profile has been
   selected, so no current local command implies it.

Whichever portable path is selected needs a canonical bounded record, a rule
for simultaneous conflicting successors, explicit author/recovery authority,
and site-local handling of a delayed old-key article. A partitioned site may
not know a revocation yet. The policy must say when new admission changes,
while preserving accepted historical verdicts and the exact original source.
Private-group authorship needs its own metadata and deniability decision
before these public transferable key records are reused there. None of these
choices selects a new cryptographic library or changes the both-required
Ed25519 and ML-DSA-65 profile.
