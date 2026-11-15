# Internal ordered history and import connection

The peer history functions are internal C consumers. No network handler or
new authorization admission calls them. Existing remote authorization remains
blocked; these changes neither relax it nor route around it.

`fn2-peer-history-open-core` consumes an actually held `fn2-csnapshot` token,
owner and generation. The shared `fn2-event-read-open-core` derives each next
installed journal entry from that cut in the same operation; its extent,
allocation generation and installed-root edge must match. The checkpoint
caller retains its independent `fn2-checkpoint-build-ownerp` admission.
The peer caller obtains its physical cursor namespace from `fn2-core-origin`.
An actually empty held cut completes without reading a nonexistent entry;
its settled commit root must also be empty. A journal's historical namespace is separately authenticated by the shared
seal verifier; namespace numbers are not compared chronologically.

`fn2-peer-history-member-core` advances the existing record/member verifier
and Merkle append. It exposes one copied canonical semantic member only when
that same step appends the expected event to the actual frontier. A full,
stale or wrong-owner destination refuses before continuation advances. The
source and destination are separate owned ranges. Copy bytes are scratch
until the returned status is `:member`; failures expose zero event and length.
The held C cut and existing source edges protect the source across yields;
physical reads use the existing allocation pins. Close refuses pending I/O,
then uses actual C snapshot release before resetting reader continuation.

This is an exclusive resident cut: it drains admitted C work and blocks new
staging while held. It is not a persisted peer cursor. Authenticated archived
prefix traversal and a scalable retained-cut policy remain separate work.
The reader is not a view-filtered catchup page, a coverage claim or an importer.

The independent internal import producer is `fn2-peer-import-start`, the
existing bounded `fn2-identity-decide`, then `fn2-peer-import-declare`. It
checks the original decoded row against the actual completed query and owner,
retains original evidence/receipt fields, and uses C's existing union
freshness. Imported facts use `EST/L=0`; they neither create a local article
nor select a candidate. A duplicate fact contributes no new evidence/history
count; a changed payload under the same union key is inconsistent. These
functions do not authenticate an issuer, establish global origin uniqueness,
or advance an authenticated import cursor. The ordered decode/dispatch and
coverage transaction still need integration above them.

The retained-reader fixture drives two actual B commits, actual snapshot
acquisition and physical read completion through the shared verifier. It
checks canonical member bytes, event order, destination refusal without
advance, lost lease and close behavior. The import fixture exercises actual
C resolve/stage/bind/publication, including duplicate and conflicting union
payloads; this is not a durability or crash test.

Current status is source-only. The shared member verifier and the new member
consumer now carry explicit pending guard-verification events; a compiled guarded serving boundary
requires those exact leaf-to-wrapper obligations to be admitted and exercised.
A typed-domain error-path control also checks that an overflowing event sum
keeps the prior u60 continuation and marks uncertainty; this malformed reader
is not claimed reachable from the held-source opener.
No network or complete-catchup claim follows from these source controls.
