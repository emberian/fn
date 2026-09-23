# Portable fn authorship joined to a Mini operation

This public synthetic fixture uses the sibling P0 E1 source/package and P2
`signed.eml`, plus `changed-carrier.eml`: a newly signed source whose only
application-source difference is its Message-ID. Both authored sources carry
exactly the same base64 Mini P0 package. The changed carrier used the same
public principal and Ed25519 test key with a newly generated scratch ML-DSA-65
key; `changed-ml-public.pem` and `.raw` are public. `changed-claim.json`
contains its ACL2-derived source ID and signed header claims. The full
hybrid keyset was independently pinned for each verification call. These
portable signatures do not attest fn Store retention or topic admission.

The Mini local application is `mini-e1`, subject 7, content target 600 and
capability 61. The new route derived operation
`6df49d3b28b9c17fdf4360aeee7d45b76327b7d9a4bc047f370356001eb54e1`
from the re-admitted Mini origin domain, semantics, genesis and original
transaction ID. It took neither package nor operation ID from a report JSON.
`decision-first.json` is proposed until `signed-first-call.bin` was submitted
and `accepted-first-outcome` confirmed accepted count 2. A new process
recovered `decision-repeat.json` and byte-identical `reply.bin` without a
new intent. The changed authenticated source returned
`decision-conflict.json`; `signed-conflict-call.bin` installed separate
conflict evidence as accepted count 3. Another reopen returned
`decision-conflict-repeat.json`. `consumer-genesis.bin` and
`signed-birth-call.bin` are the public scratch consumer history prefix used
by both calls. No private key or SQLite file is shipped.

The compiled route also refused a wrong full ML key pin, a changed signed
carrier byte, and a policy that changed capability 61 to 999; each created
no intent or decision output. The full invocation and scoped result are in
[the evidence record](../../../../planning/evidence/dregg-e1-portable-consumer-p2.md).
The binding retains the verified fn source ID and exact Mini package, but
not the full fn carrier. It is not a complete fn Store inbox, E2 cursor/ack,
or persisted signed fn application reply for posting.
