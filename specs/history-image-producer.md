# Actual private canonical image writer (PRF-1144 / SCN-1050)

The full obligation is the host-called `fn-hpi-tick`, reached by
`fn-owner-history-image-tick` through native `fnn-hpi-step`. The writer
retains a fixed controller, five fixed page buffers and the existing
`pgs-digest-state`. The caller's actual maintenance admission must reserve
all constructor/child/native/source lifetimes before those allocations;
image growth alone is not that whole-operation admission.

Immutable job source4 is `(epoch (capture-ticket count) 0 0)`; census is
pass0 and the actual source restart supplies emission pass1/row ordinal.
The stage ID is the issued maintenance job ID, naming one private stage
and two spool files for one attempt. Uncertain effects retain that attempt
and its credit until joined cleanup; no host counter creates an identity.

`fn-hpi-begin` derives exact rounded column/pool capacities, calls the actual
canonical layout/domain check and applies the admitted runtime/profile
extent coordinate. `fn-hpi-growth-request` returns exactly ten fields:
`(:checkpoint-growth source4 stage maintenance N T M stage-end 32N 32T)`.
Actual `fn-osj-grow` issues and retains the corresponding exact receipt.
Every step and source offer checks that receipt against the actual funded
pool before child allocation, issue, ACK consumption or buffer reuse.
A generic later maintenance growth invalidates the old receipt, so all
image work must finish before later framed segments grow their own backing.

The stream writes physical zero-page0 separately, then the logical header,
four columns and pool with canonical zero padding. It hashes acknowledged
stage bytes with the existing `pgs-dcb` engine, writes one32-byte data digest
per spool slot, streams341 entries per table with two zero tail words, hashes
acknowledged tables, then streams the full M-page directory from table digests.
Directory hashing covers all M pages. The terminal root uses original
`fn-hpir-root 1 1 N directory-digest`, the fixed16-word/128-byte concrete
record check extracted from `pgs-x-write-rec`, with N data pages. The abstract
`pgs-make-rec` calls constrained `pgs-digest` and cannot be executed; `fn-hpir-root-agrees-with-current-record-writer` connects the complete six-field
root to the actual `pgs-x-write-rec` with no hypotheses. Its proof derives the
checksum representation from actual BLAKE3 output and the concrete word writes;
legal executable reference calls still satisfy their stobj guards. Abstract
digest observation remains a separate named proof obligation.
The writer returns the exact
captured node/salt/count/trail for the outer existing `fn-his-binding`.
Full Store summary and A/F/P/E/R framing/publication stay with the outer
producer; they are not invented or omitted by this canonical image helper.

Write-page effect is
`(:write-page source4 stage serial region logical physical offset 16384 generation)`;
ACK is `(:written source4 stage serial generation :ok/:uncertain)`.
New I/O effects are ten fields
`(tag source4 stage serial kind ordinal offset length generation payload)`,
with tag `:read-stage`, `:write-spool` or `:read-spool`.
Reads return `(tag source4 stage serial kind ordinal generation outcome octets)`,
tag `:image-read` or `:spool-read`; writes return
`(:spool-written source4 stage serial kind ordinal generation outcome)`.
Outcome is `:ok`, `:uncertain` or `:refused`, never a transport ACK.
Response octets are validated in at most64 cells. Only one effect is pending;
exact stage/source/serial/generation and requested coordinate match precedes
consumption. A mismatching completion leaves the continuation unchanged.

The native wrapper retains already-admitted buffers, threads the actual
funded pool and performs no I/O, budget/key/address/hash decisions. Producer
I/O executes only returned effects under its actual stage descriptor authority.
`fnn-hpi-offer` requires the actual new-salt `fn-omk` result; old source header
MKEY is not a substitute. Source rows stay pending through cold byte demands
until `:row-done` with `(:row-emitted rowtoken encoded)` after column3 install.

Status: all writer definitions and guards pass protected source admission.
The complete small decoded-cold-row trajectory compares all9 physical pages,
all7 digest spools, padding/table/directory words, frozen terminal fields and
root against the independently executed `pgs-x-write-rec`. Mutation fixtures
check the live ledger/issued demand antecedents before stale-stage, uncertain
outcome and malformed-octet rejection. These are source runtime fixtures.
General full canonical residual/effect/authority/progress proof, abstract
digest observation, larger table/directory trajectories, initial whole-operation
funding and actual native joined execution remain open. No certificate,
qualified image, deployment, publication or complete checkpoint claim follows.
Physical page0 remains zero as the original snapshot format specifies: its
sole root record is protected by the outer F binding consumed by `fn-his-open`.

The actual funded host wrappers also pass scoped source admission in the same
writer/effect world. A reachable fixture installs the actual pool, obtains
its maintenance and image-growth receipts, drives full zero-page issuance,
and calls the exact native-facing effect projections. Its short-write result
puts the writer in recovery while retaining the pending effect, buffer
generation, complete buffer and live credit. This is a concrete host seam
fixture; it does not establish initial whole-operation allocation adequacy
or replace native syscall/lifetime and general writer proofs.

The proof-only tagged byte/census join connects both resident and decoded
cold children to one canonical residual and length invariant. Tick preserves
that residual; attributed supply preserves it only with the current demand,
exact requested position and byte from the immutable pool. The uniform
census counts an emitted supply byte exactly once. Its supply law explicitly
keeps active success distinct from completed refusal. The actual producer
`fn-hct-tick` completed-row theorem then preserves article count and padded
pool length, assuming the carried prior census, child invariant and exact
row denotation. Five complete positives and fifteen hypothesis-removal
witnesses passed, including a wrong NIL-classifier byte. This does not
establish source lineage, strict productive progress or the whole image
writer invariant.

The tagged pool boundary now preserves the complete concrete page prefix plus
canonical pending words through the actual `fn-hpe-tick` and attributed
`fn-hpe-supply`. The proof reuses the original pack8 and eight-byte-prefix
lemmas. It includes partial words, eighth-byte writes, final padding and
full-page supply without consumption. A proof-only finite schedule calls the
actual tick, supply and page reset; conditional completion yields exactly the
original codec's packed words and byte count for either resident or cold rows.
Seven complete positives and thirteen premise-removal witnesses passed; the
malformed logical-buffer cases are corrupted-state examples. A logical page
transfer proves no physical write acknowledgment or release. Source lineage,
productive termination and whole writer phase/effect/authority remain open.
The final proper-local evidence is
`planning/evidence/history-pool-tagged-refinement-source-2026-09-30.json`;
its proof body took29.39 ACL2 seconds/10,608,053 steps in the composed source
world, with no matched proof-cost or qualification claim.

The actual writer growth call now uses the selected Linux x86-64 signed-long
backing profile, and every retained grant check also checks that profile.
The exact effect projection admits I/O only within its captured target or
spool extent and the signed offset domain. Profile refusal preserves the
complete cursor, ledger, five buffers and digest state. Its oversized-layout
fixture is a corrupted-state case; it does not claim a valid huge census
passes earlier current-format constraints. An actual funded first page,
out-of-extent pending-request mutation and uncertain-write recovery passed
in the same composed source world. The full cold image trajectory was rerun
against the changed controller. This establishes no whole-operation INIT
adequacy, whole writer invariant/progress or native execution claim; exact
source evidence is `planning/evidence/history-image-native-profile-source-2026-09-30.json`.


The supporting `history-image-writer-refinement` safety boundary is now
proved for the actual ten-output `fn-hpi-tick`. Immutable capture and exact
stage receipt remain live through retained steps; successful initial growth
establishes the same authority. Returned `:write`/`:io` alone establishes the
fixed effect tag, pending effect, captured source/stage and monotone serial.
Internal arbitrary-tag helpers retain their own tag constraint. The complete
uncertain-page and uncertain-stream laws preserve the ledger, all five buffers
and digest state. Stream return word `:uncertain` sets the cursor phase to
`:recovery-required`; it is distinct from the page return word
`:recovery-required`. Literal tests reach all four actual I/O phase kinds,
assert complete premises/results, and falsify each omitted premise while
retaining the others. Corrupted phase witnesses use explicitly constructed
matching observations and make no claim that the native executor emits them.
The canonical byte trace still uses an explicit acknowledged-write/read oracle;
A-HPI-POSITIONAL-IO's visible-byte assumption needs exact held FD/private role
and ordered trace composition and does not establish durability. Whole byte
fidelity, productive progress, initial demand and native qualification remain
open. PRF-1144 remains planned with no completion events.


`history-image-private-trace` now connects a full acknowledged write to an
exact later read under A-HPI-POSITIONAL-IO, and connects the actual complete
nine-field read observation to that named visible range. The interleaved
stage/data-spool/table-spool trace carries a stable pairwise-distinct file
identity triple and an explicit visible frame for every untouched role on
every write. A full count on the selected role alone supplies no such frame.
Local functional-instance witnesses exercise all literal read/readback
premises and complete outputs; corrupt abstract bytes and improper payloads
are labelled separately from actual controller-issued operations.

These are conditional proof-only byte-trace laws. Their helper definitions
are not served entries or guard-verified executable implementations. Actual
held FD-to-file identity/nonalias lifetime correspondence and association of
trace payloads with issued HPI effects still need the composed writer proof,
alongside canonical phase invariants, productive progress and whole-operation
INIT/native qualification. The named visible-byte assumptions establish no
durability. Exact source evidence is
`planning/evidence/history-image-private-trace-source-2026-09-30.json`;
PRF-1144 remains planned with no completion events.


The actual `fn-hpi-tick` directory-emission phase now appends the canonical
global `pgs-encode-run` word and grows the concrete scratch to its next
canonical prefix while preserving the ledger, four other buffers and digest
state. Its carried proof invariant relates ordinal/component to page/used
position, remaining words, the captured table count and the exact current
cached digest. The served step does not reevaluate that model. A full small
decoded-row/page/spool trajectory reaches the positive; current-cache
corruption and missing-cache IO demand separately falsify the two literal
premises and complete results.

This is a continuing directory-word phase law. Preservation of the entire
carried invariant, page handoff/reset, table packing with 341 entries and two trailing zero words,
whole pool/data/digest/root fidelity and strict productive progress remain
open. No initial/native/qualification scope is transferred. Exact source
evidence is `planning/evidence/history-image-directory-phase-source-2026-09-30.json`.
