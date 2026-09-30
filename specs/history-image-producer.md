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
