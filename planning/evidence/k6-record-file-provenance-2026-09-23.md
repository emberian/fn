# K6 P-RECORD file-fence provenance, first certified cut

`fn-bs-k6-actual-record-file-cut-has-exact-frame` in
`books/byte-store-record-provenance.lisp` names the actual `fn-bs-run` of
`fn-bs-record-program`: at pair index 5, after successful create, write-all,
file fsync and record-file observation, the fresh inode's durable octets equal
the exact supplied frame. The proof reduces that interpreted cut to the
create/write/fence transition and proves the raw octet equality; it does not
derive its result by comparing decoded Store record members.

The theorem requires `fn-bs-statep`, a fresh staging key, and a
true-list frame. `tests/acl2/byte-store-record-provenance-tests.lisp` executes
a second P-RECORD with one prior durable article and has separate failing
examples for an occupied staging key, malformed frame and a stale pending
write to the unallocated next inode. The prior article remains durable at
the observed cut.

Hbox selected certification: `python3 tools/farm.py submit hbox --jobs 2
--acl2 /tank/fn/toolchains/w28/acl2-literal-4g --cache /tank/fn/certcache
--remote-root /tank/fn/gates/takeover-byte-store-k568
books/byte-store-record-provenance
tests/acl2/byte-store-record-provenance-tests`, then
`python3 tools/farm.py wait hbox run-20260923T194601Z-8871 --wait-seconds 30`.
Both requested roots passed. Exact ACL2 executable/core identity, source and
closure digests, invocation and per-root results are in
`planning/evidence/manifests/certify-20260923T194604Z-4187906.json`.
`make check` passed after ledger regeneration.

Root integrated both the initial packet and redundant-premise removal as `a2c1a407`/`51d64f50`. The current T10a dependency union passed hbox `run-20260923T195023Z-3a05` in 4.711 seconds with two jobs, 69 cached dependencies and two certified roots. [The exact manifest](manifests/certify-20260923T195032Z-4192209.json) and the changed-root gate cover this combined source, not physical storage hardware.

The first packet proved only the file-fence inode. The next packet below
adds the immutable-link cut. General K0 relation preservation and physical
successful-directory-fence qualification remain separate obligations.

The subsequent packet proves
`fn-bs-k6-actual-record-linked-input-has-exact-frame` over the same actual
interpreter at pair 8, following the successful immutable link. The final
transaction name resolves to the newly allocated fenced inode whose
durable bytes are exactly the frame; the proof does not use equality of
decoded records. The second P-RECORD witness retains an older durable
article. Counterexamples cover each top-level premise: malformed byte
state with a stale next-inode write, invalid input with an atom instead of
frame octets, occupied staging key, and occupied final name. The selected
hbox book and test roots passed again under `run-20260923T195758Z-cdfb`,
with exact source/closure/toolchain evidence in
`planning/evidence/manifests/certify-20260923T195801Z-4383.json`.

At this stage the remaining K6 link was from pair 8 through the modeled
crash-image selector to the scanner's raw record frame. The next packets
addressed the surviving final name and pair 10; whole-list scanner
provenance and general K0 call-trace relation establishment remain open.

The next packet closes that link at the decoder input:
`fn-bs-k6-actual-linked-crash-decoder-reads-candidate` proves that every
admissible crash image of the actual linked cut whose final name survives
has the exact fenced frame at that name, and `fn-bs-record-of` decodes it
to ACL2's candidate. It adds a no-earlier-operation premise at the final
name on pair 5. A modeled prior set/delete pair shows why live name
absence alone is insufficient: a crash can keep the old set and lose the
delete and new link, yielding a different surviving inode. The test book
also exercises retained older article, kept and dropped new links, and an
image whose candidate inode bytes were corrupted after crash construction.
The full scanner's record-list membership and K0 relation
establishment remain open.

Hbox selected certification for the crash/decoder packet used
`python3 tools/farm.py submit hbox --jobs 2 --acl2
/tank/fn/toolchains/w28/acl2-literal-4g --cache /tank/fn/certcache
--remote-root /tank/fn/gates/takeover-byte-store-k568
books/byte-store-record-provenance
tests/acl2/byte-store-record-provenance-tests` and
`python3 tools/farm.py wait hbox run-20260923T201251Z-a0c9 --wait-seconds 30`.
Both requested roots passed; the original result, source and closure digests,
ACL2 executable/core identity and tool versions are in
`planning/evidence/manifests/certify-20260923T201255Z-24557.json`.

`fn-bs-k6-actual-attempted-cut-keeps-linked-byte-state` then proves
that actual P-RECORD pair 10 (`record-attempted`) has the same byte state
as pair 8 after the successful link; `fn-bs-k6-attempted-crash-decoder-reads-exact-frame`
lifts the crash/decoder result to that cut. The test executes the second
P-RECORD through both indices and checks the same kept-link crash image.
Selected hbox certification passed both requested roots under
`run-20260923T201801Z-6afb`; the original result, source and closure
digests, and ACL2 identity are archived in
`planning/evidence/manifests/certify-20260923T201804Z-28115.json`.

The following related-input packet establishes a K0 trace slice:
`fn-bs-k6-related-input-file-cut-has-no-transaction-pending` proves that
the actual create/write/file-fence prefix leaves the transaction directory
quiet when the input byte state is related to a `:record-staged` kernel
state. Thus `fn-bs-k6-related-attempted-crash-reads-exact-frame` derives the
earlier-operation condition used above, while retaining explicit final-name
absence, modeled crash-image and surviving-name premises. The test's
second-publication input satisfies the relation; its prior set/delete
counterexample fails the relation and leaves the earlier operation at the
file cut. This does not yet establish the relation for every served call or
prove a whole-list scanner observation.
Hbox selected certification of the book and test roots passed under
`run-20260923T202750Z-a913`, with the original source, closure,
toolchain and per-root result in
`planning/evidence/manifests/certify-20260923T202752Z-42668.json`.

The next strengthened theorem derives final-name absence as well. A
related `:record-staged` state has the candidate's typed Store-event sequence
at the end of its contiguous durable transaction namespace; a successful
file-cut prefix leaves that namespace unchanged. Thus
`fn-bs-k6-related-attempted-surviving-scan-source-is-exact-frame` needs no
separate final-name freshness premise. The input predicate previously used
the article-only `fn-record-sequence` accessor; it now uses
`fn-store-event-sequence`. A non-article `:undertake` event is the separating
test: the former accessor does not return sequence 1, while the typed
accessor does, and the actual second-publication crash image reads its exact
frame and scans the old article followed by that retention event. General
served input relation establishment and the universal whole-list scanner
theorem remain open.
The typed-input change and new proofs passed selected hbox certification of
`books/byte-store-relation`, `books/byte-store-record-provenance` and their
test roots under `run-20260923T203809Z-c1fb`; original results are in
`planning/evidence/manifests/certify-20260923T203812Z-60507.json`.
`tools/green_check.py --changed-since HEAD` identified ten further stale
dependents of the changed relation book. All ten passed a bounded two-job
hbox run `run-20260923T203916Z-4bed`, archived at
`planning/evidence/manifests/certify-20260923T203919Z-62820.json`.
The linked-cut theorem's name-typing proof hint was also changed to the
typed Store-event accessor; the book and test root passed selected hbox
certification under `run-20260923T204231Z-6c75`, archived at
`planning/evidence/manifests/certify-20260923T204236Z-70620.json`.

The conditional whole-list bridge is now certified:
`fn-bs-k6-related-attempt-surviving-crash-scans-exact-frame-event` names the
actual pair-10 P-RECORD cut and proves that a surviving link's scanner result
is the old durable prefix followed by the candidate decoded from the exact
fenced frame. It derives the scanner index from the typed Store-event
sequence, unchanged durable namespace, and model crash-image namespace
alternatives. Unlike a restatement of scan equality, its premises are the
related staged input, valid frame/name, fresh staging name, relation of the
actual pair-10 byte/kernel states, modeled crash image and surviving final
link. The pair-10 relation is observed in the second-article and non-article
retention fixtures; universal P-RECORD preservation of it is still K0.
Selected hbox certification of the book and test root passed under
`run-20260923T205309Z-9c0f`, original manifest
`planning/evidence/manifests/certify-20260923T205311Z-99085.json`.

The subsequent K0 trace packet proves
`fn-bs-k0-record-attempted-cut-kernel-is-link-observation` in the same
book. The actual P-RECORD pair 5 is the `:record-file :ok` callback; the
actual pair 10 is the `:record-link :ok` callback after a successful immutable
link. A five-step suffix theorem joins them. The relation at input derives
final-name absence, and the file-fence cut supplies the fresh source inode;
the theorem concludes exact equality of the pair-10 logical state with the
two callbacks, without assuming output relation or scanner equality. Its
test book exercises an article and a retention event after one durable
article, and separates the relation, typed-input, and staging-freshness
hypotheses with distinct stopped traces. Selected hbox certification passed
under `run-20260923T210658Z-6956`, original manifest
`planning/evidence/manifests/certify-20260923T210701Z-143870.json`.
The byte-state clauses of the pair-10 output relation remain unproved,
especially pending-link shape, framed candidate in the fenced target, and
authority inode provenance under an arbitrary retained prefix. The served
Store-node caller's preparation-to-`fn-bs-record-inputp` bridge remains
separate. Thus the earlier conditional scanner theorem is still conditional.

A second certified K0 slice,
`fn-bs-k0-attempted-cut-has-one-issued-transaction-link`, derives the
entire pair-10 pending transaction-directory list as the single
`(:set-entry :transactions NAME NEXT-INO)` operation. This is a physical
prefix fact over the actual `fn-bs-run`, not a scanner premise. It uses the
input relation's absence of prior transaction operations, the staged file's
fresh fenced inode, and the successful link; article and retention fixtures
and all three premise counterexamples are in the same test book. Selected
two-root hbox certification passed under `run-20260923T211220Z-bdef`,
original manifest
`planning/evidence/manifests/certify-20260923T211222Z-158686.json`.
Full pair-10 relation preservation remains open as stated above.

Local clause lemmas in the same book now prove the pair-10 pending shape and
that the newly fenced target decodes to the candidate from the durable view.
They use the input relation to exclude a simultaneous root operation and
the exact physical link to identify the candidate target. These are
components of the output relation, not a new general K0 keystone. The
article and retention fixtures evaluate both. The book and test roots
passed selected hbox certification under `run-20260923T211841Z-3e5c`,
original manifest
`planning/evidence/manifests/certify-20260923T211844Z-175171.json`.
The then-outstanding byte-side proof was preservation of the old durable decoded
record list through fresh inode allocation/write/fence for arbitrary
retained history, then composition with state and authority-known/fenced
invariants and the kernel crash-image clause. A source relation permits
other durable authority inodes; the argument must use authority-known plus
the next-inode allocation bound to exclude aliasing, rather than assuming
old record bytes are unaffected.

That old-prefix obligation is now proved in
`fn-bs-k0-attempted-cut-keeps-old-durable-record-prefix`, over the actual
P-RECORD pair-10 interpreter state and arbitrary retained history. The
fresh-allocation theorem supplies non-aliasing of every old transaction
target; the proof establishes pointwise exact durable octets, uses unchanged
durable names, and applies the scanner's generic read-agreement theorem.
The test book has article and retention witnesses after an acknowledged
article, plus relation, typed-input and staging-freshness counterexamples.
Dropping the relation allows `next-ino` to alias the old durable article
inode and the new write changes that old record. Selected hbox certification
of book and test roots passed under `run-20260923T212653Z-31d7`, original
manifest `planning/evidence/manifests/certify-20260923T212655Z-195160.json`.
Whole pair-10 relation composition still needs state and root authority
provenance, plus the file-kernel crash-image and phase clauses.

The next bounded source packet closes three of those clauses for the actual
pair-10 P-RECORD interpreter cut, without asserting the whole relation.
`fn-bs-k0-attempted-cut-statep` derives byte-state well-formedness from the
real create/write/file-fence/link prefix. The fresh allocation cannot alias
the durable frontier or config target, so their exact durable values survive
the write and link. Together with the old decoded record-prefix theorem and
the exact logical callbacks, `fn-bs-k0-attempted-cut-kernel-admits-durable-image`
proves that the byte cut's durable frontier and records are a valid
`fn-sf-crash-imagep` of the pair's logical file state. These are clauses of
the output `fn-bs-store-relation`; they do not presuppose scanner equality.
Selected hbox certification of the book and its existing K6/K0 test root
passed under `run-20260923T220552Z-97a8`, original manifest
`planning/evidence/manifests/certify-20260923T220600Z-285204.json`.
Authority-known and authority-fenced over the *new* pending inode, plus
composition of the pending phase and config/record clauses into the full
pair-10 relation, remain open. The existing K0 input relation is still a
proof premise rather than an established fact for every served call trace.

The next local authority fact is now proved without fixing the file write
list: `fn-bs-k0-apply-writes-preserves-known-inode` inducts over arbitrary
pending operations, and `fn-bs-k0-new-inode-survives-write-fold` applies it
to the fresh inode inserted by O_EXCL. The actual pair-5 file-fence theorem
handles both zero and nonzero write-all branches, the generic pair-8 link
join preserves that inode table entry, and
`fn-bs-k0-attempted-cut-has-new-inode` carries it through the unchanged
pair-10 byte state. The related-input join uses the separately proved
name, true-list frame and absent-final-name facts; it never treats a
fixed pending operation list as an input assumption. A second-article and
retention-event witness checks the inode at pair 10. Selected hbox book
certification passed under `run-20260923T222026Z-6cf4`, original manifest
`planning/evidence/manifests/certify-20260923T222030Z-323574.json`; the
affected test root passed under `run-20260923T222108Z-44aa`, original
manifest `planning/evidence/manifests/certify-20260923T222110Z-325598.json`.
The new inode's authority-known fact is only one member of the authority
list. Preservation of every prior authority target and the fenced status
of the entire list remain before the full relation can be claimed.

The next K0 packet closes that successful `record-attempted` pair-10
relation. `fn-bs-k0-attempted-cut-authority-targets-are-old-plus-new`
derives the exact authority inode list from the actual interpreter trace.
`fn-bs-k0-attempted-cut-keeps-other-inode-entry` proves every old table
entry survives fresh allocation, write, file fence and link; list induction
and the fresh inode theorem establish `fn-bs-authority-knownp` at the cut.
The parallel filtered-write argument proves every old authority inode
remains fenced, while the link's target is the new fenced inode. The
`fn-bs-k0-staged-input-durable-records-match` lemma derives the old record
list equality from the *input* relation's crash-image arm at
`:record-staged`, rather than assuming the desired output scan. Finally,
`fn-bs-k0-record-attempted-cut-establishes-relation` composes those facts
with state, config, frontier, pending shape/candidate, and logical callback
lemmas to prove `fn-bs-store-relation` of the actual pair-10
`fn-bs-run`/`fn-bs-record-program` result. The stated premises are an
already related input, ACL2's typed frame/name input and fresh staging.

The test book executes a second article and a typed retention event after
an acknowledged article, checking the full relation and old inode
preservation. It also has `must-fail` runs when the input relation, typed
final name, or staging freshness premise is removed. Two additional
structural counterexamples separate authority existence (a dangling old
entry) and fencing (a pending write to the old article inode); these
remain byte-state-valid but are not related inputs. Selected hbox roots
`books/byte-store-record-provenance` and
`tests/acl2/byte-store-record-provenance-tests` passed under
`run-20260923T223322Z-7fe8`, original manifest
`planning/evidence/manifests/certify-20260923T223325Z-359941.json`.
ACL2 8.7 at `/tank/fn/toolchains/w28/acl2-literal-4g` took 6.901 s
for the book and 2.217 s for its test root; source, closure and core
digests are in the manifest. A bounded live proof session first isolated
the missing staged-input record equality, and the final relation theorem
proved in 0.88 s of ACL2 prover time with byte and codec internals closed
except the named relation/phase selectors.

This is one successful P-RECORD cut with an input relation premise.
Establishment of that premise at every served call, other P-RECORD cuts
and outcomes, frontier/initialization/recovery programs, adapter-to-model
syscall correspondence, and physical successful-barrier qualification
remain open. The theorem does not convert the selected native SIGKILL or
dm-flakey observations into a power-loss guarantee.
