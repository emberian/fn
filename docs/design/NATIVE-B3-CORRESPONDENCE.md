# Native BLAKE3 correspondence pilot

The Merkle-node replacement now calls a shared, guarded ACL2 word store, with a
conditional theorem equating its **entire digest carrier** to the actual
`fn2-mk-node` result. C/FFI behavior remains an explicit assumption. This pilot
does not discharge the other seven native replacements or prove BLAKE3 in C.

`books/digest-store.lisp` defines `fn2-digest-store-words` through the existing
generated `fn2-digests-put`. Indexed effect and observation theorems cover all
eight word columns, other rows and metadata. Snapshot and overwrite lemmas
support reconstructing `fn2-mk-node` from its returned words. The two logical
Merkle writers and raw `fn2-b3-native-store` use this same scalar function; no
second hash algorithm or served octet list is introduced.

`fn2-native-mk-node-whole-effect` in `books/native-b3-correspondence.lisp`
consumes `fn2-a-crypto-native` on a specific `:fn2-b3-node` observation: captured
left and right word rows, the eight output words, and the digest carrier
protected during the C call. The reference observation uses the actual
`fn2-mk-node`, including aliased destinations. Equality of the output words
alone is insufficient: the C/FFI assumption must also preserve that protected
carrier. The theorem proves the following ACL2 store composition; it does not
prove the primitive supplies its assumed observation. This is neither a
collision-resistance assumption nor an assumption that the entire host works.

The existing equality local witness also proves the new
`fn2-a-crypto-native-identical-observation` constraint. Previously the abstract
predicate could be identically false. Reflexivity supplies genuine positive
observations without asserting that a particular C invocation produces them.
Whole-antecedent positive theorems exercise destination equal to the left and
right input, with distinct input rows and a protected sibling. The hypothesis
removal witness supplies the correct digest but changes the sibling: the result
is a different entire carrier and the primitive assumption is false.

`books/native-b3-evidence.lisp` connects this CRITICAL boundary to the live
fn2-squares/OWED registry, included by the node image and OWED exporter. Its
registered statement is taken from the admitted theorem's world property.
Formula-bound evidence proves the actual domain, all hypotheses and conclusion
for a concrete aliased call; its removal witness preserves the digest words but
corrupts the protected sibling. The removed primitive hypothesis and the
conclusion are both false, while the remaining hypotheses hold. Regeneration
checks the live statement and ABI, and the completion row names `fn2-mk-node`.
This registration retains the explicit C/FFI assumption.

`served_host_check` separately pins the complete source AST of the input loader,
node adapter and shared-store adapter. It checks the eight word offsets and
that both original input rows are captured before the C call and destination
write, including exact destination forwarding and reference fallback. Mutants
for a wrong output offset, overwritten captured word, swapped input, extra raw
write and bypassed shared store are refused. These are source-wiring controls,
not a proof of C memory safety, SAP semantics or native execution.

The zero-prefix startup qualification now compares the whole pool before and
after the primitive as well as its returned count. The focused SBCL fixture
executes the actual ACL2 reference body and raw qualifier with a foreign-call
substitute that returns the correct count and writes byte N outside [0,N).
The old qualifier at `09c4b380b` accepts this fault; the new qualifier refuses
it, including an empty span. This strengthens finite qualification only:
formal consumption of `fn2-a-native-span` remains open.

Author validation used a qualified warm dependency world based on `09c4b380b`,
then helper commit `688bab338`, in the isolated Forge native-contract lane.
The unchanged indexed observation, Merkle reconstruction and other-row frame,
conditional whole-effect theorem, both alias positives and full frame-removal
witness were admitted. The whole-effect proof took 3,691 steps / 0.04 seconds;
the two positives took 255 steps each, and frame removal took 437 steps.
These author results are retained under the lane's
`build/native-contract-author/`.

The current 19-book evidence closure passed qualified record certification
`certify-20261115T002302Z-613027` at authenticated
`68ab9f5620c71e63d2027558659b699d2e6d1934`. All 19 source files are byte equal
to root `07a4db98c`; the closure key is
`147eb51e774711f4a35251c33ddff602c57cd583067043b08759ba9e1929bc14` and source
identity is
`a29310e3b5dd74c9985763b5a44c5a33ca38f53e536be56e1b8f8120f204f645`.
Thirteen qualified compiled pairs were reused, including the separately
published current layout pair, and six books were certified and published.
Official triage found no failures, limits or killed processes. The record used
the toolchain below, with external memory cap 2,147,483,648 bytes and swap zero.
The whole-effect theorem cost 120,979 steps / 0.35 seconds; the evidence book
cost 1.119 seconds. Current Merkle cost 10.802 seconds and BLAKE3 cost 17.628
seconds remain D26 proof-cost work. This record covers the evidence closure,
not native execution or the full host. Its exact cache coordinates and
certificate/compiled-payload hashes are retained in
[`receipts/native-b3-evidence-68ab9f562.json`](receipts/native-b3-evidence-68ab9f562.json).

Current native execution subsequently passed on the **28-book qualified
world** comprising `native-b3-evidence` and `format-check`, with source identity
`588cfb732b69cc51417745b63bd332b8cc9b6770fe07db7a3299554b04792521`.
All 28 books and the raw adapter, gate, C build script, C sources and headers
(42 files) were checked byte equal to root `07a4db98c`. The necessary six
format books first passed qualified record
`certify-20261115T002747Z-617826`, reusing 15 dependencies with clean triage.
Native loading then used only qualified compiled pairs, with no certification
or source fallback. The C library was freshly built from those exact sources;
the compiler, build environment and library digests are recorded in
[`receipts/native-b3-runtime-68ab9f562.json`](receipts/native-b3-runtime-68ab9f562.json).

Actual startup qualification and both native destination-alias calls passed,
including equality of the entire digest carrier to the saved logical function
and preservation of the sibling row. The live detector reported **10,065
unchanged-or-declared bindings and eight declared replacements**. In a separate
process, a real C-backed zero-prefix call returned the correct count and then
changed byte N outside [0,N); qualification refused it with
`zero-prefix result or pool frame` before the success marker. These current
finite controls strengthen qualification; they do not discharge the C/FFI
assumption, `fn2-a-native-span`, other native refinements or the full-host gate.
Both processes ran under the external 2 GiB cap with swap zero and finished;
the baseline took 2.021 seconds and the fault control 2.072 seconds.

The exact donor `390c57de0e006e4ab06becf6c278daa04c4d7782` subsequently passed
record certification `certify-20261114T230520Z-536071`: 16 books, 12 qualified
compiled dependencies reused and four certified/published, with no triage
failures, under toolchain
`8aeb1bea18968c6cd33ac633a80ebf67e4924504db112fd27eb11f16a27b2a8c`.
The source identity is
`4deace910449b0db0f7c49e8dc37d1ea2a765ac5ad70cbba9ecb0b1533105d42`.
Merkle's 28.971-second whole-book cost remained a D26 issue; later hint work is
separate evidence. The donor certification does not cover newer profile or
operations source changes in the composed root.

Actual native execution then passed on the narrower **25-book qualified donor
world**, loading `native-b3-correspondence` and the actual zero-prefix provider,
`format-check`. No source fallback or cold certification ran. Its source
identity is
`82a7566fac33e240ab7bd0b3550af1c2062422645cf53c1ca34c19dff0940e2a`.
Raw BLAKE3, shared-store and C input bytes were checked against current
`66f61818a11dec05d49d8d383897d1e3d9981b69`. The C library was reused only after
matching its C-source and compiler receipt. Process startup qualification,
whole-carrier equality for both actual aliased native node calls, and the
protected sibling passed; the binding detector reported **10,034
unchanged-or-declared bindings and eight declared replacements**.

A separate process interposed an actual C-backed zero-prefix call that returned
the correct count, then changed byte N outside [0,N). Qualification refused it
with `zero-prefix result or pool frame` before the load-success marker. This
establishes frame sensitivity of the qualifier, not universal C memory safety.
The donor-model/current-primitive scope is retained in
`build/native-contract-runtime/`; it is not a current-root or full-host pass.

The eventual full-host batch must load this contract book in the same current
world as TLS and `tests/native-device-fault-boundary.lsp`. Earlier e892 native
qualification and historical A155 runtime success do not cover these changes.
