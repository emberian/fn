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
These are author REPL results, **not record certification**. Runtime
qualification of the newly connected shared-store path also remains pending.
Evidence is retained under the lane's `build/native-contract-author/`.

The eventual full-host batch must load this contract book in the same current
world as TLS and `tests/native-device-fault-boundary.lsp`. Earlier e892 native
qualification and historical A155 runtime success do not cover these changes.
