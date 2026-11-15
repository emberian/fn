# Physical reader provider packet

This SOURCE packet is based on current cold parent `255b5d598`, including its actual RELEASE producer and credit setup. The implementation source is `e887f9bb4`; the machine-readable [manifest](receipts/loader-current-packet.json) binds the exact files and current ROOT comparison. No ACL2, native or remote job was run for this packet. Earlier pinned34 qualification and bound66 partial author evidence do not qualify this source.

## Named changes

- `ba7c2238b`: import the existing `run-physical-bound{,-bind,-io,-step}` engine, source-gated `run-physical-{source,io,step,release}` wrappers and `checkpoint-source-loader`. They retain actual full Refs, owner tuples, operation identities and checker state. No second parser, hash, allocator or caller readiness flag was introduced.
- `runs.lisp`: extend cursor/path physical Ref state and add the original helper definitions. Preserve every parent cache and installed-row transition. `runs-assemble.lisp` dispatches a physical MISS through authenticated loading and preserves the existing resident path; header/child/up dispatch retain exact child and parent Refs.
- `checkpoint-metadata.lisp`: only ordinary run begin/step use the installed-source constructor and cursor owner. The archive's role/witness changes stay with its owner.
- `checkpoint-metadata-driver.lisp`: the real root1 callback borrows dedicated existing working windows, issues physical reads separately, waits for the real completion and detaches its read/catalog ownership before DONE. It has42 inputs,31 maximum STEP results and19 READ results. The actual parent prefinish hook remains the completion path.
- `checkpoint-metadata-release.lisp`: normal publication release additionally requires the real reader detached predicate. The current working-credit release primitive and every RELEASE producer remain unchanged.
- `machines-b.lisp`: only the cursor count family changes. Root1 retains its profile-derived row; archive gets the next row. From actual row counts, root1 is `rows-2` and archive is `rows-1`. The shared predicate requires at least two rows before selection; the advertised selector guards and actual root1 consumers enforce it. No B initialization group is changed.
- `machines-c.lisp` and `run-physical-readiness.lisp`: use the same canonical cursor geometry. The one additional cursor row grows existing profile-derived cursor/path/checker/field/digest allocations; it does not add a stored-data ceiling. The parent's already-admitted29-window working geometry is unchanged.
- `cd9023f93`: reject zero/one-row direct carrier geometry and preserve pending `:wait`, allowing the actor to idle until its actual completion. The initialized production-carrier zero/one/two fixture is authored but unexecuted.

## Separate byte quota change

`e887f9bb4` changes only six source/root1-consume charge sites plus the byte quota. Let `C` be the actual assembled `*fn2-c-read-callback-bytes*`: its existing formula derives from registered entry/key maxima, restart decoding, bounded comparisons and sector work. The reported turn charge is `C+4096`; the master byte quota is `16384+2C`. An ACL2 assertion checks `C+(C+4096) <= 16384+2C`. A source control checks that each actual master arm contains at most one C-cost root1 operation. Other current states and charges remain intact.

The structural step contract is unresolved: root1's defcost currently omits steps, whose default is0. Retaining32 master steps and4 descriptors is not a proof of the leaf's decoder/field work or of the whole turn. The byte inequality is not a progress theorem. In particular, this packet does not treat an unchanged `:more` return at a small budget as progress.

## Actual caller and review cut

The real caller root is `books/checkpoint-master-events`, through the existing source/read/page-consume arms and generated callback faces. Its activation gate remains false. Narrow reviewed module roots are `books/checkpoint-metadata-driver`, `books/checkpoint-metadata-release`, `books/run-physical-bound-step` and `books/run-physical-bound-bind`; `books/run-physical-release` supplies ordinary catalog-owned cursor teardown.

Run the two named Python source controls in the manifest. They check exact shared engine provenance, current RELEASE/foundation preservation, B event order, return limits, fixed-row gates, scoped charge projection and an acyclic complete literal include graph. These checks establish source composition only. The archive owner must compose schema/internal declaration and selected-source/witness changes, and the decoder/caller-cost audit must finish before a wide archive entry or full serving claim.
