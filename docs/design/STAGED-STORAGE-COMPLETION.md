# Staged storage completion integration

This package exposes the simulator's existing physical effect before terminal
publication. It copies staged implementation source from `e0dbbfee9` onto
`dd7af355c` (which differs from `b770d16e9` only by the primitive-test Makefile
registration). It preserves the predicates, guards and theorem statements;
it does not qualify this new root or a real device.

On `:returned`, `fn2-sim-native-stage` has called `fn2-sim-physical` once
and exposes a raw packet and active=4 with no terminal post. The packet is
`(slot gen kind event len code count aux word now fault)`. Its count is the
reported return count, not an independently established effect footprint.
Holding this state exposes completion withholding. `fn2-sim-native-post`
uses the same `fn2-sim-complete-result`, scalar normalizer and terminal publisher
as ordinary completion. `fn2-sim-find-write` selects only active=1, so crash
scanning cannot repeat an already performed active=4 write.

The scheduled split is currently **Fence only**. The explicit paired stage/post
API now stores the raw return for every kind it accepts, and requires exact
saved-packet equality before publication. This packet-binding repair is source
only; its general physical-result domain/guard proofs and new controls have not
executed. It does not establish scheduled Read/Write withholding.
Active=3 retains its Send early-release meaning and is unreachable for a fresh
Fence in this domain. The supported-storage antecedent and every output of
`fn2-sim-native-finish-is-atomic` remain unchanged.

The physical transfer uses the existing byte/storage implementation. Effectful
EIO/ENOSPC, failed-fence persistence and commit uncertainty are not added here;
the storage continuation owns those changes. They must preserve physical effects
separately from the subsequently reported result. Native `:failed` versus model
`:io` correspondence also remains outside this package.

Six CORE-OWN projections move verbatim from `sim/check.lisp` to
`sim/check-core.lisp`; the original checker includes that book. This removes
assembled TRACE/WORK/reference dependencies from physical transfer. OWN proof
hints use the existing profile field facts and declaration-derived public
column reader/bound interfaces; function guards and bodies are unchanged.

## Evidence and limits

The following executed in a Forge world with qualified common core103 on the
older authentic440 source, plus the named OWN override from `cdc0a8e44`:

- OWN book: 18.00 s; initializer guard 0.07 s, issue observer guard 0.19 s.
- Transfer source admission: 7.89 s wall; physical adapter: 174.85 s.
- Simulator source/guard admission: 169.138 s, one original LOCAL scope.
  An AST control verified the original event order after budget-only wrappers;
  a postcondition checked that its two private lemmas did not leak.
- Cut-program source admission, including the whole-state atomic theorem:
  theorem 3.88 s / 137,724 steps; whole program load 45.869 s wall.
- All nine mutable operation-cut controls: assertion passed in 0.12 s.
- The separate raw-state unit was record-certified on `d6be64b81`: 14 reused
  dependencies, one changed test, 0.818 s. Its count=3/aux=5 values distinguish
  columns and are explicitly unreachable for a physical Fence.

These are historical source admissions and finite simulator controls, not
certification on `dd7af355c`. Exact-root guards, certification and the storage
continuation's composed withheld-Fence controls remain pending. The long
adapter/main loads remain proof-cost defects.

The nine-control test is the exact admitted prefix of its donor, ending before
the immutable-witness experiments. The positive whole-formula witness previously
refused on nested-stobj NON-EXEC evaluation; hypothesis removal was not reached.
Those unadmitted drafts and the native real-fd/replay pilot are excluded here.
R22 whole-witness completion, current scheduled ENVELOPE controls, real-fd
execution, universal cut mapping and host refinement remain pending. The default
native program gate must continue to refuse incomplete mapping.

## Copy integrity and local gates

`staged-storage-completion-source.json` records donor file hashes, canonical
function/macro forms and explicit theorem statements. The six moved wrappers
match the root originals. The test prefix matches its donor forms exactly, and
the Makefile adds only its two test registrations, preserving the primitive
registration. This establishes source-copy integrity, not semantic proof.

Local packaging gates are strict Lisp parsing, secrets/diff checks, the focused
served-native source controls, source-only native audit, and dry-run selection
of each new test root. No ACL2, native build, remote allocation or production I/O
is performed to package this commit.

On this packaged root, strict parsing and copy/move/Makefile integrity controls
passed; all 26 focused served-native Python controls passed. The source-only
audit passed (17 source cuts) and still reports `cut_mapping_status=incomplete`
and `host_refinement=not_checked`. Each test's dry-run affected-by selection
returned only that test. These are local source gates, not proof or runtime
qualification.

## Explicit-cut packet binding repair

The original explicit API saved only Fence results, so a caller could stage a
Read or Write, change its raw code/count, then publish that different result
without another physical effect. The repair saves every returned packet before
setting active=4 and removes the non-Fence equality bypass in `native-post`.
`complete-result` saves the same representable receipt on the atomic path,
retaining the existing whole-state staged/atomic equality statement. Function
arguments and guards remain unchanged; the receipt absorption helper is stronger
because it drops its Fence-only hypothesis. `native-post-rejects-changed-return`
states the full unchanged core/sim/OWN frame on packet inequality.

The same `defcolumns` enum adds actual physical refusal codes `:exhausted`,
`:state`, and `:owner`, after the original fourteen tags. Count/aux remain u32;
the packet retains all eleven coordinates. The domain fact must connect the
actual transfer count bound and dispatch result codes to those generated fields;
its new proof and the generalized stage guards are **unexecuted**. This is not
an admission claim. `sim/native-cut-state` is unchanged, allowing the separate
storage write-EIO fault-list addition to compose without an overlapping edit.

`tests/native-cut-binding-unit` issues a two-byte Write with a one-byte short
physical prefix and a two-byte Read that copies one initial-image byte before
reaching disk bounds. It checks the actual raw code/count and byte projections,
rejects changed code/count/aux/word/time/fault/generation, keeps the original
packet usable once, refuses its duplicate, and refuses physical reissue while
active=4. These assertions are prepared, **not executed**. The existing admitted
nine-control source is byte-identical and is a dependency of the new unit.

`staged-packet-binding-source.json` records exact file hashes and verifies all
existing function declarations/guards plus the full atomic theorem statement
against root `b2c2083e2`; the older packaging manifest remains historical.
Strict parsing, secrets/diff checks, the 26 focused Python source controls, the
source-only cut audit, and the new unit's isolated dry-run selection passed.
No ACL2/native/record gate or remote allocation ran for this repair. Global cut
mapping remains incomplete and host refinement remains unchecked. The next gate is actual general-domain/guard admission followed by
this mutable unit and the unchanged full atomic equality proof, in a coherent
allocated source-matched world.

## Current return-domain proof preparation

On integrated `8ef310`, the new proof support stays local to `sim/sim.lisp`.
A shared local macro generates return-tag contracts for the actual pool,
network and storage calls. The transfer proof composes those contracts and
inducts on the existing byte loop; a separate prefix bound and selected-amount
bound supply the reported-count limit. The physical dispatch then composes
these facts with the network nonce type. The public return-domain proof keeps
the dispatch, codec and byte loop opaque. The older Fence proof hint names the
now-called `fence-complete-from` primitive. These are source-prepared proof
interfaces, not admitted facts.

All existing function definitions and explicit theorem formulas compare
identically to that root, including the whole atomic theorem; the receipt is
`staged-return-domain-support.json`. No additional foundation book changes.
Strict parse, secrets/diff, and all 31 current focused native source controls
pass. ACL2 admission, mutable controls and the combined cancel/storage execution
remain unrun. The current 125-book combined test closure had only nine exact
compiled qualified cache candidates at the read-only inventory: moving faults
out of `books/operations` changed 116 closure keys. The older f64 86/38 inventory
and its 29 matching main-b2 misses cannot qualify this newer root. No parallel
cold build, install or ACL2 session was started.
