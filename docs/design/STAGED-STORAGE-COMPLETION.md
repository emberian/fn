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

The scheduled split is currently **Fence only**. Only Fence stores the packet
in return columns and checks exact saved-packet equality at publication.
The explicit cut driver can carry Read/Write packets in its caller; this does
not establish scheduled Read/Write withholding or arbitrary-packet safety.
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
