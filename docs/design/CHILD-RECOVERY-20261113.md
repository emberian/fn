# Child-form recovery (GPT-6 Astra, 2026-11-13)

The sibling-machine table discovery generator and its focused positive/negative
fixture are certified on forge. The remaining operation-child extraction is a
recovered checkpoint, **not ready for integration or claimed certified**.

## Verified small change

`fn2-arms-extra-children` now resolves registered machine stobjs referenced by
child operations even without a typed link. Ordinary unregistered stobjs still
fail. `tests/machine-child-tables-unit` exercises both cases.

Forge `/build/lanes/stride-acl2-children`:
- `build/acl2/certify-20261113T220731Z-3289748`: machine-arms + 16 dependencies passed.
- `build/acl2/certify-20261113T221208Z-3294811`: focused unit passed, 17 cached dependencies.
- The focused unit also loaded all 15 forms in proof_repl.
- `tests/machine-arms-unit` broader run is red at the existing
  `fn2-arms-probe-run-loop-children-keeps-directory` theorem before the new fixture.
  Its run is `build/acl2/certify-20261113T220851Z-3291257`.

## Recovered extraction, not yet validated

The agy worker left seven other books changed: assembly-index, authority,
commit, machines-b, machines-c-bind, machines-c-groups, upload. It had neither
created its forge tree nor executed remote certification. The work extracts
child bodies and replaces core bodies with wrappers; no served machine has
actually been switched to child form yet.

Recovery fixed a concrete name collision: the newly introduced zero-argument
macro `fn2-commit-child-events` collided with an existing recursive function.
The new macro is `fn2-commit-operation-child-events`, called in assembly-index.
Other duplicate defun/defmacro names were checked in changed books; none remain.

Next validation: machines-c-bind and machines-c-groups in proof_repl, then the
new B child macro materialization in assembly-index, then authority/upload;
only switch txn after the called child faces and their guards/refinements work.
The large extraction needs review for semantic equivalence and generated facts,
not merely admission. Carrier factoring remains unimplemented.

## Shared work

Integration includes Kimi profile/CNS fixes at 2d120e941. Composed-build owns
machines.lisp row-width repair. Served-names owns new authority lookup opcode
and arms above the refactored helper block; merge its validated result before
composed authority checks. Durability-frames owns cross-kind frame proofs.
Forge jobs require parent allocation; use 8–12G and at most two ACL2 jobs.
