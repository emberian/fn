# Shared cleanup transformation: root and cold

This donor is tool/test/fixture-only on parent cold `b7f18ce94`. Runtime books are
unchanged. Parent already composed the cleanup through `9405d5019`, `15c5023fb`,
`c82a0af56`, `bf015035b`, and `b7f18ce94`, retaining its physical installed-source
refusal and `:busy` park branch.

`project(before, before_schema)` now requires explicit canonical before
`defcolumns` declarations and checks they agree with the actual input sources.
Physical-column presence controls retention of the physical-root fence; its
absence is not a caller readiness flag. A wrong schema refuses before editing.
The same six-form draining recipes compose on the resulting actual source.

Two independently frozen exact cases are retained:

- ROOT099 input to frozen root800fa output, including the exact original held
  fixture. Original full-book byte equality is unchanged and does not depend on
  the mutable cold tree.
- Cold a565 input to already-composed b7f runtime output. Exact full-book equality
  and cold semantic controls retain the physical fence before cache/pool access,
  stored owner tuple, and the original `:busy` park path.

`fixture_source(schema, label)` emits every actual row column. Nonpool scalar
extras generate one complete snapshot helper per carrier; all installed-table
comparisons use that helper. Physical count, version floor and future appended
scalars are kept if declared, never dropped unconditionally. Pool scalars are
also inventoried; unsupported new arrays refuse rather than silently disappear.
ROOT099's empty-extra case still reproduces its existing fixture exactly.

The cold held fixture has been regenerated with complete actual physical/source
columns and the physical-count scalar. It is prepared and unexecuted. No runtime
books, ACL2, cache artifacts or installation state were changed.

Commands (source checks only):

```
python3 tools/seal_cleanup_current_projection_test.py
python3 tools/seal_cleanup_cold_projection_test.py
python3 tools/seal_cleanup_current_projection.py --case root
python3 tools/seal_cleanup_current_projection.py --case cold --check-current
```

Explicit cold regeneration from the actual current schema (writes the test leaf
only after checking production output; never overwrites `books/runs.lisp`):

```
python3 tools/seal_cleanup_current_projection.py --case cold --check-current --emit-held tests/seal-release-row-held-unit.lisp
```

The frozen cold fixture is separately retained for before/after controls. Future
physical-root refusal controls should be a separate test leaf or an explicit
fixture-generation extension so regeneration cannot silently erase them.

Incoming cold adoption must still refuse DRAINING before the old private skip in
`fn2-checkpoint-live-adoption-retire-overlays` when that adopter is imported;
the parent has not imported that book yet. This tool repair grants no merge,
runtime qualification, activation, payload retirement or FREE authority.
