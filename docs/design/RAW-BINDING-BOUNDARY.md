# Raw startup binding boundary

`tools/served_host_check.py --load` now refuses an undeclared change to an ACL2
world function binding during the launcher's raw startup. This is a runtime
identity check at that boundary, not a native output/effect refinement theorem.

The served trace is concrete: `tools/image-node.lsp` includes `books/node-profile`
and `books/merkle`, enters raw mode, and loads `host/b3-native.lisp`, `host/ffi.lisp`,
`host/adapter.lisp` (which loads `host/device.lisp`), and
`host/native-serve-raw.lisp`. For example, `fn2-n-complete` in `host/adapter.lisp`
calls `fn2-host-result` in `books/host-boundary.lisp`, which delegates to
`fn2-sim-terminal-values`. A raw replacement can affect this chain without
changing ACL2's stored guard-verification status.

Before this repair, the load check inspected direct callees' ACL2 `symbol-class`
before raw loading and only `fboundp` afterward. Executed SBCL controls against
the frozen `06b1785df` generator accepted both a raw `defun` replacing a guarded
entry and a dynamically named `symbol-function` replacement of a logical leaf
absent from the raw call inventory. Each control executed the corrupted
raw-to-entry-to-leaf result before the old gate reported success.

The repaired generator snapshots actual `fdefinition` objects and unbound states
of symbols with a `symbol-class` in the live ACL2 world, across all packages.
Special operators have no ordinary function cell and are excluded. It checks
those cells after executing the actual raw load prefix. An undeclared changed,
removed, or newly filled binding is refused, including transitive callees absent
from the lexical inventory. Existing direct guard and post-load binding checks
remain in force.

`NATIVE_REPLACEMENTS` independently declares the eight intentional BLAKE3 pairs;
it is not read from the host's mutable `*fn2-b3-native-entries*`. Each target must
already have a guarded ACL2 binding, and its installed function object must equal
the selected native implementation's function object. Tests compare this explicit
map with the current host declaration. The logical assumptions remain
`fn2-a-crypto-native` in `books/assumptions-integrity.lisp` and
`fn2-a-native-span` in `books/assumptions-native-span.lisp`; this identity check
does not connect either predicate to native outputs or state effects. Current
obligations are declared through `books/owed.lisp` and exported to `docs/OWED.md`;
the historical `tools/keystone_critical_map.json` is absent from this tree.

Validation on this lane: the 29 named-module controls in
`tests.test_served_host_check` and `tests.test_served_native_program_check` pass,
and the served source audit reports five raw sources with zero findings. New
runtime controls execute the real generated detector under SBCL; ACL2 metadata
lookup is a small stand-in. They cover unchanged bindings, actual reached
corruption, raw `defun`, unbinding, filling an unbound logical name, exact selected
native identity, wrong or omitted installation, and missing guarded targets.

The qualified composed `--load` gate remains to run on the integrated certified
world. This lane performs no ACL2 certification and establishes no complete
reachable-guard/attachment inventory. Constrained attachments, raw state/constant
changes, startup side effects, later function rebinding (including restart hooks),
native C semantics, and source/image/library identity remain separate boundaries.
