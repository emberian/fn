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

The native BLAKE3 startup segment also passed against the actual qualified ACL2
world at frozen `e892441f7df396d3eb8b6c88b2d8dbec2ac76aa6` on November 14.
Its roots are `books/merkle` and `books/fnct-pool`, with a 31-book union closure
and source identity
`5ed1e8233409b65ec4290cabc85668bd8f3df6474460c744d32d82c6e6e2e691`.
The record toolchain identity is
`8aeb1bea18968c6cd33ac633a80ebf67e4924504db112fd27eb11f16a27b2a8c`.
Merkle's necessary one-book delta was certified in
`certify-20261114T214743Z-456637`: 12 qualified compiled dependencies reused,
one book built in 28.41 seconds, and no triage failures. That whole-book cost
remains above D26; it is not a performance-completion claim.

The native check installed all 31 qualified pairs, built `libfn-blake3.so` from
that checkout with `host/build-blake3.sh`, and executed the process startup
qualification and the real generated binding detector. It reported **11,331
unchanged-or-declared bindings and eight native assumptions** in 2.574 seconds.
The receipt binds the compiler identity, ABI description, current substitution
map, generated driver, 51 source/helper digests and the newly built library;
all input digests and library bytes remained unchanged through the run. The
library SHA-256 is
`36a16c26476b4f1add88fcadef34cff5242dbfd88eea3bcb1855ccbc71a21baa`.
This is startup qualification plus binding identity, not native refinement or
complete process-load attestation.

Two controls then ran against that real qualified world. A dynamically named
replacement of `FN-B3-W32`, absent from the raw call inventory, changed its
executed result from 1 to 0. A replacement of the declared
`FN2-FC-ZERO-PREFIX` likewise changed a fresh zero-filled pool's observed result
from 1 to 0. Each process exited 1 with the exact named raw-replacement diagnosis
before `FN_SERVED_HOST_LOAD_OK`. The successful baseline and both actual-world
controls are retained in the isolated snapshot
`forge:/build/lanes/assumption-load-e892441f7-git/build/assumption-native-*`.
Local copies and a digest index are in the load lane's
`build/assumption-native-e892-evidence/`.

The full composed host `--load` remains pending. At `e892441f7`, its
`books/node-profile` plus `books/merkle` closure has 168 books. The active
130-book callback closure is a subset; after the Merkle leaf, 29 additional
uncached prefix books remain beyond that callback closure. Reuse its qualified
artifacts, then recompute the exact delta for the integrated TLS/current-host
revision before certifying only the missing ancestors. Run the full host load
gate and the explicit `tests/native-device-fault-boundary.lsp` companion against
that same composed world. The current source-only raw-device tests and the
historical A155 runtime pass do not discharge that companion. Later TLS and
device-fault changes, including root `5686fb26d`, are outside this frozen native
segment's scope; no server was started by these checks.

No complete reachable-guard/attachment inventory is established here.
Constrained attachments, raw state/constant changes, startup side effects, later
function rebinding (including restart hooks), native C semantics, and complete
source/image/library execution identity remain separate boundaries.
