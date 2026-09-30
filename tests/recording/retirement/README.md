# Retirement source regressions

These packets preserve independently executed actual-function recording
regressions. Each Lisp fixture contains the exact native function snapshot
under test, recording I/O or clock/core stubs, and a real SBCL thread or
mutex. The result files name the source and fixture hashes and their scope.
They are neither an ACL2 proof nor a qualified native image or disk test.
Changed function bytes require a new packet; these results do not transfer.

- `caller-baseline.lisp` reproduces direct stopped-line write and descriptor
  close while a timed-out writer remains alive. `caller-repair.lisp` asserts
  retained descriptor/path and only the initial write after timeout, and
  exactly one close after a definite join.
- `deadline-baseline.lisp` records a predeadline observer blocked by the
  semantic mutex beyond the deadline. `deadline-repair.lisp` asserts that
  the same actual observer returns before deadline while the real mutex
  remains held, then marks deadline and stop on the next clock observation,
  with zero semantic calls. It does not cover the complete accept loop,
  existing maintenance, final worker settlement or process exit duration.
- `observer/actual-observer.lisp` records the later actual observer, roster
  macro and pure decision bodies: a held semantic mutex, 25 forced stale
  waits after concurrent deadline, 25 paired deadline observations and a
  completed observation that performs no clock call. It preserves completed
  record identity and stop. `observer/generate.py` archives the original
  coordinate-specific extraction recipe; its absolute paths are historical,
  not a portable test runner. The immutable Lisp snapshot is self-contained.

Run each fixture in a fresh selected-toolchain SBCL process with
`sbcl --script FIXTURE`. Baseline files preserve the failure rather than
asserting repaired behavior. The core action in the caller fixture is the
actual pure definition evaluated as Common Lisp; the clock fixture uses
recording clock/core stubs. Neither grants production attachment authority.
