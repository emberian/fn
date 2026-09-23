# BP kind-5 publication, mixed namespace, and operation width, 2026-09-23

The guarded foundation and A2 byte books now compose the received kind-5
publication authority with one-directory recovery classification.
`fn-bpnf-publication-authorize` takes the exact pending `:persist` echo and
observed lock/name facts; on success ACL2 supplies the final name, frame,
and initial publisher. `fn-bpnf-mixed-recovery-plan` splits the one physical
FNBS namespace and applies the old contiguous planner to legacy names and
hidden stages. Kind-5 row bytes remain subject to `fn-bpnf-replay-rows`.
There is still no native caller of these functions; the current service calls
the outbound-only machine, and `bp receive` uses the older receive path.

The machine now refuses a new reception when the epoch is outside the frame's
unsigned 64-bit range or the next operation ID is the maximum 64-bit value.
The last issuable ID increments to that terminal frontier, which cannot
issue again. Tests exercise both sides of this boundary. The ordinary
uncertain-state fence and recovery-only exception remain unchanged.

ACL2 8.7 / SBCL 2.6.8 on hbox, toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`,
passed these exact source digests with jobs 2 and no `--closure`:

- `run-20260923T181330Z-4900`, manifest
  `planning/evidence/manifests/certify-20260923T181332Z-4063622.json`:
  mixed namespace book and test before the width change.
- `run-20260923T181203Z-c0fc`, manifest
  `planning/evidence/manifests/certify-20260923T181209Z-4061712.json`:
  publication/codec affected sweep before the width change.
- `run-20260923T181544Z-94d1`, manifest
  `planning/evidence/manifests/certify-20260923T181547Z-4065137.json`:
  foundation, guards, replay, codec, publication, and test roots after the
  width change.
- `run-20260923T181723Z-7e8f`, manifest
  `planning/evidence/manifests/certify-20260923T181726Z-4066781.json`:
  five remaining A2 roots affected by the changed foundation bytes.

The strict `green_check.py --changed-since b4e1855c` report found zero
ungreen among 21 changed books and four dependent roots. `make check` passed
after regenerating the ledger locally; generated ledger files are left for
the integrated root to regenerate. These are ACL2 book and source checks,
not native image or receive-loop evidence. The native publisher/recovery join,
admitted-principal boundary, and physical callback lifetime assumption remain
open.
