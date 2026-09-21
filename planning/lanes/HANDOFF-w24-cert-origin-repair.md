# W24 certificate-origin tooling repair handoff

Branch: `w24/cert-origin-repair`

Code/test commits: `16176d65`, recovery checkpoint `8758c4c5`, and the
follow-up commit recorded in the evidence note.

The farm no longer runs the legacy per-book certificate installer.  Before a
targeted run it selects the exact roots with `certify_books.py --dry-run`,
matches the remote ACL2 executable digest, and installs one dependency set
whose source, toolchain, and absolute origin are coherent.  Incremental reuse
requires the dependency origin to equal the remote root the run will extend.
If that set is unavailable, no ACL2 process starts; `--closure` is the explicit
recovery path and purges stale pairs before dependency-ordered recertification.

Owned files:

- `tools/certs.py`
- `tools/certify_books.py`
- `tools/farm.py`
- `tests/test_certs.py`
- `tests/test_certify_runner.py`
- `tests/test_farm.py`
- `planning/evidence/cert-origin-coherence-2026-09-21.md`
- adjacent exact manifests/logs/test artifacts

No requirement/proof registry, BOARD, shared cache, ACL2 executable, production
profile, or book was changed.  No ACL2 certification was run.  Exact failures,
the source bug, test invocation, results, and remaining real-farm validation
are recorded in the evidence note.

Post-reboot recovery replaced the launcher regex with a finite recognizer for
the small generated-launcher subset.  It reads at most 64 KiB, follows at most
one outer wrapper, streams the launcher/core/runtime hashes, and never executes
an unknown launcher to infer its identity.  This recognizer is deliberately not
a shell parser: unfamiliar commands, shell control operators and dynamic paths
remain unqualified.  Runner and reader hashes are retained as certification
provenance but do not fragment a compatible artifact set.
