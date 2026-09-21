# Current-path performance measurement

- Owner source: `not-run`
- Harness revision: `1720cd2a01e27ff0f02df4ccfb845e40c5856fba`; harness SHA-256 `aa86479d41182b3d6f6ab169a1a1cd20925319790f9d9c01b374a5a39448426d`.
- Host: `Linux-6.11.0-29-generic-x86_64-with-glibc2.40`; load at start `(0.74267578125, 1.81689453125, 2.642578125)`.
- Owner scope: development-oracle evidence only: `bin/fn post` through the live `bin/fn run` control socket; each accepted post reports `path=control`. This Python bridge path is not a production endpoint.
- Native scope: direct `tools/run_store.py` / `tools/run_reader.py`; it does not measure served owner/control behavior.

## Owner results

- Owner path: skipped by --skip-owner; no owner/control claim.

## Recovery and native direct

- Owner recovery: not-run (exit not-run).
- Native direct: source 81e9a2259f180a854609764426cbcb3e3b1bf141 image-sha256 9bb4e657858aa91b1aff16f87c78aee8d1e9a2323dafb75ee17e2df0278c9213.
- Native direct init 0.691737s, one accepted 1024-byte post 0.219218s, recovery 0.053533s; cumulative child peak RSS 55588 KiB.
- Native reader startup 0.100944s; first greeting 0.006469s.

Commands and full per-invocation outcomes, source hashes, exact input sizes, RSS, tool versions, and logs are in the adjacent JSON artifact.
