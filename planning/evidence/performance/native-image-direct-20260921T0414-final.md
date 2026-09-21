# Current-path performance measurement

- Owner source: `not-run`
- Harness revision: `045096e2e5d6a1c1b52bd81625d7bd4a80430d5f`; harness SHA-256 `c12e34afba4ea790f58320fbcaf69c10e673198a0fb2c549afb31d7657e395cb`.
- Host: `Linux-6.11.0-29-generic-x86_64-with-glibc2.40`; load at start `(1.37744140625, 1.82861328125, 2.291015625)`.
- Owner scope: development-oracle evidence only: `bin/fn post` through the live `bin/fn run` control socket; each accepted post reports `path=control`. This Python bridge path is not a production endpoint.
- Native scope: direct native-image `--fn store` / `--fn reader` calls with no Python child; it does not measure served owner/control behavior.

## Owner results

- Owner path: skipped by --skip-owner; no owner/control claim.

## Recovery and native direct

- Owner recovery: not-run (exit not-run).
- Native direct: source 452828c4bd9fa2c2e60122d0ab9f51a26101baba image-sha256 f6f9581fa1fd92c93de8eec9b5e50d3e44d48496aa289c5735b3242e45db29c9.
- Native direct init 0.355276s, one accepted 1024-byte post 0.174939s, recovery 0.025273s; cumulative child peak RSS 55552 KiB.
- Native reader startup 0.100956s; first greeting 0.010764s.

Commands and full per-invocation outcomes, source hashes, exact input sizes, RSS, tool versions, and logs are in the adjacent JSON artifact.
