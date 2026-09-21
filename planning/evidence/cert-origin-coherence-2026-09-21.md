# ACL2 certificate origin-coherence repair, 2026-09-21

Status: tooling regression fixed and locally tested.  No ACL2 closure was
re-certified and no shared cache or toolchain was modified for this packet.

## Observed failures

Two persvati runs used the pinned
`/home/ember/fn-tools/acl2-8.7/saved_acl2` executable (SHA-256
`c8a7a804d9cc80e2025a8ab0e1d9325f2a0c4a027a5dcdcb2c1093e9cd5c8163`).
Both certified `books/wire-invariants` and
`books/bp-receiver-state-invariants`, then failed while certifying
`books/served`:

| Run | Tree | Archived manifest | Served log |
| --- | --- | --- | --- |
| `certify-20260921T110538Z-3055091` | `/home/ember/fn-lanes/w19-bp-fast-invariant` | `a734bd038b9da41f076af955b6dc4d5ff50b3bd389d03c70bc68fdc83ec59157` | `8b96283236a668c4629250a393ac63e8ab611bcb4a4788866aaac3e4289f3d53` |
| `certify-20260921T110653Z-3068248` | `/home/ember/fn-lanes/w13-owner-integrated-gate` | `5e8164c644d9c8cba36b5ff2976d43df1a47c4256d618278568431368ed6b15f` | `9291ed5a2beb6c74936bb10344546abc5ba20a9e1bd4429f2e8d7951a2b89e21` |

The exact manifests are in `planning/evidence/manifests/`.  The exact failing
per-book logs are beside this record.  The first log shows one `peer-inbound`
certificate requiring dependencies under
`/Users/ember/dev/fn/build/lanes/w18-native-bp-app`, while familiar-name
dependencies had already been included from `/home/ember/fn-lanes/w12-bp-sequence`,
`/home/ember/fn-lanes/w19-bp-authored-wire`,
`/Users/ember/dev/fn/build/lanes/w22-native-auth`, and
`/tank/fn/lanes/w9-records`.  The second failure repeats the same condition in
the intended canonical tree, mixing `/Users`, `/tank`, and several `/home`
origins.  ACL2 correctly refused the different full-book-names; source content
hash equality did not make their absolute names interchangeable.

## Cause and repair

`tools/certs.py` already had the production `install_artifact_set` selector,
which groups a whole requested closure by source set, ACL2 toolchain, and
absolute origin.  `tools/farm.py` still invoked the older per-book `install`.
That command independently selected an entry for each closure key, so a
source-identical parent from one origin and child from another could be copied
into the same remote tree.

Farm submission now performs a preflight before starting ACL2.  It asks the
certification runner for the exact selected roots, hashes the ACL2 executable
on the farm host, and installs one coherent set for the selected roots'
unselected dependencies.  Because the run will author the selected roots at
the remote path, the reused dependencies must also have that exact origin.
An unavailable set refuses before ACL2 starts and directs the caller to
`--closure`.  With `--closure`, a set miss removes every `.cert`/`.port` pair
in the selected closure and the existing dependency-ordered scheduler authors
the closure under one root.  A complete matching set may still be installed
before the explicit recertification.

The per-book publication path now records the toolchain identity immediately.
This matters when a run is killed before its final cache sweep: its passing
books remain selectable by the same coherent-set rules rather than being
present with an all-null toolchain identity.

## Regression evidence

Command, from source commit `16176d65` atop baseline
`8659ec48ce894e8b317793a65b96ba8123e823d7`:

```text
python3 -m unittest tests.test_certs tests.test_farm tests.test_certify_runner
python3 -m py_compile tools/certs.py tools/certify_books.py tools/proof_artifacts.py tools/farm.py
```

Result: 87 tests passed in 23.404 seconds with Python 3.14.7 on Darwin arm64;
the compile check exited zero.  The regression creates two source-identical
origins whose certificate bytes name different absolute parent/child paths. It
first demonstrates that legacy per-book installation constructs the invalid
mixture, then shows set installation refuses it without copying either pair.
Separate cases establish exact-origin selection, dependency-only incremental
reuse, stale-pair purge on explicit closure recertification, farm refusal before
ACL2, and the immediate-publication toolchain identity.  The complete test
output and artifact digests are archived beside this record.

Limitations: these are deterministic tooling tests, not an ACL2 certification
or a farm qualification run.  The next real targeted run should use the
canonical `/home/ember/fn-lanes/w13-owner-integrated-gate` origin and preserve
its cache-preflight identity in the farm record.  A miss must be handled by an
explicit `--closure` run; the tool does not combine partial origins or suppress
ACL2's full-book-name checks.
