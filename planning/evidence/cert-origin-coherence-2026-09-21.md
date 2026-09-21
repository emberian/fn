# ACL2 certificate origin-coherence repair, 2026-09-21

Status: tooling regression fixed and locally tested, including the post-reboot
launcher/core/runtime recovery.  No ACL2 closure was re-certified and no shared
cache, system ACL2 installation or toolchain was modified for this packet.

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
per-book logs are beside this record as deterministic `gzip -n` archives; the
table gives each decompressed log's SHA-256.  The first log shows one `peer-inbound`
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

The follow-up identity is the SHA-256 of a compatibility record containing the
recognized launcher chain, saved core, Lisp runtime and the proof environment.
The runner and certificate-reader hashes remain attached as audit provenance;
changing those development tools alone does not claim that ACL2 wrote an
incompatible certificate and therefore does not force an endless recertification
cycle.  Launcher-only legacy manifests are not reusable.

Launcher recognition is finite and non-evaluating.  The tool reads no more than
64 KiB of each launcher, follows at most one outer wrapper, and accepts only a
shell shebang, comments/blank lines, literal `export` assignments, and one
absolute `exec` with a literal absolute `--core` path.  Other commands, control
operators, relative or dynamic paths, oversized/non-text inputs, recursion and
unknown shapes are unqualified.  The content hashes themselves are streamed.
This is a narrow recognizer for the two observed generated-launcher layers, not
a general shell parser and not a proof-trust improvement.

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

## Post-reboot recovery validation

The dirty source was first preserved unchanged in unsigned checkpoint
`8758c4c5`.  After the bounded recognizer review, focused tests ran under the
new process-group containment runner from the sibling `w24/process-containment`
lane:

```text
python3 ../w24-process-containment/tools/run_command.py --timeout 60 -- \
  python3 -m unittest tests.test_acl2_toolchain tests.test_certs \
  tests.test_farm tests.test_certify_runner \
  tests.test_proof_artifacts.AcquisitionTests -v
```

Result: 96 tests passed in 15.950 seconds on Darwin arm64.  The containment
runner provides TERM, bounded grace, KILL and direct-child reaping for its task
process group; it does not claim cleanup for `setsid`-escaped descendants or a
supervisor killed with SIGKILL.

The broader first invocation ran 98 tests in 14.558 seconds: 97 passed and the
unrelated `ProfileTests.test_default_and_dtn_are_distinct_declared_images`
failed because current `IMAGE_PROFILES["default"]` contains `books/bp-node`
while the older assertion says it must not.  The narrowed acquisition suite
above excludes that stale profile-policy assertion without hiding a changed
toolchain test.

A read-only, non-executing probe of the installed Homebrew ACL2 launcher also
qualified its two literal launcher layers, 235,047,944-byte saved core and SBCL
runtime under the new identity in 0.072 seconds.  No ACL2 process, certification,
farm run or build was started.  Remote-origin qualification remains the next
integration check after this packet lands.
