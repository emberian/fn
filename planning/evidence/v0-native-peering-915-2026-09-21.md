# Native peering matrix slice: immutable 915 image

This is an immutable, task-local native-operator observation on `persvati`.
It does not publish `planning/v0-matrix.json`, and it does not establish that
the saved image corresponds to the declared source content.

## Subjects and procedure

The staged test/tool source was Git archive commit
`dab98108fbfefd7ec29a023ed3fd6d79d30b9d8e`, unpacked at
`/tmp/fn-native-matrix-915-20260921T191500-dab98108`. The saved execution
image was `/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host`.

| subject | SHA-256 |
| --- | --- |
| declared source commit | `915d5c729877eddee7dd3f72eadad21cca463d1a` |
| declared 287-input source manifest | `eb0051343d388901b48e7f1de281ba3d1f6079cab062f25060b186cf01e3aaa4` |
| saved image | `2d8259c22388119793ad3dde525497f9095bdb2489ac01e597b439f3d0ff5c09` |
| saved image core | `eaa5b56c8337b5c6b02eb046ef5ba7cd6c2eaabf59720db664104d0fe5ad08b2` |
| SBCL runtime | `b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5` |
| staged `tests/test_native_peering.py` | `e21959ce8cc1829951a3b3a8c51aa23394973faf407d5ac9068b440c42bb4c39` |

The run created task-local stores/configurations with public native image
commands. It did not write the frozen image tree or an installed service. It
called `V0Matrix.native_peering_suite` through
`tools/native_peering_matrix_slice.py`, with a 180-second external timeout;
that tool neither deploys Git nor publishes the current matrix.

```sh
timeout 180s python3 tools/native_peering_matrix_slice.py --worktree "$PWD" \
  --image /home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host \
  --runtime /home/ember/fn-tools/sbcl/bin/sbcl \
  --source 'source-commit=915d5c729877eddee7dd3f72eadad21cca463d1a source-manifest-sha256=eb0051343d388901b48e7f1de281ba3d1f6079cab062f25060b186cf01e3aaa4' \
  --commit 915d5c729877eddee7dd3f72eadad21cca463d1a \
  --json "$PWD/native-matrix-915.json"
```

The runner hashes the staged launcher and image before and after the witness.
Each native owner PID is inspected through `/proc/PID/exe` and
`/proc/PID/cmdline`; the actual `--core` argument and runtime/core hashes must
match the expected values. A missing or mismatching identity fails the witness
and blocks every transit/feed row.

## Result

[`v0-native-peering-915-2026-09-21.json`](v0-native-peering-915-2026-09-21.json)
was generated at `2026-09-21T19:06:39Z` in 7.0 seconds. Its row digest is
`0809ceb764706fdab27a04ccf790c9d3041cdf113c4ea7de0f4e60efe88d30df`:
9 accepted, 2 refused, 181 not-exercised, and no uncertain or not-built rows.

- `V0-TRANSIT-{OFFER,TRANSFER,IDENTICAL}-{AB,BA}` are accepted (`335`, `235`,
  and byte-identical service respectively).
- `V0-TRANSIT-DUPLICATE-{AB,BA}` is refused (`435`).
- `V0-FEED-QUEUE`, `V0-FEED-OFFER`, and `V0-FEED-JOURNAL` are accepted: the
  requeue witness found `FNFD`, killed/restarted the source, and served
  identical target octets.
- `V0-FEED-ONCE` stays not-exercised: a manually opened inbound `IHAVE` that
  receives `435` does not observe the owner queue after acknowledgement.

The direct selected witness also passed in 4.912 seconds and recorded actual
runtime/core paths and hashes for A, B, restart-A, and restart-B.

## Retained artifacts and diagnosis

| artifact | SHA-256 | meaning |
| --- | --- | --- |
| [`native-selected-success.log`](v0-native-peering-915-artifacts/native-selected-success.log) | `ca46fb60c0b75e47baad0c473f6e9147ca9ae861a9d68ed68fbf8682338f96af` | selected-test success and structured witnesses |
| [`matrix-slice-success.log`](v0-native-peering-915-artifacts/matrix-slice-success.log) | `1cc36fdf0439fe9edba72f85b46d1c0a2be30e4c5fc82603971d5e5c9aa9304d` | exact matrix-slice output |
| [`requeue-before-inbound-peer.log`](v0-native-peering-915-artifacts/requeue-before-inbound-peer.log) | `c5e4ff26eac712a5fec2745d60d5a03cfd2f106759b4aa2d09b4fb200643fb64` | retained failed requeue attempt |
| `v0-native-peering-915-2026-09-21.json` | `144410db19929f1e15820812f1e25dc13e63b320e097281a287a8f12e3ee6692` | complete 192-row accounting |

The failed requeue attempt used harness revision `278bfe6b` (test SHA-256
`7824f76cb016ad7d91f994c25370925b9fed3281e01803aae55c590e19e75506`) and
timed out after 61.248 seconds with `restart-b did not receive
<native-requeue-after-kill@example.invalid>`. A's outbound peer was configured,
but B lacked its inbound peer record before startup; the owner treated the
connection as a reader. Commit `2296e76c` configures B before it starts, after
which the selected test passed and the matrix accounting was rerun.

The source commit and manifest are declared inputs. This run measures saved
image and launched runtime/core bytes, but does not establish their
correspondence to the source manifest.
