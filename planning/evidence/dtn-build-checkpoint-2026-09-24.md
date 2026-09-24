# DTN images can `store init`: the build fix and the lists check

[native-subsets-6c0626c5](native-subsets-6c0626c5-2026-09-24.md), failure 2:
`store init` exited 4 on both `6c0626c5` DTN images, so
`test_native_app_journal` failed 0/10 and two `test_native_image_profiles`
DTN subtests failed. This lane fixed it in two layers and added a static
check to `make check` that finds both layers.

## The two layers

1. **ACL2 side** (`c7b76b59`). `host/native/build-dtn.lisp` did not `ld`
   `host/checkpoint-host.lisp`, which defines
   `fn-store-checkpoint-clone-fence-name`. `io.lisp`'s `fnn-clone-fence-path`
   names that function every time a Store opens. The `ld` now follows
   `store-node-host`, in the same position as in build.lisp. Through it the DTN
   proof profile gains `books/checkpoint-publish`, `-compaction` and
   `-pack-retire`; `-auxiliary` was already there.
2. **Raw side** (`0fdf5837`). The images built from `c7b76b59` still exited
   4 on `store init`, now with `The function ACL2::FNN-CHECKPOINT-NAME-RESULT
   is undefined`. `fnn-clone-fence-path` decodes the fence name with that
   function, and only `host/native/checkpoint.lisp` defined it.
   `build-dtn.lisp` does not load that module, and it should not load it
   whole: the module's `checkpoint clone` path calls five owner functions
   that only `owner.lisp` defines. The decoder therefore moved, unchanged,
   into `io.lisp` next to its first caller; `checkpoint.lisp` still calls it.
   The default image loads `io.lisp` before `checkpoint.lisp`, so its load
   order does not change.

## The `ld` lists compared

Transitive `ld` closure (each host file's own `ld`s followed): build.lisp
has 29 host files and build-dtn.lisp has 14. No host file is loaded only by
the DTN build. `owner-host.lisp` is already in the DTN closure through
`native-admin-host.lisp`. The 15 files that only build.lisp loads are listed
in `DTN_OMITTED` in `tools/build_lists_check.py`, each with its reason:

| host file | why the DTN image omits it |
| --- | --- |
| `anchor-wire-host`, `anchor-server-host` | used only by `anchor.lisp`, which the DTN image does not load |
| `reader-host`, `native/reader-model-host` | the NNTP reader and its model, left out by design. `io.lisp`'s `reader` and `model` verbs name 7 of their functions; the build-dtn.lisp header documents those refusals and faults |
| `native-config-host` | used by `config.lisp`, `operator.lisp` and `owner.lisp`, none loaded |
| `native-auth-host`, `native-auth-admin-host` | used by `auth.lisp` and `auth-admin.lisp`, not loaded |
| `feed-filename-host` | used by `feed-filename.lisp`, not loaded |
| `native-operator-host`, `native-control-host`, `native-hybrid-control-host` | operator and control surfaces, not loaded |
| `hybrid-signature-host` | the DTN image loads no crypto |
| `topic-history-metadata-host` | only includes a book, for `topic-local.lisp`, which is not loaded |
| `bp-release-owner-host` | `workflow.lisp` names 4 of its functions, but only for an owner-mode journal. Only `bp-node.lisp` and `bp-obligation.lisp` open one, and neither is loaded |
| `bp-native-app-host` | `bp-service.lisp` names `fn-owner-bp-tcpcl-ingress` only when it has a non-NIL owner. `bp.lisp` passes `NIL NIL`, and `bp-node.lisp` is not loaded |

The two lists stay separate, and the check keeps them aligned. The DTN list
is deliberately smaller, and each build script is the declaration that
`tools/proof_artifacts.py --profile <p>` reads.

## The check (`make check`)

`tools/build_lists_check.py` finds four kinds of defect:

- **omitted:** a host file in build.lisp's closure that is not in
  build-dtn.lisp's closure and has no `DTN_OMITTED` entry.
- **stale:** a `DTN_OMITTED` entry for a file that the DTN build loads, or
  that build.lisp does not.
- **reached:** a DTN-loaded raw module names, as a quoted symbol, a function
  defined only in an omitted host file, or a DTN host file calls one. The
  entry must list that function and say why it is unreachable.
- **raw:** a DTN-loaded raw module calls a function, or names it with `#'`,
  and only a raw module that build.lisp loads and build-dtn.lisp does not
  defines it. Comments and strings are ignored. `DTN_RAW_REACH` says why each
  such call is unreachable: `admin.lisp`'s live owner arm, which only
  `control.lisp` calls, and `bp-service.lisp`'s owner ingress.

`tests/test_build_lists_check.py` has 9 cases:

- The tree is clean.
- Removing the checkpoint `ld` gives both the omitted and the reached
  finding. An allowlist entry for the file does not excuse the reference.
- Restoring the `c7b76b59` `io.lisp` and `checkpoint.lisp` gives the raw
  finding.
- Deleting one entry from each allowlist gives its finding. A stale entry
  gives its finding.
- A docstring mention is not a call.

The check does not follow the books that an omitted host file includes, and
it cannot see a counterpart name computed at run time.

## Images built

On hbox, 2026-09-24 about 16:20 to 16:40 UTC, in
`/tank/fn/scratch/dtn-build-checkpoint/tree6c`.

**Source.** `git archive 6c0626c5`, with three files replaced by their
`0fdf5837` versions:

| file | SHA-256 |
| --- | --- |
| `host/native/build-dtn.lisp` | `d01436a1…` |
| `host/native/io.lisp` | `120e3234…` |
| `host/native/checkpoint.lisp` | `5e4c61bc…` |

The dev tree could not be used. dev changed `books/records-shape`,
`owner-log`, `owner-config-observe`, `byte-store-k0` and `nntp-pinned-msgid`
after `6c0626c5`, and `/tank/fn/certcache` has no complete DTN set for those
digests. `proof_artifacts acquire` answered "no complete current artifact
set", and this lane runs no farm. The three files above have no other changes
between `6c0626c5` and dev.

**Artifact set.** Acquired and validated with `--profile dtn`: set
`1acf1cb91b0c9a19…`, 261 books, 86 roots, result `loaded`. Toolchain: ACL2
8.7 (`/tank/fn/toolchains/w28/acl2-literal-4g`), SBCL 2.6.8
(`/tank/fn/sbcl`), OpenSSL 3.5.8.

**Build.** `FN_NATIVE_PROFILE=production|developer
FN_NATIVE_BUILD=host/native/build-dtn.lisp
FN_NATIVE_IMAGE=build/fn-host-dtn[-developer] swarm-build sh
tools/build_native_host.sh`. Both runs exited 0, and each core is 118M.

| image | launcher SHA-256 | core SHA-256 |
| --- | --- | --- |
| `fn-host-dtn` | `9d9d06e1b3be5598…` | `0c1a41193d1bd657…` |
| `fn-host-dtn-developer` | `6ededf4de4008913…` | `f62250c948a2e7bb…` |

These are unfrozen scratch images, not a release. The launchers point at
`/tank/fn/sbcl`.

**The intermediate `c7b76b59` pair** (checkpoint-host only) had cores
`736fd58a…` and `b2cca4a2…`. Both exited 4 on `store init`, and that result
is what led to layer 2.

## Results

`store init fn.test` on a scratch store:

| image | result |
| --- | --- |
| `fn-host-dtn` | exit 0 |
| `fn-host-dtn-developer` | exit 0 |

On the `6c0626c5` images, both exited 4.

Each module ran on its own as `python3 -m unittest -v tests.<module>`, with
these variables set:

- `FN_NATIVE_DTN_HOST` and `FN_NATIVE_DTN_DEVELOPER_HOST`: the new pair.
- `FN_NATIVE_BP_HOST`: the new DTN developer image.
- `FN_NATIVE_CONTACT_SENDER` and `_RECEIVER`: the new DTN production image.
- `FN_NATIVE_HOST` and `FN_NATIVE_DEVELOPER_HOST`: the frozen `6c0626c5`
  default images.

Logs are in `/tank/fn/scratch/dtn-build-checkpoint/logs/` with `SHA256SUMS`.

| module | tests | pass | fail | skip | s | log SHA-256 (16) | vs 6c0626c5 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| test_native_app_journal | 10 | 10 | 0 | 0 | 8 | `261b205daf8d0e0b` | was 0/10 |
| test_native_image_profiles | 12 | 12 | 0 | 0 | 2 | `a841ffa6e8db17d9` | was 10 + 2 failed subtests |
| test_bp_service_native (dtn-developer) | 16 | 16 | 0 | 0 | 14 | `1adfcf0b26a3d84e` | same, control |
| test_bp_receive_integrity_native (dtn-developer) | 4 | 4 | 0 | 0 | 1 | `ed583ef1554709f6` | same, control |
| test_bp_contact_native | 2 | 2 | 0 | 0 | 0 | `a3826e764a9dade1` | same, control |

`make check` is green on the commit carrying this record, after `tools/ledger.py --write` (host-names warnings 814 to 813: io.lisp no longer calls a function only checkpoint.lisp defines). The new check reports "default ld
closure 29, DTN 14, omitted with reasons 15; 0 finding(s)".

## What this does not establish

- **Default image not rebuilt.** Moving `fnn-checkpoint-name-result` also
  changes the default image's source. The default image was not rebuilt, so
  that change rests on load order alone: `io.lisp` is loaded before
  `checkpoint.lisp`.
- **Not dev's books.** The DTN images are built from `6c0626c5` books, not
  dev's. The next shared cut builds all four images from dev.
- **Only the DTN-relevant modules ran.** `test_bp_node_native` and
  `test_bp_app_native` use the default images and were not run. Their
  failures 1 and 7 are unrelated to this fix.
