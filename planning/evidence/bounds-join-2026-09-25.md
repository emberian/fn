# Bounds join: P1 + P2 + P4 on one tree (2026-09-25)

Lane `lane/bounds-join`, D27. Commits c0b0b351, 1592f1d2, 87611947 (after
merging dev at 73123e1d), 5865882c, adfa6276, 452d62cb, 2e0125c4, aa8949c4
and the evidence commit. The images were built from 452d62cb. Its books are
byte-identical to 87611947 and aa8949c4.

## 1. The profile's article term, the defaults, the group-name fact

- `fn-bs-profile-validp` (books/byte-store-frame.lisp) has a new relation
  `:max-record-octets-below-the-article-record`: R >=
  `(fn-record-encoded-octets-ceiling A G)`. This replaces P1's note, which used
  the kind table's 65,538 figure. `fn-bs-profile-validp-facts` carries the
  relation.
- **Keystone** `fn-bs-profile-admits-every-article-record`. Under an admitted
  profile, a record with payload <= A and groups <= G encodes to at most R
  (`fn-record-encode-length-bound`). The host calls validity through
  `fn-bs-profile-init-verdict` (host/store-host.lisp:385),
  `fn-profile-upgrade-verdict` (:429) and `fn-bs-profile-admittedp` at
  install (host/owner-host.lisp:219).
- **Defaults** now read P2's ceilings (`*fn-bs-profile-defaults*`):
  - R = 67,108,864
  - A = 16,777,216
  - G = 4,096
  - names = 256 (460 capped at the label width)
  - the article record for (A, G) is 17,847,355, within R
- **Format-7 translation** (the coordinator's decision: the codec-ceiling G).
  - G = 65,535 and names = 256.
  - R = max(H/T, article record of (A, G)) = max(196,608, 17,138,486) =
    17,138,486, within either tuple's H (24 MiB, 768 MiB).
  - R only grows, so every kind's budget is unchanged.
  - Preset frames: development `e8ec6e0c…`, scale `27cb85e1…`
    (tests/test_native_profile_upgrade.py).
- **Group name vs label.** `fn-cfg-labelp-of-record-group-name`
  (books/config.lisp) states that every group name the record codec admits is
  a configuration label. It is the one statement relating
  `*fn-record-max-group-name*` 256 and `*fn-cfg-max-label*` 256.
  native-admin's typed-delta keystone uses it. Raising the name ceiling to
  the wire's 460 fails there.
- **Teeth** (byte-store-frame-tests, config-tests, native-control-tests,
  nntp-post-tests):
  - a tight witness, and one refusal by name per argument of the relation;
  - a concrete counterexample per hypothesis of the keystone:
    - dropping "admitted": a non-profile reads R = 0, and an empty record
      encodes to 70 octets;
    - dropping the article bound: 196,609 payload octets in one group;
    - dropping the group bound: six 256-octet groups at A;
  - a 256-octet group name is both a group name and a label; a 257-octet
    string is not a label.

## 3. The frame `:blob` (131,072) must wait: its own packet

`*fn-frame-max-blob*` is one width for every `:blob` field of every schema.
A per-schema width needs four changes:

1. A spec form `(:blob . W)` in books/frame-fields.lisp: `fn-frame-specp`,
   `fn-frame-field-okp`, `-octets` and `-parse`.
2. Both round-trip directions in books/frame-invariants.lisp (23 references).
3. frame-journal's local length lemma (field count × (4 + cap)) rewritten as
   a sum of per-field widths. This is the guard P2 hit.
4. For the control socket, a read bound taken from the carried profile:
   - `fnn-control-read-frame` holds up to the maximum in memory, and
     `*fn-nctrl-max-frame*` at a u32 blob is 4.26e9.
   - The bound becomes `fn-nctrl-max-frame-for A`, passed by the owner.
   - The client's file read (`fn-native-control-host-max-article`) follows.
   - Hybrid control's 65,536 (`native-hybrid-control`, another lane's) moves
     with it.

books/frame-fields has 516 affected roots (274 books). That is a freeze of
nearly the whole tree, more than a join can certify inside three runs.
Until that packet lands, `operator post` carries at most 131,072 octets. The
NNTP path carries A: see §2.

## 4. Leftovers

- **POST oversize wording.** A POST the wire closes at the body limit
  (`(:reject :body-overlimit)`) now answers `441 posting failed; the article
  exceeds the configured size` (books/nntp-post.lisp, `fn-nntp-post-step`).
- **Control refusal reason.** A new FNCT status
  `:article-exceeds-profile-bound` is appended, so every earlier octet is
  unchanged.
  - `fn-native-control-refusal-status` maps the injection reason `:oversize`
    to it. `fn-native-control-refusal-status-is-a-refusal`.
  - The owner asks `fn-owner-operator-refusal-reason` after a refusal
    (host/owner-host.lisp; host/native/owner.lisp
    `fnn-owner-control-submit-serialized`).
  - Clients accept `fn-native-control-host-statuses` instead of three
    literal lists.
  - Native: `refused operator post ARTICLE-EXCEEDS-PROFILE-BOUND` (native-a.log).
- **`*fn-store-capacity*` is gone.** The checkpoint host reads the live
  node's capacity (`fn-store-sn-capacity`, host/store-node-host.lisp).
  tests.test_native_checkpoint: 26 run, OK (3 skipped), native-c-checkpoint.log.
- **tools/workflow_journal.py `MAX_INBOUND_BUNDLE`** now mirrors the model's
  2^32-1. frame_bridge had refused every Python store session: "host inbound
  bundle cap is 4194304 but the model says 4294967295", 49 of 64 tests. The
  Python inbox's `MAX_INBOUND_AGGREGATE` of 64 MiB remains a data cap.
- **The Python store suite for P1's opaque profile is red.** The run was
  `python3 -m unittest tests.test_store tests.test_store_config
  tests.test_store_lifecycle tests.test_acl2_bridge tests.test_checkpoint
  tests.test_store_node_host` on hbox (native-c-pystore.log): 64 run, 17
  failures and 19 errors. 19 raise `StoreFault: store was written under a
  different store format`, and most failures are `post returned 4`. P1's
  Python change (tools/run_store.py `_config_from_metadata` and the format-7
  `SUPPORTED_PROFILES` dictionaries) does not open the store it writes. The
  cause is not isolated. `MAX_TRANSACTION_COUNT` (128) and `DEFAULT_CONFIG`
  belong to those format-7 dictionaries, and `command_post` reads its payload
  bounded by `DEFAULT_CONFIG["max_payload_bytes"]` (32,768), which is a data
  cap. This rework was not done.
- **The verifier and the signer.** `tools/fn_verify.py` and
  host/native/signature-command.lisp contain no literal 32768; P4 removed
  both. The verifier's widths are `SOURCE_MAX_V1`/`V2`, and SpecBookTieTests
  ties them.
- **The dtn image did not build on dev's bytes.** host/native/build-dtn.lisp
  lacked `books/records-concrete-owner`, and `fn-owner-io` failed at
  translate. It is fixed at 452d62cb, and the dtn cores now build.

## 2. Native (hbox; images from 452d62cb)

Cores (`build/images/452d62cb…/`):

| Image | Core sha256 |
| --- | --- |
| fn-host | `8e93f320…` |
| fn-host-developer | `d91e1a63…` |
| fn-host-dtn | `0d5337b3…` |
| fn-host-dtn-developer | `662c4368…` |

The image closure was certified on hbox (w28 `acl2-literal-4g`, 8 jobs,
incremental, default + dtn roots, 132 roots). 170 books were certified and
passed (certify-image.log, evidence dir `certify-20260925T051135Z-2562623`).
The tests ran under `systemd-run --user --scope -p MemoryMax=24G`.

| Log (planning/evidence/bounds-join-2026-09-25/) | sha256 | Result |
| --- | --- | --- |
| native-a.log | `9b7b10dd…` | join tests + profile-upgrade before the frame update |
| native-b-upgrade.log | `0f428d0a…` | tests.test_native_profile_upgrade: OK, including the 20 format-7-to-8 cuts, old or new |
| probe.log / probe.json.gz | `ecc5f0d8…` / `0fa4076d…` | 53 of 56 rows |
| native-c-verify.log | `84cfa6d7…` | 17 run, 1 error |
| native-c-checkpoint.log | `108e6efe…` | OK |
| native-c-pystore.log | `6eb706cf…` | red, see §4 |

**POSTs under a profile whose article field is 4 MiB.** The probe ran with
`--init-flags '--max-article-octets 4194304'`, a 204,800-octet candidate and
size controls. Results by article size:

| Octets | Reply | Stored |
| --- | --- | --- |
| 33,792 | 240 | re-read identical |
| 204,800 | 240 | re-read identical |
| 1,048,576 | 240 | re-read identical |
| 2,097,152 | owner stopped, exit 4, empty reply | nothing |
| 3,145,728 | owner stopped, exit 4, empty reply | nothing |
| 4,194,305 | `441 posting failed; the article exceeds the configured size` | nothing |

The 4,194,305 row shows as FAIL only because this run's judge compared the
reply with its CRLF still attached. The judge is fixed (aa8949c4).

**Every POST cut × {kill, eio} (46 rows) passes on a 204,800-octet article.**
The cuts on a 3 MiB article were not possible, for the reason below.

**Finding: the owner stops on articles of 2 MiB and more.** The log line is:

> owner core/store fault; process stopped: ACL2 error in fn-owner-take:
> Control stack exhausted

This is in native-a.log (the deploy rehearsal's 3 MiB POST) and in the probe.
It is a per-octet non-tail recursion reached from `fn-owner-step (:take)`.
The site is not isolated. `fn-owner-take` compares owner states with
`equal`, and injection and path-update build octet lists; either is a
candidate. The process fails closed: nothing is stored and the listener
stops. This is D27's concrete-representation work, the octet list at
runtime, and it caps a served article between 1 MiB and 2 MiB whatever the
profile says.

**P4's signed POSTs.** The 7,717-octet signed POST is verified (240), the
tampered one gets 441, and the unsigned one gets 240. The 60 KiB v1 POST
(70,040 octets) ended the connection before a reply, so the 200 KiB v2 and
tampered v2 cases did not run. Not isolated: the developer
`store ROOT init` with `FN_VERIFY_INIT_FLAGS` may not have set A, and a
refusal of an oversize body can race the client's write. Still open.

## 5. The deployed store: offline 7-to-8

Rehearsed by `tests.test_native_bounds_join.DeployRehearsalTests`
(native-a.log) on a format-7 scale store from the c3420013 image
(`/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/fn-host`,
frame `bf6e6df9…`), with one article. The steps and results:

- Opens under the new image: `profile format=7 max-transactions=4096
  max-history-octets=805306368 max-record-octets=17138486
  max-article-octets=32768 max-groups-per-article=65535 ...`.
- `--max-article-octets 4194304` alone is refused
  `max-record-octets-below-the-article-record`, and the frame is unchanged.
- With `--max-record-octets 33554432` as well, it gives `upgraded ...
  transactions-used=1 transactions-budget=4096 previous-budget=4096`, format
  8, A 4,194,304, R 33,554,432.
- Rollback: the old image refused the format-8 store (nonzero exit).
  Restoring the kept `config.json` brought back frame `bf6e6df9…`, and the
  old image's `status` exited 0. The step was repeated and exited 0.
- The 3 MiB POST stopped the owner (the finding above), so "POST 3 MiB,
  re-read, restart, still open" is **not shown**.

The procedure for the hbox node (unit `fn-node.service`, config
`/tank/fn/node/fn.toml`, installs under `/tank/fn/node/fn-<rev>`):

1. Install an image carrying P1+P2+the join with `packaging/install-native.sh`
   into `/tank/fn/node/fn-<rev>`, as in node-hbox-da5fd8cb-2026-09-23.md. Do
   not start it yet.
2. `systemctl --user stop fn-node.service`. Then `cp -p <store>/config.json
   <store>/config.json.format-7`. This copy is the rollback.
3. `<new>/fn-host --fn operator /tank/fn/node/fn.toml status` should print
   `profile format=7 max-transactions=4096 ... max-record-octets=17138486`.
4. Run `<new>/fn-host --fn operator /tank/fn/node/fn.toml store
   upgrade-profile`.
   - With no flag, this is the pure 7-to-8 step: `previous-budget=4096
     transactions-budget=4096`.
   - To raise A to 4 MiB, pass `--max-article-octets 4194304
     --max-record-octets 33554432`. R must hold the article record of
     (A, 65,535), 21,300,022, or the step is refused by name.
   - Given the owner finding, do not raise A above 1 MiB until the take
     recursion is fixed: `--max-article-octets 1048576` needs no R change.
5. `status` should show format 8. Exit 3 (uncertain) at step 4 is resolved
   by `status`, which reads the old frame or the new one.
6. Point the unit's `ExecStart` at the new image, daemon-reload, start.
7. Rollback, with the unit stopped:
   `cp -p <store>/config.json.format-7 <store>/config.json`, then point
   `ExecStart` back at the old image. An image before P1 cannot open format
   8. Rollback is sound only while no committed record exceeds the format-7
   R: the old image's bounded open read is 65,538-sized.

## Certification

| Run | Box, toolchain | Rev | Scope | Result | Manifest |
| --- | --- | --- | --- | --- | --- |
| run-20260925T050405Z-c4af | persvati, w25, 2 jobs, 300 s | 1592f1d2, before the dev merge | `--affected-by` store-budget-naming, byte-store-frame, config, native-admin, nntp-post, native-control | 311 passed, 17 failed | `certify-20260925T050452Z-738350.json` |
| run-20260925T052905Z-8357 | persvati, w25, 2 jobs, 300 s | aa8949c4 | `--affected-by` byte-store-frame, store-budget-naming | 191 of 191 passed, none over 10 s | `certify-20260925T053008Z-1001454.json` |

Notes on run c4af:

- The 17 failures are all the records-concrete family (records-concrete*,
  owner-*-carried, owner-recover-ocl, owner-offer-indexed and their tests),
  which dev fixed at 44aaf698.
- config 1.6 s, native-admin 6.4 s, nntp-post 4.1 s and native-control 4.0 s
  passed, with their tests between 2.5 s and 4.8 s. Those sources are
  unchanged since.
- byte-store-frame-tests took 58.6 s there because of three must-fails of
  about 15 s each. They are replaced by concrete counterexamples, and the
  book takes 2.4 s in run 8357.

Per book in run 8357: byte-store-frame 2.9 s, its tests 2.4 s,
store-budget-naming 3.0 s, its tests 5.2 s, store-profile-upgrade-tests
2.9 s, store-budget-tests 2.8 s.
