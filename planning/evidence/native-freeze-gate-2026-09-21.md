# Native frozen-origin repair gate — 2026-09-21

This record preserves the bounded certification and native-image repair gate
on `persvati`.  The remote origin remained
`/home/ember/fn-gates/freeze-f7190d69`; its name records the first snapshot,
not the revisions later mirrored into it.  No installed ACL2 toolchain was
modified.

## Qualified toolchain

- ACL2 wrapper: `/home/ember/fn-gates/toolchains/w25/acl2-literal`
- wrapper SHA-256: `346b7ee183e8c291cb61cf31be75a332caf329fa74b4995921cbb224208f2c08`
- compatibility identity: `1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`
- ACL2 core SHA-256: `1bc67f611886a0898641bbb0a67a38baddc6b800c1c31a1d757d26e10eda3ffd`
- SBCL runtime SHA-256: `b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5`
- reported versions: ACL2 8.7 and SBCL 2.6.8

The wrapper was used by exact path for certification and image construction.
Runtime tests also set `FN_ACL2` to that path and put
`/home/ember/fn-tools/sbcl/bin` first in `PATH`.

## Certification history

The full `55e6d00a` repair attempt, handle
`run-20260921T163612Z-b31e`, failed after 157 successful roots and five failed
roots.  Manifest `certify-20260921T163617Z-1753773.json` records the failure;
the primary error was the unproved proper-list obligation in
`FN-NATIVE-ADMIN-PEER-PLAN`.

Revision `8071a825` repaired that obligation.  Handle
`run-20260921T165123Z-ea6a` certified only the five failed roots with
`closure=false`; manifest `certify-20260921T165126Z-1889362.json` records the
pass.  Preflight used exact-origin artifact set
`de22e40bb9bb6845049dfb26200a9af78b9fb75d4f3970c10b2ff18f21960724`
and installed 58 dependencies with none missing.

The later initialization repair at `e96e8a39` was certified in three bounded
steps:

- `run-20260921T170207Z-598e`: configuration observation book and test;
- `run-20260921T170323Z-7290`: the five native admin/observation/operator roots;
- `run-20260921T170417Z-36fa`: all 56 declared default-image roots.

The resulting load-checked default artifact set was
`f00ed389a9f953a6a54eff070dd13e6cbcae527bf9c4d2ac0fd001afa4e429af`,
146 books, source identity
`528d7c8e177c003821c19f0d7d228b732f48c0ab7476e49db4e5cc5c3ce7cec9`.
The BP application fast-path repair at `7b23b6a5` then passed focused handle
`run-20260921T173415Z-1332` for `books/bp-native-app-fast` and its ACL2 test.

## Native results

The final scoped source revision was `8c231978`.  All three images built with
the exact wrapper:

| Image | Launcher SHA-256 | Core SHA-256 | Core bytes |
|---|---|---|---:|
| production | `6855eba7d15424b1db8f039d1dff777f3bb675eb014662f7394f04ddb2818dd0` | `3364a22c75699e7d55161ab06608120e1831a5d0ccc8d4ef4222baa495e7e5ad` | 303730928 |
| developer | `f044c29d98257cd8a0a7dc627ba68d7ae0bb39ec80f6dbdb329c25ea418e9cfb` | `21f48285f7dbdecb8649b5a38a191c861f4ed88e0cb8a746f2f4c5c4e06d23ea` | 303763704 |
| DTN | `f66d0b514d8479ecf9d567d74433429af081eb52a9662ad7783c079532c30c26` | `931a2b77e563a697b3299a969db23a9882e5d82b05a4b2405db8237103b77cc0` | 295110720 |

Runtime evidence was intentionally scoped across the repairs instead of
repeating already-passing batches after every narrow change:

- At `0626d428`, the production matrix ran 55 tests in 80.724 seconds: 52
  passed; the remaining three exposed one platform reset expectation and the
  BP absent-journal defect.
- At `7b23b6a5`, those exact three cases passed in 26.826 seconds after the
  focused logical repair and narrowed Linux reset expectation.
- At `7b23b6a5`, the DTN/static batch passed 32/32 in 18.447 seconds with no
  skips.
- The developer batch passed 22/23 and exposed a client file descriptor kept
  open by its fixture plus a real once-mode SIGTERM polling gap.
- At final revision `8c231978`, the repaired developer transit case and new
  incomplete-POST SIGTERM regression passed 2/2 in 5.429 seconds.

This is a scoped gate, not a claim that every earlier runtime case was rerun
against the byte-identical final images.  It establishes the concrete
failure-to-repair chain, focused ACL2 certification, load-checked artifact
sets, three final builds, the 32-case DTN batch, and focused final owner
regressions.  The log files beside this record preserve the exact outputs.
