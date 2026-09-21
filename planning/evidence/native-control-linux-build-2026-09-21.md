# Native control Linux build and runtime evidence

The final source packet is `b0dfdf55`; later commits add only evidence. This is
the exact-source control gate for that packet, not a build claim about later
whole-main U13/admin changes. The source was copied to `persvati` at the
absolute origin `/home/ember/fn-lanes/w22-native-control`, and its relevant
digests matched the worktree:

```text
c5c420b2e67573b69e8c43ce966b45a27a013c6b6d119415b3f54668d75ad93d  books/native-control.lisp
429933c6c4990c42ade07c16b78fa15f5de4f95ba013b3d6b9a67b6fcd0151e0  host/native-control-host.lisp
719ac40260b91f587de4c1d4c258b0d4c2dd0840d4e28bc843125c75fef946fc  host/native/io.lisp
f51d9b926a7b123065c4d88aec492eddbaaef6bc17771cce4766c774883de282  host/native/control.lisp
e3aed7a3a467fc254359583ad019d095157496ed6e648996930585f31cc34d74  host/native/owner.lisp
9dc3311d124bb7c148b09cdf9236e1cebe941ee3b56e4a9af95763e7ce4263ac  tests/test_native_control.py
```

Platform and tools were Linux 6.17.0-40-generic x86_64, ACL2 8.7, SBCL
2.6.8, and Python 3.13.7. Certification ran with two jobs and 1800-second
per-book timeouts. The staged exact-origin closures were:

```text
131/131 passed  certify-20260921T104857Z-2884731  manifest sha256 7804e21d0bc9dd9c701bd92d12ea02a901fecb12aebafb87bb087bfb2af7e6f8
 24/24 passed  certify-20260921T111546Z-3157398  manifest sha256 76060d51b264ed23bd2482ec58b0d6be1c2b83b9068f848eded160fec4100dff
 91/91 passed  certify-20260921T111821Z-3183148  manifest sha256 588ec0cbeff487f787c1d823091ce26eb5c046139a799b5e0879542cf4d92db6
```

The first closure covered the native build roots present in the initial
packet. The second recertified the changed control model and tests. The third
closed newer auth, Store correspondence, anchor, owner configuration and feed
journal roots found by the first image build attempt.

The exact manifests are retained at:

```text
planning/evidence/manifests/certify-20260921T104857Z-2884731.json
planning/evidence/manifests/certify-20260921T111546Z-3157398.json
planning/evidence/manifests/certify-20260921T111821Z-3183148.json
```

The exact build command was:

```text
FN_ACL2=$HOME/fn-tools/acl2-8.7/saved_acl2 sh tools/build_native_host.sh
```

It exited zero and reported `built build/fn-host (282M core)`. The resulting
launcher SHA-256 was
`1532e3dac37298ac64c0555dacca9405efcb9363087709bee61f2923fcff1f7c`,
and the `build/fn-host.core` SHA-256 was
`8c8eb547a346e1aad5e60b9879e1224ea355735b369c2c7dca89c4b90653f237`.
The build log SHA-256 was
`55aa453a0c969cf6221e38c5093cc75e9fe1603e70a23ae63648fdeae5bddbfd`;
its retained gzip is
`planning/evidence/native-control-native-host-build-20260921.log.gz`
(compressed SHA-256
`2ff7fcbc9bbe5dfc43da62698c79b7f4dbe80cc018fd741cdbe2df4aca342f1e`).
It contained `FN_NATIVE_BUILD_LOADED` and no uncertified-book or ACL2 error
marker. ACL2 could not load a compiled object for the already certified
`owner-feed-port` book and loaded its source instead; this is a build-time
performance limitation, not an uncertified inclusion.

The resulting image ran:

```text
FN_NATIVE_HOST=$PWD/build/fn-host python3 -m unittest tests.test_native_control -v
```

All seven cases passed in 14.445 seconds. The exact output is in
`planning/evidence/native-control-linux-4ef765a6-2026-09-21-tests.log` (SHA-256
`4321022e6ace0c05a12421283206d1ed5ed76a540487bdc97609865d463897ae`).
