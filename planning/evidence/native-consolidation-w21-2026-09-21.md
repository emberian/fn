# Native consolidation integration check, 2026-09-21

Source revision: `cf3678977c097180a7a661ff4955dd21ce3bcbc5`. ACL2 8.7 / SBCL 2.6.8 on the local macOS host.
Invocation from the repository root:

```
ACL2_CUSTOMIZATION=NONE /opt/homebrew/bin/acl2 < planning/evidence/native-consolidation-w21-raw-load.lsp
```

The [driver](native-consolidation-w21-raw-load.lsp) loads the combined raw modules;
the [transcript](native-consolidation-w21-raw-load.log) reaches
`FN_W21_RAW_LOAD_OK` with no read or load error. This verifies raw source loading
only: the logical wrappers are not loaded or exercised by this driver, and it
is neither a saved-image build nor a service/runtime or ACL2 proof test.

The staging source-map unit test also passed. The integrated scaffold check at
`b1062dd` passed with its existing lint warnings; it is structural only.
The separately source-pinned component runtime evidence is in the recovery,
receive-integrity, checkpoint and anchor packet reports. A frozen combined
certification/build/runtime batch remains required.

Loaded source SHA-256 digests:

- `host/native/io.lisp`: `d8a24e67135ac7e00f6bbb23547f72fb1c359e6218f154452a57ea1a7bfe8294`
- `host/native/immutable-publish.lisp`: `7db72d19038ab800e63aae8568bd6b93b4ecdc2971bc7fb4430dd5af67fa33ea`
- `host/native/checkpoint.lisp`: `46690f8926c9dca03c77016e42596faa748c6c3c68d74a15f644fa2c1d1f0f5f`
- `host/native/workflow.lisp`: `a6de8a33df8495e7f8c58ade4656fe50b5ad3f6d30c242a58204e0c4ac73ff52`
- `host/native/tcpcl.lisp`: `9afe910f855b26d57eef3a538e54cd582f85175ea8db1a4c53200fc10b65522d`
- `host/native/bp.lisp`: `f26c2de34c4d581201defbbf02f87d0da054fdafc778cc5220b99eea35fce424`
- `host/native/bp-service.lisp`: `68b6a5ad6db269003c82493b2249c405e787137ea7d8489b37bc544e62f9c5db`
- `host/native/feed-filename.lisp`: `ff125eafc002f8190e0874a5b666d736b0c6cbf9acc2e810edc71fc7ddd99054`
- `host/native/owner.lisp`: `430e695987781582a4669587402c2577fd0514c7101e3adf0ded958daa6c6097`
- `host/native/crypto.lisp`: `4ee2a19a83d825ecbed8b0f70518411ae4c7597547318e3b8c8d653a3bf83192`
- `host/native/anchor.lisp`: `97948477bc57b9c4909019bb01f03319daa6e49d6c07af0818c24be15f164963`


After the resource-bound repair, integrated revision `7a0b96f` also passed
`tests/test_native_io_progress.sh` locally, printing `native-io-progress: ok`.
That raw suite exercises actual directory enumeration at and above the bound,
plus existing native I/O error/progress cases. It does not load a newly certified
combined image. The earlier raw-load hashes above deliberately pin the earlier
source; they are not hashes of this later I/O revision.
