# Native operator status/recover dispatch increment

Source: `w15/native-operator` commit `b9ed8e5` for the raw module, with the corrected ACL2 grammar at `c56e8a1`; isolated hbox source copy
`/tank/fn/gates/w15-native-operator`, without `.git`. The source digest for
`books/native-operator.lisp` is recorded by the manifest.

`host/native/operator.lisp` is an unregistered raw native module for the future
owner build. Its positional form is `--fn operator CONFIG-PATH COMMAND ...`.
It reads bounded configuration and argv octets, calls only
`fn-native-operator-host-run` and its ACL2 result projections, then executes
only the ACL2-designated normalized `status` or `recover` plan using the
existing native store functions. It emits one tagged stderr result after the
operation returns. `run` reaches an owner-required normalized plan and `post`
is explicit usage until the owner supplies a shared-submission callback; neither
creates a second service owner or a direct payload-post bypass. Owner convergence will consume
the `run` plan through the named result accessors.

The current saved image does not include this unregistered module: owner
convergence owns build and service integration. This packet therefore certifies
the callable ACL2 wrapper and plan grammar, not a deployed `--fn operator`
command. It makes no accepted-service log before an executed status/recover
operation succeeds.

Hbox closure command:

```
FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 FN_CERT_CACHE=/tank/fn/certcache \
python3 tools/certify_books.py --jobs 1 --closure \
  tests/acl2/native-operator-host-tests
```

ACL2 8.7 / SBCL 2.6.8 passed in the source-pinned manifest. The host wrapper
test verifies it calls the exact result subject and its status/action/exit
projections. The corrected grammar and wrapper closure is [certified here](manifests/certify-20260921T085200Z-1886133.json); the prior raw-dispatch witness is retained [here](manifests/certify-20260921T084415Z-1876240.json).
