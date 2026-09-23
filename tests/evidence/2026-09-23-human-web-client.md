# Local human web client, 2026-09-23

The client-only source was based on `2c916fc7f86ef7b18ee7be3d3edeaf805604b4ee`.
`python3 -m unittest tests.test_fn_web tests.test_fn_client -q` passed 40
tests on macOS with Python 3.14.7. These used actual local NNTP and HTTP
sockets against `tests.fake_node`, covering escaped article content, form
limits, accepted/refused/uncertain POST, and Message-ID retention when a
connection fails before greeting.

The native check used the pre-existing frozen hbox developer image at
`/tank/fn/gates/takeover-v0-image-329a51a2/build/images/329a51a23f08e42904d4e0894c94ef5dc243d17e/fn-host-developer`
(SHA-256 `e4eeefd290450e7497dade96e2c4089e0caacfa88f72c737f51a92b2f3b2ba18`)
and Python 3.12.7. The new client scripts were copied into
`/tmp/fn-web-native.U54SCd` on hbox; the frozen source tree was used only as
the native image's working directory and was not changed. The frozen tree's
Git worktree metadata was unavailable, so its path/image digest are the
identifiers for this run. The copied `fn_web.py` and `fn_client.py` SHA-256
digests were respectively `fa2c84840a1c4b53351d03d755faf5823cd1bf083ac37ec6d6a9f96162256df7`
and `5b32c318bb053a9cbfa7226cd6ad40b898d46a2c98b2cdf960171b1b28d7120b`.

Invocation from the scratch directory:

```sh
FN_NATIVE_DEVELOPER_HOST=/tank/fn/gates/takeover-v0-image-329a51a2/build/images/329a51a23f08e42904d4e0894c94ef5dc243d17e/fn-host-developer \
FN_NATIVE_TEST_ROOT=/tank/fn/gates/takeover-v0-image-329a51a2 \
python3 -m unittest discover -s tests -p test_fn_web_native.py -v
```

The [captured log](2026-09-23-human-web-native.log) (SHA-256
`2d2541c496ddebd14c34b10937b4446c835929d0e03e3209f0aaa6d399a681bd`)
passes. It initializes a disposable native Store, starts the native served
owner, lists the real group through the web client, sends a POST, and reads
the stored article back through `OVER` and `ARTICLE` with escaped HTML.

This establishes one local developer-image loopback path. It does not qualify
public HTTP exposure, TLS/authentication against a deployed node, browser
accessibility, signature verification, remote transport, or a consumer
processing acknowledgement. There is no ACL2 book change or proof claim.
