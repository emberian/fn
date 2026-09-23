# Browser submission and provenance follow-up, 2026-09-23

This is a client-only follow-up to [the initial slice](2026-09-23-human-web-client.md).
It adds a bounded in-process submission record holding exact composed lines,
Message-ID, and original NNTP outcome. The HTTP path is POST → 303 → GET;
concurrent and repeated POSTs with one form identifier send only once. A GET
settlement lookup asks `ARTICLE` without reposting or changing the historical
POST result. Eviction and simulated web-client restart return 410 without a
POST. The client has no durable draft spool or fn acknowledgement role.

`python3 -m unittest tests.test_fn_web tests.test_fn_client -q` passed 43 tests
on macOS with Python 3.14.7, including a concurrent two-request socket test,
an uncertain result with a later absent lookup, bounded record eviction and
lost client memory. `tools/fn_web.py` SHA-256 was
`a0ffc20ae878d066dff435f8d941bce4e66e8da9a11f077d67d2a17e1e70d8f3`;
`tests/test_fn_web.py` was
`57248330dd1ed07cdd9225ddf8378161c30eddd55d05397421ec411aa00b7aeb`.

A real Chrome Dev browser opened the local client over a fixture NNTP socket.
The groups, indented thread, selected article, reply composer, and accepted
result were visually inspected. Tab moved focus from Subject through From and
Message to Post; Return submitted and landed on `/result?id=…` after the 303.
The first browser run exposed `Origin: null` under `Referrer-Policy:
no-referrer`, which the HTTP origin guard refused. Changing the policy to
`same-origin` preserved no cross-site referrer while a repeated browser POST
reached the accepted result. The updated group labels, thread metadata,
human-readable identity caveat, separate `FN-Statement` and `FN-Authorship`
presence, and collapsed node diagnostics were inspected. This used fixture
article content for layout, not a claim about a deployed node.

The [native log](2026-09-23-human-web-followup-native.log), SHA-256
`01335515e4afe90e060a35e0707e0243ddb7ac9012673cbaaa4641fff5b03a1e`,
records a passing scratch Store POST/readback with the revised redirect flow
against the same frozen hbox developer image and Python 3.12.7 described in
the initial record. Invocation was:

```sh
FN_NATIVE_DEVELOPER_HOST=/tank/fn/gates/takeover-v0-image-329a51a2/build/images/329a51a23f08e42904d4e0894c94ef5dc243d17e/fn-host-developer \
FN_NATIVE_TEST_ROOT=/tank/fn/gates/takeover-v0-image-329a51a2 \
python3 -m unittest discover -s tests -p test_fn_web_native.py -v
```

The frozen image itself did not change. This does not establish browser
behavior under every engine, persistent client-side deduplication across a
restart, deployed TLS/authentication, a signature verdict, or public HTTP
readiness. No server, host, or ACL2 source changed.
