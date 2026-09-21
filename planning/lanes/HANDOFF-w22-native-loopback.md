# W22 native loopback projection handoff

Source: `ce33820a3c8882a6c83e529e0f9b3ed3cba2c49d` (the preceding endpoint
implementation is `9843848d08a8d7955950722b7b5679bc49180462`).

`books/native-config.lisp` owns the only listener-host projection: the three
already admitted spellings map to `(:inet (127 0 0 1))` for `127.0.0.1` and
`localhost`, and `(:inet6 (0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1))` for `::1`; every
other octet sequence is `:bad`. `host/native/owner.lisp` calls the ACL2 wrapper with its unchanged
host-octets callback argument, validates the returned two-element tag/vector
shape before taking either element, and binds that vector. It does no DNS,
host-string comparison, or family choice. The callback's five arguments and
the auth/control surfaces are unchanged.

`certify-20260921T101141Z-78762` passed the owned closure on macOS arm64 with
ACL2 8.7 / SBCL 2.6.8: `books/defrecord`, `books/cbor`, `books/records`,
`books/native-config`, `host/native-config-host`, and
`tests/acl2/native-config-tests`. The immutable source-pinned manifest is
[`certify-20260921T101141Z-78762.json`](../evidence/manifests/certify-20260921T101141Z-78762.json).

The ACL2 tests witness accepted IPv4, `localhost`-to-IPv4, IPv6, malformed
address refusal, and the host wrapper. `tests/test_native_operator_cli.py`
adds actual public `operator CONFIG run --once` bind-and-serve cases for all
three profiles. They were **skipped**, not passed, because this worktree had
no source-matched `build/fn-host`; rebuild the integrated source and run that
test before claiming native endpoint runtime evidence.
