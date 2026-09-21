# Native anchor manifest, acquisition and FNAN runtime evidence

Input revision: `12e78af8cdbe3a9f8d825b5edb5c69f31cbf7df0` on
`w14/native-primitives`.

> Historical, superseded persistence evidence.  Review found that this exact
> revision appended a raw native SHA-256 trailer and classified persistence
> with a raw-Lisp `attempted` Boolean, and recovery decoded a visible final
> name without first establishing file and directory barriers.  The live run
> below remains an interoperability observation for its pinned source; it is
> not safe durable-acceptance evidence.  The later anchor-replace packet
> replaces those twins with ACL2 `fn-frame-trailer` and a host-called ACL2
> phase machine and adds an EIO/restart recovery witness.

## Certified ACL2 profile

Invocation:

```text
python3 tools/certify_books.py --jobs 1 \
  books/anchor-servers tests/acl2/anchor-server-tests
```

ACL2 8.7 passed both requested roots.  The exact executable, source closure,
certificate digests, command and times are in
`planning/evidence/manifests/certify-20260921T090224Z-18711.json` (SHA-256
`0854736d95735922d7456ccea2fa636e2c07f2d0a5d5a0fdd7fd5fb427496363`).
The certified surface maps a bounded server name to endpoint, selected key,
whole pin set and acquisition bounds; the tests include both pinned names,
unknown and near-miss names, timeout endpoints, key membership and width.

## Native component regression

Invocation on each host:

```text
sbcl --noinform --disable-debugger --script \
  tests/native_anchor_acquisition.lisp
```

The exact same native sources and test were run on:

| Host | SBCL | libsodium | Result | Log SHA-256 |
| --- | --- | --- | --- | --- |
| `nextop.local` | 2.6.8 | 1.0.22 | passed | `9e8647113a18beef53d54d659034ab0c32ba81d44bc63b0f2513828857c0dcb2` |
| `hbox` | 2.2.9.debian | 1.0.18 | passed | `7fcd66cfe432f17e0038d9434baa48bd90978f04a51ba1a0e6116c9b12e7b630` |
| `persvati` | 2.6.8 | 1.0.18 | passed | `c8fc5bc53a81f9455250d908255541b88eb9ee14c99a9835127f4a3022feac9f` |

Each transcript includes the content digests it ran.  The regression covers
OS nonce acquisition, known-answer signature/root observations, a negative
signature, a connected UDP exchange, the ACL2 request/parser seam, and a
4097-octet datagram whose first 4096 octets could otherwise be mistaken for a
bounded response.  The last is refused as overbound.

## Saved-image CLI observation

`tools/build_native_host.sh` loaded the new common-image components and wrote
`build/fn-host.core` (SHA-256
`7137f75dfbc320bf28c74d208ebfb1d64853673c66e75212c5d1ac9cf1c9c03f`).
The build log reached `FN_NATIVE_BUILD_LOADED`.  The build script nevertheless
exited 1 because this lane did not recertify the unrelated `books/served` root
and the pre-existing anchor-invariants closure; its intended gate rejects any
`Uncertified` warning.  The exact limitation is retained in
`build-summary.log` (SHA-256
`b8b9c0652cf9ea36d62be9d8759dd665e0c389c137109a56efaf0c88967d86f2`)
and `build.stderr.log` (SHA-256
`45d4bc5cd1afe134cfa26940f0c2e2104cafb778cde613fb7c47a33f9ff87ac1`).
This is not a clean common-image build claim; the root frozen certification
batch must close that gate.

The written image was exercised with:

```text
build/fn-host --fn store STORE init comp.test
build/fn-host --fn anchor acquire STORE does-not-exist 2
build/fn-host --fn anchor acquire STORE int08h 3
build/fn-host --fn anchor acquire STORE int08h 3
```

The exact transcript is `native-cli.log` (SHA-256
`6cb5c73f482a16f740b66b8057ddc1a680f3f10c185a598cc594c19f4f6e0fd8`).
It records unknown-name refusal/exit 1, a live int08h acceptance/exit 0 and a
394-byte durable FNAN, a batched response kept uncertain/exit 3 under D22, and
then a separate restarted process decoding the held FNAN and refusing a
one-nonce overlapping response as stale/exit 1.  The anchor command calls
`fnn-crypto-startup` in each restarted image before acquisition.

The live-server run is an interoperability observation, not a deterministic
test or a proof that the server is honest.  DNS has no whole-path deadline;
send and receive readiness each use the selected timeout.  The readiness-to-I/O
race is safely reported as network uncertainty.  General Merkle-path binding,
author signing policy, restore/advance CLI composition and physical storage
qualification remain outside this packet.
