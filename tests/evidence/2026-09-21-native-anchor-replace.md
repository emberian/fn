# Native FNAN replacement and restart recovery evidence

Input revision: `d073fa9979cac368567adbd3aa6600e820b92d44` on
`w14/native-primitives`.  The implementation commit is `32b8920`; `d073fa9`
adds only the explicit EIO/restart success marker to the native regression.

This packet supersedes the persistence portion of `12e78af`.  It does not use
a raw SHA-256 or a raw attempted/not-attempted persistence decision.  FNAN
sealing and decode use shared `fnn-seal` and `fnn-digest-of`, whose trailer is
ACL2 `fn-frame-trailer`.  Native line `host/native/anchor.lisp:215` calls the
executable counterpart of `fn-anchor-rp-step` itself.

## ACL2 certification

Invocation:

```text
python3 tools/certify_books.py --jobs 1 \
  books/anchor-replace tests/acl2/anchor-replace-tests
```

ACL2 8.7 passed both requested roots.  Exact executable, source closure,
certificate digests, command and timing are in
`planning/evidence/manifests/certify-20260921T092103Z-35156.json` (SHA-256
`89c8c96cba1930e3423a49ce30fe19dafdb8d40fa62cef46c0f2ae8063e8c7bf`).

The host-called step keystones are:

- `fn-anchor-rp-step-is-durable-only-after-directory-barrier`: a step can
  introduce `:durable` only from `:replace-visible` on
  `(:directory-result :ok)`.
- `fn-anchor-rp-step-is-recovered-only-after-directory-barrier`: a step can
  introduce `:recovered` only from `:recover-directory` on
  `(:recovery-directory-result :ok)`.

The finite-trace lifts require those directory observations in every trace
from publication or recovery start.  Tests exercise the full reachable trace,
the pre-syscall `:replace-issued` cut, success-before-directory, uncertain
replace, present/absent recovery, and terminal self-loop witnesses showing why
the “not already terminal” hypothesis is necessary.

## Actual native EIO and restart witness

Invocation on each host:

```text
sbcl --noinform --disable-debugger --script \
  tests/native_anchor_acquisition.lisp
```

The regression performs an actual filesystem rename and injects an EIO at
`:anchor-replaced`, before the result reaches ACL2.  `fnn-anchor-publish`
returns uncertain.  A fresh store instance then barriers the visible final
file and its directory before `fnn-anchor-load-held` decodes it.  Each run
prints `FN_NATIVE_ANCHOR_REPLACE_EIO_RESTART passed`.

| Host | SBCL | libsodium | Result | Log SHA-256 |
| --- | --- | --- | --- | --- |
| `nextop.local` | 2.6.8 | 1.0.22 | passed | `ec5a15a89438544718f6b7545b10840d7b38fb354d945666de6b074d0ef023bd` |
| `hbox` | 2.2.9.debian | 1.0.18 | passed | `95ad96f9a9edbb4a43b43c0f524ae171e92b1634e07e5ccc4c04509d318d26d9` |
| `persvati` | 2.6.8 | 1.0.18 | passed | `0ac63cf8cd0e0eab8c9fe64c564b9fb222429f1a9efdb61148677047e2432b3c` |

Every transcript includes source digests.  The test also retains the UDP
overbound and cryptographic known-answer/negative checks.

## Common-image observation and limitation

The common build reached `FN_NATIVE_BUILD_LOADED` and wrote a core with
SHA-256 `bf1bb82d6fbbdf2dda1d6a501ffa82764894f9607a0374a2fd5dc5974608d817`.
Its script still exited 1 because this isolated lane did not recertify the
unrelated served closure and the pre-existing anchor-invariants closure.  The
exact retained limitation is `build-summary.log` (SHA-256
`ea612c124e230241beca31561623cff2e43de35652291bb5fa46b63066df1803`)
and `build.stderr.log` (SHA-256
`ebc3dd8332555a0e734f14ace6d6253bffb91a1a24cc2efcc2b4b56f13dde353`).
This is not a clean common-image build claim; root's frozen batch owns it.

The written image accepted one live int08h response, wrote a 394-byte FNAN,
then a fresh process performed recovery barriers, decoded it, and refused an
overlapping one-nonce response as stale.  The exact transcript is
`native-cli.log` (SHA-256
`3ee2b9f2d7df526e146b760fde5ab0b8548b32431619d8bb0a2f629ae573b3f4`).
This is interoperability evidence only.  It does not prove server honesty,
storage durability, a DNS deadline, or general Merkle-path binding.
