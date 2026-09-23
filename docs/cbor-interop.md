# CBOR interoperability probe

`tests/interop_cbor.py` is an optional interoperability probe for the
experimental primitive profile in `books/cbor.lisp` and the provisional schema-0
record in `books/records.lisp`. It is deliberately outside the default
`unittest` suite and does not add a project dependency.

The independent implementation is `cbor2==6.1.4`, installed in the isolated
`build/cbor-interop-venv` environment. The observed package metadata identifies
it as an RFC 8949 CBOR implementation; its API documents `dumps(...,
canonical=True)` as an optional canonical encoding mode. The probe uses the
library's ordinary decoder/encoder for independent generic CBOR behavior and
does not use a Python reimplementation of fn's profile. Sources consulted:

- [cbor2 on PyPI](https://pypi.org/project/cbor2/) (version and RFC 8949 scope)
- [cbor2 API reference](https://cbor2.readthedocs.io/en/stable/api.html)
- [RFC 8949 §4.2.1](https://www.rfc-editor.org/rfc/rfc8949.html#section-4.2.1)

Run it from the repository root with:

```sh
python3 -m venv build/cbor-interop-venv
build/cbor-interop-venv/bin/python -m pip install --disable-pip-version-check --no-input 'cbor2==6.1.4'
build/cbor-interop-venv/bin/python tests/interop_cbor.py
```

The run creates `build/cbor-interop/run-*/manifest.json`. The manifest records
the exact command, Python/platform, cbor2 version and module path, ACL2
executable/version/hash, source hashes for the two ACL2 books and the driver,
per-case hashes/lengths, and the result. It is generated evidence and is kept
under `build/`; root should copy the relevant run identity into the consolidated
evidence record.

Observed run on 2026-09-18 at `20260918T103100Z`: 38 cases passed with Python
3.14.7 on macOS 26.6.1 arm64, cbor2 6.1.4, and ACL2 8.7 (SBCL 2.6.8). The
machine-readable result is
`build/cbor-interop/run-20260918T103100Z-30006/manifest.json`; its ACL2
executable SHA-256 is
`36519682f97e83f1aadf9d092f46cb944d6621751595b8abf6b27b74309df324`. A later
run should be recorded separately rather than silently replacing this observed
result.

The primitive cases compare both directions. ACL2 encodes unsigned integers and
definite byte strings and cbor2 decodes them; cbor2 encodes the same values and
ACL2 decodes them. Integer boundaries are 0, 23, 24, 255, 256, 65535, 65536,
and `2^32-1`. Byte-string boundaries include 0, 23, 24, 255, 256, and 65535.
The probe also checks 65536-byte and over-input refusals, truncation, trailing
items, non-minimal argument heads, negative integers, text, arrays, maps, tags,
floats, indefinite byte strings, and a 64-bit integer head.

`cbor2` accepts the full generic CBOR forms in several refusal cases. The probe
records that acceptance separately from fn's result: fn's profile intentionally
accepts only major type 0 uint32 and major type 2 definite byte strings, with
shortest argument heads, a 65535-byte payload limit, a 65538-octet input limit,
and exact single-item decoding. Therefore generic CBOR acceptance is not
reported as fn-profile acceptance.

The schema-0 and schema-1 fixtures use the attached `fn-record-encode` and
`fn-record-decode-exact` calls. cbor2 decodes the concatenated primitive items,
re-encodes them, and supplies an independently encoded sequence back to ACL2.
This checks primitive sequence interoperability for both exact record grammars;
the separately certified codec seam establishes the general round-trip and
canonicality claims.

The ACL2 bridge sends only generated decimal octet-list literals to fixed calls
to `fn-cbor-*` and `fn-record-*`; no external bytes are passed to the Lisp
reader or evaluator. This probe supplies integration evidence for `SCN-013` and
`ENC-001`'s current primitive/schema-0 scope. It does not prove canonicality,
bounded work, cryptographic properties, or full native/batch interoperability.
