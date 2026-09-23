# Frozen native reader regression: INN, live configuration, matrix

These checks reused the one developer saved image built from source
`884e48166594749231f6fcf6083dd9c50d54942a` at
`hbox:/tank/fn/gates/integrate-reader-repair-20260923/build/fn-host-developer`.
The launcher SHA-256 was
`ec8442a896d4b1b1ab242bfe649e5e595567c4bfb278fc7ce4091da581f0680a`;
the core SHA-256 was
`4a49fe97136f8c592464eac64921b02b9f1482d38d90c46b5d219ccebecb17c1`.
Its build and focused reader evidence in
`planning/evidence/native-reader-884e4816-2026-09-23.md`
records the current-source certificate closure and earlier HDR/index tests.
No image was built for this regression pass, and no deployed node was used.

## Real INN 2.7.4

The exact frozen `tools/inn_lab.py` driver (SHA-256
`12a009c48c40455bd3869f6a776ed4c72b5cdad7bae8876286df3d4f178a14bf`)
ran against the pinned `/tank/fn/inn/2.7.4` install with the image above,
`--native-openssl-prefix /tank/fn/toolchains/openssl-3.5.8`, and an isolated
lab root `/tank/fn/labs/reader-inn-884e4816-2044`. Its explicit ports were
innd 11519, nnrpd 11520, fn 11590, outbound tap 11518 and inbound tap
11517. The tool cleaned the run tree and released its lock.

The generated [report](inn-reader-884e4816-2026-09-23.md) and
[findings](inn-reader-884e4816-2026-09-23.findings.json) record 82 steps,
zero failed, zero not exercised, zero violated and zero inconclusive; all 33
declared findings held. The report SHA-256 is
`503ab5e165ce8a650e4dfeb9d4f9ee4fd61dc058bb2964a50187139012eb18f8`;
the findings JSON SHA-256 is
`d657f43fda1c302c282bbd2807abb4a85b2f83a63387c2daa38b844f988ee64b`.
The [runner output](native-reader-regression-884e4816-logs/inn-reader-884e4816-run.log)
has SHA-256 `801c442fe1d0ba9ac547254e5f6e0c951adeea3bd705bf8e7aae0ca79d9c72fe`.
The exercised scope includes fn POST/operator submission into INN, INN
innfeed into fn, independent nnrpd/fn read-back, Path/Xref comparison,
duplicate and loop handling, and owner and innd restarts. The lab reports
the exact wire replies and article octets; it does not test a second outbound
peer, TLS, or remote network transport.

## Live configuration

The frozen `tests/test_native_live_reconfiguration.py` driver (SHA-256
`3d9e89f8cab9df7739262ed7c24560dfd62f5ec286f11ee4689e2b7cf3fc8e6e`)
ran with `FN_NATIVE_HOST` set to the same image and `FN_OPENSSL_PREFIX` set
to `/tank/fn/toolchains/openssl-3.5.8`. All 11 tests passed in 1.366 seconds;
the [log](native-reader-regression-884e4816-logs/test-native-live-reconfiguration-884e4816.log)
has SHA-256 `7183e094015f0f16660cf83c2bd342b2c8354d149751d5ce61860e493f0aa0f8`.
Four were saved-image scenarios, including a running owner's durable group
creation, an older reader's unchanged pinned view, a new reader's live group
view, peer addition and restart, writer-lock refusal, and owner continuity.
Seven checked the frozen source's call path; they are not runtime witnesses.

## Native v0 matrix

An initial matrix invocation at this frozen source stopped before any feature
row because `tools/v0_matrix.py` did not pass the image's pinned OpenSSL
prefix to its packaged-image probe. The original frozen tool SHA-256 was
`0430eaef482786a2b06f78563a2e3c4b7b7a035ca5dd6bea374e3fb898235ba1`.
Its [stopped-early report](v0-reader-884e4816-2026-09-23.md) and
[JSON](v0-reader-884e4816-2026-09-23.json) preserve 220 not-exercised rows;
the [runner log](native-reader-regression-884e4816-logs/v0-reader-884e4816-preflight-failed.log)
has SHA-256 `07fcdc6e7054bca59faa091da0c2cbee0ad06546ba3cfa93211322d56917935b`.
The direct public command succeeded once `FN_OPENSSL_PREFIX` was supplied.

The orchestration-only fix `f337faf7` adds `--native-openssl-prefix` to all
matrix native launch sites. `python3 -m unittest tests.test_v0_matrix -q`
passed 47 tests, including a new command/probe regression. The patched
matrix driver SHA-256 was
`19039cd934444bd4c17f476236faf8b83accf1c1132e19af6b8efae6ff1494e9`.
It deployed **source 884e4816** into a separate hbox tree and reused the
**same saved image**; the driver patch changed neither. Two public-operator
stores were preprovisioned under
`/tank/fn/labs/reader-matrix-884e4816` on ports 11690/11691. The matrix used
`--backend native-operator`, the same image for its developer-only cut,
`--native-runtime /tank/fn/sbcl/bin/sbcl`, the w28 ACL2 executable, and
`--no-campaign`; scale and its own INN phase were not requested.

The [rerun report](v0-reader-884e4816-openssl.md) and
[JSON](v0-reader-884e4816-openssl.json) are the evidence, with SHA-256
`2287bebb09a8dc8fce0827f6432e7d436c85b9be67e4571f35e20d29fe38f103`
and `e394c3ef29c4d90cfc131afe218af89450857bee8af850852f62524ab3577b5e`.
Across 220 rows it recorded 135 accepted, 36 refused, two uncertain, 44
not exercised and three not built; **zero outcome disagreements**. The
independent Python `nntplib` client read both nodes, and the native public
peering and protected STARTTLS/AUTHINFO suites passed inside the matrix.
One row remains a host usage fault rather than a D13 refusal:
`V0-NODE-LOOPBACK` offered `0.0.0.0` and the operator rejected the invalid
configuration with exit 5, while that row expected refusal exit 1. The
matrix therefore exited 1 and is **not a passing whole-matrix gate**. The
[runner log](native-reader-regression-884e4816-logs/v0-reader-884e4816-openssl.log)
has SHA-256 `99cba9e6c6d76fdbcd66fade63c94bae799e9057f97b7486411e989bde30e535`.
The test keeps usage, refusal and uncertain distinct; this report neither
relabels exit 5 nor fills the unexercised feature rows with inferred results.
