# Evidence: frozen combined v0 runtime matrix (W12)

This is the first two-node runtime measurement of the frozen combined source
`cdbd6b285542110616dc96bfd3d037d410dfc20a`.  It is an observation of two
loopback nodes on one host, not a proof or a publication of
`planning/v0-matrix.json`.

## Input and artifact set

On hbox (Ubuntu 24.10, 24 CPUs, Python 3.12.7, ACL2 8.7 / SBCL 2.6.8), the
command was:

```
python3 tools/v0_matrix.py cdbd6b285542110616dc96bfd3d037d410dfc20a \
  --host hbox --tree w12-integrated-cdb --jobs 4 --keep \
  --acl2 /tank/fn/acl2-8.7/saved_acl2
```

The deployed snapshot was
`/home/hbox/fn-deploy/w12-integrated-cdb-cdbd6b2`.  Acquisition of the
`default` native-plus-owner profile found no current matching cache set, so
the gate certified its declared closure with four jobs and then loaded it.
The exact record is
[`certify-20260921T065003Z-1681307.json`](manifests/certify-20260921T065003Z-1681307.json):
97 books passed in 268.604 seconds; it records the ACL2 executable digest
`64030dda0b03bbb6cf50984889f5ce1e2ba867b6ce3c9a65403afc44f9b4fdb5`, the
complete source/certificate digests, and no local-closure forbidden-facility
finding.  Its manifest SHA-256 is
`fcf75f778b25408df08d79b26880e1a963c21b21315a32ec322b0135912bac55`.

## Original measurement

The immutable [matrix result](v0-runs/20260921T064956.625126Z-cdbd6b2-11d907e01b5e/matrix.json)
and [rendered report](v0-runs/20260921T064956.625126Z-cdbd6b2-11d907e01b5e/report.md)
record a 1137.5-second run from 2026-09-21T06:49:56Z.  Of 192 rows, 149 were
accepted, 32 were refused, 2 were uncertain, 8 were not exercised and 1 was
not built.  Three rows disagreed with their stated expectations:

- `V0-AUTH-GATED-A` and `V0-AUTH-GATED-B` received `340 send article to be
  posted` before login where the plan expects refusal.
- `V0-BP-CRASH` was refused: after the crash it recorded
  `interrupted_absent=False` and `no_partials=False` despite durable state.

All ordinary reader, POST/read-back, transit, owner-feed, and recovery rows
reached their recorded decisions.  The run did not exercise
the BP replay result, BP node/dtn7-rs interoperation, carried-media import,
scale, INN, or slrn; the matrix names each blocker.  The statement reader
header was `not-built` because `:fn-verified` is not wired into the reader on
this source.

## Corrected TAKETHIS probe

The original capability-pin phase spent its two 600-second phase budgets
waiting for `TAKETHIS`: the driver issued the command and waited for an
initial reply, while RFC 4644 section 2.5 requires the article block before
the server sends its final reply.  This was a matrix-harness defect, not an
ACL2 or server defect.  The changed driver sends `TAKETHIS`, the terminating
empty block, then reads the final status; its generated overlay SHA-256 was
`55dd10ccb9f1555c5bf3f1aae84484fbcb350decfb90f313c39b5b98fd9c68d6`.

Without recertifying or rerunning the matrix, two `pins` invocations ran
against the kept snapshot, with only that generated driver overlaid:

```
python3 gate-run/matrix-corrected.py pins --port 45143 --group fn.letters \
  --user matrix --secret matrix-secret-8f21
python3 gate-run/matrix-corrected.py pins --port 33765 --group fn.letters \
  --user matrix --secret matrix-secret-8f21
```

Both exited zero.  The exact outputs are
[`pins-corrected-a.json`](v0-runs/20260921T064956.625126Z-cdbd6b2-11d907e01b5e/pins-corrected-a.json)
(SHA-256 `a8e310bdef8bcec0cea0c272f5bc6b835f8daa026aeed5b77046f184d313e712`)
and
[`pins-corrected-b.json`](v0-runs/20260921T064956.625126Z-cdbd6b2-11d907e01b5e/pins-corrected-b.json)
(SHA-256 `a3154fda1113351a252cc106903bb536086c2c7ae86dcb2b7b7e1bc70d474d91`).
Node B, which retained transit permission in that post-matrix state, returned
`439 <pin.take@matrix.example.invalid>` after the empty TAKETHIS block;
node A correctly refused its disabled transit command with `502`.  This
confirms the bounded probe completes and does not revise any original matrix
verdict.

The regression `CapabilityPinProtocolTests` runs the shipped driver against a
recording connection double and requires `send TAKETHIS`, `sendall .\\r\\n`,
then `line` in that order.  `python3 -m unittest tests.test_v0_matrix -v`
passed 43 tests, and `python3 -m py_compile tools/v0_matrix.py` passed.
