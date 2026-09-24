# P3 exact historical report retry, 2026-09-24

The earlier experimental native topic path admitted a report but classified an
exact retry as a control refusal. `fn-th-prepare-report` already returned the
retained admission before checking current quota, roster or policy. This packet
connects that result to the actual owner call: `fnn-owner-topic-local-serialized`
calls `fn-owner-topic-propose`, whose `fn-th-local-propose :report` selects an
earlier accepted schema-1 T10 event and its historical keyring snapshot from
the carried topic prefix. Only `(:replayed-historical prior)` returns the new
successful status; the owner does not call `fnn-owner-topic-commit` on that arm.
The FNCT kind-8 reply carries only one status octet (code 4), not the prior
admission or any caller-supplied source. The command's exit projection returns
zero while printing `topic accepted, replayed-historical` distinctly.

The called-path theorem `fn-th-local-propose-report-retry-is-historical` traces
that success to the selected exact earlier source, pinned snapshot and retained
same-topic admission. `fn-th-report-retry-returns-retained-admission` supplies
the substantive selection and equality fact. The tests distinguish a not-yet
admitted proposal and a missing historical source from an exact retry. The
reply tests cover the 43-octet sealed frame, its 1-octet payload, roundtrip,
unknown code 5 and trailing-payload refusal; the native-control host wrapper
roundtrip and exit projection are also exercised.

The source-matched native scenario is prepared in
`tests/test_native_topic_local.py`: it uses one-report quota, admits one exact
signed report, retries before and after a Store reopen, and compares every
transaction filename and SHA-256 digest before and after. A missing historical
source must still refuse. It has **not** run on a matching saved image; the
shared native qualifier owns that run after combined closure and image build.

ACL2 8.7, hbox toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`,
shared certificate cache, two jobs, 120-second per-book limit and no `--closure`:

- `run-20260924T042103Z-6cb7`: owner-called proposal book passed; manifest
  `certify-20260924T042111Z-878525.json`, SHA-256
  `89f2f99dc6db363a18c19f890c182d7e5a9226332984a72741c80407a55a7eb4`.
- `run-20260924T042126Z-1225`: topic reply book and proposal/reply tests
  passed; manifest `certify-20260924T042136Z-879890.json`, SHA-256
  `bffa5db6e0294924a721db5d208ae7cfaec8252838b6470e823b7cba2a193dcd`.
- `run-20260924T042854Z-39e9`: final reply and native-control wrapper test
  roots passed; manifest `certify-20260924T042906Z-890015.json`, SHA-256
  `afa73fee0e684b29251b2801d247cc6485cac7852fbf5e44c274375b5b5c9fc5`.

The last manifest records exact source digests and the composed dependency
origins. These scoped proofs and tests do not establish a saved-image result or
physical publication refinement. The version-1 anchor event also lacks a
separate reference to the earlier administrator-install generation: it records
the installed ID and its own Store generation. Binding both ID and installed
generation needs a versioned event migration and is tracked as a separate
TOP-002 gap; this retry packet does not alter historical event bytes.
