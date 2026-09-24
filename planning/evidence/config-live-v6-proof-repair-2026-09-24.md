# Configuration publication projection repair

The failed combined `f0d67034` run exposed
`fn-ocl-durable-keeps-file-phase` in `books/config-owner-live`. Its unchanged
statement says configuration publication preserves the Store file phase.
The new configuration updater expanded into nested `update-nth` forms before
the exported `fn-sn-files-of-fn-sn-with-configuration` rule could match.
This was a failed proof, not an observed change to configuration behavior.

Source `90d40083` locally disables that updater in the proof book. It changes
no definition, theorem statement, native host behavior or public theory.
The existing selector rules now establish the file and history projections.
The original failed combined evidence is retained in
[the f0d record](topic-index-f0d-combined-red-2026-09-24.md).

A bounded hbox proof REPL installed 127 matching dependencies from the
composed cache, loaded the prefix, admitted the two projection theorems and
all 112 remaining forms. The file-phase theorem took 0.00 seconds of proof
time and 867 prover steps. The session was stopped before certification.
Interactive admission alone is not the certificate.

Ordinary scoped run `run-20260924T042010Z-b64a`, in
`/tank/fn/gates/config-live-v6-20260924`, passed both
`books/config-owner-live` and `tests/acl2/config-owner-live-tests`.
Its committed manifest is
`manifests/certify-20260924T042020Z-876512.json`. The run used two jobs,
a 120-second per-process bound, 128 installed dependencies and two new
certifications. Certification wall time was 14.907 seconds: 10.594 seconds
for the book process and 4.277 for the test process. The book remains just
above the ten-second iteration target.

The pinned executable was `/tank/fn/toolchains/w28/acl2-literal-4g`, toolchain
identity `d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`;
the manifest records source/include digests and the toolchain details.
This scoped result does not qualify the combined image or establish physical
configuration publication; those remain separate proof and runtime work.
