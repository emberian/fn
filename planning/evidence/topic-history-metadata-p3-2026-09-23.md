# P3 exact-source topic metadata, component evidence

The first experimental P3 slice adds `books/topic-history-metadata.lisp` and
`tests/acl2/topic-history-metadata-tests.lisp`, with an offline native
`topic-inspect-carrier` path. The native command calls
`fn-th-host-inspect-source` through `fnn-core` in
`host/native/signature-command.lisp` after the existing hybrid-carrier verifier
has returned exact authored source bytes. The command explicitly reports
`admission=unestablished`. This is no durable topic policy or Store admission.

On 2026-09-23, hbox certified the book at source SHA-256
`7fafa6aec06cddafa4a15f510b8eb2f19c27c9954f4ce607813569d7d60a9477`
in [the book/test manifest](manifests/certify-20260923T200634Z-19239.json)
and the final test book at source SHA-256
`27b24d95223db2e003530f4295b72777590a0dea1ab117a6a34d964c5d381f3d`
in [the final test manifest](manifests/certify-20260923T200855Z-21687.json).
The command was `python3 tools/farm.py submit hbox
books/topic-history-metadata tests/acl2/topic-history-metadata-tests --jobs 2
--acl2 /tank/fn/toolchains/w28/acl2-literal-4g --cache /tank/fn/certcache
--remote-root /tank/fn/gates/topic-metadata`, without `--closure`. ACL2 8.7,
SBCL 2.6.8 and toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`
are recorded in the manifests. The final test certificate took 1.988 s with
zero slot wait; the book itself was reused at its matching digest from the
previous passing manifest.

Tests exercise root, control and report roundtrips; a maximum root with 16
ordered authors and 64 domain octets encodes to 1,531 binary octets and 2,047
field octets. They reject the 17th author, duplicate authors/parents, duplicate
FN-Topic fields, malformed/folded base64 and oversized input. The book proves
its emitted binary is at most 1,536 octets, an over-limit decode refuses before
item parsing, and every accepted decoded binary re-encodes identically. These
are component facts. The maximum constructor length is an executed boundary
vector, not a general proved upper-bound theorem. PRF-062 remains in progress
until the host-called source projection has its binding theorem and the native
saved-image gate executes at matching bytes.

`tests/test_native_topic_metadata.py` is prepared with the literal field value
emitted by ACL2 and signs it through the native hybrid carrier. It checks
candidate output, relay-header invariance, signature refusal after authored
byte mutation, duplicate-field refusal and malformed folding. No additional
native image was built for this lane while the combined BP image was being
built. The live `/tank/fn/node` service was untouched. Root will run the test
on a combined image and record that image's source revision and result.
