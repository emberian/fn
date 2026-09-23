# P3 exact-source topic metadata, component evidence

The first experimental P3 slice adds `books/topic-history-metadata.lisp` and
`tests/acl2/topic-history-metadata-tests.lisp`, with an offline native
`topic-inspect-carrier` path. The native command calls
`fn-th-host-inspect-source` through `fnn-core` in
`host/native/signature-command.lisp` after the existing hybrid-carrier verifier
has returned exact authored source bytes. The command explicitly reports
`admission=unestablished`. This is no durable topic policy or Store admission.

The follow-up assurance batch gives that native call symbol an ACL2 logic-mode
definition in `books/topic-history-metadata.lisp` and proves
`fn-th-host-inspect-source-binds-authored-field` about the exact function named
by the command. Successful projection requires a parsed source with exactly
one FN-Topic field and equals decoding that authored field's unfolded value.
`fn-th-constructor-encoding-bound` and `fn-th-constructor-roundtrip` cover
every valid root, control and report value: at most 1,531 encoded octets and
39 items, then decode(encode(value)) = value. A received article with relay
Path, Xref and a competing FN-Topic is an executed separation witness: the
authored source remains a root candidate while projecting the whole received
article refuses its duplicate field. Invalid duplicate-author constructors
and duplicate authored fields provide must-fail teeth for the hypotheses.

Hbox certified the changed codec (`f44975a4206b18a65c19cf0cba40c8d70fc2b01483e67df5b21a7345305e4e36`),
new invariant book (`ac76677c92057c98b3ae20d344f368c8f566f278700c9d288285c43e9cea27ec`),
and test book (`c41016b68e30a22d9bec90752ec48e7f4b0cd01cd4474bc868f2cf14c957b84e`)
in [the exact follow-up manifest](manifests/certify-20260923T203140Z-48694.json).
The invocation was `python3 tools/farm.py submit hbox
books/topic-history-metadata books/topic-history-metadata-invariants
tests/acl2/topic-history-metadata-tests --jobs 2
--acl2 /tank/fn/toolchains/w28/acl2-literal-4g --cache /tank/fn/certcache
--remote-root /tank/fn/gates/topic-assurance`, without `--closure`. ACL2 8.7,
SBCL 2.6.8 and toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`
are recorded there. The three roots took 1.688, 4.383 and 1.88 seconds.

The first frozen-image native test exposed a composition limit, not a topic
decoder failure. ACL2 measured the portable FN-Authorship header prefix at
7,525 octets. With 143 octets of ordinary headers and the 295-octet root
FN-Topic field line, the received header is 7,963 octets and parses. A
duplicate of that field raises it to 8,258 octets, exceeding the article
parser's 8,192-octet header limit; `fn-hc-received-plan` returns
`:unverified :article` before topic inspection. A short valid zero-parent
report field emitted by ACL2 yields a duplicate-field received article of
7,981 total octets. The carrier plan accepts and extracts the exact authored
source, then `fn-th-host-inspect-source` returns `:duplicate`. The revised
native test at commit `1da3801f` has SHA-256
`695f3cd55468443ff821ca95f9883bd56062754a3fe325b4e3367e49ee0563c8`.
Staged as `build/test-topic-followup.py` against frozen `884e4816` developer
image, it passed one test in 0.662 s. The log at
`/tank/fn/gates/integrate-reader-repair-20260923/build/test-topic-followup-884e4816.log`
has SHA-256 `fddfe257926a17f7a712195893acfd92ab2ab508da07ad9b5910d46e804b6349`.
This is a test-driver correction against the frozen image, not a rebuilt
image at the follow-up assurance source digest.

The maximum 2,047-octet field value also exceeds the article parser's
998-octet physical-line limit when emitted on one line. The current decoder
rejects folding whitespace, so the full bounded component profile is not yet
realizable through a portable carrier. The next envelope batch must define
ACL2-owned bounded folding/normalization and raise the header budget from a
measured combined profile; the current native gate does not cover the maximum
constructor.

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
vector in the first batch; the general upper-bound theorem is in the follow-up
above. PRF-062 remains in progress until the native saved-image gate executes
at matching bytes.

`tests/test_native_topic_metadata.py` is prepared with the literal field value
emitted by ACL2 and signs it through the native hybrid carrier. It checks
candidate output, relay-header invariance, signature refusal after authored
byte mutation, duplicate-field refusal and malformed folding. No additional
native image was built for this lane while the combined BP image was being
built. The live `/tank/fn/node` service was untouched. Root will run the test
on a combined image and record that image's source revision and result.
