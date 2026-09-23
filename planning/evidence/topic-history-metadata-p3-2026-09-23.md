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
The decoder applies the topic-specific 1,536-octet whole-input preflight
before calling `fn-stmt-decode-items` with 39-item fuel. That statement seam
uses its standard 65,538/65,535 internal profile budgets, not 1,536-octet
internal budgets. Its declared-length checks compare against the remaining
prechecked input before taking bytes, so the smaller external preflight bounds
actual allocation and work while the standard seam inverse theorem supplies
the constructor roundtrip.

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

At that frozen image, the maximum 2,047-octet field value also exceeded the
998-octet physical-line limit when emitted on one line. The following
envelope batch resolves the source-level limit; the frozen native gate did
not cover the maximum constructor.

The envelope batch keeps the 998-octet physical-line and 32,768-octet
complete-source limits while raising the article parser's local header cap
to 16,384 octets and physical-header-line cap to 256. ACL2 now renders
FN-Topic base64 in 72-octet chunks with exactly one HTAB continuation. The
projector strips whitespace only as a candidate and accepts a folded field
only when the original raw lines equal the canonical ACL2 renderer; ordinary
single-line values keep the previous no-whitespace rule. The certified
`fn-th-field-lines-fit-85` theorem bounds every rendered physical line to
85 octets, below 998. Tests alter a continuation HTAB to SP and observe
`:folding` refusal.

An ACL2 maximum root has 16 ordered authors and 64 domain octets. Its
normalized value is 2,047 octets, canonical field uses 29 physical lines
and 2,143 wire octets. With 143 ordinary header octets and the full 7,525
octet FN-Authorship prefix, ACL2 measured an exact authored source of 2,289
octets and received carrier of 9,814 octets: 9,811 header octets, 135
physical header lines plus the separator. `fn-article-parse` accepts source
and carrier, `fn-hc-received-plan` recovers the exact source byte-for-byte,
and `fn-th-project-field` returns the maximum root. The binary fixture
`tests/fixtures/topic-history/max-root-field.bin` is 2,143 octets, assembled
from 64-octet chunks of ACL2's `fn-th-field-wire *th-max-root*` result; its
SHA-256 is `8b9aeeb3311f313d5b0826f105faaa05e93f398017451442ed7c128d04584851`.
The prepared native test signs this exact maximum source, inspects the
carrier, repeats inspection after relay Path/Xref prefixes, and refuses an
authored-byte mutation. A source-matched saved-image run of that maximum
profile remains open for root's combined build.

The envelope source and its tests were certified on hbox with ACL2 8.7,
SBCL 2.6.8 and toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`.
The [article and first envelope manifest](manifests/certify-20260923T205409Z-107337.json) records the changed
`books/article.lisp` digest
`8f81baba8e94b5db2bab12f7a12632bf01976b7d709f39faced1e35711df9155`
and passing article invariant/test roots. The [final invariant manifest](manifests/certify-20260923T205651Z-114702.json) records
`books/topic-history-metadata.lisp` digest
`99707bb41409058e8e31089fb96b1a878c3d3a182955d814f5834f915d33737f`
and `books/topic-history-metadata-invariants.lisp` digest
`f368a08d60945174ef4b65e0f00e85b02f8702ae190bb161a091208940335844`.
The [maximum-carrier source test manifest](manifests/certify-20260923T210021Z-121875.json) records final test digest
`d515ca5fca4b62672f6f3ba54f1904bb0c8809238efe931eb22d1176b205ac28`.
The scoped command was `python3 tools/farm.py submit hbox` with the named
article and topic book/test roots, `--jobs 2`,
`--acl2 /tank/fn/toolchains/w28/acl2-literal-4g`,
`--cache /tank/fn/certcache`, and
`--remote-root /tank/fn/gates/topic-envelope`, without `--closure`.
The maximum-carrier test certificate took 1.933 seconds; the exact requests,
source digests, and root results are in the manifests. The broad reverse
closure after the article-envelope change and the new native image remain
root's combined qualification work.

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
