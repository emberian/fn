# Native protected feed and restart witness, 2026-09-23

This is a bounded runtime observation, not a certification or a power-loss
claim. Five `tests.test_native_protected_peering` tests passed on hbox in 22.500
seconds. The complete captured output is
[`matrix-protected-f0b8b166-2026-09-23.log`](matrix-protected-f0b8b166-2026-09-23.log),
SHA-256 `7746ad2478f885d76e436d8a26f3a95d13fadabb4de957d09eb7e256e62f1ead`.
The invocation was `./run-protected-f0b8b166.sh tests.test_native_protected_peering`
in `/tank/fn/gates/takeover-matrix-witnesses`; the script contains the exact
environment and invokes `python3 -m unittest -v`. Its production and developer
images are the frozen pair at
`/tank/fn/gates/takeover-image-upgrade-f0b8b166/build/images/f0b8b166a3d5d56124ba45114bda0bd34affa5b8`.
The script set `FN_NATIVE_HOST`, `FN_NATIVE_DEVELOPER_HOST`, the source and
launcher/core/runtime digests below, `FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g`,
and `FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8`.
Python was 3.12.7; the saved images used bundled SBCL 2.6.8.

| Input | SHA-256 or source revision |
| --- | --- |
| Image source | `f0b8b166a3d5d56124ba45114bda0bd34affa5b8` |
| Production launcher / core | `432622d29a28d59455e01f3e5b426036c5862db21d5f7d1205a9304ab11e3505` / `004b694980fb1f2882eea9876da32028e8b183948277f72df5edbf6d66e19ff2` |
| Developer launcher / core | `e4eeefd290450e7497dade96e2c4089e0caacfa88f72c737f51a92b2f3b2ba18` / `66115e4374e71d107dc94f9f214cc0aeb68ac933334b83ee46d777944c958747` |
| Bundled SBCL | `b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5` |
| Harness `tests/test_native_protected_peering.py` | `b18a74c73c9f1c98b6eea342aa740ab6779800c3499f47e9ce7cb093389b71bd` |
| ACL2 journal inspector `tests/test_feed_journal_live.py` | `0b9bb4702e20fe4009ef49af8dd0193d4e89ed55f8b14e172fa2b98413403d92` |
| Matrix mapper `tools/v0_matrix.py` | `a13db24d839259195b399db382344e7987dce1487d1a9fc76f47e3023c9aca55` |

Both saved-image owners used fresh loopback stores and locally generated
certificates. The target required AUTHINFO on a protected connection; the
source named STARTTLS, its trust anchor, hostname, and credential profile.
Both directions delivered and reread identical article octets before and
after both owners restarted. A protected reader with no peer role answered
`502 transit is not permitted on this connection` to the same `IHAVE`, as
`books/nntp.lisp`'s reader dispatcher specifies (lines 80–89, RFC 3977
§3.2.1). Wrong outbound password and wrong certificate anchor each prevented
delivery while both owners remained alive.

The post-ack sender SIGKILL left the ACL2-replayed FNFD queue at `:done` both
before and after restart. Its journal had one offer, one sent, and one outcome
before the kill; those counts did not grow on restart. Recipient public status
reported `articles=1`. For the interrupted transfer, the developer sender
stopped immediately after durable `:feed-sent` and before the socket send,
then received SIGKILL. The ACL2 inspector read the real FNFD bytes: its state
before restart was `(:sent 1)`, after `fn-feed-restart` it was `:queued`, with
one offer, one sent, no outcome, and one queued entry. Restarting the sender
with the production image completed the obligation as `:done`; the journal
then had two offers, two sent records, one outcome, and the recipient had
exactly one article. Offer and sent records count transport attempts; the
entry's `attempts` projection was zero in these inspected states and is not
used as the transport count.

The journal inspector uses ACL2 `fn-feed-journal-scan`, `fn-feed-replay`, and
`fn-feed-restart` over the file bytes, with a valid synthetic feed contact.
Its eight live tests passed on ACL2 8.7 at
`/tank/fn/toolchains/w28/acl2-literal-4g`; local matrix unit tests passed
60/60 and `make check` exited zero. The proof books were unchanged by this
matrix harness batch. The test stops before the first socket write, so it
does not observe a duplicate accepted article or wire-level `CHECK` on the
first resumed attempt; it observes the durable requeue, new offer/sent
records, final outcome, and recipient Store count. It exercises process
death, not power loss, on one host and filesystem. The structured native
matrix must leave any row without its own matching observation
`not-exercised`.
