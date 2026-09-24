Frozen native subject: `bc9be7ec`, default composed artifact set
`1ac9d4538aa454f4a64ad76aeda77e65c16d62da2eff5214d1dcff8b28970c82`
(222 books, zero rejected); validation loaded all 87 production image roots.
The production image was
`/tank/fn/gates/reader-clone-poll-native-bc9-20260923/build/fn-host`
(SHA-256 `703ebc440fc696317e9f2169f0da1222ddd3a4fbe184c3c58d8b64353d606264`),
and the developer image at the same gate had SHA-256
`0261d56337f1c8278f29e1190ef34c011f5920b6a0df104c87fad69e8537fe5f`.
Both used w28 ACL2 and OpenSSL 3.5.8. Neither was deployed.

With source driver `tests/test_native_reader_index.py` SHA-256
`62da466617897a76e36b7cc9e761ec9518bd608f16232672ae15431457b043d3`,
`FN_RUN_NATIVE_READER_INDEX=1 ... python3 -m unittest tests.test_native_reader_index -v`
passed the indexed Message-ID and 24-group/96-LISTGROUP socket workloads,
but failed its historical live-group test after `operator group create fn.live`:
a fresh NNTP connection answered `211` for the group, while the subsequent
`operator post --group fn.live` returned REFUSED. An isolated repeat reproduced
the group creation, fresh `211`, then REFUSED; a following `fn.test` post
reported BUSY. The exact suite output is `native-reader-bc9-original.log`
(SHA-256 `03b0bd330e2ebd57d64006206f63eb22eb83ae0fc1d9a0ef8c1c696883ce2426`).
The native Store group-code cache was set only during recovery and did not
follow ACL2 owner live reconfiguration; the group-code lookup also sat outside
the Store-attempt refusal handler. Commit `c5d57cc8` repairs those paths, but
this image is intentionally the original negative subject.

With source driver `tests/test_native_checkpoint.py` SHA-256
`c89a056a69b2786d34bc0cda07e3b24458d14aeebc57eeda0318be9df5a0bb34`,
the independent canonical-parent-alias clone refusal and historical authored
verdict clone/reopen tests both passed under `FN_RUN_NATIVE_CLONE=1` in 4.109 s.
The exact log is `native-clone-bc9-independent.log` (SHA-256
`5cdb03d7a8c9eebc3784a54d140e824c9cee79ee0f0eefc59bc04242a2e38dad`).
The advancing consumer-ACK clone case depends on the poll CLI fix and was not
run on this known-broken image.
