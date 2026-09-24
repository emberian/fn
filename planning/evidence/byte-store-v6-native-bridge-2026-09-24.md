# Store v6 native observation bridge repair

Source: `08ba33bb` on `fix/byte-store-native-topic`, based on `8c61c098`.
The source files are `books/byte-store-native-correspondence.lisp` and
`books/byte-store-fault-keystones.lisp`; the corresponding existing test books
are `tests/acl2/byte-store-native-correspondence-tests.lisp` and
`tests/acl2/byte-store-fault-keystones-tests.lisp`.

The frozen `8c61c098` hbox qualification failed
`fn-bs-native-io-is-byte-observation` because its hint opened the expanded
Store v6 constructor. ACL2 was left with unreduced `fn-sn-files` and
`fn-sn-node` selectors over a fourteen-field list. The separate K7 fault
book used the same expansion in four composed-subject theorems. Their theorem
statements and host calls did not change. Local selector lemmas now close the
v6 constructor in the observation proof; the K7 hints use that proved
observation bridge and the composed state's file projection.

The native host calls `fn-store-sn-io` from `host/native/io.lisp:786` via
`fnn-observe`; the wrapper calls `fn-sn-io` at
`host/store-node-host.lisp:432`. The K7 theorems state that this called
transition fences after record-link, allocator-rename, or either authority
directory error. The shared owner binds a different callback to
`fn-owner-io`; its configured-owner caller correspondence remains a separate
K0 obligation.

Validation: `python3 tools/farm.py submit hbox
books/byte-store-native-correspondence
tests/acl2/byte-store-native-correspondence-tests
books/byte-store-fault-keystones
tests/acl2/byte-store-fault-keystones-tests --jobs 2
--remote-root /tank/fn/gates/byte-native-08ba33bb-20260924` submitted
`run-20260924T034653Z-7b9e`. The archived
[manifest](manifests/certify-20260924T034701Z-815999.json) reports exit 0,
four roots certified, zero book failures, ACL2 8.7, and qualified hbox
toolchain identity `d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`.
Its `source_digests_sha256` bind the exact books and include closure. The
manifest reports `certify_wall_seconds: 7.324` (individual roots 2.242,
2.660, 2.332 and 2.723 seconds respectively). The farm root was
`/tank/fn/gates/byte-native-08ba33bb-20260924`. Because the mirrored tree has
no Git metadata, the manifest's `git_revision` is null; source identity rests
on those exact file digests and the local `08ba33bb` checkout. The changed-book
`green_check --changed-since 8c61c098 --summary` reported two
changed books, two dependent tests and zero not green. `make check` passed.

This selected certification repairs the Store v6 proof regressions in those
four roots. It does not certify the whole frozen image or establish the
physical platform durability profile. The same frozen qualification also
bounded a separate K6 provenance proof-cost event and `owner-invariants`;
those are recorded as open work, not counted as passing here.
