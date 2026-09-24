# K6 staged-name proof cost and Store v6 projection repair

Source: `1b734fe8` on `fix/byte-store-k6-cost`, based on `8c61c098`.
The affected root is `books/byte-store-record-provenance.lisp`; its test root is
`tests/acl2/byte-store-record-provenance-tests.lisp`.

The frozen `8c61c098` qualification bounded
`fn-bs-k6-related-staged-durable-final-name-absent` after 570.10 seconds,
with no proof checkpoint. Its hint opened the full Store file state and event
codec while proving a sequence-shape fact. A local theorem now extracts that
fact for the reachable `:record-staged` phase, and the K6 theorem keeps the
codec closed. The same book then exposed three K0 prepare hints that expanded
the fourteen-field Store v6 constructor. They now use the already proved
`fn-sn-files-of-fn-sn-update` projection. The K6 and K0 theorem statements
remain unchanged; the new local lemma is a proof step, not a registry event.

The selected hbox command was `python3 tools/farm.py submit hbox
books/byte-store-record-provenance
tests/acl2/byte-store-record-provenance-tests --jobs 2
--timeout-seconds 300
--remote-root /tank/fn/gates/byte-k6-cost-1b734fe8-20260924`.
Run `run-20260924T035813Z-ace4` produced the archived
[manifest](manifests/certify-20260924T035822Z-840791.json): both roots passed,
ACL2 8.7, qualified hbox toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`,
and `certify_wall_seconds: 9.506`. The provenance book took 7.027 seconds,
its test book 2.456 seconds, and the formerly costly K6 event 0.02 seconds.
The manifest binds the exact source and closure through `source_digests_sha256`;
the mirrored farm tree has no Git metadata, so `git_revision` is null.
`green_check --changed-since 8c61c098 --summary` reported one changed book,
one dependent test, and zero not green at these bytes. `make check` passed.

This evidence covers the selected K6/K0 provenance root and its existing
teeth. It does not certify the entire frozen image or establish a physical
platform durability profile.
