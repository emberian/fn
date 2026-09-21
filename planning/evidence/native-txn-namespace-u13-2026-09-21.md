# Native transaction namespace U13 evidence

Revision `316e72d6` replaces the native transaction-directory parser with the
bounded `fnn-list-directory-bounded` observation and the ACL2 scan subject
`fn-bs-txn-observation-pairs`. `fn-store-txn-observation` supplies explicit
`(sequence, filename)` pairs; `fnn-durable-records` still compares each decoded
record sequence to that issued sequence before replay.

On hbox, source-matched ACL2 certification passed: direct scan/codec/test
closure `certify-20260921T103557Z-2047084` (49 books), followed by the 103-book
closure required by the developer-only store runtime image
`certify-20260921T104140Z-2053030`. The production image is outside this packet:
its remaining certificate closure includes unrelated owner/BP/TCPCL modules.

`host/native/build-store-test.lisp` is developer-only evidence wiring. It loads
the certified store dependencies and the actual `host/native/io.lisp` command
path, then saves `build/fn-host-store-test`; it is not an operator host profile.
The built image ran the source map and process tests for a malformed final name
and a hard-linked filename/decoded-record sequence mismatch. Both passed.

The native runtime witness covers bounded observation and namespace binding. It
does not claim full power-loss correspondence, arbitrary concurrent directory
mutation, or configuration-history recovery policy.
