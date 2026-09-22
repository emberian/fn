# T8 live reconfiguration: certification evidence (2026-09-22)

Lane `t8/reconfig`, tree 0215c889 (branch from dev 2788d4cb). Toolchain
`/home/ember/fn-gates/toolchains/w25/acl2-literal` on persvati, cache
`/home/ember/fn-certcache`, `--jobs 4`.

## Closure run

`python3 tools/farm.py submit persvati books/owner-config books/native-admin
books/config-records tests/acl2/owner-config-tests tests/acl2/native-admin-tests
tests/acl2/config-tests books/owner-prepare-correspondence
tests/acl2/owner-prepare-correspondence-tests books/native-operator --closure
--jobs 4 --timeout-seconds 1800 --remote-root /home/ember/fn-gates/t8-reconfig ...`

Run `run-20260922T194322Z-e870`, manifest
`planning/evidence/manifests/certify-20260922T194330Z-3337336.json`: exit 1,
97 passed and 15 failed. Certified: `books/config-records`,
`tests/acl2/config-tests` and the whole closure below the store cascade.
Failed: `books/store-node-traces`, `store-node-resolution`, `store-observed`
(the store cascade, not edited here) and every book above them, including
`books/owner-config`, `books/native-admin` and their test books, which have
no certificate on this run.

## Provisional wave

`python3 tools/triage.py persvati books/owner-config books/native-admin
tests/acl2/owner-config-tests tests/acl2/native-admin-tests
books/owner-prepare-correspondence tests/acl2/owner-prepare-correspondence-tests
books/native-operator --remote-root /home/ember/fn-gates/t8-triage
--budget-seconds 800 --rounds 1 --jobs 4 ...`, run `run-20260922T200009Z-2da1`
(not a certification). Proved, not certified, waiting only on
`books/store-node-traces`: `books/owner-config`, `books/native-admin`,
`books/native-operator`, `tests/acl2/owner-config-tests`,
`tests/acl2/native-admin-tests`, `tests/acl2/owner-prepare-correspondence-tests`.
Independent reds in the closure: `store-node-traces`, `store-node-resolution`,
`store-observed`, `store-prepare-correspondence`, `owner-invariants`
(`fn-own-read-offers-against-the-live-node`), and
`owner-prepare-correspondence` (`fn-opc-configured-step-preserves-owner-relation`).
The last one's only failing arm, reproduced in a proof_repl session over this
tree, is `(:open ...)`: `fn-ocfg-open`'s `fn-own-reader-context` has no
relation-preservation lemma. This lane did not change `fn-ocfg-open`; the
`(:complete)` arm it changed proves. Timeout: `books/peer-inbound` (800 s).

## Harness

`python3 -m unittest tests.test_native_live_reconfiguration -v`: the three source
checks pass; the two image witnesses skip because `build/fn-host` is not
present here. `V0-CFG-LIVE` is not claimed: a group created live is not
served before restart (`books/owner-config.lisp` OPEN item 3), which the
image test records as an expected failure.
