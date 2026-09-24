# Topic event separation in Store proof closure, 2026-09-24

The frozen integrated source `8c61c098` exposed a false article-stamp
classification. A valid `:topic-admin-install` satisfies the former
retention/identity/consumer exclusions, but advances Store history without
installing an article. `fn-replay-article-eventp` and
`fn-sn-finish-installs-the-stamp-the-record-carries` now explicitly exclude
topic events. The replay stamp projection consequently omits them. The
acceptance-stamp test book asserts a valid topic install contributes no stamp,
retains the ordinary article's stamp, and uses a concrete `must-fail` to show
the old exclusions do not imply article classification. The composite
finish-node helper keeps the actual accepted-statement arm proof closed over
the 14-slot Store constructor. These statements concern logical article
classification and replay, not native saved-image execution.

The keyring reconfiguration theorem remains unchanged: it preserves a valid
Store state and its history relation. Its proof now projects the 14-slot
constructor's selectors explicitly, including topic, while keeping the topic
record grammar closed in the completion-enabled proof. The malformed
wrong-sequence-tag test still checks the retention decoder's exact
`(:error :record)` and the composed decoder's refusal. Its previous assertion
of the dispatcher’s final `(:error :version)` detail was invalidated when a
later topic decoder alternative was added; that incidental tag was never the
public refusal contract.

All runs used hbox ACL2 8.7/SBCL with toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`,
the shared certificate cache, two jobs, explicit roots, and no `--closure`:

- [`certify-20260924T035440Z-832740.json`](manifests/certify-20260924T035440Z-832740.json): `books/acceptance-stamp-invariants` emitted its per-book success marker. The overall two-root run failed on the then-unrepaired Store-prepare book.
- [`certify-20260924T035643Z-837105.json`](manifests/certify-20260924T035643Z-837105.json): `books/store-prepare-correspondence` passed.
- [`certify-20260924T035738Z-838587.json`](manifests/certify-20260924T035738Z-838587.json): both corresponding ACL2 test books passed.
- [`certify-20260924T034540Z-814575.json`](manifests/certify-20260924T034540Z-814575.json): `tests/acl2/store-events-tests` emitted its per-book success marker; that broader repair-attempt run failed on the two then-unrepaired invariant books.

The successful book markers are cited per book rather than calling either
failed multi-root run green. Matching cache closure keys cover the unchanged
source of those books in the final repair tip. Full reverse closure and a new
combined image remain the integration gate's work. The earlier proof-REPL
composition concern was not reproducible after the cache had the complete
dependency closure: the status lane loaded 95 matched dependencies from 12
snapshot origins under the same toolchain identity, with no cache policy
change.
