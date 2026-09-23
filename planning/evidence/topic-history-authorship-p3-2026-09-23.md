# P3 topic candidate authorship binding, scoped evidence

The offline native `topic-inspect-carrier` command calls
`fn-th-select-verified-source` in `host/native/signature-command.lisp` after
`fnn-hsig-verify-received-carrier` returns `(:verified exact-source principal
ordered-keys)`. The ACL2 selector invokes the existing exact-source topic
projector and derives `(principal, keyset-id)`, where `keyset-id` is
`fn-id-subject-of-payload` of the canonical
`fn-hsig-keyring-snapshot(principal, ordered-keys)`. A root is
`:controller-matched` only when both declared principal and keyset identity
equal that verified reference. `:controller-mismatch` remains a generic
authenticated topic candidate, never an authority verdict. A report's author
comes from the verified reference regardless of `From` or mutable relay
headers. The CLI still reports `admission=unestablished`.

The separate `fn-th-select-accepted-event` reads a schema-1 retained article
and historical keyring snapshot only after
`fn-hsig-article-event-snapshot-bindsp-v1` succeeds. That T10 predicate ties
the event's exact authored source to its received carrier, source identity,
historical `:verified` verdict and enrolled principal/ordered keys. The
selector then calls the same verified-source selector on those bound values.
The historical wrapper is an ACL2 candidate API ready for a future Store
topic-admission caller; no current native path invokes it or commits a topic
admission. Its binding predicate checks retained evidence and does not
reimplement the cryptographic primitive verifier.

`fn-th-selected-root-matches-verified-context` proves that a successful
host-called matched-root result carries both declared fields equal to the
verifier-derived author reference. `fn-th-selected-report-author-is-verified-context`
proves the report author is that reference. The accepted-event theorem
`fn-th-accepted-root-author-is-historical-enrollment` adds the T10 binder as
an explicit premise for a historical matched root. The test book executes a
matching root, changed principal, changed keyset under the same principal,
false `From`, competing relay FN-Topic, a real schema-1 carried event,
changed historical enrollment and substituted retained source. Must-fail
events remove principal, keyset and snapshot binding premises. These witnesses
separate principal equality from exact keyset equality; they do not treat
`From`, an unbound verdict, or relay headers as authority.

The scoped hbox run
[`certify-20260923T211422Z-167141.json`](manifests/certify-20260923T211422Z-167141.json)
certified `books/topic-history-authorship` and
`tests/acl2/topic-history-authorship-tests` at SHA-256 source digests
`e447fc3d6835234908043559ab34541710bb7420629bcc870a6a9e3943558da2`
and `2cea1bd09ca5017352ac82d2f78287fdf946c34053c53ca94751913a75ffd577`.
It used ACL2 8.7, SBCL 2.6.8 and toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`.
The command was `python3 tools/farm.py submit hbox
books/topic-history-authorship tests/acl2/topic-history-authorship-tests
--jobs 2 --acl2 /tank/fn/toolchains/w28/acl2-literal-4g
--cache /tank/fn/certcache --remote-root /tank/fn/gates/topic-author-binding`.
It installed 50 matching dependency certificates and certified the two roots
without `--closure`; their ACL2 times were 1.857 and 2.029 seconds.

The changed native inspector and assertion in `tests/test_native_topic_metadata.py`
await a source-matched combined saved-image run. The hbox component result
does not establish native formatting, Store topic events, anchor installation,
roster adoption, succession, fork resolution, report admission, or application
authorization. Those are separate P3 work.
