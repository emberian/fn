# Experimental P3 root-only admission component

`fn-th-prepare-anchor` receives an actual completed T10 schema-1 article
event and historical keyring snapshot, not a caller-supplied verified flag. It
uses `fn-th-select-accepted-event`, requires the root controller and keyset
declaration to match the retained verified context, compares the caller ID to
an installed local administrator ID, rejects an existing root identity, and
requires a quota of 1 through 64 within a 16-anchor projection. It returns a
proposed topic event with the caller ID and T10 source reference. The local
projection remains unchanged until `fn-th-commit-anchor` recomputes the same
event against the historical inputs and adds the anchor.

`fn-th-prepare-report` likewise uses T10's bound source and key context. Its
fresh branch requires an active selected root, an exact verified author-ref in
the roster, all named parents earlier admitted within that same topic, and
remaining quota. A prior exact source/reference returns
`:replayed-historical` before current checks; conflicting source context is
refused. `fn-th-commit-report` recomputes the proposal before appending an
immutable historical admission and decrementing the finite quota. The
theorem `fn-th-fresh-report-is-grounded-in-current-root` proves the positive
branch's policy, roster, parent and quota conjuncts over this executable
preparation function. The commit theorems establish that a successful local
projection change requires equality with the recomputed proposal, and
`fn-th-replace-anchor-preserves-distinct-topic` shows a different topic's
anchor is untouched by replacement.

The test book constructs a T10-accepted root and signed carrier-backed report
using the existing ACL2 constructor. It executes anchor preparation and
commit, report preparation and commit, exact retry after a one-report quota is
exhausted, changed historical enrollment, wrong administrator, a separate
verified principal outside the roster, an unadmitted parent, and exhausted
quota. `must-fail` forms show that removing administrator, anchor, roster,
parent or quota premises changes outcomes. The `:contested` and
`:stale-policy` branches reserve future control-selection behavior and are
unreachable in this root-only composition.

Persvati certified the book in
[`certify-20260923T214858Z-589315.json`](manifests/certify-20260923T214858Z-589315.json)
and the final test bytes in
[`certify-20260923T215046Z-608772.json`](manifests/certify-20260923T215046Z-608772.json).
The invocations selected explicit roots, jobs 2, default persvati ACL2
`/home/ember/fn-gates/toolchains/w25/acl2-literal`, without `--closure`.
The toolchain identity is
`1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`;
the book and final test source SHA-256 digests are
`2c64009ea499647ea330666f7ac950fdbe57307450b99deb40df306029dad7b7`
and `0aa66e70b28eb5ac7194e28f1f482e9fa18af0a746e2fb63146399e1fb657092`.
The first two proof attempts exposed a guard proof opening the source codec;
replacing a partial `member-equal` call with total bounded author membership
kept that guard closed. The interrupted attempts are not cited as passing.

The follow-up codec book defines a distinct `fnto` version-1 payload for the
two proposed topic operations. It bounds input before statement decoding,
rejects unknown versions, trailing bytes and noncanonical encodings, and
requires the referred T10 article sequence to precede the topic event. The
anchor and report witnesses round-trip exactly; duplicate parents and an
over-quota anchor fail the recognizer. The accepted-canonical theorem and
an explicit oversize refusal test certify with the codec and test book in
[`certify-20260923T215838Z-688900.json`](manifests/certify-20260923T215838Z-688900.json)
on persvati using jobs 2 and the same toolchain identity. Exact source digests
are `cfae4af194b8eef8ce84c7080b527d46da56e9da7a46918a9c8ba7ffbc2897ff`
for the book and `657f67ee87880b526a284adce23173ab947541671541fc5261d82a8da38ee570`
for its test. The subsequent Store union recognizes the codec's two event
kinds and dispatches encode/decode and exact coordinates through the common
Store event functions. The focused [Store union book](manifests/certify-20260923T220254Z-735116.json),
[union test](manifests/certify-20260923T220325Z-741278.json), and
[replay/Store reverse roots](manifests/certify-20260923T220410Z-748161.json)
passed on persvati at jobs 2 with explicit roots and no closure flag, using
the same ACL2 toolchain identity. This is a syntax and envelope join only. No topic event can be
published by a native caller, and replay must not apply one until it can
re-resolve prior T10 source context and the historically installed local
administrator.

The ordered recovery-prefix component in `books/topic-history-prefix.lisp`
finds only preceding T10 accepted events and snapshots before invoking the
existing root/report commit validation. Its source-matched
[book and test manifest](manifests/certify-20260923T222127Z-926909.json)
passed on persvati with the standard ACL2 toolchain, jobs 2 and explicit
roots. The test accepts a bound root and rejects a wrong local administrator,
missing prior accepted event and missing snapshot. This does not integrate
the projection into Store's carried state or validate the native caller.

The local administrator component constructs a one-time install event from a
bounded observed UID and a separate 32-octet entropy observation. Its root
wrapper refuses a different current UID before invoking root preparation;
replay of a prior installation does not use current process credentials.
The [source-matched book and test manifest](manifests/certify-20260923T222820Z-998372.json)
passed on persvati, jobs 2, with explicit roots. The test's accepted root,
wrong-UID refusal, duplicate-install refusal and must-fail wrong-UID case
exercise the called wrapper. This logical event has no Store payload or
native caller yet, so it does not establish durable operator authority.

This packet has no same-journal publication,
replay/index relation, retention dependency pin, historical administrator
configuration lookup, native command or source-matched native test. It cannot
claim durable admission, a served topic view, or Mini authorization. Those are
the next P3 joins before a release claim.
