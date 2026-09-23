# Pre-stamp checkpoint migration, 2026-09-23

The exact frozen pre-T2 developer image was
`/tank/fn/gates/takeover-image-upgrade-f0b8b166/build/images/f0b8b166a3d5d56124ba45114bda0bd34affa5b8/fn-host-developer`.
The T2 developer image was
`/tank/fn/gates/takeover-t2-image-daa6c15e/build/images/daa6c15ef9d5c900b6e31ec9c9b51b9aaa708789/fn-host-developer`.
The probe ran on hbox with isolated temporary stores below
`/tank/fn/gates/crash-t2-migration`; it operated on no live node.

Before this decoder change, the old image initialized a Store, committed
sequence 0, and published and selected generation 0 of an ordinary checkpoint.
The T2 image's `store recover` completed authoritative replay but exited 4:
`recovered transactions=1 articles=1 ... checkpoint=corrupt reason=selected
generation 0 does not decode: (:ERROR :INVALID)`. The old checkpoint's node
contained a five-field article; T2's `fn-checkpointp` requires a sixth stamp.
This is a real migration failure, not an inference from the source diff.

The separate selected-pack case used the old image to pack sequence 0, commit
sequence 1, and reclaim the covered transaction file. The T2 image recovered
`transactions=2 articles=2` with only the suffix transaction file left and
returned both old article payloads byte-for-byte. The pack path therefore did
not exhibit this checkpoint-node shape failure. `checkpoint=none` in its
Store recovery output is expected: the selected pack is a separate authority.

The fix lives in the ACL2 checkpoint codec. New captures emit schema 1.
Schema 0 accepts the old ready-node five-field article list only after adding
`:legacy` and passing the complete current checkpoint recognizer; a non-NIL
pending field is refused. It also admits the short-lived T2 schema-0
six-field node unchanged. Schema 1 never coerces the old layout. The changed
canonicality theorem is restricted to the current header, since a migrated
old logical value cannot be encoded back to the old byte sequence by the new
encoder. The test book has a reachable committed legacy fixture, a version-1
old-shape refusal, and a `must-fail` showing why the current-header premise
cannot be dropped.

The patched ACL2 `fn-cpc-frame-open`, with the actual old selected generation
frame bytes and executable crypto/codec attachments, returned `(T :LEGACY)`
for successful decode and the retained article's stamp. Its frame digest and
header were checked before the logical migration. The affected ACL2 roots
`books/checkpoint-codec`, its test, `books/checkpoint-publish`, and its test
certified on hbox with w28 ACL2/toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`.
The selected-root runs were `run-20260923T171352Z-ca5a` and
`run-20260923T171651Z-82cc`; their archived manifests are
`planning/evidence/manifests/certify-20260923T171354Z-3979969.json` and
`planning/evidence/manifests/certify-20260923T171654Z-3986326.json`, binding exact source
digests and closure. A rebuilt exact-source native image has **not** yet run
the repaired selected-checkpoint migration; the frozen daa image still fails
as measured above. The probe is
`tests/campaign/t2_checkpoint_migration_probe.py` and requires explicit
old/new image and isolated-root environment paths.
