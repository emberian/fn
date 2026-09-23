# T2b native NEWNEWS migration on the frozen 329 image

The first native migration test failed at its greeting assertion, before it
checked either response: the read-only native reader answered `201`, while
`tests/test_native_newnews_migration.py` required `200`. Its remaining old-only
expectation was also contrary to [the T2b horizon policy](../../specs/acceptance-stamp.md#26-newnews-answers-from-the-stamp).
This reader supplies no wall observation. With only a schema-0 article, no
newer stamped article exists to bound it, so the conservative `:none` horizon
reports the legacy Message-ID at both 1970 and 2099. After a schema-1 post,
that new stamp bounds the older article: the 1970 query reports new then old,
and the 2099 query is empty. The corrected test asserts both complete response
blocks and the `201` greeting; no served or host implementation changed.

The correction ran on hbox against the existing frozen image at source
`329a51a23f08e42904d4e0894c94ef5dc243d17e`, using
`build/freeze/run-next-runtime.py` SHA-256
`b0bb1d4a0151011ec02c40e87db419c63fb78830ac2489d485abd5b70072295e`
with only `tests.test_native_newnews_migration_fixed` selected. This was a
copy of the corrected test placed beside the original in the frozen source;
its SHA-256 was
`628e5141446921c22655b8393d99ec555e95e769df85937e86c633b2f9892286`.
The driver set the same old/new image and ACL2 environment as its wider run.
Python was 3.12.7. The new developer image core SHA-256 was
`59a228c5deddae7a0be1f12732c360e686ad825d16ec50f411ac0dc6b62cd144`;
the pre-T2 developer image core SHA-256 was
`66115e4374e71d107dc94f9f214cc0aeb68ac933334b83ee46d777944c958747`.

Result: one test passed in 0.516 seconds, exit 0. The exact
[test log](t2b-newnews-migration-329-logs/test_native_newnews_migration_fixed.log)
has SHA-256
`960b55e4bfbddc31929e10eb2cc31b10b1a8acb0843fb28d8b484eaf68f593e6`.
The original frozen test remains unchanged, so this result validates the
corrected expectation against that image; it does not claim a new image build
or a wall-observed reader branch.
