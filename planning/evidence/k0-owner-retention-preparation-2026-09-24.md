# K0 owner retention preparation handoff

`host/owner-host.lisp:360-378` constructs a retention event with
`fn-store-retention-event-make`. Its sequence is the live Store identity-next;
both txid and generation are the live acceptance next-txid. The three host
text conversions call `fn-store-octets->string`, which is
`fn-record-octets-string` (`host/store-host.lisp:49-50`). The host then invokes
`fn-owner-step (:store (:prepare-retention event))`, which calls the logical
`fn-ocfg-step` (`host/owner-host.lisp:208-212`).

`fn-orpr-configured-store-of-prepare-retention` equates that configured-owner
Store projection to `fn-sn-prepare-retention`. The public
`fn-orpr-host-retention-prepare-branches` states the exact constructor
arguments and, from a reserved Store projection, proves the host's two result
branches: an unchanged Store projection is not staged (`:refused`), while a
changed projection is `:record-staged` with `fn-sf-record-candidate` equal to
the exact event (`:prepared`). It does not require a second host-side
calculation of the event. The ACL2 test reaches a well-formed configured owner,
stages an undertaking, and refuses a syntactically valid release for an absent
obligation. A `must-fail` test uses the same reached owner after staging:
without the reserved-phase premise, refusal leaves `:record-staged` in place
and the public conclusion fails.

A bounded hbox ACL2 proof REPL loaded the final book in source order and was
stopped. Selected certification invoked
`python3 tools/farm.py --root /Users/ember/dev/fn/build/lanes/owner-retention-preparation --remote-root /tank/fn/gates/owner-retention-preparation-863c2141-farm --jobs 2 --timeout-seconds 180 --acl2 /tank/fn/toolchains/w28/acl2-literal-4g --cache /tank/fn/certcache submit hbox books/owner-retention-preparation tests/acl2/owner-retention-preparation-tests`.
Run `run-20260924T062239Z-df2a` passed both selected roots; [manifest](manifests/certify-20260924T062249Z-1003562.json).
ACL2 8.7 executable SHA-256 was
`9f73da2a84d664516033fb6e944c55b55d1f7206e9599cac46ca2b208de26aa8`
with toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`.
The source digests were
`f2bda39c6a3376b8a6a4f110ab5c21c6fa04c91d12667093cb15b705fd62d583`
for the book and
`c1557d46522125d2f1bb6b18254577827a221d3137b48ca55464ecda4e26c5f1`
for its test. The two roots took 3.676 s and 4.075 s; total wall time was
7.79 s. The run installed 124 dependencies from the matching shared cache
without closure certification.

The theorem starts at a reserved logical Store projection. It neither proves
that every served caller reaches that phase with a byte-related physical
state, nor proves subsequent byte publication, error cuts, or physical
filesystem barriers. The separate byte retention packet handles selected
P-RECORD cuts from its stated related inputs; a composed served-call K0 theorem
remains open.
