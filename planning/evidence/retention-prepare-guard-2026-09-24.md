# Host-reached retention preparation guard

`host/store-node-host.lisp:514` calls `fn-sn-prepare-retention` for the
standalone Store. The production shared-owner route reaches the same Store
transition from `host/native/bp-obligation.lisp:44,66` through
`fnn-owner-retention-commit` (`host/native/owner.lisp:746`),
`fn-owner-prepare-retention` (`host/owner-host.lisp:360,377`), and
`fn-owner-step` (`host/owner-host.lisp:207-211`). The ACL2 function is in
`books/store-node.lisp:913`. Its declared guard is `fn-sn-statep` of the input
Store; before this packet its guard had not been verified.

`verify-guards fn-sn-prepare-retention` now proves that a Store satisfying
`fn-sn-statep` supplies the file-state and node-state guards needed on the
reachable reserved/valid-retention-event arms. The logical transition is
unchanged. In `tests/acl2/store-node-guards-tests.lisp`, the ACL2 guard-world
assertions check the exact exported guard and Common Lisp compliance. A
reachable freshly reserved Store stages an `:undertake` event while leaving
the live node unchanged until the directory barrier; a malformed Store/input
pair exercises the total logical refusal with guard checking disabled.

The isolated lane started from `dev` at `7caa9a03`. The certified source
SHA-256 for `books/store-node.lisp` is
`12e83e44b6091e46e86ae077ebdd6c37601bec32308f08d59f45f60a92feb3cf`;
the final test book is
`1c72323fc9bea00e7db356150d1b585a92f95be5729c0c0739b48d401c4b23ce`.
Both manifest before/after digests match. The ordinary hbox invocation was
`python3 tools/farm.py submit hbox --jobs 2 --remote-root /tank/fn/lanes/retention-prepare-guard books/store-node tests/acl2/store-node-guards-tests`.
Run `run-20260924T041858Z-b469` passed with ACL2 8.7 at
`/tank/fn/toolchains/w28/acl2-literal-4g`, toolchain identity
`d5f2b9f0d2cf68c6074ea7046fbd2e560d2984fe22d7e03f93045975ac889f0`.
Its [manifest](manifests/certify-20260924T041901Z-866651.json) records 69
compatible cached books and six certified books. `books/store-node` took
26.315 s, `store-node-invariants` 116.791 s, `store-node-traces` 74.018 s,
`store-node-resolution` 5.280 s, `store-observed` 6.782 s, and the initial
guard test 2.823 s. The guard verification event itself took 0.01 s and 416
prover steps; the 232.077 s run reflects the dependent books, not guard
search. After adding the reachable witness, a one-job incremental run
`run-20260924T042515Z-f8f4` passed the final test book in 2.722 s with all
74 dependencies matched and retained; its [manifest](manifests/certify-20260924T042518Z-885757.json)
records the final test digest.

The `green_check --changed-since 7caa9a03 --summary` audit finds both edited
books green at their bytes and 167 reverse dependents stale. The lane did not
recertify that full reverse closure, build a native image, or prove that
`fn-own-step`/`fn-ocfg-step` maintains the Store guard at every host call.
Those are separate integrated caller and image obligations. This proof says
nothing about physical barriers or durable retention on hardware.
