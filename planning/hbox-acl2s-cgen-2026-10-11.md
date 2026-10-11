# hbox: acl2s/cgen certified, `test?` runs there (2026-10-11)

Statement-first packets (COORDINATION 6.6) need an ACL2 `test?` counterexample search; until 15:02 EDT 2026-10-11 hbox could not run one because `acl2s/cgen` was uncertified in its system books.

## What was certified
- Command (hbox, Builder B14, PID file `/tank/fn/scratch/b14-cgen.pid`, log `/tank/fn/scratch/b14-cgen.log`):
  `cd /tank/fn/acl2-8.7/books && ACL2_CUSTOMIZATION=NONE swarm-build perl build/cert.pl --acl2 /tank/fn/toolchains/w28/acl2-literal-4g-tls64k -j 8 acl2s/cgen/top`
- Result: exit 0, 303 system books built (std/strings, defsort, acl2s/defdata, acl2s/cgen and their closure), 15:01:53-15:02:13 EDT.
- Scope: the make dry run (hbox:/tank/fn/scratch/b13-cgen-dry.log) listed only books with no existing certificate; no existing system certificate and no fn certificate was rebuilt.

## Toolchain identity unchanged
`python3 tools/acl2_toolchain.py identity /tank/fn/toolchains/w28/acl2-literal-4g-tls64k` on hbox after the certify prints `8aeb1bea18968c6cd33ac633a80ebf67e4924504db112fd27eb11f16a27b2a8c`, the identity `/tank/fn/certcache` is keyed on. The identity binds launcher, core, runtime and environment, not system-book certificates, so the fn certificate cache stays valid.

## Proof that it works
hbox:/tank/fn/scratch/b14-cgen-test.lsp under the same launcher (log b14-cgen-test.log):
- `(test? (implies (and (natp x) (natp y)) (< x (+ x y))))`: "Test? found a counterexample" (y = 0), 3 counterexamples, 198 witnesses.
- `(test? (implies (true-listp l) (equal (len (append l l)) (* 2 (len l)))))`: "Test? succeeded", 0 counterexamples, 1989 witnesses.

## Use
In a session on hbox's w28 launcher: `(include-book "acl2s/cgen/top" :dir :system :ttags :all)` then `(acl2s-defaults :set testing-enabled t)` and `(test? <statement>)`. Run it through `swarm-build` like every hbox job.
