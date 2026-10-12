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

## Use: tools/test_search.py, never a bare `test?`
A bare `test?` prints "Test? succeeded" when it tested nothing. Over any function that takes a stobj (or a constrained function without an attachment) Cgen skips testing completely and says so only at verbosity 3 (found by P6 on fn-ptx-step; reproduced over `fn-lgb-cell` and the `fn-octets` stobj). It also says "proved" when no generated example satisfied the hypotheses. Most of fn's keystones are over stobjs, so the final "Test?" line is not evidence of a search (rule 6.6).

`python3 tools/test_search.py [--book books/<name>]... [--setup <events file>] '<statement>'`, run in a tree whose certificates are installed (on hbox through `swarm-build`), runs `test?` at verbosity 3 between markers and prints exactly one line:
- `SEARCHED <m> examples 0 counterexamples (<n> tested, <u> unique)`, exit 0, only when Cgen's summary shows at least one example satisfying the hypotheses and none falsifying the conclusion;
- `COUNTEREXAMPLE <first binding>`, exit 1;
- `SKIPPED <reason>`, exit 2: testing skipped (stobj or unattached constrained function), no example satisfied the hypotheses, no Cgen summary, a setup or translation error, or a timeout.
The verbose transcript goes to `--log` (default a fresh file under `build/test-search/`), its path on stderr.

Live on hbox in the C3 tree (ec78ffb17) with `--book books/store-log-buffer`: the `fn-lgb-cell` stobj statement printed SKIPPED with Cgen's own reason; `(implies (natp x) (< x 5))` COUNTEREXAMPLE ((X 53)); `(implies (natp x) (<= 0 x))` SEARCHED 1944 examples; `(implies (and (natp x) (equal x (+ x 1))) (< x 5))` SKIPPED 0 of 2000 satisfied. A SKIPPED over a stobj statement means the search is owed another way (an executable stobj-free restatement of the same predicate, searched); a packet citing 6.6 cites a SEARCHED or COUNTEREXAMPLE line.
