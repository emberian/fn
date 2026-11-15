# Budgeted digest fetch: current-source proof packet

SOURCE ONLY. No ACL2, certificate installation, pair-alist comparison, native
execution or farm job has run for this packet. Archive authority and hold release
remain unfinished; this packet grants neither.

The base is `a1dba5a1c7bd303ba6085c589b9020c357624079`. The entire original
`fn2-rec-fetch` definition, `fn2-rec-byte-at` definition and two byte theorems,
and `fn2-rec-fetch-shape` theorem are byte-identical to the base. The original
pool-digest blob is `d1e67d1c69ed93f48841082bb5517fe8193e9f87`, SHA256
`f7d2dd9f1687703d8df34e771925515c32998325d844bbc05d316e63191c1096`.
No pool/layout/column/BLAKE3 source is changed. In particular, the qualified
layout SHA256 stays `2060684efd33bb23e0c426275edc9a3dc6c47b50ceda0b80207c84ec7fd89d48`.

`fn2-rec-fetch-step` consumes at most its byte budget, returning the absolute
next byte and a width-constrained partial U32 accumulator. It calls the existing
`fn2-layout-byte :u32` transition and writes a digest word only after all four
bytes succeed. Budget zero preserves the complete carrier and continuation.
An owner/stale/bounds error preserves the partial word and all previously
committed words. The pool is read-only. The unchanged old fetch remains the
reference for code and complete digest-carrier effects.

`fn2-rec-fetch-exec-refines` states exact two-result equality under the original
typed guard. Local proof support supplies a full four-result worker composition
statement, extracts the aligned four-byte reads/store from the original fetch,
and splits the remaining worker at that word. The final hint inducts the
original fetch. These statements and guard events are authored, UNRUN proof
obligations, not established equalities. Source controls cannot discharge them.
The first refuting gate must admit the new definitions, invariant/composition
lemmas and guard events before reaching the final equality; a failure there
must be fixed before importing the event-reader continuation.

`tests/pool-digest-budget-unit.lisp` uses the actual U32 encoder and independent
boundary words including high-bit/all-one values. It checks all aligned starts
0..8 against the unchanged API with complete carrier copies and the whole
refinement premise, 32 budget-one visits, budget-zero effects, wrong owner,
stale generation, stale after a partial word (byte5/acc255), and a fill10
failure with identical complete-carrier effects. The expected values are not
derived by decoding the writer output. These executable controls are UNRUN.

The mechanical transformations and their before fixtures are in
`tools/pool_digest_budget_rewrite.py` and `tools/pool_digest_proof_rewrite.py`.
Seven Python source controls pass. Lisp structural checks, secrets and diff
checks pass. No logical proof or executable fixture success is claimed.

## Exact dependency/cache cut

`digest-fetch-current-inventory.json` records the plain-world v4 closure keys,
source/form hashes and candidate cache metadata for exactly ten local books.
The nine unchanged dependencies have compiled candidates at
`fn@forge:/home/fn/.cache/fn-certs` for toolchain
`8aeb1bea18968c6cd33ac633a80ebf67e4924504db112fd27eb11f16a27b2a8c`;
only the changed `books/pool-digest` key misses. Candidate integrity/origin
selection used the existing `certs.cached_entries`/`choose_entry` recipe from
`/build/lanes/ticket-frontier-3b62`. This is metadata and payload-integrity
inventory, not ACL2 core/pair compatibility or certification. The earlier
hbox default-cache query is superseded and supplies no miss evidence.

Reproduce the read-only inventory with:

```
python3 tools/digest_fetch_current_inventory.py --remote --output /tmp/digest-fetch-current.json
```

The shared launcher coordinate supplied by the integrator is
`/tank/fn/toolchains/w28/acl2-literal-4g-tls64k`. No launcher was invoked. Any
later gate requires a named root compute grant and must reuse the nine cached
candidates without silently certifying dependencies. The broader cold archive
reader/boot closure is deliberately excluded from this prerequisite packet.
