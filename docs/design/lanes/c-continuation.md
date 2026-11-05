# fn2 layer C continuation (the ordered-run metadata engine; present state at origin/dev a4bea27de, rewritten whole 2026-11-04)

Layer doc: `docs/c-ordered-runs.md`. Brief: `docs/design/briefs/FN2-LAYER-C-ORDERED-RUNS.md`. No C seat is live on
2026-11-04; nothing of C's is in flight.

## On dev (C, newest first)
- edc631a44 (H4, Nov 2): `fn2-seal-pending-p` moved to `books/sealer.lisp`; pending whenever the seal row is in
  `:build`, `:filter` or `:install`, or `:idle` with a sealable published overlay; `fn2-seal-cache` refuses a
  collision with a `:ready` page (core stop `*fn2-stop-reason-sealer-cache*`). Teeth in `tests/sealer-unit.lisp`,
  `tests/sealer-machine-unit.lisp`.
- 19d57c6d5 (F3): schema rows emit `put-<prefix>-row` and `<prefix>-rowp` (`fn2-defschema-row-events`); the txn
  writes through `:links` and `(:set ...)` instead of ~70 hand `fn2-successor-arg` calls.
- Nov 1: `fn2-successor-emit` (`:child fn2-succ-emit-children`, `books/machines-c-bind.lisp`), the one-encoding
  workspace emitter the txn's `:ready` passes to B.
- Earlier: C1a .. C-S4 (runs, Ribbon filters per run, ordered schemas, range reads, folds with summary keystones,
  every transaction write through its batch's successor, served reads for cursor rows), the sealer 429702ef1, the
  published frontier 93ede3b02, the §4a identity records with the two-lookup decision 0022ac2f8, E's
  `fn2-consumer-names` and `fn2-successor-stream-member`.

## What serves
Every reader verb on H's line reads C (GROUP .. NEWNEWS, HDR/XHDR, OVER, the cursor's seeks); POST stages through
the successor; CHECK/IHAVE seek identity. 26 verbs, both carriers, 0 disagreements at 132ac2c62.

## Capacity (the fact that bounds sustained use)
Installed runs are one table of `:identity-runs` rows (default 64, `books/machines-c.lisp:51,91`) shared by every
schema; each frozen overlay seals into its own run; a POST writes 8-10 schemas, so 64 rows last six to eight
POSTs, then the install answers `:full` and the core stops `:sealer-full`. Each run's pages stay resident in 64
KiB slots, so that pool class runs out first. Nothing reclaims a row before C5.

## Owed, with the exact next step
1. **Minimal C5**: a sealer merge phase over at most eight live runs of one schema, size-tiered (doc §5). This is
   on the spine: sustained POST needs it.
2. **`:child` bodies** for `fn2-successor-put`, `-arg`, `-arg-octets`, `-arg-octets-late`, `-fill-octets`,
   `-resolve`, `-stage`, `-out`, `-bind`, `-release`, `fn2-identity-decide-start`, `-decide`, `fn2-group-lookup`
   (all `machines-c-bind.lisp` and neighbours; only `-applied`, `-emit`, `-stream-member` have one). Each is the
   `stobj-let` body over its children. Then the txn can be generated in `:children` mode.
3. **The sealer in the form**: `fn2-sealer-seal` and `fn2-sealer-idle` are `defmachine-callback`s
   (`books/machines-c-sealer-events.lisp:104,138`).
4. **`fn2-member-replay`**: B's hook (`books/commit.lisp:134`) waits for C's body: decode by kind, fill `:event`
   fields from the header, insert through `fn2-succ-bind-slot`.
5. A pool class for C's arenas at the concrete profile (48 x 64 KiB, or 4 KiB arenas plus 48 x 4 KiB slots) and
   `:identity-runs` 512 before helm's concrete run; the profile's owner decides.
6. §4a steps 3-4 (reads at a named view, the checker, the keystones as `defthm-owed` rows); C-SEAL-NO-ROW's dead
   `:no-row` branch; `fn2-xl-step` skipping runs on the summary filter.

## Seams
- To B: `fn2-run-layout-decode` and the record kinds (`*fn2-commit-txn-record-kinds*`).
- To D: the successor ops above; `fn2-identity-decide*`; the reads (`fn2-read-seek`, `-seek-step`, range reads).
- To E: `fn2-consumer-cursor`, `fn2-consumer-names`, `fn2-successor-published`, `fn2-successor-stream-member`.
