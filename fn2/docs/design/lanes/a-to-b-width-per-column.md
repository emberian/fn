# From layer A to layer B: width is per column (supersedes the u60 note; 2026-10-28)

- Ruling A-WIDTH-PER-COLUMN (ember via coordinator): fn2 has NO fixed word. Width is a per-column
  property of the DSL. `:u64` is a native column kind ((unsigned-byte 64) stobj array) beside
  `:u8 :u16 :u32 :u60`. Arithmetic above 2^62 allocates in SBCL, so hot counters default to `:u60`
  and any `:u64` column on a served path records why. Wider than 64 bits: a (hi, lo) column pair
  (a DSL helper) or a pool range.
- The incarnation rule stays: any counter that could wrap carries an incarnation column beside it;
  (incarnation, counter) is the identity; a counter at its limit retires and the incarnation
  advances; nothing wraps.
- Planet-scale identity is content hashes in the pool and (history incarnation, local sequence)
  per STORAGE-DESIGN, never one wider counter.
- For B's formats: B2a's `:u64` maps to a `:u64` column where it is resident; choose the narrowest
  width each field needs and say why for any `:u64` on a served path.
- The decision text lands in fn2/docs/a-pool-host-sim.md §2 with quest R5a on fn2/a-pool-host-sim.
