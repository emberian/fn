# LANEDUMP reclaim-host (Claude Opus 5.5)

Branch lane/reclaim-host from dev ac70f38d. PRF-088, STO-014, SCN-048.
Record: planning/evidence/reclaim-host-2026-09-25.md.

## Done
1. D25 switch: all SIX host sites (four list sites -> fn-rcl-existing-action;
   two BUFFER sites in host/owner-host.lisp, the native owner's hot path ->
   new fn-rclb-existing-action, books/store-reclaim-buffer.lisp, keystone
   fn-rclb-existing-action-is-rcl-existing-action). Native images include it.
3. status line `reclaim rule=R reclaimable= reclaimable-octets= held= reclaimed=
   freed-octets=` (books/native-live-status.lisp fn-nls-reclaim-words; clock =
   4th element of the open observation, host/native/io.lisp).
4. OVER msgid 430 / current 423 "article reclaimed", ranges skip tombstones,
   NEWNEWS lists only live (books/nntp-reclaimed.lisp keystones).
   fn-nntp-newnews-without-payload now keeps tombstones (contract change, stated).
5. (part) holders from the consumer projection, conservative
   (books/store-reclaim-holders.lisp, fn-rcl-store-holders-hold-behind-a-lagging-consumer).

## Not done
2. `store reclaim` byte program + `--dry-run`: K0 cannot express replacing a
   committed transaction (see record section 2; recommend design B, reclaim
   through the compaction pack). Model decision needed before any bytes.
5. precise consumer reading, feed state, FNBS, charge release.
6. hbox native run (nothing to run without the verb).

## Findings
- reader pins: offline reclaim needs no durable pin.
- tombstone-shaped submissions from peers: unverified whether refused.
- inherited make-check errors fixed: STO-014 spec anchor line, statuses.

## Certification
- r1 run-20260925T100702Z-292c (manifest certify-20260925T100724Z-3668605):
  store-reclaim-buffer failed (one lemma), fixed in REPL.
- r2 run-20260925T103332Z-559f: running.
