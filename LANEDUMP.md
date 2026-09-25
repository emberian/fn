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
- r1 run-20260925T100702Z-292c (certify-20260925T100724Z-3668605): buffer lemma failed; fixed.
- D32 join fix: lane/reclaim-d32fix 0915bac2 (+ manifest 50f1340e), persvati
  run-20260925T183420Z-c5c7, certify-20260925T183440Z-4046016, passed
  (store-reclaim 8.0 s, store-reclaim-tests 2.4 s). Merged by the deputy (f20ea7ae).
- r2 run-20260925T103332Z-559f (certify-20260925T103408Z-3975153): four proof
  failures (indexed-lines correspondence, std/lists books not certified on
  persvati, holders keystone, a stobj call in a test); all fixed.
- r3 run-20260925T183827Z-4dd7 (certify-20260925T183859Z-4091844), after merging
  dev: 265 roots; every book this lane changed PASSES (nntp-responses,
  nntp-range-indexed(+invariants, tests), nntp-newnews(+tests), nntp-reclaimed,
  store-reclaim-tests 3.4 s, native-live-status 6.5 s (+tests 5.1 s),
  store-reclaim-holders 2.0 s) EXCEPT the buffer family: poster-bytes-buffer
  fails on dev for D32 (pbb-d32 lane owns it), so store-reclaim-buffer,
  its tests and octets-stobj-tests fail behind it. store-reclaim-buffer must be
  re-stated over the D32 fn-pbb-path-agent once pbb-d32 lands.
  Over 10 s in r3: owner-invariants 16.7 s (known, see reclaim-d13), and
  config-owner-live, native-admin, native-admin-peer, provenance-owner at 10.4-11.0 s
  on a shared box.
- r4-r6 (holders tests only, decoupled from the buffer tests): the keystone
  witness and all three must-fail teeth pass; the COUNT witness
  `(fn-rcl-store-counts rule 0 caught)` fails (certify-20260925T185623Z-65311).
  Likely cause: the counts pass the store's own verdict list (fn-sn-verdicts),
  and the owner fixture's article probably carries an authorship verdict
  (:verdict-needs-payload), which the per-article witness (verdicts nil) does not
  see. Not established; next step: evaluate the verdict list in a REPL and
  state the witness over it. Stopped at the run budget instead of a blind 7th run.
