# bp (BP-DESIGN, Fable) lanedump, branch lane/bp (base origin/integrate/20261004 @ec2c1b3da)

Status 2026-10-04 ~23:50: wound down on ember's word (Fable lanes stop, an
Opus continues). Design packet drafted; first slice's keystones STATED, not
admitted; no host change; no certify; no image; SCN-1110 not run.

## What landed on lane/bp (one commit)
- `planning/design/bp-2026-10-04.md`: the decision file. §1 rule today
  (loop table, every existing deadline, findings F1-F7), §2 decisions
  (what a round is; no sweep deadline; fairness as bounds; receive-round
  job for the whole-frame decode; receipt→release two ledgers + K5; S025 as
  contended-idle Busy termination; forward-round cursor slice; ION X10A/B
  source-done, native owed; SCN-1110 plan; signed R/Q = run), §3 slices,
  §5 keystone register, §6 advisory review NOT RUN, §7 DECISION = PROPOSED.
- `books/bp-forward-cursor.lisp` (UNHOOKED): fn-bpfc-scan/turn/run and the
  theorems K1 fn-bpfc-turn-advances-at-most-quantum, K3
  fn-bpfc-turn-after-a-yield-is-the-larger-turn, K2
  fn-bpfc-run-is-the-plan-choice with lemmas (scan-with-more-quantum-agrees,
  scan-covering-never-yields, scan-covering-is-the-plan-choice,
  run-is-one-large-turn). None admitted yet.
- `tests/acl2/bp-forward-cursor-tests.lisp` (UNHOOKED): five-row fixture,
  positive/removal/mutation teeth for K1-K3. Not run.
- PRF-1311 claimed (build/coordinator/id-claims.jsonl) for the family;
  not yet in planning/proofs.json.

## Why no REPL
Laptop pool refused the book (no usable certs for the BP closure, toolchain
bf681d75 vs cache fcedce7e, ~300 books); persvati refused on 33 misses
(nntp-auth closure) and both fn slots were held; hbox slot granted then
withdrawn at load 18.9. No session of mine is running anywhere.

## Exact continuation (for the Opus lane)
1. REPL (laptop once root's LAPTOP-WARM cache is warm, else hbox under
   swarm-build when load < 16): `python3 tools/proof_repl.py start bpfc
   books/bp-forward-cursor --host <box> --upto fn-bpfc-scan-advances-at-most-quantum`;
   expect the defuns and fn-bpfc-ordered-true-listp to admit; then send the
   theorems in order. Likely needs: nthcdr-of-nthcdr for K3 at the turn
   level; induction on rows for the scan lemmas with fn-bprt-outbound-choice,
   fn-bpnp-held-dest, fn-bpn-nth, fn-bpp-eidp, fn-bprt-nth disabled (as
   bp-node-forward-plan does); K2's run lemma by induction on fuel using K3
   + scan-with-more-quantum-agrees. A theorem that does not go through is a
   proof-owed item naming it (python3 planning/repair/repair.py), filed in
   the same push.
2. Remove the UNHOOKED lines, add both books to the Makefile ACL2_BOOKS
   after books/bp-node-forward-plan + its tests (tools/test_roots_check.py);
   `python3 tools/farm.py submit hbox books/bp-forward-cursor
   tests/acl2/bp-forward-cursor-tests --affected-by books/bp-forward-cursor`;
   `evidence_manifests.py add RUN`.
3. Host: host/native/bp-node.lisp `:forward` arm (line ~1177): keep a
   `forward-cursor` beside `outbox-after`; call
   `(fnn-core 'fn-bpfc-turn (or forward-cursor (fnn-core 'fn-bpfc-initial))
   held table busy +fnn-bpnode-forward-quantum+)` (64); `:entry` →
   fnn-bpnode-forward-start with (second answer), cursor := (third answer);
   `:yield` → cursor := (second answer), counts as pending for --once;
   `:drained` → cursor := nil. Leave fnn-bpnode-forward-contact (tick verb).
   Then `python3 tools/host_check.py --load`, `tools/harness_check.py
   --write-stubs` (assembler's rule), `tools/build_lists_check.py`.
4. Witness `tests/native_bp_forward_cursor_source.lisp` on the prefix-probe
   pattern (tests/native_bp_prefix_probe_source.lisp): count
   fn-bprt-outbound-choice calls per :forward turn on 2,000 rows, old 2,000
   vs new <= 64, same entry. Runner: tests/test_native_raw_scripts discovers it.
5. Spec row in specs/bp-path.md (new subsection "The forward round") per
   packet §2.7, saying fairness is not bounded and the position skip is a
   list walk until the held set is indexed.
6. READY to assembler af2c7accc6871ee99 (copy integrator a5616a62b81a6c9b5)
   with `| sha | world receipt | manifest | image | native run |`; ask for
   images developer,dtn-developer at that sha (batched); run
   `tools/hbox_native.sh --box hbox --image-set <sha> .
   tests.test_bp_node_native.NativeBpNodeTests.test_keepalive_peer_does_not_block_second_canonical_request`
   plus the three forward natives named in packet §2.7; file with
   evidence_store.py put; index line is the claim.
7. Advisory review of the packet (packet §6.1 says how), then §7 DECISION.
8. Slices 2-4 per packet §3.
