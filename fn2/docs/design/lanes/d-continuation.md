# fn2 layer D continuation (present state, rewritten whole; 2026-10-30 evening, the seventh Opus seat)

Seat: Opus, layer D. The seat WRITES the code; Codex only for bounded pieces with real signatures.
Brief `build/coordinator/briefs/FN2-LAYER-D-MACHINES-NNTP.md` over `FN2-SEAT-COMMON.md` (note its new
"Landing on a moved tip" rule: disjoint moves need only your own books + export, not a regate).
Layer doc `fn2/docs/d-machines-nntp.md` §14 (D4+D5).

## State
- **D4 2/n LANDED**: dev 57601292a (READY sent).
- **D5 1/n COMMITTED** on branch fn2/d4 at 6dbae203e (worktree `build/lanes/fn2/d4`, message
  `build/d-seat/d5/d5-1.msg`), on dev 03b4a2f41 (A5r 2/3). Whole-tree gate running on forge in
  `/build/lanes/d-as7` (`build/gate-full.sh`, PID file `build/gate.pid` = group leader; status in
  `build/gate.status`, `build/owed.status`). When green: regenerate `fn2/tests/surface/fn2_conn_interim.json`
  on forge (`tools/acl2 < fn2/tests/conn-interim-export.lsp | python3 fn2/tests/conn-interim-json.py`;
  POST's row stays: posting is not advertised), copy back OWED.md (+ q1-d-tally.lisp if it changed),
  amend (`git commit --amend -F build/d-seat/d5/d5-1.msg -- <paths>`), compare A4 (113), secrets,
  `git push origin fn2/d4:dev` (moved tip: disjoint → own books + export only; overlap → regate),
  READY to main (H reruns the oracle).
- Design as built: layer doc §14.8 "D5 1/n as built" (committed). Section book times on hbox
  (loaded): -d 47.8 s before the txn ops moved to -d-txn (now -d ≈ 33, -d-txn ≈ 22 expected);
  measure on forge from the gate.
- Dev trees: **hbox** `/tank/fn/lanes/fn2-d5` (tar copy of fn2/, tools/, acl2-projects; set
  `FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g-tls64k`; PID file `build/c1.pid`); REPL loop
  `sh build/d-seat/d5/repl.sh` (certified assembly-callbacks-c + the upload/txn macros redefined
  from the worktree + every D section; valid only while defmachine declarations match the certs).
  Trace probes `build/p4.lsp`..`p6.lsp` there. forge `/build/lanes/d5` is an obsolete scaffold
  tree this seat made (safe to delete).
- Pending small commit after D5 1/n (main): A5r's peer opt-in on fn2-conn (`(peer-family :u8)
  (peer-port :u16) (peer-w0..w3 :u32)` in :fields and the :admission :copy; dev f6485baea), re-read
  `fn2-conn-reader-only-interim` against a-pool-host-sim.md §4.1.1, and the WIRE control: a 501-and-
  close on an over-long unterminated line counts as that line's reply (1- and 7-octet delivery).
- Read and fine: C's :sealable (rank 23, pure wait, b43206a3d). For D7 4/n: S5's ledger grant pair
  needs the liveness theorem (ready implies grant-one names a row) with a control.

## Next
1. Land D5 1/n (above). 2. The A5r opt-in + WIRE control commit.
3. Seams to raise with main: B-S2 (real admission, member result), a wake source for `:full`.
4. D5 2/n (durable POST, posting advertised), D5 3/n (IHAVE/TAKETHIS), D7 4/n, D6.
5. When C sends the :sealable resources.lisp branch: read the diff (rank 23, pure wait).

## Pitfalls hit (this seat)
- `(mv :x (f fn2-core))` is illegal: bind fn2-core with let first (`build/d-seat/d5/mvfix.py`).
- Readers of another row after a disabled predicate need the snapshot check inline.
- After any core-changing call, re-check `fn2-txn-snapshot-read-code`/idp before reading rows.
- A machine kind's table defines K-PREPARE etc.: arm names must avoid K-<table op> names.
- A charge above the smallest kind cap needs the kind of the row proved after the run.
- The core's child init wfp lemma must hold without the recognizer hypothesis.
- forge-certify on hbox needs acl2-projects/ and FN_ACL2.
- Plus the previous seat's: running rows keep wait-reason :completion; tau on conn guards; split
  section books; forge-certify output is in build/certify-*.log; no drivers after a failed closure.
