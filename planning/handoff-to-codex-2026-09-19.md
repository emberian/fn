# Handoff to the Codex root, 2026-09-19 ~02:50

Status: **in-flight wave, handed over mid-certification** because the Claude
session's weekly usage ran out. Nothing below is integrated into `dev` yet.
Read in this order: this file, `AGENTS.md` (the "Assurance rules" section is
new and binding), `planning/review-2026-09-18-independent.md` (the audit that
every lane is executing), then each lane's `LANEDUMP-<name>.md`.

## What happened since `a5a30d8`

| Commit | Content |
| --- | --- |
| `b12a18e` | Independent adversarial review: 14 concrete defects, 20 ledger overclaims, 6 Python/ACL2 twins, 7 structural naiveties, blocklace correspondence with dregg/minidregg, re-sequenced C1. Full `make certify` at HEAD passed all 113 roots. |
| `0bd0b5c` | AGENTS.md assurance rules (twelve, each tied to a review finding); `docs/prefixes.md`. **Base of every lane branch.** |

## The ten lanes

Each lane is a git worktree at `/Users/ember/dev/fn/build/lanes/<name>` on
branch `lane/<name>`, branched from `0bd0b5c`. Each was ordered to write
`LANEDUMP-<name>.md` at its worktree root and to make a WIP commit of all its
owned files before stopping. If a LANEDUMP is missing, the lane was cut off
before it could write it; its dirty files are still in the worktree and its
`HANDOFF.md` (if present) is the next best source.

| Lane | Model | Packet (review §8) | State at handoff |
| --- | --- | --- | --- |
| host-repair | opus | D1 D2 D11 D12 D13 D14 + small items; exit codes; F_FULLFSYNC | 3 commits, all items done, full Python suite green (173 tests), HANDOFF.md written, certification re-running detached |
| nntp-served-path | opus | D3 (503-everything DoS), real effect typing, cursor invariant | 9 dirty files, mid-certification |
| twins-into-acl2 | opus | frame.lisp/identity.lisp; Python framing/identity/msgid/groups/charge become bridge calls | 17 dirty files incl. new books and tools/frame_bridge.py, HANDOFF.md written |
| crash-fidelity | fable | D4 crash points, D5 ghost successes, D6 open-observed ⇒ snt-relation | 21 dirty files, mid-certification of the rewritten store chain |
| sender-proofs | fable | D7 replay-interpreter theorems, D8 durable-intent theorem, F11; specs/bp-evolving-store.md | 2 commits; first three roots certified incl. D8 keystone; HANDOFF.md written |
| substrate | fable | crypto-seam, principal, statement, lace, policy books (blocklace shape from dregg); decision packet D09/D11 | 22 dirty files (new books), HANDOFF.md written |
| assurance-tooling | opus | books/assumptions.lisp, tools/ledger.py, teeth books, proofs.json events regenerated | 2 commits, HANDOFF.md written |
| hygiene | sonnet | index X⊆X fix, checkpoint guards, prose overclaims, now.md split, evidence-index, swarm-cycles roles | 18 dirty files, final certification running |
| bp-primary-time | opus | rfc9171/9172/9173, bp-primary*, bp-fragment*, clock*, specs | 2 commits, HANDOFF.md written |
| wire-article-transfer | opus | wire O(B²) fix + fn-wire-next partition theorem, article fields correspondence, transfer overlap | 14 dirty files, mid-certification |

## Convergence plan (not yet executed)

1. For each lane: read LANEDUMP, then `cd build/lanes/<name>` and run
   `FN_ACL2_TIMEOUT_SECONDS=1800 make certify` and `make check` (plus the
   lane's named Python tests) to get a green gate. Serialize these; ten at
   once oversubscribes the box (load 24 on 12 cores) and each takes over an
   hour under contention versus 26 minutes idle.
2. Merge into `dev` in this order, `make check` after each:
   additive lanes first (substrate, bp-primary-time, assurance-tooling), then
   base-book lanes (crash-fidelity, wire-article-transfer, sender-proofs,
   nntp-served-path), then the two host lanes that share files
   (twins-into-acl2, then host-repair; both edit `tools/run_store.py` and
   `tools/workflow_journal.py` in different functions; `specs/store-experiment.md`
   has hunks from both, see host-repair's HANDOFF), then hygiene last (prose
   everywhere).
3. On the merged tree: one full `make certify`, the full Python suite
   (`python3 -m unittest discover -s tests -p 'test_*.py'`), `make check`
   (now includes `tools/ledger.py --check` from assurance-tooling), and
   `python3 tools/ledger.py` to regenerate `planning/ledger.md`.
4. Write `tests/evidence/2026-09-19-wave1.md` + `.json` with fresh digests
   (old evidence records are frozen snapshots; six tool sources changed in
   host-repair, do not edit old records).
5. Remove worktrees (`git worktree remove build/lanes/<name>`), keep branches.

A draft of wave 2 (evolving-Store receiver, policy-term adoption into
FNWF/FNRJ, bundle identity in the adapter, mutable owner + clock, POST,
per-principal resources, BP guard closure, native envelope, relay undertaking,
generated fault campaign) is in the Claude session notes; the same list is the
review's §8 rows 8 to 14 plus C2-01/C2-07.

## Operational traps (each cost a lane an hour or more)

- `tools/certify_books.py` defaults to 600 s per book; `books/article-properties`
  exceeds it under contention. Always `FN_ACL2_TIMEOUT_SECONDS=1800`.
- Long certifications were repeatedly SIGTERM'd mid-run (at 20, 76, 84, 85 of
  113 roots). A detached run died too, and one lane admitted running
  `pkill -f` on an ACL2 pattern, so the likely cause is cross-lane friendly
  fire. **Never `pkill -f`, `killall sbcl` or any pattern kill on this shared
  box; kill only PIDs you started.** Also prefer the harness's background
  mechanism over a bare `&`.
- ACL2 certificates are not relocatable: copying `.cert` files into a worktree
  yields "Uncertified" warnings. Each worktree certifies its own closure.
- Never `find /` or search under `build/` (a gigabyte of old lane copies; it
  also trips macOS TCC prompts for the terminal).
- Never `git stash`; never `git add -A`; commit named files; `git commit -F`.

## Who did what

Terra, Sol, Luna and Astra in the planning docs are the 2026-09-18 Codex
roles (`gpt-5.6-terra/sol/luna`, and the Codex root). The review and wave 1
were run by a Claude Fable 5.1 root with Opus, Sonnet and Fable lanes. Model
names are workload allocations, not correctness claims; every lane's evidence
is its own gate.
