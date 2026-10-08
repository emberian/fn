# Owner carrier: the design, as it stands on dev 617a83910 (2026-10-08)

The owner's state is a set of ACL2 state globals the host reads and writes beside the one owner
value `fn-owner`. Each is a side channel: the books decide, the host holds the state the decision
reads, and nothing proves the two agree. The program (coordinator, 2026-10-08 13:40) moves them,
family by family, into the carried owner value; the gates are the lock checker and
`tools/owner_globals_check.py` (baseline `tools/owner_globals_baseline.json`). Item:
`planning/repair/items/OWNER-CARRIER-GLOBALS.json`. This file is the design of record for that
program and keeps the decisions of lane carrier2's packet (2026-10-04, `955d90257`, advisory-reviewed
by grok-4.7 and Kimi K2.7). It is rewritten whole, never appended. Sections 0 to 3 are the decided
shape; section 4 is the map of the 73 globals into families; sections 5 to 8 are the order, the
owned invariant, the writer census and the guard slice. Paths are relative to the repo root.

**The lean, in one line.** Carry state by accessor funnel first (section 3), make the stobj
`fn-owner-st` the physical form once, last (section 8, S6); do not make the owner invariant a stobj
type (ACL2 8.7 refuses it, section 6); remove the whole-state guard by the idiom change, per served
chain (section 8), not by a raw-dispatch row.

## 1. Present-state coordinates and the drift from the 10-04 packet

Measured on `617a83910` (origin/dev, 2026-10-08 07:09).

- `owner_globals_check` counts, in the loaded host: `host/owner-host.lisp` 68
  (baseline 66 after the one authorized raise, section 9), `host/history-root-host.lisp` 5 (together
  the 73 of section 4, families 1 to 13),
  `host/bp-native-app-host.lisp` 22, `host/native/bp-app.lisp` 15 (the same app names read by the
  native side), `host/native/*.lisp` 7 (admin 1, mux 2, owner 4 against a baseline of 3, pull-service
  1), `host/native-live-status-host.lisp` 1. Distinct names overlap across files; the families of
  section 4 are by name. It is red on dev: owner-host 68 > 66 (`fn-owner-reclaim-live`,
  `fn-owner-history-root-status` unadmitted) and `host/native/owner.lisp` 4 > 3.
- `fn-owner-retain-carry` is already carried: its accessor and writer live in
  `books/owner-retain-state.lisp` (`fn-owner-retain-carry`, `fn-owner-retain-carry-put`), outside the
  scanner's reach. That move is the precedent the baseline's 10-04 reason cites for five other names.
- Drift, packet claim against dev:
  1. The packet's S1 (`fn-sf-countersp`, the eight io steps off the `mbe`) is NOT on dev: it is
     `a10f9c6c7` on `origin/lane/carrier2`. `books/store-files.lisp` has no `fn-sf-countersp`;
     `fn-sf-start-frontier` (line 686) still carries `(mbe :logic (fn-sf-statep s) :exec t)`;
     `tests/acl2/store-files-counters-tests.lisp` does not exist on dev.
  2. `fn-owner-io` is `host/owner-host.lisp:1810` (packet: 1680) and its guard is still
     `(fn-sn-statep (fn-sbud-oc-store (fn-owner-ocfg state)))`.
  3. The nine owner `:raw-with` rows stand (`host/interfaces.lisp` lines 222 and 1835 to 2015);
     `planning/interfaces.json` `raw_dispatched` lists 15 names (9 owner, 6 `fn-hist$p-*`/`fn-hroot-*`),
     as the packet said. `A-OWNER-INVARIANT-CARRIED` stands in `specs/failures.md:44`; the
     `:incomplete` escape is at `host/owner-served-carried.lisp:94`.
  4. The owed list is about 365 `fn-` symbols from that line to the end of the file (packet: 338);
     the ledger carries 21 `PGO-OWED-*` items, all open (packet: 25 summing 332). The numbers are
     the shape, not the value; section 7 says how to regenerate them.
  5. `books/owner-carrier.lisp` (`fn-owner-st`: `fn-ost-ocfg`, `fn-ost-installedp`, `fn-ost-carry`),
     `tools/owner_carrier/{thread.py,sexp.py,snapshot.py,world.lisp}` exist unchanged in role. The
     packet's `writers.lisp` and `tests/owner_carrier_writers.lisp` were not on dev and are brought
     here with this lane (they have not been run since; section 7).
  6. Cited and present: `books/owner-retain-transitions.lisp`, `host/owner-retain-host.lisp`,
     `books/def-carried.lisp`, `tools/raw_dispatch_rule.py`, `tests/test_native_owner.py`,
     `books/owner-host-relation.lisp`, `books/owner-log-route.lisp`, `books/records-concrete*.lisp`,
     `planning/design/sf-statep-idiom-2026-10-03.md`, `planning/handoff-2026-10-03/cost-gate.md`,
     `books/crypto-attach.lisp`.
  7. The packet's framing was the guard (cost) and the stobj move. The global families are new
     here; the packet's census of globals was only `fn-owner` and `fn-owner-retain-carry`.

## 2. The exposure the packet measured (unchanged)

COST-GATE (image set `45e05c7fd`, guards on, 2 KiB POSTs): `fn-owner-io` costs 92 ms and 11.8 MB per
call at N=1000 articles, exponent 1.0; 99.9% is the counterpart evaluating the entry guard
`fn-sn-statep` of the live Store. The nine raw rows skip that walk under the trust marker
`A-OWNER-INVARIANT-CARRIED`; nothing proves the skipped guard holds at the call. The chain carries
`fn-sn-statep` only because of two `mbe` layers (`fn-sf-*` steps, `fn-rcon-sn-io`), so the guard
cannot be narrowed in place: the `mbe` obligation forces each caller's guard up to the host entry.
A trap: `fn-sf-shapep` is O(N) (its `fn-sfr-canonp`/`fn-sl-canonp` rebuild the snoc-list); a guard
is chosen by what the body needs, never by a predicate's name. Edit-site census: 54 sites of
`(mbe :logic (R s) :exec t)` in 19 books, six recognizers (`fn-sn-statep` 27, `fn-sf-statep` 17,
`fn-node-statep` 4, `fn-retain-statep` 3, `fn-cnode-statep` 2, `fn-exchange-statep` 1).

## 3. The decision: accessor funnel now, the stobj once, the idiom change for the guard

**Two moves, not one.** (A) The globals move into a carried owner value. (B) The guard walks leave
the entries. They are independent and were conflated by the 10-02 plan, which is why two attempts
(`lane/stage-5b-carrier@fa32ac06f`, dev's `fn-owner-st` book) produced no landed migration: a
global-to-stobj move is atomic (every reader of `'fn-owner` switches in one commit or the owner has
two authorities), touches 277 functions, and does not shrink the proof debt, it makes the writer
list exact.

**Move A, per family, by accessor funnel.** For each family (section 4):

1. A books file `books/owner-<family>-state.lisp` defines the family's record (a structural,
   attachment-free recognizer; fields untyped or naturals), its initial value, and the PURE
   transitions the host's wrappers currently compute with `f-put-global` in between calls to the
   books' decisions. Each transition is `(new-record, outputs) = f(record, inputs)`.
2. The slot is read and written through one accessor pair in that file, with the signature the stobj
   field will have (`(fn-ost-<family> st)` / `(fn-ost-install-<family> v st)`; today bodies over
   `state`, in the style of `books/owner-retain-state.lisp`). The host names no
   `fn-owner-<family>-*` global; it calls the transition and installs the result.
3. Teeth, per family: a theorem that the composed transition equals the current host composition
   (the decision outputs are the books' existing `fn-ock-*`, `fn-opl-*`, ... values, unchanged), a
   frame theorem (no other global moves), the recovery-reset equation (what `fn-owner-install-extended`
   in `books/owner-recovery-retain.lisp` writes today), and a wrong-answer witness (a stale record
   yields the refusal, not the success).
4. The family's host globals leave the baseline in the same commit (`--write-baseline`, shrink only).

**Move B (S6, once).** When the last family is funnelled, thread the accessors over `fn-owner-st`
with dev's `tools/owner_carrier/thread.py` on then-current dev, in one commit, never rebased: every
funnel body changes from a global read to a stobj field read, the host call sites do not change.
`lane/stage-5b-carrier` is retired as an input (its `xf.py` rewrote hint pairs wrongly; its
`sigs2.txt` is from a world 1,058 commits behind).

**Open decision for the coordinator (q0).** The scanner counts only `host/`. A funnel that keeps one
`f-put-global` in `books/` drops the host count to 0 without removing the global (as `retain-carry`
did). Either the item's exit is met at Move A (the books own the transitions and the relation, the
host holds nothing), or the check also counts the funnel files, so the global count reaches 0 only
at Move B. This design recommends the second: add `books/owner-*-state.lisp` to the scan with
their own baseline rows, which the funnels enter and S6 empties. Until decided, funnels are
written so either holds.

## 4. Families: the 73 globals of owner-host and history-root-host, and the bp-app channel

The table is by name. "Consumes" is the host function that reads or writes the family and the
books functions it passes the values to (`f-get-global`/`f-put-global` grep of `host/`). R and W are
read and write. Counts sum to 68 in `host/owner-host.lisp`; history-root adds 5 in its own file;
row 14 is the cross-file bp-app channel.

| # | family (globals; count) | consumed by (host function: books functions) | becomes |
|---|---|---|---|
| 1 | catalog-root (`catalog-root-counter`, `catalog-root-incarnation`; 2) | `fn-owner-catalog-root-reserve` RW, `-current` R: `fn-cri-reserve`, `fn-cri-tokenp` (`books/catalog-root-incarnation.lisp`); `fn-owner-catalog-capture-context`; native `host/native/owner.lisp:1532,8231` | slot `catalog-root` = (counter, incarnation); NOT reset by recovery install (never reset by open, reclaim or a failed publication) |
| 2 | publication-capture (`sco-attempted`, `sco-base`, `sco-base-payloads`, `sco-deferred`, `sco-durable`, `sco-inflight`, `sco-pending`, `sco-requested`, `sco-serial`, `orc-pass`; 10) | `fn-owner-sco-due`, `-request`, `-capture`, `-note-durable`, `-note-base-payloads`, `-publication-done`, `-publication-abandoned`, `fn-owner-orc-request`, `-orc-capture`, `-orc-finish`, `fn-owner-orcp-capture`: `fn-ock-requested-next`, `fn-ock-request-word`, `fn-ock-capture-budget`, `fn-ockp-space`, `fn-opl-attempted`, `-blockedp`, `-next-serial`, `-settle`, `-holdsp`, `fn-orc-release-slot`, `fn-orc-capture-slot`, `fn-scka-strip-base`, `fn-sco-sequence` (`books/owner-checkpoint-open.lisp`, `owner-publication-lifecycle.lisp`, `owner-reclaim*.lisp`); reset in `fn-owner-install-extended`; `fn-owner-sco-global` / `fn-owner-sco-deferred` already in `books/owner-state-accessors.lisp` | slot `publication` = a 10-field record; reset by install except none persists |
| 3 | authority publication (`account-carries`, `account-root-state`, `canonical-state`; 3) | `fn-owner-authority-publication-install` RW: `fn-cp-nth`, `fn-sn-consumer`; `books/consumer-account-carries-state.lisp`, `consumer-account-state.lisp`, `owner-canonical-state.lisp`, `owner-canonical-read-state.lisp` | slot `authority` = (account-carries, root-state, canonical) |
| 4 | reader views (`reader-views`, `access-cache`; 2) | `fn-owner-reader-views-capture` W: `fn-ocv-capture`, `fn-ocfg-at-reader-view`; `fn-owner-chunk-span-install-result` W/`fn-owner-access-cache` R: `fn-own-tls-result-*`, `fn-splan-step-make` (`books/owner-connection-state.lisp`) | slot `readers` |
| 5 | feed (`feed-inputs`, `feed-intents`, `feed-pending`, `feed-safe-offset`, `feed-stopped`; 5) | `fn-owner-feed-configure`, `-dial-open`, `-lost`, `-tls-established`, `-reply-article`, `-reply-chunk-synced`, `-install-port-result`, `-replay-counted`, `-journal-begin/-scan/-offset`, `-reconcile-*`: `fn-own-feed-*`, `fn-fc-*`, `fn-feed-journal-*`, `fn-ores-feed-port-publication` (`books/owner-recovery-retain.lisp` reset) | slot `feed`; `feed-inputs` is socket-only (rebuilt at recovery) |
| 6 | admission (`connection-held`, `handshakes`, `credit-reserve`, `credit-taken`, `article-slots`, `reclaim-live`; 6) | `fn-owner-connection-budget` W, `-connection-held-refresh`, `fn-owner-handshake-admit/-done/-leave/-state`, `fn-owner-proxy-handover`, `fn-owner-take` W (credit-taken), `fn-owner-shed-outcome` R: `fn-cbud-*`, `fn-hsb-*`, `fn-pxy-*`, `fn-exp-connections-capacity`, `fn-mca-*`; `reclaim-live` also read by `fn-owner-reclaim-live-p` and native control (lane control-receipt's area) | slot `admission`; `reclaim-live` waits for control-receipt |
| 7 | config carries (`auth`, `store-profile`, `profile-carry`, `limit-carry`, `carried-usage`, `record-debt`, `record-octets`; 7) | `fn-owner-set-auth(-config)`: `fn-auth-make-config`; `fn-owner-install-profile`, `-apply-limit-profile`, `-limit-decided`, `-record-debt`, `-record-octets`: `fn-osb-install`, `fn-pvc-make`, `fn-lim-carry-after`, `-funded`, `fn-cvec-record-debt`, `fn-pcb-tally-records` (`books/store-profile-carried.lisp`, `owner-recovery-retain.lisp`); native-live-status reads `record-octets` | slot `config` |
| 8 | take and submission carries (`take-config`, `parse-carry`, `plan-carry`, `submit-intent`, `shared-resolution-id`, `identity-grant`, `incoming-context`, `cat-candidate`, `cat-pending`; 9) | `fn-owner-take` W, `-plans-for`, `-incoming-context-register`, `-submission-intent`, `-submission-resolution`, `-identity-reservation`, `-prepare-retention`, `-prepare-buffer`, `-cat-prepare-sealed-produced`, `-finish-identity`, `-finish-submission-synced`, `-orcp-swap-word`: `fn-apc-take`, `-plans-extend`, `-icar-carry-of`, `-submission-intent`, `fn-idr-*`, `fn-cat-prepare-sealed`, `fn-sca-finish` (`books/owner-parse-carried.lisp`, `owner-incoming-context.lisp`, `owner-retain-transitions.lisp`, `owner-post-carried.lisp`) | slot `takes`; with `fn-owner-retain-carry` these form the retention slot the stobj's `fn-ost-carry` already names |
| 9 | exposure table (`exposure`, `exposure-public`, `exposure-close`; 3) | `fn-owner-exposure-open/-charge/-idle/-progress/-release/-install-set`: `fn-exp-*` (`books/owner-connection-state.lisp`, `-callbacks`, `-callback-refinement`) | slot `exposure` |
| 10 | open-result channel (`closep`, `starttlsp`, `submittedp`, `effects`; 4) | written by `fn-owner-exposure-open` after `fn-exp-open-state`, `fn-exp-open-effects`, `fn-served-closingp`; read by native `fnn-owner-*` after the call | NOT a slot: the wrapper's own result (extra `mv` values) |
| 11 | decision-result channel, transit (`transit-article-subject`, `-authority`, `-budget`, `-bytes-subject`, `-carried`, `-evidence`, `-groups`, `-kind`, `-payload`, `-reason`; 10) | all written by `fn-owner-transit-decide` after `fn-peer-decision-kind`, `-reason`, `fn-peer-evidence`, `fn-own-sub-decision`, `fn-pa-peer-carried-sources`, `fn-pcb-peer-budget`, `fn-asj-subject`; read by `fn-owner-transit-log-line`, `-evidence`, `-kind`, `-reason`, `fn-owner-peer-carried-relay-event`, native `fnn-owner-transit-groups` | NOT a slot: the decision's result record (the host never re-reads it across calls) |
| 12 | reply/log channel (`output`, `log-line`, `login-log-line`, `control-reason`, `app-refusal-reason`, `connection-budget-line`; 6 in owner-host; also read in 5 native files) | `fn-owner-exposure-open`, `-shed-outcome`, `-outcome`, `-control-outcome`, `-log-reopen`, `-operator-submit`, `-login-gate-buffer`, `-connection-budget`, `-retire-intake-refused`: `fn-olog-*`, `fn-ocpr-*`, `fn-otm-shed-reply`, `fn-olr-*` | NOT a slot: the wrapper's result (reply and log line are values) |
| 13 | history root (`history-root-counter`, `-current`, `-lease-counter`, `-roots`, `history-source-counter` in `host/history-root-host.lisp`; `history-root-status` in owner-host; 6) | `fn-owner-hroot-begin/-pin/-put/-get/-activate/-detach/-current/-frontier`: `fn-hroot-begin-ledger`, `-begin-word`, `fn-mcr-resize`, `fn-hist-count`, `fn-host-hist-sync`; `fn-owner-hroot-note`: `fn-hroot-refresh-status`; `books/history-capture-state.lisp` | slot `history-roots`; `status` is being removed by lane S, and MEM-013's live-root work is in flight there |
| 14 | bp-app plan channel (`app-*` 21 names and `log-line`; 22 in `host/bp-native-app-host.lisp`, 15 read by `host/native/bp-app.lisp`) | `fn-owner-app-plan` W, `-plan-install` W, `-plan-answer`, `-plan-deferred`, `-submit-synced`, `-record`: `fn-bpaj-plan-matches-intentp`, `fn-bpaj-transit-plan-under`, `fn-bpaj-request*`, `fn-bpaj-dispatch-fast`; native `fnn-bpapp-accept-locked`, `-bind-context`, `-request-intent` | NOT a slot: the plan is one returned value |

Classification, the point of the table. Slots (1 to 9, 13) are state that persists across calls and
that one ACL2 decision reads together with others; they become fields of the carried owner value
(Move A funnels, Move B stobj fields). Channels (10, 11, 12, 14) are values a wrapper hands the
caller through a global because the signature has no room; they are not state, they never need a
slot, and the transformation is to return them (`(mv erp value state)` grows the extra values, or
a result record), which changes every caller and so lands per channel with the native readers
(`host/native/*.lisp`) in the same commit. The scanner counts both alike; the channels' removal is
purely mechanical and carries no new invariant, which makes them cheap in proof and wide in edit
surface.

## 5. Order, smallest risk first

1. **Catalog-root (2 names).** The pilot: one function pair, books already hold the decisions
   (`fn-cri-reserve` with three theorems), one cross-recovery requirement. Proves the funnel
   pattern and the teeth shape on the smallest case.
2. **Publication-capture (10).** Retires the one authorized raise (`fn-owner-sco-serial`). The
   decisions are already pure in the books (`fn-ock-*`, `fn-opl-*`); only the state shuttling is
   host. `orc-pass` shares the slot-release equation with `sco-inflight` (`fn-orc-release-slot`).
3. **Authority publication (3), reader views (2), exposure table (3).** Each written by one
   installer; relations in books already (`owner-connection-state.lisp`, `consumer-account-state.lisp`).
4. **Feed (5), admission (6 less `reclaim-live`), config carries (7).** Wider fan-out;
   admission's `reclaim-live` waits for lane control-receipt.
5. **Take and submission carries (9).** Touches the served POST path and joins the retention slot;
   done after the pattern is routine and with the host-path tests.
6. **Channels 11, 12, 14, 10.** One at a time with their native readers; the result-return
   convention is set once (a record per decision) by the first.
7. **History root (6).** Last: lane S is mid-change on `history-root-status` and MEM-013's live
   root.
8. **S6 (Move B)**, then S4 and S5 of section 8.

Every family commit must: leave `timeout 300 python3 tools/owner_globals_check.py` no worse, lower
the baseline for the names it retired, certify the changed books with `farm.py submit <box>
--lane --affected-by <book>`, run `lock_discipline_check` and `host_check --load`, and carry its
teeth (section 3, item 3).

## 6. The owned invariant, as a carried field (decided; unchanged)

The invariant is not a stobj type and cannot be (ACL2 8.7: `chk-defstobj-attachments` at
`~/tools/acl2-fn/acl2-8.7/other-events.lisp:20938` refuses a recognizer that depends on an attached
function; `chk-defabsstobj-attachments` (24504) refuses it for `defabsstobj`. `fn-digest` is
attached, `books/crypto-attach.lisp:75`, and `fn-lgoc-invariantp` reaches it through
`fn-cst-relation`.) The workaround both carriers use, and the one `def-carried` exists for:

- fields untyped (`:initially nil`); the physical recognizer (`fn-owner-stp`) structural and
  attachment-free;
- the semantic relation a plain `:logic` predicate over the carrier, never executed on a served path
  (`fn-owner-retain-statep` over `state` today (`books/owner-retain-transitions.lisp`); when the
  stobj lands `fn-ost-retainp` :=
  `(and (fn-ost-installedp st) (fn-lgoc-invariantp (fn-ost-ocfg st)) (fn-prc-carryp (fn-ost-carry st)))`);
- carried by theorem through `def-carried`: `:established` at the recovery install (`:ok :recovering`,
  under A-RECOVERED-OPEN), `NAME-FN-carries` per writer, `:concludes` bridges to each entry guard's
  carried heads;
- completeness over the exact writer set: `stobjs-out` once the stobj exists, the installer closure
  before (section 7).

Every family slot of section 4 adds to this relation a conjunct that is structural (its recognizer)
and, where the family has a semantic invariant (catalog-root: counter is a natural and the
incarnation token names a counter below it; publication: `fn-opl-holdsp` coherence of inflight, pass
and serial), a carried one. Alternatives recorded for the Store's own stobj (ST2/ST3): an
attachment-free reference digest with an equality theorem; a `:corr-fn` absstobj whose exports may
call `fn-digest`; removing the attachment. `fn-sn-statep` splits as the index does under D21:
shape in the recognizer, digest and replay agreement carried by theorem. Record that in
`specs/owner.md` before ST2.

## 7. The writer census (decided; run it before any deletion)

F is a writer of the owner's globals iff its closure (bodies, guards and attachments, `:logic` and
`:program`) reaches: (1) `put-global` or `makunbound-global` with key `'fn-owner` or
`'fn-owner-retain-carry`, or a non-literal key; (2) an evaluator over a computed form or function
(`trans-eval` family, `ev-fncall` family, `magic-ev-fncall`, `ld`; `apply$` and `ev$` excluded:
badged functions cannot take `state`); (3) `return-last` whose first argument is not a built-in key
(raw code under a ttag); (4) a function with no `unnormalized-body` that is neither a primitive nor
constrained without an attachment. `tools/owner_carrier/writers.lisp` implements it over
`world.lisp`'s `fn-ocw-*` closure, with teeth in `tests/owner_carrier_writers.lisp` (one synthetic
function per route, a reader and an unrelated put that must stay clear, a cycle, an attachment).
**Both files are unrun on dev.** The census must be extended to the family globals: the writer
globals constant `*fn-ocw-writer-globals*` becomes every family's global, so a function that reaches
only `fn-owner-sco-*` is a writer of the sco slot and of nothing else. Run in the image world, file
with the image set's sha (`evidence_store.py put`).

Disposition of the owed writers (the packet's, to be regenerated): host-called state-returning
functions not in the installer closure (about 297 of 338 then) are deleted from the owed list with
their `PGO-OWED-*` rows closed `refuted: not a writer`; host-called compliant writers get the
preservation theorem `(implies (fn-owner-retain-statep state) (fn-owner-retain-statep RET))` by the
tier-A pattern (`host/owner-retain-host.lisp`); `:program` writers stay proof-owed by name until
program-to-logic. `def-carried` then declares completeness by closure (`:writers (:closure ...)`),
refuses a `:program` writer by name, and `A-OWNER-INVARIANT-CARRIED` is deleted. The family funnels
make this census sharper: each slot's writer set is the funnel's installer closure.

## 8. The guard slice and the migration steps (the packet's S1 to S6, with status)

| step | what | status on dev |
|---|---|---|
| S1 | `fn-owner-io` off the whole-state guard: `fn-sf-countersp s := (and (natp (fn-sf-frontier s)) (natp (fn-sf-barriers s)))`; the eight io steps unconditional with that guard and the `mbe` deleted; `fn-sn-io`, `fn-sn-file-step`, `fn-rcon-sn-io`, `fn-rcon-sn-file-step`, `fn-rcon-sf-record-dir-result`, `fn-rcon-own-store-io`, `fn-rcon-ocfg-io`, `fn-olr-ocfg-reserve/-order` weakened to it in lockstep; `fn-owner-io`'s guard loses `fn-sn-statep`; the served row's `:concludes` gains `fn-owner-retain-statep-implies-io-guard` | on `origin/lane/carrier2@a10f9c6c7`, not merged; certify evidence is in that lane's dump |
| S2 | take, prepare, refuse, known-abort chains | not started |
| S3 | finish and recovery chains | not started |
| S4 | delete the nine owner `:raw-with` rows, `A-OWNER-INVARIANT-CARRIED`, the `:incomplete` escape; `RAW_OWNER_ENTRIES` 7 to 0 in `tests/test_native_owner.py` | needs RAW-DISPATCH's exit |
| S5 | `def-carried` completeness by closure, owed-writer disposition (section 7) | needs the census run |
| S6 | Move B: the stobj, once, with `thread.py` | after the last family funnel |

S1's props (each with satisfiable, teeth, premise-inhabited): P1 `fn-sf-countersp` and
`fn-sf-statep-implies-countersp` (non-vacuous witness `(fn-sf-make :ready 0 nil 'junk nil nil nil 5)`
satisfies the head and fails `fn-sf-statep`); P2 the changed guards; P3 the existing statements
re-proved unchanged (`fn-sf-<step>-preserves-state`, `fn-sn-io-cannot-acknowledge`, the unconditional
`-is-` twin theorems, `fn-owner-io-preserves-retain-state` at `host/owner-retain-host.lisp`, its teeth
`fn-owner-io-refuses-an-unsafe-observation`); P4 `fn-owner-retain-statep-implies-io-guard`. Reviewed
findings that changed the plan (all folded into `a10f9c6c7`): the `mbe` deletion is lockstep on both
twin sides; a preservation lemma `fn-sf-io-steps-keep-countersp` is needed because the frontier
directory result installs the candidate as the frontier; between S1 and S4 the row still skips an
O(1) conjunct and the dispatch debt is unchanged (the safety gain, a faithful computation on an
off-invariant state, holds after S4 only); the writer criterion is conservative (section 7). The
off-invariant identity is used by exactly three local lemmas, none on the io path
(`fn-si-prepare-off-state-is-identity`, `fn-hma-finish-outside-the-state-is-a-stutter`,
`books/store-observed.lisp:217`). Collision rule: S1 does not touch `host/interfaces.lisp`,
`books/definterface.lisp`, `books/def-carried.lisp` or `tests/test_native_owner.py`.

What the lean does not claim: (B) does not make O(1) an entry whose body walks the store; such a
chain (e.g. `fn-sf-prepare-record` through `fn-sf-history-recoverablep`) is a representation item for
the ST-stages, named when found.

What would change the lean: a keystone (not a local lemma) found to use the off-invariant identity
is restated under its hypothesis, or the slice stops and escalates; if the generator owner refuses
completeness-by-closure as unsound the escape stays for exactly the named route.

## 9. The ratchet raise (2026-10-08)

`fn-owner-sco-serial` (RL-02, `431bb1981`) is the one authorized raise: `host/owner-host.lisp` 65
to 66 (coordinator option (a), 13:40), recorded in the baseline's `_reasons`, with the ACKS line
`ratchet:owner_globals_check:host/owner-host.lisp`. It was made with the tool's new
`--raise-to FILE=N --admit NAME`, which raises one row by exactly the named globals, refuses a count
above what is present, and leaves every other row as stored. It moves with the publication-capture
family (row 2) and the raise retires with it. `fn-owner-reclaim-live` (lane control-receipt) and
`fn-owner-history-root-status` (lane S removes it) are not admitted; the check stays red on them.

## 10. Open

- (q0) where the scanner stops counting a funnel (section 3).
- (q1) the generator owner's view of completeness-by-closure.
- (q2) `fn-sn-shapep`/`fn-sf-shapep` O(N), left to the ST-stages.
- (q3) the native counterpart-arm POST figure after S1 needs the integrator's batch image
  (`FN_NATIVE_DISPATCH_COUNTERPART=1`; the script the packet named, measure_post.py, is not on dev).
- (q4) exact owed-writer counts need the section 7 census in a current image world.
- (q5) `host/native/owner.lisp` is 4 over a baseline of 3 on dev, not caused by this program.
