# ARENA-FORGET design note, 2026-10-03 (lane/arena-forget, Opus 5.5)

**REVISED after Astra's c05 (section 8 below supersedes sections 2, 4(a) and 7 where they differ).**

For the coordinator's Codex consultation. Paths are relative to the lane worktree
`/Users/ember/dev/fn/build/lanes/arena-forget` (base origin/dev 4aa332295).

## 0. The measurement and what it reduces to

`RECLAIM installed records=5 reclaimed=2 dropped=1` then `CHECKPOINT release ... closed=0 retired=1
held=named named=1:2:0`. The two names are the EXT entries of the two reclaimed records' OLD handles
(`books/payload-arena-extent.lisp` `fn-arx-file-count`); nothing ever rewrites them, so
`fn-xrt-quiet-files` (`books/extent-retire.lisp:276`) never answers the file and `fnn-extent-close`
(`host/native/extent.lisp:1225`) is never reached. The file is already unlinked (`fnn-log-drop`,
`host/native/io.lisp:7255`); only the descriptor holds its blocks.

DEF-HOLDER's F4 and my own sweep agreed that the design is smaller than a new liveness relation; c05 showed F4's liveness clause and its release site are wrong (section 8).
The generation table (`books/arena-reader-pins.lisp`), the retire/release path
(`host/native/io.lisp:6806-6861`), the file count column, the quiet check and the pending close already
exist. What is missing is (a) an arena export that drops one handle's entry, (b) the list of handles a
reclaim swap un-names, (c) the proof that the swapped history names none of them.

## 1. Holder inventory (verified in source; DEF-HOLDER's R1 table agrees)

Holders of a payload handle across a release of the owner mutex:

| holder | where | registers | releases | at a reclaim swap |
|---|---|---|---|---|
| the served history's rows (Store records, view archive, `fn-cat`, `fn-hist`) | `books/owner-reclaim-pass.lisp:310,381-395`; `host/owner-host.lisp:5177`; `host/native/owner.lisp:5760-5761` | intern (`books/store-intern.lisp:49`, `books/catalog-record.lisp:391`) | none per handle | all four rebuilt from the rewritten rows in the swap quantum; connections re-pinned to the rebuilt view (`fn-orcp-repin-conn` :333 takes archive/index from the rebuilt owner) |
| off-mutex readers: publication, export, reclaim dry run, the pass | `host/native/owner.lisp:5255,5305,5469,5661` | `fnn-arena-pin` under the mutex | `fnn-arena-unpin` :5152,5270,5315,5415,5504,5788 | swap word `:readers` unless only the pass is pinned (`books/owner-reclaim-pass.lisp:156`) |
| a connection's response plan (OVER cursor) | `host/native/owner.lisp:483,4549`; `books/response-plan-pins.lisp:30` | `(:acquire cid)`, same table | `mux.lisp:274,505`, `pull-service.lisp:293,399,452`, `web-host.lisp:125,134` | counted as a reader: blocks the swap (DEF-HOLDER F5) |
| whole-arena leases `fn-pvl-livep`, `fn-rpv-livep` | `books/payload-view-lease.lisp:19-54`, `books/recovery-payload-view.lisp:5-45` | acquire | release | their drivers are not loaded by `host/native/build.lisp`; the forget must still refuse while one is live |
| fenced / in-flight log members `(handle file place size)` | `host/native/io.lisp:6323,6765,6836` | commit | `fnn-log-reseat-fenced` | NOT tested by the swap word (it tests the owner's queue/pending/inflight). See 4(c). |
| staged-page retirements already pending in the pins table | `host/native/io.lisp:6856` | `(:retire handles)` | `(:release)` then `fn-arena-release` | may name a reclaimed handle later; harmless (the release frees a page only under an extent entry) |

Copies that are not handles and are already protected: a cold read holds a copied entry and the fd, guarded
at close by `fn-pio-file-clear-p` (`extent.lisp:1232`); the extent cache is dropped per file at close
(`extent.lisp:1234`); the page-file pin answers `:read-file-held` (`extent.lisp:1251`).

NOT holders (re-resolve by Message-ID under the mutex): feeds (`books/peer-feed.lisp:3-5`,
`books/owner.lisp:2499`), consumers (`books/consumer-position.lisp:35-46`), BP jobs
(`books/bp-outbound.lisp:48`), pending/queue/inflight/staged/refused/ledger/facts
(`books/owner.lisp:26-49`, `books/packed-submission.lisp:13-15`). The arena header's reason for "no
delete" was not what the tree does; the header is corrected on the lane.

Memory-only leftovers the swap neither clears nor checks (not read after the swap, but they keep old
articles alive): `fn-owner-access-cache` (`host/owner-host.lisp:1322,4286`: entries keyed by the old
archive), `fn-bprj-bound-store` (`host/bp-native-app-host.lisp:110`: the old Store by pointer until the
next BP callback). `fn-owner-reader-views` (`host/owner-host.lisp:3898`) is expected nil when idle but
nothing tests it. These belong to the memory half (section 6).

## 2. The liveness relation

A handle is live iff a row of the served history names it, OR a reader is pinned at a generation at or
below the stamp at which it stopped being named, OR a whole-arena lease is live. All three are carried:
the rows by the swap, the generations by `fn-arpn-step` (one count per generation, one comparison with
the oldest pin), the leases by one slot each. No scan per forget. DEF-HOLDER provides the composed
theorem (its instance 3, `fn-handle-holds`); this lane owns the export and the disk/memory return.

I had started a hand ghost machine for the same statement (ROOTS, per-holder handle sets, forgotten set;
invariant "no live holder holds a forgotten handle"); its lemmas up to the split are REPL-admitted and it
is parked at `build/coordinator/lanedumps/arena-forget-ghost.lisp.txt`, superseded by DEF-HOLDER unless
you want it finished.

## 3. The forget theorems (statements)

Built and REPL-admitted on the lane (not yet certified):

- `fn-arena-forget` (`books/payload-arena.lisp`; `:logic fn-arena$a-forget`,
  `books/payload-arena-extent-logic.lisp`: `(update-nth h nil a)` inside the arena, the identity outside).
  No existing `:logic` definition changed; one export added to the generic and to the attached
  `fn-arena-extent`.
- KEYSTONE `fn-arena-forget-payload`: `(natp h)` ⇒ payload h is empty; `(natp k)`, `k ≠ h` ⇒ payload k
  unchanged; the count is unchanged (no handle is reused); an arena stays an arena. `h < count` was
  proved redundant and dropped.
- Concrete: `fn-arena$x-forget` marks EXT[h] `:forgotten` (a new entry kind whose view is the empty
  payload: no realizer, no child read) and empties the stage slot. KEYSTONE `fn-arx-forget-file-count`:
  under `fn-arena$xcorr`, the count of the file EXT[h] named falls by exactly one and every other file's
  count is unchanged. With the existing `fn-xrt-quiet-files-are-unnamed` and
  `fn-xrt-dropped-file-is-released` that is "the file count reaches 0, the file goes quiet, the host
  closes it".
- KEYSTONE `fn-arf-apply-released-payload` (`books/arena-forget.lisp`): what the host does with the pins
  step's `:release` answer (`fn-arf-apply-released`: a plain handle is a staged page to release, a
  `(:forget h)` item is forgotten) empties exactly the tagged handles.

To build (the wide part, section 7): **the root theorem** — the handles the swap retires are named by no
row of the rewritten history.

## 4. Questions for Codex

(a) **Where the root fact is carried.** The pass has the captured old rows and the interned rewritten
rows as position-parallel lists (`host/native/owner.lisp:5670,5676,5728`); unchanged rows are kept by
pointer, changed rows are records interned at fresh handles (`fn-orcp-intern-rows`, handle = the count
before, `books/catalog-record.lisp:442`). The retired set is "old handle of every position whose row
changed". Disjointness from the new rows' handles needs: the old rows' handles are pairwise distinct and
below the arena count. Nothing proves that today (`fn-row-handle-inp` is a bounds check;
`fn-scol-okp` relates facts to bytes, not handles to each other). Options: (A) a carried relation
H(records, arena) = handles distinct and below the count, preserved by open / commit / swap, sibling of
`fn-scol-okp` with the same writer list; (B) a per-handle name count column in the concrete arena
(like the file column), built in the swap's existing `fn-owner-orcp-load-columns` walk, forget
admissible iff 0; (C) DEF-HOLDER's `:named-by`. I prefer (A): no new column, and it also gives
`fn-scol-okp-of-forget`. Which does Codex prefer, and is there an existing invariant I missed?

(b) **The logical value of a forgotten handle.** `nil` (the empty payload) keeps `fn-arena$ap` and every
`:logic` definition. A late read then returns an empty payload, through no realizer and no descriptor:
safe, but not a refusal BY NAME. A named refusal needs either a marker in the logical value (changes
`fn-arn-payload-listp`: whole-tree) or a concrete-only reader `fn-arx-forgotten-p` the host checks.
Is "empty, never dangling" enough given every reader is pinned or under the mutex, or must the read path
answer a named refusal?

(c) **Reseat must not resurrect.** `fn-arx-commit-place` finds an empty payload anywhere, so a fenced
member whose handle was forgotten would be reseated as a zero-length extent and re-name the log file.
Proposed: `fn-arx-commit-extent` (and the lz twin) refuse a handle whose payload length is 0; the
keeps-the-arena keystones only get easier. Alternative: the swap word also requires no fenced member.

(d) **F5.** Connections are counted, not identified, so one undrained response holds off every swap
(8 rounds, then `RECLAIM deferred reason=readers`). With the forget retired at a stamp, the swap itself
no longer needs `readers = 0` for safety of the reclaimed handles — only for the catalog/history stobj
swap under readers that read `fn-cat` off the mutex. Is relaxing the swap word in scope here or its own
row? I propose its own row; this lane's native measures reclaim with reads between quanta, not during
the swap quantum.

## 5. Late holder, cost, crash

- Late holder: the retirement is released only when no pin is at or below its stamp
  (`fn-arpn-release-postdates-every-live-pin`); a holder pinned at or below it keeps it pending
  (`fn-arpn-release-keeps-every-covered-retirement`: the mutation tooth, forget refused). An unpinned
  read after the forget reads the empty payload (4(b)).
- Cost per operation: retire = one walk of the two row lists the pass already holds, off the mutex
  (pointer compare per row); forget = one EXT write + one count move + one page resize per handle; release
  = the pending retirements it walks; quiet = one count read per retired file (unchanged).
- Crash: the forget and the close are process-local (the open rebuilds the arena from the installed
  checkpoint; the file is already unlinked before the forget). The model crash point is a new cut
  `:forgotten` between `:swapped` and `:released` in `*fn-orcp-cuts*` / `+fnn-reclaim-cuts+`, with outcome
  "the new publication" like `:swapped`; recovery after a kill there must find no dropped segment and
  open the rewritten history.

## 6. Memory

Returned by the forget: the staged page, the EXT entry, and (at close) the extent cache entries of the
file. NOT returned: a resident payload's octets in the paged child (`books/payload-arena-paged.lisp`:
payloads are packed in 256 KiB pages; no per-payload free). In a served node resident payloads are the
tombstones (`fn-cat-intern-list` → `fn-arena-seal-list`) and anything sealed by list. Returning those
needs a per-page live count (the file column's shape) so a page whose payloads are all forgotten is
resized to 0. Proposed as the lane's last slice, after the disk path lands; plus clearing
`fn-owner-access-cache` in the swap.

## 7. Slices

1. DONE on the lane (REPL): the export, the concrete forget, the three keystones above.
2. Independent of the answers, next: teeth for 1; `fn-arf-changed-handles` (the pairwise walk) with its
   pure list theorem (distinct + fresh ⇒ disjoint); 4(c)'s refusal; `fn-scol-okp-of-forget` under
   "unnamed"; certify `--affected-by books/payload-arena`.
3. After the answers: the root fact (4(a)); host wiring in `fnn-owner-reclaim-pass` (retire in the swap
   quantum, the pass re-pins, `fn-arf-apply-released` where `fn-arena-release` is called today and before
   the quiet check); the `:forgotten` cut; the native (reclaim with reads running: fd closed, file
   unlinked, df and RSS back, no restart) with page_io / owner / recovery / crash_model.
4. Resident memory (section 6).

No host file is wired until the root fact is proved: a forget of a handle a kept row still names would
serve an empty article until restart.

## Astra's view (consultation c08, gpt-6-astra, read-only at lane/arena-forget 45bab6a65, 1304 s)

### Liaison fact-check (codex-liaison-11, 2026-10-03); cross-read with c05 (lanedumps/def-holder.md, "Astra's view")
Checked in source myself (worktree build/lanes/codex-c08-forget):
- CONFIRMED (c): zero length is the wrong "forgotten" predicate AND the resurrection is wider than fn-arx-commit-place:
  fn-arx-arena-prefixp answers t for n = 0 (books/payload-commit-extent.lisp:46-55); fn-xrt-reseat-one sends a captured
  checkpoint-frame handle through the same commit reseat (books/extent-retire.lisp:101-111, from fn-xrt-reseat-frame :121,
  host-called per owner.lisp:4932); the direct reseat exports fn-arena$x-reseat-extent / -lz-extent take any in-range h with
  no liveness condition (books/payload-arena-extent.lisp:684-711, per Astra's quote). The refusal must be "forgotten / not
  owned by this reseat", with a named status the host acts on.
- CONFIRMED, A LEAK THAT EXISTS TODAY without any forget: the reclaim pass interns the tombstone rows BEFORE the swap loop
  (host/native/owner.lisp:5726-5729, `(setq rows (fnn-owner-reclaim-intern ...))`); a pass deferred by :readers/:delta ends
  in fn-owner-orcp-finish and unlinks only the stage (:5792-5799), leaving those freshly sealed arena payloads unnamed and
  unreleased. Every deferred reclaim grows the arena. Own row.
- CONFIRMED, an exception-protocol contradiction: fnn-extent-close says "Any error escapes with the tables/lease intact.
  The owner fences; ambiguous close never refunds and resumes" (host/native/extent.lisp:1243-1244), but its caller
  fnn-owner-release-extents catches serious-condition and logs "CHECKPOINT release failed (files stay retired)" and
  continues (host/native/owner.lisp:5011-5012). An ambiguous close is swallowed, not fenced. Own row (served/recovery path).
- CONSISTENT with c05: (a) handles ARE shared across catalog / history / view projections (fn-sca-load-held-row commits the
  held row history supplies; served-catalog-owner.lisp:434-454 per Astra), so the root fact is a carried name COUNT over
  declared roots with projection theorems (option B), not pairwise distinctness over all structures.
- NOT CHECKED by me: the crash-order walk in (e) (owner.lisp:5694-5786; Astra finds NO unlink-before-durable bug, only an
  unproved composition), section (b)'s response divergence on an empty read, (d), (g)'s per-consumer table.
Liaison's reading: (a) B -- a carried per-handle name count over declared roots, published with the rebuilt roots;
(b) neither empty nor a bolted-on refusal: every host-called read carries a proved "live handle" premise and the raw boundary
FAIL-STOPS with a named forgotten-payload fault (agrees with the coordinator that an empty article is wrong; a missing payload
of a kept row is an invariant failure, not 430/423); (c) refuse by lifecycle, not length, at ALL reseat paths (10 families
examined); (d) OWN ROW; (e) no ordering bug found, but the composition is unproved and :forgotten's placement is unspecified;
(f) pin theorems are safety only: they omit roots and leases and do not schedule release. WIRE AFTER the eight ordered
proof requirements in (h). NEEDS EMBER: no.

### Astra's answer (verbatim)

(a) **B**, with explicit root/projection ownership: catalog/history/view aliases share handles; counting only one structure is insufficient (§a).
(b) **OTHER: logical empty + proved live-read domain + named fail-stop at the raw boundary**; **AGREE** with rejecting silent success, not with disguising invariant failure as article absence (§b).
(c) Zero-length refusal **WRONG as the forgotten predicate**; **10 other path families** examined, including checkpoint reseat and direct reseat (§c).
(d) **OWN ROW** for relaxing the swap; busy-server progress remains a qualification dependency (§d).
(e) Crash: **HOLE in the claimed composition/cut coverage**, not a demonstrated unlink-before-durable-publication bug (§e).
(f) Liveness: **INSUFFICIENT**; the pin theorems are safety statements, omit root/lease coverage and do not schedule release (§f).
Overall: **WIRE AFTER** root-count/projection preservation, lifetime/read boundary, non-resurrection, crash composition, release scheduling, and certification with teeth (§h).
**NEEDS EMBER: no.** These are engineering/proof obligations, not private-policy choices.

## Scope and the three keystones — read before the recommendations

This is a source consultation of the supplied lane diff, not certification or a runtime result. No ACL2, build, native test, deployment, or tracked edit was performed. “SOUND” below means the stated source-level argument is sound within the stated assumptions; it does not assert that this lane is certified. “HOLE” identifies a missing safety/progress argument or a concrete bad construction; “UNVERIFIED” identifies a reachability/composition claim I could not establish. The supplied brief itself says the change is “REPL-admitted, not certified” (`build/codex/c08/CONSULT.md:5`).

**SOUND, narrowly: keystone 1 matches section 3's payload/count/type statement.** It is not a theorem that forgetting is admissible. In particular it has no root, reader, lease, or retirement hypothesis. The second conjunct does not need `natp h`: the logical definition is identity for non-natural h. Count preservation plus subsequent append-only seals supplies non-reuse within an arena incarnation; count preservation alone does not address clear/reopen.

`books/payload-arena.lisp:752-761`:
```lisp
(defthm fn-arena-forget-payload
  (and (implies (natp h)
                (equal (fn-arena-payload h (fn-arena-forget h fn-arena)) nil))
       (implies (and (natp k) (not (equal k h)))
                (equal (fn-arena-payload k (fn-arena-forget h fn-arena))
                       (fn-arena-payload k fn-arena)))
       (equal (fn-arena-count (fn-arena-forget h fn-arena))
              (fn-arena-count fn-arena))
       (implies (fn-arena-p fn-arena)
                (fn-arena-p (fn-arena-forget h fn-arena))))
```

`books/payload-arena-extent-logic.lisp:77-82`:
```lisp
; its retirement stamp still holds (books/arena-forget.lisp).
(defun fn-arena$a-forget (h fn-arena$a)
  (declare (xargs :guard (natp h)))
  (if (and (natp h) (< h (len fn-arena$a)))
      (fn-oct-update h nil fn-arena$a)
    fn-arena$a))
```

**SOUND arithmetic; WEAK lifecycle conclusion: keystone 2 matches the qualified file-count claim.** It subtracts one iff the old entry actually names natural file f. A staged, resident, or already-forgotten entry subtracts zero. It says nothing about eventual close, successful OS close, another descriptor, a later reseat, or generation/issued-read/lease gates. The comment's “and the host closes” is stronger than this theorem.

`books/payload-arena-extent.lisp:1572-1586`:
```lisp
; KEYSTONE (PRF-ARF-2).  The forget gives back exactly H's name: the count of
; the file H's entry named falls by one and every other file's count is
; unchanged.  So once every handle that named a dropped file is reseated or
; forgotten its count is 0, fn-xrt-quiet-files answers it
; (books/extent-retire.lisp) and the host closes its descriptor while
; serving.  Host subject: host/native/io.lisp fnn-arena-forget-due calls
; fn-arena-forget on the live arena, whose attachment runs fn-arena$x-forget.
(defthm fn-arx-forget-file-count
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena$a)
                (natp h) (< h (len fn-arena$a)) (natp f))
           (equal (fn-arx-file-count f (fn-arena$x-forget h fn-arena$x))
                  (- (fn-arx-file-count f fn-arena$x)
                     (if (equal (fn-arx-entry-file (nth h (nth *fn-arena$x-exti* fn-arena$x))) f)
                         1
                       0))))
```

`books/payload-arena-extent.lisp:484-486`:
```lisp
(defun fn-arx-entry-file (e)
  (declare (xargs :guard t))
  (if (or (fn-arn-extentp e) (fn-arn-lz-extentp e)) (nth 0 e) nil))
```

**SOUND extensional result; HOLE as permission to forget: keystone 3 matches the note's apply-the-tagged-items statement, but REL is arbitrary.** It is not required to equal a pins-step answer, have stamps of any particular age, or name handles absent from roots. Supplying `REL = ((0 (:forget 0)))` and a valid one-payload arena with a kept row naming 0 satisfies the applicable clauses and empties that row's payload. This is a counterexample to the claimed lifecycle interpretation, not to the defthm. “Exactly” means tagged handles become empty and other payload values stay unchanged; it cannot mean an iff between empty payload and membership, since untagged payloads may already be empty.

`books/arena-forget.lisp:200-216`:
```lisp
; KEYSTONE (PRF-ARF-3).  The release empties exactly the tagged handles of
; what the pins step released: such a handle reads the empty payload, every
; other handle keeps its payload, the count is unchanged (no handle is
; reused) and an arena stays an arena.  Host subject: host/native/io.lisp
; fnn-arena-apply-due calls fn-arf-apply-released under the owner's mutex.
(defthm fn-arf-apply-released-payload
  (and (implies (and (natp k) (not (member-equal k (fn-arf-pend-handles rel))))
                (equal (fn-arena-payload k (fn-arf-apply-released rel fn-arena))
                       (fn-arena-payload k fn-arena)))
       (implies (and (natp k) (member-equal k (fn-arf-pend-handles rel)))
                (equal (fn-arena-payload k (fn-arf-apply-released rel fn-arena))
                       nil))
       (equal (fn-arena-count (fn-arf-apply-released rel fn-arena))
              (fn-arena-count fn-arena))
       (implies (fn-arena-p fn-arena)
                (fn-arena-p (fn-arf-apply-released rel fn-arena))))
  :hints (("Goal" :in-theory (disable fn-arf-apply-released))))
```

`books/arena-forget.lisp:114-136`:
```lisp
; mutex: a staged page is released, a tagged handle is forgotten.  One arena
; export per item.
(defun fn-arf-apply-items (items fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (atom items)
      fn-arena
    (let ((fn-arena (cond ((natp (car items))
                           (fn-arena-release (car items) fn-arena))
                          ((fn-arf-forget-item-p (car items))
                           (fn-arena-forget (cadr (car items)) fn-arena))
                          (t fn-arena))))
      (fn-arf-apply-items (cdr items) fn-arena))))

; The host's call (host/native/io.lisp fnn-arena-apply-due): REL the pins
; step's :release answer, ((S . ITEMS) ...).
(defun fn-arf-apply-released (rel fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (atom rel)
      fn-arena
    (let ((fn-arena (if (consp (car rel))
                        (fn-arf-apply-items (cdr (car rel)) fn-arena)
                      fn-arena)))
      (fn-arf-apply-released (cdr rel) fn-arena))))
```

**WEAK host-subject claims; not intrinsically vacuous.** The payload clauses have ordinary nonempty-array witnesses; the file clause is intended for a corresponding extent-backed arena; the release clause has tagged and untagged natural-handle witnesses. None states an impossible hypothesis. Full reachable positive/hypothesis-removal witnesses and admission remain UNVERIFIED here. The two named native functions in the comments, `fnn-arena-apply-due` and `fnn-arena-forget-due`, have no definitions in the searched tracked books/host/tests Lisp source: their only occurrences are the comments quoted above. The actual native release loop below still calls only `fn-arena-release`. Therefore these are intended future subjects, not current host-call evidence. The primitive correspondence is useful and must be certified, but does not supply lifetime admissibility.

`host/native/io.lisp:6854-6861`:
```lisp
            (fnn-call 'fn-lzr-commit-reseats fenced (fnn-lz-dicts) arena)
          (fnn-call 'fn-arx-commit-reseats fenced arena))
        (fnn-arena-retire (mapcar #'first fenced))))
    (let ((due (fnn-arena-release-due)))
      (when due
        (let ((arena (fnn-live-arena)))
          (dolist (entry due)
            (dolist (h (cdr entry)) (fnn-call 'fn-arena-release h arena))))))))
```

`books/payload-arena-extent.lisp:1411-1424`:
```lisp
(defthm fn-arena-extent-forget{correspondence}
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena-extent)
                (natp h))
           (fn-arena$xcorr (fn-arena$x-forget h fn-arena$x)
                           (fn-arena$a-forget h fn-arena-extent)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-arx-view-of-update-inside fn-arx-view-of-stage-update-inside
                                     fn-oct-update-is-update-nth))))

(defthm fn-arena-extent-forget{guard-thm}
  (implies (and (fn-arena$xcorr fn-arena$x fn-arena-extent)
                (natp h))
           (and (natp h) (fn-arena$x-wfp fn-arena$x)))
  :rule-classes nil)
```

## (a) Root fact and every writer

**Recommendation: B, a carried name-count/lifetime relation over precisely declared active roots, with projection theorems for aliases.** Compute the candidate counts during the existing rebuild walk, publish them atomically with the replacement roots, maintain them at incremental writers, and permit forget only at zero plus the reader/lease condition. Do not count only visible NNTP rows: withdrawn/history rows and future replay/export sources matter. DEF-HOLDER's `:named-by` can package this theorem; it cannot replace its proof.

**Cost:** a concrete per-handle column (or equivalent generated carry), allocation/accounting for it, preservation at each writer below, a concrete/logical correspondence, and explicit rules for root publication and retirement. No scan at each forget. **What it breaks:** the lane's “no new column” preference and any caller that implicitly acquires a root without maintaining the carry. It preserves sharing. A future optimization may collapse redundant projection counts to one canonical owner only after proving those projections are always covered.

**HOLE in unqualified A; no evidence of payload deduplication at intern.** There is ordinary handle sharing across structures: catalog load commits the held row supplied by history; history load appends that same event; a catalog article carries the same payload handle plus all groups and local memberships. A withdrawn/context-updated row is another row value with the original handle. Hence pairwise distinctness across the inventory of all row-like objects is false. However, that does **not** refute the narrower proposed invariant over just one canonical `records` list: aliases in derived structures can be justified by a projection relation. I found no intern deduplication or reachable duplicate handle within that canonical list. That narrower A remains a plausible theorem, not an established one. A counter over all aliases is not mathematically mandatory if those projection theorems exist; it is my recommended implementation here because the consultation requires covering the wider root inventory, whose closure is not yet established.

`books/served-catalog-owner.lisp:434-454`:
```lisp
  (let ((h (cond ((fn-cat-rowp r) r)
                 ((fn-sca-composite-shapep r) (fn-hstxa-held r))
                 (t nil))))
    (if h
        (if (fn-midx-lookup (fn-record-msgid h) view-index)
            (fn-cat-commit h fn-cat)
          (fn-cat-commit (fn-held-with-withdrawn h (cons (fn-cat-count fn-cat) 0)) fn-cat))
      fn-cat)))

(defun fn-sca-load-held-rows-from (rows view-index fn-cat)
  (declare (xargs :stobjs fn-cat :guard (fn-sca-held-rowsp rows)))
  (if (consp rows)
      (let ((fn-cat (fn-sca-load-held-row (car rows) view-index fn-cat)))
        (fn-sca-load-held-rows-from (cdr rows) view-index fn-cat))
    fn-cat))

(defun fn-sca-load-held-rows (rows view-index fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-sca-held-rowsp rows))
           (ignorable fn-arena))
  (let ((fn-cat (fn-cat-clear fn-cat)))
    (fn-sca-load-held-rows-from rows view-index fn-cat)))
```

`books/history-columns.lisp:786-797`:
```lisp
(defun fn-hist-load-events (events fn-hist)
  (declare (xargs :stobjs fn-hist :guard (true-listp events)))
  (if (consp events)
      (let ((fn-hist (fn-hist-append (car events) fn-hist)))
        (fn-hist-load-events (cdr events) fn-hist))
    fn-hist))

(defun fn-hist-load (events salt fn-hist)
  (declare (xargs :stobjs fn-hist
                  :guard (and (true-listp events) (unsigned-byte-p 32 salt))))
  (let ((fn-hist (fn-hist-clear salt fn-hist)))
    (fn-hist-load-events events fn-hist)))
```

`books/catalog-view.lisp:53-65`:
```lisp
(defun fn-cat-row-article (seq fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp seq) (< seq (fn-cat-count fn-cat))
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil)
           (ignorable fn-arena))
  (let ((h (fn-cat-at seq fn-cat)))
    (fn-make-article (fn-record-msgid h)
                     (fn-record-payload h)
                     (fn-record-groups h)
                     (fn-held-numbers h)
                     t
                     (fn-record-stamp h))))
```

`books/held-record.lisp:287-303`:
```lisp
(defun fn-held-with-withdrawn (h withdrawn)
  (declare (xargs :guard t))
  (fn-held-make (fn-record-sequence h) (fn-record-txid h) (fn-record-generation h)
                (fn-record-msgid h) (fn-record-payload h) (fn-record-groups h)
                (fn-record-obligation-id h) (fn-record-content-subject h)
                (fn-record-release-evidence h) (fn-record-charge h)
                (fn-record-stamp h) (fn-held-facts h) (fn-held-context h)
                (fn-held-numbers h) withdrawn))

(defun fn-held-with-context (h context)
  (declare (xargs :guard t))
  (fn-held-make (fn-record-sequence h) (fn-record-txid h) (fn-record-generation h)
                (fn-record-msgid h) (fn-record-payload h) (fn-record-groups h)
                (fn-record-obligation-id h) (fn-record-content-subject h)
                (fn-record-release-evidence h) (fn-record-charge h)
                (fn-record-stamp h) (fn-held-facts h) context
                (fn-held-numbers h) (fn-held-withdrawn h)))
```

**SOUND: intern means allocate, not content deduplicate.** `fn-intern-event` dispatches record/composite articles to `fn-cat-intern-list`; that obtains count and seals even if the bytes already occur elsewhere. Buffer intern likewise obtains count and seals. `fn-intern-row-at` merely constructs at its supplied h; by itself it guarantees no freshness. The prepare entry supplies count and seals only when prepare changes the Store. Thus an identical payload or retry that is actually interned gets a fresh handle; a refusal that leaves Store unchanged does not seal. “Duplicate request was suppressed” and “payload bytes were deduplicated” are different claims.

`books/store-intern.lisp:49-61`:
```lisp
(defun fn-intern-event (w keyring generation fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (fn-prin-keyringp keyring) (natp generation))))
  (cond ((fn-record-p w) (fn-cat-intern-list w keyring generation fn-arena))
        ((fn-stxa-p w)
         (let ((a (fn-replay-composite-record w)))
           (if (fn-record-p a)
               (mv-let (held fn-arena)
                 (fn-cat-intern-list a keyring generation fn-arena)
                 (mv (fn-hstxa-make w held) fn-arena))
             (mv :bad fn-arena))))
        ((fn-wire-event-p w) (mv w fn-arena))
        (t (mv :bad fn-arena))))
```

`books/catalog-record.lisp:391-407`:
```lisp
(defun fn-cat-intern-list (w keyring generation fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (fn-record-p w) (fn-prin-keyringp keyring)
                              (natp generation))
                  :guard-hints (("Goal" :in-theory (enable fn-record-p fn-record-payloadp)))))
  (let* ((bytes (fn-record-payload w))
         (h (fn-arena-count fn-arena))
         (fn-arena (fn-arena-seal-list bytes fn-arena)))
    (mv (fn-held-make (fn-record-sequence w) (fn-record-txid w)
                      (fn-record-generation w) (fn-record-msgid w) h
                      (fn-record-groups w) (fn-record-obligation-id w)
                      (fn-record-content-subject w) (fn-record-release-evidence w)
                      (fn-record-charge w) (fn-record-stamp w)
                      (fn-held-facts-of bytes)
                      (fn-held-context-of bytes keyring generation)
                      nil nil)
        fn-arena)))
```

`books/catalog-record.lisp:414-424`:
```lisp
(defun fn-cat-intern (w fn-octets keyring generation fn-arena)
  (declare (xargs :stobjs (fn-octets fn-arena)
                  :guard (and (fn-prin-keyringp keyring) (natp generation))))
  (let* ((bytes (fn-octets-list fn-octets))
         (h (fn-arena-count fn-arena))
         (fn-arena (fn-arena-seal-buffer fn-octets fn-arena)))
    (mv (fn-held-make (fn-record-sequence w) (fn-record-txid w)
                      (fn-record-generation w) (fn-record-msgid w) h
                      (fn-record-groups w) (fn-record-obligation-id w)
                      (fn-record-content-subject w) (fn-record-release-evidence w)
                      (fn-record-charge w) (fn-record-stamp w)
```

`books/store-intern.lisp:911-922`:
```lisp
(defun fn-intern-row-at (w keyring generation h)
  (declare (xargs :guard (and (fn-record-p w) (fn-prin-keyringp keyring)
                              (natp generation) (natp h))
                  :guard-hints (("Goal" :in-theory (enable fn-record-p fn-record-payloadp)))))
  (let ((bytes (fn-record-payload w)))
    (fn-held-make (fn-record-sequence w) (fn-record-txid w)
                  (fn-record-generation w) (fn-record-msgid w) h
                  (fn-record-groups w) (fn-record-obligation-id w)
                  (fn-record-content-subject w) (fn-record-release-evidence w)
                  (fn-record-charge w) (fn-record-stamp w)
                  (fn-held-facts-of bytes)
                  (fn-held-context-of bytes keyring generation)
```

`books/store-intern.lisp:933-944`:
```lisp
(defun fn-store-prepare-interned (s w fn-arena)
  (declare (xargs :stobjs fn-arena :guard (fn-sn-statep s) :verify-guards nil))
  (if (and (fn-record-p w) (fn-prin-keyringp (fn-sn-keyring s))
           (natp (fn-sn-keyring-generation s)))
      (let* ((row (fn-intern-row-at w (fn-sn-keyring s) (fn-sn-keyring-generation s)
                                    (fn-arena-count fn-arena)))
             (next (fn-sn-prepare s row)))
        (if (equal next s)
            (mv s fn-arena)
          (let ((fn-arena (fn-arena-seal-list (fn-record-payload w) fn-arena)))
            (mv next fn-arena))))
    (mv s fn-arena)))
```

**Writer inventory / preservation obligations.** These are the required writer families, not a claim that an exhaustive image-world writer check has run:

| Writer | Fresh allocation? | Required preservation |
|---|---|---|
| Cold open/full recovery and log suffix replay | Yes for each article intern; non-article events do not seal | Initialize/rebuild counts and handle bounds; no old-incarnation retirement may survive |
| Checkpoint arena load | Clear then one seal per payload; canonical numbering starts over | Match the loaded canonical rows to that pool, not old process handles |
| Prepare/commit/completion, including retry paths | Prepare seals at old count when admitted; completion publishes that prepared handle | Count only when a root is published; prove the prepared token has one allocation and cannot be republished incorrectly |
| Reclaim intern | Fresh for rewritten plain records; unchanged held rows are returned intact | Keep rewrite provenance; never infer freshness from row inequality alone |
| Reclaim swap | No new seals in the swap itself | Atomically replace Store/view/catalog/history and their count relation, retire exactly the old roots un-named |
| Withdrawal/cancel | The target keeps its handle; an independently accepted control article uses normal prepare | Visibility removal is not root removal; preserve counts of history/withdrawn rows |
| Reconfiguration/keyring recontext | Existing rows keep handles while contexts change | Preserve handle ownership despite non-identical row values; new config events use their own event path |
| Catalog/history/index/view/cache/connection root installation | Copies or projects handles, not fresh allocation | Establish projection/ownership, and prove stale projections inaccessible or held until release |

The fresh replay branch is below. Checkpoint load and its actual host bridge are in §e; swap/rewrite definitions and the no-allocation metadata writers are quoted in this section. Reconfiguration's complete closure through every host entry, every prepare token producer, and all arbitrary checkpoint acceptance cases is **UNVERIFIED**; these must be in the preservation theorem, not accepted from this inventory.

`books/payload-extent.lisp:279-299`:
```lisp
(defun fn-arx-cat-intern-extent (w x keyring generation fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (fn-record-p w) (fn-prin-keyringp keyring) (natp generation)
                              (fn-arn-extentp x))
                  :guard-hints (("Goal" :in-theory (enable fn-record-p fn-record-payloadp)))))
  (let* ((bytes (fn-record-payload w))
         (h (fn-arena-count fn-arena))
         (fn-arena (fn-arena-seal-extent (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x) (nth 4 x) (nth 5 x)
                                         fn-arena)))
    ;; The facts and the context from one parse of the article
    ;; (books/store-intern-once.lisp, KEYSTONE
    ;; fn-ipo-facts-context-is-facts-and-context); the logic reads each.
    (mv-let (facts context)
      (mbe :logic (mv (fn-held-facts-of bytes) (fn-held-context-of bytes keyring generation))
           :exec (fn-ipo-facts-context bytes keyring generation))
      (mv (fn-held-make (fn-record-sequence w) (fn-record-txid w)
                        (fn-record-generation w) (fn-record-msgid w) h
                        (fn-record-groups w) (fn-record-obligation-id w)
                        (fn-record-content-subject w) (fn-record-release-evidence w)
                        (fn-record-charge w) (fn-record-stamp w)
                        facts context nil nil)
```

`books/payload-extent.lisp:316-325`:
```lisp
(defun fn-arx-intern-event (w r position file keyring generation fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (natp file) (fn-prin-keyringp keyring) (natp generation))
                  :guard-hints (("Goal" :in-theory (disable fn-record-p fn-intern-event
                                                            fn-arx-cat-intern-extent)))))
  (let ((x (and (fn-record-p w) (true-listp r) (true-listp position)
                (fn-arx-extent-of file position r w))))
    (if x
        (fn-arx-cat-intern-extent w x keyring generation fn-arena)
      (fn-intern-event w keyring generation fn-arena))))
```

`books/store-intern.lisp:172-179`:
```lisp
(defun fn-store-set-keyring (s keyring fn-arena)
  (declare (xargs :stobjs fn-arena :guard (fn-sn-statep s)
                  :guard-hints (("Goal" :in-theory (e/d (fn-sn-statep) (fn-sf-statep fn-node-statep))))))
  (if (fn-prin-keyringp keyring)
      (fn-sn-set-keyring s keyring
                         (fn-contexts-of-rows (fn-sf-records (fn-sn-files s)) keyring
                                              (1+ (fn-sn-keyring-generation s)) fn-arena))
    s))
```

**SOUND correction: `dropped=1` does not mean a row was removed.** The driver passes `covered` log-segment indices to `fnn-log-drop`, and prints that function's returned count. The rewrite is a map (`cons` of one rewrite per row), returning either a tombstone record or the original row. The intern is another map and rejects `:bad`; native code checks each chunk's length. Thus the particular “dropped row shifts positions” attack is not a reachable construction of this pass as inspected. A general pairwise-diff retirement helper would nevertheless be dangerous if a future rewrite filtered or reordered rows: old `[A(h0), B(h1)]`, new `[B(h1)]` would retire h0 and could also mishandle a missing tail. Old `[A(h0), B(h1)]`, new `[B(h1), C(h2)]` would retire h1 despite its survival at another position. Distinct old handles alone cannot prevent either mistake.

**WEAK proof coverage:** the present recursion supports position preservation by inspection; the loop-equivalence theorem below is not the required theorem saying that a changed position contributes an old handle absent from *every* new root. `fn-arf-changed-handles` has no definition in tracked Lisp at this revision (the note lists it as next work). Prove length/order/unchanged-row identity and fresh-handle disjointness together for the successful host-called intern/rebuild path. Better still, derive retirements from explicit rewrite results or zero name counts, not a raw host pointer comparison.

`books/owner-reclaim.lisp:91-112`:
```lisp
  (let ((o (fn-orc-row-octets row fn-arena)))
    (if (fn-rclp-rewrites-p o ctx)
        (fn-rclp-tombstoned (fn-record-result-record (fn-record-decode-exact o)))
      row)))

; Executes by a loop (depth_check: a chunk's rows), equal by
; fn-orc-rewrite-rows-loop-is-rev-onto.
(defun fn-orc-rewrite-rows-loop (rows ctx acc fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (consp rows)
      (fn-orc-rewrite-rows-loop (cdr rows) ctx
                                (cons (fn-orc-rewrite-row (car rows) ctx fn-arena) acc)
                                fn-arena)
    (fn-ag-rev-onto acc nil)))

(defun fn-orc-rewrite-rows (rows ctx fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (mbe :logic (if (consp rows)
                  (cons (fn-orc-rewrite-row (car rows) ctx fn-arena)
                        (fn-orc-rewrite-rows (cdr rows) ctx fn-arena))
                nil)
       :exec (fn-orc-rewrite-rows-loop rows ctx nil fn-arena)))
```

`books/owner-reclaim-pass.lisp:264-275`:
```lisp
(defun fn-orcp-intern-rows-loop (rows keyring generation acc fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (fn-prin-keyringp keyring) (natp generation))))
  (if (atom rows)
      (mv (fn-ag-rev-onto acc nil) fn-arena)
    (mv-let (row fn-arena)
      (if (fn-record-p (car rows))
          (fn-intern-event (car rows) keyring generation fn-arena)
        (mv (car rows) fn-arena))
      (if (eq row :bad)
          (mv :bad fn-arena)
        (fn-orcp-intern-rows-loop (cdr rows) keyring generation (cons row acc) fn-arena)))))
```

`host/native/owner.lisp:5591-5600`:
```lisp
    (loop while rest do
      (let* ((chunk (loop repeat +fnn-reclaim-chunk-rows+ while rest collect (pop rest)))
             (done (fnn-owner-gated (service :control)
                     (first (fnn-call 'fn-owner-orcp-intern-chunk chunk keyring generation
                                      (fnn-live-arena))))))
        (when (eq done :bad) (return-from fnn-owner-reclaim-intern nil))
        (unless (and (listp done) (= (length done) (length chunk)))
          (fnn-fault "owner returned a malformed interned chunk"))
        (push done out)))
    (let ((all nil)) (dolist (c out all) (setq all (nconc c all))))))
```

`host/native/owner.lisp:5781-5787`:
```lisp
                   (let* ((covered (fnn-log-covered-indices store (first position)))
                          (paths (mapcar (lambda (k) (fnn-segment-path-at store k)) covered))
                          (dropped (fnn-log-drop store covered)))
                     (fnn-err "RECLAIM installed records=~d reclaimed=~d dropped=~d ms=~d"
                              count (length (second decision)) dropped (ms))
                     (fnn-owner-release-extents service store *fnn-checkpoint-frames* paths pin))
                   (fnn-reclaim-cut :released)))))
```

`host/native/io.lisp:7261-7268`:
```lisp
  (when indices
    (dolist (k indices)
      (let ((path (fnn-segment-path-at store k)))
        (when (fnn-lstat path) (fnn-unlink path))
        (fnn-log-at :drop-unlinked)))
    (fnn-fsync-dir (fnn-journal-dir store))
    (fnn-log-at :drop-durable))
  (length indices))
```

**SOUND rebuilding of the four named roots; WEAK “all in the swap quantum.”** Their construction is off-mutex; their publication is in the swap quantum. `fn-orcp-rebuild` recovers Store/view from rewritten rows; `fn-owner-orcp-load-columns` loads fresh catalog/history from those rows; native installs those two stobjs after the owner swap. The source subject for new root invariants must include `fn-owner-orcp-swap` and the column installation protocol, not merely a free-standing list theorem.

`books/owner-reclaim-pass.lisp:310-313`:
```lisp
(defun fn-orcp-rebuild (rows configs frontier max-conns)
  (declare (xargs :guard t :verify-guards nil))
  (let ((e (fn-rii-sco-extend (fn-sco-capture configs nil) configs rows)))
    (list e (fn-ock-recover-extended e configs frontier max-conns))))
```

`books/owner-reclaim-pass.lisp:381-393`:
```lisp
(defun fn-orcp-swap-base (live rebuilt)
  (declare (xargs :guard t))
  (fn-own-make (fn-own-store rebuilt) (fn-own-view rebuilt)
               nil (fn-own-next-id live) (fn-own-max-conns live)
               (fn-own-pending live) (fn-own-ledger-field live)
               (fn-own-clock live) (fn-own-facts live) (fn-own-config live)
               (fn-own-queue live) (fn-own-inflight live) (fn-own-feeds live)
               (fn-own-node-secret live) (fn-own-refused live)))

(defun fn-orcp-swapped-owner (live rebuilt)
  (declare (xargs :guard t :verify-guards nil))
  (let ((o (fn-orcp-swap-base live rebuilt)))
    (fn-own-set-conns o (fn-orcp-repin-conns o (fn-own-conns live)))))
```

`host/owner-host.lisp:5177-5183`:
```lisp
(defun fn-owner-orcp-load-columns (key rows view-index salt fn-arena fn-cat fn-hist)
  (declare (xargs :stobjs (fn-arena fn-cat fn-hist) :mode :program))
  ; THE SWITCH: the fresh catalog under the same key as the served one
  ; (fn-owner-orcp-key), so the swap changes no tag.
  (let* ((fn-cat (fn-sca-load-held-rows-keyed key rows view-index fn-arena fn-cat))
         (fn-hist (fn-hist-load rows salt fn-hist)))
    (mv :loaded fn-cat fn-hist)))
```

`host/native/owner.lisp:5756-5768`:
```lisp
                                     (fnn-state-checkpoint-install store stage)
                                     (setq installed t)
                                     (fnn-reclaim-cut :installed)
                                     (fnn-owner-core 'fn-owner-orcp-swap rebuilt)
                                     (fnn-install-stobj 'fn-cat cat)
                                     (fnn-install-stobj 'fn-hist hist)
                                     (setq swapped t)
                                     ;; The swapped owner is the open's owner
                                     ;; before its recovery barriers: :ready
                                     ;; only after them, in this quantum
                                     ;; (fn-orrd-a-post-after-the-swap-is-
                                     ;; taken-as-before).
                                     (fnn-owner-reclaim-barriers store))
```

**WEAK root closure: caches and sidecars are not all rebuilt.**

* Access cache is read on subsequent requests. The note's literal “not read after the swap” is false. However, reuse is keyed by archive **and** control equality; refresh grows only when the prior articles are a tail, otherwise it rebuilds. I found no unconditional stale-payload read here. Prove the key/projection relation and clear old entries at swap for retention, rather than treating their existence as a demonstrated use-after-forget.
* BP bound Store is a real selectable old root. Binding copies the current Store pointer; `fn-bprj-store` reads it. Native BP completion explicitly rebinds. The assertion that **every** possible reader rebinds before use after swap is **UNVERIFIED**, so the note cannot dismiss it as merely memory. Clearing/rebinding it at root replacement is simpler than relying on distant callback discipline.
* `fn-owner-reader-views` is a semantically active alternative view, not a cache that can simply be ignored. `fn-ocv-reader-view` selects its head when nonempty; the actual span call takes it. The swap word checks queue/pending/inflight/catalog-pending, not this slot. The capture state machine clears it on complete/drop, but the implication “swap admissible ⇒ reader-views nil” still needs a theorem over the actual host sequence. A stale nonempty capture gives a concrete *corrupted-state* counterexample; reachable stale capture is **UNVERIFIED**.
* An existing invariant/gate the note misses: `fn-owner-history-reset-status` blocks swap while a history capture slot exists; swap also resets the canonical sidecar and advances its epoch. This helps protect another history source. It is not handle uniqueness or a proof of coverage for every page fill.
* The scratch history image is reset after writing/adoption (`fn-his-release`), so an assertion that it necessarily retains a served old history after every swap is unsupported. Concurrent borrowers of that scratch image still need the custody argument in §c.

`host/owner-host.lisp:4271-4276`:
```lisp
         (let* ((cache (fn-scr-prepare-access (fn-owner-access-cache state) owner id))
                (RC (fn-mca-read-span
                      (fn-owner-credits state)
                      (fn-owner-ocfg state) (fn-owner-reader-views state)
                      id start end cache sched (fn-owner-article-slots state)
                      (fn-owner-credit-reserve state) fn-octets fn-arena fn-cat)))
```

`books/group-access-cache.lisp:93-100`:
```lisp
(defun fn-gacc-view (text archive control cache)
  (declare (xargs :guard t))
  (let ((e (fn-gacc-find text cache)))
    (if (and e
             (equal (fn-gacc-archive e) archive)
             (equal (fn-gacc-control e) control))
        (fn-gacc-entry-view e)
      nil)))
```

`books/group-access-cache.lisp:182-199`:
```lisp
(defun fn-gacc-refresh (text archive control old)
  (declare (xargs :guard t))
  (if (and (consp old) (equal (fn-gacc-text old) text))
      (if (and (equal (fn-gacc-archive old) archive)
               (equal (fn-gacc-control old) control))
          old
        (mv-let (found prefix)
          (if (fn-gacc-same-cut-p control (fn-gacc-control old))
              (fn-gacc-prefix (fn-state-articles archive)
                              (fn-state-articles (fn-gacc-archive old)) nil)
            (mv nil nil))
          (if found
              (fn-gacc-entry text archive control
                             (fn-gacc-extend-view text archive prefix
                                                  (fn-gacc-entry-view old)))
            (fn-gacc-entry text archive control
                           (fn-gac-view-entry text archive control)))))
    (fn-gacc-entry text archive control (fn-gac-view-entry text archive control))))
```

`host/bp-receipt-journal-host.lisp:4-12`:
```lisp
(defun fn-bprj-store (state)
 (declare (xargs :stobjs state :mode :program))
 ; The native BP application node owns one Store inside fn-owner.  This
 ; selector is only a callback choice; it never copies that Store into the
 ; standalone bridge global.  Operator-only app-journal commands retain the
 ; legacy standalone source.
 (if (equal (f-get-global 'fn-bprj-store-source state) :owner-bound)
     (f-get-global 'fn-bprj-bound-store state)
   (f-get-global 'fn-store-sn state)))
```

`host/bp-native-app-host.lisp:105-118`:
```lisp
(defun fn-owner-app-bind-receipt-store (state)
  (declare (xargs :stobjs state :mode :program))
  ; An explicit snapshot for this serialized callback.  The caller rebinds
  ; immediately after every owner mutation and before FNRJ preflight/apply;
  ; the standalone fn-store-sn global is never consulted in owner mode.
  (let* ((state (f-put-global 'fn-bprj-bound-store
                              (fn-owner-store state) state))
         (state (f-put-global 'fn-bprj-store-source :owner-bound state)))
    (value :ready)))

(defun fn-owner-app-unbind-receipt-store (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((state (f-put-global 'fn-bprj-store-source :standalone state))
         (state (f-put-global 'fn-bprj-bound-store nil state)))
```

`host/native/bp-app.lisp:34-38`:
```lisp
(defun fnn-bpapp-bind-context (journal request application-result)
  ;; Rebind after the Store transition, then select the one exact committed
  ;; record through ACL2.  The native adapter never enumerates candidates.
  (fnn-bpapp-bind-owner-store)
  (unless (eq (fnn-owner-arena-action 'fn-owner-app-record) :found)
```

`books/owner-reader-view.lisp:61-81`:
```lisp
(defun fn-ocv-capture (views event current)
  (declare (xargs :guard t))
  (cond ((eq event :start)
         (if (consp views) views (list current)))
        ((eq event :next)
         (if (and (consp views) (not (consp (cdr views))))
             (list (car views) current)
           views))
        ((eq event :complete)
         (if (and (consp views) (consp (cdr views)))
             (list (cadr views))
           nil))
        ;; :unnext -- the START-NEXT took nobody: no next batch.
        ((eq event :unnext)
         (if (consp views) (list (car views)) nil))
        ;; :drop -- the START took nobody, or the owner stops.
        (t nil)))

(defun fn-ocv-reader-view (views current)
  (declare (xargs :guard t))
  (if (consp views) (car views) current))
```

`host/owner-host.lisp:5213-5227`:
```lisp
  (if (not (eq (fn-owner-history-reset-status state) :history-reset-clear))
      (value :busy)
   (let* ((oc (fn-owner-ocfg state))
          (o (fn-ocfg-owner oc))
          (st (fn-own-store o)))
    (value (fn-orcp-swap-decision
            (fn-orcp-swap-word count-cap frontier-cap s-cap
                               (fn-sf-records-count (fn-sn-files st))
                               (fn-sf-frontier (fn-sn-files st))
                               st
                               (and (null (fn-own-queue o)) (null (fn-own-pending o))
                                    (null (fn-own-inflight o))
                                    (null (f-get-global 'fn-owner-cat-pending state)))
                               readers)
            oc (nth 1 rebuilt))))))
```

`books/history-capture-state.lisp:14-16`:
```lisp
(defun fn-owner-history-reset-status (state)
 (declare (xargs :stobjs state :guard t))
 (fn-hhc-reset-status (fn-owner-history-capture-slot state)))
```

`books/history-capture-custody.lisp:115-117`:
```lisp
(defun fn-hhc-reset-status (slot)
 (declare (xargs :guard t))
 (if slot :history-source-held :history-reset-clear))
```

`books/owner-recovery-retain.lisp:48-59`:
```lisp
         (next (fn-orcp-swapped-ocfg (fn-owner-ocfg state) oc))
         (swapped (fn-ocfg-owner next))
         (state (f-put-global 'fn-owner-identity-grant nil state))
         (state (fn-owner-authority-proposal-clear state))
         (state (fn-owner-canonical-reset state))
         (state (fn-owner-install-ocfg next state))
         (count (fn-sf-records-count (fn-sn-files (fn-own-store swapped))))
         (state (fn-owner-retain-carry-put (nth 2 rebuilt) state))
         (state (f-put-global 'fn-owner-record-octets (nth 3 rebuilt) state))
         (state (f-put-global 'fn-owner-record-debt (nth 4 rebuilt) state))
         (state (f-put-global 'fn-owner-carried-usage (nth 5 rebuilt) state))
         (state (f-put-global 'fn-owner-sco-base (fn-scka-strip-base e) state))
```

`books/owner-canonical-state.lisp:11-18`:
```lisp
(defun fn-owner-canonical-reset (state)
  (declare (xargs :stobjs state :guard t))
  (let* ((epoch (fn-owner-canonical-epoch state))
         (state (f-put-global 'fn-owner-canonical-state nil state))
         (state (f-put-global 'fn-owner-canonical-pending nil state)))
    ; An invalid prior epoch stays unavailable; it is never silently reused.
    (f-put-global 'fn-owner-canonical-epoch
                  (if (natp epoch) (1+ epoch) :fault) state)))
```

`books/history-image-snapshot.lisp:179-184`:
```lisp
(defun fn-his-release (fn-hrecs$c)
  ; The concrete emptied (the page store's arrays given back): after the
  ; publication has written the image, and after the open's check, the
  ; words of a whole image are not kept.  Decides nothing.
  (declare (xargs :stobjs fn-hrecs$c))
  (fn-hrc-reset 0 fn-hrecs$c))
```

**HOLE: neither existing bounds nor facts invariant supplies H.** Bounds are just natural-and-below-count; `fn-scol-okp` says decided facts equal facts of current bytes. Repeating the same valid row twice satisfies both. A forgotten handle also remains below count. They cannot discharge root disjointness.

`books/store-intern.lisp:194-208`:
```lisp
(defun fn-row-handle-inp (h fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (and (natp (fn-record-payload h))
       (< (fn-record-payload h) (fn-arena-count fn-arena))))

(defun fn-rows-handles-inp (rows fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (cond ((atom rows) t)
        ((fn-held-p (car rows))
         (and (fn-row-handle-inp (car rows) fn-arena)
              (fn-rows-handles-inp (cdr rows) fn-arena)))
        ((fn-hstxa-p (car rows))
         (and (fn-row-handle-inp (fn-hstxa-held (car rows)) fn-arena)
              (fn-rows-handles-inp (cdr rows) fn-arena)))
        (t (fn-rows-handles-inp (cdr rows) fn-arena))))
```

`books/served-columns.lisp:58-73`:
```lisp
(defun fn-scol-row-okp (row fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (or (not (fn-hf-nov (fn-held-facts row)))
      (equal (fn-held-facts row)
             (fn-held-facts-of (fn-nntp-payload-bytes (fn-record-payload row) fn-arena)))))

(defun fn-scol-rows-okp (rows fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (consp rows)
      (and (fn-scol-row-okp (car rows) fn-arena)
           (fn-scol-rows-okp (cdr rows) fn-arena))
    t))

(defun-nx fn-scol-okp (fn-arena fn-cat)
  (and (fn-arena-p fn-arena)
       (fn-scol-rows-okp fn-cat fn-arena)))
```

**WEAK as a substitute root invariant: the existing `fn-arn-store-corr`.** It equates the logical arena with the list of record payloads and has seal/append and seal-many/open theorems. This is useful payload correspondence, but its statement contains neither handle distinctness nor ownership of projected rows, pending readers or leases. It does not establish the proposed root-count condition.

`books/payload-arena.lisp:836-841`:
```lisp
(defun fn-arn-payloads-of (records)
  (declare (xargs :guard t))
  (if (consp records)
      (cons (fn-record-payload (car records))
            (fn-arn-payloads-of (cdr records)))
    nil))
```

`books/payload-arena.lisp:858-879`:
```lisp
; The relation itself is logical (defun-nx): the arena's value against the
; history.  Nothing executes it; a commit and an open establish it by the
; two theorems that follow, and nothing on a served path evaluates it.
(defun-nx fn-arn-store-corr (fn-arena records)
  (equal fn-arena (fn-arn-payloads-of records)))

; Commit: the finished record joins the head of the history and its
; payload is sealed; the relation is kept.
(defthm fn-arn-store-corr-of-commit
  (implies (fn-arn-store-corr fn-arena records)
           (fn-arn-store-corr (fn-arena-seal-list (fn-record-payload record) fn-arena)
                              (append records (list record))))
  :hints (("Goal" :in-theory (enable fn-arena-seal-list))))

; Open: every retained record's payload sealed oldest first from the empty
; arena establishes the same relation a history of commits would have.
(defthm fn-arn-store-corr-of-open
  (fn-arn-store-corr (fn-arn-seal-many (fn-arn-payloads-of records) nil) records)
  :hints (("Goal" :in-theory (enable fn-arena-seal-list))))
```

## (b) Empty payload or named refusal

**Recommendation: logical empty only on the unobservable dead domain; all live host-called reads carry a proved lifetime premise, and the raw boundary fail-stops with a named `forgotten-payload` fault on an impossible dead read. AGREE with the coordinator's safety concern.** Do not translate a kept row's missing payload into `430 no such article`, `423 reclaimed`, or a successful empty article. Actual reclaim remains a tombstone response. This third way needs a logical lifetime carrier (the root/retirement state), a representation relation to the concrete forgotten bit, and a theorem for the checked reader's outcomes. Merely bolting a host predicate onto a total logical reader would leave D27's outputs/effects boundary unproved.

**Cost:** live-domain hypotheses and preservation on reader entry boundaries, checking the concrete marker at raw reads, and named fault propagation before output begins. Keep the ordinary byte-list arena abstraction on its valid domain. **What it breaks:** callers that use a stale handle as an acceptable empty value; callers bypassing the checked boundary; any assertion that all nat/below-count handles are live. It avoids forcing all payload values to become a new sum type, but does not avoid the lifetime proof.

**SOUND: empty and forgotten are indistinguishable in the existing logical payload value.** `fn-arn-payload-listp` accepts octet lists; nil is an octet list, and the test source explicitly seals nil. The record recognizer also admits nil payloads (the witness below), so “all stored records have positive payload length” is not an interface invariant. This is distinct from a legitimate NNTP article with an empty *body*: its headers/separator are still bytes. An FN-RCL2 tombstone cannot be zero length: its recognizer requires at least 145 cells and magic. Reachability of a zero-total-length payload through the live posting admission path is **UNVERIFIED**; it is unnecessary to assume such reachability to show the generic arena/record API cannot use zero as its dead bit.

`books/payload-arena-bytes.lisp:100-105`:
```lisp
(defun fn-arn-payload-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-cbor-octet-listp (car xs))
           (fn-arn-payload-listp (cdr xs)))
    (null xs)))
```

`tests/acl2/payload-arena-tests.lisp:57-66`:
```lisp
                       (let* ((fn-octets (fn-octets-from-list '(4 5) fn-octets))
                              (fn-arena (fn-arena-seal-buffer fn-octets fn-arena)))
                         (mv fn-arena fn-octets))
                       fn-arena)))
         (fn-arena (fn-arena-seal-list nil fn-arena))
         (result (list (fn-arena-count fn-arena)
                       (fn-arena-payload-len 0 fn-arena)
                       (fn-arena-get 0 2 fn-arena)
                       (fn-arena-payload 0 fn-arena)
                       (fn-arena-payload-len 1 fn-arena)
```

`books/records-shape.lisp:264-266`:
```lisp
(defun fn-record-payloadp (octets)
  (and (fn-cbor-octet-listp octets)
       (<= (len octets) *fn-record-max-payload*)))
```

`tests/acl2/records-teeth-tests.lisp:229-237`:
```lisp
; fn-record-p-of-make-is-without-payload: a reachable witness (the witness
; record remade with its own payload, and with none) with both sides true.
(defmacro rec-teeth-remake (payload)
  `(fn-record-make 1 2 3 "<a@example.invalid>" ,payload
                   '("fn.letters" "fn.test") "archive-a" "content-a"
                   "release-a" 4 841000000))
(assert-event (equal (rec-teeth-remake *rec-teeth-payload*) *rec-teeth-record*))
(assert-event (fn-record-p (rec-teeth-remake *rec-teeth-payload*)))
(assert-event (fn-record-p (rec-teeth-remake nil)))
```

`books/reclaim-tombstone.lisp:30-32`:
```lisp
(defconst *fn-rcl-magic* '(0 70 78 45 82 67 76 50))   ; NUL "FN-RCL2"
(defconst *fn-rcl-tombstone-fixed* 145)
(defconst *fn-rcl-article-subject-size* 56)
```

`books/reclaim-tombstone.lisp:49-52`:
```lisp
(defun fn-rcl-tombstonep (payload)
  (declare (xargs :guard t))
  (and (fn-rcl-at-leastp *fn-rcl-tombstone-fixed* payload)
       (fn-rcl-prefixp *fn-rcl-magic* payload)))
```

**WEAK premise in the consultation: ordinary ARTICLE is not demonstrated to return `220` with an empty body here.** Following the reader to its definition: handle bytes call `fn-arena-payload`; the native extent accessor returns nil for `:forgotten`; ARTICLE/HEAD/BODY then require framing including a header/body separator. Nil fails it, so an otherwise valid article identifier gets **503 stored article framing unavailable**. STAT bypasses framing and can still produce **223 retrieved**. A forgotten tombstone loses its tombstone marker, so a direct byte-based STAT can change from reclaimed refusal to success. This is still wrong and hides the true internal fault. A `220 empty` result from another served path is **UNVERIFIED**, and should not be repeated as a found fact.

The Xref compatibility path does not rescue nil: it inserts Xref only when the payload has the separator, then calls the same response-of-bytes function.

`books/nntp-session.lisp:27-37`:
```lisp
(defun fn-nntp-payload-bytes (p fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (natp p)
      (if (< p (fn-arena-count fn-arena))
          (fn-arena-payload p fn-arena)
        nil)
    p))

(defun fn-nntp-article-bytes (article fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (fn-nntp-payload-bytes (fn-article-payload article) fn-arena))
```

`books/payload-arena-extent.lisp:460-475`:
```lisp
(defun fn-arena$x-payload (h fn-arena$x)
  (declare (xargs :stobjs fn-arena$x
                  :guard (and (natp h) (< h (fn-arena$x-count fn-arena$x))
                              (fn-arena$x-wfp fn-arena$x))))
  (let ((e (fn-arena$x-exti h fn-arena$x)))
    (cond ((fn-arn-extentp e)
           (fn-durable-realize-octets (nth 0 e) (nth 1 e) (nth 2 e) (nth 3 e) (nth 4 e) (nth 5 e)))
          ((fn-arn-lz-extentp e)
           (fn-durable-realize-lz (nth 0 e) (nth 1 e) (nth 2 e) (nth 3 e) (nth 4 e) (nth 5 e)
                                  (nth 6 e) (nth 7 e)))
          ((eq e :staged) (fn-arx-stage-payload h fn-arena$x))
          ((eq e :forgotten) nil)
          (t (stobj-let ((fn-arena-paged (fn-arena$x-inner fn-arena$x)))
                        (v)
                        (fn-arena-paged-payload h fn-arena-paged)
                        v)))))
```

`books/nntp-responses.lisp:65-95`:
```lisp
(defun fn-nntp-article-response-of-bytes (session article bytes number kind updatep group)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-nntp-article-idp article))
      (fn-nntp-single session "503 stored article identifier unavailable")
    (if (fn-rcl-tombstonep bytes)
        (fn-nntp-single session (if updatep
                                    "423 article reclaimed"
                                  "430 article reclaimed"))
      (let ((next-session (if updatep
                              (fn-nntp-set-cursor session group number)
                            session)))
        (if (equal kind :stat)
            (fn-nntp-make-result
             next-session
             (list (fn-nntp-reply-effect
                    (fn-nntp-crlf (fn-nntp-retrieval-initial kind number article)))))
          (mbe :logic
               (let ((section (fn-nntp-section-of-bytes bytes kind)))
                 (if (and (fn-nntp-framed-of-bytes bytes)
                          (equal (car section) :ok))
                     (fn-nntp-make-result
                      next-session
                      (list (fn-nntp-reply-effect
                             (append (fn-nntp-crlf (fn-nntp-retrieval-initial kind number article))
                                     (fn-nntp-stuff-lines (car (cdr section)))
                                     '(46 13 10)))))
                   (fn-nntp-single session "503 stored article framing unavailable")))
               :exec
               (let ((acc (fn-nntp-response-block-rev bytes kind)))
                 (if (equal acc :error)
                     (fn-nntp-single session "503 stored article framing unavailable")
```

`books/nntp-responses.lisp:38-48`:
```lisp
(defun fn-nntp-retrieval-initial (kind number article)
  (fn-nntp-append-pieces
   (list (cond ((equal kind :article) (fn-nntp-string-octets "220 "))
               ((equal kind :head) (fn-nntp-string-octets "221 "))
               ((equal kind :body) (fn-nntp-string-octets "222 "))
               (t (fn-nntp-string-octets "223 ")))
         (fn-nntp-decimal-field number) '(32)
         (fn-nntp-string-octets (fn-article-msgid article))
         (cond ((equal kind :article) (fn-nntp-string-octets " article follows"))
               ((equal kind :head) (fn-nntp-string-octets " headers follow"))
               ((equal kind :body) (fn-nntp-string-octets " body follows"))
```

`books/nntp-article-pass.lisp:285-291`:
```lisp
(defun fn-nntp-response-validp (bytes kind)
  (declare (xargs :guard t))
  (if (equal kind :article)
      (and (fn-octet-listp bytes)
           (fn-nntp-blank-linep bytes)
           (fn-nntp-crlf-validp bytes t))
    (fn-nntp-section-validp bytes kind)))
```

`books/nntp-reader-compat.lisp:351-376`:
```lisp
(defun fn-rcompat-served-payload-of-bytes (server article payload)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (consp (fn-xref-pairs article))
           (not (fn-rcl-tombstonep payload))
           (mbe :logic (fn-nntp-split-okp (fn-nntp-split-article payload))
                :exec (and (fn-octet-listp payload) (fn-nntp-blank-linep payload))))
      (append (fn-xref-field server (fn-xref-pairs article))
              (list 13 10)
              payload)
    payload))

(defun fn-rcompat-article-reply-exec (session article number kind updatep group
                                              server fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (let* ((stored-bytes (fn-nntp-article-bytes article fn-arena))
         (served (fn-nntp-article-response-of-bytes
                  session article
                  (fn-rcompat-served-payload-of-bytes server article stored-bytes)
                  number kind updatep group)))
    (if (equal (fn-nntp-result-session served)
               (if (fn-nntp-response-okp-of-bytes article stored-bytes kind)
                   (if updatep (fn-nntp-set-cursor session group number) session)
                 session))
        served
      (fn-nntp-article-response-of-bytes session article stored-bytes
                                         number kind updatep group))))
```

**HOLE beyond ARTICLE: other readers can silently answer inconsistent data.**

| Reader family if a dead handle leaks through | Source-derived effect |
|---|---|
| ARTICLE/HEAD/BODY; XFN-ZARTICLE fallback | Generic framing refusal as above, not an explicit dead-handle fault |
| STAT | May succeed from identifier alone as above |
| OVER / HDR column path | Existing facts can remain valid-looking while `:BYTES`/overview length becomes zero; cached tombstone flags may disagree with byte readers |
| Resumable overview span | Uses stored offsets with `fn-arena-get`; after forgetting, prior length hypotheses need not hold; raw behavior outside guard is not justified by the theorem |
| Checkpoint writer / export / alpha materialization | A below-count handle reads nil; writer source validity accepts its encodable zero length, so silent empty serialization is possible if lifetime protection fails |
| Feed / consumer / BP payload materialization | Re-resolve current roots, then obtain the same bytes; a wrong root yields empty bytes. Exact downstream protocol outcome is reader-dependent; not uniformly 430 or success |

These are conditional bad-state/interleaving consequences, not claims that all are reachable in the current served composition. Wire every such entry through the lifetime relation; do not fix only ARTICLE.

`books/served-columns.lisp:207-219`:
```lisp
(defun fn-scol-nov-overview (article facts fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (let ((nov (fn-hf-nov facts)))
    (if (fn-hnov-ok nov)
        (list :ok
              (fn-record-string-octets (fn-hnov-subject nov))
              (fn-record-string-octets (fn-hnov-from nov))
              (fn-record-string-octets (fn-hnov-date nov))
              (fn-record-string-octets (fn-hnov-msgid nov))
              (fn-record-string-octets (fn-hnov-references nov))
              (fn-nntp-article-length article fn-arena)
              (fn-hf-body-lines facts))
      (list :error))))
```

`books/served-columns.lisp:254-259`:
```lisp
(defun fn-scol-tombstonep (article fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t))
  (let ((facts (fn-scol-facts article fn-cat)))
    (if facts
        (fn-hnov-tomb (fn-hf-nov facts))
      (fn-nntp-article-tombstonep article fn-arena))))
```

`books/served-columns.lisp:348-365`:
```lisp
(defun fn-scol-hdr-content (field article fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard t))
  (let ((facts (fn-scol-facts article fn-cat)))
    (cond ((not facts)
           (fn-nntp-hdr-content field article fn-arena))
          ((fn-nntp-hdr-metadata-tokenp field)
           (list :ok
                 (fn-nntp-decimal-field
                  (if (fn-nntp-keywordp field ":BYTES")
                      (fn-nntp-article-length article fn-arena)
                    (fn-hf-body-lines facts)))))
          ((fn-scol-field-index field)
           (let ((nov (fn-hf-nov facts)))
             (if (fn-hnov-ok nov)
                 (list :ok (fn-record-string-octets
                            (fn-scol-hnov-at (fn-scol-field-index field) nov)))
               (list :error))))
          (t (fn-nntp-hdr-content field article fn-arena)))))
```

`books/nov-span-window.lisp:6-29`:
```lisp

(defun fn-nsw-step-aux (h at left pending fuel acc fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (natp h) (< h (fn-arena-count fn-arena))
                              (natp at) (natp left)
                              (<= (+ at left) (fn-arena-payload-len h fn-arena))
                              (natp fuel) (true-listp acc))
                  :verify-guards nil :measure (nfix fuel)))
  (cond
   ((zp fuel) (mv (revappend acc nil) at left pending 0))
   (pending
    (if (and (not (zp left)) (equal (fn-arena-get h at fn-arena) 10))
        (mv-let (out next rest carry used)
          (fn-nsw-step-aux h (+ 1 at) (- left 1) nil (- fuel 1) acc fn-arena)
          (mv out next rest carry (+ 1 used)))
      ; The pending CR was not paired. Emit its scrubbed SP first; the
      ; unread byte is revisited on the next fuel unit, never swallowed.
      (mv-let (out next rest carry used)
        (fn-nsw-step-aux h at left nil (- fuel 1) (cons 32 acc) fn-arena)
        (mv out next rest carry (+ 1 used)))))
   ((zp left) (mv (revappend acc nil) at left nil 0))
   (t
    (let ((byte (fn-arena-get h at fn-arena)))
      (mv-let (out next rest carry used)
```

`books/store-checkpoint-arena-writer.lisp:164-169`:
```lisp
(defun fn-scka-src-payload (s fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (true-list-fix
   (if (natp s)
       (if (< s (fn-arena-count fn-arena)) (fn-arena-payload s fn-arena) nil)
     s)))
```

`books/store-checkpoint-arena-writer.lisp:185-191`:
```lisp
(defun fn-scka-src-okp (s fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (natp s)
      (and (< s (fn-arena-count fn-arena))
           (fn-scc-nat-encodablep (fn-arena-payload-len s fn-arena)))
    (and (fn-cbor-octet-listp s) (true-listp s)
         (fn-scc-nat-encodablep (len s)))))
```

`books/owner-feed-article.lisp:44-46`:
```lisp
(defun fn-ofa-feed-article (o msgid fn-arena fn-hist)
  (declare (xargs :stobjs (fn-arena fn-hist) :guard t))
  (fn-handle-bytes (fn-apr-feed-article o msgid fn-hist) fn-arena))
```

**Fan-out measurement (static, not proof dependency count).** In `git ls-files books host tests`, `.lisp` files only, case-insensitive exact symbol tokens (symbol constituents `[A-Za-z0-9_$*-]`), including comments, declarations, theorem statements and hints: `fn-arn-payload-listp`: **38 occurrences / 38 lines / 13 files**; `fn-arena-payload`: **193 occurrences / 191 lines / 46 files**; `fn-arena-payload-len`: **77 / 77 / 24**; `fn-arena-get`: **38 / 38 / 16**. These are reproducible text counts, not counts of theorems needing changes. The quoted definitions above identify the symbols measured. A marker inside each logical payload changes the payload-list recognizer and accessor contracts broadly; a separate checked read/lifetime boundary can preserve the byte-value model, but all length/get and stored-compressed consumers must be included, not just the 193 payload mentions.

**SOUND call-chain clarification: export materializes bytes; live inspect-by-ID reports presence.** Export calls `fn-store-sco-encode-chunk`, which calls the record loop; that loop materializes each row with `fn-row-wire-of`. A held row uses `fn-row-bytes`, then `fn-held-wire` reconstructs its record with those bytes. This is a concrete downstream path for a leaked dead handle to become an encoded empty payload. Composite rows instead select their stored transaction in this alpha function; do not assume every row representation reads the arena here.

`host/native/owner.lisp:5355-5365`:
```lisp
                     do (fnn-checkpoint-yield "export" batch)
                        (destructuring-bind (octets-list rest)
                            (fnn-core 'fn-store-sco-encode-chunk cursor +fnn-export-chunk+
                                      (fnn-live-arena))
                          (unless (listp octets-list)
                            (fnn-fault "ACL2 returned a malformed export chunk"))
                          (let ((chunk (mapcar (lambda (octets)
                                                 (cons (fnn-bridge-record-sequence octets) octets))
                                               octets-list)))
                            (fnn-export-step dir fd (fnn-core 'fn-sxp-export-chunk chunk) fault)
                            (incf written (length chunk))
```

`host/store-node-host.lisp:828-838`:
```lisp
(defun fn-store-sco-encode-records-loop (records fn-arena acc)
  (declare (xargs :mode :program :stobjs fn-arena))
  (if (consp records)
      (fn-store-sco-encode-records-loop
       (cdr records) fn-arena
       (cons (fn-rcon-store-event-encode (fn-row-wire-of (car records) fn-arena)) acc))
    (revappend acc nil)))

(defun fn-store-sco-encode-records (records fn-arena)
  (declare (xargs :mode :program :stobjs fn-arena))
  (fn-store-sco-encode-records-loop records fn-arena nil))
```

`host/store-node-host.lisp:873-876`:
```lisp
(defun fn-store-sco-encode-chunk (records n fn-arena)
  (declare (xargs :mode :program :stobjs fn-arena))
  (mv-let (chunk rest) (fn-store-sco-split records n nil)
    (list (fn-store-sco-encode-records chunk fn-arena) rest)))
```

`books/store-intern.lisp:111-129`:
```lisp
(defun fn-row-bytes (h fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (and (natp (fn-record-payload h))
           (< (fn-record-payload h) (fn-arena-count fn-arena)))
      (fn-arena-payload (fn-record-payload h) fn-arena)
    nil))

(defun fn-row-wire-of (row fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (cond ((fn-held-p row) (fn-held-wire row (fn-row-bytes row fn-arena)))
        ((fn-hstxa-p row) (fn-hstxa-stxa row))
        (t row)))

(defun fn-rows-wire-of (rows fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (atom rows)
      nil
    (cons (fn-row-wire-of (car rows) fn-arena)
          (fn-rows-wire-of (cdr rows) fn-arena))))
```

`books/held-record.lisp:238-244`:
```lisp
(defun fn-held-wire (h payload)
  (declare (xargs :guard t))
  (fn-record-make (fn-record-sequence h) (fn-record-txid h)
                  (fn-record-generation h) (fn-record-msgid h) payload
                  (fn-record-groups h) (fn-record-obligation-id h)
                  (fn-record-content-subject h) (fn-record-release-evidence h)
                  (fn-record-charge h) (fn-record-stamp h)))
```

The shared `fn-handle-bytes` helper likewise tests only naturalness/bounds before the arena read; it has no dead-handle test.

`books/payload-arena.lisp:852-856`:
```lisp
(defun fn-handle-bytes (h fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (and (natp h) (< h (fn-arena-count fn-arena)))
      (fn-arena-payload h fn-arena)
    nil))
```

Live `store inspect ID` is different: the native request invokes the presence lookup and passes its boolean to the report decision; it does not fetch article bytes. The legacy raw inspect command opens a store and, after the presence lookup, writes the payload lookup. That payload bridge calls `fn-store-sn-lookup`, whose source uses `fn-handle-bytes`. Thus inspect must be qualified by entry: the live presence report is not evidence that payload reads are sound, while the offline payload path gets a reconstructed arena on open. A reachable forgotten handle in that offline path is **UNVERIFIED**, not a found post-swap response bug.

`host/native/admin.lisp:343-353`:
```lisp
(defun fnn-owner-inspect-request (service msgid)
  "Row S3: `store inspect ID' on the running owner: the owner's own lookup of
ID (the Message-ID table, O(1)) under the owner mutex, answered as ACL2's
word (books/owner-maintenance-request.lisp fn-omr-inspect-word) with the
status fn-omr-inspect-status decides: accepted when found, refused when
absent.  The client renders the offline report from the word."
  (let* ((octets (fnn-octets (fnn-core 'fn-record-string-octets msgid)))
         (found (fnn-owner-serialized
                 service nil (lambda () (and (fnn-bridge-lookup-found-p octets) t))))
         (word (fnn-core 'fn-omr-inspect-word found)))
    (list :reason (fnn-core 'fn-omr-inspect-status word) word)))
```

`host/native/io.lisp:5252-5268`:
```lisp
(defun fnn-command-inspect (root message-id)
  (multiple-value-bind (store records) (fnn-open-live-store root nil)
    (declare (ignore records))
    (unwind-protect
         (let ((msgid (progn
                        ;; Python encodes the Message-ID after opening the
                        ;; store, so a non-ASCII identifier is a usage error
                        ;; only once the store itself opened.
                        (unless (every (lambda (c) (< (char-code c) 128)) message-id)
                          (error 'fnn-usage-error :message "Message-ID is not ASCII"))
                        (fnn-octets (fnn-ascii-octet-list message-id)))))
           (cond ((not (fnn-bridge-lookup-found-p msgid)) +fnn-exit-refused+)
                 (t (write-sequence (fnn-bridge-lookup msgid) *fnn-stdout*)
                    (finish-output *fnn-stdout*)
                    +fnn-exit-ok+)))
      (fnn-store-close store))))

```

`host/native/io.lisp:1826-1828`:
```lisp
(defun fnn-bridge-lookup (msgid)
  (let ((value (fnn-core-arena-state 'fn-store-sn-lookup (fnn-octet-list msgid))))
    (if (null value) (fnn-make-octets 0) (fnn-as-octets value))))
```

`host/native/io.lisp:1863-1866`:
```lisp
(defun fnn-bridge-lookup-found-p (msgid)
  (let ((value (fnn-core-state 'fn-store-sn-lookup-foundp (fnn-octet-list msgid))))
    (cond ((eq value t) t) ((null value) nil)
          (t (fnn-fault "ACL2 returned a non-boolean")))))
```

`host/store-node-host.lisp:1561-1587`:
```lisp
(defun fn-store-sn-lookup (msgid-octets fn-arena fn-hist state)
  (declare (xargs :stobjs (fn-arena fn-hist state) :mode :program
                  :guard (fn-cbor-octet-listp msgid-octets)))
  (if (not (fn-af-message-idp msgid-octets))
      (mv nil nil fn-hist state)
    ; The row's HANDLE through the history stobj's Message-ID answer, not the
    ; acceptance state's article (fn-apr-payload-of-is-the-article-payload,
    ; books/acceptance-payload-ref.lisp: equal at rest under R), and its
    ; bytes read through the arena (books/store-intern.lisp fn-handle-bytes:
    ; no bytes for a handle outside it).
    (let ((store (f-get-global 'fn-store-sn state)))
      (mv-let (fn-hist state) (fn-host-hist-sync store fn-hist state)
        (mv nil (fn-handle-bytes (fn-apr-payload-of (fn-store-octets->string msgid-octets)
                                                    store fn-hist)
                                 fn-arena)
            fn-hist state)))))

(defun fn-store-sn-lookup-foundp (msgid-octets fn-hist state)
  (declare (xargs :stobjs (fn-hist state) :mode :program
                  :guard (fn-cbor-octet-listp msgid-octets)))
  (if (not (fn-af-message-idp msgid-octets))
      (mv nil nil fn-hist state)
    ; fn-apr-foundp-is-article-found (books/acceptance-payload-ref.lisp), under R.
    (let ((store (f-get-global 'fn-store-sn state)))
      (mv-let (fn-hist state) (fn-host-hist-sync store fn-hist state)
        (mv nil (fn-apr-foundp (fn-store-octets->string msgid-octets) store fn-hist)
            fn-hist state)))))
```

## (c) Resurrection and delayed holders

**Recommendation: refuse reseating a handle because it is forgotten (or no longer owned by the reseat operation), not because its byte length is zero.** Make the host-called reseat return a named status, preserve the arena on refusal, and explicitly settle/remove obsolete fenced obligations. Add an ownership precondition for direct reseats and checkpoint reseats too. The swap must either drain fenced members or prove they cannot include its retired handles; do not rely on an undocumented correlation between owner-idle and log-fenced-empty.

**Cost:** a lifetime-aware reseat interface and host propagation, correspondence for the lz/plain/fallback paths, and proofs that delayed operations cannot name a quiet/closed file. **What it breaks:** silent no-op reseat APIs and using length as liveness. Adding only a fenced-empty swap condition would add more reclaim deferrals and would not cover the checkpoint/direct-reseat paths below.

**HOLE: the stated empty search resurrection is real at the function boundary.** `fn-arx-arena-prefixp` answers true when n=0; the search can find such a prefix at its first admissible offset. `fn-arx-commit-extent` constructs a descriptor with the arena payload length, including zero. `fn-arx-commit-reseat` then overwrites the slot. The lz path falls back to this plain path when it cannot make an lz descriptor. A faithful zero-length extent can preserve the logical empty arena while re-naming a file: “keeps the arena” is insufficient to prove non-resurrection of representation resources.

`books/payload-commit-extent.lisp:46-68`:
```lisp
(defun fn-arx-arena-prefixp (h j n tail fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (natp h) (< h (fn-arena-count fn-arena))
                              (natp j) (natp n) (<= n (fn-arena-payload-len h fn-arena)))
                  :measure (nfix (- (nfix n) (nfix j)))))
  (if (or (not (natp j)) (not (natp n)) (<= n j))
      t
    (and (consp tail)
         (equal (car tail) (fn-arena-get h j fn-arena))
         (fn-arx-arena-prefixp h (1+ j) n (cdr tail) fn-arena))))

; The first I in [I, END] where the payload opens (nthcdr I r), walking the
; record's tails; nil when none.
(defun fn-arx-arena-find (h n tail i end fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (natp h) (< h (fn-arena-count fn-arena))
                              (natp n) (<= n (fn-arena-payload-len h fn-arena))
                              (natp i) (natp end))
                  :measure (nfix (- (1+ (nfix end)) (nfix i)))))
  (cond ((or (not (natp i)) (not (natp end)) (< end i)) nil)
        ((fn-arx-arena-prefixp h 0 n tail fn-arena) i)
        ((atom tail) nil)
        (t (fn-arx-arena-find h n (cdr tail) (1+ i) end fn-arena))))
```

`books/payload-commit-extent.lisp:93-107`:
```lisp
(defun fn-arx-commit-extent (h file position r fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (natp h) (< h (fn-arena-count fn-arena))
                              (natp file) (true-listp position) (true-listp r))))
  (let* ((start (nfix (nth 0 position)))
         (n (nfix (nth 1 position)))
         (roff (nfix (nth 2 position)))
         (k (and (equal (nth 3 position) (len r))
                 (<= (+ start *fn-arx-record-at*) roff)
                 (<= (+ roff (len r) *fn-frame-trailer-octets*) (+ start n))
                 (fn-arx-commit-place h r fn-arena))))
    (if (natp k)
        (list (nfix file) start (- n *fn-frame-trailer-octets*)
              (+ roff k) (fn-arena-payload-len h fn-arena) (nfix (nth 4 position)))
      nil)))
```

`books/payload-commit-extent.lisp:148-158`:
```lisp
(defun fn-arx-commit-reseat (h file position r fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (natp file) (true-listp position) (true-listp r))))
  (if (and (natp h) (< h (fn-arena-count fn-arena)))
      (let ((x (fn-arx-commit-extent h file position r fn-arena)))
        (if (and (true-listp x)
                 (fn-arn-extent-guardp (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x) (nth 4 x) (nth 5 x)))
            (fn-arena-reseat-extent h (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x) (nth 4 x) (nth 5 x)
                                    fn-arena)
          fn-arena))
    fn-arena))
```

`books/payload-lz-replay.lisp:257-267`:
```lisp
(defun fn-lzr-commit-reseat (h file position z dicts fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (natp file) (true-listp position) (true-listp z)
                              (fn-lzr-dictsp dicts))
                  :verify-guards nil))
  (let ((e (and (natp h) (< h (fn-arena-count fn-arena)) (fn-cbor-octet-listp z)
                (fn-lzr-extent-of file position z (fn-arena-payload h fn-arena) dicts))))
    (if e
        (fn-arena-reseat-lz-extent h (nth 0 e) (nth 1 e) (nth 2 e) (nth 3 e) (nth 4 e) (nth 5 e)
                                   (nth 6 e) (cdr (assoc-equal (nth 7 e) dicts)) fn-arena)
      (fn-arx-commit-reseat h file position z fn-arena))))
```

**HOLE: the current “refusal” is not by name and the host cannot observe it.** The scalar reseat returns the arena unchanged on failure; the batch returns only the arena. `fnn-log-reseat-fenced` removes the fenced list before calling the batch and ignores its result, then retires plain handles. Merely adding a positive-length test yields an unreported skip, not the coordinator's named refusal. It also refuses the valid empty arena/record values in §b. It can be an optional optimization only after a narrower supported positive-length domain is proved; it is not the correct semantic dead-handle check.

`books/payload-commit-extent.lisp:162-171`:
```lisp
(defun fn-arx-commit-reseats (members fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (atom members)
      fn-arena
    (let* ((m (car members))
           (fn-arena (if (and (true-listp m) (equal (len m) 4) (natp (nth 1 m))
                              (true-listp (nth 2 m)) (true-listp (nth 3 m)))
                         (fn-arx-commit-reseat (nth 0 m) (nth 1 m) (nth 2 m) (nth 3 m) fn-arena)
                       fn-arena)))
      (fn-arx-commit-reseats (cdr members) fn-arena))))
```

`host/native/io.lisp:6845-6861`:
```lisp
  (let ((fenced (fnn-log-with-kernel (log)
                  (prog1 (reverse (fnn-log-fenced log)) (setf (fnn-log-fenced log) nil)))))
    (when fenced
      (let ((arena (fnn-live-arena)))
        (if (fnn-log-lz log)
            ;; KEYSTONE fn-lzr-commit-reseats-keep-the-arena (PRF-326): a
            ;; framed member is re-pointed at its block when the block
            ;; decodes to the handle's payload; any other member takes the
            ;; plain reseat.
            (fnn-call 'fn-lzr-commit-reseats fenced (fnn-lz-dicts) arena)
          (fnn-call 'fn-arx-commit-reseats fenced arena))
        (fnn-arena-retire (mapcar #'first fenced))))
    (let ((due (fnn-arena-release-due)))
      (when due
        (let ((arena (fnn-live-arena)))
          (dolist (entry due)
            (dolist (h (cdr entry)) (fnn-call 'fn-arena-release h arena))))))))
```

**Other path count: ten families**, enumerated below. This count includes safe/rejected candidates; it is not ten demonstrated reachable bugs.

### C1 — recovery replay: SOUND within an incarnation; durability obligation in §e

Replay interns at fresh count through `fn-arx-intern-event`/`fn-arx-cat-intern-extent` (quoted in §a), or list/lz intern. Old process handles are not persistent capabilities. Restart can assign the same natural number to a different canonical payload; “never reused” must therefore be scoped to the current arena incarnation. Recovery must select the rewritten checkpoint and correct suffix, not replay the covered pre-reclaim prefix. It must refuse damaged/missing required history, not resurrect old acceptance by scanning leftovers. The scan selector below separates covered segments from the suffix.

`books/store-log-segments.lisp:243-263`:
```lisp
(defun fn-lgs-open-plan (names first)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (disable fn-lgs-indices fn-lgs-range
                                                            fn-lgs-all-present fn-lgs-below
                                                            fn-lgs-max-index)))))
  (let* ((present (fn-lgs-indices names))
         (top (fn-lgs-max-index present 0)))
    (cond ((atom present)
           ; No segment at all: an init that did not finish (the segment is
           ; init's last step) when no checkpoint names one, else history
           ; short of the checkpoint.
           (if (posp first)
               (list :refused :history-short-of-checkpoint)
             (list :refused :no-segment)))
          ((posp first)
           (if (and (<= first top) (fn-lgs-all-present (fn-lgs-range first top) present))
               (list :scan (fn-lgs-range first top) (fn-lgs-below present first))
             (list :refused :history-short-of-checkpoint)))
          ((not (member-equal 1 present)) (list :refused :checkpoint-damaged))
          ((fn-lgs-all-present (fn-lgs-range 1 top) present)
           (list :scan (fn-lgs-range 1 top) nil))
```

### C2 — checkpoint reload AND delayed checkpoint frame reseat: SOUND durable copying; HOLE without lifetime binding on the reseat

The checkpoint is **written before** the swap, from the **rewritten** rows, then installed durably before old segments are dropped; §e follows the calls. Before-versus-after-swap alone is the wrong distinction. It contains copied canonical payload bytes; it is not a serialized array of old `(file,place)` entries. A pre-reclaim checkpoint cannot be substituted after unlink unless its own retained bytes and suffix cover the required history.

A distinct in-process resurrection is `fn-xrt-reseat-one`: a captured checkpoint frame handle goes directly through the same empty-matching commit reseat. A delayed old frame after forget can change `:forgotten` back to an extent and name the checkpoint file. The frame loop's DONE says the frame lengths parsed, not that every reseat succeeded. Current reader/swap exclusion may rule out particular overlapping publications; that reachability proof is **UNVERIFIED**. The function boundary remains vulnerable and must be part of the non-resurrection theorem.

`books/extent-retire.lisp:101-111`:
```lisp
(defun fn-xrt-reseat-one (h file start end j l fn-octets fn-arena)
  (declare (xargs :stobjs (fn-octets fn-arena)
                  :guard (and (natp file) (natp start) (natp end) (natp j) (natp l)
                              (<= (+ j l) end)
                              (<= (+ end *fn-frame-trailer-octets*) (fn-octets-len fn-octets)))
                  :verify-guards nil))
  (fn-arx-commit-reseat h file
                        (list start (+ end *fn-frame-trailer-octets*) (+ start j) l
                              (fn-arx-trailer-nat-at-buffer end fn-octets))
                        (fn-oct-slice-list j (+ j l) fn-octets)
                        fn-arena))
```

`books/extent-retire.lisp:128-141`:
```lisp
  (if (atom handles)
      (mv t fn-arena)
    (let ((r (fn-sccr-read-nat i end fn-octets)))
      (if (not r)
          (mv nil fn-arena)
        (let ((l (car r)) (j (cdr r)))
          (if (not (and (natp l) (natp j) (<= (+ j l) end)))
              (mv nil fn-arena)
            (let ((fn-arena (if (natp (car handles))
                                (fn-xrt-reseat-one (car handles) file start end j l
                                                   fn-octets fn-arena)
                              fn-arena)))
              (fn-xrt-reseat-frame (cdr handles) file start (+ j l) end
                                   fn-octets fn-arena))))))))
```

### C3 — issued cold read completion: SOUND file ownership; not a handle resurrection

An issued read can finish after a handle is forgotten: its file pin keeps the descriptor open, so it can still read the old bytes. Settlement publishes the checked bytes to the extent cache, **not into EXT[h]** and not directly as an article reply. The command is retried against the then-current owner. Thus reading old bytes before close is not by itself wrong; returning them to a newly resolved reclaimed article would be. Source supports retry and cache settlement, but the complete theorem that connects the retry's root epoch to its wire response remains **UNVERIFIED**.

After-close fd reuse is excluded for these issued rows by the close gate, provided the row lifecycle is followed: cancelled rows remain non-settled and pin the file; completion checks exact token and settles once. These are file pins, not necessarily arena-generation pins. The arena-forget header's claim that every cold worker pinned the generation is too broad.

`host/native/owner.lisp:4530-4539`:
```lisp
       (let ((step (fnn-owner-chunk-span-no-io cid incoming sched)))
         ;; Row A4 (c): the first line needs a page not in memory; its read
         ;; happens off the mutex (fnn-owner-handle-chunk, fnn-owner-cold-line).
         (when (and (consp step) (eq (car step) :fnn-extent-cold))
           (let ((entry (cdr step)))
             ;; Owner->extent lock order: issue at the validated capture,
             ;; before releasing the mutex that excludes file retirement.
             (return-from step
               (values :fnn-extent-cold entry
                       (fnn-owner-cold-issue-locked service cid entry)))))
```

`host/native/owner.lisp:4250-4266`:
```lisp
          (directp (multiple-value-setq (answer settled-io)
                     (fnn-extent-direct-settle worker token verdict)))
          (t (multiple-value-setq (answer settled-io) (fnn-extent-complete-read token verdict))))
    (when hold (fnn-err "PAGE-IO settled token=~s answer=~s" token answer))
    (when (equal mode "duplicate")
      (fnn-err "PAGE-IO duplicate answer=~s"
               (if directp (fnn-extent-direct-settle worker token verdict)
                 (fnn-extent-complete-read token verdict))))
    (when (and token (eq answer :publish))
      (destructuring-bind (id cid file eoff elen trailer) token
        (declare (ignore id cid))
        ;; An unfunded entry carries no ledger charge to release on eviction.
        (multiple-value-setq (cachedp evicted)
          (fnn-extent-cache-store file eoff elen trailer octets (and (not directp) token)))))
    ;; No caller has received RESULT: readiness is a predicate, never a
    ;; borrowing getter. An exceptional transfer keeps the slot and charge.
    (when worker (setf (fnn-cold-worker-result worker) nil))
```

`host/native/owner.lisp:4396-4402`:
```lisp
(defun fnn-owner-cold-line (service cid incoming socket class peerp entry read)
  (declare (ignore entry))
  (multiple-value-bind (word since now limit) (fnn-owner-cold-await service read)
    (case word
      (:serve (fnn-owner-handle-chunk service cid incoming socket class peerp))
      (:unavailable (fnn-owner-unavailable-line service cid incoming since now limit class))
      (otherwise (fnn-owner-resource-unavailable-line service cid incoming word class)))))
```

`books/page-read-ownership.lisp:58-75`:
```lisp
(defun fn-pio-complete (r token verdict)
  (declare (xargs :guard t))
  (if (and (fn-pio-rowp r) (equal token (fn-pio-token r))
           (not (eq (nth 6 r) :settled)))
      (mv (append (fn-pio-token r) (list :settled))
          (cond ((not (eq verdict :ok)) (list :fault verdict))
                ((eq (nth 6 r) :cancelled) :cancelled)
                (t :publish)))
    (mv r :stale)))

(defun fn-pio-file-clear-p (file rows)
  (declare (xargs :guard t))
  (if (atom rows)
      t
    (and (not (and (fn-pio-rowp (car rows))
                   (equal (nth 2 (car rows)) file)
                   (not (eq (nth 6 (car rows)) :settled))))
         (fn-pio-file-clear-p file (cdr rows)))))
```

`host/native/extent.lisp:1228-1245`:
```lisp
  (sb-thread:with-mutex (*fnn-extent-lock*)
    (let ((closed 0) (keep nil)
          (rows (loop for row being the hash-values of *fnn-extent-issued* collect row)))
      (dolist (id ids)
        (if (fnn-core 'fn-pio-file-clear-p id rows)
            (progn
              (fnn-extent-cache-release (fnn-extent-cache-drop-files (list id)))
              (when (and *fnn-extent-lz-last* (eql (first (first *fnn-extent-lz-last*)) id))
                (setq *fnn-extent-lz-last* nil))
              (let* ((word (first (fnn-core-page-read-pool 'fn-owner-page-read-close-preview id)))
                     (fd (gethash id *fnn-extent-fds*)))
                (case word
                  ((:closable :unfunded-offline :stale)
                   (when (and fd (eq word :stale))
                     (fnn-fault "registered incarnation lacks its resource lease"))
                   ;; Any error escapes with the tables/lease intact. The
                   ;; owner fences; ambiguous close never refunds and resumes.
                   (when fd (fnn-close fd) (incf closed))
```

### C4 — `fn-pgs-fill-realize` / frame fill: HOLE in local ownership, global race reachability UNVERIFIED

The function copies fd/base while holding the extent lock and then performs pread after releasing it. It issues no `fn-pio` row and acquires no file lease here. Interleaving: obtain fd; another actor closes the retired file; OS reuses fd; pread reads another object (or fails). Digest validation may reject wrong content, but does not prove descriptor lifetime. It neither re-creates a handle nor re-names EXT, but can re-read a retired file or a reused fd. The frame wrapper calls this exact function. Fix the ownership or prove every call is protected by a declared enclosing lease/generation and cannot overlap close. The history-capture swap gate in §a is helpful but does not by itself cover all callers or ordinary checkpoint retirement.

`host/native/extent.lisp:1145-1159`:
```lisp
(defun fn-pgs-fill-realize (file addr)
  (multiple-value-bind (fd base)
      (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
        (values (gethash file *fnn-extent-fds*) (gethash file *fnn-extent-bases* 0)))
   (let ((octets (make-array 16384 :element-type '(unsigned-byte 8))))
    (unless (and fd (integerp addr) (<= 0 addr))
      (error 'fnn-extent-fault
             :message (format nil "history-page-read: no page file ~a (page ~a)" file addr)))
    (let ((got (fnn-extent-pread fd octets (+ base (* addr 16384)))))
      (unless (= got 16384)
        (let ((path (sb-thread:with-mutex (*fnn-extent-lock* :wait-p t)
                      (gethash file *fnn-extent-paths*))))
          (error 'fnn-extent-fault
                 :message (format nil "history-page-read: page ~a of ~a: ~a of 16384 octets"
                                  addr path got)))))
```

`host/native/extent.lisp:1183-1189`:
```lisp
(defun fn-pgs-fill-frame (file addr sel base pgs-mem)
  (unless (and (member sel '(0 1 2)) (integerp base) (<= 0 base)
               (<= (+ base 2048) (fn-pgs-frame-len sel pgs-mem)))
    (error 'fnn-extent-fault
           :message (format nil "history-page-read: frame ~a at word ~a is outside the page store"
                            sel base)))
  (fn-pgs-frame-put sel base (fn-pgs-fill-realize file addr) pgs-mem))
```

### C5 — peer/feed/pull/web response in flight: SOUND for materialized copies; WEAK universal holder claim

A copied byte vector may finish sending after reclaim; it cannot re-name a handle. Feed lookup reads a current Message-ID under the serialized owner call, then carries output bytes. Pull and web retain the same response plan until rendering completes and unpin in unwind cleanup. A plan containing a lazy cursor is still a holder, unlike an already materialized network buffer. Their generation coverage and the current no-reader swap condition are in §f. BP's bound-Store exception is in §a; do not blanket-classify all BP callbacks as non-holders. Exhaustiveness over every transfer/consumer entry remains **UNVERIFIED**.

`host/native/feed-service.lisp:278-288`:
```lisp
(defun fnn-feed-reply-step (service link octets now)
  "Apply one ACL2-framed reply event, never a host-parsed line."
  (fnn-owner-transit-serialized
   service nil
   (lambda ()
     (let* ((publication (fnn-owner-feed-arena-step 'fn-owner-feed-reply-chunk
                                                    (fnn-feed-link-peer-octets link)
                                                    (fnn-octet-list octets) now))
            (word (fnn-feed-checked-word
                  (fnn-owner-feed-word publication)
                  '(:starttls :tls :auth-user :auth-pass :mode :ready :send :quiet :refused :unsendable :connection-refused :streaming-refused :need-input :closed :invalid :fault)
```

`host/native/pull-service.lisp:282-293`:
```lisp
          (destructuring-bind (plan close starttls consumed &rest more) results
            (declare (ignore starttls more))
            (unwind-protect
                 (loop
                   (multiple-value-bind (octets rest donep yieldedp)
                       (fnn-owner-render-next-quantum service cid plan :transit)
                     (setq reply (concatenate 'fnn-octets reply octets))
                     (when donep (return))
                     (setq plan rest)
                     (when yieldedp
                       (sleep (/ (fnn-core 'fn-splan-cursor-resume-ms) 1000)))))
              (fnn-owner-response-unpin service cid))
```

`host/native/web-host.lisp:114-125`:
```lisp
              (destructuring-bind (plan close starttls consumed &rest more) results
                (declare (ignore starttls more))
                (unwind-protect
                     (loop
                       (multiple-value-bind (part rest donep yieldedp)
                           (fnn-owner-render-next-quantum service cid plan :reader)
                         (setq reply (concatenate 'fnn-octets reply part))
                         (when donep (return))
                         (setq plan rest)
                         (when yieldedp
                           (sleep (/ (fnn-core 'fn-splan-cursor-resume-ms) 1000)))))
                  (fnn-owner-response-unpin service cid))
```

### C6 — plain staged-page retirements: SOUND in both orders, absent an intervening reseat

Release after forget sees neither plain nor lz extent and is identity; forget after release marks the entry and empties the stage again. A staged entry is not freed by plain release. Thus a plain pending handle does not resurrect or re-name a file, and both orders yield the same payload/file-name result. This says nothing about a stale *reseat* interposed between them.

`books/payload-arena-extent.lisp:715-744`:
```lisp
(defun fn-arena$x-release (h fn-arena$x)
  (declare (xargs :stobjs fn-arena$x :guard (natp h)))
  (if (and (< h (fn-arena$x-ext-length fn-arena$x))
           (< h (fn-arena$x-stage-length fn-arena$x))
           (or (fn-arn-extentp (fn-arena$x-exti h fn-arena$x))
               (fn-arn-lz-extentp (fn-arena$x-exti h fn-arena$x))))
      (stobj-let ((fn-arena-page (fn-arena$x-stagei h fn-arena$x)))
                 (fn-arena-page)
                 (resize-fn-arena-page-bytes 0 fn-arena-page)
                 fn-arena$x)
    fn-arena$x))

; The forget (lane arena-forget, 2026-10-03): handle H's entry becomes
; :forgotten -- whatever it was: an extent (its file's count falls by one,
; fn-arx-mark), a staged copy or a resident payload -- and its stage slot is
; emptied.  No read of H reaches a realizer or the child again: its payload
; is the empty one.  A handle outside the arena is left alone.  One entry
; write, one count move, one page resize: no walk.
(defun fn-arena$x-forget (h fn-arena$x)
  (declare (xargs :stobjs fn-arena$x
                  :guard (and (natp h) (fn-arena$x-wfp fn-arena$x))))
  (if (< h (fn-arena$x-count fn-arena$x))
      (let ((fn-arena$x (fn-arx-mark h :forgotten fn-arena$x)))
        (if (< h (fn-arena$x-stage-length fn-arena$x))
            (stobj-let ((fn-arena-page (fn-arena$x-stagei h fn-arena$x)))
                       (fn-arena-page)
                       (resize-fn-arena-page-bytes 0 fn-arena-page)
                       fn-arena$x)
          fn-arena$x))
    fn-arena$x))
```

### C7 — seal/stage/update beyond count: SOUND at guarded exported seals; internal writes are not capabilities

Seal-list/buffer/range/extent choose old count and append the child; a forgotten in-range slot is therefore not reused by them. Stage-write alone only changes a stage page; `:forgotten` remains masked unless some operation changes EXT. Forget checks count and is identity outside it. `fn-arx-mark` can grow EXT and update an arbitrary natural index; it is an internal mechanism, not a proof that host callers may manufacture future slots. Prove the exported call chain and forbid raw bypasses. There is no count-bound hypothesis on the internal mark itself.

`books/payload-arena-extent.lisp:624-649`:
```lisp
(defun fn-arena$x-seal-list (xs fn-arena$x)
  (declare (xargs :stobjs fn-arena$x
                  :guard (and (fn-cbor-octet-listp xs) (fn-arena$x-wfp fn-arena$x))))
  (let* ((h (fn-arena$x-count fn-arena$x))
         (fn-arena$x (stobj-let ((fn-arena-paged (fn-arena$x-inner fn-arena$x)))
                                (fn-arena-paged)
                                (fn-arena-paged-seal-list xs fn-arena-paged)
                                fn-arena$x)))
    (fn-arx-mark h 0 fn-arena$x)))

; The buffer seal STAGES: the child seals the empty payload (keeping the
; handle numbering), the handle is marked :staged and its stage slot holds
; the copy.  The owner's POST prepare seals through here
; (host/native/io.lisp fnn-seal-live-buffer); the commit reseats it
; (fn-arena$x-reseat-extent) once the log made it durable.
(defun fn-arena$x-seal-buffer (fn-octets fn-arena$x)
  (declare (xargs :stobjs (fn-octets fn-arena$x)
                  :guard (fn-arena$x-wfp fn-arena$x)))
  (let* ((h (fn-arena$x-count fn-arena$x))
         (fn-arena$x (stobj-let ((fn-arena-paged (fn-arena$x-inner fn-arena$x)))
                                (fn-arena-paged)
                                (fn-arena-paged-seal-list nil fn-arena-paged)
                                fn-arena$x))
         (fn-arena$x (fn-arx-mark h :staged fn-arena$x))
         (fn-arena$x (fn-arx-stage-grow h fn-arena$x)))
    (fn-arx-stage-write h fn-octets fn-arena$x)))
```

`books/payload-arena-extent.lisp:594-602`:
```lisp
(defun fn-arx-mark (h e fn-arena$x)
  (declare (xargs :stobjs fn-arena$x :guard (natp h)))
  (let* ((fn-arena$x (if (< h (fn-arena$x-ext-length fn-arena$x))
                         fn-arena$x
                       (resize-fn-arena$x-ext (max 64 (* 2 h)) fn-arena$x)))
         (fn-arena$x (fn-arx-files-move (fn-arx-entry-file (fn-arena$x-exti h fn-arena$x))
                                        (fn-arx-entry-file e)
                                        fn-arena$x)))
    (update-fn-arena$x-exti h e fn-arena$x)))
```

### C8 — second reclaim pass while retirements remain: WEAK

Correct roots let a second pass capture only the new row handles; old tagged handles remain pending and need not block new readers after their stamp. But the swap clears the pass/publication-inflight slots before the native drop/reseat/release work completes. Whether a higher native controller serializes a second request throughout that tail is **UNVERIFIED**. Two tails must not overwrite each other's checkpoint/retired-file state or let an old checkpoint frame reseat undo forget (C2). Explicit operation identity plus publication/source ownership is required; an assumed “only one pass” must name its enforced scope.

`books/owner-recovery-retain.lisp:69-76`:
```lisp
         (state (f-put-global 'fn-owner-sco-base-payloads nil state))
         (state (f-put-global 'fn-owner-sco-durable count state))
         (state (f-put-global 'fn-owner-sco-attempted count state))
         (state (f-put-global 'fn-owner-sco-deferred nil state))
         (state (f-put-global 'fn-owner-sco-inflight nil state))
         (state (f-put-global 'fn-owner-orc-pass nil state))
         (state (fn-owner-put-credits (fn-orcp-release (fn-owner-credits state)) state)))
    (value count)))
```

`host/native/owner.lisp:5779-5788`:
```lisp
                   (fnn-reclaim-cut :swapped)
                   (setq word :installed)
                   (let* ((covered (fnn-log-covered-indices store (first position)))
                          (paths (mapcar (lambda (k) (fnn-segment-path-at store k)) covered))
                          (dropped (fnn-log-drop store covered)))
                     (fnn-err "RECLAIM installed records=~d reclaimed=~d dropped=~d ms=~d"
                              count (length (second decision)) dropped (ms))
                     (fnn-owner-release-extents service store *fnn-checkpoint-frames* paths pin))
                   (fnn-reclaim-cut :released)))))
        (when pin (fnn-arena-unpin pin))
```

### C9 — forget twice / same-quantum intern: SOUND primitive idempotence, HOLE in selection if the wrong handle is tagged

Twice-forget does not double-decrement: after the first mark, `fn-arx-entry-file :forgotten` is nil (§g). A subsequent seal gets old count, not h. But nothing in the primitive prevents forgetting the fresh handle just interned in the same quantum; the root/epoch relation must exclude it. Example: count N, intern replacement at N, mistakenly tag N rather than the old handle; the primitive correctly empties the newly published payload. This is a mutation witness for selection, not a reachable legitimate schedule established here.

### C10 — direct plain/lz reseat exports: HOLE unless the lifecycle contract excludes dead handles

These exports accept an in-range h and a well-formed extent; no forgotten/live condition appears. They can replace `:forgotten` with a nonempty descriptor, re-read old bytes and re-name any chosen file. Unlike C2/fenced commit matching, a positive-length test in `fn-arx-commit-extent` does not protect these direct exports. Restrict and prove every caller or make the actual operation check lifecycle. A theorem about the raw forgotten reader alone is not closed under this transition.

`books/payload-arena-extent.lisp:684-691`:
```lisp
; The reseat: handle H's entry becomes the extent (its stage slot, if any,
; stays until the release: a reader that saw :staged still finds its copy).
(defun fn-arena$x-reseat-extent (h file eoff elen poff plen trailer fn-arena$x)
  (declare (xargs :stobjs fn-arena$x
                  :guard (and (natp h) (< h (fn-arena$x-count fn-arena$x))
                              (fn-arena$x-wfp fn-arena$x)
                              (fn-arn-extent-guardp file eoff elen poff plen trailer))))
  (fn-arx-mark h (list file eoff elen poff plen trailer) fn-arena$x))
```

`books/payload-arena-extent.lisp:706-711`:
```lisp
(defun fn-arena$x-reseat-lz-extent (h file eoff elen poff plen trailer n dict fn-arena$x)
  (declare (xargs :stobjs fn-arena$x
                  :guard (and (natp h) (< h (fn-arena$x-count fn-arena$x))
                              (fn-arena$x-wfp fn-arena$x)
                              (fn-arn-lz-guardp file eoff elen poff plen trailer n dict))))
  (fn-arx-mark h (list file eoff elen poff plen trailer n dict) fn-arena$x))
```

## (d) F5 and busy-server progress

**Recommendation: OWN ROW for relaxing the swap**, coordinated as a dependency of any sustained busy-server reclaim claim. Keep this lane's initial safety contract with no other arena reader; separately replace global stobj swapping under old cursors with explicit immutable-version/cursor ownership before weakening that condition.

**Cost:** a separate composition/progress proof and a qualification scenario that keeps old and new readers live through a swap. **What it breaks:** a claim that adding forget alone guarantees reclaim under continuous traffic; it does not require holding this lane's primitive proofs hostage to a larger cursor redesign.

**SOUND F5 effect; WEAK explanation “connections are not identified.”** Connections *are* identified in the response owner alist `(cid . G)`, and duplicate acquisition is rejected. The swap receives only the aggregate reader count minus its own pin, so identities are lost at this decision. Any other live pin gives `:readers`. Eight yields are attempts, not a wait-until-drained guarantee.

`books/response-plan-pins.lisp:30-47`:
```lisp
(defun fn-rpin-step (owners st event)
  (declare (xargs :guard (and (alistp owners) (fn-arpn-okp st))))
  (let* ((id (and (consp event) (consp (cdr event)) (cadr event)))
         (held (fn-rpin-owner id owners)))
    (case (and (consp event) (car event))
      (:acquire
       (if (or (not (natp id)) held)
           (mv owners st :duplicate)
         (mv-let (next g) (fn-arpn-step st '(:pin))
           (mv (cons (cons id g) owners) next :acquired))))
      (:release
       (if (not held)
           (mv owners st :absent)
         (mv-let (next answer) (fn-arpn-step st (list :unpin (cdr held)))
           (if (equal answer :ok)
               (mv (fn-rpin-remove id owners) next :released)
             (mv owners st :inconsistent)))))
      (otherwise (mv owners st :refused)))))
```

`books/owner-reclaim-pass.lisp:156-177`:
```lisp
(defun fn-orcp-swap-word (count-cap frontier-cap s-cap count-now frontier-now s-now idle readers)
  (declare (xargs :guard t))
  (cond ((not (and (equal count-now count-cap) (equal frontier-now frontier-cap)))
         :delta)
        ((not (equal s-now s-cap)) :delta)
        ((not idle) :busy)
        ((not (equal readers 0)) :readers)
        (t :swap)))

; KEYSTONE.  A swap is taken only over exactly the captured Store with no
; other reader: the rebuilt state replaces a state that is the capture, so
; the swapped owner's history is the rewrite of the owner's whole history
; (fn-orcp-swapped-history-is-the-offline-rewrite below).
(defthm fn-orcp-swap-only-over-the-capture
  (implies (equal (fn-orcp-swap-word count-cap frontier-cap s-cap
                                     count-now frontier-now s-now idle readers)
                  :swap)
           (and (equal s-now s-cap)
                (equal count-now count-cap)
                (equal frontier-now frontier-cap)
                idle
                (equal readers 0)))
```

`host/native/owner.lisp:5518-5520`:
```lisp
(defparameter +fnn-reclaim-swap-rounds+ 8
  "Swap quanta a pass tries while the commit pipeline is busy or another
off-mutex reader holds the arena, before it defers by name.")
```

`host/native/owner.lisp:5744-5748`:
```lisp
                   (dotimes (round +fnn-reclaim-swap-rounds+)
                     (let ((sw (fnn-owner-gated (service :control)
                                 (let ((w (fnn-owner-core 'fn-owner-orcp-swap-word count frontier s
                                                          (1- (fnn-arena-reader-count))
                                                          rebuilt)))
```

`host/native/owner.lisp:5770-5778`:
```lisp
                       (case sw
                         (:swap (return))
                         (:delta (deferred :delta) (return-from pass))
                         (:unbound (deferred :unbound) (return-from pass))
                         ((:busy :readers)
                          (when (= round (1- +fnn-reclaim-swap-rounds+))
                            (deferred sw) (return-from pass))
                          (sb-thread:thread-yield))
                         (t (fnn-fault "owner returned a malformed swap word")))))
```

**WEAK starvation claim: one permanently stalled output is timed out, but progress is not guaranteed.** Native mux gives an outgoing window a deadline, faults on its expiry, and its guarded handlers finish the connection, which unpins. However the deadline is renewed for each next window; a long response making progress can hold its plan pin across many windows. Overlapping finite responses can keep count positive forever. Thus “one slow reader always starves reclaim” is too absolute, while “busy traffic can repeatedly defer reclaim” follows directly. No fairness/eventual-swap theorem is supplied by forget.

`host/native/mux.lisp:385-390`:
```lisp
    (setf (fnn-mux-conn-out conn) (fnn-mux-z-out conn (fnn-octets octets))
          (fnn-mux-conn-out-at conn) 0
          (fnn-mux-conn-out-op conn) op
          (fnn-mux-conn-out-deadline conn) (fnn-mux-ticks +fnn-mux-send-seconds+)
          (fnn-mux-conn-after conn) after
          (fnn-mux-conn-want conn) nil)
```

`host/native/mux.lisp:457-466`:
```lisp
        (if plan
            (multiple-value-bind (octets rest donep yieldedp)
                (fnn-mux-render-next loop conn plan)
              (when yieldedp
                (fnn-mux-plan-yield conn rest (fnn-mux-conn-after conn) t)
                (return-from fnn-mux-flush nil))
              (setf (fnn-mux-conn-plan conn) (if donep nil rest)
                    (fnn-mux-conn-out conn) (fnn-mux-z-out conn octets)
                    (fnn-mux-conn-out-at conn) 0
                    (fnn-mux-conn-out-deadline conn) (fnn-mux-ticks +fnn-mux-send-seconds+)))
```

`host/native/mux.lisp:1142-1149`:
```lisp
              ((and (fnn-mux-conn-out conn) (due (fnn-mux-conn-out-deadline conn)))
               ;; fnn-send-all's deadline, in the send's own named scope.
               (fnn-owner-connection-call
                service (fnn-mux-conn-out-op conn)
                (lambda ()
                  (if (fnn-mux-conn-channel conn)
                      (error 'fnn-tls-io-error :detail "operation timed out")
                    (fnn-os-fail sb-posix:etimedout)))))
```

`host/native/mux.lisp:316-333`:
```lisp
(defmacro fnn-mux-guarded ((loop conn) &body body)
  "The worker's handlers (fnn-owner-serve-client before this file), each
ending the connection with fnn-mux-finish."
  (let ((l (gensym "LOOP")) (c (gensym "CONN")) (service (gensym "SERVICE")))
    `(let* ((,l ,loop) (,c ,conn) (,service (fnn-mux-service ,l)))
       (handler-case (progn ,@body)
         (fnn-store-indeterminate (e)
           ;; The shared boundary has already stopped mutation; the cleanup
           ;; must not attempt a later close transition.
           (setf (fnn-mux-conn-cid ,c) nil)
           (fnn-owner-fence-service ,service)
           (fnn-err "owner uncertain; recovery required: ~a" e)
           (fnn-mux-finish ,l ,c))
         (fnn-store-fault (e)
           (let ((faulted-cid (fnn-mux-conn-cid ,c)))
             (setf (fnn-mux-conn-cid ,c) nil)
             (fnn-owner-fault-service ,service faulted-cid e))
           (fnn-mux-finish ,l ,c))
```

`host/native/mux.lisp:268-274`:
```lisp
  (unless (eq (fnn-mux-conn-phase conn) :done)
    (let ((service (fnn-mux-service loop))
          (cid (fnn-mux-conn-cid conn))
          (opened-cid (fnn-mux-conn-opened-cid conn))
          (was (fnn-mux-conn-phase conn)))
      (setf (fnn-mux-conn-phase conn) :done)
      (fnn-owner-response-unpin service (or cid opened-cid))
```

**HOLE if the condition is relaxed on the strength of the three new keystones.** None of those three mentions readers at all, so none silently depends on readers=0; they simply cannot justify the relaxation. Existing `fn-orcp-swap-only-over-the-capture` explicitly concludes `(equal readers 0)`. Native response capture says later cursor quanta use the original catalog. Retired-handle generation safety does not keep an old cursor's catalog sequence number meaningful after replacing `fn-cat` or `fn-hist`. The future root/holder theorem, cursor/version theorem and swap theorem must all be changed together.

`host/native/owner.lisp:4543-4549`:
```lisp
         (unless (fnn-core 'fn-splan-step-p step)
           (fnn-fault "owner returned a malformed served step"))
         ;; Capture the response's lifetime before leaving this quantum.
         ;; Reclaim's swap excludes every live arena reader, including this
         ;; pin while a later cursor quantum still uses the original catalog.
         ;; :await and :redeem keep it too; their plans contain this STEP.
         (fnn-owner-response-pin service cid)
```

## (e) Durable effects and crash gaps

**SOUND observed ordering; HOLE in the note's composed crash claim.** I found no source evidence of old segments being unlinked before the new checkpoint has been written, file-fsynced, renamed and root-directory-fsynced. The missing claim is that the complete host-called lifecycle, including new cuts and every retained source, refines recovery. A label-to-`:new` table is not that proof.

The actual order is:

1. Capture under owner mutex and rotate log; pin the arena (§a/§f).
2. Rewrite captured rows off mutex. Build the checkpoint history image from the prepared rewritten/canonical rows, then make the log durable.
3. Create staging checkpoint; write history image and arena/table frames; fsync the staging file; close its write fd. `:staged` follows.
4. Intern tombstones and rebuild in-memory replacement Store/view/catalog/history. This is not a second durable publication.
5. In one swap quantum: rename staged checkpoint onto checkpoint path; fsync Store root; `:installed`; install owner and catalog/history; recovery barriers; `:swapped` outside the quantum.
6. Unlink each covered old log segment; `drop-unlinked` after each; fsync journal directory; `drop-durable`.
7. Register new checkpoint, reseat retained payload handles to its frames, find quiet retired files, stamp them, test readers and file leases, close qualifying descriptors; `:released`.
8. Proposed forget belongs after successful root un-naming/retirement and before quiet evaluation, with a proved release condition. Its precise placement relative to unlink is **not yet implemented**. The assertion “already unlinked before forget” is true only if the eventual call is placed in the post-drop release work. A `:forgotten` label merely between `:swapped` and `:released` does not specify that order.

Here are the durable calls, including the definitions behind the stage/install wrappers.

`host/native/owner.lisp:5694-5708`:
```lisp
                   (destructuring-bind (setup next n arun)
                       (let ((prepared (fnn-core 'fn-owner-sco-next nil nil configs rows
                                                 (fnn-checkpoint-walk rows) segment
                                                 (fnn-live-arena))))
                         (multiple-value-bind (position2 image2)
                             (if prepared
                                 (fnn-history-image-build
                                  (fnn-core 'fn-sco-records (first prepared))
                                  (first ident) (second ident) position)
                                 (values position nil))
                           (setq image image2)
                           (fnn-core 'fn-owner-sco-setup-of prepared frontier revision position2
                                     segment budget
                                     (fnn-core 'fn-his-stream-free free*
                                               (fnn-history-image-np image)))))
```

`host/native/owner.lisp:5715-5725`:
```lisp
                     (fnn-log-make-durable (fnn-store-log store))
                     (unwind-protect
                          (setq stage (fnn-state-checkpoint-stage
                                       store
                                       (lambda (fd)
                                         (fnn-history-image-write fd image)
                                         (fnn-checkpoint-write-steps
                                          fd setup segment (length rows) (fnn-store-config store)
                                          (fnn-live-octets-pub) arun))))
                       (fnn-octets-pub-release))))
                 (fnn-reclaim-cut :staged)
```

`host/native/io.lisp:2803-2810`:
```lisp
      (handler-case
          (progn
            (fnn-write-staged-at store stage octets
                                 :state-checkpoint-created :state-checkpoint-written
                                 :unlink-on-failure t)
            (setq written t)
            (fnn-at store :state-checkpoint-staged-durable)
            stage)
```

`host/native/io.lisp:3562-3578`:
```lisp
  (let ((fd (fnn-open stage (logior sb-posix:o-wronly sb-posix:o-creat sb-posix:o-excl) #o600))
        (done nil))
    (unwind-protect (progn (fnn-at store created)
                           ;; CONTENTS is a byte vector, or a writer the
                           ;; caller hands in (the owner's checkpoint plan,
                           ;; fnn-plan-write-all: the file's bytes straight
                           ;; from the publication buffer, no vector of the
                           ;; file), written between the same two cuts.
                           (if (functionp contents)
                               (funcall contents fd)
                             (fnn-write-all fd contents))
                           (fnn-at store written)
                           (fnn-fsync-file fd)
                           (setq done t))
      (fnn-close fd)
      (when (and unlink-on-failure (not done))
        (ignore-errors (fnn-unlink stage))))))
```

`host/native/io.lisp:2818-2830`:
```lisp
(defun fnn-state-checkpoint-install (store stage)
  "fnn-state-checkpoint-write's second half: the staged file STAGE renamed
onto the checkpoint name and the root fenced (cuts replaced, durable).  From
the rename on the outcome is uncertain (the old or the new file, never a torn
one: fn-bs-scp-program-crash-is-old-or-new)."
  (handler-case
      (progn
        (fnn-replace stage (fnn-state-checkpoint-path store))
        (fnn-at store :state-checkpoint-replaced)
        (fnn-fsync-dir (fnn-store-root store))
        (fnn-at store :state-checkpoint-durable))
    (fnn-os-error (e)
      (fnn-indeterminate "state checkpoint replacement is indeterminate: ~a" e))))
```

`host/native/io.lisp:7255-7268`:
```lisp
(defun fnn-log-drop (store indices)
  "P-DROP (design 2026-09-27 storage-log section 6): unlink each covered
segment of INDICES (a checkpoint names a later first suffix segment and is
installed), cut drop-unlinked after each, then fence journal/, cut
drop-durable.  A death between unlinks leaves covered segments the next
open's plan names again (fn-lgs-open-plan's DROP), never a segment it scans."
  (when indices
    (dolist (k indices)
      (let ((path (fnn-segment-path-at store k)))
        (when (fnn-lstat path) (fnn-unlink path))
        (fnn-log-at :drop-unlinked)))
    (fnn-fsync-dir (fnn-journal-dir store))
    (fnn-log-at :drop-durable))
  (length indices))
```

`host/native/owner.lisp:4981-4995`:
```lisp
          (fnn-owner-gated (service :control)
            ;; fnn-call answers the values as a list: the quiet set is its
            ;; first (the whole list was taken for the set once, so no
            ;; dropped file ever closed: KEYSTONE fn-xrt-dropped-file-is-
            ;; released says which do).
            (let ((quiet (first (fnn-call 'fn-xrt-quiet-files *fnn-extent-retired*
                                          (fnn-log-member-files (fnn-store-log store))
                                          arena))))
              (unless (and (listp quiet) (every #'integerp quiet))
                (fnn-fault "ACL2 returned a malformed quiet set"))
              (when quiet
                (setq *fnn-extent-pending*
                      (append *fnn-extent-pending* (list (cons (fnn-arena-stamp) quiet)))
                      *fnn-extent-retired* (set-difference *fnn-extent-retired* quiet)))
              (incf closed (fnn-owner-release-pending-extents-locked pin))
```

**Crash matrix (deduced from that order; assumes stated durable filesystem contracts and correct checkpoint bytes):**

| Death gap | Recovery input / required outcome | Can an unlinked segment be required? |
|---|---|---|
| During rewrite/image build/staging write, before staged fsync | Prior checkpoint plus journal; staging candidate ignored/swept | No segment has been dropped by this pass |
| After staged fsync, before install rename | Prior publication; new staging bytes are not the installed publication | No |
| After rename, before root-directory fsync | Treat durability as uncertain; old or new publication under crash model | No drop has happened yet; both retain required journal prefix |
| After root fsync / `:installed`, before memory swap | New checkpoint plus its suffix; killed process's old RAM is irrelevant | No drop yet; restart must not choose old RAM |
| During owner/catalog/history swap, before `:swapped` | Same durable new checkpoint | No; no partial in-memory swap is recovered |
| After swap, during individual segment unlinks, before journal fsync | New checkpoint; remaining covered segments may persist/reappear and are excluded from scan | No, provided new checkpoint's payload pool and suffix binding are self-contained |
| After drop-durable, before forget / partial forget / after forget before quiet | New checkpoint plus suffix, fresh arena | No; old numeric handle identity is not recovered |
| After quiet/stamp, during or after close | Same new durable publication; issued I/O must prevent premature close in the live process | No for recovery; live descriptor safety is a separate obligation |

The ordering obligation is **durably installed, authenticated, self-contained rewritten checkpoint plus the suffix-start/chain binding before any covered segment unlink**. It is not “swap happened” or “forget happened.” If a checkpoint merely retained `(file,place)` references into the dropped segments, this would be a real recovery hole; the present checkpoint writer instead copies arena payload bytes and the loader seals them into a fresh arena.

`books/store-checkpoint-arena-writer.lisp:136-150`:
```lisp
; writer copies it from.  A held row's payload is its handle in the live
; arena (when the handle is sealed; else no octets), any other sealing
; row's is the octet list its wire event carries (a composite's article).
; The writer copies a handle's octets straight from the arena, one
; fn-arena-get per octet (`fn-scka-append-src'), so the arena run is written
; without alpha: the history is never materialized as wire records to write
; it.  One walk of the rows (`fn-scka-srcs-n', in bounded steps) gives the
; lengths and the sources together.

(defun fn-scka-src-of (row w fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (if (and (fn-held-p row) (fn-record-p w))
      (let ((h (fn-record-payload row)))
        (if (and (natp h) (< h (fn-arena-count fn-arena))) h nil))
    (fn-scka-payload-of w)))
```

`books/store-checkpoint-arena-load.lisp:41-57`:
```lisp
(defun fn-scka-seal-n (i end n fn-octets fn-arena)
  (declare (xargs :stobjs (fn-octets fn-arena)
                  :guard (and (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets)) (natp n))
                  :measure (nfix n)
                  :guard-hints (("Goal" :use ((:instance fn-sccr-read-nat-facts))
                                 :in-theory (disable fn-sccr-read-nat-facts)))))
  (if (zp n)
      (mv t i fn-arena)
    (let ((r (fn-sccr-read-nat i end fn-octets)))
      (if (not r)
          (mv nil i fn-arena)
        (let ((j (cdr r)) (l (car r)))
          (if (> (+ j l) end)
              (mv nil i fn-arena)
            (let ((fn-arena (fn-arena-seal-range j (+ j l) fn-octets fn-arena)))
              (fn-scka-seal-n (+ j l) end (1- n) fn-octets fn-arena))))))))
```

`books/store-checkpoint-arena-load.lisp:561-571`:
```lisp
(defun fn-scka-load (plan fn-octets fn-arena)
  (declare (xargs :stobjs (fn-octets fn-arena) :verify-guards nil))
  (let ((o (fn-scka-open-run plan fn-octets)))
    (if (not (eq (car o) :ok))
        (mv o fn-arena)
      (let ((fn-arena (fn-arena-clear fn-arena)))
        (mv-let (ok i fn-arena)
          (fn-scka-seal-n (nth 1 o) (nth 2 o) (nth 3 o) fn-octets fn-arena)
          (if (not ok)
              (mv (list :refused :arena) fn-arena)
            (mv (fn-scka-finish (nth 4 o) (nth 5 o) i (nth 2 o) fn-octets) fn-arena)))))))
```

`host/store-node-host.lisp:633-661`:
```lisp
(defun fn-store-sco-decode-finish (i end fn-octets state)
  (declare (xargs :stobjs (fn-octets state) :mode :program))
  (let* ((load (and (boundp-global 'fn-store-sco-load state)
                    (f-get-global 'fn-store-sco-load state)))
         (state (f-put-global 'fn-store-sco-load nil state))
         (loaded (if (and (consp load) (consp (cdr load)))
                     (fn-scka-finish (car load) (cadr load) i end fn-octets)
                   (list :refused :arena))))
    (if (and (consp loaded) (eq (car loaded) :ok) (consp (cdr loaded)))
        ; The tables mean the capture (fn-sct-capture-of-tables-of-capture):
        ; the 7-tuple the open extends, its event index rebuilt from E.
        (let* ((checkpoint (fn-sct-capture-of-tables (cadr loaded)))
               (state (f-put-global 'fn-store-sco-checkpoint checkpoint state))
               ; PKT-854: the tables' part of the checkpoint digest, only
               ; when `store ROOT digest' asked (fn-store-sco-want-
               ; checkpoint-digest); the arena's part follows the load
               ; (fn-store-sco-note-checkpoint-digest).
               (state (f-put-global
                       'fn-store-sco-tables-digest
                       (and (boundp-global 'fn-store-sco-want-digest state)
                            (f-get-global 'fn-store-sco-want-digest state)
                            (list (fn-sco-sequence checkpoint)
                                  (fn-sckd-tables-digest (cadr loaded))))
                       state))
               ; The F row's log position and frontier (a store's
               ; open starts its scan there: books/store-log-segments.lisp).
               (state (f-put-global 'fn-store-sco-log-position
                                    (list (fn-sct-tables-log (cadr loaded))
                                          (fn-sco-at 2 (fn-sct-tables-f (cadr loaded))))
```

**WEAK “recovery always opens rewritten history.”** Valid checkpoint recovery has that intended result. Corruption, missing required suffix, or a rejected image must yield a named failure when the dropped prefix is no longer available; it cannot promise successful recovery from arbitrary damage. `fn-lgs-open-plan` (quoted in C1) explicitly refuses `:checkpoint-damaged` or `:history-short-of-checkpoint`. The native loader clears rejected checkpoint state. Do not turn fallback-to-full-replay commentary into a guarantee after covered segments are gone.

`host/native/io.lisp:2594-2618`:
```lisp
(defun fnn-state-checkpoint-load (store)
  "Decode the checkpoint into ACL2's global: (values STATUS S) with STATUS
:absent, :refused, :exceeds-bound, :schema (a file of another schema, D34:
the journal replays, `status' says reason=checkpoint-schema), :arena (a file
without the arena run: reason=checkpoint-arena) or :ok, the vocabulary of
fn-scka-select-named."
  (multiple-value-bind (status value)
      (handler-case (fnn-state-checkpoint-plan store)
        (fnn-os-error () (values :refused :io)))
    (case status
      (:absent (fnn-core-state 'fn-store-sco-clear) (values :absent 0))
      (:refused (fnn-core-state 'fn-store-sco-clear)
       (values (case value (:exceeds-bound :exceeds-bound) (:schema :schema) (t :refused)) 0))
      (t (let ((answer (fnn-core-buffer-state 'fn-store-sco-decode value)))
           (if (and (consp answer) (eq (first answer) :arena) (= (length answer) 4)
                    (every (lambda (x) (and (integerp x) (>= x 0))) (rest answer)))
               (multiple-value-bind (st s)
                   (fnn-state-checkpoint-load-arena (second answer) (third answer)
                                                    (fourth answer))
                 (if (and (eq st :ok) *fnn-checkpoint-image*)
                     (fnn-state-checkpoint-adopt-image store s)
                     (values st s)))
               ;; A file without the arena run (tables-only, written before
               ;; the flip) is refused by name: reason=checkpoint-arena.
               (values (if (equal answer '(:refused :arena)) :arena :refused) 0)))))))
```

**SOUND distinction: close is process-local with externally visible resource effects.** EXT/descriptor tables are reconstructed per process; killing the process also closes descriptors. Closing the last descriptor of an unlinked file is exactly what releases disk blocks, as the source comment says. Thus “process-local” does not mean “no externally observable effect,” nor exempt a named death cut from the model. A `:forgotten` cut can have the same durable recovery publication as adjacent cuts while still being a distinct model point.

`host/native/extent.lisp:1194-1206`:
```lisp
;;; Online disk release (lane online-reclaim-2, row Q16, PRF-930;
;;; books/extent-retire.lisp).  A descriptor is no longer held for the
;;; process's life: once a checkpoint publication has reseated the live
;;; payloads at the installed checkpoint's frames, the files it dropped (the
;;; covered log segments, the previous checkpoint) are RETIRED, and a retired
;;; file waits until ACL2 finds it quiet (fn-xrt-quiet-files: its count in
;;; the arena's file column is 0 and no log member in flight names it), is
;;; then pending at the arena-reader generation stamped there, and its
;;; descriptor closes once no off-mutex arena reader pinned at or below that
;;; stamp still runs (fnn-arena-clear-p, books/arena-reader-pins.lisp).
;;; Closing the last descriptor of an unlinked file gives its blocks back
;;; while the owner serves.  host/native/owner.lisp fnn-owner-release-extents
;;; drives it.
```

**HOLE in cut-check coverage; correction to “unlink has no cut.”** Unlink already has `drop-unlinked` and directory durability has `drop-durable`, both in the host and `fn-lgs-drop-program`. However `fnn-log-at` does not validate its supplied name, and the declared log-model list below omits them. The supplied `native_program_check.py` does not generally discover every possible kill: it checks listed programs/cuts, only named host routes, and delegates some route checks. Its own docstring excludes callers/runtime control flow. `fnn-reclaim-cut` is in owner.lisp, whereas this walk's primitive set names `fnn-at`; the top-level reclaim table is not automatically a proof of the native path. Add the new cut and the existing segment/reclaim cuts to the actual checked mapping; test the checker rejects an unmapped kill. Do not claim running this checker certifies close/forget ordering. No checker was run in this consultation.

`books/store-log-segments.lisp:490-495`:
```lisp
(defun fn-lgs-drop-program ()
  (declare (xargs :guard t))
  (list (list :unlink :journal :covered)
        (list :cut "drop-unlinked")
        (list :fsync-dir :journal)
        (list :cut "drop-durable")))
```

`host/native/io.lisp:6284-6287`:
```lisp
(defparameter +fnn-log-model-cuts+
  '("log-written" "log-fenced" "log-truncated" "log-recovered"
    ;; books/store-log-extend.lisp fn-lg-extend-program (fnn-log-ensure-extent).
    "log-extended" "log-extent-fenced"))
```

`host/native/io.lisp:6348-6354`:
```lisp
(defun fnn-log-at (point)
  "A developer-image cut: FN_NATIVE_LOG_FAULT=NAME (a +fnn-log-model-cuts+
name) kills the process at NAME with SIGKILL, so no cleanup runs."
  (let ((armed (fnn-developer-selector "FN_NATIVE_LOG_FAULT")))
    (when (and armed (string= armed (string-downcase (symbol-name point))))
      (sb-posix:kill (sb-posix:getpid) sb-unix:sigkill)
      (fnn-fault "test SIGKILL did not terminate the process"))))
```

`books/owner-reclaim-pass.lisp:214-225`:
```lisp
(defconst *fn-orcp-cuts*
  '(:captured :rewritten :staged :interned :rebuilt :installed :swapped :released))

(defun fn-orcp-cut-outcome (cut)
  (declare (xargs :guard t))
  (cond ((member-eq cut '(:captured :rewritten :staged :interned :rebuilt)) :old)
        ((member-eq cut '(:installed :swapped :released)) :new)
        (t :unknown)))

(defthm fn-orcp-every-cut-is-old-or-new
  (implies (member-equal cut *fn-orcp-cuts*)
           (member-equal (fn-orcp-cut-outcome cut) '(:old :new))))
```

`tools/native_program_check.py:35-44`:
```lisp
It CANNOT decide, and does not claim: runtime control flow -- which arm of a
`handler-case`, `ignore-errors`, `when`/`unless`/`if` runs; every form is read
as executed once, in source order, and a `loop`/`dolist` other than
`fnn-recover`'s barrier loop (expanded to its three lambdas) is read as one
iteration; whether an opaque ACL2 call (`OPAQUE_CALLS`) performs the
transitions it is declared to; what a `funcall` of any other callback or a
function defined outside io.lisp does; operating-system semantics of the
syscalls; that the running image executes the source read here; and
anything in the callers of these functions.  Parsing is a small
s-expression scanner over the defun text: no Lisp reader, no evaluation.
```

`tools/native_program_check.py:70-78`:
```lisp
# Which host function performs which program of books/byte-store-programs.lisp.
# The per-file programs (P-FRONTIER, P-RECORD, P-RECOVER, P-MARKER) went with
# format 8 (lane log-recovery-2, PKT-838); the log route's programs
# (books/store-log-route-programs.lisp, the table's other programs) are
# checked by tests/campaign/native_cuts.py verify_log_route_arms below.
PROGRAM_HOSTS = {
    "fn-bs-finish-program": "fnn-finish",
    "fn-bs-recover-stage-cleanup-program": "fnn-sweep-staging",
}
```

`tools/native_program_check.py:105-107`:
```lisp
SYSCALLS = {"fnn-open", "fnn-write-all", "fnn-fsync-file", "fnn-fsync-regular",
            "fnn-fsync-dir", "fnn-replace", "fnn-link", "fnn-unlink", "fnn-mkdir"}
PRIMITIVES = SYSCALLS | {"fnn-observe", "fnn-at"}
```

## (f) Generation pins, leases and pinned connections

**SOUND pin arithmetic; INSUFFICIENT complete liveness condition.** The literal statements are below. The first says a *released* retirement's stamp is strictly less than every still-live generation. The second retains a pending item if a live generation is **at or below** its stamp, including equality. These prove safe exclusion under the table invariant. They do not identify which handles a reader holds, establish roots no longer name them, include whole-arena leases, or say release/close will eventually be scheduled.

`books/arena-reader-pins.lisp:429-452`:
```lisp
(defthm fn-arpn-release-postdates-every-live-pin
  (implies (and (fn-arpn-okp st)
                (member-equal e (mv-nth 1 (fn-arpn-step st '(:release))))
                (< 0 (fn-arpn-pins-of h (second (mv-nth 0 (fn-arpn-step st '(:release)))))))
           (and (member-equal e (third st))
                (< (car e) h)))
  :hints (("Goal" :in-theory (disable fn-arpn-split fn-arpn-clear-through-p)
                  :use ((:instance fn-arpn-split-released-are-clear
                                   (pend (third st)) (pins (second st)))
                        (:instance fn-arpn-clear-through-below-every-pin
                                   (s (car e)) (pins (second st)))))))

; ... and a retirement some live reader is pinned at or below stays pending.
(defthm fn-arpn-release-keeps-every-covered-retirement
  (implies (and (fn-arpn-okp st)
                (member-equal e (third st))
                (< 0 (fn-arpn-pins-of h (second st)))
                (<= h (car e)))
           (member-equal e (third (mv-nth 0 (fn-arpn-step st '(:release))))))
  :hints (("Goal" :in-theory (disable fn-arpn-split fn-arpn-clear-through-p)
                  :use ((:instance fn-arpn-split-keeps-every-unclear
                                   (pend (third st)) (pins (second st)))
                        (:instance fn-arpn-clear-through-below-every-pin
                                   (s (car e)) (pins (second st)))))))
```

**SOUND same-mutex-section rule.** Pin before retire gets current G; retire stamps S=current and increments current. So G=S is protected. Pin after retire gets S+1 and must take only new roots. A mutex alone does not make that last property true: the order of acquiring the source and pinning matters. A late reader of an unrebuilt old view can get G>S and is not covered. The old-root-acquisition counterexample is precisely what the absent root/projection relation must exclude.

`books/arena-reader-pins.lisp:211-226`:
```lisp
(defun fn-arpn-step (st ev)
  (declare (xargs :guard (fn-arpn-okp st)))
  (let ((cur (first st)) (pins (second st)) (pend (third st)))
    (case (and (consp ev) (car ev))
      (:pin (mv (list cur (fn-arpn-pin-at cur pins) pend) cur))
      (:unpin (let ((g (and (consp (cdr ev)) (cadr ev))))
                (if (and (natp g) (fn-arpn-held-p g pins))
                    (mv (list cur (fn-arpn-unpin-at g pins) pend) :ok)
                  (mv st :refused))))
      (:retire (let ((items (and (consp (cdr ev)) (cadr ev))))
                 (if (true-listp items)
                     (mv (list (+ 1 cur) pins (cons (cons cur items) pend)) cur)
                   (mv st :refused))))
      (:stamp (mv (list (+ 1 cur) pins pend) cur))
      (:release (mv-let (rel keep) (fn-arpn-split pend pins)
                  (mv (list cur pins keep) rel)))
```

`books/arena-reader-pins.lisp:151-154`:
```lisp
(defun fn-arpn-clear-through-p (s pins)
  (declare (xargs :guard (and (natp s) (fn-arpn-pinsp pins))))
  (or (atom pins)
      (< s (caar pins))))
```

**WEAK integration: no retirement stamp at today's swap.** The current swap sequence quoted in §a installs the owner/columns and barriers without a tagged retirement. `fnn-arena-stamp` is currently called after quiet-file detection; `fnn-arena-retire` is used for fenced staged pages. Proposed forget needs its own retirement in the same root-publication quantum. The pass's own capture pin would keep its tagged retirements pending unless it releases/re-pins after discarding every old-row/old-entry alias; do not exempt it with clear-except while it can still use those aliases. Re-pinning without relinquishing the old data merely lies to the table.

`host/native/io.lisp:6806-6825`:
```lisp
(defun fnn-arena-retire (items)
  "ITEMS (a list) taken away from the arena now: pending at the stamp ACL2
answers, released by fnn-arena-release-due."
  (let ((s (fnn-arena-pins-step (list :retire items))))
    (unless (integerp s) (fnn-fault "ACL2 returned a malformed arena stamp"))
    s))

(defun fnn-arena-stamp ()
  "A stamp for a retirement the caller keeps itself (the generation
advances): release it once (fnn-arena-clear-p S)."
  (let ((s (fnn-arena-pins-step '(:stamp))))
    (unless (integerp s) (fnn-fault "ACL2 returned a malformed arena stamp"))
    s))

(defun fnn-arena-clear-p (s &optional own)
  "Whether no reader is pinned at or below the stamp S; OWN, when given, the
asking reader's own pin, not counted."
  (let ((answer (fnn-arena-pins-step (if own (list :clear-except s own) (list :clear s)))))
    (when (eq answer :refused) (fnn-fault "ACL2 refused an arena clear test"))
    answer))
```

**HOLE for whole-arena leases.** Neither `fn-arf-apply-released` nor the primitive forget takes either lease ledger. `fn-arpn-step` also has no lease argument. The leases' own release/reset checks are real, but they do not check forget. The note says their native drivers are not loaded; the inspected raw build load list names owner/extent but contains no payload-view/recovery-payload-view driver load. This is an absence finding from the complete file search, not proof that every possible transitive/raw path is unreachable. Treat native lease absence as **UNVERIFIED** until a closed-world image check establishes it, or include the lease state in the actual forget decision. In particular the payload-view slot carries a prefix and acquire identity; it is not automatically an arena-generation pin.

`books/payload-view-lease.lisp:30-57`:
```lisp
(defun fn-pvl-livep (token s)
  (declare (xargs :guard t))
  (and (fn-pvl-ledgerp s)
       (fn-pvl-token-matchp token (fn-omk-at 0 (fn-omk-at 2 s)))))
(defun fn-pvl-acquire (s prefix capture-ticket resource-lease)
  (declare (xargs :guard t))
  (cond ((not (and (fn-pvl-ledgerp s) (natp prefix)
                   (natp capture-ticket) resource-lease))
         (list :refused :payload-view-domain s))
        ((fn-omk-at 2 s) (list :refused :payload-view-busy s))
        ((and (natp (fn-omk-at 1 s))
              (<= capture-ticket (fn-omk-at 1 s)))
         (list :refused :payload-view-spent-ticket s))
        (t (let ((token (list :payload-view (fn-omk-at 0 s)
                             prefix capture-ticket)))
             (list :acquired token
                   (list (fn-omk-at 0 s) capture-ticket
                         (list token resource-lease)))))))
(defun fn-pvl-release (s token settlement)
  (declare (xargs :guard t))
  (cond ((not (fn-pvl-livep token s)) (list :refused :payload-view-stale s))
        ((not (eq settlement :joined)) (list :retained :cleanup-pending s))
        (t (list :released token
                 (list (fn-omk-at 0 s) (fn-omk-at 1 s) nil)))))
(defun fn-pvl-reset (s)
  (declare (xargs :guard t))
  (cond ((not (fn-pvl-ledgerp s)) (list :refused :payload-view-domain s))
        ((fn-omk-at 2 s) (list :refused :payload-view-live s))
```

`books/recovery-payload-view.lisp:25-48`:
```lisp
(defun fn-rpv-ownedp (s) (declare (xargs :guard t))
  (if (fn-omk-at 3 s) t nil))
(defun fn-rpv-livep (s token) (declare (xargs :guard t))
  (and (fn-rpv-ledgerp s) (fn-rpv-token-matchp token (fn-omk-at 0 (fn-omk-at 3 s)))))
(defun fn-rpv-acquire (s prefix source maintenance) (declare (xargs :guard t))
  ; RSA token is (:recovery-source ticket process-epoch ack-serial).
  (let ((ticket (fn-omk-at 1 source)))
    (cond ((not (and (fn-rpv-ledgerp s) (natp prefix)
                     (fn-omk-widthp source 4)
                     (eq (fn-omk-at 0 source) :recovery-source)
                     (natp ticket) maintenance)) (list :refused :recovery-view-domain s))
          ((fn-rpv-ownedp s) (list :refused :recovery-view-busy s))
          ((and (natp (fn-omk-at 2 s)) (<= ticket (fn-omk-at 2 s)))
           (list :refused :recovery-view-spent s))
          (t (let ((token (list :recovery-payload-view (fn-omk-at 1 s) prefix ticket)))
               (list :acquired token
                     (list :recovery-payload-view-ledger (fn-omk-at 1 s) ticket
                           (list token source maintenance))))))))
; Only the host's atomic same-row RoleReleasableP/RoleReturn composition
; invokes this transition. There is no supplied joined argument.
(defun fn-rpv-release (s token) (declare (xargs :guard t))
  (if (not (fn-rpv-livep s token)) (list :retained :recovery-view-stale s)
    (list :released token
          (list :recovery-payload-view-ledger (fn-omk-at 1 s) (fn-omk-at 2 s) nil))))
```

`host/native/build.lisp:425-432`:
```lisp
        (load "host/native/crypto.lisp")
        (fnn-crypto-initialize)
        (load "host/native/io.lisp")
        ;; D40: the raw-dispatched entries, from the fn-interfaces table of
        ;; this world (an unknown or unverified target stops the build).
        (fnn-install-raw-dispatch)
        ; The payload arena's extent realizer (A-DURABLE-EXTENT; PRF-281).
        (load "host/native/extent.lisp")
```

`host/native/build.lisp:508-520`:
```lisp
        ; The writable NNTP owner.  It registers the `owner' verb and calls
        ; only host/owner-host.lisp wrappers for protocol and state decisions.
        (load "host/native/owner-control-turn.lisp")
        (load "host/native/owner.lisp")
        (load "host/native/receiver-parser-turn.lisp")
        ; Its connections on a fixed set of I/O loops (PKT-605).
        (load "host/native/mux.lisp")
        ; The outbound feed is a lifecycle extension of that same owner.  The
        ; public operator activates it; the developer-only low-level owner
        ; entry retains its separate diagnostic surface.
        (load "host/native/feed-service.lisp")
        ; The NEWNEWS pull feed, the same owner's other lifecycle extension.
        (load "host/native/pull-service.lisp")
```

**SOUND response-plan multiplicity at the table layer.** `fn-rpin-step` (§d) binds cid to its captured generation, and its funded-ownership theorem bounds owned response pins by actual generation counts. Under that relation the generation release theorem covers these plans. It is not a proof that every native continuation retains the pin until its final use.

`books/response-plan-pins.lisp:94-100`:
```lisp
(defthm fn-rpin-step-preserves-funded-ownership
  (implies (and (fn-arpn-okp st)
                (<= (fn-rpin-count-at h owners)
                    (fn-arpn-pins-of h (second st))))
           (let ((next (fn-rpin-step owners st event)))
             (<= (fn-rpin-count-at h (mv-nth 0 next))
                 (fn-arpn-pins-of h (second (mv-nth 1 next))))))
```

**SOUND re-pin of every owner connection in the list; WEAK “every continuation replaced.”** `fn-orcp-swapped-owner` maps the repin function over all `fn-own-conns live`. `fn-own-served-conn` supplies the rebuilt owner's live view; `fn-served-repin` replaces archive/index/buckets/control if that live view exists. It preserves wire/session fields, and it cannot reach native response plans held outside that connection record. A mid-response cursor is protected today because its response generation pin blocks the swap (§d), not because repinning rewrites that external cursor. A mid-command wire continuation does not automatically equal a payload holder; its row-bearing actor/continuation custody still requires an exhaustive proof. A missing rebuilt live view makes `fn-served-repin` identity, so prove its presence from admissibility rather than ignoring that branch.

`books/owner-reclaim-pass.lisp:333-349`:
```lisp
(defun fn-orcp-repin-conn (owner conn)
  (declare (xargs :guard t))
  (let* ((sconn (fn-served-repin
                 (fn-own-served-conn owner conn (fn-own-conn-live-session owner conn))))
         (pinned (fn-served-conn-pinned sconn)))
    (fn-own-conn-make-group-indexed (fn-own-conn-id conn)
                                    (fn-served-pinned-version pinned)
                                    (fn-served-pinned-frontier pinned)
                                    (fn-served-conn-wire sconn)
                                    (fn-served-conn-session sconn)
                                    (fn-served-conn-archive sconn)
                                    (fn-own-conn-config conn)
                                    (fn-own-conn-observation conn)
                                    (fn-served-conn-verdicts sconn)
                                    (fn-served-conn-index sconn)
                                    (fn-served-conn-group-index sconn)
                                    (fn-served-conn-control sconn))))
```

`books/owner-reclaim-pass.lisp:360-366`:
```lisp
(defun fn-orcp-repin-conns (owner conns)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (if (consp conns)
                  (cons (fn-orcp-repin-conn owner (car conns))
                        (fn-orcp-repin-conns owner (cdr conns)))
                nil)
       :exec (fn-orcp-repin-conns-loop owner conns nil)))
```

`books/owner.lisp:1838-1847`:
```lisp
(defun fn-own-served-conn (o conn session)
  (declare (xargs :guard t))
  (fn-served-make-conn-live (fn-own-conn-wire conn) session
                            (fn-own-conn-archive conn) (fn-own-conn-config conn)
                            (fn-own-conn-observation conn) (fn-own-clock o)
                            (fn-own-conn-verdicts conn) (fn-own-conn-index conn)
                            (fn-own-conn-group-index conn) (fn-own-conn-control conn)
                            (fn-served-pinned-make (fn-own-conn-version conn)
                                                   (fn-own-conn-frontier conn) nil)
                            (fn-own-view-live (fn-own-view o))))
```

`books/served.lisp:1196-1215`:
```lisp
(defun fn-served-repin (conn)
  (declare (xargs :guard t))
  (let ((live (fn-served-conn-live conn)))
    (if (not live)
        conn
      (fn-served-make-conn-live
       (fn-served-conn-wire conn)
       (fn-served-repin-session (fn-served-conn-session conn)
                                (fn-served-live-archive live))
       (fn-served-live-archive live)
       (fn-served-conn-config conn)
       (fn-served-conn-observation conn)
       (fn-served-conn-injection conn)
       (fn-served-live-verdicts live)
       (fn-served-live-index live)
       (fn-served-live-buckets live)
       (fn-served-live-control live)
       (fn-served-pinned-make (fn-served-live-version live)
                              (fn-served-live-frontier live) t)
       live))))
```

**HOLE: release scheduling is independent of safe release.** Today's native due-item polling is in fenced completion; unpin alone only updates the table. A quiet server that retires while its own pin remains live, later unpins, and performs no further COMPLETE may never apply tagged forgets unless new wiring adds a release trigger. File pending-close retries exist, but they cannot make a still-named file quiet before forget. Required progress theorem: after last relevant holder ends, a scheduled bounded release quantum applies eligible forgets, recomputes relevant quiet candidates, and drives close without needing a new POST. The note's proposed re-pin can help only after the pass actually drops its old aliases.

`host/native/io.lisp:6801-6804`:
```lisp
(defun fnn-arena-unpin (g)
  "The reader pinned at G ended."
  (unless (eq (fnn-arena-pins-step (list :unpin g)) :ok)
    (fnn-fault "ACL2 refused an arena unpin at generation ~a" g)))
```

`host/native/io.lisp:6831-6835`:
```lisp
(defun fnn-arena-release-due ()
  "The pending retirements ACL2 releases now, ((S . ITEMS) ...)."
  (let ((due (fnn-arena-pins-step '(:release))))
    (unless (listp due) (fnn-fault "ACL2 returned a malformed arena release"))
    due))
```

`host/native/io.lisp:6856-6861`:
```lisp
        (fnn-arena-retire (mapcar #'first fenced))))
    (let ((due (fnn-arena-release-due)))
      (when due
        (let ((arena (fnn-live-arena)))
          (dolist (entry due)
            (dolist (h (cdr entry)) (fnn-call 'fn-arena-release h arena))))))))
```

## (g) The new concrete entry kind and all inspected consumers

**SOUND direct entry dispatch, conditional on correspondence.** The lane explicitly handles `:forgotten` in logical entry view and all three concrete byte accessors: length=0, get=0, payload=nil. Thus those branches do not fall through to resident child bytes. `get=0` is not a valid way to serve old spans: a well-guarded get requires i below the now-zero length; a stale raw caller is outside that proof domain.

`books/payload-arena-extent.lisp:172-180`:
```lisp
(defun fn-arx-entry (e x s)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((fn-arn-extentp e) (fn-durable-octets (nth 0 e) (nth 3 e) (nth 4 e)))
        ((fn-arn-lz-extentp e)
         (fn-lzr-lz-value (nth 7 e) (fn-durable-octets (nth 0 e) (nth 3 e) (nth 4 e)) (nth 6 e)))
        ((eq e :staged) (fn-arx-stage-octets s))
        ((eq e :forgotten) nil)
        (t x)))

```

`books/payload-arena-extent.lisp:427-475`:
```lisp

(defun fn-arena$x-payload-len (h fn-arena$x)
  (declare (xargs :stobjs fn-arena$x
                  :guard (and (natp h) (< h (fn-arena$x-count fn-arena$x))
                              (fn-arena$x-wfp fn-arena$x))))
  (let ((e (fn-arena$x-exti h fn-arena$x)))
    (cond ((fn-arn-extentp e) (nth 4 e))
          ((fn-arn-lz-extentp e) (nth 6 e))
          ((eq e :staged) (fn-arx-stage-len h fn-arena$x))
          ((eq e :forgotten) 0)
          (t (stobj-let ((fn-arena-paged (fn-arena$x-inner fn-arena$x)))
                        (n)
                        (fn-arena-paged-payload-len h fn-arena-paged)
                        n)))))

(defun fn-arena$x-get (h i fn-arena$x)
  (declare (xargs :stobjs fn-arena$x
                  :guard (and (natp h) (< h (fn-arena$x-count fn-arena$x))
                              (fn-arena$x-wfp fn-arena$x)
                              (natp i) (< i (fn-arena$x-payload-len h fn-arena$x)))))
  (let ((e (fn-arena$x-exti h fn-arena$x)))
    (cond ((fn-arn-extentp e)
           (fn-durable-realize-octet (nth 0 e) (nth 1 e) (nth 2 e) (nth 3 e) (nth 4 e) (nth 5 e) i))
          ((fn-arn-lz-extentp e)
           (fn-oct-nth i (fn-durable-realize-lz (nth 0 e) (nth 1 e) (nth 2 e) (nth 3 e) (nth 4 e)
                                                (nth 5 e) (nth 6 e) (nth 7 e))))
          ((eq e :staged) (fn-arx-stage-get h i fn-arena$x))
          ((eq e :forgotten) 0)
          (t (stobj-let ((fn-arena-paged (fn-arena$x-inner fn-arena$x)))
                        (v)
                        (fn-arena-paged-get h i fn-arena-paged)
                        v)))))

(defun fn-arena$x-payload (h fn-arena$x)
  (declare (xargs :stobjs fn-arena$x
                  :guard (and (natp h) (< h (fn-arena$x-count fn-arena$x))
                              (fn-arena$x-wfp fn-arena$x))))
  (let ((e (fn-arena$x-exti h fn-arena$x)))
    (cond ((fn-arn-extentp e)
           (fn-durable-realize-octets (nth 0 e) (nth 1 e) (nth 2 e) (nth 3 e) (nth 4 e) (nth 5 e)))
          ((fn-arn-lz-extentp e)
           (fn-durable-realize-lz (nth 0 e) (nth 1 e) (nth 2 e) (nth 3 e) (nth 4 e) (nth 5 e)
                                  (nth 6 e) (nth 7 e)))
          ((eq e :staged) (fn-arx-stage-payload h fn-arena$x))
          ((eq e :forgotten) nil)
          (t (stobj-let ((fn-arena-paged (fn-arena$x-inner fn-arena$x)))
                        (v)
                        (fn-arena-paged-payload h fn-arena-paged)
                        v)))))
```

**Consumer audit.**

| Consumer | Verdict on new kind |
|---|---|
| `fn-arena$xcorr` / `fn-arx-view` | Uses the updated entry abstraction; no forgotten-to-resident fallback there. Does not carry live-root ownership |
| EXT file column / mark | `fn-arx-entry-file` yields nil for marker; move decrements prior natural file only |
| Release staged page | Both extent recognizers false for marker; returns unchanged, safe (§c C6) |
| Plain/lz reseat | Overwrites marker without lifetime check: fail-open ownership hole (§c C10) |
| Commit/checkpoint reseat `fn-xrt-*` | Does not case-split EXT; uses logical payload matching, so zero-empty resurrection (§c C2) |
| Raw compressed export `fn-arena-stored` | Non-lz default is nil; forgotten silently falls back to ARTICLE, not a named dead-read fault |
| Checkpoint writer | Does not inspect entry kind; zero length/empty bytes look encodable (§b) |
| Ordinary export/inspect through rows/alpha | Same payload accessor erases the distinction; no separate kind check established |
| Quiet-file scan | Reads count and log-named set only; correct unnamed arithmetic, not permission to close against untracked readers |

The direct EXT consumers found by source search are in `payload-arena-extent.lisp` plus `fn-arena-stored` in native extent.lisp; proofs also mention its logical field. This is a textual consumer inventory, not an image-world completeness theorem. The export and inspect entry distinctions are followed in §b. Exhaustiveness over every operator entry and each downstream fault mapping remains **UNVERIFIED** and must be checked before wiring.

`books/payload-arena-extent.lisp:749-760`:
```lisp
(defun fn-arena$xcorr (fn-arena$x fn-arena$a)
  (declare (xargs :verify-guards nil))
  (and (fn-arena$xp fn-arena$x)
       (fn-arx-files-agree (nth *fn-arena$x-exti* fn-arena$x)
                           (nth *fn-arena$x-filesi* fn-arena$x))
       (fn-arn-payload-listp fn-arena$a)
       (<= (len (nth *fn-arena$x-inner* fn-arena$x)) (len (nth *fn-arena$x-exti* fn-arena$x)))
       (equal (fn-arx-view 0 (len (nth *fn-arena$x-inner* fn-arena$x))
                           (nth *fn-arena$x-exti* fn-arena$x)
                           (nth *fn-arena$x-inner* fn-arena$x)
                           (nth *fn-arena$x-stagei* fn-arena$x))
              fn-arena$a)))
```

`books/payload-arena-extent.lisp:550-553`:
```lisp
(defun fn-arx-files-move (old new fn-arena$x)
  (declare (xargs :stobjs fn-arena$x))
  (let ((fn-arena$x (if (natp old) (fn-arx-files-dec old fn-arena$x) fn-arena$x)))
    (if (natp new) (fn-arx-files-inc new fn-arena$x) fn-arena$x)))
```

`host/native/extent.lisp:1122-1131`:
```lisp
(defun fn-arena-stored (h fn-arena)
  (let ((e (and (integerp h) (<= 0 h)
                (< h (fn-arena$x-ext-length fn-arena))
                (fn-arena$x-exti h fn-arena))))
    (if (fn-arn-lz-extentp e)
        (list (nth 7 e)
              (fn-durable-realize-octets (nth 0 e) (nth 1 e) (nth 2 e)
                                         (nth 3 e) (nth 4 e) (nth 5 e))
              (nth 6 e))
      nil)))
```

`books/extent-retire.lisp:276-286`:
```lisp
(defun fn-xrt-quiet-files (retired named fn-arena$x)
  (declare (xargs :stobjs fn-arena$x
                  :guard (and (nat-listp retired) (true-listp named))
                  :verify-guards nil))
  (mbe :logic
       (cond ((atom retired) nil)
             ((and (not (member (car retired) named))
                   (equal (fn-arx-file-count (car retired) fn-arena$x) 0))
              (cons (car retired) (fn-xrt-quiet-files (cdr retired) named fn-arena$x)))
             (t (fn-xrt-quiet-files (cdr retired) named fn-arena$x)))
       :exec (fn-xrt-quiet-files-loop retired named fn-arena$x nil)))
```

**SOUND count delta; WEAK memory claim.** Already forgotten/staged/resident slots name no natural file, so no file count changes; file-backed slots decrement their own file exactly once under correspondence. Forget does not shrink EXT or count, nor free the packed resident child's bytes: its body only marks EXT and resizes the stage slot. The resident seal puts bytes in the child (§c C7). Therefore “EXT entry returned” means its old descriptor/reference is replaced, not that the arena slot/storage is returned. RSS reduction is not established by these theorems. A per-page live count is a separate representation/cost change; returning one stage array does not prove allocator/OS RSS falls.

**HOLE to avoid:** a default for an *unknown* malformed entry still treats it as resident (`t x` / child). `:forgotten` is explicitly handled, so this is not a newly demonstrated marker bug, but a fail-stop boundary should reject impossible entry kinds rather than widen the trusted raw domain.

## (h) What the note misses; minimum proof and native refutation

**HOLE: DEF-HOLDER is a proposal, not a theorem dependency at this revision.** The sibling says “Nothing landed yet” and describes the instance it “will land.” The arena-forget book includes only arena-reader-pins and payload-arena, and its `GEN` line is a comment. The parked ghost machine does encode roots disjoint from pending forget handles and requires a take to be a subset of roots; those are the hard hypotheses, not facts established for native state. Its header says later lemmas were not tried. Replacing this with a macro does not discharge host-root/source ownership.

`build/codex/c08/def-holder.md:3-6`:
```lisp
Worktree /Users/ember/dev/fn/build/lanes/def-holder, branch lane/def-holder from origin/dev 4aa332295.
Deliverable 1 (this file, section 1-3): the resource/holder inventory from source and the interface
sketch, for the coordinator's Codex consultation and for ARENA-FORGET. Nothing landed yet.

```

`build/codex/c08/def-holder.md:197-201`:
```lisp
3. The payload-handle instance for ARENA-FORGET: `(def-holder fn-handle-holds :resource (natp :ordered t)
   :holders ((reader ... fn-arpn's pin/unpin) (response-plan ...)) :lease (fn-pvl-livep fn-rpv-livep)
   :named-by (<rows name h> <reclaim install un-names the old handle>))' and the composed theorem that a
   released handle is unnamed and unheld: ARENA-FORGET cites it as the precondition of fn-arena-forget
   where fn-arena-release is called today. I provide the theorem; ARENA-FORGET owns the export.
```

`books/arena-forget.lisp:32-46`:
```lisp
; The liveness relation itself -- a released handle is named by no row and
; held by no reader, response plan or whole-arena lease -- is DEF-HOLDER's
; payload-handle instance (build/coordinator/lanedumps/def-holder.md section
; 4, instance 3: rows + generation + leases); this book owns what the
; release DOES and cites that theorem as its precondition.
; GEN: def-holder fn-handle-holds
;
; A LATE holder -- a read of a handle after its forget, by a holder that did
; not pin -- reads the EMPTY payload through no realizer and no descriptor
; (fn-arena-forget-payload; the concrete entry is :forgotten,
; books/payload-arena-extent.lisp): never a closed or reused file.

(in-package "ACL2")
(include-book "arena-reader-pins")
(include-book "payload-arena")
```

`build/codex/c08/arena-forget-ghost.lisp.txt:1-4`:
```lisp
; ARENA-FORGET's hand ghost machine (sections 2-3 cut from books/arena-forget.lisp, 2026-10-03).
; Everything up to fn-arf-split-acc-kept-holder-pend-ok was REPL-admitted on persvati; the
; holder-level lemmas after the marker were written and NOT yet tried (persvati's disk filled).
; Superseded by DEF-HOLDER's instance 3 unless the coordinator says otherwise.
```

`build/codex/c08/arena-forget-ghost.lisp.txt:65-77`:
```lisp
(defun fn-arf-inv (m)
  (declare (xargs :guard t :verify-guards nil))
  (let ((st (nth 0 m)) (roots (nth 1 m)) (rs (nth 2 m)) (f (nth 3 m)) (n (nth 4 m)))
    (and (fn-arpn-okp st)
         (natp n)
         (true-listp f)
         (fn-arf-below-p roots n)
         (fn-arf-below-p f n)
         (fn-arf-below-p (fn-arf-pend-handles (third st)) n)
         (fn-arf-disjointp roots f)
         (fn-arf-disjointp roots (fn-arf-pend-handles (third st)))
         (fn-arf-pinned-p rs (second st))
         (fn-arf-holders-ok rs f (third st)))))
```

`build/codex/c08/arena-forget-ghost.lisp.txt:113-119`:
```lisp
      (:take (let ((hs (and (consp (cdr ev)) (cadr ev))))
               (if (subsetp-equal hs roots)
                   (list (fn-arf-pins-st st '(:pin))
                         roots
                         (cons (cons (first st) hs) rs)
                         f n)
                 m)))
```

Other omitted obligations, established by the constructions and quoted source above:

* **Actual response semantics:** the empty read is not uniformly 220/430; framing refusal, STAT success, cached metadata and persistence writers diverge (§b).
* **Status propagation:** silently unchanged reseat is not a named refusal, and the fenced list is removed before that result is considered (§c).
* **Canonical versus live handles:** checkpoint canonical numbering and arena clear/reopen are different incarnations. Retired items need an epoch or proof that all old tables are destroyed before reuse (§e/C1).
* **Alias lifetime versus container lifetime:** repinning the owner connection does not rewrite an external native cursor; cache identity and old-reader views matter (§a/§f).
* **Progress:** pin safety is not eventual release; no later POST should be required. Deferred/failed passes also allocate fresh tombstone handles before a swap and have no compensating forget in the inspected failure path. Repeated `:delta`/`:readers` retries can accumulate unserved arena entries; prove safe disposal of those abandoned allocations after their holders end. The driver interns before the swap loop and its failure cleanup removes staging/finishes the pass without undoing the arena (`host/native/owner.lisp:5726-5729`: “`(setq rows (fnn-owner-reclaim-intern service rows keyring generation))`”; `:5794-5798`: “`(ignore-errors (fnn-unlink stage))`”, “`(fnn-owner-core 'fn-owner-orcp-finish)`”).
* **Bounded release work:** one O(1) forget does not bound a due list of all reclaimed handles or root-count rebuild publication work. Make application/retry resumable and keep pending ownership until applied; exhausting a quantum must not drop its tail. `fn-arf-apply-items` / `fn-arf-apply-released` recurse to exhaustion (quoted above). No matched cost evidence is supplied here.
* **Failure after partial apply:** pins-step `:release` removes pending entries before the host applies them (§f). A fault/quantum yield between item applications needs a retained due-work owner; otherwise forgotten work may be lost or repeated. Idempotent forget helps retry, but does not itself retain the remaining work.

### Ordered proof requirements before host wiring

These are recommendations, not assertions that the proofs already exist. Each is motivated by the source-backed holes above.

1. **Specify lifetime and roots in ACL2.** Define handle incarnation, active root ownership/counts, covered projections, row/cursor/lease holders, retired-but-unapplied work and forgotten state. Prove a read-authorized handle is not forgotten; distinguish zero bytes from dead.
2. **Establish the relation at actual open/replay/checkpoint producers.** Prove fresh seals/bounds and canonical numbering, including composite events, duplicates/retries and empty payloads. Do not introduce an unchecked host-supplied H flag.
3. **Preserve it at every writer in §a.** In particular prove the host-called successful rewrite/intern/rebuild/swap un-names exactly the retired handles; all installed projections and reader views agree; a failed/deferred pass cannot leak or publish its fresh allocations. Prove position-parallelism if the retirement selector still relies on it.
4. **Compose actual source acquisition with pins and leases.** Every off-mutex old handle has a pin at G≤S or an explicit lease; every G>S acquisition reads only current roots. Cover response cursors, whole-arena views, BP bound Store, cold file reads, page-fill/frame callbacks, and the pass's own re-pin. Add a closed-world entry/holder check rather than trusting comments.
5. **Certify concrete forget and its boundary, with teeth.** The three statements, correspondence, guard verification, count preservation and idempotence; positive full-antecedent witnesses, hypothesis-removal witnesses and separate corrupted-state/mutation witnesses. Include no-file entries and file id 0. Prove `fn-scol-okp` and the broader served relation survive unnamed forget.
6. **Prove non-resurrection and checked-reader outcomes for every actual caller.** Plain/lz/direct/checkpoint reseats cannot transition forgotten→live or name a retired/closed file; legitimate empty payloads remain supported. Named refusal/fault is observed by the native call chain. If logical empty is retained, prove boundary equivalence only on the live domain and model the fault effect outside it.
7. **Prove crash composition and resource settlement.** Self-contained durable rewritten checkpoint and suffix binding precede unlink; every declared kill point has recovery semantics; partial forget/due application is safe; close is protected by all file holders and cannot be retried after ambiguous OS close without recovery. The broad handler in `fnn-owner-release-extents` currently catches `serious-condition` and logs continuation (`host/native/owner.lisp:5011-5012`: “`(serious-condition (e)`”, “`CHECKPOINT release failed (files stay retired): ~a`”). Its interaction with the close comment's “ambiguous close never refunds and resumes” (`host/native/extent.lisp:1243-1245`) must be resolved in the actual exception protocol, not assumed safe.
8. **Prove bounded progress under explicit fairness assumptions.** After the last relevant holder ends, release work runs without another commit, returns disk once all kept payloads are reseated, and retains ownership across yields/faults. State the no-reader swap limitation until F5's own row is complete. Certify affected roots and their includers; then qualify the matching native image. No REPL admission or successful byte-output test substitutes for these proofs.

### Native tests that can refute the design

The note's broad “reads running, fd closed, file unlinked, df/RSS back, no restart” test is useful, but **insufficient**: reads merely between quanta do not exercise an old reader alive through the swap; df/RSS do not detect wrong data; successful close does not demonstrate descriptor-reuse safety; no restart cannot validate crash recovery.

Use a deterministic multi-phase scenario with byte-for-byte expected responses and resource identities:

1. Store several large distinct articles in one segment, a cross-post, a duplicate/retry, a withdrawn article, a tombstone, and a legitimate zero-byte arena/record fixture through an appropriate supported lower-level test entry. Keep some articles and reclaim others. Warm one response/cache and leave another cold. Check kept ARTICLE bytes, STAT, OVER/HDR lengths, reclaimed-by-number/Message-ID replies, export and the checkpoint/reopen payloads.
2. Hold an OVER cursor after capture, and hold a cold read after issued-row registration but before pread return. Request reclaim. With today's swap contract it must defer by name and forget nothing. When F5 is relaxed, that old cursor must still read its exact old snapshot until release; a new reader must see the new root.
3. Release the cursor but retain the cold issued row; allow swap/drop/forget. Prove by observations the cold row holds the old fd until return/cancellation joins. Force late, cancelled, duplicate and stale completions; then aggressively reuse OS descriptor numbers. Verify no bytes go to the wrong response and no settled handle is reseated by completion.
4. Separately hold `fn-pgs-fill-realize` after fd acquisition; trigger retirement/close attempts. This specifically targets F1, which an issued cold-read test does not cover.
5. Delay fenced reseat and checkpoint-frame reseat until after the target's retirement; verify named stale/forgotten handling, unchanged marker and zero file-name count. Exercise both plain/lz and direct-reseat guards. Then apply plain page release and forget in both orders, forget twice, and attempt wrong freshly interned handle selection as a mutation test.
6. Hold each whole-arena lease; attempt forget, then release it. Keep a stale reader-view/BP/cache projection in a deliberate corruption test: demand a named fault, never a plausible article answer. Distinguish these from reachable production schedules.
7. Kill at every gap in §e, including checkpoint rename-before-directory-fsync, each unlink, before/after individual forget items, quiet/stamp, and close. Reopen and compare the complete retained history and payload bytes; corrupt the installed checkpoint after covered-segment drop and demand named recovery refusal. Do not accept a generic successful exit.
8. After the final holder releases, send **no new posts**. Disk release must still progress. Repeat failed/deferred and successful reclaim passes with long overlapping finite responses; verify pending work and fresh abandoned intern allocations do not accumulate. Measure disk blocks, open descriptors, stage/cache/child allocations and RSS separately under matched conditions.

**Consultation disposition:** repair the root/lifetime and resource-boundary composition, retain the useful forget primitive, and then wire it. The supplied files do not require an Ember policy decision; the uncertainty is in implementation/proof coverage.

## 8. Revision after c05 (binding)

### 8.1 The forget is never the staged-page release

`host/native/io.lisp:6856-6861` releases the staged copy of every reseated member on every COMPLETE; those
handles stay named. That call site and `fn-arena-release` are unchanged. Forget items exist only as
`(:forget H)`, and the only producer is `fn-arf-retire-event`, called once per reclaim swap with the
handles `fn-arf-changed-handles` answers. Made theorems, not conventions (slice 2):

- `fn-arf-apply-released-of-plain-items-is-identity`: a released retirement whose items are naturals (what
  `fnn-log-reseat-fenced` retires) leaves the logical arena equal (`fn-arf-items-handles` of a nat-list is
  nil, so with `fn-arf-apply-released-payload` every payload is kept).
- `fn-arf-forget-items-come-from-the-swap`: over the pins step, every `(:forget H)` item that `:release`
  answers was retired by a `(fn-arf-retire-event HS)` event with `H` in `HS` (the pins step keeps items
  verbatim: `fn-arpn-release-postdates-every-live-pin` gives membership in PEND; PEND only grows by
  `:retire ITEMS`). Host closure: `fnn-arena-retire` is called with naturals only, and
  `fnn-arena-retire-forget` (new) is the only caller with tagged items: a `reach_check`/host grep gate.

### 8.2 Liveness: no reachable root names H (last name, all roots)

The precondition becomes: at the swap's stamp, H is named by no root the owner can reach after the swap,
and every root captured before the swap is covered by a pin at or below the stamp. Roots, each with how it
is discharged:

| root | after the swap | discharge |
|---|---|---|
| Store records, view archive/verdicts/trie, `fn-cat`, `fn-hist`, `fn-owner-sco-base` (replay index) | rebuilt from NEW rows | `fn-arf-changed-handles-are-unnamed` + the distinctness root fact |
| connection archives / indexes | re-pinned from the rebuilt view (`fn-orcp-repin-conn` → `fn-own-served-conn` live branch) | same theorem, through `fn-orcp-swapped-owner`'s conns (to prove: every conn's archive is the rebuilt view's) |
| OVER cursors / response plans | swap word `:readers` excludes them | the swap-word keystone `fn-orcp-swap-only-over-the-capture` (`readers = 0`) |
| off-mutex readers (publication, export, dry run) | excluded by `:readers` | same |
| the pass's own captured OLD rows and checkpoint writer sources | pinned at `pin`, below the stamp | the retirement is stamped after `pin` and released only after the pass unpins |
| fenced / in-flight / pending log members | swap word tests the owner's queue/pending/inflight, NOT the host's `fnn-log-fenced`/`-inflight` | NEW: the retirement waits for the next COMPLETE's reseat (retire after `fnn-log-reseat-fenced` drains), or the swap word gains "no host log member"; plus 8.4 (a forgotten fenced handle is never reseated) |
| BP workflow node (`fn-workflow-state`'s node slot, `books/bp-workflow.lisp:308-320`) | NOT touched by the swap | OPEN: it carries a Store whose records name handles. Either the swap rebinds the workflow node to the swapped Store in the same quantum, or prove every workflow read re-resolves through the owner's arena by Message-ID. Must be decided before wiring. |
| `fn-bprj-bound-store` (old Store by pointer until the next BP callback) | not touched | rebound before every BP use (`bp-app.lisp:19,37,89,111,305`): show no read through it between swap and rebind, or clear it in the swap |
| `fn-owner-access-cache` (entries keyed by the old archive) | not touched | clear in the swap quantum (one assignment) |
| `fn-owner-reader-views` | not tested | add to the swap word's idle test |
| NEWNEWS tail, consumer remote-visible writer | unwired today (no issuer: `host/...remote-visible`, "No public export or issuer exists") | declared in the root list; the def-holder world-walk must refuse wiring them without a hold |
| whole-arena leases `fn-pvl`/`fn-rpv` | drivers not loaded | the forget event refuses while either is live (one slot test each) |

So the root fact is no longer "the old rows' handles are distinct" alone: it is distinctness over the union
of every kept root's names. The roots the swap rebuilds collapse to the rows; the kept roots are either
excluded by the swap word, rebound/cleared in the swap quantum, or OPEN (the BP workflow node).

### 8.3 Logical invalidation is separate from physical release

Logical: `fn-arena-forget` makes EXT[H] `:forgotten` and frees H's staged page (volatile memory only).
Physical: this design returns disk ONLY by closing the last descriptor of an already-unlinked WHOLE file
(the dropped log segments, the previous checkpoint). No hole punch, no extent reuse, no allocator inside a
live file: the log is append-only and checkpoints are replaced whole, so a place P is never rewritten while
its inode exists, and the inode's blocks return only at the last close, which already waits for every issued
cold-read row naming the file (`fn-pio-file-clear-p`, `extent.lisp:1232`) and every page-file pin
(`:read-file-held`). A cold read's (file, place) custody is therefore covered by the existing file-level
custody. Stated as a constraint in PRF-1235's scope ("no place inside an open file is reused"); a later
design that reuses places owes Astra's per-place custody and is out of this lane.

### 8.4 No resurrection

`fn-arx-commit-reseat-leaves-an-empty-handle` (REPL-admitted): a forgotten handle has no place in any
record, so neither the COMPLETE's reseat nor the checkpoint frame reseat re-names a file through it. Still to
check (coordinator's list): recovery replay and checkpoint reload rebuild the arena from the installed
publication, which no longer contains the reclaimed rows' old handles (fresh arena, handles renumbered) —
the forget is volatile and nothing about it is replayed; a late cold-read completion publishes into the
extent cache keyed by (file, eoff, elen, trailer), never into EXT (`owner.lisp:4258-4263`), and its
continuation re-runs the line against the re-pinned connection; a peer transfer in flight resolves by
Message-ID under the mutex.

### 8.5 Named refusal (coordinator's lean, adopted)

A read of a forgotten handle must answer a named refusal, not the empty payload. Logical value stays `nil`
(no `:logic` change, whole-tree fan-in avoided); the refusal is concrete: `fn-arx-forgotten-p H` (one EXT
read) is checked by every host read entry before it serves bytes (`fnn-owner-handle-chunk`'s arena reads,
the feed render, BP outbound), answering `:forgotten` by name, with a theorem that under the 8.2 invariant
the check never fires on a served path (so it is a guard against wiring errors, not a behaviour).

### 8.6 Crash ordering

Existing order (`owner.lisp:5756-5786`): install (commit point) → swap → drop/unlink covered segments →
release. The forget is volatile and goes at or after `:swapped`, before `:released`; new cut `:forgotten`
with recovery outcome "the new publication" (same as `:swapped`). Physical release (fd close) is after the
durable install at every cut; unlink happens only for segments the installed checkpoint covers. A kill at
`:forgotten` loses only volatile state. The crash model's `close` exemption covers the fd close; the unlink is
the existing modelled `drop-*` cut.

### 8.7 Slice plan, changed

2. (now) theorems 8.1; `fn-arf-retire-event` as the sole tagged producer; `fn-scol-okp-of-forget`
   (written, admit after certs); certify the closure (run-20261002T221425Z-b22f in flight).
3. Root fact over the union of roots (8.2): distinctness of handles across Store records ∪ view ∪ `fn-cat`
   ∪ `fn-hist` as a carried relation sibling of `fn-scol-okp`; the rebuilt roots theorem; swap-word
   additions (host log members, reader views); swap-quantum clears (access cache, bound store).
   BLOCKED on a decision: the BP workflow node (8.2) — I propose the swap rebinds it.
4. Concrete named refusal (8.5).
5. Host wiring + `:forgotten` cut + native (unchanged goal: fd closed, file unlinked, df/RSS back, no restart).
6. Resident memory (section 6).
DEF-HOLDER's instance is cited where it exists; this lane no longer assumes F4's three-clause relation.

## DECISION (coordinator + Astra agreed, 2026-10-03; ember not needed, may overturn)
Wire the forget only after the eight ordered proof requirements in Astra's section h. Specifically:
(a) Option B: a carried per-handle NAME COUNT over the declared roots, computed in the rebuild walk and
published atomically with the rebuilt roots, with projection theorems for aliases (pairwise distinctness
is false across catalog/history/view rows). (b) Host-called reads carry a proved live-handle premise and
the raw boundary FAIL-STOPS with a named forgotten-payload fault: never an empty article, never 430/423.
(c) Refuse resurrection by LIFECYCLE status ("forgotten / not owned by this reseat"), not by zero length,
on every reseat path (fn-arx-commit-place, fn-xrt-reseat-one's delayed checkpoint-frame handles, the
direct reseat exports). (d) F5 is its own row. (e) Specify the :forgotten cut relative to unlink and
prove the host lifecycle's crash composition. (f) Release is scheduled by the root count and the
whole-arena leases, not by the pin counter alone. Native refutation: Astra's eight phases.
New rows, live on dev: deferred reclaim leaks sealed tombstone payloads (owner.lisp:5726-5729 vs
:5792-5799) -> ARENA-FORGET, first; close errors swallowed against their protocol (extent.lisp:1243-1244
vs owner.lisp:5011-5012) -> Astra (t43).

## Astra's view (c10): the BP workflow node at the reclaim swap (gpt-6-astra, read-only at lane/arena-forget 6a91ff1d6, 211 s)

### Liaison fact-check (codex-liaison-11, 2026-10-03)
- CONFIRMED, and it is a defect on dev independent of the forget: reclaim's holder context has NO BP slot content.
  fn-rcl-store-holders (books/store-reclaim-holders.lisp:78-87) returns (list nil <consumer cursors> nil nil): reader pins,
  feeds and BP are literally nil; the verdict's :held-bp-obligation arm tests only that nil list
  (books/store-reclaim.lisp:275), and neither store-reclaim.lisp nor store-reclaim-pack.lisp nor expiry.lisp consults the
  retention ledger (fn-retain-*). The header (:15-23) still says reclaim is "offline (refused while an owner runs)" and BP
  is "open (PRF-088)" -- stale since the online reclaim pass landed. So an expired article with an outstanding :forward
  retention pin can be reclaimed; a later workflow attempt re-reads it from its node (bp-outbound.lisp:67-90) and would
  build its ADU from a tombstone (Astra: ADU validation accepts payload octets, bp-adu.lisp:102-122; not checked by me).
- NOT CHECKED by me: the answer-1 chains (bp-release rebind operation, FNBS wire copies, ION reread), and the
  additional-roots list in 3 (14 globals; Astra marks served reachability UNVERIFIED for the continuation families).
Liaison's reading: REBIND is the right mechanism (the job state holds Message-IDs, not handles; enqueued FNBS jobs own wire
copies), but it is SAFE only once reclaim respects canonical BP retention pins -- which it does not today. The retention pin,
not a new workflow holder, is the holder; it is unbounded in time by design (released by receipt or durable abandon only).

### Astra's answer (verbatim)

REBIND SAFE IF reclaim excludes every live BP source dependency and replay no longer needs reclaimed bytes; NOT established today.

1. Rebind the node, preserving work/config/receipts/pending/fence/transaction IDs; the existing operation is
`host/bp-release-owner-host.lisp:99-105` → `books/bp-release.lisp:136-140`. Do not retain the entire old node indefinitely.
Work holds Message-ID/subject/obligation IDs, not an arena handle (`books/bp-workflow.lisp:125-147`).
`host/native/bp-obligation.lisp:44-59,152-191` serializes replay, construction and publication;
`host/workflow-host.lisp:217-225` → `books/bp-outbound.lisp:67-90` resolves in that workflow node.
A later workflow attempt reconstructs bytes, so replacing its article with a tombstone changes its request.
There is no tombstone exclusion at that read; ADU validation accepts payload octets (`books/bp-adu.lisp:102-122`).
Already-enqueued FNBS jobs instead own wire copies: `bp-obligation.lisp:225-227` (under host/native/),
`books/bp-node-job-offer.lisp:30-46`; resend/fragmentation uses that wire (`host/native/bp-service.lisp:519-527,549-573`).
Transport/custody observations do not themselves release the Store pin; receipts match work metadata
(`books/bp-workflow.lisp:213-227`), then canonical release commits and syncs (`host/native/bp-obligation.lisp:91-124`).
ION is an extra rereader: `host/native/workflow.lisp:409-440` constructs ADU then validates the observation;
`host/workflow-host.lisp:318-325` and `books/bp-ion-workflow.lisp:41-62` reread the article.
Restart begins with today's node (`host/bp-release-owner-host.lisp:10-24`), replays historical ION gates
(`books/bp-ion-workflow.lisp:142-190`), then suppresses replayed submit effects. Post-release replay equivalence
is UNVERIFIED: historical routes precede receipts/waivers and can still request payload. A live-work pin alone is insufficient for that proof.

2. The retention pin SHOULD be the holder, but currently is not connected to reclaim:
`host/native/owner.lisp:5674-5678` → `host/owner-host.lisp:1038-1042` → `books/expiry-instant.lisp:20-22`
→ `books/expiry.lisp:467` → `books/store-reclaim-pack.lisp:634-638` → `books/store-reclaim-holders.lisp:78-87`:
the BP holder list is literally NIL. `books/store-reclaim.lisp:275` tests only that list, not retention.
Thus even a canonical outstanding :forward pin does not prevent selection when other reclaim conditions permit it.
Also enqueue/attempt/request do not require that pin (`books/bp-workflow.lisp:371-434`; `bp-outbound.lisp:73-78`).
Undertaking is separate (`host/native/bp-obligation.lisp:79-88`); FNWF-local undertaking can modify only its node
(`books/bp-release.lisp:182-195,307-312`). Do not assume every workflow job has a canonical Store holder.
Use canonical durable pins mapped subject→Message-ID, covering admission gaps and every enabled adapter.
Pins have no elapsed-time bound (`books/retention.lisp:393-429`); retry/lifetime/transport timeout do not release them.
Receipt or durable operator abandon releases them (`host/native/bp-obligation.lisp:10-24,91-113`);
ordinary pause/drop is not abandonment (`books/bp-carry-control.lisp:268-298`). Holding may be indefinite by policy.

3. Additional roots found by host global/special reads and writes; “unchanged” means the current swap does not clear/rebind:
- `fn-store-sn`: full open Store (`host/store-node-host.lisp:443`), unchanged; owner consumes/clears only
  `fn-store-sco-open` (`host/owner-host.lisp:463-470`). Exclude standalone readers or clear their stale image.
- `fn-store-sco-checkpoint`, `fn-store-sco-pass`: checkpoint rows/source handles (`host/store-node-host.lisp:559,888-910`), unchanged.
  `fn-store-sco-load` clears at decode-finish (:637); legacy `fn-store-checkpoint` / `fn-store-checkpoint-node`
  (`host/checkpoint-host.lisp:261,285`) remain unchanged, diagnostic/offline carriers.
- `fn-reader-selection`, `fn-reader-archive`, `fn-reader-verdicts`, `fn-reader-conn`
  (`host/reader-host.lisp:92-94,62`): standalone reader roots, unchanged; shared-owner coexistence UNVERIFIED.
- `fn-owner-cat-candidate` / `fn-owner-cat-pending` (`host/owner-host.lisp:1870-1877`): staged row carriers;
  candidate consumed there; swap tests pending (:5225), does not clear candidate. Require idle→no candidate.
- `fn-owner-canonical-admission-executor`, `fn-owner-history-semantic-reader-base`: retained Store/view
  (`host/admission-preparation-host.lisp:49-51`; `books/admission-preparation-source-capture.lisp:10-18`), unchanged.
  `fn-owner-history-node-state` / `fn-owner-history-semantic-state` retain produced node/row/ready state
  (`host/admission-semantic-node-host.lisp:71-73`; `host/admission-authority-preparation-host.lisp:112-113`), unchanged.
- `fn-owner-history-config-base` / `fn-owner-account-config-preparation`: Store/view/node continuation
  (`host/account-config-source-host.lisp:61-64`; `host/account-config-preparation-host.lisp:15-20`), unchanged.
- `fn-owner-pic-continuation`: selected-payload controller (`host/post-identity-captured-host.lisp:34-35,48-59`), unchanged.
  These continuation families need holder exclusion/terminal cleanup; actual concurrent served reachability is UNVERIFIED.
- `*fnn-staged-handle*` (`host/native/io.lisp:1767,7834-7835`): consumed by log-take, not swap-cleared.
  `*fnn-live-hrecs*` (:3295-3309): scratch history pages rebuilt before swap, not swap-cleared; residual-name closure UNVERIFIED.
  `*fnn-cat*` / `*fnn-hist*` DO rebind (`host/native/owner.lisp:5576-5584`); canonical state/pending DO clear
  (`books/owner-recovery-retain.lisp:52`; `books/owner-canonical-state.lisp:11-18`). Grep is not exhaustive dynamic-root proof.

Must-do before wiring
1. Connect canonical BP pins to actual reclaim/expiry selection; require durable holding before payload-dependent work, including ION.
2. Prove rebind preserves outstanding ADUs and terminal/restart replay; exercise retry, receipt, abandon and ION history after reclaim.
3. Discharge the additional roots in the name-count relation; atomically rebind valid workflow state, clear stale caches, then forget.
4. Keep DECISION.md's lifecycle fail-stop/crash requirements. Source-only at 6a91ff1d629dbe4bf75d97ab82e6a88a87d0b46f; no builds/proofs run.

## 9. Lane state after c08 + c10 (arena-forget, 2026-10-03)

- DONE (first, own READY when certified): the deferred-reclaim leak. `books/owner-reclaim-seal.lisp`:
  the pass predicts its tombstone rows off the mutex at BASE = the arena count (`fn-orcs-predict`) and seals
  them in the swap quantum only after `fn-orcs-seal-word` answers :swap (:moved when another seal moved the
  count). KEYSTONE `fn-orcs-seal-is-the-intern` (no hypothesis): the prediction at the arena's count is
  `fn-orcp-intern-rows`'s rows and the seal its arena. Choice and reason: seal-after-decision rather than
  release-on-defer, because there is no export that gives back a resident payload's octets (forget frees the
  entry and stage, not the paged child), so release-on-defer still grows the arena; the catalog load and the
  rebuild never read payload bytes (`fn-sca-load-held-rows` ignores the arena; `fn-orcp-rebuild` takes none),
  so they work over predicted rows. Cost: the swap quantum now seals k tombstones (~100-300 octets each);
  measured in the native before READY. Native: `tests/test_native_over_pins.py` defers three passes under a
  held OVER and requires the reported `arena=` count unchanged.
- c08 (a) adopted: option B, a per-handle NAME COUNT over the declared roots, computed in the rebuild walk
  and published with the rebuilt roots; section 8.2's per-root table becomes its root declaration list, not
  a distinctness argument (`fn-arf-changed-handles-are-unnamed` stays as a lemma only where rows are
  unaliased).
- c08 (b) adopted, superseding 8.5: host-called reads carry a live-handle premise; the raw boundary
  fail-stops with a named forgotten-payload fault (`fn-arx-forgotten-p` triggers it); never empty, never 430.
- c08 (c) adopted: `fn-arx-commit-reseat-leaves-an-empty-handle` is reworked to a LIFECYCLE refusal
  (forgotten / not owned by this reseat) on every reseat path: commit place, `fn-xrt-reseat-one`'s delayed
  checkpoint-frame handles, the direct reseat exports. The zero-length refusal in `fn-arx-commit-place` is
  removed again (empty payloads are legal).
- c10: the BP workflow node is rebound at the swap through the existing release operation, preserving work,
  receipts and txids; owed: rebind preserves outstanding ADUs and restart replay; retry/receipt/abandon/ION
  after a reclaim; cover or idle-exclude the 14 globals Astra lists. Host wiring of the forget waits for
  RECLAIM-RETENTION's holder fix (books/store-reclaim*.lisp and the holder slots are theirs; this lane stays
  in payload-arena*, arena-forget*, extent-retire, payload-commit-extent, owner-reclaim-pass/-seal and the
  owner.lisp reclaim driver).
