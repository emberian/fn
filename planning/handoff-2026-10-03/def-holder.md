# CONTINUATION (wind-down 2026-10-03 night, ember: too many agents)
Branches pushed: lane/def-holder 297e4f700 (on origin/lane/arena-forget 9a3a85be3), lane/def-holder-core
409f1ae54 (on origin/dev); both sent to the runner for the all-onto-dev merge. Ledger: DH00/DH01/X14 ready.
Runs left on hbox, NOT harvested (harvest them, do not re-run): certify run-20261003T021008Z-02fb
(certify-20261003T021413Z-3069010, page-read-direct closure at dc462c44e; the head 297e4f700 adds a :root
row and the parameterised handle-holds keystone, both REPL-admitted only -- resubmit at the merged head);
natives hbox native-wt-20261003T020633Z at f34d7057b (page_io, slow_disk, owner, log, recovery,
crash_model, init_publication, mux, reader_clients; `tools/hbox_native.sh status wt-20261003T020633Z`);
the F1 native test_a_publication_never_retires_the_history_image (page_io) has never run; check-lane at
187b3470b (`tools/remote_check.sh attach hbox`). REPL sessions dh/hh/pd stopped. Worktrees
build/lanes/def-holder and build/lanes/def-holder-core: remove when landed. Next agent: base on origin/dev
after the merge; dev failures arrive as ledger items. Full state and the exact NEXT below.

# LANEDUMP def-holder (Fable 5.1), 2026-10-03

Worktree /Users/ember/dev/fn/build/lanes/def-holder, branch lane/def-holder from origin/dev 4aa332295.
Deliverable 1 (this file, section 1-3): the resource/holder inventory from source and the interface
sketch, for the coordinator's Codex consultation and for ARENA-FORGET. Nothing landed yet.

## 1. Inventory: every resource/holder pair, how it is tracked today

Legend. KEY = what identifies one unit of the resource. TRACKED = the structure the releaser reads
to learn the unit is still held, and its cost per query. A row marked SCAN re-walks all holders per
query; COUNT is carried incrementally; NONE means nothing records the holder.

### R1. Payload handle (books/payload-arena.lisp; KEY = natp handle, never reused)

| holder kind | structure (file:line) | acquire | release | TRACKED |
|---|---|---|---|---|
| catalog row / article names exactly one handle | books/held-record.lisp:1-14; rows via fn-sn-indexed-rows books/store-node.lisp:1545 | fn-intern-event books/store-intern.lisp:49, fn-intern-row-at :911, fn-cat-intern books/catalog-record.lisp:414 | none per handle: the reclaim pass interns a tombstone handle (fn-orcp-intern-rows books/owner-reclaim-pass.lisp:277) and the old handle is simply no longer named | NONE (fn-row-handle-inp books/store-intern.lisp:194 is a bounds check) |
| off-mutex arena reader at generation G (checkpoint publication, export, reclaim dry-run/pass) | fn-arpn state (CUR PINS PEND), books/arena-reader-pins.lisp:184; host *fnn-arena-pins* host/native/io.lisp:6772 | (:pin) fn-arpn-step :215; fnn-arena-pin io.lisp:6793; sites host/native/owner.lisp:5255,5305,5469,5661 | (:unpin G) :216; fnn-arena-unpin io.lisp:6801; sites owner.lisp:5152,5270,5315,5415,5504,5788 | COUNT per generation; quiet = one comparison fn-arpn-clear-through-p :151 |
| connection response plan (one hold per cid, delegates to the generation table) | owners alist (cid . G), books/response-plan-pins.lisp:30 fn-rpin-step; slot response-pins owner.lisp:116 | (:acquire cid) fnn-owner-response-pin owner.lisp:483, site :4549 | (:release cid) fnn-owner-response-unpin owner.lisp:490; sites host/native/mux.lisp:274,505, pull-service.lisp:293,399,452, web-host.lisp:125,134 | SCAN of the alist per op (fn-rpin-owner :11) |
| snapshot payload view (whole-arena prefix) | ledger (inc last active), books/payload-view-lease.lisp:19-30 | fn-pvl-acquire :34; host owner.lisp:1653-1667 | fn-pvl-release :48 (needs :joined); owner.lisp:1678 | single slot; fn-pvl-livep :30; fn-pvl-reset refuses a live view :54 |
| recovery payload view | books/recovery-payload-view.lisp:5 | fn-rpv-acquire :29 | fn-rpv-release :45 | single slot; fn-rpv-ownedp :25 |
| log members in flight / fenced (handle, file, place) | fnn-log struct host/native/io.lisp:6289 fields :6323; push :6765 | commit | fnn-log-reseat-fenced io.lisp:6836: reseat, then (:retire handles) :6856, then fn-arena-release per released handle :6857-6861 (a logical no-op today; ARENA-FORGET makes it the forget) | SCAN: fnn-log-member-files io.lisp:6864 (file level only) |
| staged copy per handle (fn-arena$x-stage) | books/payload-arena-extent.lisp:52 | fn-arena$x-seal-buffer :611 | fn-arena$x-release :687 | NONE by the arena; the host retires the handle list at a stamp (above) |
| online reclaim pass capture / checkpoint writer sources (handles as copy sources) | books/owner-reclaim.lisp:8-11; books/store-checkpoint-arena-writer.lisp:136-189; fn-xrt-step-handles books/extent-retire.lisp:87 | capture under the mutex | pass/publication end | via the generation pin only |

NOT holders (they hold a Message-ID and re-resolve the handle per call under the owner mutex):
feeds (fn-own-feed-article books/owner.lisp:2499, fn-handle-bytes at books/owner-feed-article.lisp:46;
host feed-service.lisp:198,283), consumers (an ack position; transient reads
books/consumer-remote-visible-buffer.lisp:67-134), BP jobs (fn-bpo-article-handlep books/bp-outbound.lisp:48,
bp-request-plan.lisp:170, bp-ingress.lisp:840-870; books/bp-held-payload.lisp header "Host: NONE YET"),
cursors (obligation-view-cursor, view-delta-cursor, owner-retire-cursor: no handle). The closed world of
handle READERS is table fn-payload-kinds :handle (books/payload-kinds.lisp:88, tools/payload_kind_check.py).

### R2. File generation / descriptor (KEY = natp incarnation id, fn-pio-file-issue books/page-read-ownership.lisp:124)

Tables *fnn-extent-fds*/-paths/-incarnations/-bases under *fnn-extent-lock*, host/native/extent.lisp:48-54.
Acquire fnn-extent-register :86 (callers io.lisp:2630, 6761, 7503, 7511; owner.lisp:4946).
The ONLY close: fnn-extent-close extent.lisp:1225 (fnn-close :1245).

| holder kind | structure | acquire | release | TRACKED |
|---|---|---|---|---|
| extent-column entry naming the file | fn-arena$x-files column books/payload-arena-extent.lisp:52 | fn-arx-files-inc :491 via fn-arx-files-move :522 from fn-arx-mark :566 (every seal/reseat :596-678) | the reseat moves the count; fn-arena$x-clear :634 zeroes | COUNT per file (fn-arx-file-count :1392); keystone fn-arx-file-count-zero-names-none :1419 |
| issued cold read (the row is the pin) | *fnn-extent-issued* extent.lisp:62; row fn-pio-rowp books/page-read-ownership.lisp:10 | fnn-extent-issue-direct extent.lisp:988 (fn-pio-direct-admit books/page-read-direct.lisp:53); funded fnn-extent-issue-read :890 | fnn-extent-direct-settle :1016 (fn-pio-direct-settle :84); fnn-extent-complete-read :922. Cancel :912 does NOT release (keystone fn-pio-direct-cancelled-read-still-pins-its-file page-read-direct.lisp:221) | SCAN of every issued row per close: fn-pio-file-clear-p page-read-ownership.lisp:68, called extent.lisp:1230 |
| log member in flight / fenced | fnn-log (above) | commit | COMPLETE reseats it to the log extent | SCAN io.lisp:6864 -> the NAMED input of fn-xrt-quiet-files |
| off-mutex reader that may hold an entry naming the file | fn-arpn | fnn-arena-stamp owner.lisp:4993 | fnn-arena-clear-p owner.lisp:4854 | COUNT (generation) |
| ledger :file-pin / :window / :cached / :discovery bindings | books/page-read-ledger.lisp:10-13 bindings; page-file-lease.lisp:7 fn-prf-acquire | fn-owner-page-file-pin host/page-file-lease-host.lisp:14; owner.lisp:4867 | fn-prf-release page-file-lease.lisp:39; owner.lisp:4880 | SCAN of bindings: fn-prl-file-heldp page-read-ledger.lisp:83 -> close-preview :read-file-held |
| fn-pgs-fill-realize | extent.lisp:1145: fd under the lock :1147, pread OFF the lock | - | - | NONE. Relies on the docstring at :141-145 ("held for the process's life"); not verified that an image id never enters *fnn-extent-retired* (ids are matched by path, :1215). FINDING F1 |
| fnn-extent-window-run | extent.lisp:267, fd :282-285 | ledger window lease :578 | :423 | ledger scan only; not an issued row |

Quiet for close = three layers read in fnn-owner-release-extents owner.lisp:4925: fn-xrt-quiet-files
books/extent-retire.lisp:276 (file count 0 and not log-named; keystones :317, :342, :354), then
fnn-arena-clear-p S (generation), then inside fnn-extent-close fn-pio-file-clear-p + close-preview.
Cut: retired (*fnn-extent-retired* :1208) -> pending at S (*fnn-extent-pending* :1210) -> closed; retries at
owner.lisp:4300, 4862, 4888, host/native/recovery-payload-view.lisp:63. Process-local lists; no named cut
(crash model v2 section 2.3 exempts close: no durability effect).

### R3. Worker slot (KEY = slot; fn-pxe row books/page-read-executor.lisp:20; host fnn-cold-worker extent.lisp:244)

Holder = one issued read's token. Acquire fn-pxe-assign :36 (via fn-pio-direct-admit); release fn-pxe-return :65
then fn-pxe-commit-direct page-read-direct.lisp:70. "All busy" is NOT a theorem over the slot set: the host
offers the head of an intrusive free stack (*fnn-cold-free* extent.lisp:251; :1003-1012) or NIL, and ACL2
refuses by name (:read-resources-unavailable). Late outcome :stale-job (fn-pxe) / :stale (fn-pio).

### R4. Arena generation (KEY = natp G; fn-arpn)

The one instance that already has the target shape: COUNT per key kept ascending, O(1) quiet test,
release theorem (fn-arpn-release-postdates-every-live-pin :429), refused late unpin (:unpin of an unheld G
-> (mv st :refused) :219). Two other refcount shapes exist hand-written beside it: index-backing
connection holder (per-row alias count + generation refcount, books/index-connection-holder.lisp:16,
not in the image) and the file column (R2).

### R5. Retention obligation (durable, in the node state; KEY = obligation id)

Pin (id subject kind evidence charge) books/retention.lisp:107; state (capacity reserved pins releases) :337.
Holder kind UNTRACKED on the pin (kind :archive/:forward + evidence only; no BP job / feed / operator field).
Acquire fn-retain-admit :382 (node prepare/complete books/node.lisp:372,399; BP undertake
books/bp-release.lisp:191; replay books/replay.lisp:582). Release fn-retain-release :413, only :forward
(bp-release.lisp:249, replay.lisp:588, waiver books/bp-carry-waiver.lisp:42); :archive never released
(fn-sn-finish-keeps-every-archive-obligation books/store-node-retention.lisp:518).
The disjointness invariant fn-retain-ids-disjointp :62 is a conjunct of fn-retain-statep :347-350, which sits
in :guard at retention.lisp:367,383,415, post-retain-carried.lisp:775,788, replay-identity-index.lisp:215,240,
node.lisp:56 (mbe :logic only; :exec skips) -- and fn-retain-known-id-scanp :308 (O(pins+releases)) runs
twice per prepare. The carry (fn-prc trie, post-retain-carried.lisp:774) replaces the scan but the host never
asks it (one guard at host/owner-host.lisp:2290). No "quiet" notion: releasable = fn-bprl-release-okp.
Host: host/bp-release-owner-host.lisp:34-80, host/native/bp-obligation.lisp:20,75,83,92,278.

### R6. Connection pinned view / version (KEY = version/config generation)

Conn record holds version, frontier, archive, trie, group index (books/owner.lisp:126-161); config pins alist
(conn-id . cfg) books/owner-config.lisp:69. Acquire fn-own-open owner.lisp:1428 / fn-ocfg-open :529; repin
fn-own-advance :2028, fn-own-read-repinned :1933; release fn-own-close :2078 / fn-ocfg-close :558 / fn-own-fault.
TRACKED: SCAN of the connection list (fn-ocfg-conns-pinnedp :273, fn-ocfg-group-pinned-by-readerp :373).
fn-own-min-pinned :3176 / fn-own-reclaim-floor :3186 are called by NOTHING. The reclaim swap waits instead
on the arena reader count (fn-orcp-swap-word :readers books/owner-reclaim-pass.lisp:156; owner.lisp:5747
passes (1- reader-count)): any undrained connection response blocks the swap (FINDING F5). Captured reader
views (fn-ocv books/owner-reader-view.lisp:61): which connections opened at the view is UNTRACKED.
Host: host/owner-host.lisp:3924,4525,4543,4547; native owner.lisp:250,1767,1796,1806,2891; mux.lisp:291.

### Crash points today

A cut is a string step (list :cut "name") in a byte program; tools/native_program_check.py compares the
program's steps with the fnn-at sites of host/native/io.lisp (only fnn-finish and fnn-sweep-staging are
walked, PROGRAM_HOSTS :75); the registry is tests/campaign/native_cuts.py NativeCut(name, program,
candidate, ...) with host defparameters +fnn-*-model-cuts+ (io.lisp:2740,3730,3760,3795,4198,4385,4836,
4847,6284; owner.lisp:5515 +fnn-reclaim-cuts+ mirrors *fn-orcp-cuts* books/owner-reclaim-pass.lisp:214 --
the ONE place a book declares the cut names the host mirrors). No macro, no book-level declaration.
tools/resilience/scenario.py:75 PENDING_BOUNDARIES: `page-read-outstanding` has a hold form
(FN_NATIVE_PAGE_IO_HOLD) and NO kill cut; `reclaim-candidate-selected` likewise. fnn-log-at (io.lisp:6348)
does not validate its name; rotate-*/drop-* cuts used at :7265-7415 are absent from +fnn-log-model-cuts+
(FINDING F2).

## 2. Findings beyond the brief

- F1 fn-pgs-fill-realize (extent.lisp:1145) preads off the lock with no row and no pin.
- F2 (CORRECTED by Astra/liaison 2026-10-03): the rotate-*/drop-* cuts ARE modelled
  (books/store-log-segments.lisp:460-495, SEGMENT_PROGRAM_HOSTS native_cuts.py:737); the gap is that
  fnn-log-at (io.lisp:6348) accepts any name, so an unknown cut never fires unnoticed, and no check
  compares declared cuts, host sites and models both ways. Astra's t40 (lane/codex-log-cut-coverage)
  builds that check; the generated fn-holder-cuts rows feed it (row shape to agree once t40 lands;
  the rows are macro-emitted, so a static reader needs the ledger's expansion mirror).
- F3 RETRACTED (c05, verified by me at owner-host.lisp:1825-1835 and 1985-2012): the host refreshes
  the fn-prc carry on every prepare (`(fn-prc-refresh (fn-owner-retain-carry state) ...)`) and hands it
  to fn-pout-prepare-article / fn-ppc-pout-prepare-article-cat, whose admissibility is the trie path.
  What stands is only that fn-retain-statep's disjointness conjunct sits in mbe :logic guards (the
  :exec skips it): not a served cost. Its mbe keyset is GENERATORS' def-keyset-check pilot.
- F4 (CORRECTED, c05): feeds and BP outbound hold a Message-ID and a rendered COPY (octets), not a
  deferred handle; consumers are NOT excluded wholesale: the remote-visible writer retains a row and
  re-reads its handle (consumer-remote-visible-buffer.lisp:85-136; unwired: no issuer, host
  consumer-remote-report-host.lisp:57-58). The sentence "the forget goes where fn-arena-release is called
  today" was WRONG: io.lisp:6856-6861 releases the STAGED COPY of every reseated member on every commit
  (handles still named by their rows; fn-arena-release is the logical identity, payload-arena.lisp:692).
  A forget there would invalidate live articles. ARENA-FORGET already separates the two (a plain natural
  = a staged page, (:forget H) = a swap's un-named handle, arena-forget.lisp:51-73); only (:forget H)
  items from a reclaim's un-naming may reach the forget. Handle liveness is NOT "named by a row OR pinned
  OR leased": it is "no reachable ROOT names H" over ALL roots (section 1b below), plus physical custody
  (a cold read names (file, place), not H) and the durable ordering (physical release after the
  durable replacement at every cut).
- F5 (RE-RATED, c05): response pins ARE identified by cid (fn-rpin-step: duplicate acquire refused,
  release unpins that cid's generation); the swap counts readers. A stalled socket is released by the
  per-window output deadline. So F5 is a liveness/starvation gap under sustained reads (the swap defers
  8 rounds then reason=readers), not a leaked pin. SPEC ERROR found with it: specs/lifecycle.md row 5
  cited fn-own-min-pinned / fn-own-reclaim-floor, which no executable consumer calls (fixed on this lane:
  the row now cites the response hold PRF-1059 and the swap's reader test / repin).
- F1 (RE-RATED, c05): claim-gap. The off-lock pread of fn-pgs-fill-realize is real; the served
  close/reuse interleaving is not established: the history-image id is registered fresh
  (extent.lisp:141-149) and only owner.lisp:4946-4956 retires ids, by path. Needs an explicit image
  lease or a checked exclusion (a def-holder instance of the file resource), after the cold read.

### 1b. The holders the headline missed (c05), now in the relation
- cold reads: a worker holds (file, eoff, elen, trailer) -- a PLACE, not H (extent.lisp:830-843 throws
  the physical coordinate; the row page-read-ownership.lisp:8 names no handle). A forget must not let
  P be REUSED while a token is out; file close already waits (fn-pio-file-clear-p). PHYSICAL CUSTODY.
- connection views: every connection retains version/archive/index (books/owner.lisp:126-163); the
  installing reclaim REPINS every live connection to the rebuilt view in the swap quantum
  (fn-orcp-swapped-owner -> fn-orcp-repin-conns, owner-reclaim-pass.lisp:360-393). ROOT, :repinned.
- OVER cursors: the cursor keeps (group k top v ...) and reads fn-cat/fn-arena per quantum under the
  response pin acquired BEFORE the plan leaves the quantum (owner.lisp:4545-4549). ROOT, :pinned.
- NEWNEWS tail: newnews-cursor.lisp:229-284 keeps an article-list tail; "called by nothing served yet".
  ROOT, :unwired.
- BP workflow node: fn-workflow-state holds (fn-sn-node sn) (host/workflow-host.lisp:19-24) and
  bp-outbound resolves articles in THAT node (bp-outbound.lisp:67-72) before reading the handle;
  on the traced command the open and the request thunk share one serialized region
  (bp-obligation.lisp:44-59). ROOT, :serialized (a longer-lived image must be refreshed per swap).
- consumer remote-visible writer: a retained row re-read by handle (above). ROOT, :unwired.
- fenced / in-flight log members (H FILE PLACE OCTETS), io.lisp:6316-6323, 6745-6766: NOT tested by
  the swap word; ARENA-FORGET's 4(c) (reseat must not resurrect). ROOT, :pinned by the swap's own
  clause (open: the swap word requires no fenced member, or fn-arx-commit-extent refuses a forgotten
  handle).
- checkpoint writer sources / reclaim capture / export capture: captured row lists read off the mutex
  under fnn-arena-pin taken BEFORE the thread starts (owner.lisp:5253-5270 etc.). :pinned.
- whole-arena leases fn-pvl / fn-rpv: a token-and-state live test, prefix explicit in the token;
  drivers not in the native image. :unwired.

## 3. Interface sketch (one page)

A resource is a KEY type; a holder kind is a pair of host-called entries; holding is a carried count per key
(fn-arpn's table, generalized), never a scan. Macros expand to ordinary events; a generic theory proved once,
each instance a functional instantiation (def-carried's pattern).

    (def-holder NAME
      :resource (KEYP [:ordered t])        ; the key recognizer; :ordered keys get stamps and an O(1)
                                           ; quiet test (fn-arpn-clear-through-p); unordered keys get
                                           ; per-key membership (the live set is bounded by the holders)
      :holders ((KIND :acquire (FN :key K-TERM [:ok OK]) ; FN's answer that holds; K-TERM over `_' (the
                                                          ; call) names the key held; OK its success word
                      :release (FN :key K-TERM [:ok OK])) ; the answer that drops it; any other answer
                                                          ; of FN leaves the table as it was
                ...)
      [:carried-count (COUNT-FN ZERO-THM)] ; an existing incrementally carried count (a stobj column:
                                           ; fn-arx-file-count) declared AS this relation: ZERO-THM is
                                           ; cited, no table is generated for it
      [:lease (LIVE-P ...)]                ; single-slot whole-prefix leases that also hold every key
      [:named-by (NAMES-P UNNAME-THM)]     ; for handle-like keys: the rows' naming relation and the
                                           ; theorem that the release entry un-names the key
      :effect (:process-local "rebuilt at open: THM")
            | (:durable PROGRAM CUT))      ; what the release's EFFECT is (see crash points)

Generated (names fixed, statements regenerated from the world like def-carried; a hand row refused):
  NAME-table/-okp/-initial; NAME-held-p K; NAME-count; NAME-quiet-p S (ordered: one comparison);
  NAME-step (:hold K | :drop K | :retire ITEMS | :stamp | :release | :clear S | :clear-except S G).
  (a) carried relation: NAME-KIND-acquire-holds, NAME-KIND-release-drops, per kind, by :use of the
      declared FN's theorem in minimal-theory (the acquire's success answer holds its key, the release's
      success answer drops it, every other answer keeps the table);
  (b) preservation: NAME-KIND-keeps-okp per entry, NAME-run-keeps-okp by functional instantiation;
  (c) release theorem: NAME-release-postdates-every-live-hold (every item :release answers was pending at
      a stamp below every live hold) and NAME-quiet-means-no-holder; with :named-by,
      NAME-quiet-item-is-unnamed-and-unheld -- the forget/close precondition in one theorem;
  (d) late holder: NAME-drop-of-unheld-is-refused: (mv st :refused), state unchanged, distinct from
      :released and from a refused acquire;
  (e) crash points: NAME emits `*NAME-cuts*' = (NAME-decided NAME-released) and a row in table
      fn-holder-cuts (:process-local -> the candidate column is "rebuilt", with the cited rebuild theorem
      that the open's table is NAME-initial; :durable -> CUT must be a :cut of PROGRAM's step list, else
      refused). Host mirror: the host's release site wraps decide/effect in (fnn-holder-cut :NAME-decided)
      / (:NAME-released); tests/campaign/native_cuts.py gains HOLDER_CUTS read from the table (the
      *fn-orcp-cuts* / +fnn-reclaim-cuts+ pattern), so native_program_check finds them declared;
  (f) teeth: per GENERATORS' published contract (lanedumps/generators-2.md section 2), def-holder emits
      `(table fn-teeth-owed NAME-...)' for every generated keystone ((c) and (d) above); the instance's
      test book writes one `defteeth' per owed name (full-antecedent witness, one break per hypothesis,
      the late-holder mutation, :mutations (:none "why") where the statement has no hypothesis), and
      `(defteeth-check)' refuses an owed keystone with no fn-teeth row. A `def-holder-teeth' helper in
      the test book expands a scenario (a hold, a stamp, a drop, a late drop) into those defteeth forms
      the way def-carried-view-teeth does, so the ground values are written once.
Fail closed: at admission and under def-holder-check in the image world, every function in the world whose
body calls NAME-step with :hold or :drop, and every fn-interfaces entry returning the table's carrier, must
be a declared KIND's acquire or release (fn-cd-unproduced-call's walk); an undeclared caller refuses the
declaration. For handle keys, every fn-payload-kinds :handle reader must be reached under a declared hold
(the row lookup under the mutex, or a pinned generation) -- proposed as a second stage, world-walk over the
:handle table.

Boundary with DEF-ENTRY (proposal): def-holder OWNS the cut names and the table row (fn-holder-cuts) for
holder releases; def-entry's per-entry crash-point enumeration READS that table for an entry declared as a
holder's release and emits no cut of its own for it. One generation, two readers. The crash model's
`close' exemption stays: a :process-local effect is declared rebuilt-at-open, not durable.

## 3b. The macro after c05 (landed on lane/def-holder)
- An ACCOUNTING component, said in its header: def-holder authorizes no forget or close by itself; a
  release is licensed by (1) the instance's ROOT theorem over all roots, (2) the generated accounting,
  (3) physical custody ended, (4) the durable ordering.
- Holder forms: logic `(KIND :acquire (FN THM :table I :result P :key K :ok OK [:when W] [:keeps THM2])
  :release (..))`; host `(KIND :host t :acquire FNN :release FNN :in (FNN ..))`; ROOT `(KIND :root t :in
  (FN ..) :status (:repinned|:pinned|:serialized|:excluded|:unwired "why"))`.
- Effects classified: (:process-local "why") | (:durable PROGRAM "cut") | (:physical CUTS :cut K :after K2)
  -- CUTS a defconst keyword list the host mirrors; K2 (the durable replacement) must precede K, else
  refused. Returning blocks is never process-local.
- Closure: def-holder-check walks the whole world (a function calling a holder step that is no declared
  entry is refused); tools/holder_check.py (make check) closes over the RAW HOST both ways: every
  declared acquire/release is called inside its :in functions, every host call of one is inside a
  declared :in (fail closed), every root's keeper exists, and the effect's two cuts are MARKED in the
  row's :in functions in order (a declared cut is a name; the marker makes it a checked release;
  absence is a note, fatal under --strict).
- Teeth: (table fn-teeth-owed 'K '(:by def-holder :claim CLAIM :subject FN)) after every generated
  defthm (GENERATORS v1): CLAIM in source shape over the same translated parts, so its translation is
  the theorem.
- Identity per holder (c05): the :stamped shape stays count-only by design (anonymous readers) and
  composes with fn-rpin's cid layer and fn-pio's token layer as declared logic holders; an identified
  keyed step (tokens per key, duplicate hold / absent drop refused) is NEXT, for the cold-read instance.
- :carried-count (a stobj column declared as the relation) NOT yet implemented: when it is, the cited
  theorem's exact statement is compared (fn-cd-generated-problem's rule).

## 4. Instances I will land (in order), each its own READY

1. books/def-holder.lisp + tests/acl2/def-holder-tests.lisp: the generic theory and the macro, proved on
   fn-arpn's own shape (the arena generation table becomes `(def-holder fn-arena-readers ...)' or is kept
   and shown EQUAL to the generated table -- decided by which is net-negative).
2. The cold-read instance: `(def-holder fn-pio-file-holds :resource (natp) :holders ((cold-read :acquire
   (fn-pio-direct-admit ...) :release (fn-pio-direct-settle ...))))': fnn-extent-close reads a count, not
   fn-pio-file-clear-p over every issued row; the six keystones of page-read-direct keep their names, the
   file-pin keystone is re-cited through the generated holds theorem; teeth unchanged in meaning.
3. The payload-handle instance for ARENA-FORGET: `(def-holder fn-handle-holds :resource (natp :ordered t)
   :holders ((reader ... fn-arpn's pin/unpin) (response-plan ...)) :lease (fn-pvl-livep fn-rpv-livep)
   :named-by (<rows name h> <reclaim install un-names the old handle>))' and the composed theorem that a
   released handle is unnamed and unheld: ARENA-FORGET cites it as the precondition of fn-arena-forget
   where fn-arena-release is called today. I provide the theorem; ARENA-FORGET owns the export.
4. retention (R5) and connection views (R6): declared, not rewritten, in this stretch. R5's disjointness
   scan (F3) is GENERATORS' `def-keyset-check' pilot (generators-2.md section 3: it names
   fn-retain-ids-disjointp); I do not touch it. The host-not-calling-the-carry half of F3 stays a row.

## State (2026-10-03, after the usage-limit resume)
- lane/def-holder-core b81e6300c READY (sent); the runner has it for the batch after the priority image
  set. 409f1ae54 adds the filed manifest line (certify-20261002T231000Z-1767432).
- lane/def-holder (on origin/lane/arena-forget 9a3a85be3): handle-holds (PRF-1240) + the COLD-READ
  INSTANCE, certified: hbox run-20261002T233038Z-675d, certify-20261002T234044Z-2479459 PASSED 14/0
  (filed, 41c46b47d). Then a proof-cost pass (the admitted branch stated once: 2.7M -> 322k and
  2.2M -> 87k steps; run-675d had the book at 22.4 s under 3 jobs, over D26): resubmitted.
  interface_emit --check 0, host_check --books 0, holder_check 0 (2 declarations) on hbox at 09df08b63;
  planning/interfaces.json regenerated (f34d7057b).
- CLOSE-PATH COST (hbox REPL pd, 1e6 queries, 0 bytes allocated either way): old walk
  fn-pio-file-clear-p over 1 / 4 / 8 issued rows: 0.04 / 0.03 / 0.04 s; new lookup
  fn-pio-direct-quiet-p over 1 / 4 / 8 held files: 0.02 / 0.01 / 0.01 s. Both are bounded by the
  worker count (4) -- the difference is ~30 vs ~10 ns per query. The host-side change is what
  matters: fnn-extent-close no longer collects every issued row of the hash table into a fresh
  list per call (one `loop collect` + one fnn-call with that list per retired file); it passes the
  carried table (no allocation). Honest scope: a micro-cost either way at 4 workers.
- NATIVES: hbox native-wt-20261003T020633Z (developer, production, dtn-developer at f34d7057b):
  page_io, slow_disk, owner, log, recovery, crash_model, init_publication, mux, reader_clients.
  (wt-20261002T234202Z died at interfaces-check: the regenerated registry was not yet committed.)
- Sessions on hbox: dh, hh, pd. Idle 3 h.
- 187b3470b: holder cuts in the crash model -- native_cuts.holder_cuts (read from the declarations) +
  verify_holder_cut_map (declared cuts / +fnn-holder-cuts+ / (fnn-holder-cut ..) markers both ways; a
  :physical effect's cuts in the reclaim list) wired into native_program_check (holder cuts: PASS);
  scenario.py registers holder-<cut> boundaries (rule rebuilt, FN_NATIVE_HOLDER_FAULT) and
  page-read-outstanding's kill_form = holder-fn-pio-file-holds-decided; test_resilience_checker 57/57,
  test_holder_check 5/5. Farm run-20261003T021008Z-02fb (the proof-cost pass) and check-lane at
  187b3470b running on hbox; natives wt-20261003T020633Z at f34d7057b (later commits: a docstring in
  extent.lisp, proof hints, tools/tests -- no served byte).
- LEDGER (build/coordinator/repair): DH00 ready (the core, with the runner), DH01 in-progress (the
  cold-read instance + handle-holds + holder cuts), X14 in-progress (F1: a checked exclusion --
  *fnn-extent-image-id* at adoption, fnn-owner-release-extents refuses by name, the :excluded root
  history-image, native test_a_publication_never_retires_the_history_image; a72e41722). arena-forget
  (aee559491e807f178) told of the two file boundaries (handle-holds includes its book; reclaim-cuts).
- 297e4f700: the liveness keystone PARAMETERISED over NAMED (the handles the roots still name) with
  the root fact's conclusion (fn-arf-disjointp of the walk's handles from NAMED) as hypothesis; the
  corollary ...-under-the-pairwise-root-fact instantiates today's fact; arena-forget agreed (its
  per-handle name count, c08 (a), will prove the disjointp and cite the keystone with ROOTS-NAMED).
  hh session restarting on it.
- ALL-ONTO-DEV (ember, 2026-10-03 night): lane/def-holder 297e4f700 and lane/def-holder-core 409f1ae54
  sent to the runner (a8c1198f67920c411) with the honest state (two books REPL-admitted not certified;
  natives at f34d7057b in flight; the F1 native unrun). DH01 and X14 ready at 297e4f700. After the merge:
  base on origin/dev; dev failures come back as ledger items.
NEXT (exact):
0. After the merge: new worktree on origin/dev; harvest run-02fb, the natives and check-lane as evidence
   for the landed bytes; fix forward on dev.
1. (superseded by 0) Harvest run-02fb, resubmit the farm at 297e4f700 (refused while 02fb certifies), the natives at
   f34d7057b then one run at a72e41722 for page_io (incl. the F1 witness), slow_disk, owner, recovery,
   init_publication (developer + dtn-developer), check-lane at the head; then READY lane/def-holder
   (sequenced after ARENA-FORGET): cold-read instance + handle-holds.
2. FN_NATIVE_HOLDER_FAULT=fn-pio-file-holds-decided:kill as page-read-outstanding's kill form in
   tools/resilience/scenario.py (PENDING_BOUNDARIES), with one native run of it.
3. F1 as a file-resource instance (fn-pgs-fill-realize: an image lease or a checked exclusion).
4. tools/ledger.py def_holder_expansion; the fn-holder-cuts row shape for t40.

## Obstructions and asks (standing section)

- The arena header's design reason ("a feed, consumer or BP job may hold the handle") is not what the
  tree does; please route F4 to ARENA-FORGET now, it changes its proof obligation from four holder kinds
  to rows + generation + leases.
- F1 (fn-pgs-fill-realize off-lock pread with no pin) is a served-path ownership gap of the same family
  as r31 F1/F2; it is not in my brief; it should be a row.

## Astra's view (consultation c05, gpt-6-astra, read-only at 4aa332295, 1358 s)

### Liaison fact-check (codex-liaison-11, 2026-10-03)
Checked in source myself (worktree build/lanes/codex-c05-holder):
- CONFIRMED the release-site counterexample to F4's "the forget goes where fn-arena-release is called today": io.lisp:6856-6861
  releases the STAGED copy of every reseated member (fnn-arena-retire of the fenced handles, then fn-arena-release per due
  handle) -- these handles are still named by their rows; fn-arena-release is the logical identity
  (books/payload-arena.lisp:692-694). A forget there would invalidate live articles on every commit. NOTE: lane arena-forget
  already distinguishes the two (books/arena-forget.lisp:51-73: a plain natural is a staged page, a (:forget H) item is
  forgotten), so this binds the WIRING (only (:forget H) items from a reclaim's un-naming may reach the forget), and F4's
  sentence must be corrected.
- CONFIRMED F5's precision: response pins are IDENTIFIED by cid (books/response-plan-pins.lisp:30-46: duplicate acquire
  refused, release unpins the cid's generation); the swap counts readers. A stalled socket is released by the per-window
  output deadline; F5 is a liveness/starvation gap under sustained reads, not a leaked pin.
- CONFIRMED F2 is a nit (same finding as Astra's o01, verified there: the segment cuts are modelled and mapped).
- NOT CHECKED by me: the F1 rebuttal's chain (extent.lisp:141-149 image id registered fresh, only owner.lisp:4946-4956
  retires ids, by path), the F3 rebuttal (host/owner-host.lisp:1825-1835 refreshes and passes the fn-prc carry), and the
  per-holder chains in section 1 (consumer remote-visible writer, BP workflow node global, NEWNEWS tail, cold-read
  physical place).
Liaison's reading: headline FALSE as an exhaustive inventory: add derived-place holders (a cold read names (file, place),
not H: forget must not let P be REUSED while a token is out), retained views/continuations (connection archives;
OVER cursors; NEWNEWS tail when wired), and consumer/BP source carriers (the BP workflow keeps its own node in a global;
the remote-visible writer keeps a row; both unwired or serialized today). Liveness UNSAFE as stated: it must be "no
reachable root names H" (last name, all roots, not TOP only), separate logical invalidation from physical extent reuse,
and order physical release after the durable replacement. Macro WITH CHANGES.

### Astra's answer (verbatim)

Headline: FALSE as an exhaustive inventory; add derived-place workers, retained views/continuations, and consumer source carriers, distinguishing served paths from unwired components (§1).
Forget relation: UNSAFE as stated/applied; it needs last-name removal over every reachable root, physical-read custody, and recovery-safe storage ordering (§2).
Macro: WITH THESE CHANGES; keep the counter generator, but require ownership/refinement and host closure before authorizing release (§3).
F1: claim-gap; off-lock fill is real, but the alleged served close/reuse interleaving is not established for the separately registered history-image id (§4).
F2: nit in the declared-name/docstring contract; the claim that rotation/drop lack model checks or tests is false (§4).
F5: claim-gap in liveness/specification; conservative swap deferral is reachable, but stalled-socket timeout/fault cleanup exists (§4).
ARENA-FORGET must NOT replace io.lisp:6861's staged-copy release with handle deletion; prove a separate last-reference retirement and crash-safe physical-release protocol first (§2).

## 1. Inventory attack

Scope: source `4aa332295c85f03f5a97d7b0ac2228f9b95ab1e9` (`git rev-parse HEAD`). This is source inspection, not execution, certification, or a deployment claim. No tracked files were changed; no builds, ACL2, SSH, or tests were run. Negative call-site findings below are literal source searches over `books/` and `host/`; dynamic/generated reachability beyond the stated scope is **UNVERIFIED**.

Terminology matters. The brief explicitly includes “bytes/fd/offset/place derived from” a handle (`build/codex/c05/CONSULT.md:19-21`). I mark an independently materialized byte buffer **HOLDER (copy)** under that broad definition, while distinguishing it from a holder that prevents forgetting the original arena storage. Otherwise the inventory would confuse the lifetime of a reply allocation with the lifetime of its source. Recommendations and hypothetical interleavings below are design conclusions, not assertions that a proposed forget already executes.

### Feeds: HOLDER (copy); NOT a deferred arena dereference on the traced send path

The actual chain is more specific than the sketch's reference to `fn-own-feed-article`:

- `host/native/feed-service.lisp:278-285`: `fnn-feed-reply-step` calls `fnn-owner-transit-serialized`, and inside its lambda calls `fnn-owner-feed-arena-step 'fn-owner-feed-reply-chunk`.
- `host/native/owner.lisp:1869-1872`: transit serialization is `(fnn-owner-serialized service cid thunk :transit)`; that function runs `fnn-owner-gated` at 1821-1824. The macro holds `(sb-thread:with-mutex ((fnn-owner-service-lock ,s)) ...)` around the body and gate cleanup at 1593-1605. Returning from that form is the unlock boundary.
- `host/owner-host.lisp:4877-4896`: it derives `msgid` with `(fn-own-feed-inflight-msgid (fn-feed-queue feed))`, then passes `(fn-ofa-feed-article owner msgid fn-arena fn-hist)` into the reply event. `books/owner-feed-article.lisp:44-46` defines this as `(fn-handle-bytes (fn-apr-feed-article o msgid fn-hist) fn-arena)`. The actual reader, now defined in `books/payload-arena.lisp:769-773`, returns `(fn-arena-payload h fn-arena)` for an in-range natural.
- `host/native/owner.lisp:778-779` converts the rendered command with `(fnn-octets (fnn-core 'fn-ores-feedpub-command publication))`. `feed-service.lisp:315-321` returns that command from the serialized lambda; at 450 the caller receives it, and at 462 executes `(fnn-feed-send link command)`. The send definition at 239-243 accepts `octets` and passes them to TLS/send-all.

Thus the off-mutex object is rendered octets, not an fd/offset to fetch later. This confirms the narrow feed assertion, not the universal assertion about all holders. A copy still needs its own memory charge and lifetime.

### Consumers: HOLDER; the blanket “transient reads” exclusion is false

**Remote-visible writer, logical/component holder.** `books/consumer-remote-visible-buffer.lisp:46-48` constructs `(list :remote-visible-write key phase row ...)`; 78-79 returns `(:yield ... row ... (fn-arena-payload-len h fn-arena) ...)`. On a later `fn-crvp-plan`, 85-91 reloads `row` from state and sets `(h (fn-record-payload row))`; 132-136 reads `(fn-arena-get h i fn-arena)`. This is a retained row/handle, not a Message-ID re-resolution. The guards at 98-100 check range and length, not a forget generation or a storage lease.

Followed into its consumer: `books/consumer-remote-collection-buffer.lisp:78-80` invokes `fn-crvp-step` on the retained child. `books/consumer-remote-collection-state.lisp:65-80` starts the writer, keeps `:collection-writing` through `fn-owner-remote-collection-keep`, and later invokes `fn-crcol-write-step`. The keep function at 7-11 calls `fn-owner-remote-scan-update-internal` with `pending`. `host/consumer-remote-report-host.lisp:61-90` supplies this continuation to `fn-owner-remote-collection-step-internal` from a `:program` entry.

**Reachability limit:** that same host file says at 57-58, “No public export or issuer exists,” and its presently available report step returns `(:unavailable :remote-report-runtime-representation)` at 55. The collection publication itself returns `(:unavailable :remote-collection-publication-issuer)` in `books/consumer-remote-collection-state.lisp:15-17`. I did not establish a served native path issuing this writer. Do not report a currently demonstrated served use-after-free here; do include this real carrier before enabling it. Its source recheck at 33-35 (`fn-owner-history-recheck` and `fn-hep-capture-livep`) must be connected to arena/physical storage lifetime, not merely assumed to imply it.

**Pull: HOLDER (response plan, then copy), already protected on the inspected paths.** `host/native/pull-service.lisp:269-298` explicitly renders “off the owner mutex,” receives the plan from `fnn-owner-handle-chunk`, and uses `unwind-protect` around repeated `fnn-owner-render-next-quantum`, with `(fnn-owner-response-unpin service cid)` at 293. It concatenates the octets into `reply` at 288. The outer round has `unwind-protect` at 435 and cleanup unpin at 452, then owner close at 455. Timeout is converted to `(:lost :timeout)` at 445; the reconnect branch also unpins `old` at 399. Those cover the inspected ordinary/error/timeout/replacement exits. A general theorem that every raw exception path reaches cleanup is **UNVERIFIED**; no omitted normal fault/timeout exit was found. Pull's plan is covered by the response-plan holder kind, but calling all consumers non-holders is still inaccurate.

### BP outbound/ingress/held payload: host paths exist; distinguish ADU copies from retained source rows

**HOLDER (copy), NOT a deferred arena handle on the traced outbound path.** `books/bp-outbound.lisp:67-72` finds the article using `(fn-bp-work-msgid work)`; 55-59 reads `(fn-arena-payload (fn-article-payload article) fn-arena)`; 94-101 encodes the resulting request with `(fn-bpa-encode request)`. `host/workflow-host.lisp:217-225` calls `fn-bprq-plan` over the workflow state and arena. `host/native/bp-obligation.lisp:146-191` calls that wrapper, destructures `(tag attempt outcome key adu destination retry)`, validates `adu` as an octet list, publishes attempt/outcome, and returns `(list key adu destination)`. Its serialization is real: `fnn-bpo-call-with-owner-journal` at 34-64 runs the thunk inside `fnn-owner-transit-serialized` at 44-59. After that call returns, 193-227 hands the ADU to the separate carrier as `:enqueue ... adu ...`. This is an owned encoded copy across the boundary.

**NOT “Host: NONE YET” for BP generally.** That text belongs specifically to `books/bp-held-payload.lisp:13-17` and its optimized comparison `fn-bphh-request-article-matches`, not BP transport or request production. Its body at 84-90 passes `(fn-record-payload held)` to `fn-bphh-octets-at-p`; the latter at 23-32 loops over `fn-arena-get`. No host call to these `fn-bphh-*` functions was found. The inspected host paths above refute the broader interpretation of the comment.

**Ingress:** `books/bp-ingress.lisp:848-860` finds the current article by record Message-ID and compares `(fn-handle-bytes (fn-article-payload article) fn-arena)` with the incoming record payload. That comparison is a synchronous arena read, not evidence that every surrounding BP state stores only Message-IDs. **HOLDER (component node carrier):** workflow state has a node slot, not only Message-IDs: `books/bp-workflow.lisp:308-320` defines `(list node config works receipts pending fenced used-txs)`; `fn-bp-initial-state` at 339-343 puts its supplied node there, and restart preserves `(fn-bp-state-node s)` at 654-663. `books/bp-ion-workflow.lisp:181-190` initializes from the supplied node and replays records; `host/workflow-host.lisp:19-24` supplies `(fn-sn-node sn)` and stores the returned workflow in the `fn-workflow-state` global. Later request generation reads that global at 224-225 and resolves the article in **that workflow node**, `bp-outbound.lisp:67-72`, before reading its handle at 55-59. Thus re-resolution by Message-ID alone does not establish re-resolution in the current top catalog. On the traced native command, however, journal open and the entire request thunk share one serialized region (`bp-obligation.lisp:44-59`), followed by store close at 60-64; an unlocked later reread of that node on this command is **UNVERIFIED**, not an established stale-handle execution. Any longer-lived workflow image must be in the row-root contract or refreshed before reuse. Exhaustive native ingress/receipt carrier closure is **UNVERIFIED**. Do not use the unused `fn-bphh` header to discharge it.

### Cold workers: HOLDER (derived physical extent), missing from the headline handle-liveness relation

Here is the requested full interleaving boundary:

1. While owner exclusion still holds, `host/native/owner.lisp:4533-4539` captures `entry` from `:fnn-extent-cold` and calls `fnn-owner-cold-issue-locked`. The latter at 4212-4225 issues through `fnn-extent-issue-direct` or `fnn-extent-issue-read` and retains `token` and `worker` in a cold-read object. `extent.lisp:830-843` defines the cache miss as `(throw 'fnn-extent-cold (list file eoff elen trailer))`: the arena dereference has already become a physical coordinate.
2. The owner call returns/unlocks. `extent.lisp:932-959`'s worker destructures `(id cid file eoff elen trailer)`, reads `fd` under the extent lock at 942-944, leaves that lock, then executes `(fnn-extent-pread fd octets eoff)` at 955. `fnn-extent-executor-job` at 481-505 stores the private result in the worker, so even completion has a retained result lifetime.
3. The issued row is `(ID CID FILE EOFF ELEN TRAILER PHASE)`, with no payload handle or catalog version (`books/page-read-ownership.lisp:8-24`). `fn-pio-complete` at 58-66 checks the exact token and phase: error gives `(:fault verdict)`, cancelled gives `:cancelled`, otherwise `:publish`; stale gives `:stale`. `books/page-read-direct.lisp:84-92` additionally requires the worker's matching returned job. It does **not** ask whether H's catalog row is still named.
4. `owner.lisp:4258-4263` publishes the result into the extent cache by `(file eoff elen trailer)`. The served cold-line continuation at 4396-4402 ignores the old `entry` and reruns `fnn-owner-handle-chunk` on `incoming`, rather than delivering H's old bytes as an already authorized article reply.

**SOUND for current whole-file close:** `extent.lisp:1230-1232` checks all issued rows through `fn-pio-file-clear-p`; its definition at `books/page-read-ownership.lisp:68-75` rejects every unsettled row naming the file. Cancellation deliberately leaves that ownership: `extent.lisp:912-918`, “Revoke this request's publication right; the worker still owns its fd.” The worker must actually return (`extent.lisp:517-521`) before settlement.

**HOLE for a new block-returning forget:** a file pin prevents descriptor close; it does not, by itself, prohibit reusing one extent inside that still-open file. If H's place P is recycled while this token exists, the worker still reads P. Correct trailer validation can turn that into a fault, but is not a storage-ownership proof; matching old cached bytes also do not authorize an obsolete semantic read. Keep P immutable until actual settlement/last borrow, or prove a copy/version protocol. The plain cold-line path acquires its issued row before the response pin at owner.lisp:4549 is reached, so it cannot silently be subsumed under “connection response pins.”

### Plans, mux, web, pinned connections, and cursors: HOLDER, with different representations

**Current ARTICLE/BODY response: HOLDER (copied reply), not the imagined handle-streaming plan.** `books/nntp-responses.lisp:137-139` executes `fn-nntp-article-response-of-bytes` over `(fn-nntp-article-bytes article fn-arena)`. That reader is defined in `books/nntp-session.lisp:27-37` through `fn-nntp-payload-bytes`, which materializes `fn-arena-payload`. The reply contains stuffed octets at responses.lisp:132-135. The native window renderer calls `fn-splan-window` with only `plan`, `size`, and an output buffer (`host/native/owner.lisp:446-459`), not an arena or handle. This source does not establish that the current native ARTICLE/BODY path streams a handle over many quanta.

**OVER: HOLDER (version/catalog dependency).** Its cursor is `(list group k top v legacyp owedp)` (`books/served-catalog.lisp:788-790`); the effect is `(list :over-cursor cur)` at 840-842. A later native quantum calls `fn-splan-cursor-step ... (fnn-live-stobj 'fn-arena) (fnn-live-stobj 'fn-cat)` under `fnn-owner-serialized` (`owner.lisp:515-527`). In `books/served-plan-cursor.lisp:136-153`, the step calls `fn-ovw-step`, emits reply bytes, and retains the remaining cursor. Thus the cursor need not literally store H to require the same catalog/version to remain readable.

The response hold is captured at `owner.lisp:4545-4549`, before leaving the quantum: “while a later cursor quantum still uses the original catalog.” Mux saves `rest` into `fnn-mux-conn-plan` at `mux.lisp:458-466`; 450-456 yields at cursor boundaries; 505 unpins only after all windows drain. A plan captured in an `:await`/`:redeem` continuation is explicitly included in the capture comment at owner.lisp:4548, and the return arms carry `step` at 4630-4635. Web loops over the same quantum renderer and unpins in `unwind-protect` (`web-host.lisp:114-125`), then holds an independent concatenated `reply` at 120. The ordinary web close also unpins at 133-136.

**Idle connection views: HOLDER (indirect rows), not necessarily an active response hold.** `books/owner.lisp:126-163` exposes connection `version`, `frontier`, `archive`, `index`, and `group-index`; in particular `fn-own-conn-archive` at 141-144 returns the retained archive slot. There is no basis for interpreting “named by a row” as only the current top view. The current reclaim implementation avoids that counterexample by repinning all connections: `books/owner-reclaim-pass.lisp:333-349` builds each connection from `fn-served-repin`, and `fn-orcp-swapped-owner` at 390-393 calls `fn-orcp-repin-conns` on the entire live connection list. Active responses prevent the swap (§4). This mechanism is different from assigning every idle connection an arena-generation pin. A generalized incremental unname must either include old-view roots or prove this atomic repin condition for its actual entry.

**NEWNEWS cursor component: HOLDER (article-list tail), not yet served.** `books/newnews-cursor.lisp:229-231` stores `(list :newnews groups threshold tail maxes horizon)`; 277-284 yields that tail then later calls `fn-nntp-article-tombstonep` on its article. The header at 42-46 explicitly says `fn-nnw-response` “is called by nothing served yet.” Count it as a component requiring a holder contract before integration, not as an observed native leak.

**LISTGROUP on the inspected served path: NOT an additional delayed handle reader.** `books/served-catalog.lisp:1572-1584` computes `shown` using `fn-scat-range-numbers` and emits `(fn-nntp-number-lines shown)` in the same call; it has no arena parameter. Its response allocation and connection view remain holders as above. A resumable implementation elsewhere being enabled is **UNVERIFIED**.

**Other continuation shapes cannot be dismissed by their names.** `books/served-plan-position.lisp:8,28-35` defines `(:position-plan current skipped-reverse remaining origin resource)` and retains both plan halves, origin and resource. Merely proving that an individual cursor's scalar position is not a handle would not show that its enclosing continuation releases every row/plan alias. Native reachability of this positioning component is **UNVERIFIED**.

### Checkpoint writer/file, recovery/log, export/inspect, snapshots, staged copies

- **HOLDER — checkpoint writer source list and frame list.** `books/store-checkpoint-arena-writer.lisp:145-159` extracts a held row's handle as a source; 164-168 dereferences a natural source through `fn-arena-payload`; 202-214 appends each payload to the output buffer and returns the remaining sources. `books/extent-retire.lisp:87-92` extracts source handles from checkpoint-writer state. This is not just a scalar count. The live publisher acquires `fnn-arena-pin` before `make-thread` (`owner.lisp:5253-5270`), uses it through publication and reseating, and unpins at 5152. These are already generation-protected holders, provided the pin lifetime still spans the entire new forget protocol.
- **HOLDER — durable checkpoint contents, but NOT a persisted pointer to the old process's fd table.** The checkpoint writer actually copies payloads (`store-checkpoint-arena-writer.lisp:202-205`: `fn-scka-payload-octets (fn-scka-src-payload s fn-arena)`). Reopen resets the arena and seals its own payload run (`io.lisp:2651-2673`: `fnn-payload-startup-reset`, repeated `fn-scka-seal-n`, then `fn-store-sco-decode-finish`). Thus forgetting a purely volatile copy is not automatically a dangling-name crash bug. Destroying bytes still required by a selected durable checkpoint/log is a different operation and needs the crash ordering in §2.
- **HOLDER — log members, in-flight and fenced.** The raw structure at `io.lisp:6316-6323` documents `(HANDLE . OCTETS)` and `(H FILE PLACE OCTETS)`; `fnn-log-members-in-flight` at 6745-6766 actually pushes `(list (car m) (fnn-log-extent-file log) place (cdr m))`. These exist independently of the published catalog and are not a disjunction in F4. Ordinary durable log replay scans file bytes and re-interns records: `io.lisp:7483-7514` registers fresh file ids and streams records/places; 2698-2706 invokes `fn-ssr-intern-step ... :resident ... (fnn-live-arena)`. The durable source obligation is preservation of those bytes and their binding, not identity of a previous process's fd integer.
- **HOLDER — recovery view/root.** `host/native/recovery-payload-view.lisp:4-18` acquires only in `:recovering` and returns `(fnn-make-snapshot-payload-view ... arena)`; release at 26-40 requires the matching lifecycle/arena and delegates to the core. A separate recovery root acquires a file lease using `(fn-hrs-h-file base-handle)` at 45-56; release occurs under owner then extent lock at 57-63. Whole-arena custody and physical-root custody are distinct, not interchangeable counters.
- **HOLDER — snapshot whole-arena view.** `owner.lisp:1653-1667` retains both token and actual arena; 1678-1685 releases only through the lifecycle check. The logical lease's release refuses a stale token and retains on non-`:joined` settlement (`books/payload-view-lease.lisp:48-53`). Its prefix is an explicit token field (`34-47`), so the macro must specify whether the lease covers `h < prefix` or conservatively every key. `fn-pvl-livep` takes **token and state** at 30-33; the proposed bare `:lease (LIVE-P ...)` is not yet a complete existential live-lease predicate.
- **HOLDER — export and reclaim capture.** Online export captures under owner exclusion, pins before spawning, and later reads the captured immutable record list (`owner.lisp:5274-5290,5300-5315`). The dry-run acquires a pin while capturing at 5465-5469 and unpins at 5504. Installing reclaim does likewise at 5651-5661 and 5788. These are existing generation holders, but their captured old rows must be included in the pin-to-reachability theorem.
- **NOT a served concurrent arena holder — inspected standalone inspect route; HOLDER (copy) after lookup.** `io.lisp:5252-5267` opens its own live store, calls `fnn-bridge-lookup`, writes the resulting bytes, then closes. The bridge at 1826-1828 calls `fn-store-sn-lookup` and converts its value to octets; the wrapper at `host/store-node-host.lisp:1561-1576` synchronizes history and invokes `fn-handle-bytes`. No owner mutex is present in that standalone route. Safety there relies on its own store/open lifetime, not on a fictional universal owner-mutex premise. Full offline tool/open-exclusion coverage is **UNVERIFIED**.
- **NOT a local arena handle reader — `fn-peer-relayed-octets` itself.** `books/peer-inbound.lisp:340-346` takes `cfg peer octets` and returns `fn-pu-relay-article` over those octets; no arena/handle argument. Mid-transfer peers/TCPCL still own input/output buffers and durable carrier jobs. The traced BP outbound carrier receives an encoded ADU (§1 BP), not an arena descriptor. Exhaustive TCPCL buffer-to-storage dependency closure is **UNVERIFIED**.
- **HOLDER — staged copy/old extent descriptor.** `books/payload-arena-extent.lisp:606-621` stages a buffer under H; 656-663 reseats H while preserving its stage slot “a reader that saw :staged still finds its copy.” At 685-697 release empties **only** the stage slot of an extent handle. File retirement separately checks zero arena file count and not log-named (`books/extent-retire.lisp:276-286`), stamps under owner exclusion (`owner.lisp:4981-4995`), then waits on generation and issued-file custody. Do not identify this representation retirement with loss of the logical payload.

### `fn-payload-kinds`: WEAK type-flow check, not a closed lifetime world

The checker is not limited to books, but also does **not** cover native host code. `tools/payload_kind_check.py:207-210` reads `(ROOT / "books").glob("*.lisp")` and `(ROOT / "host").glob("*.lisp")`; neither is recursive. `host/native/` is outside this path set. At 57 its seed accessors are exactly `{"fn-article-payload", "fn-held-payload"}`; 106-109 adds declared `:source` calls. At 247-265 it skips definitions without these seeds, accepts `:wire` definitions, and accepts declared sinks. This checks how certain retained payload values are consumed; it does not prove capture, lock dominance, non-escape, or future-use lifetimes. `books/payload-kinds.lisp:78-87` itself says `:handle` can mean “compares it ... returns it, or ignores it.” A kind declaration is not a holder theorem.

I enumerated all literal `fn-payload-kind ... :handle` declarations in `books/*.lisp` and all non-comment exact-symbol occurrences in recursive `host/**/*.lisp`. For **every actual payload-byte/length reader** in that set:

| Declared reader; definition quote | Direct host call sites and classification |
| --- | --- |
| `fn-handle-bytes`, `books/payload-arena.lisp:769-773`: `(fn-arena-payload h fn-arena)` | `host/store-node-host.lisp:1573-1575`: `(fn-handle-bytes (fn-apr-payload-of ...) fn-arena)`. Standalone inspect via `io.lisp:1826-1828,5252-5267`, and lookup in the offline verify path at `io.lisp:5360`; no mutex in the direct wrapper. Output is bytes; open/source lifetime required. |
| `fn-arena-payload`, exported at `books/payload-arena.lisp:473`; implementation `books/payload-arena-extent.lisp:433` (`fn-arena$x-payload`) | No literal direct host call; reached through wrappers such as feed, BP, checkpoint, inspect and response preparation above. Those paths have different lifetime regimes. |
| `fn-arena-payload-len`, exported at `books/payload-arena.lisp:471`; concrete definition `books/payload-arena-extent.lisp:403` | One exact host occurrence in the **guard**, `host/page-window-executor-host.lisp:230`: `(< i (fn-arena-payload-len h fn-arena))`. Its body at 231 calls `fn-arena-get`. Native caller `extent.lisp:403-421` validates a live snapshot view and reads under its documented owner capture exclusion; a cold result issues a window token before unlock. No unlocked length call established. |
| `fn-nntp-arena-prefixp`, `books/article-arena-reads.lisp:18-26`: `(equal (car prefix) (fn-arena-get h i fn-arena))` | No literal direct host call; synchronous NNTP/tombstone reads through the response/cursor chain above. |
| `fn-nntp-payload-bytes`, `books/nntp-session.lisp:27-33`: `(fn-arena-payload p fn-arena)` | No literal direct host call; response preparation is under owner exclusion; the later ordinary renderer reads materialized effects. |
| `fn-bs-handle-bytes`, `books/byte-store-scan.lisp:398-400`: `(nth h arena)` | No literal direct host call; this is the list-valued byte model, not an unlocked native fd read. |
| `fn-rcl-payload-bytes`, `books/store-reclaim-holders.lisp:153-157`: `(fn-arena-payload p fn-arena)` | No literal direct host call; online reclaim/export-related transformations reach it through their named entry wrappers and captured generation; offline uses require standalone lifetime. |
| `fn-rcl-payload-len`, same file:213-222: `(fn-arena-payload-len p fn-arena)` | No literal direct host call; same capture requirement. |
| `fn-rcl-payload-tombstonep`, same file:224-236: `(fn-rcl-arena-prefixp *fn-rcl-magic* p 0 fn-arena)` | No literal direct host call; same capture requirement. |
| `fn-rcl-payload-tomb-length`, same file:240-242: `(fn-rcl-tomb-length (fn-rcl-payload-bytes p fn-arena))` | No literal direct host call; same capture requirement. |
| `fn-nntp-newnews-without-payload`, `books/nntp-newnews.lisp:111-124`: declaration says “keeps a tombstone's handle, drops the rest” | No literal direct host call. It both reads and produces article carriers; do not classify the result as handle-free. |
| `fn-nntp-article-length`, `books/article-arena-reads.lisp:70-81`: `(fn-arena-payload-len p fn-arena)` | No literal direct host call; reached by served article/overview logic. |
| `fn-nntp-article-tombstonep`, same file:84-98: `(fn-nntp-arena-prefixp *fn-rcl-magic* p 0 fn-arena)` | No literal direct host call; reached by served logic and the unwired NEWNEWS cursor. |

The remaining declared sinks are not payload-storage readers: `fn-payload-handle-p`, `natp`, `<`, `fn-make-article`, `fn-held-make` (`payload-kinds.lisp:94-104`, “recognizer,” “compared,” “carried unchanged”); `fn-apr-refsp` (`acceptance-payload-ref.lisp:56`, “compares ... handle”); `fn-cat-rowp` (`catalog-logic.lisp:107`, “handle (natp)”); `fn-bpi-node-record-committedp` (`bp-ingress.lisp:776`, “compares ... handle”); `fn-scol-find-row` (`served-columns.lisp:86`, “reads no octets”); `fn-sn-committed-recordp` (`store-node-invariants-base.lisp:584`, “compares ... handle”); `fn-ctl-withdrawal-effect` and `fn-cev-withdrawn-by-some` (`control-authority.lisp:603`, “formal is ignored”; `control-evidence.lisp:356`, “which ignores it”). The named `fn-*` sinks have no literal non-comment direct host calls in this search. `natp` and `<` occur throughout host guards/comparisons; those are scalar tests, not deferred arena reads. Constructors/comparators can still preserve aliases and therefore matter to escape analysis.

**HOLE:** the table omits foundational read sites that do not have either seed accessor in their body. Examples: `fn-arena-get` in `page-window-executor-host.lisp:231`, the raw `fn-arena-stored` implementation reading `fn-arena$x-exti` and `fn-durable-realize-octets` at `extent.lisp:1122-1130`, and the remote writer's `fn-record-payload` at `consumer-remote-visible-buffer.lisp:91`. These defeat an argument that enumeration of this table alone closes all arena readers. The table above is a complete direct textual reader-call census, **not** a complete transitive proof of every host entry's reader reachability; that stronger closure remains **UNVERIFIED** and must be part of the implementation gate.

## 2. Liveness relation: UNSAFE as a forget precondition today

### HOLE — the proposed release site retires a representation, not an unnamed handle

The decisive source is `host/native/io.lisp:6837-6861`. It says “each fenced staged member's handle is re-pointed at the log extent that now durably holds its payload”; it calls `fn-lzr-commit-reseats` or `fn-arx-commit-reseats`, then:

```lisp
;; io.lisp:6856-6861
(fnn-arena-retire (mapcar #'first fenced))))
(let ((due (fnn-arena-release-due)))
  (when due
    (let ((arena (fnn-live-arena)))
      (dolist (entry due)
        (dolist (h (cdr entry)) (fnn-call 'fn-arena-release h arena))))))))
```

No catalog unname occurs in this function. Its concrete callee at `books/payload-arena-extent.lisp:687-697` is:

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
```

Logical identity is explicit: `books/payload-arena.lisp:692-694` states `(equal (fn-arena-release h fn-arena) fn-arena)`. That is exactly why it is safe to call for a still-live catalog handle. Full forget changes this contract.

**Concrete counterexample to the proposed wiring:** commit an article at H; leave its row named; COMPLETE reseats H to durable log storage and retires the stage at S; there are no arena-generation pins, so `:release` returns H; replacing the existing call with forget invalidates the still-named H; the next ARTICLE/feed/duplicate lookup reads it. This needs no missing holder and no race. A correct generated `unnamed` precondition would **refuse** this call, not justify it. Keep the existing stage release and create a separate retirement queue for genuinely unreachable handles.

### SOUND ordering — equality belongs in the protected side, subject to an acquisition protocol

`books/arena-reader-pins.lisp:215-224` pins `cur`; retire records `(cons cur items)` and increments `cur`; `:stamp` also returns old `cur` and increments. At 151-154, clear is `(or (atom pins) (< s (caar pins)))`. Thus a reader pinned **at** S is protected; strictly-below protection would be wrong. `fn-arpn-retire-stamp-covers-every-live-pin` at 416-424 states `pin <= stamp` and `new-cur = stamp+1`.

But there is no handle-unname stamp in the cited COMPLETE path: it stamps **after reseating** (io.lisp:6854-6856). Installing reclaim swaps catalog/history after durable checkpoint installation (`owner.lisp:5756-5761`) and repins all connections; this is not a per-handle unname event either. A proposed unname and stamp must be one owner-serialized operation. A reader must acquire protection **before** copying an old reference; a reader pinning after S must be unable to rediscover a pre-S reference. There is no reader “during” an indivisible owner-locked swap; one improperly acquired off-lock can fall into precisely that hole. The publisher code explains why pinning on the new thread would be too late (`owner.lisp:5246-5250`).

The current theorem `fn-arpn-release-postdates-every-live-pin` (`arena-reader-pins.lisp:429-434`) concludes only `(member-equal e (third st))` and `(< (car e) h)` for live pin generation h. It has no catalog, live payload, durable-root, issued-read, or whole-arena-lease argument. It proves the counter discipline, not semantic forget safety at io.lisp:6861.

### HOLE — durable naming/storage ordering

Required theorem: after any release/reuse of storage P, **every permitted recovery outcome** of every cut still has the required payload bytes for every row it can recover, or a validated replacement/tombstone/copy for that row. Publishing an in-memory replacement is insufficient. Counterexample for a proposed disk-block forget: last durable checkpoint names old content at P; memory installs a tombstone; no counted reader remains; P is returned/reused; death precedes the durable replacement; reopen selects the old checkpoint/log and needs P. Pin counts all become empty on crash, so rebuilding the count table cannot repair the lost bytes.

The existing installing reclaim orders its durable install before the swap and release (`owner.lisp:5756-5786`: `fnn-state-checkpoint-install`, `:installed`, `fn-owner-orcp-swap`, then log drop and `fnn-owner-release-extents`). The named cuts are `captured rewritten staged interned rebuilt installed swapped released` (`owner.lisp:5515-5516`); the source explicitly distinguishes pre-install old publication versus post-install new publication at 5512-5513. These are relevant existing boundaries, **not** a theorem about an unimplemented extent-reuse operation. The model must also cover failure/uncertainty and the window between last durable replacement and physical free/reuse.

Conversely, the current checkpoint copies a canonical payload run and reconstructs it on open (§1). If forget only frees an obsolete volatile buffer while all recoverable disk bytes remain intact, the hypothetical durable dangling-name argument does not apply. Specify the effect precisely: volatile pages, descriptor, file unlink, hole punch, reusable allocator extent, and logical identity have different obligations. The model's existing exemption is narrowly “close(2) has no durability effect and is not a step” (`specs/crash-model-v2.md:603-604`), not “all process-local bookkeeping permits disk reclamation.”

### HOLE — last name, not one removed name; all roots, not only TOP

The relation must quantify over **all** reachable row roots and pending users, or carry a proved exact reference count. Removing one catalog row does not imply no other row, historical view, writer source list, or workflow node names H. The connection archive and NEWNEWS tail are concrete examples (§1). `books/owner-reclaim-pass.lisp:270-295` retains rows unchanged when they are not wire records and interns the rewritten wire rows; a theorem that one rewrite produces a new tombstone handle is not a uniqueness theorem for all old handles.

Retry semantics do not require preserving every old full payload forever. `books/source-routes.lisp:273-287`'s `fn-sr-a-retry-after-reclaim-is-already-stored` assumes the **current held payload** equals `fn-rcl-tombstone-of ...`, then concludes `fn-store-existing-action ... = :duplicate`. Preserve the tombstone's identity evidence and every live root to it. That theorem supplies neither permission to erase a still-named tombstone nor proof that no alias to the original payload remains.

### HOLE — omitted pending/fenced members and physical custody

The F4 sentence (`SKETCH.md:120-123`, “named by a row ... OR ... pinned ... OR ... lease”) lacks the log members that its own R1 lists. The raw log stores them before COMPLETE (§1). If “row” is broadened to include these plus cold-read/window/source/continuation carriers, write that definition and prove every producer maintains it; otherwise add explicit clauses. A cold row names P, not H, and may protect storage even when H itself can safely be invalidated. Separate **logical handle invalidation** from **physical extent reuse**.

### WEAK — response count is backed by an identity table, but not by plan reachability

The sketch's “counted, not identified” is incomplete. `books/response-plan-pins.lisp:30-46` maps cid to generation, rejects duplicate acquire, and releases the generation recorded for that cid. `fn-rpin-step-preserves-funded-ownership` at 94-100 proves the response count at each generation is bounded by the arena count. The host updates both under one pin lock (`owner.lisp:501-509`). This proves an accounting relationship; it does not say that every handle reachable from a plan is covered by its generation or that every final use precedes its unpin. The capture/drain/cleanup paths provide source evidence, but the proposed composed theorem still owes that connection.

**Required precondition for ARENA-FORGET:** no reachable logical root needs H; every older captured root either ended or is covered by a live hold; no pending publication can expose H after the check; every physical dependency on H's former storage has ended or uses a separately preserved immutable copy; durable recovery remains valid at every physical-release/reuse cut. Check and mutation must exclude new acquisition, and reuse must preserve incarnation identity. None of the counter theorems cited by the sketch alone establishes this.

## 3. Macro attack

### HOLE — opted-in counter writers are not a closed holder world

The proposed check searches for callers of `NAME-step` and interfaces returning its carrier (`SKETCH.md:176-181`). A holder that only copies `(fn-record-payload row)` never enters either set; the remote-visible continuation above is a concrete shape. Raw Lisp worker structs, captured lambdas, globals and fd/offset tokens also live outside an ACL2 function-world walk (`extent.lisp:483-505`, worker result storage; `owner.lisp:5255-5268`, capture lambda). A `:program` wrapper can pass a carrier across calls without returning the counter (`consumer-remote-report-host.lisp:61-90`).

**Change:** start from resources/read primitives and carrier-producing interfaces, not only opt-in counter mutation. Track transfer/borrow/escape and final use. Walk macroexpanded/translated bodies in the appropriate world; cover raw native code separately. Unknown dynamic calls, `apply$`, function-valued fields or macro-generated calls require a checked contract or rejection. A call graph alone cannot establish lock dominance, generation pairing, or that a reference is not stored for later use. The “second stage” is essential before any deletion claim; it is deferrable only while the generator is explicitly an accounting component that authorizes no forget/close.

### HOLE — identity and duplicate release disappear in a count-only generalization

`SKETCH.md:129-153` makes holds counts per resource key and exposes `(:drop K)`. Two holders A/B of K can have count 2; A drops, then a duplicate A drop decrements B's hold. “Drop of an unheld key is refused” does not catch this because K is still held. The present generation counter intentionally knows only aggregate multiplicity (`arena-reader-pins.lisp:123-142`); response ownership adds cid identity (`response-plan-pins.lisp:35-46`); cold reads add exact token and worker incarnation (`page-read-direct.lisp:70-92`). Preserve those layers.

Require an acquisition identity, holder instance/kind, resource incarnation, and exact release receipt/ownership transition. Do not collapse cancellation, actual worker return, cache transfer, and refund into one drop. `extent.lisp:912-918` and `owner.lisp:4264-4288` explicitly keep ownership until the actual result alias is relinquished.

### HOLE — `:carried-count` must prove the exact relation, not cite an arbitrary theorem

`SKETCH.md:142-144` says `ZERO-THM` is “cited” as the existing relation. A supplied theorem symbol is insufficient. Read its literal statement and generate/prove an instantiated obligation of this shape: under the invariant **carried by the host-called state**, `COUNT(state,key)=0` implies no holder in the **declared population** names that key. Also prove initialization and every mutation preserve the count relation, and that the host release reads that same column. An unrelated zero theorem, extra unestablished hypotheses, wrong key argument, different state component, or equality only on an unreachable branch must fail admission. A proof of a regenerated canonical goal using the nominated theorem is preferable to pretending semantic equivalence is a string match.

For multiplicity/quotas, require the exact count equality, not merely zero-implies-none. The file count alone is deliberately only one layer: `books/extent-retire.lisp:282-284` additionally requires `not member ... named`, and `extent.lisp:1230-1240` checks issued rows and the resource-ledger close verdict.

### HOLE — acquisition/release summaries have no complete interface contract

“By :use of the declared FN's theorem” (`SKETCH.md:154-156`) does not identify that theorem in the input syntax. Add explicit proof symbols or generate their precise obligations from a checked interface schema: full formal/result positions, pre/post state, key set/multiset, ownership token, success/refusal/fault/uncertain alternatives, and effect classification. Check the actual result, not one non-unique success keyword. Multi-key acquire needs a set/list of acquisitions and all-or-nothing/partial-success semantics. A release that transfers custody to cache is neither disappearance nor unchanged state.

“Any other answer ... leaves the table as it was” needs a proved frame condition for **all** other outcomes. Refusal can legitimately spend an identity without creating a hold: `extent.lisp:86-96` reserves a fresh incarnation before attempting OS open, and its docstring says “Failed constructors spend the name.” Design the frame condition around resource ownership, not equality of every field regardless of documented allocator behavior.

### HOLE — classify the release effect, not the counter's persistence

`SKETCH.md:148-149,163-168` accepts `:process-local "rebuilt at open: THM"` or one durable program/cut. A count table being ephemeral says nothing about whether its release punches a disk hole, unlinks a file, or returns allocator blocks. Require a structured theorem reference and generated goals about recovered resource state **and** effect noninterference/recovery relation, plus host effect mapping. A rebuilt-at-open table need not be `NAME-initial`: recovery can legitimately rebuild live names/leases; proving it initially empty is wrong for durable retention state (`books/retention.lisp:331-357`, active pins and release records).

Pure volatile stage-buffer freeing can be process-local; deleting recoverable disk contents cannot. Existing close exemption does not exempt a SIGKILL injection from needing a recovery interpretation. If the macro emits `NAME-decided`/`NAME-released` process-death cuts, both need a modeled coordinate and recovery contract, including any caller's pending durable operations. One supplied `CUT` does not map both sites or the effect sequence between them.

### HOLE — a declared cut is not automatically a checked host release

`tools/native_program_check.py:75-78` maps only `fn-bs-finish-program -> fnn-finish` and `fn-bs-recover-stage-cleanup-program -> fnn-sweep-staging`. Its primitive set at 105-107 contains `fnn-at`, not the proposed `fnn-holder-cut`. `check` at 936-945 checks `programs_named()`; `programs_named` filters with `p in PROGRAM_HOSTS` at 846. Adding `HOLDER_CUTS` names alone does not cause a new host release body to be walked.

There are other specialized source checkers; rotation is an example (§4), so do not infer their absence merely from this map. But for def-holder, require an explicit `(host file, function, model program, effect mapping, all cut sites)` binding and reject uncovered host injection sites globally. Check placement/order, not just that a string appears in a declaration. Exercise each reachable cut and label unreachability explicitly. A process-local rebuilt row can carry a trivial durable-state-preservation theorem, but cannot evade AGENTS.md's process-death rule by naming the candidate “rebuilt.”

### WEAK — late-drop outcomes must survive the host boundary

`SKETCH.md:161-162` says `(mv st :refused)` is distinct from a refused acquire, but the value `:refused` alone does not encode which operation failed. Either the operation tag remains in the boundary result or use structured reasons. Also preserve actual current API semantics: `fn-rpin-step` returns `:absent` for idempotent cleanup (response-plan-pins.lisp:40-46), and native unpin accepts `(:released :absent)` (`owner.lisp:497-499`). Do not turn legitimate cleanup into a user-visible uncertain write or silently turn an inconsistent release into success. Generate/check boundary mapping to the caller's result/reply/exit contract; not every internal drop needs a new network reply, but every externally reported outcome must retain its meaning.

### WEAK — teeth obligations can still be omitted from the checking world

The contract correctly reads the theorem from the world and checks positive `Hi and C` and each removal `retained Hj and not Hi and not C` (`generators-2.md:31-39`). That is useful. But owed rows are source-side and the refusal occurs only when somebody executes `defteeth-check` in a test/image world (`:43-46`). Omitting the test book, checking before later declarations, localizing a row, or hand-inserting an unvalidated `fn-teeth` row can leave a production image apparently complete. These are design holes, not demonstrated behavior of an implementation that does not yet exist.

Require a final mandatory closure check over the actual image's source obligations, matched theorem statements/digests, and evidence that the corresponding test world certified; refuse hand table rows or validate their generated obligations independently. Ratcheting only newly registered keystones (`generators-2.md:48-52`) does not cover an unregistered theorem or an omitted generated obligation. Include preservation/acquisition/representation bridges when they are relied upon as keystones, not only sketch items (c)/(d) (`SKETCH.md:169-172`). A hypothesis-free theorem still can have a meaningful implementation mutation; lack of hypotheses does not by itself justify `:mutations (:none ...)`. Failed proof search is not the negative witness—the explicit falsifying evaluation is.

### SOUND only with an actual subject bridge — an existing implementation can remain

`SKETCH.md:190-192` allows retaining fn-arpn and showing it equal to the generated table. That is acceptable only with a named refinement/equality connecting the **host-called operation**, its outputs and state effects, to the generated transition, under a maintained invariant. The host actually calls `fn-arpn-step` (`io.lisp:6787-6791`); equality of two unused recognizers or initial tables is insufficient. Avoid running parallel counter tables that can drift. Generate wrappers/theorems around the existing representation where that is smaller; “net-negative” lines is a design preference, not proof of correct subject selection.

**Additional HOLE:** handle key order and retirement-generation order are distinct. In `fn-arpn-step` the first state field is a generation and pending entries carry its stamp (`arena-reader-pins.lisp:183,220-224`). `SKETCH.md:197-200` instantiates `natp :ordered t` for handles while registering generation pins. A natural handle does not become comparable to a retirement stamp by sharing the `natp` recognizer. Separate resource key, holder token, acquisition epoch, and retirement stamp in the macro signature; prove the relation between them.

## 4. Findings verified and rated

### F1 — claim-gap; alleged served close/fd-reuse race not established

Full function, `host/native/extent.lisp:1145-1167`:

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
    (let ((acc nil))
      (declare (type (simple-array (unsigned-byte 8) (16384)) octets))
      (loop for k of-type fixnum from 2047 downto 0 do
        (let ((w 0) (base (* 8 k)))
          (loop for b of-type fixnum from 7 downto 0 do
            (setq w (logior (ash w 8) (aref octets (+ base b)))))
          (push w acc)))
      acc))))
```

The lock gap is real. Direct raw callers are its `*1*` wrapper (1169-1170) and `fn-pgs-fill-frame` (1183-1189). The frame form fills history-record pages: `books/history-records.lisp:440-459` calls it in the executable `fn-hrs-frame-fill-pgs`/`fn-hrc-frame-fill` chain; `history-records-disk.lisp:102-109` calls it to load disk image runs. The concrete host entry is `fnn-state-checkpoint-adopt-image`: `io.lisp:2630-2631` registers `file` with `fnn-extent-register-at path base` and calls `fn-store-sco-image-open`. The wrapper calls `fn-his-open` and `fn-his-check-row` (`host/store-node-host.lisp:998-1018`). This is real checkpoint-history paging during open, not the issued payload-worker route. Crucially, the caller immediately runs `(fnn-call 'fn-his-release (fnn-live-hrecs))` at `io.lisp:2635-2636`, with the comment “the adopted words are not kept (nothing reads them yet).” Later served use of that adopted image, including an arbitrary served ARTICLE invocation of this raw fill, is **UNVERIFIED**; do not substitute “served” for the known open/history-image validation path.

Why the proposed fd-reuse execution is not currently demonstrated:

- `extent.lisp:141-149` registers a **fresh id** for the checkpoint image; the docstring says “held for the process's life.” The underlying register issues an ACL2 incarnation at 91-96 and installs a newly opened descriptor at 106-113.
- The only source of retired ids found is `owner.lisp:4946-4956`: `new-id` is a **different** `fnn-extent-register` call for payload reseating; retirement adds previous `*fnn-extent-checkpoint-id*` and ids whose paths are in `dropped-paths`. It does not retire every id with the checkpoint path.
- Both callers supply segment paths: publication computes `(mapcar ... fnn-segment-path-at ... covered)` at 5120-5122; reclaim does the same at 5781-5786. `fnn-extent-ids-of-paths` at extent.lisp:1217-1223 matches only this supplied path list. The separate history-image id at checkpoint path therefore does not enter this set on the traced paths.
- The only call to `fnn-extent-close` found is pending retirement in `owner.lisp:4855`. No path was found that puts this image id there. The primitive itself can close any supplied eligible id (`extent.lisp:1225-1253`), so exclusion is a caller/namespace fact, not enforced by an image-root type or local pin in the fill.

If future retirement includes image ids, then lookup fd → unlock → retire/close fd → another open reuses fd → pread would be possible without new custody. Today that extension is hypothetical. **Fix:** explicitly represent the image-root lease and its last reader/close rule, or enforce and check the present process-lifetime exclusion. The fill's lack of a local issued row does not by itself prove a reachable current UAF. Also distinguish the stale “held for life” comment on general log extent registration (`io.lisp:7492-7495`) from the separately allocated image descriptor: log extents really are retired online.

### F2 — nit in declaration/validation; coverage accusation disproved

The declaration is exactly (`io.lisp:6284-6287`):

```lisp
(defparameter +fnn-log-model-cuts+
  '("log-written" "log-fenced" "log-truncated" "log-recovered"
    ;; books/store-log-extend.lisp fn-lg-extend-program (fnn-log-ensure-extent).
    "log-extended" "log-extent-fenced"))
```

The injection function really does not validate membership (`io.lisp:6348-6354`):

```lisp
(defun fnn-log-at (point)
  "A developer-image cut: FN_NATIVE_LOG_FAULT=NAME (a +fnn-log-model-cuts+
name) kills the process at NAME with SIGKILL, so no cleanup runs."
  (let ((armed (fnn-developer-selector "FN_NATIVE_LOG_FAULT")))
    (when (and armed (string= armed (string-downcase (symbol-name point))))
      (sb-posix:kill (sb-posix:getpid) sb-unix:sigkill)
      (fnn-fault "test SIGKILL did not terminate the process"))))
```

All literal calls in `host/`:

| Name | `host/native/io.lisp` line | In `+fnn-log-model-cuts+`? | Model/check status |
| --- | ---: | --- | --- |
| log-truncated | 6718 | yes | log program map |
| log-recovered | 6720 | yes | log program map |
| log-written | 6743 | yes | log program map |
| log-fenced | 6903 | yes | log program map |
| drop-unlinked | 7265 | no | segment drop program |
| drop-durable | 7267 | no | segment drop program |
| rotate-created | 7316 | no | segment spare program |
| rotate-fenced | 7318 | no | segment spare program |
| rotate-renamed | 7377 | no | segment rotation program |
| rotate-headed | 7388 | no | segment rotation program |
| rotate-durable | 7415 | no | segment durable-rotation program |
| log-extended | 7865 | yes | log extend program |
| log-extent-fenced | 7867 | yes | log extend program |

For the six declared names, `tests/campaign/native_cuts.py:690-716` compares the declaration, program cuts, and every `fnn-log-at` in each mapped host function. For the seven segment names, **a separate map exists**, at 737-742:

```python
SEGMENT_PROGRAM_HOSTS = {
    "fn-lgs-spare-program": "fnn-log-prepare-spare",
    "fn-lgs-rotate-program": "fnn-log-rotate",
    "fn-lgs-rotate-durable-program": "fnn-log-make-durable",
    "fn-lgs-drop-program": "fnn-log-drop",
}
```

`verify_log_segment_cut_map` at 751-769 checks host operations/cuts in program order and compares **all** `fnn-log-at` names in each mapped body to its model cuts. Those cut declarations are present in `books/store-log-segments.lisp:461-495` as `(list :cut "rotate-created")`, `rotate-fenced`, `rotate-renamed`, `rotate-headed`, `rotate-durable`, `drop-unlinked`, and `drop-durable`. The verifier is called by `tests/test_native_cut_map.py:13` and `tests/test_native_checkpoint_auto.py:130`. The standalone `native_program_check.py` map is narrower (§3); it does not supply global closure over arbitrary new release functions.

They are also **not silently unexercised**: `tests/test_native_log_compaction.py:43-44` lists all seven, and 227-235 iterates them, sets `FN_NATIVE_LOG_FAULT`, asserts return code `-9`, reopens, and compares all inspected articles with the before image. This consultation did not run that test, so a passed result at this revision is **UNVERIFIED**.

These are genuine durability-relevant deaths: `io.lisp:7264-7267` unlinks then fences the journal directory; 7313-7318 creates/preallocates then fsyncs the spare; 7367-7388 renames and writes the head; 7413-7415 fences file then directory. An unknown selector with no matching `fnn-log-at` simply never triggers; an extra cut in a **mapped segment body** would fail the set comparison; an extra cut in an **unmapped function** is not globally rejected by this mechanism. **Fix:** unify the injection name registry or explicitly include the segment vocabulary, validate unknown selectors, and add global injection-site closure. Do not file “rotation/drop have no model crash points” as a bug.

### F5 — claim-gap/liveness limitation, not a proved permanently leaked response pin

The gate is exactly `((not (equal readers 0)) :readers)` in `books/owner-reclaim-pass.lisp:156-163`; the host supplies `(1- (fnn-arena-reader-count))` at `owner.lisp:5745-5748`, excluding the reclaim pass's own pin. Any undrained response with a valid response hold therefore prevents the swap even if its remaining data is already copied. The host tries eight rounds (`owner.lisp:5518-5520`) and returns a named deferral at 5774-5777; it does not loop forever inside the pass.

A totally stalled socket has a deadline: `mux.lisp:463-466` sets `out-deadline`; timers at 1142-1149 raise the scoped timeout; `fnn-mux-guarded` at 316-345 routes faults to finish; `fnn-mux-finish` at 270-274 unpins `(or cid opened-cid)`, retaining a way to identify the holder even when fault handling clears cid. Normal drain unpins at 505. This disproves the simple “one timed-out connection holds forever” story. The timeout is per output window, not a total reclaim admission deadline; sustained overlapping responses can continually make the zero-reader test fail. No eventual-reclaim/fairness theorem was established, and no bounded whole-response duration is proved by those per-window deadlines.

The “called by NOTHING” statement also needs precision. `books/owner.lisp:3176-3188` defines `fn-own-min-pinned` recursively and calls it from `fn-own-reclaim-floor`. `books/owner-invariants-served.lisp:560-579` proves bounds including `fn-own-reclaim-floor-below-every-pin`. No executable served/reclaim consumer of that floor was found in `books/` or `host/`. Yet `specs/lifecycle.md:77`, row 5, says “the pin holds the version below the reclaim floor (`fn-own-min-pinned`).” That is not a source description of the current reclamation gate. **Fix:** correct that specification and prove the actual response-hold/repin protocol. If reclaim must progress under continuous read traffic, adopt a proved version-retirement protocol or explicit bounded admission/draining policy; deleting the zero-reader gate without preserving old cursors would create a safety bug.

### F3 — claim-gap in the finding; key premise contradicted by current host source

`books/retention.lisp:350-356` includes disjointness in its recognizer. But `fn-retain-admissiblep` at 363-368 deliberately has `(mbe :logic (fn-retain-statep s) :exec t)`. A guard conjunct does not establish that the served executable rechecks the entire recognizer each call. Its fallback known-id scan is real at 374-377, but “twice per prepare” on the current served route is **UNVERIFIED**.

The claim that the host never asks the carry is false: `host/owner-host.lisp:1825-1835` computes `fn-prc-refresh` then passes `carry` to `fn-pout-prepare-article`; the buffer route at 1985-1986 refreshes it and at 2010-2012 passes it to `fn-ppc-pout-prepare-article-cat`. The latter's purpose is explicitly the carried prepare chain (`books/post-prepare-catalog.lisp:7`), and the direct prepare wrapper `books/owner-prepare-served.lisp:55-63` calls `fn-prc-sbud-prepare`. **Fix:** trace and measure the actual executed branch before proposing this performance row; retain any genuine fallback/guard-boundary cost as a separately established claim. No cost measurement was run here.

## 5. Missing resources and design scope

**HOLE — memory and physical custody are not just hold counts.** The sketch says “holding is a carried count per key” (`SKETCH.md:129-130`); the actual page ledger is `(budget charged next bindings [permanent-baseline])` (`books/page-read-ledger.lisp:10-16`), and file-held states include `:issued :cached :discovery :file-pin :window` at 83-91. Allocation, reservation, borrowing, transfer, cancellation, settled-but-cached data, allocator highwater and physical deallocation have different moments. `owner.lisp:4264-4288` explicitly waits until the result-bearing activation returns before refunding. A generalized holder must complement those resource contracts, not replace them with an integer and a release keyword.

**HOLE — principal/account attribution.** The proposed `(KIND :acquire (FN :key K-TERM ...))` schema has no principal, request, charge vector or budget (`SKETCH.md:137-149`). It answers “how many” but not “whose reservation pays for it,” and does not ensure reserve-before-allocate. The existing read token includes `cid` (`page-read-ledger.lisp:37-39`), but cid alone is not a proved principal/account binding. Add a checked link to the admitted operation/account, exact resource demand, transfer lineage, and refund receipt. Existing owner control turns retain returned slots/pool/state before classifying results (`owner.lisp:1841-1867`); the new macro must preserve that protocol.

**HOLDER — sockets, connection/TLS state, compression contexts, timers.** Mux finish frees SSL, releases handshake ownership, closes TLS channel, frees compression output and shuts the socket (`mux.lisp:275-304`). Its timer loop retains deadline/resume/idle references (`1133-1185`). These are resources and continuation roots outside R1-R6's payload/file focus. A connection fd is not an extent-file incarnation; give it its own acquisition/close identity and custody. Do not infer TLS/library allocation safety from an ACL2 response-pin theorem.

**HOLDER — staged files/spares and durable publication directories.** The log's spare is `(INDEX PATH FD)` and has a separate lock (`io.lisp:6332-6337`); prepare opens and fsyncs it (`7313-7323`), rotate consumes it by rename (`7360-7377`), discard closes/unlinks it (`7277-7287`). These require reservation, constructor-failure cleanup, ambiguous-effect handling, and crash interpretation. Counting a payload handle does not account for the staged file or its on-disk allocation.

**HOLDER — worker/executor slots, operation slots, fixed buffers and scheduler quanta.** `extent.lisp:988-1014` binds an idle worker and issued row before enqueue; `owner.lisp:1826-1867` threads actual slot/nonce/slots/pool across a paid owner quantum. Model slot ownership and work budget separately from file ownership. A worker's resource demand can persist after cancellation; repeated safe yields must not receive free allocations or lose the charged source carrier.

**WEAK — def-entry / def-command boundary.** Shared cut generation is a reasonable direction (`SKETCH.md:183-186` says def-holder owns cuts and def-entry reads the table). It still needs one authoritative entry contract connecting argument/result carriers, success/refusal/uncertain outcome, principal admission, physical effects, lock/borrow scope, and all command continuations. Def-command should carry that ownership through yield/resume/cancel/drain; def-entry should check the actual host-called boundary; def-holder should prove the resource relation and permitted release. None should treat another macro's unvalidated table row as proof. The only supplied interface sketches are the consultation files; any additional implemented def-entry/def-command integration guarantee is **UNVERIFIED**.

**Recommendation:** build the counter/refinement machinery first around the existing generation and exact issued-read-token protocols; make reader/carrier closure and physical-effect mapping mandatory before any destructive instance. Preserve stage-release semantics. For ARENA-FORGET, first define the full root set and separate logical dead-handle retirement from stage-copy retirement and physical extent reuse. The smallest safe deliverable is not a new call at io.lisp:6861; it is a host-connected last-reference theorem whose precondition the intended release site actually establishes.
