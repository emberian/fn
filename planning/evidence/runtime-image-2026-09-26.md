# runtime-image (2026-09-26): where the 281 MB floor goes, and why an executable-closure image does not shrink it

Lane runtime-image, D35. Branch `lane/runtime-image` from dev 91c59dabb.
ember asked why a node needs 288 MB of heap before it holds an article and
whether the distributed image could be a different kind of image. This lane
measured the image and tested the brief's proposal (an image of the
executable closure only). It changes no book and no image build. It adds the
measurement tools under `tools/runtime_image/` and this record, with its
data in `planning/evidence/runtime-image-2026-09-26/`.

All figures are from hbox (SBCL 2.6.8, ACL2 8.7, `/tank/fn/toolchains/w28/acl2-literal-4g`).
They were measured on images built from 91c59dabb by `tools/hbox_native.sh --label base
--images developer,production` (tree `/tank/fn/scratch/runtime-image/native-base/`;
`fn-host.core` sha256 d8f28a9b...e624e19; `tests.test_native_operator_verbs`
OK (22 ran, 0 skipped) on those images, log 91f537da...ff400). MiB throughout;
SBCL's "MB" is MiB.

## 1. The floor

| Measure | bare SBCL | bare ACL2 8.7 core | production image (91c59dabb) |
| --- | --- | --- | --- |
| Dynamic space the core needs ("N KiB required") | 12.9 MiB | 159.5 MiB | 271.4 MiB |
| Smallest working heap: fresh development store, 1 POST (240), ARTICLE (220) | n/a | n/a | 281 MB (274 MB: dies before LISTENING; 268 MB: refused at start) |
| RSS idle after start, 1024 MB dynamic space | 8.1 MiB | 37.3 MiB | 68.2 MiB |
| RSS after 1 / 100 / 1,000 POSTs of 2,048 octets (scale profile, A = 4,096) | | | 73.8 / 143.9 / 174.7 MiB (VmHWM 177.5) |
| Start to LISTENING (fresh store) | | | 0.023 s |
| Core file on disk | | 223 MiB (`saved_acl2.core`) | 376.6 MiB (394,842,952 octets) |

Evidence: `bare.txt` (88c46784...), `core.json` (a36d63ac...), `base-floor.json`
(42f2b199...), `base-run.json` (78a94501...). The OpenBSD record's 288 MB
(release-openbsd, SBCL 2.6.3, development profile) is the same floor on the
other platform.

The floor is the core. The heap is the saved core's content plus about 10 MB
to run. What sits in the core, from an unsaved session that loads exactly
what `host/native/build.lisp` loads (`tools/runtime_image/measure-session.sh`,
log aea99222...; bare ACL2 5c1ce39c...):

| Part | Size |
| --- | --- |
| ACL2 8.7 itself (the core's own requirement) | 159.5 MiB, of which its logical world holds 72.0 MiB (35.3 MiB of it defconst values) |
| What fn adds | 111.8 MiB |
| of which the logical world | 86.8 MiB (world total 158.9 MiB against ACL2's 72.0: 449,215 triples against 137,624; 32,345 events; 8,145 theorems; 17,836 functions) |
| of which code and other data | about 25 MiB |

The session's own dynamic usage after a full collection is 397.1 MiB (bare
ACL2: 245.2 MiB). That is 125.7 MiB above the saved core, which is
build-session state that `save-exec` does not keep. The world figures are
object sizes reachable from the world (`ri-world-report`), and the saved
core keeps the world whole.

The largest world properties in the production world are GLOBAL-VALUE (event and command landmarks, include-book records:
56.2 MiB), CONST (35.6), POS-IMPLICANTS (tau: 15.8), LEMMAS (14.2),
UNNORMALIZED-BODY (8.6), TYPE-PRESCRIPTIONS (3.2), UNTRANSLATED-THEOREM
(3.1). The node's RSS stays well under the floor: the core is mapped, and
pages the running node never touches (most of the world and the prover) are
never resident. The floor is a reservation, and it is what a datasize limit
refuses (OpenBSD: 1,536 MB `default`, 4,096 MB `daemon`). The resident cost
is what grows with the store: 68 MiB idle, 175 MiB after 1,000 posts.

## 2. The per-call question

The host calls executable counterparts. `fnn-call` (host/native/io.lisp,
"Calls into the certified core") applies `ACL2_*1*_ACL2::NAME` for every
entry, which is how every current-view.json host function is reached. The
host functions are the :program wrappers of `host/*.lisp`. Inside them,
guard-verified subjects run as compiled raw Lisp.

To confirm this, `tools/runtime_image/world-probe.lisp` is loaded into the
production core before `(acl2::sbcl-restart)`. It counts every call of the
ACL2 functions that read or evaluate through the world (`fgetprop`,
`sgetprop`, `global-val`, `w`, the `ev` family, `trans-eval`, `ld-fn`,
`wormhole1`, `translate*`, `fmt`), every `*1*` call of an fn function, and
the raw calls of named subjects. For each world read it also counts the
nearest fn frame. The run was 100 POSTs, then 100 ARTICLEs, on a fresh scale
store (`node_measure.py probe`, `base-probe2.json` 38aba988...):

| Path | World reads | `*1*` calls (distinct) | raw subject calls | ld / ev / trans-eval / wormhole |
| --- | --- | --- | --- | --- |
| start (LP and the return-from-lp form) | 30 fgetprop, 21 w, 5 global-val | 100 | 0 | 1 ld-fn, 1 trans-eval, 1 translate11, 2 ev-rec |
| 100 POSTs | 900 fgetprop + 900 w = 9 per POST | 9,186 (60) | 601 `fn-scar-ocfg-read-tls-prefix`, 200 `fn-rclb-existing-action` | 0 |
| 100 ARTICLEs | 0 | 561 (16) | 101 `fn-scar-ocfg-read-tls-prefix` | 0 |

All nine world reads per POST come from the `*1*` of logic-mode host
wrappers: `fn-store-identity-text` (2), `fn-store-charge`,
`fn-store-frame-store-protected`, `fn-store-metadata-frontier-frame`,
`fn-store-metadata-frontier-next`, `fn-store-obligation-id-of`,
`fn-store-publication-admissibility` and `fn-store-txn-name`. It is ACL2
8.7's own dispatch (interface-raw.lisp, `oneify-cltl-code-1`):
`(symbol-class fn (w *the-live-state*))` decides whether the guard-verified
raw body may run. There is no defattach dispatch through the world;
attachments are raw special variables. No guard error, `ld`, wormhole or
evaluation happens on either path. The ARTICLE path reads no world at all.
Scope: encapsulation sees only full calls, and ACL2 8.7 declares none of
these functions inline.

## 3. The executable-closure image (the brief's proposal): measured, not worth building

`tools/runtime_image/closure.lisp` computes the host's executable closure over
the production world. The roots are the 1,156 ACL2 function symbols named in
`host/native/*.lisp` and the 920 functions the ld'ed host wrappers define.
The edges are each function's body, guard and attachment. The closure has
7,374 functions (238 built into ACL2), and each is mapped to the book that
introduces it (Kestrel's `book-of-event`, restated so that no book enters the
world). `tools/runtime_image/closure.py` then keeps every book that
introduces a reached function or carries `verify-guards`/`defattach`, plus
their non-local include-book ancestors, which ACL2 loads regardless
(`prod-books.txt`):

| | Books | Theorems |
| --- | --- | --- |
| In the production world | 400 fn + 21 system | 7,313 fn + 212 system |
| Introduce a reached function | 325 | |
| Guard/attachment books | 22 | |
| Ancestors only (theorem books a kept book includes) | 51 | |
| Kept | 398 | 7,313 (all) |
| Excluded | 2 (`codec-attach`, a one-line umbrella whose two children stay; `store-observed-traces`) | 0 |

The fn books interleave definitions and theorems. Every invariants book
(owner-invariants, byte-store-invariants, nntp-effects, ...) is a non-local
include of a book the host executes. So the brief's condition "where ACL2
requires a book's theorems to include it at all, the book stays" keeps 398
of 400 books and every theorem. The 21 system books are all included by kept
fn books.

A session over the 66 release roots (`build.lisp` with its include-books
replaced; `rel-ri.txt`, log 9d58f126...) measured dynamic usage of 393.2 MiB
against production's 397.1 MiB, which is 3.9 MiB or 1.0%. The world is
157.9 MiB against 158.9 MiB, and the closure is unchanged (7,374
functions). No `release` build variant was added, and HST-017 was not taken:
a variant that saves 1% is debt, not a release. Tasks 4 and 5 (qualifying a
release image, byte-identical transcripts, the throughput gate, the OpenBSD
VM) have no image to run on and were not run. `node_measure.py run
--transcript` records a served transcript for that comparison when one
exists; today's image's transcript is `base-transcript.bin` (8768dea4...,
kept on hbox).

## 4. What does shrink it: an image without the logical world

The same session stripped the installed world after measuring it
(`ri-strip-report`; the session is unusable afterwards and nothing is
saved). It kept only the twelve properties execution reads (`symbol-class`,
`stobjs-in`, `stobjs-out`, `formals`, `invariant-risk`, `absstobj-info`,
`stobj`, `stobj-function`, `attachment`, `predefined`, `constrainedp`,
`guard`), replaced the world by those triples and collected. Dynamic usage
went from 397.1 MiB to 299.4 MiB, 97.7 MiB (24.6%) freed. With every
property dropped it was 295.7 MiB. Any reference the strip missed keeps
objects alive, so 97.7 MiB is a lower bound. Taken off the 271.4 MiB core,
it projects a floor of about 174 MiB, near bare ACL2's 159.5. This is a
projection, not a measured image. The rest of the floor is ACL2's compiled
prover and SBCL, which a world strip does not remove. A floor below about
100 MiB needs an image that does not carry ACL2 at all, which is a different
host.

What a world-free image must still do, from §2:
- keep `symbol-class` (and the stobj properties) for the `*1*` dispatch;
- start without LP reading the full world. Startup reads 30 properties and
  runs one `ld`/`trans-eval` of the return-from-lp form. This is untested:
  an image that skipped LP would need its own entry;
- keep a guard failure inside `fnn-call` a fault, never a crash. An ACL2
  guard-error message formats through the world. This is also untested.

This is a change to how the image relates to ACL2's logical state, so it is
a decision (packet below), not a lane default.

## Assurance chain

No book, no host file and no image changed. The chain is the same as it was.
Native entry `bin/fn` leads to `fn-native-entry`, then `fnn-call` to the
`*1*` of the host wrapper, then (with `symbol-class` read from the world,
§2) the guard-verified raw subject, the refinement and behavioural theorems
of the certified closure, and the observed results above. The measurement
tools decide nothing a node does: they run in unsaved sessions or in a
probe-loaded copy of the core.

## Packets (for the deputy / ember)

1. **The world-free image (decision).** Trace: §1 to §4. Constraint:
   `*1*` dispatch reads `symbol-class`, and LP runs at start. Default: do not
   build it now; ship today's image with the heap figure heap-from-profile
   derives. Alternative: a build step that strips the world to the
   execution properties before `save-exec`, a raw entry that skips LP, and
   guard-failure behaviour re-qualified. Its cost is an image whose ACL2
   state is no longer ACL2's, with every `*1*` path re-qualified, for about
   98 MiB of floor (projected). The alternative of calling the raw
   functions directly (no `*1*`, so no world read) would move guard checking
   into the host, which AGENTS.md forbids. Affected: host/native/build.lisp,
   the native entry, heap-from-profile's CORE input. What continues without
   it: everything.
2. **The release manifest's book list.** The release already names its
   source revision (`fn --version`), and the qualification record ties that
   revision to a closure manifest (current-view.json `closure_manifest`).
   Writing ACL2's `include-book-alist` (421 books and their book-hash) beside
   the core at build time, then carrying it through the freeze, would make
   the link per-image. `packaging/freeze-native-image.sh` has open edits in
   lane/release-openbsd and lane/crypto-deps, so this belongs to whichever
   lane owns the freeze next. HST-017 is left for it.

## Commits

See LANEDUMP (the lane's commit hashes).
