# image-anatomy (2026-09-26): what is in the node's image, what a node touches, and what it takes to get smaller

Lane image-anatomy, branch `lane/image-anatomy` from dev 0d71113c0. An
investigation: no book, host file, build script or release image changed.
It adds the measurement and experimental-image tools under
`tools/image_anatomy/` and this record, with its data in
`planning/evidence/image-anatomy-2026-09-26/`. Every figure is from hbox
(SBCL 2.6.8, ACL2 8.7, toolchain `w28/acl2-literal-4g`). MiB throughout.

The base image was built by `tools/hbox_native.sh --label base --images
developer,production 0d71113c0 tests.test_native_operator_verbs` (tree
`/tank/fn/scratch/image-anatomy/native-base/`, `fn-host.core` sha256
8c65089dd21d..., 394,842,952 octets; operator_verbs OK, 22 ran). Every
experimental image is that core, started without ACL2, changed, and saved
again (`derive.sh`); none is a release, none was deployed.

## The answer (one page)

**Where the bytes are.** The production core holds 367.8 MiB of objects:
263.1 in the dynamic space (the 271.4 MiB "required" figure, including page
slack), 62.2 in read-only space and 42.5 in the code and symbol spaces.

| Owner | MiB | Touched by a node after 1,000 POSTs |
| --- | --- | --- |
| The logical world (fn books 71.6, ACL2's ground zero 67.8, community books 3.5, host wrappers 2.3) and its installed index on symbols (7.9) | 153.0 | 3.9 |
| Build residue: 85,001 symbols of ACL2 input channels, one per file ACL2 opened while building (34.3), ACL2's xdoc text `*acl2-system-documentation*` (33.2), the hons space (15.7), the memoize call array (8.0) | 91 | 4.0 (the channel symbols, touched at every start) |
| ACL2's compiled system (37.1) and ACL2's own `*1*` functions compiled at build with their source forms kept (39.8 of "code:none-*1*") | 77 | 8.4 |
| SBCL (code 24.0, symbols 6.4) | 30.4 | 20.6 |
| fn's compiled books (raw 5.8, `*1*` 5.0) and the native host (3.7) | 14.5 | 6.4 |

fn's own compiled code is 14.5 MiB; the 403 book `.fasl` files are 7.5 MB on
disk. The floor is ACL2's logical state and build residue, not fn's code.

**What a node truly needs.** A node touches 50.7 MiB of the core by the time
it listens and 62.3 MiB after 1,000 POSTs, 98% of it clean pages of the core
file (shareable, reclaimable). It reads the world for exactly **63 (symbol,
property) pairs** across the four qualifying modules and a provoked guard
violation: 48 `symbol-class` lookups of logic-mode host wrappers (the `*1*`
dispatch) and 15 reads when LP translates the `:return-from-lp` form. Of the
175.6 MiB resident after 1,000 posts, about 100 MiB is new heap outside the
core, which is garbage-collector policy (lane image-floor), not the image.

**Three ways to get smaller, measured** (each image passed operator_verbs 22,
hybrid_author 11, starttls 2, implicit_tls 3, and reports a provoked guard
violation as the same fault):

| Step (cumulative) | Core required | Core file | RSS start / after 1,000 | Assurance cost |
| --- | --- | --- | --- | --- |
| production image | 271.4 | 394.8 MB | 67.8 / 175.6 | |
| re-saved once, nothing changed | 271.3 | 394.8 MB | 44.9 / (121.6 after 300, base 156.2) | none: same objects, new layout |
| tree-shake functions (13,964 of 32,263 removed, and all 2,161 macros) | 247.1 | 344.2 MB | | removed code the static closure says is unreachable; residual: a computed call to a removed function becomes an undefined-function fault |
| + world reduced to the 63 pairs and the execution properties of kept functions (449,215 triples to 55,880) | 134.4 | 224.3 MB | 45.6 / 145.0 | guard messages still name the guard; anything that asks the world something new gets the default |
| + build residue dropped (channels, defconst discriminators, xdoc, hons space) | 74.3 | 132.5 MB | 65.3 / 167.4 (see the hons note) | none for the node |
| + raw entry without LP/ld (`entry.lisp`) | 71.7 | 127.6 MB | 62.1 / 164.0 | the node runs outside ACL2's read-eval-print loop: an unwind-protect frame, `*ld-level*` 1 and the local-top-level catch are provided by 12 raw lines |
| direct calls (fnn-call applies raw functions, no `*1*`) | unchanged | | unchanged (46.7 / 125.2 after 300, it is also a re-save) | loses every guard check at the boundary; time gain within noise |

The hons note: dropping the saved hons space (15.7 MiB) makes ACL2 build a
fresh default one at every start, which costs about 17 MiB of resident
memory; shake2's 45.6 MiB start is the better figure. The right move is a
small hons space kept in the image (`hons-resize-fn` failed in my attempt).

**Misconceptions in "export the definitions into plain SBCL".**
1. *The bytes are fn's code.* No: fn's compiled code is 14.5 MiB of 367.8.
   An export keeps SBCL (30 MiB) and removes what a world strip and a residue
   drop remove anyway.
2. *The compiled books cannot run without ACL2.* Only partly: 395 of 400 fn
   book fasls load into a bare SBCL with ACL2's 64 package names, six no-op
   stand-ins for include-book's compiled-file protocol and four list
   functions. They then call 189 undefined names: about 60 `*1*` primitives
   (`car`, `binary-+`, ...), about 45 fn functions of the 5 stobj books that
   failed to load (stobj creation at load time), and about 70 ACL2 runtime
   functions: list utilities (`take`, `true-listp`, `string-append`),
   `*1*` dispatch (`w`, `symbol-class`), stobj support
   (`with-inside-absstobj-update`, `replace-live-stobjs-in-list`,
   `chk-make-array$`) and the error path (`hard-error`, `illegal`, `fms`,
   `wormhole-er`, `throw-raw-ev-fncall`, `interface-er`). A shim is a few
   hundred lines plus a stobj runtime plus a replacement error printer, not a
   reimplementation. But it replaces ACL2's executable semantics (guard
   checking, attachments, stobj invariants) with raw Lisp: exactly the
   assurance the node now gets from running inside ACL2.
3. *The image is 271 MiB of memory.* On Linux it is 271 MiB of address
   space; 50 to 62 MiB of it is ever resident, mostly clean file pages.
4. *The prover is loaded, so it costs memory.* It costs reservation and
   file size, not residency: 5.9 of ACL2's 37.1 MiB of code is ever touched.
5. *Static tree-shaking can remove ACL2.* It cannot on its own: every ACL2
   function statically reaches the whole system through the error path
   (`guard-raw -> untranslate1 -> fmt-to-comment-window! -> wormhole ->
   set-w -> initialize-acl2 -> ld-fn -> ... -> prove`) and through `apply$`
   (`do$ -> apply$-lambda -> cl-cache -> tau -> type-set -> rewrite`). The
   closure kept 17,434 to 18,299 functions (about 4,900 of them ACL2's)
   whatever the roots.

**Recommended path to "tens of MB"** (estimates in lane-days):
1. *Image-floor's world strip, with this record's list* (the 63 pairs plus
   the 12 execution properties of kept functions; value stacks cut to the
   current value), *plus the residue drop* (channel symbols, defconst
   discriminators, xdoc, a small hons space): measured core requirement
   about 134 to 76 MiB (from 271). 1 to 2 lane-days on top of image-floor.
2. *Re-save the built image once* (start the saved core without ACL2, save
   again): measured start RSS 67.8 to 44.9 MiB and after 300 posts 156.2 to
   121.6 MiB, at no assurance cost. Half a day, plus finding why the first
   save lays the core out worse (below).
3. *Size the node's own reservation honestly*: `--dynamic-space-size` from
   the profile (image-floor), and a control stack sized by measurement, not
   ACL2's 64 MiB per thread. 1 lane-day with a deep-recursion witness.
4. *Tree-shaking of functions*: worth 24 MiB of dynamic space and 14 MiB of
   code, but only with cut points in ACL2's error printer and `apply$`,
   which are raw-Lisp obligations. Defer.
5. *Direct calls*: do not. See §4.

With 1 to 3 a node needs a core of about 75 MiB and a heap sized by its
profile; it is resident at about 45 MiB when it starts. "Tens of MB" of
reservation needs the remaining 72 MiB of shaken core to shrink further
(debug info, the memoize array, ACL2's remaining tables: an estimated 20 to
30 MiB), which is a second step after 1 to 3, about 2 lane-days, and should
be measured before it is promised.

## 1. What is in the image

`ia-anatomy.lisp` runs inside the production core before ACL2 starts
(`anatomy.sh`). It gives every allocated object one owner, walking roots in
order: every world triple oldest first (so an object is charged to the event
that introduced it; origin from `boot-strap-flg` and `include-book-path`),
then ACL2's property index on symbols, then every code component with its
debug info and non-symbol constants (owner from its source file), then every
symbol by package. It joins every object with residency snapshots
(`ia_node.py`, from `/proc/PID/pagemap`: present, and clean file page versus
private page). Data: `anatomy-base.log` (sha256 04a32536...),
`ia_report.py` prints the tables.

By space: dynamic 263.1 MiB (11,979,429 objects), read-only 62.2, immobile
(code 41.0, symbols and fdefns) 42.5. By type: conses 175.7 MiB, strings
71.5, code 41.0, simple vectors 17.8, symbols 10.3.

The world by property: GLOBAL-VALUE 42.5 MiB (event landmarks: whole event
forms), CONST 35.6 (defconst values, xdoc text among them), POS-IMPLICANTS
15.8 (tau), LEMMAS 14.2, UNNORMALIZED-BODY 8.6, TYPE-PRESCRIPTIONS 3.2,
UNTRANSLATED-THEOREM 3.1, RUNIC-MAPPING-PAIRS 2.6, THEOREM 2.0. Touched
after 1,000 posts: 2.1 MiB of the world's 145.1.

ACL2's code by source file: other-events 6.7 MiB, axioms 5.6, translate
3.1, history-management 2.8, rewrite 2.4, defthm 1.9, ... The 39.8 MiB of
"code:none-*1*" is 7,351 `*1*` functions of ACL2 system functions (e.g.
`translate11`'s is 379 KB) compiled with `compile` at ACL2's build; SBCL
keeps each one's source form in its debug info.

The touched set by owner after 1,000 posts (MiB): SBCL code 15.2, ACL2
symbols 6.5, ACL2 code 5.9, SBCL symbols 5.4, channel symbols 4.0, fn book
code 2.9 + 2.3 (`*1*`), ACL2 `*1*` code 2.5, world 2.1, property index 1.8,
host code 1.2.

## 2. What touches 68 MiB at start

Residency by stage (`ia_node.py stage` and `run`, production image, 1 GB
dynamic space; `base-pages-run.json`):

| Stage | RSS | Core pages touched |
| --- | --- | --- |
| SBCL started on the core, `(sleep 30)` instead of ACL2 | 30.4 MiB | 22.4 |
| + `acl2-default-restart` | 35.5 | 27.1 |
| listening (LP, `ld` of the return-from-lp form, config, store open) | 67.8 | 50.7 |
| after 1 POST | 73.6 | 54.0 |
| after 1,000 POSTs | 175.6 | 62.3 |

Before any ACL2 code runs, SBCL touches every symbol object (224,030
symbols, 10.3 MiB; the 85,001 channel symbols among them) and 7 MiB of code.
ACL2's restart adds 5 MiB. LP and the node's start add 24 MiB: SBCL code
(3.9), ACL2 code (1.9), host and book code (4.0), symbols, 2 MiB of world
reads, and 8 MiB of conses and strings touched for the first time.
Private memory at start is small: 0.9 MiB of written core pages, 5.1 MiB
of new heap, 4 MiB of GC tables.

A node can start touching much less: the unchanged image re-saved once
starts at 44.9 MiB (dynamic core pages touched 26.4 to 13.8 MiB, code 16.6
to 8.3, read-only 6.1 to 1.4). The re-save is SBCL's own save from a process
that never ran ACL2; ACL2's save-exec saves from the build session. Why the
first layout is worse is not established (a guess: save-exec's final
collection runs from the build session's roots and places objects in that
order); it is an open item, not a claim.

## 3. Tree-shaking

`shake.lisp` (with `derive.sh`): roots are every ACL2 function (raw and
`*1*`) whose name is a token of the host's code (comments and strings
removed; 7,788 tokens, 6,074 functions), ACL2's restart, `fn-native-entry`,
and every function a special variable of any package names or holds (118).
Callees come from `sb-introspect:find-function-callees`: SBCL 2.6 calls
through linkage cells, so code constants are empty and a constant-based
closure finds nothing. Then `fmakunbound` of everything else in ACL2's and
the community books' packages, the world reduction, and the residue drop.
A saved core's objects are pseudo-static: `(sb-ext:gc :full t)` frees none
of them (dynamic usage rose from 277.5 to 283.3 MB during the shake); only
the final collection of `save-lisp-and-die` does.

Results: table in the one-page answer; images and their sha256 in
`cores.sha256`, sizes in `core-sizes.txt`, module verdicts in `modules.txt`
(log sha256s in `module-logs.sha256`). What broke along the way: the
shaker removed its own functions (fixed by excluding `IA-`); nothing broke in
the node. What it took to keep it working: the 63 recorded pairs, the
execution properties of kept functions, and (for the raw entry) the part of
`ld-fn` the node's dynamic extent relies on.

The guard violation (`guard-probe.lisp`, run inside LP or the raw entry,
through `fnn-call`): `(fn-cp-nth "not-a-natural" '(1 2))` gives
`FNN-STORE-FAULT: ACL2 error in fn-cp-nth: (EV-FNCALL-GUARD-ER FN-CP-NTH
(not-a-natural (1 2)) (NATP N) (NIL NIL) NIL)` on the production image and
on every shaken image alike.

## 4. The `*1*` question

The host's wrappers (the 920 functions the ld'ed `host/*.lisp` files define,
`wrappers.lisp`): 719 `:program` (375 declare a guard, 344 have guard `t`),
199 `:ideal` (logic mode, not guard-verified), 2 guard-verified. So the
`*1*` boundary checks (a) the declared guards of 375 program-mode wrappers,
(b) for the 199 `:ideal` wrappers, the guard of each callee until the first
guard-verified one (the `symbol-class` read decides this: 9 world reads per
POST, none per ARTICLE, per lane runtime-image). The other 344 program-mode
wrappers check nothing: `(fn-store-txn-name "not-a-sequence")` returns
`("")` with no fault on every image. Which host inputs can violate a guard:
only values the host passes unvalidated into (a) or (b); the host validates
octets before calling, so a violation at the boundary is a host bug, and
today it surfaces as a fault instead of undefined raw behaviour.

Direct calls (`direct.lisp`): POST time for 300 posts was 97.5 and 111.1 s
on the production image, 63.2 and 101.8 s direct, 92.7 s on the re-saved
image: fsync dominates and the difference is within the noise. The memory
difference in the direct image is the re-save, not the direct calls. The
cost is every check in (a) and (b), which AGENTS.md forbids moving to the
host. The world reads the `*1*` path needs are 48 pairs; keeping them costs
nothing.

## 5. The export claim, and ACL2's own facilities

`bare-load.lisp` (data `bare-load-summary.txt`): see misconception 2. A
book's compiled file is not a standalone program: it is written for
include-book's "hash table support for compilation" (it calls `hcomp-init`
and `include-book-raw`, and defines functions that include-book then
installs), refers to `ACL2_INVISIBLE::|The Live State Itself|`, and needs
community books' packages (`U`, `STD`, ...) defined.

ACL2 8.7's documented facilities: `save-exec` (`:return-from-lp`,
`:init-forms`, `:host-lisp-args`, `:toplevel-args`, `:inert-args`) saves the
whole session and has no tree-shaking; there is no "ACL2 as a library"
mode. `tools/include-raw` loads raw Lisp into a book (the opposite
direction). Kestrel's ATC (`books/kestrel/c/atc`) generates C from ACL2
functions written in its shallowly embedded C subset, and ATJ
(`kestrel/java/atj`) generates Java; neither applies to fn's books without
rewriting them in those subsets, with ATC's proofs as the payoff. SBCL
itself has no supported tree shaker; `:purify` does nothing on its
generational collector; core compression shrinks the file, not the memory
(and on a system that decompresses into anonymous memory it would make
every page private).

## 6. The OS side

Measured on Linux (`timing-*.json`, `pages-shake4-run.json`): 6 threads at
start, 7 after posts; VSZ 1.7 to 2.0 GB with a 1 GB dynamic space. Each
thread maps a 64 MiB control stack (ACL2's `--control-stack-size 64`) plus
1.5 MiB; the image script's default dynamic space is 32,000 MB; the GC
tables are 5 to 9 MiB. On Linux all of that is address space: "under 256 MB"
can only mean resident (RSS, or PSS when several nodes share the core's
clean pages) and the dynamic-space size as a ceiling.

On OpenBSD (no overcommit; not run by this lane) anonymous mappings count
against the datasize limit and are backed when mapped, so "under 256 MB
reserved" must count: the dynamic space, every thread's control, binding
and alien stacks, the GC tables and the C heap, and, if SBCL there reads the
core into anonymous memory rather than mapping the file, the core's spaces
too. The node should size itself: dynamic space = core requirement + the
profile's working heap (image-floor's heap-from-profile), control stacks
sized by measurement (a deep-recursion witness at the largest supported
article) rather than 64 MiB, and a start-time check that the sum is below
`getrlimit(RLIMIT_DATA)` that refuses with the numbers. Whether OpenBSD's
SBCL maps the core file or copies it decides whether the 132 MB core of a
shaken image counts; `procmap` on the friend's VM answers that in a minute.

## Assurance chain

Unchanged: no book, host file or build script changed. For the experiments:
native entry `bin/fn` -> `fn-native-entry` (LP's `ld`, or the raw entry in
shake4) -> `fnn-call` -> the `*1*` of the host wrapper -> `symbol-class`
from the (reduced) world -> the guard-verified raw subject. The shaken
images keep every function the static closure reaches from the host's code;
a function reached only by a computed name outside that closure would now be
an undefined-function fault (fnn-call reports it as a fault). No image here
is qualified for anything; the modules are evidence that the experiment is
viable, not that such an image is correct.

## Packets (for the deputy / ember)

1. **Re-save after build (decision).** Trace: §2. Default: take it in the
   build (`save-exec`, then start the core without ACL2 and save again),
   qualified like any image change. Alternative: leave it; cost 23 MiB of
   start RSS and 35 MiB after 300 posts. Affected: tools/build_native_host.sh,
   the freeze. Open: why the first layout is worse.
2. **The world strip's contents (for image-floor).** The 63 pairs
   (`props-all.txt`), the 12 execution properties of kept functions, value
   stacks cut to the current value, plus the residue (channel symbols,
   defconst discriminators, xdoc, a small hons space). A strip that drops
   the world but keeps the defconst discriminators keeps 33 MiB of xdoc.
3. **Control stack size (decision, with image-floor).** 64 MiB per thread is
   ACL2's prover setting; the node's need is unmeasured.
4. **Tree-shaking and direct calls: not now** (§3, §4).

## Tools (tools/image_anatomy/)

`ia_node.py` (residency snapshots of a running node), `ia-anatomy.lisp` +
`anatomy.sh` + `ia_report.py` (owners, types, touched set), `derive.sh`
(experimental image from a built one), `props-probe.lisp` (recording image:
every world pair read), `shake.lisp`, `why.lisp` (the chain that keeps a
function), `entry.lisp` (raw entry), `cut.lisp` (error-path cut, closure
unchanged: 20,060), `direct.lisp`, `guard-probe.lisp` + `guard.sh`,
`bare-load.lisp`, `wrappers.lisp`. All are measurements or experiments; none
is loaded by a release build.
