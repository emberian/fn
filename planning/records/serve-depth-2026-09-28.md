# Serve depth (PKT-877 and the class behind it; lane serve-depth, 2026-09-28)

Every node thread runs on the control stack the installed launcher passes
(books/heap-reservation.lisp fn-heap-stack-kib, 1,024 KiB), and since lane
open-depth so does every native test.  A function that calls itself outside
tail position costs one frame per step.  open-depth made the open path loop
(PRF-352); with a 100,000-article store open, the served reads still died.

## 1. Before: 26 commands kill the owner (native-sd1)

hbox native-sd1 (762f6a051, production image, the launcher's 1,024 KiB),
tests.test_native_open_depth extended to serve every command of defprotocol's
table against the open syn100k-2k store (100,000 articles in fn.test), and to
reopen the owner after a death so one run names every command that kills it
(log: serve-depth-2026-09-28/native-sd1-before.log).  Full-replay open 23.1 s.
The owner died on: LIST, LIST ACTIVE (3 forms), NEWGROUPS, LISTGROUP (3 forms),
OVER (2) / XOVER, HDR Subject / Message-ID / :bytes / :lines / Xref /
:fn-verified, XHDR, XPAT (2), NEWNEWS (2), NEXT, LAST, and LISTGROUP after the
POST: 26.  The frames named were fn-nntp-group-low, fn-nntp-group-next-number
and, for the fatal (pseudo-atomic) deaths, only "fn-owner-chunk-span: Control
stack exhausted".  Answered: CAPABILITIES, HELP, MODE READER, DATE, GROUP,
LIST NEWSGROUPS / COUNTS / ACTIVE.TIMES / OVERVIEW.FMT / HEADERS / SUBSCRIPTIONS
/ MOTD / DISTRIB.PATS / DISTRIBUTIONS, STAT, ARTICLE / HEAD / BODY / STAT by
number and Message-ID, OVER and HDR of one Message-ID, AUTHINFO, STARTTLS,
CHECK, IHAVE, TAKETHIS, POST (240), an unknown command, QUIT.

## 2. All of them in one pass: tools/depth_check.py

The host-called closure is every ACL2 function a raw host file names (1,200
roots, host/native/*.lisp: ledger.raw_host_paths) and everything they EXECUTE:
a function's body with each mbe resolved to :exec, a macro's mentions, an
abstract stobj export's :exec (the attach-stobj implementation's, for the
arena), a constrained function's attachment, and the defuns a backquoted
macro writes (books/article-header-census.lisp).  9,326 functions.  A
non-tail recursion is a call to a member of the function's SCC outside tail
position.  Ground truth: lane extract-2's frontend over the image's world
(host/native/build.lisp up to its trust tag; `depth_check.py --driver`),
nontail_recursions.py over its JSON: 604 fn functions at the lane's base, and
the source-level lint found the same 604 (`--compare`: both 604, none apart).

The 604 were classified (debt: depth an article count, a group's articles, a
history, a queue or octets; bounded: something else, named).  After the lane
and two origin/dev merges (format 10, batch AZ's health-truth-status) the same
comparison at the lane's head: 383 and 383, all shared (the extractor over the
native-sd4 tree's world, 9,814 functions).

## 3. The loops (PRF-362)

Every twin is (mbe :logic <the recursion, unchanged> :exec <loop>), and its
guard proof is exec = logic on every input satisfying the guard, by one local
lemma with the per-element functions closed (ACL2's minimal theory, or
disabled): collecting walks <f>-loop-is-revappend ((revappend acc (f ...)),
early exits and :bad kept), right folds <f>-loop-of-rev-onto (the reversed list,
fn-ag-rev-onto, now in books/rev-onto.lisp so books without the acceptance
helpers can use it), sums <f>-loop-is-plus.  About 290 walks, most written by
two generators to those three shapes and admitted only by their proofs; the
rest by hand (the projection's min/max/next/last, the number sort's insertion,
the syntax conversions, the reply's pieces, the log's frame chunks, the posted
article's Path walk, the injection path scan, fn-bump-number, the export's
entries).  Withdrawn: the twins in BP books that verify guards lazily
(set-verify-guards-eagerness 0) -- their functions run their logic, so a
twin changes nothing there -- and walks returning multiple values or stobjs
(recovery's intern steps, one 1 MiB recovery chunk each).

Certified at the lane head 3aa98794f (after both merges): hbox
certify-20260928T081546Z-462652 (902 passed) + persvati
certify-20260928T081621Z-3853586 (869 passed), 0 failed, the 1,215 affected
roots.  Witnesses: tests/acl2/serve-depth-tests.lisp (a group of 50,000
articles: count, water marks, NEXT/LAST, the LISTGROUP numbers in order and
their lines; the index numbers and a non-descending sort of 50,001; LIST
ACTIVE, NEWSGROUPS and COUNTS over 50,000 groups; 100,000 characters and
octets; 50,000 reply pieces).

## 4. After: native

hbox, production image, the launcher's 1,024 KiB, format-10 fixtures
(hbox:/tank/fn/scratch/fixtures), tests.test_native_open_depth.

native-sd4 (3aa98794f + the module's commands): syn100k-2k full replay, then
every command of the table -- 70 exchanges, the whole-range reads each
100,000 lines: LISTGROUP 0.1-0.2 s, OVER/XOVER 1.8-2.0 s, HDR 0.3-0.9 s,
XPAT 0.7-1.1 s, NEWNEWS 0.9-1.0 s, LIST ACTIVE 0.2 s -- and every live control
report (status 1.8 s, health, pins, obligations 24,400,105 octets in 90 s,
peer list, account list, access show, consumer show, show), then the store
verbs with no owner (status, digest 36.5 s, journal, retention, compression,
config, export).  No owner death.  syn1m-2k: full replay 278.5 s, the same
commands, each whole-range read 1,000,000 lines (OVER 46 s, HDR 6-17 s, XPAT
14 s, NEWNEWS 10 s); no owner death; the store verbs (digest 426 s).
native-sd5 (fd28087e8, after the last origin/dev merge, XFNCATCHUP's 291
block read): syn100k-2k everything again, POST 240, export of 100,001 records
in 34 s; syn1m-2k: open 239 s, every command, POST 240 at 1,000,000; no death.

Not stack, recorded: at syn1m-2k `status', `obligations' and the reports
queued behind them answer uncertain after the control client's 10 s, and the
owner, still rendering them, took over 600 s to stop (sd5's stop timed out;
the module now waits an hour).  `store export' of 1,000,000 records exhausts
a 32 GB heap (fnn-bridge-record-sequence holds every record as an octet
list), so the module exports syn100k-2k only.

## 5. The lint

`make check` runs tools/depth_check.py (and its unit tests): a non-tail
recursion on the host-called closure that tools/depth_baseline.json does not
classify fails, and so does an entry that is no longer one ("the list only
shrinks").  It proved itself on the first merge: dev's new BLAKE3, format-9
import, genesis and export walks were refused until twinned or classified.
At the head: 383 non-tail recursions, 306 bounded (each names its bound: a
digest's 32 octets, a number's digits, a record's fields, a command line's
510 octets, one served step's 4,096 octets, BLAKE3's log2 chunk tree, the
operator's configuration tables) and 77 debt (BP queues in the lazily
guard-verified books, the recovery chunk's intern steps, the checkpoint's
batches, the store log's per-record unpacks, TCPCL items, the model reader's
chunk folds, base64 of carrier fields).  tools/hot_path_check.py measures a
different property (a traversal per request, time) and stays; depth is this
lint's.  Known gap: a function whose guards are not verified runs its :logic
(the *1* code), and the reader follows :exec everywhere; the extractor, which
resolves that, agreed at both heads.

## 6. Findings (not stack)

- HDR :fn-verified over a range is quadratic: books/nntp-verdict.lisp
  fn-nntp-verdict-hdr-lines looks each number up in the whole article list
  (fn-nntp-available-article).  1,000 numbers of syn100k-2k: 70 s; the whole
  100,000 ran over 30 minutes holding the owner (native-sd3, stopped).  The
  native module asks 1,000.
- `operator CONFIG obligations` at 100,000: 24,400,105 octets in 90 s.
