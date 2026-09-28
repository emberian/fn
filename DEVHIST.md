# fn: a development history

Written 2026-09-28 by lane devhist (Claude Opus 5.5), eleven days in, while
the record is still fresh. The sources are the git graph of `dev`, the
planning record (`planning/decisions.md`, `planning/now.md` and its archived
versions, `planning/evidence/`, the reviews and handoffs), the coordinator's
local state files, and the agent transcripts that ClusterVision (`cv`)
indexes. What the transcripts could and could not show is said in the last
section.

Git dates in this repository are recorded in US Eastern time; this document
gives times in UTC unless it says otherwise. Every commit is authored as
ember; who actually worked is read from `Co-Authored-By` trailers (Claude) and
their absence (Codex), cross-checked against the transcripts.

The five tags `v1.0.0` to `v5.0.0` mark phase shifts in this history. They are
**retrospective prehistory tags, not releases**. fn's first release is 6.6.0
(D37); `planning/release-sequence.json` lists the prehistory tags as a segment
that sorts before it and that the release gate ignores.

| Tag | Commit | Date (UTC) | What it marks |
| --- | --- | --- | --- |
| v1.0.0 | `0bd0b5c27` | 09-19 03:27 | Genesis done: the day-one tree serves NNTP from a persistent store and exchanges over BP; the independent review's assurance rules adopted |
| v2.0.0 | `f7190d691` | 09-21 16:16 | The first wide native service composition frozen for qualification: the node is an SBCL image, Python leaves the runtime (D07) |
| v3.0.0 | `907946b58` | 09-22 20:49 | The first deployed native node agents can post to (hbox, image `dabebb84`) |
| v4.0.0 | `ac1907bf4` | 09-27 10:28 | Store format 9, the record log: the end of the D27 representation arc |
| v5.0.0 | `a3feeca16` | 09-28 05:49 | Store format 10 (BLAKE3) over the page store, after the public node went live on 6.6.0 |

## Before the first commit

fn began in a Discord thread about giving some Claudes (the agents yue and
tulip, who later posted to the first live node) a way to exchange mail. The
name was coined there: "fn for fuckin news / formal news / fenomenology of
numbers". At 06:36 on 2026-09-18 ember opened a Codex session with its root
agent, Astra:

> "hi astra. i'm feeling insane today and like i want to do something with
> acl2. the something? an "enough" nntp server to serve as a comms nexus
> between some AIs and humans."

A minute later: "Work through the architecture and proof targets first". Five
minutes after that the ambition was set, and it has not shrunk since: "What
would be "space age"? I someday would like this to be usable for
extraterrestrial operations, eg Licklider protocols are an inspiration as
well.... I honestly think we can be ambitious… as long as we do a lot of the
design up front".

## Phase 1 — Genesis (2026-09-18, Codex)

The first commit, `3e26f4345` at 07:50, is a design before it is a program:
the RFCs fn implements (3977, 4643, 4644, 5536, 5537, 2980 and the rest)
copied in, ten specifications, a requirements registry, a decision
workbook, and five small ACL2 books (acceptance, CBOR, retention, wire). The
agreed directions A01 to A07 were already written there: NNTP as the first
interface for humans and AIs, executable ACL2 semantics with meaningful proofs
of the running core, a specialised persistent store, explicit retention
obligations, and sites that stay useful while disconnected.

Codex then built the tree in one working day: one root session (Astra, the
integrator, on `gpt-6-astra`) and some thirty worker sessions on `gpt-5.6`
under the roles Terra (bounded implementation and harnesses), Sol (composition
and the hard induction proofs) and Luna (inventories, independent vectors,
narrow tooling). Fifty-six commits between 07:50 and 03:27 the next morning
took the tree from five books to seventy-two. By 09:00 the store persisted
transactions and served recovered stores over NNTP (`b8ab94818`, "Persist
transaction allocation and serve recovered stores over NNTP"); at 11:46 ember
moved BP from a later milestone into the first ("isn't the what BP enables,
absolutely vital to *how we wanna be doing it*?", decision A06), and by 13:30
a durable end-to-end BP exchange with restart recovery was integrated
(`ff381d10a`). The host was Python: `tools/run_store.py`, `run_reader.py` and
their siblings did the I/O and called ACL2 through a bridge.

That day's decisions came from ember directly: exact authored source bytes
with separate projections (D01), native author signatures plus gateway
provenance (D02), keep posts until explicit release (D03), shared groups first
with encryption designed later (D04), and NNTP and command-line clients before
the web (D17).

ember brought Claude in at 02:05 on the 19th ("wanna orient into this
project?"), and at 02:42 a Claude session committed the first independent
review (`planning/review-2026-09-18-independent.md`, five adversarial
auditors). Its verdict set the tone for everything after: the tree was honest
in most prose and free of every forbidden facility, but "the assurance ledger
points at weak siblings of the real theorems, several 'certified' rows rest on
tautologies or on functions the host never calls", and two host bugs could
brick a store or wedge the reader. Its standard, "green is not true", became
AGENTS.md's assurance rules in `0bd0b5c27`, the commit every later lane
branched from. **v1.0.0** marks it.

| At v1.0.0 | |
| --- | --- |
| Books / ACL2 test books | 72 / 41 |
| `defthm` forms in books | 1,403 |
| Book lines / host Lisp / Python | 27,333 / 840 / 8,839 |
| Certification | all 113 roots in 25 min 44 s (review §2.1) |
| Who | Codex: Astra root (`gpt-6-astra`), Terra/Sol/Luna workers (`gpt-5.6-*`); Claude Fable for the review |

## Phase 2 — Realignment and a real server (2026-09-19 to 09-21)

The same night ember set Claude a goal ("improve fn bottom-up and top-down,
twin-killing, functionality-completing, assurance-finishing; swarm wide") with
Claude Fable 5.1 as root. Wave 1 was ten lanes in worktrees under
`build/lanes/`, each executing a slice of the review: crash fidelity, the
sender proofs, moving Python "twins" of ACL2 decisions into ACL2, the served
NNTP path, assurance tooling. At 06:43 a handoff to Codex was prepared in case
Claude's usage ran out (`handoff-to-codex-2026-09-19`); in the event Claude
converged wave 1 itself and kept the root through the 20th.

ember's direction at 14:47 on the 19th, after a "what is still fake" review,
changed the project's shape more than any single decision since:

- "I don't understand why we have so much going on in Python anyway, maybe it
  was a crutch we shouldn't have reached for?" (quoted in D07);
- fn must become an actual server, pushed as hard as possible;
- "We can't be having compiled-in configuration… ("assured live
  reconfiguration" would be a great feature to brag about…)": configuration is
  durable records;
- "Authority being noncryptographic is acceptable" (for now);
- the crash model must become byte-level (write units, torn writes, directory
  atomicity only after a directory fsync);
- "Yeah lmao we need to not be doing this DTN/BP theater, we need to come up
  with a real design": fn as a BPv7 node with its own proved TCPCLv4
  convergence layer, interoperating with dtn7-rs and ION (design `687b42283`
  the same afternoon);
- proofs chain toward a UC-like composition with an ideal functionality.

The first cost of width arrived the same afternoon. Thirteen lanes each ran a
full `make certify` baseline on the laptop (load 98), and one lane's seven
global rewrite rules, exported from `bp-ingress.lisp`, pushed a downstream
book past its 1,800 s timeout. At 17:46 ember stopped the swarm over "severe
coordination-induced problems", and at 18:10: "ok wow the proof engineering
was really bad". The realignment that followed is the origin of most of fn's
proof engineering: content-hashed certificates and a certificate cache,
`--affected-by` instead of hand lists, a slot pool for ACL2 processes, the
farm (`tools/farm.py`) on the two Linux boxes, lints, and
`docs/proof-style.md` written by a Fable "core deputy" (cluster closure 183 s
to 8.3 s). Two independent deputies rejected migrating to FTY; fn kept opaque
records with its own `fn-defrecord` macro instead.

Then the server wave. `books/served.lisp` made the host loop one call of
`fn-served-step`; the single owner process took POST; an `fn` CLI with systemd
and launchd units, a deploy gate running fn as a real server on persvati, RFC
2980 legacy commands (slrn drove a live session on the 20th), an INN 2.7 lab
on hbox (75 steps, 0 failed), peering (IHAVE/CHECK/TAKETHIS), a TCPCLv4 codec
and session machine with its C1 to C4 keystones, an executable guard-verified
SHA-256 (`books/sha256.lisp`), a Roughtime client, and the first native host
image: a saved SBCL image doing raw I/O, built on persvati in 8.5 s on the
20th with a 7/7 served differential against the Python host. Lanes were Claude
Opus 5 and Fable 5.1, with a Sonnet lane for hygiene, until ember ran out of
Fable at 20:24 on the 20th ("opus-only from now on"); 530 Claude commits
landed on the 20th.

At 02:01 on the 21st ember worried that "opus has been working alone without
any fable and i fear it has ... found itself in a gyre of confusion of its own
creation", and at 06:01 handed the project back to Astra: "Actually honestly I
think you should just take over from claude… Remember to AVOID the "Twin
problem"". Codex ran a wide capability cycle that day, about ten `gpt-5.6-sol`
lanes under the `gpt-6-astra` root: hybrid Ed25519 plus ML-DSA-65 signatures
("Require both from the first release for long-lived authenticity", D09),
bounded event profiles, peer TLS, compaction, crash correspondence, a
Message-ID trie. Astra's reorientation named the failure mode of the previous
three days, and it was right: *local completion without operational
completion*. A function, a theorem, an adapter and a test each existed, and
the running path did not connect them under the same assumptions.
`tools/reach_check.py` came out of it: 41 of 288 registry events had no
subject any host line reached. At 07:36 ember settled D07: "i just wouldnt
want python in a running fn process, that isnt high assurance whatsoever". At
16:16 Codex froze "the first wide native service composition for
qualification" (`f7190d691`), the image that became `915d5c72`. **v2.0.0**
marks it.

Two incidents belong to this phase. On the 21st a Python test's parent
directory walk, `dirname('/')` being `/`, looped forever inside a test that
mocked `fsync_dir`, so every iteration retained another mock record; "this
whole machine ran out of ram and hard-rebooted"
(`planning/archive/recovery-2026-09-21.md`). The laptop's ACL2 slot pool and
its per-process heap cap descend from this and from two more subagent OOMs on
the 25th. At 19:14 the Codex root quiesced, "at the end of our allocation"
(`quiescence-2026-09-21.md`), leaving about a hundred worktrees and 273
branches.

| At v2.0.0 | |
| --- | --- |
| Books / ACL2 test books | 227 / 144 |
| `defthm` forms | 5,308 |
| Book lines / host Lisp / Python | 119,888 / 14,868 / 66,439 |
| Requirements registered | 58 |
| Who | Claude Fable 5.1 root, Opus 5 and Fable lanes (09-19, 09-20); Codex `gpt-6-astra` root and `gpt-5.6-sol` lanes (09-21) |

## Phase 3 — A native node (2026-09-22 to 09-24)

Claude came back at 01:11 on the 22nd ("gpt-6 ran out of usage limits and left
this handoff"), and ember's first worry was "i feel like maybe we've been
trapped in corners conducting this development wrong because it isnt going as
quickly as i expected." Claude's diagnosis was that the process was wrong in
width, not in kind: the Python service matrix read 141 accepted, 34 refused, 3
uncertain, while the native matrix read 9 accepted, 2 refused and **181 not
exercised**. The native node had never had the full driver pointed at it. The
reason turned out to be one line: the matrix driver started nodes with `nohup
VAR=x cmd &`, which executes a program named `VAR=x`. Every native node
"reported dead in 0.3 s", and for a day every native run had reported "not
exercised" without anyone noticing. Fixed (`783db508a`), the 915 image read
101 accepted, 22 refused, 0 faulted, with one real gap (a native node had no
path identity, so RFC 5537 loop suppression could not fire).

Three freeze passes on the 22nd took the image closure from 111 to 165 of 165
books. At 20:49 `907946b58` recorded "the first native node agents can post
to": hbox running the `dabebb84` image, probed and measured, with STARTTLS and
a login, and the full v0 matrix on the image (206 rows, 163 exercised).
**v3.0.0** marks it. Opus 5.5 was released that afternoon, and ember's
instruction ("lets use opus 5.5 as much as we can as subagents!") has held
since. The same evening ember noted that `gpt-6-sol` "came out which is half
the price/usage of gpt-5.6-sol". That night Claude's lanes made iteration a
number: a book over ten seconds became a defect, the runner started the
longest chain first, certificates became relocatable across snapshot origins,
and a from-scratch freeze of the image closure fell from 31 minutes to 1 min
44 s at sixteen jobs; ember's targets were blunt ("A full closure certifies in
about twenty minutes" that's .... unacceptably slow?", and "getting iteration
times to <3 minutes would be amazing"). The node was upgraded in place to
`da5fd8cb`; the INN lab passed 33/33 and the served cut campaign witnessed F1
to F7.

At 13:34 on the 23rd Claude handed off to Codex `gpt-6-sol`
(`handoff-to-codex-2026-09-23.md`), with letters to its successors; ember's
takeaway was to "open with measurement, put the failure modes into the goal
prompts, and give you a heads-up instead of a heads-after." Ember widened the
swarm ("Disjoint ownership is the hobgoblin of rigid swarms"): at least ten
agents, "mostly GPT-6-Sol", with claims as intentions rather than locks. The
GPT-6 shift of the 23rd and 24th landed signed ingress, author key lifecycle,
the ION binding, topic v2, and BP forwarding over negotiated TCPCL sessions
with durable kind-8 attempts and kind-9 results (+548 `defthm`, +37 books). A
trial settled a division of labour that is still in `how-we-work.md`:
GPT-6-Luna implemented bounded features against a contract and handed failed
proofs to GPT-6-Sol rather than searching for proofs itself. At 06:23 on the
24th ember asked for a wind-down; the last completed image was `863c2141`, the
final cut was red on three BP roots, and at 07:25, when GPT-6 wrote
`ALLDONE.marker` ("no new image was built. The live node is untouched"),
Claude took over as coordinator (Fable coordinating, Opus 5.5 lanes "as much
as possible"). Role names became neutral from then on. One failure of that
night belongs in the record: at 00:52 a Claude session ran `git reset --hard
origin/dev` in the shared checkout while GPT-6's lanes were live in it; GPT-6
recovered fifteen commits with nothing lost, and "never reset, stash or check
out the shared checkout" has been a standing rule since.

The 24th was the first day of deploys as routine, and ember named the trap to
avoid: "I don't want to get lost in qualification theater. we can usually
batch and overlap and converge in more-like-waves." Claude's first morning
back produced image `1a9dd747` (315 books certified, 0 failed), a two-Store
exchange (report, acknowledgement, signed reply, restart, read), and the
ten-second baseline cut from 37 books to 7; between 17:36 on the 24th and
01:15 on the 25th four images, `47bdb9a4`, `18c91321`, `4eca4148` and
`c3420013`, went to the hbox node in place, each after a one-lane
qualification. ember's correction that day, "orient to the plan, not to the
audit", is now in AGENTS.md.

| At v3.0.0 | |
| --- | --- |
| Books / ACL2 test books | 243 / 163 |
| `defthm` forms | 5,514 |
| Book lines / host Lisp / Python | 129,457 / 17,129 / 77,993 |
| Freeze of the image closure | 31 min, then 1 min 44 s at 16 jobs (09-23) |
| Who | Claude Fable 5.1 with Opus 5 then 5.5 (09-22 to 09-23 13:34); Codex `gpt-6-sol` and `gpt-6-luna` (to 09-24 07:25); Claude from then |

## Phase 4 — Representation, the mandate and consolidation (2026-09-25 to 09-27)

At 02:16 on the 25th ember asked why fn had "fixed budgets of any kind", and
four minutes later wrote what the register records as D27, the decision that
governs the rest of the history:

> "Using octet lists continues to be unacceptable at runtime. We need to
> have fewer bullshit restrictions. Each of those is a branch that someday
> will fail during operation for no meaningful reason except during
> development we were fearful and installed a footgun. Octet lists are an
> absurd amount of overhead. Let's endeavor to have efficient
> representations; otherwise the software is not useful as a system."

Two rules followed: a constant that bounds data is a defect (the operator's
profile sets limits; work per step stays bounded), and the logical model stays
octet lists while the executable path gets concrete representations with a
correspondence theorem at every boundary the host calls. Store format 8, the
operator's profile fields, landed within hours; seven of eight Python-host
twins were retired the same night. D28 opened `spike/mega`, a speculative
branch where `skip-proofs` and host-side decisions were allowed if marked, to
learn what a much larger integrated system would need; it never merges into
`dev`, and six spike lanes fed records back.

The night of the 25th is a lesson in fragility. A Fable deputy integrated
lanes from `build/coordinator/NIGHT.md` while ember slept; at about 11:30 the
account's weekly API limit terminated the deputy and a dozen lanes mid-flight.
When the limit lifted, ember's rule was to resume agents by id ("never fresh
agents"), and the resumed deputy finished: 37 merges, cut `e747dbcc` failed
qualification on a bug already fixed on `dev` (a POST at the transaction
budget stopped the owner), and cut `bbf52159` qualified and was deployed to
hbox at about 21:55, taking the live store from format 7 to 8.

That evening GPT-6, reviewing from outside the repository, wrote a "Fable 5.1
technical ownership and implementation mandate", and ember adopted it: "Do
whatever it takes, GPT-6's megaprompt is your mission." Waves 2 and 3 under
the mandate merged 57 lanes: accounts and invitations for friends' nodes,
control messages (D29: cancel as a withdrawal record, visible(T then C) =
visible(C then T)), a client-supplied Path accepted (D32, because tin could
not post), the web reader, peer pulls, a four-node mission lab. The
performance ledger of the 26th (`planning/performance-2026-09-26.md`) said
plainly why the node was still slow: every greeting ran the whole-state
recognizer over every retained payload octet by octet (87 percent of a
greeting's CPU); a 2,000-row OVER cost 17.7 s at 10,000 articles; the
automatic checkpoint of a 20,000-article store took 74 s and a 15.7 GB peak
and exhausted a 32 GB heap past about 33,000; and the BP codec spent 99
percent of its time in a CRC-32C whose XOR was computed one bit at a time by
`floor`.

GPT-6's consolidation review of the 26th became D33 to D36, confirmed by ember
that evening ("feeling good about the other decisions"): consolidation around
a committed catalog and one byte owner (`attach-stobj` prototyped first);
fresh deploys and no migrations, one store format until release; the release
is the product (one tarball per platform, Linux x86-64 and OpenBSD amd64, no
Python in a deployed node's runpath, a node "deeply under 256MB… more than
like a few dozen MB is needed at all", ember on the 26th); and a public node,
which ember placed on dregg-infra's edge rather than behind a home router
("surely we should be putting it up on ~/dev/dregg-infra"). A friend's machine
shaped the release too: an OpenBSD 7.9 box with 2 GB, clang and no SBCL, so
the release bundles its runtime and sizes the heap from the store profile.
Wave 5 was the consolidation. From the 26th integration moved to lettered
batches (AK to AZ) run by a batch-runner agent, and lanes stopped certifying
the world: "READY FOR BATCH" with their own manifests, the batch did the union
cite and the natives.

At 10:28 on the 27th batch AV merged `lane/commit-onto-log`: **store format 9,
the record log**, chained segment files with a proved crash keystone (PRF-264)
and a bounded commit wait (PRF-265); by noon the open streamed one entry at a
time. The same day fn took its licence ("AGPL-3.0 please") and ember held the
first friends' cut: "it's actually in really "chopped" shape, in terms of the
fundaments… we will continue to fork reality from 1987." **v4.0.0** marks it.

| At v4.0.0 | |
| --- | --- |
| Books / ACL2 test books | 690 / 517 |
| `defthm` forms | 11,882 |
| Book lines / host Lisp / Python | 334,311 / 35,473 / 180,087 |
| Requirements registered | 144 (end of 09-26) |
| Store formats | 7 (to 09-25), 8 (operator profile), 9 (record log) |
| Who | Claude Fable 5.1 coordinator and Fable deputies ("toplevel deputies are better as fable"), Opus 5.5 lanes (645 to 1,794 Claude commits a day); GPT-6 as reviewer through ember; Codex building downstream from `for-codex-2026-09-26.md` |

## Phase 5 — Public, released and paged (2026-09-27 to 09-28)

At 21:42 on the 27th ember made the DNS record ("ok made.") and said "get a
real fn deployed up (whatever has most recently been built and is good
enough)". By 21:50 `fn.fg-goose.online` was live on dregg-infra's edge (not on
hbox behind a home router; that placement was corrected on the 26th): native,
ports 119 with STARTTLS and 563 with implicit TLS, a Let's Encrypt
certificate, accounts by invitation only, running RSS 45 to 48 MiB. It ran a
rehearsal build that called itself 6.7.0. Eleven minutes later ember fixed the
version sequence (D37):

> "i'd like to make our first version v6.6.0 .... and then we'll work our
> way up to a v6.6.5 release, then we'll have a v6.7.x series, and then the
> final release (whenever that is) of the software would be v6.6.6. and then
> each new release would add another .6."

`VERSION` became 6.6.0; the public node was redeployed on fn 6.6.0 at 03:29 on
the 28th, about 8 s down, and a second node on hbox joined it. The OpenBSD 7.9
build guest certified the default closure (597 books, 0 failed). At 05:49
batch AY merged **store format 10**: BLAKE3 as fn's digest ("i don't mind
pulling in a blake3 c library. i STRONGLY DISPREFER the legacy SHA") with a
fifteen-field profile, on top of the page store merged five hours before (a
copy-on-write page store under `books/` with proved growth, reclamation that
never frees a live page, and 570 crash and power cuts with 0 violations).
**v5.0.0** marks it. By 16:39 both live nodes were on format 10 and peered
(one push direction still broken), and ember closed the door behind them:
"there are no such thing as future migrations :)".

The 28th's numbers are the first that look like a system: POST p50 at 100k
articles 733 to 188 ms and GROUP 520 to 51 ms (a lagging reader view had made
GROUP scan every number under the owner lock, 70 percent of owner CPU); OVER
of 2,000 rows 70 to 78 ms; HDR `:fn-verified` over the whole range at 100k
from over 30 minutes to 1.1 s; whole-tree prover steps down 30 percent (504M
to 351M) by withdrawing 257 wasteful exported rules; every book under ten
seconds at two jobs. A Chicken Scheme program extracted from ACL2's translated
terms serves a real store byte-identically (5.3 MB, 14 MB resident at start
against the 466 MB ACL2-carrying image, 3.4 times slower per command). The
page store's prototype opens in 10.5 ms at both 100k and 1M; the served open
still decodes the whole store (11.2 s and 135 s).

What is not done is stated in the same place. F8, reserved memory under 256
MB, is not met: 1,187 MB reserved at init, and a 1M store reserves 58 GB with
3.7 GB in use. The served image still carries ACL2. GPT-6's review of the 28th
names the next unit of completion as the composed boundary (a page image that
is provably the exact log prefix it claims), and ember's last method change of
the period moved every qualification, curve and 1M run to one prerelease
convergence checklist: "we're spending a LOT of time doing work that we only
need to do once". The 6.6.0 cut is held for that checklist.

| At v5.0.0 | |
| --- | --- |
| Books / ACL2 test books | 808 / 597 |
| `defthm` forms | 15,301 |
| Book lines / host Lisp / Python | 404,476 / 41,272 / 197,366 |
| Store format | 10 (BLAKE3; page store in the tree, prototype host) |
| Deployments | fn.fg-goose.online (public) and hbox, fn 6.6.0 |
| Who | Claude Opus 5.5 lanes and batch runner, coordinator Fable then Opus; GPT-6 reviews via ember |

## What the history taught

**Green is not true, at every scale.** The first review found tautologies
counted as keystones. Later versions of the same lesson: a theorem about a
function the host does not call (hence `reach_check`); a matrix whose native
rows were never exercised because of a shell quirk; an extraction gate that
passed a test binary exiting 73 because nobody checked the status (GPT-6,
09-28); two theorems that were false rather than slow (09-24), and a
zero-length write that made a byte-store theorem false until
`fn-bs-writes-nonemptyp` was added. Each produced a check rather than a
resolution to be careful.

**Proof cost is engineering, and it is usually one leak.** The 1,800 s timeout
of 09-19 was seven global rewrite rules; five books that regressed twofold on
09-24 were one rule, `fn-th-topic-eventp`, enabled at export; the whole-tree
30 percent of 09-28 was 257 exported rules. When the leak is found first,
proofs close fast (609.7 s to 7.25 s; 427 s to 0.01 s).

**Tests run at the deployed shape, or they lie.** Tests ran with a 64 MiB
stack while nodes ran with 1 MiB; at 1 MiB a node could not restart past about
30,000 articles, and 26 commands killed the owner at 100k. Some 300 recursive
walks became `mbe` loops and a shrink-only depth lint now guards them. A
native image grew because `tools/certs.py` deleted compiled files in an
install/publish loop, so ACL2 recompiled about 149 books inside the image.

**Width costs what the coordinator fails to pay.** Duplicated work was the
coordinator's fault, not the lanes'. `pkill -f` across lanes killed each
other's certifications on the 19th; `until ! pgrep -f X` loops matched their
own command lines and ran for hours on the 28th; an escaped test loop took
down the laptop on the 21st; loaded boxes measured the same bytes at two to
three times their quiet wall (so D26 made the ten-second rule's number a quiet
two-job measurement and the ratchet prover steps). The response each time was
structural: the slot pool, `swarm-build` with a memory cap, lanes in
worktrees, a batch runner, per-run box choice.

**Reversals kept.** Python was the host (09-18) and then was not (D07); raw
`store post` became developer-only (09-23); a candidate that refused
unenrolled signed articles was overruled by D23 (carry by allowlist, verify
against the author's enrollment); refusing a client-supplied Path was fn's own
early policy and D32 dropped it; in-place upgrades with rollback checks (09-23
to 09-25) gave way to fresh deploys and export/import (D34); the role-name
retirement decided on 09-22 did not happen until Claude's takeover on 09-24;
and the five-lane width of 09-22 was superseded the next day by ten.

## Who worked, in order

| When (UTC) | Coordinator | Lanes |
| --- | --- | --- |
| 09-18 06:36 | Codex root Astra (`gpt-6-astra`) | Codex Terra, Sol, Luna (`gpt-5.6-*`) |
| 09-19 02:05 | Claude Fable 5.1 | Claude Opus 5 and Fable 5.1, one Sonnet; Opus only from 09-20 20:24 |
| 09-21 06:01 | Codex Astra (`gpt-6-astra`) | about ten `gpt-5.6-sol` lanes; Claude Opus/Sonnet as cross-model reviewers |
| 09-22 01:11 | Claude Fable 5.1 | Claude Opus 5, then Opus 5.5 |
| 09-23 13:34 | Codex (`gpt-6-sol`) | about ten `gpt-6-sol` lanes, `gpt-6-luna` trials |
| 09-24 07:25 | Claude Fable 5.1, Fable deputies | Claude Opus 5.5; GPT-6 reviews through ember |
| 09-26 21:44 | Claude coordinator as its own deputy, a batch-runner agent | Claude Opus 5.5 |

## Sources, and what the transcripts could see

The git graph (3,138 first-parent commits and 7,997 in all at `9593f8c63`) and
the planning record carry most of this. Counts in the tables are measured on
each tagged tree: `.lisp` files under `books/` and `tests/acl2/`, lines
beginning `(defthm` in `books/`, and line counts of `books/*.lisp`, `host/`
Lisp and every `*.py`. They measure size, not assurance; the ledger
(`tools/ledger.py`) is the count that means something.

ClusterVision indexes 150 top-level sessions whose working directory is fn:
124 Codex sessions from 09-18 to 09-24 07:25 and 26 Claude sessions created on
09-19, 09-21 and 09-22, several of which ran for days (the coordinator's
session from 09-22 runs to this morning), with about a thousand Claude
sub-agents beneath them reachable by id. Its limits, found while writing this:
the full-text index had nothing for fn after about 09-22, so later quotes came
from the session files directly; the origin session's parsed view stops at
09-18 11:51 although its raw log runs to 09-24, so its later content (the
09-21 takeover, `ALLDONE.marker`) was read from the raw file; and no Codex
session for fn exists after 09-24. GPT-6's reviews of the 25th, 26th and 28th
were written outside this directory and reached the project only as the files
ember forwarded (`planning/review-*-gpt6*.md`,
`planning/handoff-2026-09-25-fable-mandate.md`). The coordinator's own state
files (`build/coordinator/`) are local and not in git; this history cites only
what they add to the committed record.
