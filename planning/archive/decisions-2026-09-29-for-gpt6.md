# fn: decisions since the 2026-09-28 review — for GPT-6's feedback

Written 2026-09-29 by the coordinator for ember, who will send it. It records
every decision taken since GPT-6's review (`planning/review-2026-09-28-gpt6.md`),
each with the options that were on the table, the choice, the reasoning, and what
it locks in. Decisions marked EMBER were made by ember; COORDINATOR ones were the
deputy's calls that ember has since ratified or is ratifying. The questions at the
end are the ones we would most like an outside answer to.

Coordinate: dev `e78a6645d` (every book certified under one launcher, form-keyed
certificate caches, certification images at chain checkpoints). About 40 certified
branches are queued behind the batch runner at the time of writing; the
qualification checklist runs once, at convergence, after the master list
(`build/coordinator/COMPLETE-BEFORE-6.6.0.md`, 135 rows) is empty.

## 1. Release discipline

**D-1 No migrations, one format (EMBER).** 6.6.0 is the first release anyone else
runs; every node is redeployed fresh. All legacy and prototype formats and every
migration path are deleted; same-format export/import stays as backup/restore; the
previous-layout reader (D38) is withdrawn. *Locks in:* a format change before the
cut costs a full recertification, never a migration; after the cut, the format is
versioned by release sequence.

**D-2 Qualify once (EMBER).** No repeated qualification during development. The
natives, the OpenBSD guest, F1–F8, the scale curves and the held-out 1M run happen
once, in the prerelease convergence checklist, on one immutable candidate. Lanes
certify what they change and run the native modules they name; a green is never
transferred to changed bytes.

**D-3 Complete before the cut (EMBER).** Nothing identified is deferred past 6.6.0.
The one exception is by ember's own choice: a `remember DAYS`-style history window
(D13 option b) is wanted eventually but not now.

**D-4 The served product is an SBCL core without ACL2 (EMBER).** The extractor
produces a 56 MiB core (vs 496 MiB with ACL2); the Chicken build is the oracle for
the differential, not a product; no Chez port; CakeML is out. The ACL2 image stays
the proof reference and is what the checklist qualifies against. The extraction gate
is fail-closed (every child status, an expected case manifest, refused truncations),
per GPT-6's correction.

**D-5 Release numbering is a sequence, not numeric order (EMBER, earlier).**

## 2. Memory

**D-6 F8 split adopted (EMBER):** virtual / accountable physical / working set, with
the small-node targets 256 MiB accountable and ≤128 MiB working set under a named
profile; the old "reserved ≤ 256 MB" verdict stays recorded as unmet. F4 bars adopted
with GPT-6's numbers (H = 30 s is an explicit change from the 60 s design).

**D-7 Credits, not worst-case reservation (EMBER, per GPT-6).** Admission is by
credits acquired before allocation (PRF-380); the credit travels with the buffer
through submission, durable I/O and retention; the heap figure is BASE + a credited
pool sized from the operator's budget. The article in flight is packed (512-octet
blocks, one octet per octet) and the queued submission is packed as one natural:
the default profile at a 1 MiB article limit admits 30 articles mid-body instead of
one; the reserve fell from 34 MB to 2.2 MB.

**D-8 Stall before memory (project rule, reaffirmed by EMBER).** When the node
cannot honour its figure it refuses new work by name; it never grows. Applied to
the new suffix bound below.

**D-9 Paged history (EMBER: "avoid materializing the entire heap store"; "more
on-disk data structures is extremely wise").** The resident set becomes a function
of connections and the suffix since the last checkpoint, never of the store. The
design (`planning/design-paged-history-2026-09-29.md`) surveys twelve store-scaling
heap structures; the record rows already have a page image written at every
checkpoint but the served readers still read the heap. The figure becomes
BASE + suffix bound + cache budget + credits, independent of T and H, which then
bound disk only. Small profile: 1,179 MiB reserved today → about 740 MiB; the
scale gate's 26,929 MB and the 1M store's 54 GB reserve the same 740 MiB plus
cache. First implementation: the Message-ID table on pages (certified), then the
history rows via `attach-stobj` on the existing image, then the figure book.
*Makes moot:* the header weight question (8 vs 4 heap octets per header octet),
F1 peak-vs-settled, and it makes D13 (a) painless. *Ruling (EMBER):* when a
checkpoint cannot run (a pinned reader, a stalled disk) and the suffix would pass
its bound, new POSTs are refused by name; `checkpoint-deferred` is reported (a
tenth health state, built) the moment the bound is at risk; reads are unaffected;
provisioning in time is the operator's job.

**D-10 MemoryMax sits above the figure (EMBER):** the unit's cap is the accountable
figure plus the measured fixed runtime plus a margin, set after the convergence
measurement; the contract quotes both numbers.

**D-11 F1's reopen figure is the peak (EMBER),** not the settled RSS; a 2 GB VPS
lives at the peak.

## 3. Store representation

**D-12 Configuration switches are log events, not profile fields (COORDINATOR,
ratified).** The profile is the immutable layout/limits declaration, its digest
locked into the log at open; a layout change recertifies the tree. A codec switch,
a limit raise, a retention rule is an event in the log, effective at a named
transaction id, replayed in sequence with the data it governs. Every record names
the codec current when it was written (dictionary-by-digest). *Locks in:* every
switch has a replay rule; live reconfiguration needs no restart and no export.

**D-13 BLAKE3 is algorithm 2; nothing reads algorithm 1 (COORDINATOR, ratified).**
Identities carry one algorithm octet; the SHA-256 path is deleted; page digests are
integrity checks, never identities in signed statements. The quoted bound is the
128-bit collision bound.

**D-14 The page image FNADTSN2 with need-verdict readers (COORDINATOR, ratified).**
Free-region placement, the index stored as a value in the page, event and record
rows on pages, the history stobj a view over them; a reader returns the answer or
the page it needs, the host fetches outside the owner mutex with a generation, the
expected page identity and a pinned continuation; the open reads only the root
pages. A late page is unavailable, never absent; a timeout never turns missing data
into absence.

**D-15 One abstract stobj over the page image, not a twin per consumer
(COORDINATOR, ratified).** The correspondence is proved once; readers are classified
by GPT-6's access patterns (count, indexed, bounded cursor, fold, append-prefix,
snapshot) and each pattern's refinement proved once and specialized. Readers are
moved one at a time with an equality theorem to the heap reader.

**D-16 Exact prefix binding, then lineage (found this session).** The manifest binds
the image to the exact log prefix by content (A2, landed). Proving the composition
showed the remaining hole: with an empty suffix, a restored backup that later
diverged can be swapped in as the checkpoint and the open accepts it, because two
forks with identical prefixes are indistinguishable by content. *Decision:* a
lineage identity in the log header and the checkpoint manifest (a per-open
generation nonce or a publication hash chain), a foreign lineage refused by name
even with an empty suffix, stated as the composed theorem with the fork as the
hypothesis-removal tooth, then a one-round format change (no migrations). Whether
an operator may deliberately adopt a fork with an explicit verb is open (ember:
"interesting"); the lane proposes, does not build.

**D-17 Online reclaim (COORDINATOR, reversible).** Disk blocks of dropped segments
are released on the running node; the reclaim swap is built off the mutex in
bounded steps against a pinned generation; the swap installs only when its delta
is empty and defers by name otherwise, until the incremental finalize (proved this
session: finalize of extend(E, Q) from E's carried verdict) has its resume made
linear in the delta. Proving the swap found that the next POST after a swap never
completed; fixed, with the connection-history keystone over the rebuilt store.

**D-18 The reassembly job's state lives in the events (COORDINATOR).** For hosted
BP reassembly, the job state is carried in the `:family` / `:persist-result`
events with an invariant, not in the machine state, because the log is the state
of record and the machine state is derived; the fixed held-image cap becomes a
per-step work bound and a profile limit refused by name.

## 4. Assurance

**D-19 Precise coverage replaces the keystone heuristic.** A tool walks the
certified world and attributes every theorem's function symbols by side; of 1,117
host-called entries, 396 are decision entries (they branch and name an outcome) and
330 had no direct theorem: 257 `:program` (unmentionable by any theorem), 73
`:ideal` or guard-verified. Two campaigns run on it: every non-`:program` decision
entry gets a keystone with the entry in the conclusion and its full antecedent
(63 → 47 so far; a `:delegates` declaration files exact one-form wrappers as
plumbing only when the call graph and a callee theorem agree); every `:program`
host-called entry becomes `:logic` guard-verified (a lint refuses new ones; 596
baselined). The three most surprising gaps GPT-6's style of question would have
asked about — an authorizer with 1,175 theorems about its helpers and none about
itself, the BP receive boundary, an admission proved from its own hypothesis — are
closed.

**D-20 Closure theorems.** The premise audit found 1,011 unestablished premises at
hosted entries; its two largest "never established" items were the reader's (it did
not open `let*`). Proved: refusal-is-effect-free is false by design for exactly one
refusal (the full-store POST consumes one transaction id) and every reader of ids is
accounted; every state a clean stop leaves either opens or is refused by identity
(the finalize's replay and frontier arms are dead by theorem); the B10 bug (a config
record on a full store made the store unopenable) is closed by a composed theorem
over every event kind, not by a repaired check.

**D-21 The resource contract (EMBER: "could it have a warranty?").** A document of
worst-case bounds per resource with the theorem or convergence measurement behind
each; the one open row was closed by a byte-level theorem (an acknowledged article
is recoverable at every crash point of append, fence, extension and recover).

## 5. Protocol and operations

**D-22 COMPRESS, SASL and expiry are in 6.6.0 (EMBER).** DEFLATE (RFC 8054) on the
wire with one ACL2 inflater (148 µs per article) shared with the store; the store
holds DEFLATE with a dictionary by digest (baseline 2.13×); LZ4 retired; learned
dictionaries dropped (relearning and transcoding are not simple). SASL PLAIN and
SCRAM-SHA-256[-PLUS] certified and native-green. Expiry landed. A wire dictionary
negotiation (an fn extension, XFN-DICT) is specified and its decisions certified;
the serving side is in flight. *Ruling (EMBER):* the preset-dictionary deflater is
an SBCL one only if it clears a 2×-of-zlib gate in one increment, else zlib bound
as a foreign library; the inflater stays verified either way.

**D-23 Operability: everything in place, while serving (EMBER: the docs' "raise
limits with an export, then an import" was unacceptable).** Limits are live config
events with `policy set`; a raise beyond the running reservation is recorded for
the next start and says so; maintenance verbs (recover, inspect, export, checkpoint,
snapshot) run on the running owner through the admin route, refused by name with
what it would take; a stopped store's status reads the checkpoint header, never a
replay; upgrade-beside with rollback, backups without a stop, peering as a record,
one account system, moving a node, `retire --drain` are rows in flight. Reasoned
replies are printed lines, not one colon-joined word.

**D-24 BP carry `drop --abandon` (EMBER).** An operator waiver event (principal,
obligation, reason) releases a carry pin through the receipt's own retention event,
the only release path; exactly once across the death between its two writes; a late
receipt refused as waived. Per GPT-6's "drain, transfer, or an explicit waiver".

**D-25 D13 forgetting (EMBER):** never forget for 6.6.0; capacity by raising the
transaction limit in place; expiry frees disk only. A bounded window later.

**D-26 Security rulings (EMBER, today).** TLS handshakes on 563 are metered: a
per-source and node-wide budget decided by ACL2 before the handshake runs, refused
by name, live-tunable, with a bound theorem in the contract ("we shouldn't require
being behind a proxy to be secure"). The Message-ID table, open to sxhash
multicollisions, is replaced by the paged index with a per-node keyed BLAKE3 tag and
a per-lookup page bound independent of the adversary's choices. Kept node secrets
across a reinstall mean the same cancel authority; if a redeploy rotates them,
pre-redeploy own-Cancel-Lock is lost and documented.

## 6. Method (what the session confirmed)

- Composing local theorems keeps finding real bugs: the owner relation false after a
  peer open, the unopenable store after a config record on a full store, the POST
  that never completes after a reclaim swap, the checkpoint that omitted the history
  image, the open that parsed every payload for an empty index, the forked backup
  accepted as a checkpoint. GPT-6's "the main risk is an unclosed composition" was
  right; the answer has been to state the composed theorem first and let the tooth
  find the case.
- Six branch seams in one hour, all the same shape (two lanes editing one host file
  or read chain), fixed by a union rule: the lane owning the host code merges the
  other and reports once.
- Certification wall time is the include chain, not the book count; chain-first
  scheduling, certification images at checkpoints and form-keyed certificates took a
  landing cycle from 60–90 minutes to about 15–25, and a comment-only edit from 751
  books to zero.

## 7. Questions for GPT-6

1. **Lineage (D-16):** is a per-open generation nonce in the log header sufficient,
   or should the lineage be a hash chain over checkpoint publications so a fork is
   detectable even when both sides later publish? What should a deliberate
   fork-adoption verb require of the operator, if it exists at all?
2. **Paged history (D-9):** the resident set is now bounded by connections and the
   suffix; the suffix bound is enforced by refusing POSTs when a checkpoint cannot
   run. Is refusal the right default, or should a node degrade (serve, stop
   accepting) with a longer deferral window under an explicit operator setting?
3. **The Message-ID index (D-26):** keyed BLAKE3 tags with one overflow page per
   home page. Is a per-node key enough, or should the key rotate per checkpoint
   generation to bound what an insider who learns it can do?
4. **Handshake metering (D-26):** the source key is the peer address. What is the
   right shape for CGNAT and for a peer behind a load balancer, without reintroducing
   an unmetered path?
5. **Coverage (D-19):** the `:delegates` exemption files a one-form wrapper as
   plumbing only when the call graph and a callee theorem agree. Is there a class of
   wrapper this admits wrongly?
6. **The compression gate (D-22):** is 2× of zlib's throughput the right bar for
   keeping a verified-Lisp deflater, or should the criterion be memory and worst-case
   input behaviour rather than throughput?
7. **Anything here that reopens a call from your 2026-09-28 review.**
