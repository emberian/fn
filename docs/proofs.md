# Proof strategy and evidence

Status: component theorems are being certified as implementation advances. The
[proof registry](../planning/proofs.json) is the authoritative ledger for the
larger targets, which remain open until their complete statements are supported.
See [implementation status](implementation.md) for executable scope. Partial
lemmas do not close an entire subsystem proof target.

## Assurance grows with the implemented surface

Each new reachable command, persistent record, transition, codec or adapter
operation adds assurance obligations. A proof about an older component does not
automatically cover a new caller or the composition between components. Keep
three things distinct in the [closure inventory](../planning/archive/assurance-closure.md):
evidence for implemented behavior, missing evidence for implemented behavior,
and requirements for features that have not been implemented.

For each behavior-changing batch, record the affected stable requirement/proof/
scenario IDs and the following change in scope:

| Changed surface | Evidence to add or explicitly leave open |
| --- | --- |
| State or transition | Meaningful initial/reachable invariant, rejection behavior, preservation of prior accepted facts, and finite traces |
| Caller or composition | Relation to the actual callee's state and hypotheses, including pending work; shape validity alone is insufficient |
| Durable record or side effect | Byte/record correspondence, barriers and uncertainty, live-versus-replay agreement, restart and lost-completion cuts |
| External bytes or raw execution | Decoder domain/canonicality, limits and work, guard status of the executed call graph |
| Authority or release | Exact evidence/context binding, durable decision, explicit policy/crypto/peer premises, preservation of independent obligations |
| Transport or scheduling | Duplicate/reorder/expiry/contact behavior; safety and conditional progress stated separately |

A feature checkpoint may remain experimental with an exact open list. It does
not count as assurance closure until its applicable claims have evidence.
Changing a profile or a trust assumption to avoid an obligation changes the
contract and must be recorded as such. Keep critical missing composition/recovery
evidence in a bounded closure batch before building dependent behavior on it.

No count appears in this document. Theorem, root, guard and test counts live
in [the generated ledger](../planning/ledger.md) and nowhere else, because a
number that is typed is a number that drifts. Prose carries the property, its
hypotheses and its covered scope in one sentence; it does not carry counts.
Report the property, supported domain, source digest and assumptions. A growing
count does not demonstrate that the assurance gap is shrinking. Review the
frozen batch once, fix concrete defects, and keep independent work moving; this
discipline adds no approval ceremony.

## Refinement ladder

1. **Abstract executable state:** finite maps/records and event transitions.
   Prove recognizer preservation, identity/allocation invariants, and phase rules.
2. **Bounded bytes:** refine external parsing/encoding to the accepted object and
   NNTP domains. Prove decoding, deterministic preimages, and framing properties.
3. **Crash storage model:** relate logical acceptance to records, writes, barriers,
   recovery, and checkpoint selection under named platform assumptions.
4. **Concrete execution:** use guard verification and explicit correspondence
   between logical maps and efficient representations, including abstract stobjs
   where useful. Include range-query completeness in index obligations.
5. **Multiple nodes:** reason about validated fact sets, obligation transitions,
   duplicate/reordered exchange, and explicitly conditional progress properties.

The program used by the host must be these definitions or a justified refinement.
An abstract model plus an independently written server is insufficient evidence
for claims about the running server.

## Shape of the claims

State preservation has the schematic form
`inv(s) and permitted-event(s,e) => inv(next(s,e))`. Prefer total, guarded
interfaces that explicitly reject malformed events rather than assume away
untrusted wire inputs. An invariant must include meaningful initial states and
reachable examples, so a theorem is not satisfied by an empty state domain.

Trace induction lifts one-step safety properties to finite executions. Eventual
delivery additionally needs a scheduling/contact/resource model and A-FAIRNESS.
Do not describe a safety theorem as proving inevitable delivery.

Crash refinement relates a logical transaction history to stable and volatile
storage state. A completed barrier constrains crashes; it does not simply assert
the result we intended to prove. Unacknowledged commits may survive. Index
reconstruction, checkpoint replacement, and compaction require their own
correspondence results.

Retention theorems cover protected dependency closure, not just body objects.
Handoff theorems identify cooperative-peer and node-survival hypotheses. A
cryptographic verification result alone does not establish an honest disk write.

## Trust and executable efficiency

Record assumptions from [the failure model](../specs/failures.md) per target.
Do not introduce unrestricted injectivity axioms for finite hashes. Cryptographic
properties and implementations need separately scoped arguments or assumptions.
Do not turn `skip-proofs`, trust tags, or axioms into a certification shortcut.

Termination admission, guard verification, theorem proof, book certification,
and platform tests are different evidence. A certified book can still depend on
trusted facilities; disclose those explicitly. Run certification in a clean
environment separated from host raw-I/O integration.

## The generated ledger

[`planning/ledger.md`](../planning/ledger.md) and
[`planning/ledger.json`](../planning/ledger.json) are generated by
[`tools/ledger.py`](../tools/ledger.py) from `books/*.lisp` and
`tests/acl2/*.lisp`. The tool has its own s-expression reader: it never
interns, evaluates, or macro-expands, so reading a book cannot run a book. It
reports, per book, every `defthm`, `defun`, `verify-guards`, `must-fail`,
`assert-event` and `include-book`; the guard status of every function; and the
theorems whose shape disqualifies them as registry evidence.

`python3 tools/ledger.py --check` runs inside `make check` and fails on a
cited theorem that no book defines, a cited theorem the detector flags, a cited
theorem in a book no Makefile certification root reaches, a cited function
whose guards are not verified, or a stale `ledger.md`.

`python3 tools/certified_claims.py` also runs in `make check` and fails it.
For each target marked `certified`, it checks that the registry names curated
events in the current books and that each event's defining book has archived
manifest evidence for its current source and include closure. It uses
`green_check`'s verdict, so a pass records compatible evidence from a named
run, not a certificate installed here or a qualified native image. The row
must also cite that evidence itself: its `evidence` list names at least one
manifest under `planning/evidence/manifests/`, every cited manifest exists, and
for each event's book some cited manifest records the book `passed` at its
current source digest and include closure. A certified row whose own citation
has gone stale fails even when an uncited run would vouch for it; `--explain
PRF-xxx` names, per event, the book, its current digest and the newest
manifest that certified it, which is the citation to add. A row with no such
manifest is not `certified`.

`python3 tools/proof_cost.py` in `make check` holds the ten-second rule as a
ratchet, measured at two jobs (decision D26). Only a run whose manifest
records `jobs_effective` of 2 or fewer counts. A measurement at more jobs is
printed as `RECORDED ... at N jobs` and never fails. A manifest without
`jobs_effective` is unknown: its measurements are skipped with a warning that
names the run. `planning/proof-cost-baseline.json` lists each book whose worst
current measurement at two jobs or fewer, over every host and toolchain, was
above ten seconds when the baseline was written, with that figure, its run,
host and job count. The check fails
on a book above ten seconds that the baseline does not list, or that runs more
than 25 % over its listed figure; a listed book now under ten seconds is
reported "improved; remove from baseline". Unmeasured books remain a warning
with their count. `--write-baseline` drops improved books and lowers numbers
but never adds a book or raises a figure; that needs `--allow-regression`,
which is a decision to record in the commit that uses it. The baseline only
shrinks.

### Guard status

Four states, from the source rather than from the ACL2 world: `verified`
(a `verify-guards` event, or `:verify-guards t`), `declared-off`
(`:verify-guards nil` and never verified afterwards), `default-guarded` (no
`:verify-guards`, but an explicit `:guard` or `type` declaration, which under
the default `set-verify-guards-eagerness` of 1 means ACL2 verified guards at
definition time) and `default-unguarded` (neither). Only `verified` is an
observation; `default-guarded` is an inference about what ACL2 did, so the
ledger check accepts only `verified` for a function cited as evidence. The
guard-audit test books, which ask ACL2 for `:common-lisp-compliant`, remain the
authority on what is actually guard-verified in the world.

### The suspect detector and what it cannot see

A flag is a claim about the *shape* of a statement, never about its truth.
Every flagged theorem is proved. The six shapes:

- **closed-theory-corollary** — the entire proof is `:in-theory '(A B)` over an
  explicit list of existing theorems, so the statement follows by rewriting and
  the work is in A and B.
- **instance-corollary** — the conclusion is an existing theorem's conclusion
  instantiated, and every hypothesis of that theorem is already a hypothesis
  here, so nothing was discharged.
- **reflexive-conclusion** — a conjunct of the conclusion is `X R X` for a
  reflexive `R`, possibly after unfolding non-recursive definitions.
- **definition-restated** — the conclusion is the body of a function it calls,
  possibly with the conjuncts the hypotheses already assert struck out.
- **recognizer-body-conclusion** — the conclusion is the body of a hypothesis's
  own recognizer.
- **branch-of-definition** — a hypothesis is a branch test of the function
  under discussion, or its negation, and the conclusion is exactly that
  branch's value.

Its limits, stated so nobody reads a clean report as a clean bill of health:

- It unfolds only non-recursive definitions and only to a bounded depth, so a
  tautology reachable through a recursive function is invisible to it.
- Its substitution does not track binding forms beyond inlining `let`, `let*`
  and literal lambdas, so a shadowed variable could defeat a detector.
- It ignores `make-event`, which it cannot read statically.
- It cannot see a theorem that is true, non-trivial, and about the wrong
  subject. "The theorem subject is the function the host calls" is a judgment
  recorded by hand as a `pending_subject` note in
  `planning/proof-events.json`; no shape reveals it.
- A constrained function's local witness is excluded from unfolding, so the
  detector says nothing about whether an assumption's constraints are
  restrictive. That is what the `must-fail` cases in
  `tests/acl2/assumptions-tests.lisp` are for.
- The absence of a flag is not evidence of strength. Teeth are.

### The four shape lints

Besides the suspect detector, `tools/ledger.py` reports four WARN lints,
counted in the generated ledger and listed in full under `lints` in
`ledger.json`. None judges truth; each names a cost this tree has already paid.
*Export hygiene* flags a theorem a book leaves enabled whose conclusion is an
equality between two *different* one-argument applications, or a `consp`/`len`
conclusion backchained to a `len` hypothesis. The same accessor on both sides
is a preservation lemma, which is the shape the export policy asks for, and is
not flagged; `local`, `defthmd`, `:rule-classes nil` and a non-local closing
`in-theory (disable ...)` each exempt a rule, because none of them leaves it
enabled downstream. A book that withdraws its helpers by naming them --
`(deftheory fn-x-vocabulary '(...))` and then disabling that name, including
through `(:d name)`/`(:e name)` runes, `set-difference-theories` or
`union-theories` over names the book defines -- is read the same way: the
theory is resolved to its rules, and each counts as withdrawn. What cannot be
read literally, such as a computed theory over `current-theory`, contributes
nothing, so an unresolvable withdrawal warns rather than going quiet. *Teeth form* flags a `must-fail` whose body is a bare
`thm`/`defthm` whose statement mentions no constant -- no keyword, literal,
string or `defconst` -- so it refutes a general claim rather than a specific
violating value. *Include hygiene* flags a non-local `(include-book "x")`
whose target is a local book of this tree that ends with no theory withdrawal
at all -- the same computation export hygiene uses to exempt a rule, applied
to the whole book. Such an include is not an interface: it enables every rule
`x` leaves enabled in the includer and in everything that includes the
includer. The measured case is `books/bp-ingress.lisp`, which took a non-local
include of `article-properties` for a single guard hint and turned a
six-minute proof into an 1800 s timeout, 1.92M backchain frames of which none
contributed; making that include `local` is what the lint asks for, and a
`local` include is never flagged. A `:dir :system` include, and a reference
this tree does not read as a book, are not judged, because there is no export
theory here to read.

*Host names* is the fourth, and the only lint that reads files no
certification touches. `host/*.lisp` and `host/native/*.lisp` are `ld`ed by
the bridges at start-up, so an undefined name in them is found by a bridge
dying: `host/checkpoint-host.lisp` went on naming `*fn-store-groups*` after
the compiled group table was deleted, and every `Acl2Store` constructor failed
with a Translate error until a later lane noticed. The lint reads each host
file, plus any `.lisp` outside `books/` and `tests/acl2/` that a host file or
a `tools/*.py` bridge names in an `(ld "...")`, and reports every symbol used
in function position and every `*constant*` that is defined neither in that
file, nor in a file it `ld`s, nor in the include-closure of the books it
includes, nor in [`tools/acl2-builtins.txt`](../tools/acl2-builtins.txt) --
the ACL2 and Common Lisp names the host files use today, generated from the
ACL2 8.7 sources by the recipe in that file's header rather than typed. A
finding says which: a name defined nowhere in the tree will fail the `ld`,
and a name defined in a book or host file this one does not load resolves
only because something else loaded that file into the same session first,
which is a load-order coupling no file declares. The reading is deliberately
quiet, because these files are not certified and a noisy lint is a skipped
one: `loop` bodies, package-qualified heads (`sb-posix:open`) and the
arguments of a macro this tree defines are not read at all, and a `local`
book definition counts as visible. `make check` prints all four as `WARN`;
`python3 tools/ledger.py --check --strict` fails on them, which is how a book
or a cluster that has been cleaned keeps its state.

### Certificates, the cache, and the farm

Every fn tool that starts ACL2 sets `ACL2_BOOK_HASH_ALISTP=NIL`, so ACL2 8.7
hashes book *contents* rather than write dates and absolute paths: a
`.cert`/`.port` pair is valid in any worktree and on any host whose book
content matches. [`tools/certs.py`](../tools/certs.py) is the consequence.
Two rules, each paid for by a poisoned cache. First, **a pair is published
only against a certification manifest**: a `.cert` lying beside a book proves
nothing, since after a merge it can be the previous source's certificate, so
`publish` reads the manifests `tools/certify_books.py` writes
(`--manifest PATH`, or every `build/acl2/certify-*/manifest.json` under the
worktree) and caches a book only when the source beside it still hashes to
that run's `source_digests_sha256` (and `source_digests_sha256_after` when the
run recorded one) and the certificate beside it still hashes to that run's
`certificate_digests_sha256`. There is no other publish path, and a manifest
that did not pass vouches for nothing. Second, **the key is the closure**: a
certificate is valid only for a book *and every book it includes*, so the key
is the SHA-256 of the sorted `<path>:<sha256>` listing of the book and its
whole local include closure, resolved as ACL2 resolves `include-book` and
ignoring `:dir :system`. Same book bytes over a changed dependency is a
different key, not a hit ACL2 would then refuse; the listing is recorded in
the entry's metadata. A third rule decides *where* a pair may be installed.
An ACL2 certificate's post-alist names every sub-book by the **absolute**
full-book-name it was certified at, and this project once read that as
making a pair from worktree X unusable in worktree Y. Measured on persvati on
2026-09-23 ([the record](../planning/evidence/certificate-cache-2026-09-23.md)),
it is not: with checksum book-hashes ACL2 compares sub-books by familiar
name, annotations and book-hash, never by full-book-name, and include-book
opens only the files beside the including book, so a closure assembled from
several origins includes cleanly, with those origins on disk, removed or
edited. The messages that looked like a path conflict (`its certificate
requires .../X/books/acceptance.lisp, but .../Y/books/acceptance.lisp has
been included`) are printed only after a book-hash or annotation mismatch,
and name every entry of the post-alist whose path differs. Each entry still
records the `origin_root` it was produced in: `install-set` takes one
complete origin when one exists and otherwise composes the closure from the
newest usable pair per book, never from a live worktree still on this
machine, and `install` keeps the per-book rule and reports `foreign-local`.
A pair whose bytes match a refused entry is removed, so a worktree an
earlier origin-blind install poisoned recovers. `install-set` is all or
nothing, which after a change low in the graph meant refusing the run
(2026-09-23: 338 of 409 books cached at dev's digests, 70 not, and the treewide
submit was refused). **A certification run is incremental by default:**
`certs.py install-partial` installs every book of the roots' closure, roots
included, whose pair is cached at its current closure key and this ACL2
toolchain identity, each from its own newest usable origin, and removes any
local pair of the rest; `certify_books.py --incremental` does that in-process
once it knows the toolchain, certifies the uninstalled books in dependency
order with the critical-path scheduler, and does not certify a root that
installed. Its manifest keeps `requested_books` as the books ACL2 certified
and adds `roots`, `book_provenance` (`installed` or `certified` per closure
book), `installed_books` (book to origin), `cache_install` (counts, origins,
`roots_installed`) and `installed_over_failed`: an installed book one of whose
dependencies this run certified and failed, which is a certificate of its
bytes that does not include here. An installed book over a dependency the run
certifies is sound because its key fixes that dependency's bytes, and ACL2
checks the dependency's book-hash, which a fresh certificate of those bytes
reproduces (the record's case 5). A fully cached closure certifies nothing and
passes with every root `installed`. **The compiled file travels with the pair**
([the record](../planning/evidence/fasl-cache-2026-09-25.md)): ACL2 on SBCL
writes `book.fasl` after the certificate and include-book loads it only when
it is not older than the `.cert`, so a book installed with a pair alone
loads uncompiled. The runner records `compiled_digests_sha256` for each
compiled file not older than its certificate; `publish` caches it in the
same entry, under the same closure key and toolchain identity, only against
that record; an install places it only with its pair and dates it no earlier
than the certificate, installs the pair alone when the entry has none
(removing any local `.fasl`), and removes it with the pair on every
uninstall. A fasl is relocatable as the pair is (its embedded source path is
a debugging name ACL2 never opens) and is specific to the SBCL runtime and
ACL2 core the toolchain identity names. `cache_install` counts
`fasl_installed` and `fasl_missing`.
Farm runs are the reusable case: `farm.py submit --remote-root` runs under a
path that does not exist here, and `wait` publishes with that path as the
origin, so those pairs install into any local worktree. `install` computes the
same closure key per book and copies in each matching pair, keeping a
byte-identical local certificate; `status` prints coverage, counting
foreign-local entries separately. `tools/certify_books.py` publishes against its own manifest
after a passing run, which `--no-publish` suppresses, and `make certs-install`
/ `make certs-publish` are the manual ends. What this does not establish:
nothing here proves a book certifies. That is the runner's fresh success
marker per book, and ACL2 checks the installed pair again at include time.

A farm box is where that origin rule cost the most. Its certificates live in
finished gate directories and in lane roots, all of which still exist on the
box, so every entry in its cache was `foreign-local` to every lane: a lane's
`farm.py submit --closure` onto an empty remote root re-certified the whole
substrate, article and CBOR dependency set for four new books, half an hour of
ACL2 the box had already run. A gate directory is not a live worktree, though.
It is made from one commit, certified once by the gate, and never certified
into again; a finished farm run root is the same kind of thing. So an entry
also records `origin_kind` -- `worktree`, `gate` or `run` -- and `install`
takes a snapshot entry wherever it finds it, after this worktree's own entry
and after a relocatable one, while a `worktree` origin that exists here is
refused exactly as before. An entry with no recorded kind predates the rule
and counts as a live worktree. A snapshot origin later overwritten or removed
changes nothing for a pair already installed elsewhere: ACL2 never reads it. [`tools/gate_publish.sh`](../tools/gate_publish.sh) is the
one line a gate script runs after `make certify`
(`sh tools/gate_publish.sh`); it publishes that gate directory with
`--origin-kind gate` into `$FN_CERT_CACHE`, `~/fn-certcache` on persvati and
`/tank/fn/certcache` on hbox. `farm.py submit` then installs that cache into
the mirrored tree before it starts the runner, and records what it found with
the run (`cache_install`: installed, kept, uncached, foreign-local); the
runner publishes back into the same cache as it goes
(`FN_CERT_ORIGIN_KIND=run`) and `wait` publishes the run's pairs there once
more after it, so the next lane on the box starts from them. Measured on
persvati, 2026-09-20: seeding the cache from one finished gate directory
published 209 pairs in 1.4 s, and the next `submit --closure books/wire`
installed 172 of them before the runner started.

**The seeding follows each book, not the run's verdict.** The runner used to
publish only inside `if success:`, and `success` is a statement about the
whole requested batch, so a wide run -- which exits non-zero while any root
on this tree carries an open theorem -- cached nothing at all. Measured on
persvati 2026-09-20 against an isolated cache, closure over
`books/byte-store-scan` at `--jobs 2`: the run certified 21 of 22 books, exited
1, and left 0 entries, and the next submit into the same remote root reported
`installed 0, kept 0, uncached 267`; with the per-book publish the same two
runs report 21 entries and `installed 21, kept 0, uncached 246`
([the record](../planning/evidence/farm-cache-failed-run-2026-09-20.md)). A
pair is published on its own book's evidence -- that book's fresh marker, its
clean log, its certificate -- so a run that is killed, that times out, or that
no one waits on still leaves what it proved. `wait` fetches and publishes on
its timeout path too, and says what it left running. What that removed had to
be replaced: publishing only after a wholly successful run made the run-wide
`sources_unchanged` check stand in for a per-pair one, so `certs.publish` now
refuses a book whose whole include closure no longer hashes to what the
manifest recorded. A dependency edited mid-run leaves the book's own source
untouched, and the entry would otherwise be a real certificate filed under a
key describing source it was never produced from.

**One lock per box, and it is a `flock` file.** A gate is a fresh directory
certified once, and a second `make certify` against the same cache while the
first is publishing gives the second a cache it cannot vouch for. The hand
gate scripts on the boxes take `flock` on `$HOME/fn-gates/.gate.lock`
(persvati) and `/tank/fn/gates/.lock` (hbox) -- `exec 9>LOCK; flock 9` at the
top of `gate.sh`, held until the script exits. `tools/verdict.py` kept a
second scheme of its own beside them, an atomic `mkdir` on `.verdict.lock`,
and two schemes that cannot see each other are not a lock: a verdict run and
a hand gate could certify on one box at the same time. The gate script
`verdict.py` writes now opens the same file, and before it launches anything
`verdict.py` asks the box whether that lock is free (`flock -n LOCK true`) and
refuses with the holding process named rather than queueing silently;
`--wait-for-lock` queues. A `flock` dies with the process that holds it, so
there is nothing to force-unlock and nothing that can go stale. It is a
CERTIFICATION lock: `tools/farm.py` runs do not take it (they are `--closure`
runs into their own remote root), and neither do the deploy, two-node, INN and
scale fibers.

**And the manifests answer one question nothing was asking.**
[`tools/green_check.py`](../tools/green_check.py) hashes every root in
`ACL2_BOOKS` and every book in those roots' local include closure, then finds
the newest run -- across the committed archive and this worktree's unarchived
`build/acl2/` runs -- that recorded a verdict for those exact bytes, so each
book is green at its current digest, *red* at its current digest, never at
this digest (naming its last green at an older one), or never a requested root
anywhere. It exists because on 2026-09-21 `dev` had been red for a day in
`books/stx-evidence-records`, `books/checkpoint-compaction`,
`books/hybrid-store` and `books/feed-connection`, each committed by a lane that
never certified it, with the failures already recorded at those digests in the
archive while every reader took `git log` for certification; `make check` prints
its three summary lines and `--strict` fails on a book whose newest verdict at
its current bytes is a failure. What a green there is *not*: one host's one
toolchain identity once accepted those bytes, which is not a certificate in
this worktree, says nothing about images or saved cores, and -- since the
verdict is about the book's own digest -- comes with `deps_moved`, the closure
members whose bytes have moved since, because same book over a changed
dependency is a different key.

**And the same audit is the merge gate.** `python3 tools/green_check.py
--changed-since REV --strict` lists the books and test books whose bytes differ
from the merge base with `REV`, every audited book whose include closure
reaches one, and each one's verdict at the bytes a merge would carry; it exits
1 unless every row is green. It is finding F4 of
[the proof-engineering review](../planning/review-2026-09-22-proof-engineering.md):
on 2026-09-21 five commits changed the machine under invariant books nobody
recertified, and `git log` read as green for a day. Root's procedure: a lane
certifies what it changed and its test books on the farm before it reports;
root merges locally with `--no-ff`, runs `make check` and the gate against
the pre-merge head (`ORIG_HEAD`) to see what the merge carries, pushes, and
runs one provisional wave (`tools/triage.py`) over the image closure per
batch of merges, comparing red sets and forms with the previous wave's. A
new red belongs to that batch and is fixed before the next merge. A
dependent already red for a reason the branch did not cause does not hold
the merge: on 2026-09-22 that reading held a finished lane for four hours
and added nothing, since its own books had certified inside the lane.

**And one habit is read statically.** [`tools/theory_check.py`](../tools/theory_check.py)
lists every book that opens a theory at its top for every proof in it, and
flags the ones opening a *codec* theory there (the CBOR, record, statement and
frame codecs, or any theory named `codec`), which is finding F3 of the same
review: a goal that only dispatches on a kind then carries the whole codec and
stops returning. `make check` prints its count; `--strict` fails on any codec
opening and is not yet wired in, because the count on 2026-09-22 was 74 books
and the rule in AGENTS.md applies to new and touched books first.

**And proof work gets a live session.** [`tools/proof_repl.py`](../tools/proof_repl.py)
keeps one ACL2 alive behind a Unix socket: `start NAME BOOK --upto EVENT`
installs the book's certified closure from the local cache, starts ACL2
through `tools/acl2` (the slot pool holds), sets the connected book directory
and loads the book's forms up to the named event, stopping at the first one
ACL2 refuses; `send NAME FORM` delivers one form and answers with the key
checkpoints and the summary (`--full` for everything), an event wrapped in
`with-prover-time-limit` so a search that stops returning costs a minute, not
the session; `status`, `stop`, `list`. It is the loop the freeze lanes did not
have (the review's F5): seconds per attempt against cached certificates,
instead of a closure run per attempt on the farm. A form ACL2 admits there is
not a certificate; the event goes into the book and the book certifies.
A session holds a pool slot for its life, so it belongs to a lane and ends
with it: `start` records the lane (`--lane`, `$FN_LANE`, or the tree's name:
`build/lanes/NAME`, persvati's `~/fn-gates/NAME-repl`) and stops itself after
`--idle-seconds` (default 7200) without a `send`; `list` shows each session's
lane, age, idle time and deadline, and `reap [--lane NAME | --older-than S]
[--root TREE ...]` stops dead, overdue or a merged lane's sessions, signalling
only the PIDs its state names (PKT-346).

**And when the closure is red, one run tells you every reason.**
[`tools/triage.py`](../tools/triage.py) answers the question an ordinary
certification run cannot. `include-book` refuses an uncertified dependency,
so a closure run stops at the first failure and every book above it reads
"There is no certificate on file": one run names one *layer* of independent
reds, and a ten-deep chain costs ten runs -- the shape that took three lanes,
thirty-nine runs and nine hours on 2026-09-22 (finding F1 of
[that day's proof-engineering review](../planning/review-2026-09-22-proof-engineering.md)). So a triage round does not run the closure the
ordinary way. It runs ACL2's provisional certification
([`tools/certify_books.py --pcert`](../tools/certify_books.py), `:DOC
provisional-certification`): a Create wave that skips proofs and writes each
book's `.pcert0`, **one parallel Convert wave that does every book's proofs**
-- Convert takes a sub-book's `.pcert0` in place of a certificate, so the
proofs are not a chain -- and a Complete wave that renames `.pcert1` to
`.cert` in dependency order. Each failed book is then an independent red (its
Convert failed, with its first ACL2 error and its key checkpoint), a timeout
(its Convert hit the budget; a finding in its own right, F2), *blocked* (its
Convert PASSED, so every proof in it succeeded, and a book below it has no
certificate -- nothing hides behind such a book), a cascade (its Create
failed, the one kind that can still hide another book's proofs, because
Create is the one ordered wave), or unexplained. Measured on a 63-book fn
closure on persvati at 8 jobs: an ordinary round took 690.8 s and named one
independent red with fifteen books cascading behind it; one provisional round
took 317.3 s and named four independent reds and twelve proved-but-blocked
books with nothing unanswered
([the record](../planning/evidence/triage-2026-09-22.md)).

For a Create failure, and only for that, triage still has a second
instrument: substitute the book's last green source -- `green_check`'s audit
names the run, that run's manifest names the digest, `git log --all` holds
the bytes -- into the *remote* tree only and run again, recording the
assumption. It is weaker than it looks, and the same day measured why:
`books/store-node-traces` at its last green source failed on a *different*
theorem, because those bytes were green over dependencies this tree no longer
has. **A triage run is evidence of nothing but its list of reds.** The runner
is invoked with `--no-publish` and `farm.submit` refuses to start a run whose
command line would publish anyway; `farm.fetch_logs` brings back the logs and
the manifest and touches neither cache; no manifest of it is archived; and the
report names no certify run id, because naming one would read as a
certification claim. Provisional certification is a discovery instrument for
the same reason ACL2 says it is: Complete checks sub-books' certificate write
dates rather than their book-hash, and ACL2's own documentation recommends
certifying a project's books from scratch without it for maximum trust.

`tools/verdict.py --reuse-gate [REV]` reads a gate directory that already
exists and builds its per-fiber table from it, shipping nothing and starting
no ACL2. It reads the shape both kinds of gate share (`certify.log`,
`pytests.log`, `publish.log`, `build/acl2/certify-*/manifest.json`) rather
than the `gate.done` only its own gates write, and names any of those four
that is absent in the table. Two tables produced that way, from finished hand
gates on 2026-09-20, are
[persvati `dev-909e055`](../planning/evidence/verdict-reuse-persvati-dev-909e055-2026-09-20.md)
and [hbox `dev-d50c392`](../planning/evidence/verdict-reuse-hbox-dev-d50c392-2026-09-20.md).
The per-root row comes from the manifest's `book_results`, not from
`acl2_exit_codes`: the certify driver ends in `(quit)`, which ACL2 reaches
whether or not the inner `ld` returned on a failed `certify-book`, so a book
that failed still exits 0. On `dev-909e055` the exit codes name one failing
root and `book_results` names twenty-five.

Two further controls on ACL2 processes. `--affected-by BOOK` keeps only the
roots that are, or transitively include, a named book, in Makefile order, so a
change certifies what it can have invalidated and nothing else. It searches
the roots it was given, and with none named that is every root of the
Makefile's `ACL2_BOOKS`, read by `tools/ledger.py`'s `makefile_roots`: the
runner used to carry its own list, which held 71 of the Makefile's 216 roots,
so the same command answered a question about a third of the tree and looked
identical doing it. `--closure` adds the selected roots' own local
dependencies, in dependency order, for the run that cannot assume a valid
certificate exists for them -- a fresh box, or one whose pairs were made under
another worktree's absolute paths; without it such a run dies on `There is no
certificate on file`. `--dry-run` prints the final ordered list, and the
manifest's `requested_books` is that same list, so the evidence names what was
certified rather than what was asked for. Every ACL2 this project starts
first takes a slot from a machine-wide pool of `flock` files
([`tools/acl2_slots.py`](../tools/acl2_slots.py), `FN_ACL2_SLOTS`, default 6 on
darwin and 16 on linux), waits rather than starting when the pool is full,
reports the wait once a minute naming the holders (each slot file's `PID
LABEL`), and records each wait in the run manifest. `FN_ACL2_SLOT_WAIT`
(`tools/acl2 --wait-seconds`, exit 75) bounds the wait: past it the
acquisition refuses and names every holder; unset, it waits. The
lock lives on the open file description, so a killed run leaks no slot.
Iterative `ld` work is the other way ACL2 starts here, and it does not go
through the runner: on 2026-09-19 six ACL2 processes were live on a laptop
whose pool is four, because lanes' scratch drivers invoked `acl2` directly.
[`tools/acl2`](../tools/acl2) is that path's entry to the same pool. It takes
one slot with the same lock directory and the same once-a-minute wait line,
sets `ACL2_CUSTOMIZATION=NONE` and `ACL2_BOOK_HASH_ALISTP=NIL` so an `ld`
session iterates against the world certification will see, and runs `$FN_ACL2`
(default `acl2`) with this process's stdin, stdout and stderr passed through;
`tools/acl2 --timeout 240 < driver.lsp`, also `make acl2-ld`, terminates the
child at that many seconds and exits 124, which makes the brief's
three-minute rule mechanical rather than a PID a lane has to remember to kill.
The slot is released when ACL2 exits, when it is killed by the timeout, and
when the wrapper itself dies.
Before a submit, `python3 tools/native_program_check.py --balance FILE...`
reports each unbalanced form as `unbalanced: FILE:LINE, form starting at
FILE:LINE` (with the first column-0 form inside it, where a missing close
usually shows); `farm.py submit` runs the same scan over `books/`, `host/` and
`tests/acl2/` and refuses before any rsync. Native images and tests on hbox
go through `tools/hbox_native.sh REV MODULE...`, whose `--images` takes
`developer`, `production`, `dtn` and `dtn-developer` (the DTN pair built from
`host/native/build-dtn.lisp` as the image runbook builds them).
[`tools/farm.py`](../tools/farm.py) moves a wide run to persvati or hbox:
`submit` mirrors the worktree and starts the runner detached with its own log
and status file, `wait` blocks with a bounded sleep-and-report loop and then
rsyncs back the evidence directory and the new pairs and publishes them
locally and on the box, and `status` lists the runs on a host. `--cache` names
the cache to use ON THE HOST; `submit` records it and `wait` reuses what was
recorded, which is how a measurement of the cache isolates itself from the
shared one. On hbox the runner is wrapped
in `swarm-build`, which is where that box's memory cap is enforced. A submit
with plain roots or `--affected-by` is incremental: the preflight runs
`install-partial` over the selected roots, prints how many books installed
and how many are left to certify, never refuses for a miss, and the runner
gets `--incremental` (under `--affected-by` the affected books are uncached
by construction, so it certifies them and whatever else the cache lacks).
`--require-origin ORIGIN` is the explicit demand for one complete dependency
set from one origin and refuses otherwise; `--closure` stays root's
from-scratch recertification (purge on a miss, certify the whole closure).
`--recertify BOOK` (repeatable, passed to both the preflight and the runner)
keeps a cached book out of the install so the run certifies it and its
manifest records its digest, which is how a book that every run installs and
no archived manifest certifies gets evidence `certified_claims.py` accepts.
The invocation for a lane is

    python3 tools/farm.py submit persvati --jobs 12 \
        --remote-root /home/ember/fn-lanes/<lane> \
        --affected-by books/article.lisp

and four things in it were each paid for by a run that produced nothing.
`--remote-root` takes an **absolute** path: a leading `~` is resolved against
the host's own `$HOME` in one `ssh host 'echo $HOME'` before anything uses it,
because the recorded path is also the origin the returning pairs are published
under and a certificate's post-alist names its sub-books absolutely --
`shlex.quote` had been making the tilde literal, so the remote `cd` landed
nowhere. rsync creates the last component of its destination and no more, so
`submit` makes the path first. And `cd X && ... &` backgrounds the whole list,
which meant ssh exited 0 whatever happened; each step of the submit script now
exits on its own (9 no directory, 10 no runner in the tree, 11 no writable
`build/farm`, 12 the runner did not start), `submit` raises on any of them and
`main` returns 2, so a run id is printed only for a run that exists. Fourth,
`wait` returning 3 at its deadline without fetching abandoned every pair the
run had already made, while the run itself kept going on the box; the timeout
path now fetches and publishes first and prints what it left behind.

Every harness that writes a record -- [`tools/deploy_gate.py`](../tools/deploy_gate.py),
`twonode_gate.py`, `inn_lab.py`, `scale_gate.py`, `verdict.py`,
`tcpcl_lab.py` and `tests/campaign/campaign.py` -- resolves the tree it
writes into with `deploy_gate.repo_root()`, which is `git rev-parse
--show-toplevel` from the working directory, checked to be an fn tree and
falling back to the harness file's own tree. `Path(__file__).parents[1]`
answers where the SCRIPT lives, which is a different question: a lane running
the main checkout's copy of a harness had `planning/evidence/twonode-*.md`
written into `/Users/ember/dev/fn`, untracked, blocking a merge.
`deploy_gate.evidence_path()` anchors the default name and a relative
`--evidence` on that root; an absolute `--evidence` is still taken as given,
and `--repo` still overrides.

### What a harness verdict means

A step's exit code is not a scenario's conclusion, and until 2026-09-20 the
gate family had no way to say so: every scenario assertion appended a sentence
to a `gaps` list, the exit read only `Step.failed`, and a probe declared
`expect=None` could not be failed at all. The two-node gate could therefore
watch an article fail to arrive after a cut connection, record two accepted
transfers where at most one is allowed, or read the wrong final group count,
and exit 0 -- the headline "63 steps, 0 failed" structurally could not include
a violated scenario assertion
([the follow-up review](../planning/review-2026-09-20-astra-followup.md), F1).

`tools/deploy_gate.py` now carries a `Finding` beside the `Step`, with the
vocabulary [`tools/v0_matrix.py`](../tools/v0_matrix.py) already keeps apart
over its rows: a fixed set of words never collapsed into pass/fail, a declared
inventory (`ASSERTIONS`) so an assertion the run never reached is emitted
rather than lost, one emitter that refuses an undeclared key or an undecided
verdict with no blocker, and a sha256 over the records in
`<evidence>.findings.json` so a verdict cannot be typed in afterwards. A
v0_matrix row is an OBSERVATION of a feature and `accepted`/`refused`/
`uncertain` are D13's outcomes; a finding is a CONCLUSION about an assertion,
so its two deciding words are `held` and `violated` and D13's outcomes stay in
the steps' expected exit codes.

| verdict | what it says | effect on the exit |
| --- | --- | --- |
| `held` | the assertion was decided and is true | none |
| `violated` | the assertion was decided and is false | exit 1 |
| `inconclusive` | the run meant to decide it and could not | exit 3 |
| `not-exercised` | the run did not reach it; `blocker` says why | none |
| `not-built` | the feature it is about is not on this tree | none |
| `limitation` | a scope boundary no run of this harness crosses | none |

The line between `inconclusive` and `limitation` is the one that keeps the
fix from being indiscriminate: a postpublish fault is indeterminate by
construction (D13) and no run can decide it, so it is a limitation and reports
without failing; a tap that never took its cut, a GROUP reply with no count,
or an offer command no recorder saw is a defect in THAT run, establishes
nothing, and must not stand behind a release claim. Exit 3 is D13's uncertain,
and `tools/verdict.py` carries it out as a fourth fiber state rather than
folding it into `fail` or `pass`. `tests/test_gate_verdicts.py` injects each
bad outcome into the real scenario methods and requires the failed assertion
and the nonzero exit.

### Reaping gate directories, and reading a box's memory

A gate is a `git archive` export plus the certificates it earned, at
`$HOME/fn-gates/<tree>-<rev>` on persvati and `/tank/fn/gates/<tree>-<rev>`
on hbox, and nothing ever removed one: on 2026-09-21 persvati carried 25 of
them over 1.1 G. A retired gate also does not take its processes with it --
three ACL2 children of the retired `dev-6ac2278` survived 19 hours at 0% CPU
holding 1.7 G.

[`tools/gate_reap.py`](../tools/gate_reap.py) lists every gate on a box with
its revision, its age, its on-disk size, how many `.cert` files it holds,
whether that revision is still an ancestor of `dev` (asked of the
repository, since a gate carries no `.git`) and whether any process on the
box has it or anything under it as its working directory. `--remove` deletes
only the rows it called `stale`, by a name that came back from its own
listing. Four things are never removed: a gate with a process in it; any
gate at all while the box's `flock` is held, because that means a
certification is running; the newest `--keep-recent` gates of each tree,
which is what a deploy scavenges pairs from; and a gate whose revision git
does not know, because that export may be the only copy of that tree. A box
with no `/proc` keeps everything, since "I could not check" must not read
the same as "nothing is running". First run, persvati: 12 of 25 removed,
475 M, no live gate and the six newest `dev` gates untouched.

**Do not judge a box by `free`.** hbox is a ZFS box: the ARC is counted in
`used` and in unreclaimable slab and never in `buff/cache`, so `available`
under-reports by tens of gigabytes and a lane reading it concludes the box
is full when it is idle. Measured 2026-09-21 on hbox: `Slab` 87.0 G with
`SUnreclaim` 82.3 G, `AnonPages` 2.4 G, RSS summed over every process 3.5 G,
ARC 44.7 G, on a 123 G box with 24 near-idle CPUs. `gate_reap.py` prints
`AnonPages`, the RSS sum and the ARC separately for exactly this reason;
judge the box by the first two.

### Qualifying a platform against A-DURABILITY

[`books/assumptions.lisp`](../books/assumptions.lisp) introduces each named
assumption from [the failure model](../specs/failures.md) as an `encapsulate`
with a local witness. A-CRYPTO is not among them: `books/crypto-seam.lisp`
owns the digest and signature seam, and a second constrained crypto function
would be a twin.

A platform qualification discharges A-DURABILITY like this. Write a concrete
function, say `qual-apfs-image`, that models what the qualified device,
filesystem and barrier call actually preserve across a power cut, in the terms
the profile measured. Prove the two constraints about it:
`(implies (member-equal record barriered) (member-equal record (qual-apfs-image barriered unbarriered)))`
and the no-invention constraint. Then every theorem that took A-DURABILITY as a
hypothesis transfers to that platform by
`(:functional-instance <theorem> (fn-assume-durability-image qual-apfs-image))`,
and the transfer is checked by ACL2 rather than asserted in prose. The
qualification's scope — OS, filesystem, device, write unit, barrier call, and
the fault tests performed — is recorded with the profile, and the functional
instance is what ties that scope to the theorems.

The encapsulates state the assumptions; they do not yet apply them. No theorem
in the tree takes one as a hypothesis today. Each constraint carries a comment
naming the theorems that should, which is the C1-14 and C1-15 work.

## Registry states

Requirements: `specified`, `implemented`, `validated`, or `deferred`.
Proof targets: `planned`, `uncertified-at-current-digest` or `certified`, and
the proof target's `status` is generated, never typed: `python3 tools/ledger.py
--write` derives it and `make check` (through `ledger.py --check`) refuses a
hand-edited value. `planned` means the target cites no event; `certified` means
a manifest the row cites under `planning/evidence/manifests/` recorded every
event's defining book passed at its current source digest and include closure
(the rule `tools/certified_claims.py` applies); anything else is
`uncertified-at-current-digest`. Editing a book therefore turns its targets
uncertified until the lane harvests and cites the run that certified the new
bytes. The status speaks for the cited events, not for everything the target's
statement says.

Implemented/validated requirements and certified proof targets require evidence
paths. A proof's evidence must name actual events/books, exact ACL2/Lisp versions,
command, input revision or content digest, result, assumptions, and limitations.
The scaffold checker checks references/status consistency; it cannot certify a
theorem by inspecting an evidence file.

A proof target's `events` array in [the proof registry](../planning/proofs.json)
is generated. It is regenerated from
[`planning/proof-events.json`](../planning/proof-events.json), the curated map
from target to supporting events, which is the only hand-edited half of the
ledger. A name there must exist, must not be flagged by the suspect detector,
and must live in a book a Makefile certification root reaches. Where a cited
theorem is about a function the host does not call, the entry carries a
`pending_subject` note saying so; the citation stands as component evidence and
does not meet the subject rule until a theorem equates the two functions.

Store generated logs under `build/` and durable human-reviewable evidence summaries
in versioned files as implementation arrives. Do not commit a placeholder proof
log or create a `certify` command that passes without running ACL2.
