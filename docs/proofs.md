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
three things distinct in the [closure inventory](../planning/assurance-closure.md):
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

### The three shape lints

Besides the suspect detector, `tools/ledger.py` reports three WARN lints,
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
theory here to read. `make check` prints all three as `WARN`;
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
the entry's metadata. A third rule decides *where* a pair may be installed. An ACL2
certificate's post-alist names every sub-book by its **absolute**
full-book-name, so a pair made in worktree X and installed in worktree Y on
one machine makes Y include X's books -- X's paths still resolve -- and Y's
own later certificates then conflict with them (`its certificate requires
.../X/books/acceptance.lisp, but .../Y/books/acceptance.lisp has been
included`). Each entry therefore records the `origin_root` it was produced in,
taken from its manifest's evidence path, and `install` takes this worktree's
own entry, else one whose origin does not exist on this machine, and otherwise
refuses and reports `foreign-local`. A pair whose bytes match a refused entry
is removed, so a worktree an earlier origin-blind install poisoned recovers.
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
([`tools/acl2_slots.py`](../tools/acl2_slots.py), `FN_ACL2_SLOTS`, default 4 on
darwin and 16 on linux), waits rather than starting when the pool is full,
reports the wait once a minute, and records each wait in the run manifest. The
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
[`tools/farm.py`](../tools/farm.py) moves a wide run to persvati or hbox:
`submit` mirrors the worktree and starts the runner detached with its own log
and status file, `wait` blocks with a bounded sleep-and-report loop and then
rsyncs back the evidence directory and the new pairs and publishes them
locally, and `status` lists the runs on a host. On hbox the runner is wrapped
in `swarm-build`, which is where that box's memory cap is enforced. The
invocation for a lane is

    python3 tools/farm.py submit persvati --jobs 12 \
        --remote-root /home/ember/fn-lanes/<lane> \
        --affected-by books/article.lisp --closure

and three things in it were each paid for by a run that produced nothing.
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
`main` returns 2, so a run id is printed only for a run that exists.

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
Proof targets: `planned`, `in-progress`, `certified`, or `deferred`.

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
