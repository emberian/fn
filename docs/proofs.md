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

### The two export lints

Besides the suspect detector, `tools/ledger.py` reports two WARN lints, counted
in the generated ledger and listed in full under `lints` in `ledger.json`.
Neither judges truth; each names a cost this tree has already paid.
*Export hygiene* flags a theorem a book leaves enabled whose conclusion is an
equality between two *different* one-argument applications, or a `consp`/`len`
conclusion backchained to a `len` hypothesis. The same accessor on both sides
is a preservation lemma, which is the shape the export policy asks for, and is
not flagged; `local`, `defthmd`, `:rule-classes nil` and a non-local closing
`in-theory (disable ...)` each exempt a rule, because none of them leaves it
enabled downstream. *Teeth form* flags a `must-fail` whose body is a bare
`thm`/`defthm` whose statement mentions no constant -- no keyword, literal,
string or `defconst` -- so it refutes a general claim rather than a specific
violating value. `make check` prints both as `WARN`;
`python3 tools/ledger.py --check --strict` fails on them, which is how a book
or a cluster that has been cleaned keeps its state.

### Certificates, the cache, and the farm

Every fn tool that starts ACL2 sets `ACL2_BOOK_HASH_ALISTP=NIL`, so ACL2 8.7
hashes book *contents* rather than write dates and absolute paths: a
`.cert`/`.port` pair is valid in any worktree and on any host whose book
content matches. [`tools/certs.py`](../tools/certs.py) is the consequence.
`publish` stores each valid-looking pair under the SHA-256 of its book's
content (and, below that, the book's own name, so two books with identical
bytes never share one entry); `install` copies into a worktree every pair whose
key matches a book there, never over a local certificate that already matches
its book and is no older than the cached one; `status` prints coverage.
`tools/certify_books.py` publishes automatically after a passing run, which
`--no-publish` suppresses, and `make certs-install` / `make certs-publish` are
the manual ends. What this does not establish: the cache cannot tell that a
pair describes the book beside it, only that the book hashes to the key. The
certification gate is unchanged -- a fresh success marker and a certificate per
requested book, from `tools/certify_books.py`.

Two further controls on ACL2 processes. `--affected-by BOOK` keeps only the
requested roots that are, or transitively include, a named book, in the
requested (Makefile) order, so a change certifies what it can have invalidated
and nothing else; `--dry-run` prints that list. Every ACL2 this project starts
first takes a slot from a machine-wide pool of `flock` files
([`tools/acl2_slots.py`](../tools/acl2_slots.py), `FN_ACL2_SLOTS`, default 4 on
darwin and 16 on linux), waits rather than starting when the pool is full,
reports the wait once a minute, and records each wait in the run manifest. The
lock lives on the open file description, so a killed run leaks no slot.
[`tools/farm.py`](../tools/farm.py) moves a wide run to persvati or hbox:
`submit` mirrors the worktree to the same absolute path and starts the runner
detached with its own log and status file, `wait` blocks with a bounded
sleep-and-report loop and then rsyncs back the evidence directory and the new
pairs and publishes them locally, and `status` lists the runs on a host. On
hbox the runner is wrapped in `swarm-build`, which is where that box's memory
cap is enforced.

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
