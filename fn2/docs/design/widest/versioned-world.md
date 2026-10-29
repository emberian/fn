# fn2 from the vantage of the versioned executable world (council draft, 2026-10-28)

One voice of the widest-role council (brief: `briefs/WIDEST-ROLE-20261028.md`). Vantage: fn2 as the persistent semantic image in which programs, their revisions, their live state, their suspended computations and their execution history are one enduring object with a verified history and a crash model.

## 1. The world from this vantage

fn2 is an **image**. It is not a Smalltalk heap dumped to disk; ember already ruled that out ("log as truth, snapshot a cache of its fold, no SBCL core snapshots", EMBER-ARCHITECTURE-WORDS §13). It is an image in Faré's Houyhnhnm sense: the durable thing is the whole computational world, and persistence is orthogonal because nobody serializes anything ("this serde shit is NOT houyhnhnm computing"). The world has two axes. The **history axis** is the journal fn2 already designs: commit positions, events decided in order, folds over them. The **revision axis** is new: the code and schemas that decide and interpret those events. These are content-named definitions (Unison-style hashes of syntax with hashed dependencies), gathered into **revisions**, and a commit domain moves from one revision to the next only through an event in its own journal. Every point in the world is a pair `(revision, position)`. Every fact fn2 tells anyone is stamped with both.

Five transitions act on the world. Each is a checked event in the journal, never a side channel:

- **execute**: Decide at the head under the domain's current revision `r`. The event records `r` (Julia's world age: the code that ran is the code that was current when the step began).
- **edit**: a `define` event adds definitions by Name. It changes nothing that runs until it is adopted.
- **migrate**: an `adopt` event moves the domain from `r1` to `r2` at position `p`. It carries a **migration**: a state transfer for every fold and suspended machine whose definition changed, a declared relation between old and new states, and evidence that the relation holds. The evidence is a replay certificate, the per-event-kind homomorphism equations UNIVERSAL-CONSTRUCTIONS §2.2 already names, or a named waiver.
- **materialize**: a fold `f@r2` is computed over existing history up to a frontier, under the maintenance class, with its own coverage. Readers at `r1` keep reading `f@r1` until their pins end.
- **fork**: a child domain opens on a parent cut `(r, p)` under an effect policy. Its external effects become held obligations. Nothing it does reaches the parent except through **promote**, which is a separate Decide on the parent that re-decides named commands or adopts a named revision there.

**A Tuesday.** A helm maintainer changes how owed replies expire. She edits the `dispatch` fold and its Decide rule on her laptop against a fork of the production rooms domain, opened at yesterday's cut. The fork re-executes the last week of recorded commands under her revision inside fn2's deterministic simulator, which is the same code as the executor (EXEC rule 10). It returns a **behavioural diff**: 41 replies that expired under the old revision would stay owed under hers, listed by operation identity with the events responsible. She attaches the diff to a `promote` command. The production node checks the migration's certificate for the two event kinds whose interpretation changed, then commits `adopt(r7→r8, @p)` in one batch. Seats pinned at `r7` keep their views until they re-pin. The dispatch fold at `r8` materializes behind a frontier. A wait parked under `r7` either finishes at `r7`, because the old revision is retained while that continuation holds it, or is moved by the transfer function at its next update point (Kitsune's update points, Erlang's `code_change`).

The same afternoon a game designer forks an RTS ladder at last season's end and replays every recorded match input under a balance patch. He gets "would the ladder have come out differently" as a fold over the fork. He discards the fork. Its held effects are dropped with it, and that is recorded.

**On the wire**: events carry `(domain, position, revision-name)`. Definitions travel as content-named objects with dependency closures, using the have/want exchange Unison's codebase sync and git packs both use, over the same NNTP/BP peering that carries articles. A peer that receives an event under a revision it lacks fetches that revision by Name before it folds. **Durable**: the journal, definitions, migrations with their evidence, checkpoint claims that now also commit to the revision, held fork effects. **Live**: running machines, parked continuations, materialized folds (caches by law L2). **Fast**: interpretation compiled from definitions, keyed by definition hash so a revision change recompiles only what changed. **Across nodes**: revisions, events and signed observations, never heaps.

## 2. Ten things it would build or subsume

1. **Schema migrations** (Flyway, Liquibase, Rails/Django migrations, Postgres `ALTER TABLE`). A migration is an event with a declared relation and checked evidence, run online behind a frontier while old readers stay pinned. Users switch because "the migration ran halfway and the deploy died" becomes a recovery state with a frontier, and the old shape stays readable without a dump.
2. **Event-sourcing upcasters** (Axon upcasters, EventStoreDB/Marten versioned events, Greg Young's *Versioning in an Event Sourced System*). Old events are never rewritten. They are interpreted by the fold of the revision reading them, and an upcaster is the event-kind part of a migration. Users switch because upcaster chains become a composed and checked morphism instead of a pile of hand-ordered functions nobody can test against all of history.
3. **Dynamic software update of fn2 itself and of hosted machines** (Kitsune, Ginseng, Erlang/OTP hot code loading, Theseus OS's live evolution). Code load is a journal event. State transfer is a declared function with a checked relation. Update points are machine-DSL annotations, and EXEC's bounded continuations already make every machine quiescent between quanta. Erlang users switch because `code_change` gains a recorded, replayable, crash-safe history, and the two-versions-max rule becomes "as many as pinned continuations hold".
4. **The Smalltalk/Lisp image** (Pharo, Squeak's `.changes` file and Monticello, Self, Interlisp). Pharo's `.changes` file is already an operation log beside a heap snapshot. fn2 makes the log the truth and the snapshot a fold, signed and replicable. Smalltalkers switch because the image becomes shareable, mergeable by operation, and survives a crash during save.
5. **A Unison-style codebase** (Unison UCM, Nix store, IPFS-linked code). Definitions are Names, human names are a Binding (two definitions claiming one name is `conflicted`, which is Unison's name-conflict state exactly), and the codebase replicates over peering. Unison users switch because the codebase and the data its code produced live in one witnessed log, so "which version of `f` produced this value" has an answer.
6. **Git for data** (Dolt, lakeFS, Neon branching, Datomic `as-of`, Noms, TerminusDB). A fork is a child domain on a parent cut sharing pages copy-on-write. Promotion re-decides operations under the target's Decide. It does not three-way merge states, which follows the operation-based merging line (Lippe and van Oosterom 1992) and Darcs/Pijul patch theory. Dolt users switch because a merge of operations reports a refused command as a refused command, where a merge of states can produce a row no operation would have produced.
7. **Notebooks and live programming** (Jupyter, Observable, Hazel's live evaluation with typed holes, Elm's time-travel debugger, Bret Victor's demos). Cells are definitions. Outputs are observations stamped `(revision, position)`. Staleness is a computed fact (this output's revision is not the cell's current one), not a guess. Jupyter users switch because hidden state becomes impossible: every output names the revision and history it came from.
8. **Durable execution** (Temporal, Restate, Azure Durable Functions, AWS Step Functions). A workflow is a suspended machine whose frame is a fold value at a named revision and whose awaited conditions are frontiers and obligations. Temporal's versioning ceremony (`GetVersion`, `patched`, non-determinism errors on replay) becomes world age plus a declared transfer. Temporal users switch because upgrading a workflow with ten thousand in-flight executions stops being the hardest thing in their system.
9. **Incremental build and computation** (Bazel, Nix derivations, Salsa/rust-analyzer, Adapton, Build Systems à la Carte). A derived value is keyed by `(definition hash, input names)`, its trace is the journal, and reuse across revisions follows from unchanged definition hashes. Bazel users switch because remote cache entries become signed observations whose recorded effects can be audited, not trusted.
10. **Replay and time-travel debugging** (rr, Pernosco, Redux DevTools, UndoDB). The production history is a deterministic-simulator trace, because EXEC's clock, entropy and I/O completions are already observations in the journal. So "replay last Tuesday" is a fork, and "replay last Tuesday under the fix" is a fork at a new revision. rr users switch because rr can replay a process but cannot replay it under different code, and fn2 can.

## 3. What the kernel must contain

The pruned kernel (Log, Decide, Fold, Name; Binding, Span, Frontier, Obligation) describes **one revision forever**. It has no axis for code. Each of the ten above would bolt a versioning scheme onto it, and the ten schemes would not compose. Here is what must be added, and what the eight must become.

**A new irreducible: Revision.** A revision is a content-named closed bundle: event kinds and their schemas, Decide rules, fold definitions, machine definitions with update points, protocol tables (UC §6.2), projection declarations. It is a Name with a **closure law**: every definition it references is in it or is named by hash, and a node may not fold an event whose revision closure it cannot resolve. This extends UC §5.6's "durable dependencies inline or name" from data to code. Human names over revisions and definitions are a Binding.

**A new irreducible: Migration.** A migration is a morphism `m : r1 → r2`, carried as a record with:
- `transfer`, per changed fold and machine kind;
- `relation R`, between `r1` and `r2` states;
- the **declared observations** `O`, together with which ones change on purpose;
- `evidence`: a replay certificate over a stated range, UC §2.2's per-event-kind homomorphism equations, a functorial schema map (Spivak's Σ/Δ/Π, as in CQL) when the change is purely schematic, or a waiver naming its author.

Migrations compose, and evidence composes with them. A migration whose relation is an equivalence on `O` lets everything stated over `O` **transport along it**: projections, indexes, proofs, client pins. This is the concrete place where ember's "transport along equivalences" acts on fn2. When the relation is weaker than an equivalence, observations outside its preserved fragment are re-validated, and the re-validation is recorded.

**What the eight become:**
- **Log becomes a World.** It is a forest of per-domain logs with parent cuts (forks). Each event is stamped with the revision it was decided under. `adopt`, `define`, `fork` and `promote` are record kinds. Positions gain a revision component, and law L5 extends: a revision is a fifth position type, never mixed with commit positions, live sequences, ticks or time domains.
- **Decide becomes Decide@r.** Commands name the revision they were authored against, beside UC's expected-prior-version binding. If the head revision has moved, Decide re-validates under the new one or refuses with `revision-moved`. **History is never re-decided by a new revision.** Past outcomes are facts. Only folds re-interpret them.
- **Fold becomes a family `f@r` indexed by revision.** Its value at `(r, p)` is `f@r` over the events up to `p`. Migrations connect members of the family. A fold whose definition hash did not change across `r1 → r2` is shared, not recomputed.
- **Name gains dependency closure** and definition hashing over syntax with normalized dependencies. The hash still refutes and never decides (UC §4.1).
- **Binding** carries name-to-definition and stays as is.
- **Span** gains the revision as an index dimension where a schema change touches the span. Otherwise it is unchanged.
- **Frontier becomes per revision.** `cov(f@r)` is distinct from `cov(f@r')`. Migration progress is a frontier. A read names `(r, at-least p)` or `(r, exactly-at p)`.
- **Obligation gains effect classes**: pure, recorded (the observation is in the journal), idempotent-external (carries operation identity), external. In a fork every external obligation is **held**. A real adapter can never discharge it. Promotion may re-issue it on the parent under the parent's Decide, as a new obligation.

**New record kinds**: `define`, `adopt(r1→r2, migration, @p)`, `materialize(f@r, cov, digest)`, `fork(child, parent-cut, effect-policy)`, `promote(from-fork, what, evidence)`, `discard(fork)`, `suspend(machine, revision, frame-name, awaiting)`, `observe(query, (r,p), result-digest)`. The last is a read recorded as evidence, so an observation stays a true statement about `(r, p)` forever.

**A new first-class value: Continuation.** A suspended machine is durable: `(revision, frame as a fold value, awaited frontier or obligation, upgrade policy)`. The upgrade policy is `pinned-age` (finish under the old revision, retained by an Obligation) or `transfer-at-update-point`. EXEC already makes every machine a resumable row with bounded continuations. This makes the row's code identity part of its state.

**Laws**:
1. **Interpretation**: `state(r, p) = f@r(events ≤ p)`, where each event's outcome was taken under its own stamped revision.
2. **Observation permanence**: an observation stamped `(r, p)` is never silently re-interpreted under another revision.
3. **Fork isolation**: no external effect and no state crosses from a fork except through `promote`.
4. **Revision retention**: a revision is reclaimable only when no continuation, pin, unmigrated fold or unresolved peer reference holds it. This is reclamation evidence in STORAGE's sense.
5. **Atomic adoption**: `adopt` installs in one commit batch with the transfers of every resident machine that must move at that position. A crash recovers either before it or after it, with materializations resuming from their frontiers.
6. **Migration coherence**: composite evidence certifies the composite migration, and a waiver is never upgraded to a certificate by composition.

**DSL forms**: `defrevision`; `defmigration :from :to :transfer :relation :observations :evidence`; `defmachine ... :update-points :upgrade-policy`; `defprojection ... :revision`; `fork`/`promote` as consumer-protocol verbs with wire fixtures.

## 4. The one capability that would make it epic

**Counterfactual replay over production history, with a witnessed behavioural diff as the promotion evidence.** Pick any past cut and any candidate revision. fn2 forks the world there and re-executes the *recorded commands*, not the recorded states, under the new revision in its deterministic simulator. It holds every external effect as an obligation. Then it returns a signed difference certificate: for every recorded observation and every outcome keyed by operation identity, either "the same", or "different: here is the new value and the events that made it differ". The certificate is the evidence a `promote` carries, and the production node re-checks it cheaply against its own journal digest.

No existing system offers this:
- Temporal replays only to detect non-determinism.
- rr replays a process but cannot change its code.
- Dolt diffs data, not behaviour.
- Erlang upgrades code with no record of what the new code would have done.

fn2 can, because its own choices already make production a simulator trace. EXEC rule 10 makes deterministic simulation the primary test. EXEC rule 4 means wall time never selects work. Clock, entropy and completions are observations in the journal. Operation identities give diff rows stable keys. A builder starts with five steps:
1. Make `fork` a domain id plus a parent cut over shared pages.
2. Run `fn2-reference-turn` from the parent's checkpoint over the parent's journal suffix with Decide@r'.
3. Route every outbox action to a held-obligation table.
4. Emit a fold that zips the parent's outcomes and observations with the fork's, keyed by operation identity.
5. Sign the zipped result as a checkpoint-claim-shaped record.

The first demonstration is the helm dispatch-expiry change from §1, on a week of real rooms.

## 5. What it must never do

It must never let a new revision re-decide the past. History's outcomes are facts that were decided under the code current at the time, and a revision change re-interprets them through folds and migrations, never by rewriting them. It must never let a fork's effects or state reach the parent or the outside world except through an explicit, attributed `promote` that is decided again on the parent. It must never load, patch or activate code by any path that is not a durable, replayable, signed event in the journal, because an out-of-band hot patch is exactly the hidden state this vantage exists to abolish.
