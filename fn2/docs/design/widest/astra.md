Vantage: **The instrument of collective inquiry — fn2 as the shared apparatus through which people discover what is happening, test explanations, and act together.**

## 1. The world from this vantage

fn2 becomes the infrastructure of a civilization that can revise its understanding without losing its memory. Laboratories, workshops, communities, software projects, and ecological observatories use it to connect observations to interpretations, interpretations to decisions, and decisions to their consequences. Its central object is an inquiry that remains alive: new evidence can change its answers, alternative explanations can coexist, and someone arriving years later can recover what justified an action.

On Tuesday morning, a watershed cooperative sees an unexpected temperature rise downstream. Volunteers carry intermittent sensors; a university runs laboratory assays; a municipal operator controls discharge equipment; residents contribute photographs and reports. Their instruments, notebooks, discussion rooms, simulations, and public dashboard share fn2 streams. Nobody first assembles a master database or appoints one institution the owner of every observation.

A sensor publishes transient readings while a volunteer adjusts its position. The sampling protocol commits selected windows, their calibration references, and the instrument’s reported clock uncertainty. A scientist circles an anomaly on a live chart; completing the annotation commits its geometry against an exact dataset selection. A laboratory result arrives tomorrow and joins today’s discussion without acquiring today’s timestamp or pretending its meaning was available today.

On the wire are bounded envelopes carrying an occurrence identity, a schema identity, a source, temporal coordinates, a durability class, and references to content and dependencies. Large arrays travel as content-named blocks with range verification. A subscription interweaves durable observations, provisional annotations, instrument presence, and explicitly reported gaps. Across node boundaries travel portable observations, interpretation declarations, selected evidence, and receipts; local article numbers and physical storage addresses stay local.

The durable state includes measurements selected for retention, calibration histories, protocols, analysis declarations, claims, challenges, decisions, and the evidence supporting them. Live state includes cursors, instrument previews, provisional estimates, and collaborative gestures. Fast numerical solvers and control loops run externally, opening pinned inputs and publishing named results through the same interfaces. The node performs bounded scheduling, storage, selection, and evidence checking; it never places a fluid simulation inside the commit machine.

At noon, a calibration error is discovered. The original readings remain records of what the instrument emitted. Their interpretation changes. Every affected graph, report, and proposed intervention gains an explicit status: recalculation pending, recomputed, challenged, or dependent on unavailable material. A policy can suspend an action that required the old interpretation, while preserving the fact that an earlier action was authorized under it.

This is the widest role because the same structure supports engineering diagnosis, public deliberation, experimental science, collaborative design, and everyday organizational memory. “Why did we decide that?” becomes a served query with a precise scope. “What would change our minds?” becomes an executable subscription. “Can we reproduce your result?” becomes a portable computation request whose inputs, assumptions, and missing pieces have names.

The intellectual lineage includes Engelbart’s *Augmenting Human Intellect*, de Kleer’s *An Assumption-Based TMS*, and Green, Karvounarakis, and Tannen’s *Provenance Semirings*. fn2 gives their concerns a common operational home: persistent, incremental, collaborative inquiry with explicit authority and failure semantics.

## 2. Ten things it would build or subsume

1. **A living laboratory notebook.** It composes with Jupyter and replaces the disconnected recordkeeping around notebooks with durable links among an executed cell, its exact inputs, instrument conditions, outputs, and subsequent corrections. Researchers keep their numerical tools while gaining results that remain interpretable after collaborators, dependencies, and datasets change.

2. **An observatory spanning disconnected instruments.** It composes with MQTT and replaces bespoke bridges between telemetry, TimescaleDB, and experiment archives with streams whose individual samples carry declared durability and observation context. Operators gain continuous previews, deliberate capture, delay-tolerant exchange, and visible sampling gaps through one consumer model.

3. **A reproducible analysis exchange.** It composes with Nix, DVC, and scientific workflow engines by making an analysis a portable declaration over named inputs, environments, and expected outputs. Users retain specialized execution backends while exchanging results with checkable dependency closures and explicit distinctions between rerunnable, independently checked, and merely attested work.

4. **A collaborative geographic evidence atlas.** It composes with QGIS and PostGIS, joining map features to observations, coordinate transformations, competing classifications, and the decisions that used them. GIS users retain spatial algorithms while gaining maps whose disagreements and revisions remain navigable instead of disappearing into exported layers.

5. **An engineering incident laboratory.** It composes with OpenTelemetry and Grafana, connecting traces, deployments, hypotheses, reproductions, and corrective actions through a persistent inquiry graph. Engineers gain a direct path from an alert to the evidence that refuted a diagnosis and the experiment that established the replacement.

6. **A public deliberation workspace.** It composes with Discourse and Decidim, attaching proposals to evidence selections, explicit assumptions, objections, and recorded decision procedures. Communities keep discussion and voting interfaces while gaining proposals that visibly respond to changed evidence without rewriting the historical record.

7. **A durable machine-learning evaluation commons.** It composes with MLflow and Weights & Biases, representing evaluations as declared selections, scoring interpretations, execution records, and claims with named applicability. Researchers gain comparisons that expose changed test populations, contaminated inputs, and revised metrics instead of silently placing incomparable scores on one leaderboard.

8. **A design studio with accountable simulation.** It composes with FreeCAD and OpenModelica, connecting geometry, material measurements, boundary conditions, simulation outputs, and physical tests. Designers keep their modeling environments while gaining automatic identification of which conclusions survive a changed component or corrected material property.

9. **An organizational memory that answers challenges.** It composes with Obsidian and replaces the evidence scattered across Notion pages and chat archives with claims linked to decisions, sources, owners, and reconsideration conditions. Teams keep familiar writing surfaces while recovering both what they believed and what would require them to revisit it.

10. **An executable publication system.** It composes with Quarto and institutional repositories, publishing an article together with selectable evidence, analysis declarations, challenges, and continuing result streams. Authors and readers gain publications that support replication and correction while preserving the exact historical edition someone cited.

## 3. What the kernel must contain

The eight interfaces are expressive enough to encode these applications as bytes. That is insufficient: applications must share the meanings that make evidence portable, corrections composable, and conclusions inspectable. The expansion belongs in semantic declarations and generated machines, backed by the existing executor and storage design.

**Log becomes a journal of occurrences with explicit observational context.** Each event distinguishes when something was observed, when its source says it occurred, when it entered this domain, and the interval over which an interpretation applies. None of these coordinates substitutes for another. Instrument time can be an interval with a declared uncertainty; commit position remains exact within its domain. Event kinds include observation, interpretation, derivation, challenge, correction, decision, and effect receipt. Correcting an interpretation appends a relationship; it does not alter the original occurrence.

**Decide becomes the admission and adoption boundary for inquiry.** It distinguishes storing someone’s assertion, checking a derivation, accepting a result under a policy, and authorizing action. A signature establishes attributed authorship under declared assumptions; a successful checker establishes its named proposition; neither establishes an empirical claim merely because it was committed. Commands name the evidence cut and interpretation versions on which they depend. If a required premise changes before adoption, the command receives a defined outcome or enters a declared reevaluation protocol.

**Fold becomes an incremental interpretation with an explanation interface.** Its declaration includes sources, interpretation identity, dependency semantics, maintenance mode, retained versions, and available observations of its result. Besides returning a value, it can return the support for that value and the conditions under which it must be reconsidered. DBSP and *Differential Dataflow* supply models for incremental computation; provenance semirings supply models for tracking alternative and joint support. Retraction support is declared explicitly: recording a correction always succeeds according to its own admission rules, while the resulting recomputation proceeds behind a published frontier.

**Name becomes the foundation for typed, portable experimental artifacts.** Content identity remains distinct from occurrence identity and semantic equivalence. Two instruments emitting identical bytes have produced two observations; two arrays in different units can represent equivalent quantities without sharing bytes. Artifacts name their encodings, shapes, units, coordinate systems, environments, and interpretation declarations through explicit manifests. Range proofs let a participant check and consume the required portion of a large artifact without materializing the whole thing.

**Binding becomes contextual attribution and identification.** Its union of validated facts still preserves conflicts, but the keys include the relevant identification scheme and scope. “This sample came from this site,” “this key operated this instrument,” and “these specimen identifiers refer to the same collection” are different bindings with different validation rules. Their acceptance by a laboratory, community, or analysis is recorded separately. This supports competing taxonomies and disputed attribution without turning every disagreement into a global identity collision.

**Span becomes a typed relation with derivation structure.** Ordinary binary indexes remain cheap, but a derived result must also name the joint set of inputs used to obtain it. A derivation record therefore forms a hyperedge from input selections and assumptions to outputs, with role labels such as calibration, boundary condition, observation, and transformation. Dependencies involving absence require a versioned selection and a completeness claim: “no failed samples” cannot be justified by an empty result from an unfinished scan. Reverse indexes make the affected portion of the graph discoverable without traversing the entire store.

**Frontier becomes a family of typed progress statements.** Delivery progress, computation coverage, source completeness, and challenge processing are separate frontiers. Reading every locally available event through position *p* establishes nothing about samples still aboard a disconnected instrument. A closed sampling window therefore needs a source-issued seal or a declared missing-data policy. Results expose the frontiers they actually depend on; an exact historical answer requires retained version state or a sufficient snapshot and replay, preserving the correction in `UNIVERSAL-CONSTRUCTIONS`.

**Obligation becomes the protocol of experimental undertaking.** A sampling request, independent replication, calibration renewal, requested review, or pending external action has an owner, admissible evidence, and explicit completion alternatives. Completing the undertaking is distinct from obtaining a favorable scientific result: a failed replication can fully discharge an obligation. Retention obligations preserve the material needed for promised checks. Physical execution uses operation identities, fencing where supported, and receipts; an ambiguous pump command remains uncertain until evidence resolves it.

These expansions need three shared declaration forms.

`definterpretation` declares a mapping between representations, its domain, preserved observations, and the evidence supporting those preservation claims. Exact unit conversion, lossy resampling, aggregation, and speculative inference are different forms. Transporting a conclusion through a mapping requires the relevant preservation law; a lossy map cannot acquire an inverse by convention. Spivak’s *Functorial Data Migration* supplies a useful vocabulary for schema movement, while the served contract names the actual observations preserved.

`defderivation` declares inputs, selection closure, assumptions, execution environment, output shape, checker, and dependency extraction. Its validity states separate locally checked derivations, externally attested runs, pending checks, and challenged results. Numerical uncertainty belongs to a declared model and method; the kernel supplies no universal confidence score.

`definquiry` declares questions, competing hypotheses, admissible experiments, observation protocols, and conditions for adopting or revisiting a conclusion. Domain libraries supply scientific and institutional policy. The kernel supplies the common transition semantics so that a laboratory’s question and a community’s decision can refer to the same experiment without sharing a worldview.

These forms generate records, indexes, protocol machines, and consumer bindings through the existing DSL architecture. Large dependency traversals and recalculations are pageable, resumable work. Payloads stay in the content store, external solvers stay external, and an unfinished explanation is returned as unfinished rather than truncated into apparent completeness.

## 4. The one capability that would make it epic

**A finding can carry an executable account of what would change it, and that account can remain active across every institution that relies on the finding.**

The experience begins with an ordinary question: “Why does the watershed dashboard recommend opening the bypass?” Selecting the recommendation opens its evidence structure: measurements, calibrations, model revision, operating constraints, adoption policy, and unresolved objections. The user can replace a premise, propose another interpretation, or commission a discriminating measurement. fn2 preserves the differences among those operations and incrementally shows their consequences.

This joins facilities associated with truth-maintenance systems, reproducible workflows, stream processors, collaborative notebooks, and operational command systems into one continuous object. The distinctive capability is the continuity from a live observation through contested interpretation to an authorized action, followed by revision when the world answers back.

A builder starts with six connected mechanisms.

First, introduce an **evidence selection**: a named query, exact source cut, interpretation version, completeness requirements, and retention terms. An analysis consumes this selection rather than “whatever the database currently contains.” A reviewer can request the same selection and receive either its promised material or an explicit account of what is unavailable.

Second, introduce a **derivation receipt** linking that selection to executable code, parameters, environment, output artifacts, and a checker or attestation. The receipt declares what dependency information was captured. Fine-grained dependencies permit narrow recomputation; opaque computations conservatively depend on their whole declared input selection.

Third, build a **support network** whose edges distinguish logical derivation, empirical support, attribution, and policy adoption. Circular references do not manufacture independent support. A challenge to a calibration can traverse calibration-dependent derivations without retracting unrelated observations or erasing a historically valid authorization.

Fourth, provide an **intervention workspace**. A participant substitutes an assumption or proposes a prospective action, and external executors compute the affected results against pinned evidence. The workspace labels outputs as conditional predictions, preserves the model that produced them, and records missing environmental inputs. A dependency graph establishes computational dependence; claims about physical causation require an explicitly supplied causal model.

Fifth, make **experiments ordinary protocols**. A proposed measurement names which competing predictions it addresses, the sampling procedure, required instruments, and completion evidence. Authorized participants claim the work, publish previews, commit observations, and discharge the undertaking. The resulting evidence automatically enters the pending comparisons because the inquiry already names its role.

Sixth, provide an **adoption transaction**. The responsible actor chooses a result under a declared policy, supplies current authority, and commits an intended action with its evidence references. The action crosses into an external effect protocol only after that durable decision. Replaying the analysis never repeats the physical action.

The watershed demonstration runs end to end. Two explanations predict different temperature patterns; volunteers conduct the distinguishing measurement; one instrument later reports a calibration correction; affected analyses recompute; an already completed action remains historical; a pending action is reevaluated; and a second institution can inspect the entire chain using its own acceptance policy.

The decisive tests deliberately interrupt this chain: lose a live sample, deliver a correction late, disconnect a source before its completeness seal, revoke an executor before result adoption, reclaim an unpromised artifact, and crash after an external command but before its receipt. Each interruption produces a precise unresolved state while unrelated inquiries continue.

The resulting object is more powerful than a reproducible report. It is a question that keeps working: attached to instruments, open to disagreement, capable of commissioning its next experiment, and accountable for the actions taken in its name.

## 5. What it must never do

It must never collapse recorded, signed, reproducible, formally checked, empirically supported, and institutionally adopted into a single status called “true.”

It must never make a correction erase the conditions under which an earlier observation, conclusion, or action occurred, or make a replay perform an external action again.

It must never demand universal agreement, unrestricted disclosure, or permanent retention as the price of participation: competing interpretations, selective sharing, and explicit loss must remain usable parts of collective inquiry.