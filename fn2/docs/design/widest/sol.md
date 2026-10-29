# Vantage: Collective inquiry — fn2 as a shared scientific instrument

## 1. The world from this vantage

fn2 becomes the substrate on which people build, test, dispute, and repair their shared understanding of reality. Instruments contribute observations; models contribute predictions; people contribute interpretations; experiments distinguish competing explanations; decisions record which evidence warranted an action. These activities share durable identities, explicit dependencies, scoped authority, and machinery that carries a correction all the way to the people and systems relying on the corrected material.

The unit that matters is an **answer together with the conditions under which someone may rely on it**. Those conditions include the observations used, the transformations applied, the calibration in force, the population sampled, the alternatives excluded, and the limits of what was actually searched. fn2 gives those conditions executable structure.

On Tuesday morning, a watershed cooperative investigates an apparent decline in dissolved oxygen. Buoys publish readings, volunteers upload sample photographs, and a laboratory contributes assay results. Each measurement names its instrument, acquisition procedure, calibration, units, sample identity, and acquisition interval; the node separately records when it received and durably accepted the report. An intermittently connected field station carries signed batches home over BP, preserving the distinction between an observation made yesterday and evidence received today.

A researcher opens a notebook against a pinned evidence collection. The notebook’s plots identify their input cut, transformation revision, exclusions, and completeness frontier. Another researcher explores an alternative sensor-drift explanation against the same collection; their interpretations coexist, with an explicit disagreement over which calibration applies.

During a sampling session, transient readings and annotations move through the same subscriptions as durable sample registrations. A technician selects a suspicious interval for preservation, committing its captured bytes and provenance before the live ring expires. Large images and time series travel as content-named chunks with range verification and object leases; plotting, numerical fitting, and instrument control run in external workers close to the relevant hardware.

At noon, the laboratory discovers a mislabeled reference sample. It publishes a correction binding the affected observations to the new sample identification. fn2 locates dependent datasets, figures, claims, reports, and operational decisions; it opens repair obligations, advances an impact-discovery frontier, and lets each reader see whether their particular answer has been reconsidered.

On the wire are observation manifests, dependency declarations, signed assessments, challenge records, experiment requests, result receipts, and exact references to retained content. Durable state includes what was observed, asserted, authorized, challenged, and undertaken; live state includes instrument previews, collaborator presence, and exploratory gestures. Fast acquisition and numerical execution remain outside the semantic executor, publishing checkpoints and consequences through ordinary authenticated operations.

Across node boundaries travel portable evidence packages, declared methods, scoped attestations, and receipts for accepting responsibility to examine a correction. Institutions retain their own authority and access rules. A laboratory can verify that a published figure used particular bytes under a particular procedure while separately deciding whether the procedure warrants the conclusion.

The widest role is a public and private infrastructure for learning: a common foundation beneath laboratories, engineering investigations, ecological observatories, research communities, and organizations that need their accumulated knowledge to remain usable when something changes.

## 2. Ten things it would build or subsume

1. **A reproducible laboratory notebook, composing with Jupyter and replacing its surrounding provenance scripts.** Researchers keep their interactive calculations while every published result receives an exact evidence cut, environment identity, dependency declaration, and correction subscription, making a collaborator’s “where did this number come from?” an executable query.

2. **An experiment and model registry, subsuming the bookkeeping shared between MLflow and DVC.** Users switch because datasets, training runs, evaluations, deployment decisions, and discovered contamination become one connected history whose corrections reach every dependent assessment without reconciling several registries.

3. **An instrument evidence bus, composing with EPICS and replacing bespoke Kafka-to-archive pipelines.** Instrument operators gain one identity and authorization surface for transient previews, durable acquisitions, calibration changes, and custody receipts, with explicit gaps and preservation chosen per item.

4. **A living research repository, composing with Dataverse and Zenodo.** Depositors retain archival releases while gaining machine-readable derivation, selective replication, challenge handling, and continuing responsibility for corrections after publication.

5. **An electronic laboratory notebook, subsuming eLabFTW’s experiment bookkeeping and integrating its instrument attachments.** Experimentalists gain sample lineage, procedure revisions, scoped signatures, and preserved distinctions between planned, attempted, observed, and accepted steps, including interrupted procedures and disputed labels.

6. **A literature and argument workspace, composing with Zotero and Hypothes.is.** Readers gain addressable claims, quotations bound to source versions, competing interpretations, and evidence subscriptions that reveal when a cited result has been corrected or its supporting material has become unavailable.

7. **An incident investigation system, composing with OpenTelemetry and replacing manually assembled incident timelines.** Operators can preserve selected transient traces, connect hypotheses to exact deployment and telemetry cuts, and carry a revised root-cause finding into the runbooks and changes that relied on it.

8. **An experimentation service, subsuming the assignment and analysis bookkeeping around GrowthBook.** Experiment owners gain durable treatment assignments, versioned eligibility rules, stopping decisions, and explicit interference assumptions, so later analytical corrections can be separated from changes to what participants actually experienced.

9. **A distributed observatory, composing with ODK and iNaturalist.** Field contributors gain offline evidence packages, consent-scoped disclosure, instrument and observer provenance, and visible reconciliation of conflicting identifications while retaining usable local collections during disconnection.

10. **A replication and review exchange, composing with OpenReview and the Open Science Framework.** Reviewers receive executable questions, bounded evidence requests, independently produced witnesses, and tracked responses, making replication a continuing relationship between records and people rather than a supplementary archive nobody watches.

## 3. What the kernel must contain

The pruned kernel describes how records accumulate, choices occur, and views emerge. Collective inquiry requires those operations to expose **why an answer depends on particular evidence, what absence it assumes, what challenges remain, and what responsibility follows a change**. These can share the existing journal, metadata engine, scheduler, and commit protocol, but their contracts must be first-class enough that clients compose them consistently.

**Log must become an evidence history with typed occurrences.** An acquisition, an interpretation, an intervention request, an attempted intervention, and a receipt are distinct record kinds. Every externally occurring event has an occurrence identity independent of its content identity: two identical instrument readings remain two observations, while retransmitting one acquisition remains one occurrence. Acquisition time, receipt position, and declared experimental time are separate types, with clock mappings and uncertainty recorded explicitly.

The interweaving amendment belongs here in full. A transient observation becomes durable through a referencing commit that secures its bytes; a digest of an expired reading establishes no recoverable measurement. Preservation requests therefore reserve capture resources before promising success, and expiration returns a typed failure or partial capture with explicit coverage.

**Decide must become a processor for scoped experimental protocols.** A protocol declaration specifies roles, admissible transitions, required evidence, resource reservations, and observable outcomes. Commands such as `register-sample`, `authorize-acquisition`, `seal-analysis-inputs`, `challenge-calibration`, and `accept-repair` execute against the relevant domain head with operation identities and durable outcome evidence.

An experiment’s physical actions require outbox obligations and external receipts. Replaying an analysis cannot repeat a centrifuge run, send another participant invitation, or acquire another physical sample; each fresh action needs a fresh authorized occurrence. Allocation and randomization likewise record the authorized procedure and required entropy evidence, making later reassessment distinguish analytical change from a different experiment.

**Fold must become a declared derivation contract.** Each derivation names its input schemas, method identity, initialization, output schema, retained state, and permitted observations. It also declares whether it is deterministic, retractable, incrementally maintainable, or executed by an external worker whose result carries an attestation.

For a numerical worker, the node checks the declared protocol, bindings, authority, and retained evidence. A stronger claim about numerical correctness requires its own checker or proof package; the worker’s signature establishes attribution. The machine DSL needs forms for bounded internal transformations and resumable dependency maintenance, while external numerical libraries remain ordinary consumers and publishers.

**Name must become a commitment to an interpretable artifact package.** A dataset’s identity binds its manifest, schema, units, coordinate systems, chunk layout, missingness conventions, and required interpretation artifacts. Separate commitments identify exact physical encodings and explicitly declared semantic views; converting Celsius to kelvin produces a named transformation with laws and provenance.

Transport along equivalences becomes practical here. An adapter declares the observations preserved by a representation change, the assumptions required, and a checked witness where available. Lossy conversions carry their loss explicitly, allowing an analysis requiring raw measurements to reject a package containing only rounded summaries.

**Binding must distinguish identity facts from scientific assertions.** A sample’s custody identity, a sensor’s signing key, a taxonomic identification, and a hypothesis about contamination have different validation rules. Contradictory identifications remain addressable assertions with issuers, scope, evidence, and supersession relations.

The kernel needs typed assessment records such as `supports`, `challenges`, `qualifies`, `withdraws`, and `supersedes`. Their admission and authority are mechanically checked; their scientific force belongs to the declared assessment method. Confidence values carry a method identity and assumptions, including correlation where applicable, rather than entering a universal confidence score that silently combines incomparable judgments.

**Span must become a dependency relation with declared meaning.** Edges distinguish “read these bytes,” “used this calibration,” “excluded these samples,” “trusted this attestation,” and “searched this collection without finding a match.” Dependencies can name individual records, content ranges, keyed selections, or versioned queries.

Negative dependencies are essential. A claim that no qualifying anomaly occurred depends on the searched population and its completeness, so a newly admitted old observation can affect the claim even though no positive edge pointed to that observation. The query DSL therefore needs versioned predicates, declared search universes, and dependency capture for absence, aggregation, and exclusion.

Reverse indexes must be complete through published frontiers. Large fan-out is processed as paged, resumable work under principal accounting; discovering a million affected results never becomes one executor step. Conservative dependency summaries are allowed when they over-report impact and declare that approximation.

**Frontier must become an account of coverage across the inquiry.** Acquisition completeness, ingestion completeness, derivation coverage, correction discovery, and repair completion are distinct frontiers. A dataset can be fully ingested while a calibration correction remains only partly propagated.

Reads retain the distinction between `exactly-at` and `at-least`. An answer additionally reports its evidence cut, applicable assessment revision, impact-discovery coverage, and unresolved relevant repair obligations. Statements about completeness name a finite collection or declared selection boundary; disconnected peers and undisclosed collections remain explicit unknowns.

**Obligation must become continuing responsibility for evidence.** Existing retention and custody obligations extend naturally to promised replication, requested review, correction notification, recomputation, and acknowledgment by a downstream custodian. Each obligation has an authorized discharge predicate, an explicit waiver path, and a scope that survives retries and restarts.

A correction notification discharges delivery responsibility only upon its declared receipt; it does not establish scientific agreement or successful repair. Retention policies separately protect raw evidence, methods, assessment history, and exact identities, so preserving one summary cannot silently discharge another user’s need to revisit the original measurement.

These eight interfaces need shared declaration forms for evidence schemas, protocols, derivations, dependency capture, assessments, and obligations. W3C PROV supplies useful provenance vocabulary; Buneman, Khanna, and Tan’s *Why and Where: A Characterization of Data Provenance* motivates distinguishing kinds of dependence; *Provenance Semirings* supplies an algebraic account for suitable query languages. Naiad and Differential Dataflow inform incremental maintenance, while *Adapton: Composable, Demand-Driven Incremental Computation* informs selective recomputation; fn2 must connect these ideas to durable responsibility and external effects.

All of this preserves the execution design: one semantic executor, concrete pageable representations, bounded resumable machines, one byte pool, and publication after durable acceptance. Generality lives in declarations and compositions whose work is accounted for. Statistical fitting, image analysis, simulation, and instrument drivers execute outside, with the core deciding the identities, permissions, bounds, and commitments that make their results composable.

## 4. The one capability that would make it epic

**A correction can travel through a distributed body of knowledge and return a verifiable account of what changed, what still stands, and who has accepted responsibility for the remainder.**

Call the operation `reconsider`. Its input is a correction package identifying the challenged evidence or assumption, the proposed replacement or qualification, the issuer’s authority, and the precise scope of the change. Its result is an evolving, inspectable repair dossier covering a named collection at a named cut.

Start with the mislabeled reference sample. Three laboratories used it; their analyses fed a public watershed model, a teaching dataset, two reports, and a cooperative’s sampling plan. Each institution has different access rules, software, and willingness to accept another institution’s assessment.

The originating node commits the correction and creates a repair campaign. A bounded machine traverses the reverse dependency index against a pinned cut, recording affected derivations and negative-query dependencies as it goes. It publishes a discovery frontier so observers can distinguish “nothing affected in this examined range” from “this range has not been examined.”

For each affected artifact, the declared derivation contract selects an admissible response: exact incremental update, full recomputation, renewed external assessment, human review, or an explicit inability to reproduce. Workers claim jobs under fenced leases. Results carry the prior artifact, correction identity, input cut, method revision, output commitment, and relevant dependency evidence, making retries idempotent and late results checkable.

The system preserves the original observation and original conclusion. It adds a new assessment explaining whether the conclusion changes, survives for a stated reason, or remains unresolved. An algebraically insensitive result can carry a checked preservation witness; an opaque external analysis remains affected until its declared reassessment protocol supplies an answer.

At a node boundary, the campaign sends an authorized impact package. A private laboratory can return a signed receipt that it has affected derivatives and has undertaken their review, exposing only the permitted commitments and status. Publicly verifiable set-completeness requires an appropriate disclosure or proof mechanism; the dossier records when its account rests on an institution’s attestation.

Discovery and repair advance independently. A public figure can remain pinned to its original reproducible inputs while displaying a relevant unresolved correction. A downstream author can subscribe to the repair frontier and publish a revised report once its own acceptance predicate holds.

A builder can begin with six record kinds: `correction`, `dependency-set`, `impact-job`, `reassessment`, `repair-receipt`, and `campaign-checkpoint`. Implement a dependency-capturing relational DSL, reverse indexes with coverage, a paged traversal machine, externally claimed recomputation jobs, and dossier reads that join impact and repair frontiers at an exact cut. Exercise the complete composition with lost replies, duplicate corrections, newly arriving observations, revoked workers, unavailable source chunks, and process death during repair publication.

The epic property is the connection from an empirical correction to a complete account of responsibility within a declared boundary. Build systems invalidate targets; databases maintain views; provenance systems describe ancestry; review platforms collect judgments. fn2 makes their operations compose across instruments, analyses, publications, and decisions, with explicit coverage and preserved disagreement.

A community could ask, “What are we still entitled to conclude after learning this?” and receive a traversable answer containing evidence, recomputation, surviving claims, unresolved questions, and accepted obligations.

## 5. What it must never do

It must never turn durable acceptance, a valid signature, a reproducible computation, or institutional authority into an assertion that an empirical claim is true.  
It must never erase an original observation or dissenting assessment when a favored interpretation changes, and every statement of completeness must name the collection and frontier it covers.  
It must never let replay, correction propagation, or a demand for reproducibility perform a fresh external intervention without a distinct authorized operation and its own durable outcome.