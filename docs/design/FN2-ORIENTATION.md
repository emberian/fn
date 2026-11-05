# fn2 orientation (present state; §3-§5 rewritten 2026-11-04 at origin/dev a4bea27de; rewritten whole, never appended)

fn2 is ember's rebuild of fn as "the thing a world is kept in": the persistent event log between systems, "the generalized redis/postgres for the datamodels we're reaching for", built bottom-up and semantics-first on `dev`, with metaprogramming meant to express the whole thing succinctly; it was promoted to the repository root on 2026-11-01 (49787612f). The old tree is frozen at 6521f18c4 (the breaking cut plus the gate work) and is the quarry. This file is the entry point: read it, then the documents it names, in order. What the tree does not yet implement is marked owed, never stated as fact.

## 1. Ember's words that bind fn2 (verbatim, dated; EMBER-ARCHITECTURE-WORDS.md §14, and the files named)
- Purpose (10-28): "i'm hoping that we can use this as sorta a "high performance database node" for the robigalia operating system someday, this node is sorta like the generalized redis/postgres for the datamodels we're reaching for"; (10-27) "i'd like fn to be usable for other dregg projects soon/eventually"; "if one were to use this software from the outside everything would work and be fast and use the pathways we're building and not legacy pathways". Earlier and standing: "this is the persistent event log between systems"; "foundational orthogonal persistence"; "BP is product."
- Rebuild in place (10-28): "do we want to rebuild a fn2 inplace here that we eventually swap over the root of the repo to?" (answered yes).
- Semantics first (10-28): "i feel like our fn2 we should be *semantics-first* and not worry as much about the proofs until we've actually gotten the implementation into a state where we WANT assurance from it"; with (10-17) "we only need to demonstrate that our TOPLEVEL THEOREMS aren't vacuous".
- Bottom up (10-28): "This software can be great but we need an extremely methodical approach to actually take it there, and it needs to be from the bottom up ..... so that it's actually comprehensive and not piecemeal...."; launching the build: "do it systematically and from the bottom up as we identified, focusing on getting the semantics and dynamics right and high performing first before we try and get lost in the assurance story. classical testing will surely find many bugs as we go along. (but we DO need to keep in the eventual proof in mind)".
- Succinctness (10-28): "i'm feeling kinda hopeful that we can come up with some metaprogramming approch that lets us express the whole thing very succinctly"; (10-28, on COHERENCE) "it sounds like maybe we need to be rethinking how our macros work, then, and maybe even have a metatheory of these things".
- The machine form (10-30): "we need to fix the machineform shit URGENTLY ... it doesn't matter or not if the software is working if the way we are building it is so trash and contrary to our earlier standards." (MACHINE-FORM-20261030.md.)
- Reground (10-30): "there is still so much more meat to put on these bones ... we should review our original fn2 discussion and files and reground ourselves ... building the fn2 of our dreams and not the fn2 that we find after letting the lanes wander through our old plan." (REGROUND-20261030.md.)
- The workflow (10-31): "why are we paying full gate cost constantly? come up with a different development workflow that doesn't have these turnover flaws. We need to stop turning over seats as often, which means individual seats need to be less retarded about their own work." (WORKFLOW-20261031.md.)
- Nothing lifted whole (10-28): "You think you can take those books whole? are they actually worth taking? what happened to our bottom-up philosophy :) hopefully as we take them we can polish them up."
- No own crypto in ACL2 (10-28): "there was never any reason to be doing our own crypto in ACL2. that requirement isn't a real requirement, we should just lose it." (OpenSSL/LibreSSL, libsodium and the vendored ML-DSA shim via FFI stand; EMBER-ARCHITECTURE-WORDS §13.)
- Nothing refused (10-28): "its our job to make software that is capable of being correct. if someone wants to deploy it in a way that is fundamentally unsound, that's on them, not us. we shouldn't go out of our way to "refuse" things though." No ceilings: "No compile-time ceilings."
- Performance (10-28): "Regarding pure step/state/event/effects: is **this** why we're fundamentally bottlenecked on the performance of our software? are you familiar with "tigerstyle""; "we've become WAY too empirical/measurement-driven". Answered by EXECUTION-MODEL §2 (the pure step is not the cause; conversions and work under the mutex were). Book time (10-28): "no book should be over 1m."
- Identity (10-28): "keep the Message-ID octets and let the operator otherwise deal with it."
- Composition (10-28): "I feel like we do need to be careful that we are composing these things correctly and not just suffering a proliferation of conceptual linkages. also we need to stop having astra do vacuity attacks lmao, and invite it to be a more equal peer collaborator".
- Width (10-28): "we need to do more expansively creative thinking about the widest role fn2 could have because you've contracted into describing the smallest version of what fn2 would be"; on the result: "I notice this is starting to sound like (modal) logics and theories. Which is good. because that's the right direction."
- Boxes (10-29): "we are permitted to use hbox & local mac to their absolute utmost for our present project." Pricing (10-29): "pricing isn't something we usually bother to do. it doesn't actually help us complete the project".
- The goal (10-28): "if we can recover fn2 and *actually close it out finished* that would be the first AI-recovered project we've pulled off".
- The twenty sentences a designer must not violate: EMBER-ARCHITECTURE-WORDS.md §14; where ember changed their mind: its §13.

## 2. Rulings that bind (main's, as present-state design files; ember overrules by editing them)
- **MACHINE-FORM-20261030.md**: one `defmachine` is the whole of a kind; arms in a step language (`:do :set :next :case :issue :park :charge :stop`), cost/writes/next/uses/refusal routing derived, so an absorb cannot be written; per-octet exports refused in arms (range primitives by handle only); a kind's book certifies alone and the assembly is a registry (placement P1-P4). Ember's answers (10-30): the migration order is fine; `:do` calls only defcost'd operations and range primitives; hand `defthm`s in a kind's book are refused unless about a declared operation ("yes, vital"); the in-flight landings land and no new arms are written in the old form.
- **IDENTITY-ACROSS-PEERS-20261030.md**: fourteen rulings. Acceptance is domain-local and peers carry evidence; receipts are attributed and selection is a fold; a conflict commits evidence; no per-name ceiling; the typed read result before any HDR item; the event envelope gains origin fields with the revision stamp now.
- **WORKFLOW-20261031.md** (rewritten whole after ember 10-31: "these gatescripts are bullshit ... revisit our entire development flow and methodology to reduce redundant and useless and bureaucratic work"): a commit establishes only that the changed books load, the touched scenarios pass in the REPL on the tiny profile, and the author read what it wrote; then push and READY. Every per-commit whole-tree gate, the byte-identical A4 baseline, OWED.md regeneration in commits and per-landing evidence sweeps are deleted; their rows run in one unattended nightly on forge that nobody waits on (owed: the script does not exist yet). Seats are long-lived and own their layers; main runs no gates. FN2-SEAT-COMMON.md §4 carries it.
- **REVIEW-20261030.md**, main's five rulings at its head (their present status is recorded there).
- **REGROUND-20261030.md** §5: main's reorientation, proposed for ember to amend and not yet amended: keep the spine to a durable POST and a readable article; stop new evidence machinery and fn1-surface breadth until then; start now the envelope fields, the consumer port's design, the FLOOR run and the range-copy path, the live plane's edge class, the BP/peering design, and the DSL pass (now MACHINE-FORM); M2 is redefined as "a consumer appends, reads, waits and acks on the laptop, and an NNTP reader sees the same article".

- **Wire words; a kind lands with its producer (ember 10-31, D46 enforced).** Every record kind, fact or schema in a design names the protocol verb that writes it and the one that reads it, in the protocol's words (a history entry per RFC 5537 §3.3, a forward pin released by the receipt ADU, a catch-up batch), with the RFC or fn1 reference beside it; a kind without a serving writer is design, never a schema, and does not land until its producer serves. "Attributed receipts" and the like are renamed to the thing.

## 3. Where the tree is (origin/dev a4bea27de, 2026-11-04; STATE-20261104.md is the one-screen state)
fn2 is the repository root since 49787612f (the fn1 tree is tagged `fn1-quarry` at 6521f18c4). H's nightly at
132ac2c62 (`build/h8/nightly/LATEST.txt` on the Mac): 26 NNTP verbs served on the simulator and the socket, 0
disagreements, five interim rows (XPAT, XFN-ZARTICLE, STARTTLS, COMPRESS, XFNCATCHUP), M2 cuts 0/12 because the
nightly does not yet run sim-layer-e over the served machines.
| layer | built (sha) | owed (the layer's notebook carries the exact next step) |
|---|---|---|
| A: pool, vocabulary, host ABI, simulator, executor | the executor, the native loop and socket, the `:local` listener, per-kind leaf books over `defattach` (F4 736591806), the cleanup reserve and the owner uid (F5 aac7a29e7) | the timer service and `fn2-issue-connect` (named by `defservice`/`defaction`, undefined); the F5 tables consumed; FLOOR; N cores on one network |
| the form | G1-G3, P1-P4, F2 (c782ff824), F3 (19d57c6d5), F4 | the `:carrier` mixin; child form for the six core-form kinds; listener registry arms |
| B: durability | B1-B4, B5-1..B5-4a, B-S2, S11 posture, S12 (55c8290de) | `fn2-commit` and `fn2-recovery-machine` in the form (in flight on lane/b-form-port); replay; B6, B7 |
| C: ordered runs | runs, schemas, folds, the sealer, §4a identity, `fn2-successor-emit`, `put-row` writers (F3), the sealer wake fix (H4 edc631a44) | minimal C5 (64 installed-run rows last six to eight POSTs); `:child` on the successor ops; the sealer in the form |
| D: machines, NNTP | conn and upload on the form (H1 da003258a), reader breadth (H3 0f568f89b), the durable POST (c985342f8), CHECK/IHAVE/TAKETHIS (H5 21b661477, 132ac2c62) | ARTICLE/HEAD/BODY from stored octets (in flight on lane/article-octets; today headers are rebuilt from the overview row); XPAT, XFN-ZARTICLE; STARTTLS |
| E: consumer, TLS, peering, BP | the consumer port and codecs, cns-edges, `fn2-cns`/`fn2-ctl` serving the six verbs through `fn2-turn` (H2 9860d85a5, F6 2456161b6) | the consumer on a socket (in flight on lane/consumer-socket); E1, E2, E4, BP, E6 |
| H: the harness | the laptop nightly at the root (bad1b23f0, 8cc2f2c4f), the interim table (554e1e407) | `H_NIGHTLY_M2` (in flight on lane/m2-measure) |
| Lean | `meta/`: the registry and the closed subset translated from the world, the step-language interpreter, `Fn2.Arms.Derive`, PW3 and PW4 (LEAN-METATHEORY.md §0) | per-arm proofs beyond the seven `ArmCorrect` instances |

## 4. The order now
BRICKS-20261031.md §5: M2 demonstrated (cuts above 0 on H's line, a reader's ARTICLE equal to the posted
octets), then the sealer and minimal C5, then the core-form kinds to child form behind a `:carrier` mixin, then
breadth (D7 timers and TLS, E2, E4, B6/B5-4b, BP, E6). The served surface is measured by the interim table
shrinking and H's line.

## 5. The documents (all in docs/design/; README.md lists them by role)
**Present state:** STATE-20261104.md, BRICKS-20261031.md.

**Settled decisions** (read first):
1. EXECUTION-MODEL.md: one semantic executor over a deterministic cooperative network of bounded resumable machines; ten rules; the refinement obligation; ember's rulings; what is owed.
2. STORAGE-DESIGN.md (with STORAGE-DESIGN-ASTRA.md, §3 the concrete format): one ordered semantic event journal, separated content-named payloads, one pageable ordered-run engine, parent-held page hashes plus a signed Merkle checkpoint claim, pins as versions with object leases, evidence-gated reclamation, four recovery states.
3. MACHINE-FORM-20261030.md and IDENTITY-ACROSS-PEERS-20261030.md (§2 above, with IDENTITY-ASTRA-20261030.md); DSL-METATHEORY.md (the one notion of declaration, the registry, the obligation store).
4. INBOX-DELIVERY.md: selection over per-stream indexes, fan-out only by address, the per-edge policy mechanisms.
5. RELEASE-PLAN.md: the surface table, the suite, the assurance start, the release definition, ember's five rulings.

**Rulings and reviews:** WORKFLOW-20261031.md, REGROUND-20261030.md with REGROUND-ASTRA-20261030.md, REVIEW-20261030.md, REVIEW-SINS-20261028.md, REVIEW-REQUEST-20261031-ARGON.md and REVIEW-ARGON-RESPONSE-20261031.md, EMBER-ARCHITECTURE-WORDS.md.

**The record of what exists and what was learned:** INTERFACES-TODAY.md (fn1's boundaries), ENVELOPE-AND-HOST.md (the floors; the host), CLIENTS-AND-DATA-MODELS.md (who uses fn), QUARRY.md (a map, never a shopping list).

**Theory kept in the tree:** COHERENCE.md (squares as how fn2 is built and checked), TRANSPORT.md, LEAN-METATHEORY.md (Lean for frame theorems, ACL2 for instances; the Lean model of the machine). The rest of the research record (WIDEST-ROLE and its twelve council drafts, UNIVERSAL-CONSTRUCTIONS, PLANES-AND-GAMES, MODAL-KERNEL, HIGHER-STRUCTURES, REALMS-FROM-DREGG, FILTERS-2026, the consultation rounds, fn1's anatomy) is in history before 49787612f and in build/coordinator/fn2/ on the Mac.

**How we work:** briefs/FN2-SEAT-COMMON.md (the method), the layer briefs briefs/FN2-LAYER-{A-POOL-HOST-SIM,B-DURABILITY,C-ORDERED-RUNS,D-MACHINES-NNTP,E-SURFACE,H-HARNESS}.md, the layer docs docs/{a-pool-host-sim,b-durability,c-ordered-runs,d-machines-nntp,e-surface,h-harness}.md, the notebooks lanes/{a,b,c,d,e,form,h,lean-meta}-continuation.md, docs/boxes.md, docs/OWED.md (generated).

**Outside the tree:** ~/paperbin/README-fn2-20261028.md (papers, the crash-model table, the three automation routes); ~/dev/acl2aiguide (public; ai/00-06 are written to be loaded into a building agent's context).

## 6. Decisions (main's rulings of 2026-10-31; one genuinely open item for ember)
Ruled by main, present state (ember overrules by editing here):
1. REGROUND §5 stands as the direction: M2 is "a consumer appends, reads, waits and acks on the laptop, and an NNTP reader sees the same article"; E's design starts now, before D's fn1 breadth. (Ember's reply to REGROUND was to put the machine form first, not to amend the direction.)
2. STORAGE-DESIGN's five decisions as amended by the scholar are adopted as built: B and C stand on them, and nothing in ember's words contradicts them; reopening one is a rewrite of B and C and is done only with a reason in STORAGE-DESIGN itself.
3. The research decisions: WIDEST-ROLE §5's five are adopted as recommended (ember on WIDEST: "the right direction"); UNIVERSAL-CONSTRUCTIONS §12 is reread as the 5.1.1 fragment's; PLANES-AND-GAMES §5.4's sentences enter the layer briefs when the live plane starts (REGROUND's start-now list, item d); MODAL-KERNEL, TRANSPORT, COHERENCE and LEAN-METATHEORY stay research until a quest consumes an item, and that quest writes the ruling.
4. The remaining envelope fields (WIDEST §3, decision 2: author key, payer principal, grant reference) go into B's event envelope now beside the revision stamp, the occurrence id and IDENTITY ruling 2's origin fields, as fields with no behaviour yet; B owns it before freezing more layouts.
5. The nightly (WORKFLOW §3) is main's: one cron on forge over the existing drivers, posting a summary per file; owed until it runs once.
Ruled by ember 10-31: emberian/fn #18 and #19 closed without comment (the 10-16 drafts in build/coordinator/replies/ are moot). #14's 10-08 question is minidregg's.

## 7. How to start (in ~/dev/fn, on dev)
Read §1-§4 here, then the settled decisions, then your layer's brief, layer doc and continuation. Hold the interfaces in your head before writing anything: name the components, their boundaries and the byte representation at each. Work by FN2-SEAT-COMMON.md. This file is rewritten whole at each milestone or ruling.
