# ember's architectural intents for fn, verbatim (2026-10-28; §13-14 brought to present state 2026-10-31 from EMBER.md 10-27..10-29 and the rulings files)

For the fn2 designer. Read-only investigation; tree origin/dev = 3bbfc4dca. Representation (octet lists, stobjs, arena, pages, the 18-step POST path) is already done in `build/coordinator/REPRESENTATION-HISTORY-20261028.md` and is not repeated here; only where a representation quote is also an architecture quote does it appear, with a pointer.

**Sources.** ember's typed turns (`cv show <id> --kind prompt,answer --json`) from the 44 top-level fn sessions: every Claude session with cwd `~/dev/fn` (09-19 to 10-01), ember's Codex desktop sessions in `~/dev/fn` (`01a0b33a` the founding Astra session, `01a0b310`, `01a0eeec`, `01a0fe41`, ...; lane sessions titled "Message Type: NEW_TASK" excluded, those are agent-written), and the seven fn coordinator sessions that ran from `~/dev/minidregg` (`9627d694`, `be1e9dcf`, `35f3668a`, `4a22422c`, `905fe751`, `d5d27b94`, `d0d33f7b`). 1,443 turns; duplicates across forked sessions collapsed to the first. Plus `build/coordinator/EMBER.md` read whole, and `planning/decisions.md` at origin/dev.

**Cite form.** `session#index YYYY-MM-DDTHH:MMZ` (UTC, from the transcript). Codex ids keep the `01a0` prefix (`01a0eeec` = EMBER.md's `cx-eeec`, `01a0fe41` = `cx-fe41`). Where EMBER.md gives a different clock for the same turn I use the transcript's. Typos are ember's. Only ember's own typed text is quoted as ember's; a question/answer pair from an `AskUserQuestion` is marked **[answer]** (the option label ember chose, which the agent wrote); a decision-register row is marked **[decision row]** and is the register's words, not ember's. Pasted third-party text (GPT-6 reviews, Discord) is never quoted as ember's, except ember's own lines inside the founding Discord paste, marked **[Discord, ember]**.

**Terms that found nothing in ember's own words**: "tigerbeetle" (only inside "tigerstyle from tigerbeetle"), "DSL", "fn-core" (ember answered a question about it, 35f3668a#1588, below), "one owner", "executor", "io_uring", "fsync", "helm" (no fn turn names helm; EMBER.md says the same for 09-29..10-13), "keystone" (only in a forwarded handoff), "6.6" outside the version topic. "One owner, one step function, one lock" is the coordinator's RUNTIME-MODEL-DRAFT-20261009 and DESIGN-RESOURCE-MODEL-20261012, not ember's; what ember said back to it is in §1.

## 1. What fn is for: purpose, users, the substrate it is meant to become

- **01a0b33a#4 2026-09-18T06:36Z** (the founding prompt; ember's own opening line, then a pasted Discord thread):
  > hi astra. i'm feeling insane today and like i want to do something with acl2. the something? an "enough" nntp server to serve as a comms nexus between some AIs and humans.

  **[Discord, ember]** inside that paste: "as for API endpoints, are you thinking, like... SMTP? christ its been so long since i thought about MTA. / i was imagining something filesystem-centric." · "ive never run NNTP so that's kinda tempting; / but i've never run 9p either and it's about time i got around to it." · "whats 9p net news look like you reckon?" · "i have a phd in megaautismo formal methods, does an NNTP server expressed in some first order logic be called for 👀" · "fn for fuckin news / formal news / fenomenology of numbers" · "i mean, what, ask Z3 to solve the next-state relation for the next coinductive step? / directly over a system of formulae? / what, over lisp atoms? / .... acl2?"

- **01a0b33a#44 2026-09-18T06:41Z**
  > What do you want to do for persistent storage  / data representation / etc etc be? What would be "space age"? I someday would like this to be usable for extraterrestrial operations, eg Licklider protocols are an inspiration as well....
  >
  > I honestly think we can be ambitious and try and make a pretty big step, as long as we do a lot of the design up front :) and you're pretty smart for it :)

- **01a0b33a#63 2026-09-18T06:48Z**
  > Sounds perfect, we can have a specialized-purpose storage layer just for what we need.

- **b3f4abb5#127 2026-09-19T02:10Z**
  > mind reviewing the work that has already been done for ... hm, oversights, derps, and places we could be dreaming much bigger in terms of formal assurance, establishing a bedrock for eventual distributed information type things in ~/dev/breadstuffs / ~/dev/minidregg ...

- **990cbaad#1779 2026-09-20T02:05Z** (what v0 and v1 mean)
  > actually to me v1 means M6 (and even a bit more beyond that). so. actually what you described is more like.... i don't even know what you described. that's just some intermediate milestone :) to me v0, the very first one we share, still requires us to be able to use *all* features between two peered fn servers... so........

- **01a0b33a#10103 2026-09-21T07:54Z**
  > i'm hoping for this to be a "high-assurance, high-pleasant" implementation :)

- **01a0b33a#21103 2026-09-23T14:05Z**
  > We want this to be useful & robust NNTP infrastructure but we also will be using it as the basis of Robigalia/dregg's agent coordination / silo communication / type things as well so future avenues of extensibility and growth are envisioned.

- **01a0b33a#21358 2026-09-23T14:18Z** **[answer]** first dregg integration: "An immutable report/receipt and reply between sleeping agents (Recommended)". **#21368** **[answer]** "Consumer-owned durable inbox/outbox, with an explicit fn cursor/ack contract (Recommended)". **#21387** **[answer]** "Separate stores/admins with explicitly trusted transport peers first (Recommended)".

- **01a0b33a#24340 2026-09-23T18:35Z**
  > because btw. eventually we'll be using this as an absolutely central component of the distributed operating system, at least to start with, topics as their own autonomous chains, different policies, different swarms all combining together via these nodes... :))

- **1db4b0cd#1145 2026-09-26T23:07Z**
  > so i was born in 1994 and never actually used usenet myself. i've been really enjoying learning abit about it, but i'm curious like. what IS the admin and privacy model. like will i be able to run a server and be its admin and hand out accounts to my agents and they'll be able to share private topics and whatnot with each other?

- **1db4b0cd#2038 2026-09-27T02:45Z**
  > regardless of that, we will continue to fork reality from 1987.

- **01a0eeec#32013 2026-10-01T01:15Z**
  > you may not fully realize it but i've been planning to hyperoptimize and generalize this into being the high assurance substrate of the robigalia distributed operating system, like this is the persistent event log between systems, and we'll be building up way more software by layering ~~/dev/minidregg / /~~dev/breadstuffs onto it / integrating this / either extending or tweaking or replacing the nntp and other models with what's actually appropriate between nodes........

- **f84a8f40#833 2026-10-01T08:07Z**
  > i'm aggressively wanting the best possible in-memory/hybrid persistent representation because this thing is going to be part of the foundational orthogonal persistence in the rest of the system and having this component be high performance high quality high assurance via metaprogarmming, proof engineering, mechanical sympathy, and careful algorithmics and datastructures, is ... the task of the day :)

- **b53753a1#8602 2026-10-01T07:48Z** (the warranty)
  > btw that IS/WAS one of the explicit goals of fn, is to have a full up-front resource accounting of all resources expended by the system on behalf of its users. "software with a warranty" was how it has been described....... some of these aspects definitely were wrong and need to be improved, but some aspects (ceremony etc) seem addressable with improved metaprogrammatic proof engineering, we should definitely do things more robustly by construction.

- **01a0fe41#2520 2026-10-03T09:25Z**
  > This is a challenging distributed OS project with a lot of moving parts. It is an honor getting to work on it with you. fn is just one small part, and eventually will serve as sort of the "redis of it all" and as the vital persistent communicable channel through with semantics flow. \~/dev/minidregg is already being built with eventually running on `fn` (or related software) as a goal.

- **01a0fe41#4594 2026-10-03T11:10Z**
  > we basically already know exaclty what the remainder of the software is going to look like, it's constrained by the principles of good software, bounded-metered-backflow-safe/DoS-resilient/QoS-operable types of software. remember that we'll be supporting many types of persistence, transience, snapshotting/folding, etc policies when we "finish up" our half of the project and hand it off to the dregg team, that's what they're gonna do. because basically this thing needs to be a rich "semantic web hyperredis" ...... disguised as a newserver this wholetime :joy: but the stuff we've been building along the way; all supports that goal; it will be additive/empowering-to-start-with-this compared to almost any other starting protocol. and compatiblity with legacy software, is somehow cool :coolguy:

- **9627d694#1312 2026-10-04T01:59Z**
  > - regardding "the redis of it all" – extensions in that realm will be for 6.6.1, in the meantime supporting the basic patterns that zmq does would be nice..... (if we have the infrastructure to make that sustainable and cheap (macros etc))!

- **9627d694#2507 2026-10-04T08:15Z**
  > zmq-shaped surface can be in 6.6.0 if we like. 6.6.0 is *for* being good enough to start treating as a foundational component for the rest of the distributed OS / mini.

- **905fe751#1734 2026-10-10T04:12Z** "i bet this would very trivially become a high assurance bluesky PDS ...... after we finish our repairs and optimizations ;)" · **#1898** "honestly could we be building out the pds on the side overatop what we already have without any conflict at all...?" · **#1901** "maybe we just Shouldn't :)" (mind changed within 30 s: no PDS side-build).

- **d0d33f7b#5003 2026-10-27T18:05Z**
  > i'd like fn to be usable for other dregg projects soon/eventually.

- **d0d33f7b#5907 2026-10-28T04:56Z**
  > how many lines of code do we even think the coresystem can be? i'm feeling kinda hopeful that we can come up with some metaprogramming approch that lets us express the whole thing very succinctly, because i'm hoping that we can use this as sorta a "high performance database node" for the robigalia operating system someday, this node is sorta like the generalized redis/postgres for the datamodels we're reaching for ...........  if that even makes sense... but like yea heh.

**Through-line.** The purpose widened monotonically and was never narrowed: an "enough" NNTP nexus for AIs and humans (09-18) → bedrock for distributed information (09-19) → dregg's agent coordination (09-23) → "the persistent event log between systems", "the high assurance substrate of the robigalia distributed operating system" (10-01) → "redis of it all", "semantic web hyperredis disguised as a newserver" (10-03) → "high performance database node", "generalized redis/postgres for the datamodels" (10-28). NNTP compatibility stays ("compatiblity with legacy software, is somehow cool"), but ember twice says the NNTP model may be "extended or tweaked or replaced" between nodes.

## 2. The node's architecture: runtime, host, step machine, threads, configuration, self-containment

- **418232ec#1632 2026-09-19T14:47Z** (answers to "what is still kinda fake"; the whole turn, which is the earliest architectural charter in ember's words):
  > - Authority being noncryptographic is acceptable.
  > - Oh jeez we need to support this as being an actual /server/ haha, let's make sure we're pushing that as hard as we can soon (obviously we need to let present wave work itself out a bit).
  > - We can't be having compiled-in configuration, and we will need to be careful to actually have formal statements about server reconfiguration events and that they are implemented properly etc ("assured live reconfiguration" would be a great feature to brag about, sometimes servers dont implement it because they think itll be hard/risky!)
  > - Let's obviously fix that identity preimage thing
  > - I don't understand why we have so much going on in Python anyway, maybe it was a crutch we shouldn't have reached for?
  > - We need to be thinking about extending some of these proofs but not going fully insane, and also not setting up "strawmen disproofs" (eg proving some strawman situation fails a certain way).  We need to make sure that the functional correctness things we're proving about our node are *eventually* capable of chaining into something /like/ a Universally Composable framework or something like that. Especially as a server we need to know "clients cant crash us regardless of what they send us" and as a server that we appropriately implement semantics.
  > - We can be ambitious about real-fixes that change things that lots of other things touch.
  > - The crash model definitely needs to be massively sophisticated, the present status is not acceptable at all.
  > - Don't worry about the article-properties failure, it is being investigated. (I suspect it is SWAP-related and involves disk corruption. Don't worry about it.)
  > - Yeah lmao we need to not be doing this DTN/BP theater, we need to come up with a real design.

- **01a0b33a#7941 2026-09-21T06:01Z** "Remember to AVOID the "Twin problem" where thehre's a bullshit python implementation of something that we should be doing with higher assurance."
- **01a0b33a#9731 2026-09-21T07:36Z**
  > (why do we have so many python paths anyway? shoudlnt that stuff all just be done in lisp mostly..??? use `cv` to discover my previous criticisms about 'python twins' to claude...  think ther ewre some... oh well maybe its fine.i just wouldnt want python in a running fn process, that isnt high assurance whatsoever))
  → **[decision row]** D07 (reaffirmed 2026-09-21): "native Lisp deployment, executing ACL2 definitions directly; no Python in the deployed node, CLI, launchers or runtime helpers."
- **01a0b33a#21001 2026-09-23T13:54Z** **[answer]** "Raw insertion developer-only; production uses normal submission".
- **997a44b0#1737 2026-09-26T19:16Z** "lmao for distribution we definitely can be shipping a different type of image right??????? what's the deal with our *runtime impact of ACL2*"
- **1db4b0cd#1329 2026-09-26T23:47Z** (numbered answers to a deficiency list):
  > 1. I don't understand how we haven't managed to replace the representation yet. That's a priority.
  > 2. We need a better mutation scheme
  > 3. Jeeeeeeeeez there's no reason to have THAT level of redundant durability is there? is that what it actually takes? there has gotta be a better/smarter job system / way of doing the whole durable storage thing.
  > 4. we can definitely fix this.
  > 5. we can do a smarter kind of multiplexing than thread-per-connection etc.
  > 6. we need to pick up some of this neglected BP work!
- **1db4b0cd#4774 2026-09-27T17:38Z** **[answer, ember's free text]** F6 open time: "Honestly. HOW is it possible that we're doing SO much work at startup. I'm extremely disgruntled with the present state of affairs." F4 scheduler: "Hmmm. I'm not sure how to answer this one fully; I'm inclined to ask "maybe we need a much more robust scheduler/time/event model, because a laggy/disk that needs maintenance is a real fact of life that we shouldn't sandpaper away with our model""
- **1db4b0cd#5608 2026-09-27T21:47Z** "what other things are we doing that ultimately would be unnnecessary if we were smarter?"
- Web reader: **01a0b33a#7296 2026-09-19T01:38Z** **[answer]** "NNTP and command-line clients first; web later". **[decision row]** (2026-09-27 23:33Z, quoted in the 09-28 register): "wait i just noticed the webreader is python?? we shouldn't have that ;)"; "i'm thinking it should be something nice built in ... lispwise". **b53753a1#2068 2026-09-28T23:39Z** "(and the webreader IS native these days, right??)". **35f3668a#1588 2026-10-09T04:31Z** item 4 below.
- **b53753a1#4298 2026-09-29T05:04Z** (admission at capacity) "i'm thinking we should refuse posts in that condition. it's basically up to the operator to ensure that they can either provision more resources in time to prevent stalling, or else perform other QoS actions...."
- **01a0fe41#6048 2026-10-03T12:55Z**
  > btw i saw we were adding a client command to export an operation's payload – we should make sure we have a VERY ROBUST suite of dev/internal commands that let us access alla tha things. and honestly we should probably be able to pop open a repl into a running one, eh???
- **35f3668a#1480 2026-10-09T03:58Z**
  > god yes wow. we'll also prefer to massively simplify the lisp host and soforth. like i feel like the abstract protocols shouldn't be all that complicated here and that most of the detail is in the actual *detail*....
- **35f3668a#1588 2026-10-09T04:31Z**, answering the five open questions of the coordinator's RUNTIME-MODEL-DRAFT-20261009 (its spine: "One step function, one owner, one lock. `fn-node-step (st event) → (mv st actions)` ... The lock is held only across step, which does no I/O"; the questions: (1) per-connection stobj allocation as the threading discipline, (2) fn-core stays the shipped artifact, (3) BP's transports in the one loop or a second, (4) the web reader inside or out, (5) wipe-and-rebuild under D68):
  > 1. do we really need to be using ACL2's runtime if we have an extractor and the "official" version has extremely expensive per-thread overhead...?? lets figure out some solution here. ideally we shouldnt be having a bunch of garbage nonsense that we do and that it should just be a nice, parsimonious, good multithreaded impl ... but maybe that's reaching too far ;)
  > 2. yeah i'm not sure what this means precisely but ..... isn't it partially answered by my answer to #1? :) and for the other half of it, yeah.
  > 3. huhm do you think one loop would be burdensome?
  > 4. i like the web reader being inside the node / the node being selfcontained like that. it used to be an external python program which i didnt like at all.
  > 5. ok yes wipeandrebuild is fine
- **905fe751#7525 2026-10-11T18:28Z** "are we having fixed-size caches in places where they are too small to withstand our workloads and so we're constantly hitting every wall in the system? maybe we need to take a more fluid to it :)"
- **d0d33f7b#3857 2026-10-16T20:30Z** (the agent-facing interface) "this feedback must be about the side "Agent" interface and not the primary nntp one, right? i think we've probably neglected that for a long time. i dont particularly want to get distracted by it if we're busy with many other aspects of our development ... but it might be nice to revisit that and nuke the old system for a new better more intelligent system built on the primitives we actually have ..."
- **d0d33f7b#5857 2026-10-28T04:34Z** "like, what do you even think the major components of our software are right now? let's have a mental model quiz. no toolcalls, you need to do this one from recall :)"
- **d0d33f7b#5863 2026-10-28T04:37Z** (on the coordinator's answer "ACL2 decides and the host does I/O"; a pure step/state/event/effects model):
  > "decides and the host does I/O" ok first off why don't you actually go look at our IO/storage model? you'll see that it's HIGHLY represented in ACL2, that we explicitly attempt to reasona bout it, and the very first line you wrote is already garbage. Regarding pure step/state/event/effects: is **this** why we're fundamentally bottlenecked on the performance of our software?  are you familiar with "tigerstyle" from tigerbeetle etc? there are definitely better ways to be doing this lmaoooo.
  >
  > Your idea of the "components, as you hold them:" do you even have any idea what the interfaces of the components even are?
- **d0d33f7b#5889 2026-10-28T04:41Z** "This software can be great but we need an extremely methodical approach to actually take it there, and it needs to be from the bottom up ..... so that it's actually comprehensive and not piecemeal...."

**Mind changes.** (a) *The step-function model.* On 10-09 ember engaged the "one step function, one owner, one lock" draft without objecting to its spine, asking only about threads, the extractor and "one loop". On 10-28 ember asks whether "pure step/state/event/effects" is *why* fn is bottlenecked, and points at TigerStyle. The 10-28 turn is the later word: fn2 must not assume the pure step/effects split is settled; it is under question. (b) *"ACL2 decides and the host does I/O"* is rejected as a description: the I/O and storage model is itself represented and reasoned about in ACL2 (10-28). (c) *Threads.* "a smarter kind of multiplexing than thread-per-connection" (09-26), then "a nice, parsimonious, good multithreaded impl" (10-09): not thread-per-connection, but multithreaded. (d) *Web.* "web later" (09-19) became "the web reader being inside the node" (10-09); the constant is "not Python".

## 3. Performance, mechanical sympathy, memory

Representation turns (octet lists, stobjs, "byte work per octet", "accidentally quadratic", "streaming views over storage") are in REPRESENTATION-HISTORY §1 rows 2-21 and are not repeated. What follows is the performance *method* and the memory *target*.

- **997a44b0#1462 2026-09-26T14:49Z** "why are we sstill obnoxiously inefficient....??? we need to address that 100s store open and the other issues as well!!!! or unless that is proving time and not runtime 😂"
- **997a44b0#1766 2026-09-26T19:50Z** "i'm trying to keep memory usage deeply under 256MB. i consider it unreasonable that more than like a few dozen MB is needed at all, but yeah. :)"
- **1db4b0cd#1320 2026-09-26T23:43Z** "what is holding this back from being a lightning-fast, mega-scalable, crash-resilient implementation? :D"
- **1db4b0cd#5036 2026-09-27T18:55Z** "is there any way possible to get the heap to be only like 10MB plus whatever data arena...?"
- **1db4b0cd#5608 2026-09-27T21:47Z** "are we required to use sha-256? blake3 is usually considered the fastest good hash these days. and also we should be doing it in a faster way lmao we can figure something out here."
- **b53753a1#1340 2026-09-28T21:35Z** (compression) "uhhhh there's gotta be some kinda extremely high performance / modern approach to this that is both pleasingly simple for us to implement and high performance to compile from lisp? or something? otherwise i guess we can pull in some C code i dont really mind that. having the store be compressed in some way also seems extremely wise?" · **#1361** "ok well we can use RFC algorithms but also we should just publish our own extensions and use better algorithms. lol." · **#5038 2026-09-29T06:25Z** "ugh again with the deflate drama. uhhh if we can have an extremely high performance once in lisp that's fine, otherwise i don't mind using zlib or whatever."
- **700aaf5a#1212 2026-10-01T19:45Z** "can we do an audit for other algorithms that should be incremental or in place or intrusive or whatever"
- **be1e9dcf#4425 2026-10-07T01:53Z** "hmmm i want to count the SBCL core as well because 128MB means ...128MB! eg for tiny VPS or a shared already-burdened rpi; you know? it does seem like we could be doin somethin to improve it up right? :) and even shrink THAT baseline. (after all we're basically just streaming views over storage). / i kinda wonder how our traversal, storage, and other patterns compare to what postgres's query planner would do to these problems :)"
- **be1e9dcf#6691 2026-10-07T22:50Z** "btw .... does our heap usage be approximately at most logn with regards to the store size? what is the actual split between memory, disk, heap, datastructre, and soforth ...? as utilization ranges?"
- **be1e9dcf#7978 2026-10-08T11:17Z** "we're hyperfixated on these memorygoals probably because they feel achievable. but they aren't actually important right now compared to uhhhhhh "making the software not shitass""
- **905fe751#2819 2026-10-10T15:17Z** "what's up with the "cores own pages" regarding the 128MiB bar...? we should keep the target but like is this because extraction isnt working or something?"
- **905fe751#7460 2026-10-11T18:13Z** "Huhm file-backed pages, those are just part of the page cache and get evicted from residency when there is any kinda pressure, right? I feel like... i am willing to discount those :) because demand-paging is just THAT good."
- **905fe751#8740 2026-10-12T08:56Z** "while we're in there planning what we can be dong to massively 10-100x the perf of this whole thing because ... modern computers are hella fast lmao ... and this software is Chuggin."
- **905fe751#11477 2026-10-12T19:37Z** "just glancing through the logs im worried we're "gradientchasing" rather than thinking holistically about what would make the system better. sometimes we dont need to witness the entire local path of improvements !"
- **905fe751#11483 2026-10-12T19:38Z** "it seems we've been doing a lot of our perf work concretely, which makes sense, but ultimately we should be analyzing in terms of iop and other count, locality, burstiness, the way it layers with the filesystem and operating system ........ right? :)"
- **905fe751#11513 2026-10-12T19:41Z** "excellent. NOW it sounds like we'll be able to do this scientifically instead of pseudoscientifically ;) and also take "nonlocal leaps" intot he "best identified perf basin" instead of just exploring local perturbations to the software."
- **905fe751#11826 2026-10-12T20:59Z** "we dont need to actually FULLY SYNC EVERY TIME ALL THE TIME in prod. it's kinder to not." (said of hbox syncing, not of the store's barrier; recorded because it is the only "sync" turn.)
- **d5d27b94#3856 2026-10-14T15:57Z** "we should stop grinding towards the memory bar. we've done amazing work. we should set guardrails to avoid bloating more than 50% from our baseline, but i think we need to just say "ok" for where we're at and pray that things get lighter as the software continues maturing."
- **d0d33f7b#5412 2026-10-27T21:15Z** "let's not worry about the memory inconsistency and tminings; i'm just hopeful we can keep doing more of the work we had identified so that if one were to use this software from the outside everything would work and be fast and use the pathways we're building and not legacy pathways"
- **d0d33f7b#5857 2026-10-28T04:34Z** "We've also become WAY too empirical/measurement-driven, over measurements that don't actually make much sense with regards to the ultimate composed system overhead&performance :)"
- **d0d33f7b#5863 2026-10-28T04:37Z** TigerStyle (§2).

**Mind changes on memory.** "deeply under 256MB ... a few dozen MB" (09-26) → "heap ... only like 10MB plus whatever data arena" (09-27) → "128MB means ...128MB!", the core counted (10-07, D69) → file-backed pages discounted (10-11) → "stop grinding towards the memory bar", guardrail +50% (10-14) → "let's not worry about the memory inconsistency" (10-27). The *target* was relaxed; the *architecture* sentences (log n heap in store size, streaming views over storage, the core baseline shrunk) were never withdrawn. **On method**: from measuring every change (09-2x) to "analyzing in terms of iop ... locality, burstiness" and "nonlocal leaps" (10-12) to "WAY too empirical" (10-28). fn2's performance design is argued from first principles (I/O counts, locality, the OS layering) and measured after, not discovered by measurement.

## 4. Storage, durability, the crash model, format, migration, wipe

- **01a0b33a#44 2026-09-18T06:41Z** "space age", "extraterrestrial operations, eg Licklider protocols" (§1). **#63** "a specialized-purpose storage layer just for what we need."
- **01a0b33a#97 2026-09-18T06:59Z** **[answer]** retention: "Keep until explicit authorized release; no automatic expiry (Recommended)" (D03).
- **418232ec#1632 2026-09-19T14:47Z** "The crash model definitely needs to be massively sophisticated, the present status is not acceptable at all." (§2)
- **771be5e0#2525 2026-09-22T16:17Z** "(What's the deal with durability/D14 ? is this something we can just address?)"
- **bbbe7a9b#1609 2026-09-25T02:16Z**
  > - what's up with our size caps, do we have the ability to let things be more ... 'unbounded'? does it come from config files? 
  > - not sure why we have fixed budgets of any kind
  > - we need to think about extending towards control messages
  > - we should revisit other aspects of the design that are leading to constrictions here
- **bbbe7a9b#1626 2026-09-25T02:20Z** (D27's source; the representation half is in REPRESENTATION-HISTORY) "We need to have fewer bullshit restrictions. Each of those is a branch that someday will fail during operation for no meaningful reason except durng development we were fearful and installed a footgun."
- **1db4b0cd#1329 2026-09-26T23:47Z** "there's no reason to have THAT level of redundant durability is there? ... there has gotta be a better/smarter job system / way of doing the whole durable storage thing." (§2)
- **1db4b0cd#2197 2026-09-27T03:09Z** "i wonder what the other options are durability architecture wise... are we smallbraining it somehow??"
- **1db4b0cd#2250 2026-09-27T03:28Z** "let's just deal with the fact that we won't be fully durable on openbsd idk.... also not sure what bug you want me to report... is this really a bug?"
- **1db4b0cd#4563 2026-09-27T16:15Z** "i do feel like we're still doing something extremely naive becaue what's up with checkpoint/replay performance...... alas."
- **1db4b0cd#4824 2026-09-27T17:47Z** "is it not possible to just store an image of our heap...??? i'm trying to understand. this serde shit is NOT houyhnhnm computing (https://ngnghm.github.io/blog/2015/08/03/chapter-2-save-our-souls/; https://ngnghm.github.io/blog/2015/08/09/chapter-3-the-houyhnhnm-version-of-salvation/)"
- **1db4b0cd#4833 2026-09-27T17:49Z** "Maybe we should be doing something on our own/lightweight instead of SBCL. that we can achieve using some (maybe only mildly invasive) macros... otherwise yeah i'm definitely interested in persistent arena typeish approaches and also being more Houyhnhnm"
- **1db4b0cd#4869 2026-09-27T17:57Z** (on the reply: a copy-on-write page store, the log as truth, the snapshot a cache of its fold, non-determinism recorded as events, no SBCL core snapshots) "now *that* sounds more reasonable. let's keep exploring and thinking a bit more."
- **1db4b0cd#4890 2026-09-27T18:00Z** "the log can contain configuration events that set seeds and nonces etc :)"
- **1db4b0cd#4774 2026-09-27T17:38Z** "a laggy/disk that needs maintenance is a real fact of life that we shouldn't sandpaper away with our model" (§2)
- **1db4b0cd#7760 2026-09-28T15:32Z** "aye. we can feel free to throw away /migrate the old nodes if we wish :)"
- **1db4b0cd#7995 2026-09-28T16:40Z** "btw what's the deal with "format 10" and stuff like that? / I feel like w eshould refactor our code to collapse all that into only supporting a single format ...?? what do you think. (this would be probably one of the last things we do before cutting 6.6.0)"
- **b53753a1#46 2026-09-28T16:56Z**
  > there are no such thing as future migrations :) when we cut 6.6.0 will be the first time that anyone else uses this, and we'll be redeploying all our nodes.
  >
  > ideally we would be tidying up our code to remove all legacy/prototype format support and attendant migrations, so that the code is as simple as possible.
- **b53753a1#1922 2026-09-28T23:03Z** "do we have actual worst-case bounds on resource consumption and soforth? like this is an enforced and deterministic property of this system under load? it could "have a warranty"?"
- **b53753a1#3730 2026-09-29T04:13Z** "what else could we move into pages? i feel like more on-disk datastructures is actually extremely wise and smart."
- **9627d694#1312 2026-10-04T01:59Z** "redeploy: bro these "deploys" are not as big a deal as you think they are. they are just toys. take em down, bring em up, whatever. don't leave old code running though."
- **be1e9dcf#4493 2026-10-07T02:13Z** "we do not have any migration or compatibility concerns :) the software has genuinely never been used by anyone but us and we plan to wipe & rebuild all public nodes..."
- **35f3668a#1588 2026-10-09T04:31Z** "5. ok yes wipeandrebuild is fine"
- **d0d33f7b#5090 2026-10-27T18:37Z** "yes to all three. sounds promising." (to the M2 plan's three product changes: reads verify once; a damaged newer checkpoint refuses open instead of falling back; live reclaim becomes segment cleaning)
- **d0d33f7b#5907 2026-10-28T04:56Z** "like, we're not convinced that our crash model is actually an appropriate model of the OS or hardware, and we should make sure that our crash model is "more tough.""

**Through-line and changes.** One format, no migrations, no reader of a previous format, wipe and rebuild (09-28, 10-07, 10-09; D34, D38 withdrawn, D68). The persistence model is Houyhnhnm: no serde, the on-disk structure is the in-memory one, the log is truth with nondeterminism as events (09-27). The crash model must be "massively sophisticated" (09-19) and, a month later, "more tough", because ember is "not convinced" it models the OS or hardware (10-28): the crash model fn has is not the one fn2 inherits by default. One relaxation: OpenBSD durability is documented, not engineered around (09-27). Durability's cost was questioned ("THAT level of redundant durability", "smallbraining") and never ratified as necessary.

## 5. Metaprogramming, generators, extraction, the runtime image (bare SBCL, fn-core)

- **990cbaad#20 2026-09-19T18:10Z** "ok wow the proof engineering was really bad. no wonder we're macroscopically struggling! we'll need to do some serious heaving to get this system realigned starting microscopically and all the way up to the macroscale."
- **771be5e0#2052 2026-09-22T14:09Z** ""A full closure certifies in about twenty minutes" that's .... unacceptably slow? I feel like we're doing our proof engineering all wrong, that there is somewhere supposed to be some abstraction/refinement boundary that keeps things snappy most of the time."
- **997a44b0#1784 2026-09-26T19:52Z** "Uhhh so, what's up with the idea of exporting into plain SBCL and soforth. like what's actually going on. please send a subagent to investigate and see what we cand o differently because i feel like we're getting caught up in misconceptions."
- **1db4b0cd#4833 2026-09-27T17:49Z** "Maybe we should be doing something on our own/lightweight instead of SBCL. that we can achieve using some (maybe only mildly invasive) macros..." (§4)
- **1db4b0cd#5056 2026-09-27T18:58Z** "i honestly love the idea of extract something. is it possible for us to use chicken scheme or something like that that is really epic???????? it's fine if not. / i am EXTREMELY curious what we can do with metaprogramming and this whole thing tho. :)"
- **1db4b0cd#5988 2026-09-27T23:02Z** "or what still remains partial in everything we've done, or could be massively simplified AND improved via metaprogramming"
- **1db4b0cd#6215 2026-09-27T23:35Z** "i wish we could delete more of the python :) like maybe 1/3-1/2 of it overall.... sortening up ... tidying tightening metaprogramming ... moving things to lsip.."
- **b53753a1#500 2026-09-28T18:11Z** (no ACL2 patch) "uhhhhhhhhh yeah i don't think we should do that lmao. / isn't our book organization kinda insane anyway?"
- **b53753a1#1457 2026-09-28T21:52Z** "aren't there other implementations that could be faster than chicken that we could equally extract to? or loke, somehow compile with sbcl, idk i'm just imagining our options here. trying to keep things slim though."
- **b53753a1#1463 2026-09-28T21:57Z** "ok. (is chez faster than chicken? should we just use that? (surely the shims we already have arent hard)) or ... idk. an SBCL core is probably the best idea... (cakeml is out)"
- **b53753a1#1896 2026-09-28T22:57Z** "this is going great :) especially the python diet, the generators, etc..."
- **adb603dc#258 2026-10-02T03:09Z** "has the software been getting simpler while it grows more powerful or are we well overdue for another pass trying to understand how to do more metaprogramming?"
- **700aaf5a#2404 2026-10-02T03:17Z** "but yeah we really do have a lot of repetition that really we should NOTICE that we are repeating when we do it, and think "shouldn't this be a macro?""
- **adb603dc#2199 2026-10-03T02:21Z** "how many of these items indicate we should just rebuild a subsystem from better macros & assurance teks to begin with...?"
- **01a0fe41#5051 2026-10-03T11:46Z** "(macros macros macros!!!)" · **#8861** "also if any come up with great ideas for macros they should go ham"
- **be1e9dcf#4275 2026-10-07T00:23Z** "I think we probably should be adapting the generators ro something right?? because without simplifying these things we'll never actually finish the project. / I think we should just have bare-SBCL if there is maintenance burden regarding the two extractors." (→ D62, D63)
- **be1e9dcf#4618 2026-10-07T03:09Z** "yes i do agree extraction is going to be the best call, although it will work *alongside* our other improvements that we are doing, and doesn't displace them, do you agree?"
- **be1e9dcf#4849 2026-10-07T04:33Z** "we aren't editing each of hundreds of sites manually write? we need to be using our lisp gigabrain and write and apply program transformations and build our own refactoring tools or use ast-grep or . etcetcetcetcetc."
- **35f3668a#1565 2026-10-09T04:21Z**
  > alright. now, we'll probably be able to reach deeep into our mind, maybe review and ground that stuff, and think really really hard about "how can we make this a mechanically sympathetic Good and Nice Concrete Implementation" that also has good assurance because it is "simple enough to be correct and fast" while also relying on as much linguistic metaprogramming as we need to not drive ourselves crazy, while also having a broad and wide base of assurance built within acl2 ........ :)
- **35f3668a#1588 2026-10-09T04:31Z** "do we really need to be using ACL2's runtime if we have an extractor and the "official" version has extremely expensive per-thread overhead...??" and, to "fn-core stays the shipped artifact": "isn't it partially answered by my answer to #1? :)" (§2)
- **905fe751#2886 2026-10-10T15:20Z** "uhhh "why are we extracting so much" like so much of the acl2 definitions have gotta be useful only for the proofs right? like whats the actual formal symbolic critical path thru...."
- **d0d33f7b#5907 2026-10-28T04:56Z** "i'm feeling kinda hopeful that we can come up with some metaprogramming approch that lets us express the whole thing very succinctly" (§1)

**Mind changes on the runtime.** Lightweight non-SBCL via macros (09-27 17:49) → CHICKEN extraction "really epic" (09-27 18:58) → "an SBCL core is probably the best idea" (09-28) → "bare-SBCL if there is maintenance burden regarding the two extractors" (10-07; D63 deletes CHICKEN) → "do we really need to be using ACL2's runtime if we have an extractor" (10-09) → "why are we extracting so much ... whats the actual formal symbolic critical path" (10-10). Settled at the latest word: one extractor to bare SBCL, extracting only the executable critical path, the shipped artifact not paying ACL2's runtime (per-thread overhead) where it can be avoided. **On generators**: constant since 09-27 and twice ratified (D41, D62): the answer to repetition is a macro, and simplification by generator is the condition for finishing at all.

## 6. BP and DTN, peering, consumers and agents, 9P, applications (helm: none)

No fn turn of ember's names helm. The agent-facing intents are "sleeping agents", consumers, the "Agent" interface and the dregg/robigalia substrate (§1).

- **01a0b33a#4618 2026-09-18T11:45Z** "btw did we end up doing anything with the bundle protocol? how are we along our pathways? functionalities? assurances?"
- **01a0b33a#4632 2026-09-18T11:46Z** "well ... "future BP adapter.." isn't the what BP enables, absolutely vital to *how we wanna be doing it*? :)" → **[decision row]** A06 (2026-09-18): "its disconnected store-and-forward capabilities are central to fn."
- **418232ec#1632 2026-09-19T14:47Z** "Yeah lmao we need to not be doing this DTN/BP theater, we need to come up with a real design." (§2)
- **771be5e0#2525 2026-09-22T16:17Z** "Q1. Yes, DTN is supposed to be part of v0, it's a crucial part of the multi-agent architecture that will be built on top of it. / Q2. I do kinda would prefer native author signatures ... Q5. Let's put off LTP for now I suppose, makes sense to put after DTN. ... Q8. Bro you do not actually need two separate machines to test the peering but feel free to do that."
- **01a0b33a#21358 / #21368 / #21387 2026-09-23T14:18Z** **[answers]** sleeping-agents receipt/reply; consumer-owned inbox/outbox with an fn cursor/ack contract; separate stores with explicitly trusted transport peers (§1).
- **bbbe7a9b#971 2026-09-24T21:56Z** **[answers]** "Carrier allowlist (Recommended)" (D23), "Carried guard (Recommended)" (D24), "Poster's bytes (Recommended)" (D25), "2-job scoped runs (Recommended)" (D26).
- **[decision row]** 2026-09-27 01:56Z (in the 09-28 register): "we will not be doing any TCPCLv3 yet, we can just wait right..?"
- **[decision row]** PKT-642 2026-09-27 (in D-register's 09-23 entry): "seems reasonable, re identity / login bound" (a consumer bound to the agent's account).
- **b53753a1#1048 2026-09-28T20:50Z** "we're gonna be peering with SOMEONE eventually but not immediately :) (it will be the openbsd node tho probably)"
- **01a0eeec#4130 2026-09-30T00:56Z** **[answer, ember's own text]** to PKT-673 (remote consumer): "Yes—add authenticated remote access scoped to the account; keep operator controls private."
- **01a0eeec#26424 2026-09-30T20:28Z** "bpsec/ltp/subsstrate/9p work – we have agent sltos dont we? why not just issue some work thru that..?"
- **9627d694#1748 2026-10-04T03:37Z** "huhm maybe we shouldnt push that remote consumer to 6.6.1; wanna pull it forward? gates-with-producers is always better than putting-into-backlog,."
- **9627d694#2507 2026-10-04T08:15Z** zmq-shaped surface in 6.6.0 (§1); **9627d694#1312** "the redis of it all" for 6.6.1 (§1).
- **9627d694#3006 2026-10-04T14:54Z** "lets make sure we take as a particular focus anything we can improve now to make everything serve, all peering and soforth."
- **be1e9dcf#6513 2026-10-07T22:21Z** "regarding 9p –  did ewe ever really get started on that line of work? also private-group is not a priority at all right now, i'm pretty sure that would be layered on at a much later point tbh (unless we already have a lot of progress on it?) / regarding substrate and observability - did we never ever start on that? it feels like it would have helped a lot with our development ...."
- **35f3668a#1445 2026-10-09T03:52Z** "BP is product."
- **35f3668a#1588 2026-10-09T04:31Z** to "BP's transports in the one loop or a second": "huhm do you think one loop would be burdensome?"
- **d5d27b94#2342 2026-10-13T23:28Z** "i'm hoping to get 6.6.0 eventually cut, and especially fn.fg-goose.online redeployed, all of our peering things buffed up massively."
- **d0d33f7b#3857 2026-10-16T20:30Z** the "Agent" interface: "nuke the old system for a new better more intelligent system built on the primitives we actually have" (§2).

**Through-line.** BP/DTN is not an adapter: it is how fn is meant to work (09-18), v0 (09-22), and "product" (10-09). Peering must be "buffed up massively" (10-13); the first real peer is "the openbsd node tho probably". Consumers are the agents' interface: consumer-owned durable progress, bound to the account, remotely usable with account credentials, built with its producer. 9P was in the founding instinct (09-18 Discord) and never started (10-07). Private groups: designed for (D04) but "layered on at a much later point" (10-07).

## 7. Assurance: semantics-first, teeth, keystones, seL4, what proof is for

- **01a0b33a#6490 2026-09-19T00:27Z** "(But I'm also concerned that as we continue expanding the frontier of feature development and flesh fn out towards "initial completeness"  that we're also expanding the assurance !)"
- **b3f4abb5#265 2026-09-19T02:20Z** "huh maybe we uhhh have some naiveties in the model that need to be seriously addressed before we think we have an actual high-assurance nntp + bp going on :)"
- **418232ec#1632 2026-09-19T14:47Z** "not setting up "strawmen disproofs" ... the functional correctness things we're proving about our node are *eventually* capable of chaining into something /like/ a Universally Composable framework ... Especially as a server we need to know "clients cant crash us regardless of what they send us" and as a server that we appropriately implement semantics." (§2)
- **01a0b33a#7331 2026-09-20T19:02Z** "- is ACL2 being used effectively? / - are we actually making progress towards a high-assurance NNTP? / - what *is* assurance, for such a usecase? / - how does this establish verified infrastructure for humans and agents to share and benefit from?"
- **01a0b33a#34778 2026-09-24T03:54Z** "btw what does our actual assurance story look like right now? what properties are we demonstrating, why do we trust the argument that they hold, and do these properties actually matter to the end-status of the entire system?"
- **1db4b0cd#4719 2026-09-27T17:10Z** "so ... what more known bugs do we HAVE in our software? or known missing features or mistranslated aspects? / like what did this 'assurance' methodology actually Gain us"
- **b53753a1#2944 2026-09-29T02:30Z** "WELL SIGHTED though! finding and removing bugs like that is why we use the methodology that we do." · **#2992** "what missing statement did we have that let this slip past our proofs? what other missing statements should we try and demonstrate?" · **#3201** "we should write some coverage-crawling tool that is actually precise and figure out what is said about what symbols, so we can know which symbols eg aren't mentioned by eg storage-consistency proofs, or something like that..?"
- **01a0eeec#30494 2026-09-30T23:56Z** (EMBER.md) "btw how do we have confidence that we've actually implemented everything correctly? the proofs are only about the proof statement. do we have differential and interoperability testing with other implementaitons?"
- **adb603dc#976 2026-10-02T22:18Z** "our assurance story must not be very convincing if we still are finding LOCKING ISSUES, like how do we not have whole-system compositional correctness statements yet..?" · **#1482 2026-10-02T23:10Z** "why AREN'T we doing full-system theorems... like why is it only about the decisions? and not about the aspects that are vitally important too..... is it beyond the ability of acl2 to model and demonstrate...?"
- **adb603dc#2736 2026-10-03T02:53Z** "i'm wondering if we can focus our efforts on at least getting the *semantics and behavior* of everything, right. this may mean doing some/most of the "native rewrite", and other things like that ... and sprinting past the assurance for a bit. i kinda want this server to be in place and functioning as we improve its other aspects"
- **be1e9dcf#4275 2026-10-07T00:23Z** "regarding teeth and everything else it's important to get the software like ....  working. and then also correct/proven ;) :D sometimes we shouldn't do those at the same time !!!!" (→ D66)
- **be1e9dcf#7823 2026-10-08T10:31Z** "when we actually put this thing through a gauntlet, are we getting everything we would want to ensure that "if the tests pass, then it is suitable for use in prod" type of things?"
- **35f3668a#1311 2026-10-09T02:50Z** "some of these "competing representations" (a lot of them DO just need to be deleted) were originally designed to make the refinement proofs easier...."
- **35f3668a#1451 2026-10-09T03:53Z** "Also. sel4 was like 10k lines of logic and was like many hundreds of thousands of lines or proofs. so."
- **35f3668a#1466 2026-10-09T03:55Z** "right. we definitely need to be simplifying and reducing duplication and unnecessary conceptual multiplication; just because we expect to have a lot of proof per logic doesn't mean we need to go about it foolishly. in fact, the task is SO challenging that unless we go about it quite intelligently, we will literally never finish it :)"
- **35f3668a#1565 2026-10-09T04:21Z** ""simple enough to be correct and fast" ... a broad and wide base of assurance built within acl2" (§5)
- **905fe751#207 2026-10-09T23:30Z** "are we actually able to PHRASE any of the statements like "no possible network / io activity causes heap explosion / DoS / etc"?"
- **d5d27b94#3816 2026-10-14T15:55Z** "it's important to get the system "running and tested" classically before spending too too much effort on assurance, because the software is a moving target, and the proofs are expensive as hell. ... and the assurance isn't a *major* focus until the 5.4 series..."
- **d0d33f7b#4950 2026-10-17T04:29Z** (on deleting the proof-bookkeeping apparatus) "let's cut it then. we only need to demonstrate that our TOPLEVEL THEOREMS aren't vacuous, the rest of them fall from use via that (and if the lemma is vacuous, well, that's just an ugly code/argument problem, not the end of the world)"
- **d0d33f7b#5907 2026-10-28T04:56Z** "yeah. i feel like our fn2 we should be *semantics-first* and not worry as much about the proofs until we've actually gotten the implementation into a state where we WANT assurance from it .... although we did surely learn a LOT of lessons from this development."

**Mind change, the largest one in the record.** 09-19 to 10-02: assurance expands with features; whole-system compositional theorems are demanded ("why AREN'T we doing full-system theorems"). From 10-03 ("sprinting past the assurance for a bit") through 10-07 (working, then proven; D66), 10-14 ("running and tested classically"; not major until 5.4), 10-17 (only toplevel theorems need be non-vacuous; the bookkeeping apparatus cut) to 10-28 ("semantics-first ... until we WANT assurance from it"). What did not change: the *kind* of statement wanted when assurance comes: whole-system, compositional (UC-like), "clients cant crash us", "no possible network / io activity causes heap explosion / DoS", worst-case resource bounds as a warranty, no strawmen, no vacuous toplevels. And the seL4 ratio (10k logic : hundreds of thousands proof) is ember's own frame for how small the logic should be.

## 8. Observability, operability, testing

- **418232ec#1632 2026-09-19T14:47Z** no compiled-in configuration; "assured live reconfiguration" (§2).
- **01a0eeec#32013 2026-10-01T01:15Z** "are we doing a lot of foolish qualification things when we should be focused on building out more infra and capability into the software? how is the observability, traceability, and debuggability of the server?"
- **b53753a1#2517 2026-09-29T01:26Z** "btw do we have a testsuite that `curl` can successfully do everything we think we support? might be a good suite for a subfable."
- **01a0fe41#1058 2026-10-03T06:14Z** "i'm also curious to have a deputy who is in charge of making comprehensive simulation/scenario tests that we can load fn under to get substantial empirical measures of performance, resilience, etc..."
- **01a0fe41#6048 2026-10-03T12:55Z** "a VERY ROBUST suite of dev/internal commands that let us access alla tha things. and honestly we should probably be able to pop open a repl into a running one, eh??? / but also what's yeah we can be putting the tracing more to use"
- **be1e9dcf#6513 2026-10-07T22:21Z** "regarding substrate and observability - did we never ever start on that? it feels like it would have helped a lot with our development ...."
- **be1e9dcf#7823 2026-10-08T10:31Z** "if the tests pass, then it is suitable for use in prod" (§7).
- **be1e9dcf#7937 2026-10-08T11:09Z** (EMBER.md) "this software really really isn't ready for a soak ;) it has so many concrete problems! and many of them we can tell just by looking at the code"
- **be1e9dcf#4949 2026-10-07T04:46Z** (EMBER.md) "we find bugs by debugging, tracing,  and source inspection in this house."

**Through-line.** Observability, tracing, a REPL into the running node and a rich internal command set are things ember asked for and found never started (10-07). fn2 should have them from the start, since they are how this house debugs.

## 9. Cryptography and identity

- **01a0b33a#116 2026-09-18T07:04Z** "i don't wanna include a naive or shitty cryptosystem, i want it to be *good*."
- **01a0b33a#192 2026-09-18T07:31Z** "MLS would be the most obvious thing, although the requirements are pretty harsh and im not sure its actually the cryptosystem for us ....... something completely different (niche/novel-on-eprint(i dont know of one but thats what im thinkg abt)) or idk...."
- **01a0b33a#96 2026-09-18T06:59Z** **[answer]** "Native author signatures plus legacy gateway provenance (Recommended)" (D02). **#7289 2026-09-19T01:37Z** **[answer]** "Yes, exact source bytes plus separate projections" (D01).
- **418232ec#1632 2026-09-19T14:47Z** "Authority being noncryptographic is acceptable."
- **01a0b33a#16532 2026-09-21T16:31Z** **[answer]** "Require both from the first release for long-lived authenticity" · **#16541** "Yeah also PQ :) it's fine." (D09: Ed25519 and ML-DSA-65)
- **997a44b0#1611 2026-09-26T18:07Z** "is there ANY alterantive to using the entirety of openssl here?? fine whatever, at least it is C."
- **1db4b0cd#6270 2026-09-27T23:41Z** "bro bad call. i don't mind pulling in a blake3 c library. i STRONGLY DISPREFER the legacy SHA."
- **be1e9dcf#4275 2026-10-07T00:23Z** "regarding the contractions: we don't care about openssl lets just do something that makes sense and do it everyhwere; we probably need to be shipping our own thing so that the postquantum stuff actually works..." (→ D64)

**Mind change.** System libssl accepted grudgingly (09-26, D35) → ship our own crypto everywhere so the post-quantum suites work (10-07, D64). The cut brief's survivor "TLS with our own crypto" is this sentence.

## 10. Versions (5.1.1 ... 6.7 ... 6.6.x ... 6.6.6)

- **990cbaad#1779 2026-09-20T02:05Z** "to me v1 means M6 (and even a bit more beyond that) ... to me v0, the very first one we share, still requires us to be able to use *all* features between two peered fn servers..."
- **1db4b0cd#1888 2026-09-27T02:22Z** "i'm contemplating what it would be to cut a v6.7.0 of this software. (all versions of fn will be v6.7.xyz)" · **#1932 2026-09-27T02:28Z** "hmm. lets not cut the v6.7.0 for friends yet. i'd prefer to address these tough aspects. heh. it's actually in really "chopped" shape, in terms of the fundaments."
- **1db4b0cd#5634 2026-09-27T22:01Z** "actually i'd like to make our first version v6.6.0 .... and then we'll work our way up to a v6.6.5 release, then we'll have a v6.7.x series, and then the final release (whenever that is) of the software would be v6.6.6. and then each new release would add another .6. that's my intention." (D37)
- **1db4b0cd#6071 2026-09-27T23:15Z** "(we don't have to wait until after the cut ! i'm gonna hold off the cut for a decent amount of time)"
- **b53753a1#98 2026-09-28T17:01Z** "i'm curious to issue a subagent that goes through and tags a v1.0.0 through v5.0.0 releases, at points along the git commit history that are reasonably meaningful / phase shifts in the development"
- **b53753a1#880 2026-09-28T20:21Z** "id on't want to defer any of the major work we've identified .... i ideally  would like to complete th eowkr ! get it all on dev. get everything gucci. *and then* we can cut 6.6.0. it isn't a race :)" (D39)
- **9627d694#2507 2026-10-04T08:15Z** "6.6.0 is *for* being good enough to start treating as a foundational component for the rest of the distributed OS / mini." (D49)
- **d5d27b94#3816 2026-10-14T15:55Z** "i'm thinking a 5.1.1 would be called for "eventually" (lmao) because we stil have a long to go before our v6. the next versions will be 5.2.2 5.3.3 5.4.4 5.5.5 6.7. ... and the assurance isn't a *major* focus until the 5.4 series..."
- **d0d33f7b#3229 2026-10-14T18:25Z** "regardding the 6. series, i do still wantt o do that series, it's just that we're not ready for 6.6 and we're gonna have a long way to go. the 6.6 series actually comes chronologically *after* 6.7, and represents the "landing sequence" of the plane / finalization of the project, in a way .... yes it is strange, but it's how this project will be doing it."

**Mind changes.** "all versions of fn will be v6.7.xyz" (09-27 02:22) → "first version v6.6.0" (09-27 22:01) → (D67, coordinator-written, 6.6.1-pre) → 5.1.1, 5.2.2, 5.3.3, 5.4.4, 5.5.5, then 6.7, with 6.6.x as the landing sequence after 6.7 and 6.6.6 final (10-14). The last is in force. fn2's first release is a 5.x; assurance becomes a major focus at 5.4.

## 11. How to change the system: replace, delete the twin, fix forward, bottom-up (architecture-relevant process only)

- **01a0b33a#7941 2026-09-21T06:01Z** the "Twin problem" (§2).
- **990cbaad#2302 2026-09-20T03:30Z** "red merges aren't a huge deal to use, we just converge-forwards, that's fine."
- **01a0eeec#31699 2026-10-01T00:58Z** (EMBER.md) "maybe construct hte new dserver instead of trying to edit some of the old/bad code...?"
- **01a0eeec#36375 2026-10-01T04:58Z** (EMBER.md) "our software makes no sense to navigate and it's impossible to see the actual architectue in the pile"
- **f84a8f40#1481 2026-10-01T10:36Z** (EMBER.md) "also we need to avoid doing reverts in the future just because they alleviate our anxiety about the color. fixing forward is the way forward....... otherwise we're regressing from what is possible..."
- **adb603dc#2660 2026-10-03T02:42Z** "it's not clear whether we should try and burn down what we identify as a workqueue or whether we should try and rebuild the new system from the ashes."
- **9627d694#1312 2026-10-04T01:59Z** "i am extremely NOT in favor of doing ANY reverting or requiring full proofs before replacing old things. i want to just put in the new code, and eventually fix forward."
- **be1e9dcf#8659 2026-10-08T23:10Z** (EMBER.md) "at this point do we just need to let our worker queues drain, and then freeze the project for like, entirely being architecturally rethought and rewritten ?"
- **35f3668a#1377 2026-10-09T03:40Z** "do we need to just ... "collapse the ladders" ? also the 'dead weight' maybe things that we **want and still need to wire up**.... but yeah.... we definitely have some purifying light to cast."
- **35f3668a#1497 2026-10-09T04:11Z** "yeah lmao we're surely able to do some major surgery here on this organism. major major surgery. without even really impacting the final delivery!"
- **905fe751#13287 2026-10-13T03:39Z** (EMBER.md) "we've never managed to EVER start on the actual rip and tear part of the plan, despite that being our intention for several days now :) are we just stuck in an attractor?"
- **d0d33f7b#4307 2026-10-16T22:04Z** "our software is a trashfire by now, so many layers of old shit that never got removed while i was begging for it to be removed.  i feel like we need to rip and tear our software .... it got so bloated .... we need a different factoring and we'd have the same (BETTER, actually) functionality/end-computing-system with so much less bullshit"
- **d0d33f7b#4389 2026-10-16T22:21Z** "i think we just have too many tombstones in this project to easily make progress. but yeah i feel like we had been working towards a higher-performance mental model and that was showing up in the code in various ways and actually simplifying a lot of code too but we had some kind of obstruction actually pushing it through"
- **d0d33f7b#4525 2026-10-16T23:47Z** "yes. approved. go. M2 whole. we will improve-forward."
- **d0d33f7b#5061 2026-10-27T18:18Z** "i don't want to become myopic and cut scope just to get something out the door."
- **d0d33f7b#5262 2026-10-27T20:02Z** "ok well let do the engineering necessary to keep ripping and tearing. that may mean building out a bunch of foundational stuff!"
- **d0d33f7b#5412 2026-10-27T21:15Z** "use the pathways we're building and not legacy pathways and use those as wedges/levers to carve away improvements to this system"
- **d0d33f7b#5889 2026-10-28T04:41Z** "it needs to be from the bottom up ..... so that it's actually comprehensive and not piecemeal...."
- **d0d33f7b#5901 2026-10-28T04:42Z** "do we want to rebuild a fn2 inplace here that we eventually swap over the root of the repo to? or do we think it's achievable to do this mostly-in-place..."
- **d0d33f7b#5993 2026-10-28T06:18Z** "before that and while we still have so much context in our window, we should gather EVEN MORE CONTEXT so we can go back and forth on a completed design ..."

**Mind change.** "rebuild the new system from the ashes" was asked as a question on 10-01, 10-03 and 10-08 and each time answered by in-place work; the breaking cut (10-16) was in place; fn2 (10-28) is the first time the rebuild is chosen, bottom-up, with a "completed design" gathered first. The constant: the new path replaces the old one and the old one is deleted, never twinned; no reverts; fix forward.

## 12. The decision register at origin/dev (`planning/decisions.md`), one line each, with a keep verdict for fn2

Source column: **E** = ember's own words decide it; **E-r** = ember ratified a coordinator/GPT-6 recommendation ("inclined to take your recommendations", "feeling good about the other decisions", an [answer] to a recommended option); **C** = coordinator or lane ruling, no ember text (the register itself says so). Verdict: **KEEP** (fn2 adopts the decision as stated), **AMEND** (the intent stands, the stated mechanism changes; the reason is given), **RE-DERIVE** (an engineering decision about the old tree's mechanism; fn2 decides afresh under the same intent), **DROP** (process, superseded, or about deleted machinery).

| ID | date | src | gist | fn2 |
|---|---|---|---|---|
| A01 | 09-18 | E | serves human and AI communication; NNTP the initial news interface | KEEP |
| A02 | 09-18 | E | executable ACL2 semantics; meaningful proofs of the running core | AMEND: semantics-first, proofs when wanted (d0d33f7b#5907) |
| A03 | 09-18 | E | specialized persistent store: immutable objects, local transactions, recoverable state | KEEP |
| A04 | 09-18 | E | retention/delivery obligations explicit and persisted with content | KEEP |
| A05 | 09-18 | E | sites useful while disconnected; batches by network or carried media | KEEP |
| A06 | 09-18 | E | BPv7 disconnected exchange is central, not an adapter | KEEP ("BP is product") |
| A07 | 09-18 | E | substantial design up front, staged implementation, evidence distinct from intent | KEEP (the fn2 design-first mandate) |
| D01 | 09-18 | E-r | sign exact authored source bytes; Path/Xref/injection in separate projections | KEEP |
| D02 | 09-18 | E-r | native author signatures plus legacy gateway provenance | KEEP |
| D03 | 09-18 | E-r | keep until explicit authorized release; refuse new obligations at capacity | KEEP |
| D04 | 09-18 | E-r | shared groups first; design privacy boundaries now; protocol open | KEEP (private groups "much later", be1e9dcf#6513) |
| D05 | backlog | proposal | first release = READER + mandatory + POST + OVER, unmoderated groups | KEEP as the floor (v0 = all features between two peered nodes, 990cbaad#1779) |
| D06 | backlog | proposal | journal/checkpoint authority with rebuildable in-memory indexes | AMEND: pages are the state, on disk = in memory (D41, 1db4b0cd#4824) |
| D07 | 09-21 | E | native Lisp deployment executing ACL2 definitions; no Python in the node | KEEP (with D63: bare SBCL, extracted) |
| D08 | backlog | proposal | restricted deterministic CBOR, exact schema versions, bounded parsing | KEEP direction; versions carry no compatibility duty (D68) |
| D09 | 09-21 | E | Ed25519 AND ML-DSA-65 required; no classical fallback | KEEP |
| D10 | backlog | proposal | local counters, origin incarnations, causal refs | RE-DERIVE |
| D10-a | 09-21 | C | a clock the host contradicts is dropped by the owner | RE-DERIVE (keep the semantics: decisions under the reading supplied with the event) |
| D11, D13, D15, D16 | backlog | proposal | group authority; forgetting history; scarce contacts; resource envelope | RE-DERIVE (open questions; D16's "measure before fixing sizes" vs D27's "no data bounds": D27 governs) |
| D12 | backlog | proposal | release responsibility only on matching committed application evidence | KEEP direction |
| D14 | backlog | proposal | pure crash model first; qualify one Linux FS profile | AMEND: the crash model must be "more tough", modelling OS and hardware (d0d33f7b#5907, 418232ec#1632) |
| D14-a/b/c | 09-20 | C | pending-transaction name in the byte-store/kernel relation; recovery freedom as a second recognizer; frontier rollback arm | RE-DERIVE (mechanisms of the old crash model) |
| D17 | 09-18 | E-r | NNTP and command-line clients first; web later | AMEND: the web reader is inside the node, not Python (35f3668a#1588) |
| D18 | backlog | proposal | prove core invariants, codecs, conditional crash recovery before "usable" | AMEND: "running and tested classically" first; assurance major from 5.4 (d5d27b94#3816) |
| D19 | 09-20 | C | header-value wildmat profile (XPAT), what fn's 501 was | KEEP (wire grammar survivor) |
| D20 | 09-20 | C | outbound guard cured by a total take-and-drop, not a carried length | RE-DERIVE |
| D21 | 09-21 | C | served statement index is a slot on `fn-sn-state`, keyring beside it | DROP (`fn-sn` layout; fn2 has a root record, D41) |
| D22 | 09-20 | C | freshness anchor carries its root; an undescribable Roughtime response is reported uncertain | KEEP the semantics ("uncertain" kept distinct) |
| D23 | 09-24 | E-r | relay trust by carrier allowlist; verify against the author's own enrollment | KEEP |
| D24 | 09-24 | E-r | peer arms' per-event node check carried, not memoized | DROP (a fix for the O(N^2) whole-node guard; fn2 must not have the guard) |
| D25 | 09-24 | E-r | duplicate vs conflict keyed on the poster's bytes | KEEP |
| D26 | 09-24 | E-r | the ten-second rule measured at 2 jobs | DROP (proof-cost process) |
| D27 | 09-25 | E | a constant that bounds data is a defect; concrete representations at runtime, lists only logical | KEEP rule 1 whole; AMEND rule 2: no list twin callable from :exec at all (REPRESENTATION-HISTORY §4) |
| D28 | 09-25 | E | spike/mega, never merged | DROP |
| D29 | 09-25 | C (GPT-6) | control messages: C2/C3 on dev, C4 deferred; cancel as withdrawal; visible(T then C) = visible(C then T) | KEEP the semantics (commutation test) |
| D30 | 09-25 | C (GPT-6) | shorter AGENTS.md; representation as a named abstraction, not a twin of every helper | KEEP the representation clause; DROP the rest (process) |
| D31 | 09-25 | C (GPT-6) | committed-history marker unconditional; A <= M <= D frozen | KEEP the invariant; RE-DERIVE the mechanism on the fn2 log |
| D32 | 09-25 | C | a client-supplied Path is accepted, injector prepends | KEEP |
| D33 | 09-26 | E-r | consolidation design (attach-stobj, catalog slice) | DROP (superseded by D41) |
| D34 | 09-26 | E | fresh deploys, no migrations, one format | KEEP |
| D35 | 09-26 | E-r | the release is the product: one tarball per platform, Linux and OpenBSD, no Python | AMEND: crypto per D64; memory per the 10-14 guardrail |
| D36 | 09-26 | E-r | a public node | AMEND: redeploy later ("we don't need to worry about redeploy rn", d0d33f7b#3240) |
| D37 | 09-27 | E | 6.6.0 first, 6.6.6 final; order is a sequence | AMEND: line is 5.1.1 ... 5.5.5, 6.7.x, 6.6.0-6.6.5, 6.6.6 (d5d27b94#3816, d0d33f7b#3229); sequence rule KEEP |
| D38 | 09-28 | E | (withdrawn) a reader of each previous format | KEEP the withdrawal: no previous-format readers |
| D39 | 09-28 | E | complete everything before the cut; qualify once; no ACL2 patch; reorg not adopted | KEEP "no ACL2 patch"; DROP the release-bar list (superseded) |
| D40 | 09-30 | C | host calls guard-verified definitions whose guard is a named preserved invariant | RE-DERIVE (exists because of the whole-node `fn-sn-statep` guard) |
| D41 | 10-01 | E-r | pages are the state: u64 column pages + byte pool, on-disk = in-memory, `fn-sn` a root record, one prepaid resource vector, built by generators | KEEP (the fn2 foundation) |
| D42 | 10-01 | E-r | history on the catalog's rows, no third representation | KEEP |
| D43 | 10-01 | E-r | acceptance-binding field reverted; later as typed words, not a 48-octet list | KEEP (typed words) |
| D44 | 10-01 | E-r | CRC-0 BP primary blocks accepted when a BIB covers them (RFC 9171 4.3.1) | KEEP |
| D45 | 10-01 | E-r | FN-RCL2 the single tombstone semantics | AMEND: one tombstone semantics, under segment cleaning (d0d33f7b#5090) |
| D46 | 10-01 | C | consumer/authority event kinds reverted until their producer exists | KEEP the rule (a kind lands with its producer) |
| D47 | 10-01 | C | park `fn-rov` | DROP |
| D48 | 10-03 | C | reader access survives a configured peer role | KEEP |
| D49 | 10-04 | E | 6.6.0 is the foundational-component release; zmq-shaped surface may be in it; remote consumer with producer | KEEP intent (renumbered per D37 amend) |
| D50 | 10-04 | C (lane) | article kind `opaque` v1; zmq patterns as generated declarations | KEEP |
| D51 | 10-04 | C (delegated) | recovery after a failed write barrier: copy-and-swap, nothing written below the frontier | RE-DERIVE on the fn2 log (keep "nothing below the frontier") |
| D52 | 10-04 | C (delegated) | a failed checkpoint releases its slot; retry by reason | KEEP the principle |
| D53 | 10-04 | C (delegated) | live reclaim opt-in with a reserved work budget | DROP: live reclaim becomes segment cleaning (d0d33f7b#5090) |
| D54 | 10-04 | C (delegated) | SESS_TERM reason 5 for pressure eviction; separate no-progress policy | KEEP |
| D55 | 10-04 | C (delegated) | auth address limit closes and discards pipelined input | KEEP |
| D56 | 10-04 | C (delegated) | Mini's asks: M2 in 6.6.x under Mini's adapter; codec generated from the grammar | KEEP "generated from the grammar" |
| D57 | 10-04 | C (delegated) | competing consumers with leases outside 6.6.0 | KEEP for now |
| D58 | 10-04 | C (delegated) | access tightening applies at once to open connections | KEEP |
| D59 | 10-04 | C (delegated) | TLS: shipped OpenSSL 3.5.8, explicit groups, hybrid X25519MLKEM768 preferred | AMEND: see D64 |
| D60 | 10-04 | C (delegated) | redeploy both nodes once blockers close | DROP |
| D61 | 10-06 | E-r | host files certified via include-book | DROP (old host build) |
| D62 | 10-06 | E | generators re-adopted (`def-loop`, `def-representation`); no hand twin where a generator should produce it | KEEP |
| D63 | 10-06 | E | one extractor, bare SBCL; CHICKEN deleted | KEEP |
| D64 | 10-06 | E | ship our own crypto library everywhere so post-quantum works; system libssl withdrawn | KEEP. Open for fn2: ember said "shipping our own thing"; the register realized it as bundled OpenSSL 3.5.8; the cut brief says "TLS with our own crypto" |
| D65 | 10-06 | E | memory a priority; 1068 MB small preset not accepted | AMEND: guardrail, no more than +50% over baseline (d5d27b94#3856) |
| D66 | 10-06 | E | working first, then proven; teeth their own phase; no weakened statements | KEEP (strengthened to semantics-first) |
| D67 | 10-06 | E-r | one version line 6.6.1-pre and one release bar | DROP (superseded 10-14) |
| D68 | 10-06 | E | no migration or compatibility obligations for any layout, schema or wire format | KEEP |
| D69 | 10-06 | E | the memory bar counts the whole resident process, core and file pages | AMEND: file-backed pages discounted (905fe751#7460); bar became a guardrail |
| D70 | 10-07 | C (under ember) | AGENTS.md for lanes, SEAT.md for the coordinator | DROP (process) |
| D71 | 10-07 | E | evidence machinery deleted; the cert cache is the record | KEEP |

The register has no D72+. Later ember rulings live only in EMBER.md and the transcripts: 10-14 version line and memory guardrail; 10-16 the breaking cut; 10-17 cut the proof-bookkeeping apparatus, only toplevel theorems non-vacuous; 10-27 the three M2 product changes; 10-28 fn2, semantics-first, bottom-up.

## 13. Where ember changed their mind (the later word governs)

| topic | earlier | later (in force) |
|---|---|---|
| assurance timing | "we're also expanding the assurance !" (01a0b33a#6490, 09-19); "why AREN'T we doing full-system theorems" (adb603dc#1482, 10-02) | "sprinting past the assurance for a bit" (adb603dc#2736, 10-03) → "working. and then also correct/proven" (be1e9dcf#4275, 10-07) → "running and tested" classically, assurance major from 5.4 (d5d27b94#3816, 10-14) → only TOPLEVEL THEOREMS non-vacuous (d0d33f7b#4950, 10-17) → fn2 "*semantics-first*" (d0d33f7b#5907, 10-28) |
| the step machine | engaged the "one step function, one owner, one lock" draft, asked "do you think one loop would be burdensome?" (35f3668a#1588, 10-09); "Regarding pure step/state/event/effects: is **this** why we're fundamentally bottlenecked ... "tigerstyle"" (d0d33f7b#5863, 10-28) | settled with Astra in EXECUTION-MODEL.md (one semantic executor over bounded resumable machines, mutation in place; the pure step is not the cause): "this seems....... reasonable. more reasonable than fn1 was." (EMBER.md, 10-28); the machine form "URGENTLY" redesigned (10-30, MACHINE-FORM-20261030.md) |
| runtime image | "something on our own/lightweight instead of SBCL" (1db4b0cd#4833); CHICKEN "really epic" (1db4b0cd#5056, 09-27) | "an SBCL core is probably the best idea" (b53753a1#1463, 09-28) → "bare-SBCL" (be1e9dcf#4275, 10-07) → "do we really need to be using ACL2's runtime if we have an extractor" (35f3668a#1588) and "why are we extracting so much" (905fe751#2886, 10-10) |
| memory | "deeply under 256MB ... a few dozen MB" (997a44b0#1766, 09-26); "128MB means ...128MB!" (be1e9dcf#4425, 10-07) | file-backed pages discounted (905fe751#7460, 10-11) → "stop grinding towards the memory bar", +50% guardrail (d5d27b94#3856, 10-14) → "let's not worry about the memory inconsistency" (d0d33f7b#5412, 10-27) |
| perf method | measure every change | "analyzing in terms of iop ... locality, burstiness" (905fe751#11483); "WAY too empirical" (d0d33f7b#5857, 10-28) |
| versions | "all versions of fn will be v6.7.xyz" (1db4b0cd#1888) → "first version v6.6.0" (1db4b0cd#5634, 09-27) | 5.1.1 ... 5.5.5, 6.7, then 6.6.x as the landing sequence, 6.6.6 final (d5d27b94#3816, d0d33f7b#3229, 10-14) |
| crypto library | "fine whatever, at least it is C" (997a44b0#1611, 09-26; system libssl); "shipping our own thing so that the postquantum stuff actually works" (be1e9dcf#4275, 10-07) | "'TLS with our own crypto' there was never any reason to be doing our own crypto in ACL2. that requirement isn't a real requirement, we should just lose it." (EMBER.md, 10-28): OpenSSL/LibreSSL, libsodium and the vendored ML-DSA shim via FFI; no crypto in ACL2 |
| web interface | "web later" (01a0b33a#7296, 09-19) | "the web reader being inside the node / the node being selfcontained" (35f3668a#1588, 10-09) |
| when to cut | "complete th eowkr ... *and then* we can cut 6.6.0" (b53753a1#880, 09-28); "keep developing (not trying to do any kind of cut" (d5d27b94#3816, 10-14, the release cut) | "we need to do the fucking breaking cut" (d0d33f7b#4307, 10-16; a code cut, not a release) |
| refusing platforms | (the 10-28 draft proposed refusing COW filesystems) | "its our job to make software that is capable of being correct. if someone wants to deploy it in a way that is fundamentally unsound, that's on them, not us. we shouldn't go out of our way to "refuse" things though." (EMBER.md, 10-28) |
| build boxes | lanes off the Mac; cloud build boxes | "we can build on this mac! we should lift whatever block on build rules :) we are permitted to use hbox & local mac to their absolute utmost for our present project." (EMBER.md, 10-29) |
| landing gates | per-landing whole-tree gates (10-29..10-30) | "why are we paying full gate cost constantly?"; "these gatescripts are bullshit ... revisit our entire development flow and methodology to reduce redundant and useless and bureaucratic work" (10-31; WORKFLOW-20261031.md) |
| pricing work | day and engineer-day budgets in plans | "(it won't take a hundred engineer-days, that's just a bad estimate, it'll take a few dozen swarmcycles)"; "(btw "pricing" isn't something we usually bother to do. it doesn't actually help us complete the project lel)" (EMBER.md, 10-29) |
| rebuild vs in place | "rebuild the new system from the ashes" asked (adb603dc#2660, 10-03; be1e9dcf#8659, 10-08), answered in place; "maybe this whole thing is hopeless ... but i suspect maybe it isnt as bad" (35f3668a#1311, 10-09) | "rebuild a fn2 inplace here that we eventually swap over the root of the repo" (d0d33f7b#5901, 10-28) |
| the proof apparatus | "we should write some coverage-crawling tool" (b53753a1#3201, 09-29) | "evidence" rituals "cargo culted" (be1e9dcf#6393, 10-07); "let's cut it then" (d0d33f7b#4950, 10-17) |
| PDS side-build | "could we be building out the pds on the side" (905fe751#1898) | "maybe we just Shouldn't :)" (905fe751#1901, 30 s later) |
| heap images | "is it not possible to just store an image of our heap...???" (1db4b0cd#4824) | "now *that* sounds more reasonable" to: log as truth, snapshot a cache of its fold, no SBCL core snapshots (1db4b0cd#4869) |

## 14. Twenty sentences a fn2 designer must not violate

Each is ember's own text, verbatim, with its cite; none is superseded by a later turn (the superseded ones are in §13). Ordered roughly from purpose down to process.

1. "this is the persistent event log between systems" (01a0eeec#32013, 2026-10-01T01:15Z)
2. "i'm aggressively wanting the best possible in-memory/hybrid persistent representation because this thing is going to be part of the foundational orthogonal persistence in the rest of the system" (f84a8f40#833, 2026-10-01T08:07Z)
3. "it's constrained by the principles of good software, bounded-metered-backflow-safe/DoS-resilient/QoS-operable types of software." (01a0fe41#4594, 2026-10-03T11:10Z)
4. "btw that IS/WAS one of the explicit goals of fn, is to have a full up-front resource accounting of all resources expended by the system on behalf of its users." (b53753a1#8602, 2026-10-01T07:48Z)
5. "BP is product." (35f3668a#1445, 2026-10-09T03:52Z)
6. "Especially as a server we need to know "clients cant crash us regardless of what they send us" and as a server that we appropriately implement semantics." (418232ec#1632, 2026-09-19T14:47Z)
7. "We can't be having compiled-in configuration, and we will need to be careful to actually have formal statements about server reconfiguration events and that they are implemented properly etc" (418232ec#1632, 2026-09-19T14:47Z)
8. "Using octet lists continues to be unacceptable at runtime :)" (bbbe7a9b#1626, 2026-09-25T02:20Z)
9. "Each of those is a branch that someday will fail during operation for no meaningful reason except durng development we were fearful and installed a footgun." (bbbe7a9b#1626, 2026-09-25T02:20Z; of fixed data bounds)
10. "this serde shit is NOT houyhnhnm computing" (1db4b0cd#4824, 2026-09-27T17:47Z)
11. "a laggy/disk that needs maintenance is a real fact of life that we shouldn't sandpaper away with our model" (1db4b0cd#4774, 2026-09-27T17:38Z)
12. "The crash model definitely needs to be massively sophisticated, the present status is not acceptable at all." (418232ec#1632, 2026-09-19T14:47Z; restated as "more tough", d0d33f7b#5907, 2026-10-28)
13. "ideally we would be tidying up our code to remove all legacy/prototype format support and attendant migrations, so that the code is as simple as possible." (b53753a1#46, 2026-09-28T16:56Z)
14. "ultimately we should be analyzing in terms of iop and other count, locality, burstiness, the way it layers with the filesystem and operating system" (905fe751#11483, 2026-10-12T19:38Z)
15. "i just wouldnt want python in a running fn process, that isnt high assurance whatsoever" (01a0b33a#9731, 2026-09-21T07:36Z)
16. "i like the web reader being inside the node / the node being selfcontained like that." (35f3668a#1588, 2026-10-09T04:31Z)
17. "we probably need to be shipping our own thing so that the postquantum stuff actually works" (be1e9dcf#4275, 2026-10-07T00:23Z), read with "there was never any reason to be doing our own crypto in ACL2" (EMBER.md, 2026-10-28): the shipped thing is a vendored PQ library behind the FFI, never crypto written in ACL2
18. "but yeah we really do have a lot of repetition that really we should NOTICE that we are repeating when we do it, and think "shouldn't this be a macro?"" (700aaf5a#2404, 2026-10-02T03:17Z)
19. "we only need to demonstrate that our TOPLEVEL THEOREMS aren't vacuous" (d0d33f7b#4950, 2026-10-17T04:29Z), read with "i feel like our fn2 we should be *semantics-first* and not worry as much about the proofs until we've actually gotten the implementation into a state where we WANT assurance from it" (d0d33f7b#5907, 2026-10-28T04:56Z)
20. "i am extremely NOT in favor of doing ANY reverting or requiring full proofs before replacing old things. i want to just put in the new code, and eventually fix forward." (9627d694#1312, 2026-10-04T01:59Z)

**The question this record once left open** ("Regarding pure step/state/event/effects: is **this** why we're fundamentally bottlenecked on the performance of our software? are you familiar with "tigerstyle" from tigerbeetle etc?", d0d33f7b#5863, 2026-10-28T04:37Z) is answered by EXECUTION-MODEL.md (§13's step-machine row): no, the measured costs were conversions, reconstruction and work under the owner mutex; fn2 is one executor mutating a fixed struct-of-arrays state in place, with bounded machines, explicit batching inside the implementation and I/O reasoned about in ACL2.
