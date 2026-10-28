# D sprint report

The scout connection is an actual A `defmachine` declaration using A's generated columns and dispatch arms. `d/machine.lisp` is isolated so continuation edits reuse its certificate. A's core is included before declaring the sidecar; its four-kind registry, simulator, pool, operation table and I/O action wrappers are unchanged. `d/connection.lisp` transforms only the generated dispatch fallback's return shape (GD1); this machine is not reachable from the existing `fn2-turn` and has no calendar/fairness claim.

`d/parser.lisp` interprets a four-command data grammar over pool handles. It scans 32 octets at a time, retains CRLF position over fragments, bounds command lines at 512 octets and header lines at 1000, and handles pipelined GROUP, ARTICLE by number or exact Message-ID, POST and QUIT. GROUP folds C's sparse metadata with continuation; ARTICLE uses C's exact-byte or number lookup and a separate bounded render phase, preserving dot stuffing. All fixture and retained article bytes are A pool ranges under the explicitly shared sprint owner (250,0,1). That owner is a lifetime convenience, not a connection-privacy or lease design.

POST uses an explicit 1024-byte supported article profile and one C group named `test`. It recognizes Message-ID only in headers, refuses a duplicate header, unstuffs body lines and pins the normalized article range. It exact-looks up the offered ID before mutation. A previously stored ID is refused conservatively; same-source duplicate versus changed-source conflict classification, RFC article validation/injection, idempotent operation IDs and concurrency reservations are not implemented. The persistence stand-in (GD2) issues real A Write into a fresh 4096-byte interval derived from the nonwrapping command ordinal, then real A Fence; the configured 128 KiB simulator device bound is checked before issue. Outcome becomes uncertain at successful Write issue, remains uncertain on failed Write/Fence, and C publication plus 240 occur only after successful Fence completion. It is not a B journal batch, event commitment, root-selection or recovery protocol. No restart claim is made.

The D scenario uses actual simulator descriptor take, controlled accept (A's existing no-seeded-input hook), physical completion, A harvest and the independent OWN monitor. A separate client byte oracle checks the complete greeting/GROUP/ARTICLE/POST/GROUP/ARTICLE/QUIT response against independently authored static octet fixtures for client fragment quanta 1, 7 and 4096. Its fence-failure control expects the uncertain line, no 240 and no C mutation. A postcondition additionally compares persisted source bytes against the simulator's durable array. The scheduler is the deliberately simple sprint sidecar driver, not A's calendar.

Five `defthm-owed` entries in `d/owed.lisp` name T1/T6/T8/T9/T10 scoped subjects. They are translated obligations, not admitted theorems. T1's guard closure, full T8 input-fragmentation/privacy, T9 source/BLAKE3/reclamation and T10 total resident-byte accounting remain owed. Nontrivial parser/connection guards remain deferred; runtime work records are conservative declared quanta, not a scalar-operation cost proof.

The explicit profile data in `d/machine.lisp` supplies `:max-article-octets=1024` and `:storage-bytes=131072`; the scenario copies these choices into retained machine columns. ARTICLE emits at most 1200 source octets per render continuation, retaining framing state between chunks. The parser compacts a consumed prefix through its already reserved TX workspace in two stages of at most 1024 source octets per call, then resumes at the rebased scan position. An unconsumed line filling the receive window gets a named framing refusal. The supported profile must fit individual admitted lines in the 4096-byte window; arbitrary larger-line spooling is not implemented.

`tests/integration.lisp` (Sol-owned) adds a whole T1 antecedent/conclusion witness and an actual tx-offset invariant-removal control, plus full-C admission exhaustion retaining POST without issuing storage. Those executable teeth do not prove universal T1 preservation. The parser/connection served functions are logic mode, with nontrivial guards explicitly unverified; this sprint is not ready for extraction.

The source REPL admitted the current parser, declaration, connection and five owed formulas, then ran all four exchange variants. Earlier aborted loads hit cumulative declaration expansion limits or an overbroad termination theory; they were fixed by separating the declaration book and using explicit countdown termination hints. Those aborted loads are not passes. The source-stage examples produced:

```text
D EXCHANGE fragment=4096 fence-failure=NIL WIRE/OWN=:PASS bytes=441
C-rows=3 outcome=3 saw-uncertain=T writes=1 fences=1 durable=T
D EXCHANGE fragment=1 fence-failure=NIL WIRE/OWN=:PASS bytes=441 C-
rows=3 outcome=3 saw-uncertain=T writes=1 fences=1 durable=T
D EXCHANGE fragment=7 fence-failure=NIL WIRE/OWN=:PASS bytes=441 C-
rows=3 outcome=3 saw-uncertain=T writes=1 fences=1 durable=T
D EXCHANGE fragment=7 fence-failure=T WIRE/OWN=:PASS bytes=103 C-rows=2
outcome=2 saw-uncertain=T writes=1 fences=1 durable=NIL
```

The official driver additionally asserts the receive-window compaction control. Final updated closure certified: parser1.838s, connection2.152s, owed1.937s (final T1 teeth text), exchange4.285s. The official updated driver ran all four exchanges and the compaction control successfully; verbatim result output follows. Initial completed closure certificate times: simulator echo286.982s, C runs7.777s, parser1.832s, machine401.929s, connection1.888s, owed1.688s, exchange3.796s. The declaration proof allocated approximately85GB cumulatively (not resident memory): expansion/proof cost is a design defect exposed by this scout, not runtime resource accounting. Cold foundation costs are reported by Sol separately. The original slot-path sandbox refusal was resolved by Sol's read-only-open wrapper using the SAME machine-wide exclusive flocks.

Line counts at final source shape: `d/connection.lisp`419, `d/machine.lisp`38, `d/owed.lisp`62, `d/parser.lisp`109, `tests/d-exchange.lisp`208, `tests/d-exchange-driver.lsp`13.

## Sub-agents

D is one sub-agent through `collaboration.spawn_agent`, running in parallel with C and coordinating through `collaboration.send_message`; no nested agents. The inherited Sol model is visible by assignment, but an exact runtime model identifier was not exposed. Parallel work helped: C's stable interface let D build against real pool handles while the independent core/simulator certificates warmed. Declaration expansion and cold ACL2 closure dominated wall time. Exact wall time is reported by Sol from the top-level task timestamps.

## Final driver output

Command: `timeout -k 5 120 fn2/sprint/acl2-readonly-slot.py < fn2/sprint/tests/d-exchange-driver.lsp` (recorded PID in `build/sprint-d-final-repl.pid`). Full output: `build/sprint-d-final-repl.log`. No ACL2 error blocks; all five assertions returned `:PASSED`.

```text
ACL2 >D EXCHANGE fragment=1 fence-failure=NIL WIRE/OWN=:PASS bytes=441 C-
rows=3 outcome=3 saw-uncertain=T writes=1 fences=1 durable=T
 :PASSED
ACL2 >D EXCHANGE fragment=7 fence-failure=NIL WIRE/OWN=:PASS bytes=441 C-
rows=3 outcome=3 saw-uncertain=T writes=1 fences=1 durable=T
 :PASSED
ACL2 >D EXCHANGE fragment=4096 fence-failure=NIL WIRE/OWN=:PASS bytes=441
C-rows=3 outcome=3 saw-uncertain=T writes=1 fences=1 durable=T
 :PASSED
ACL2 >D EXCHANGE fragment=7 fence-failure=T WIRE/OWN=:PASS bytes=103 C-rows=2
outcome=2 saw-uncertain=T writes=1 fences=1 durable=NIL
 :PASSED
ACL2 >D COMPACTION started=T rebased=T copy-quanta=(8 8) GROUP-dispatched=T
 :PASSED
ACL2 >SPRINT-EXAMPLE-PASS d-exchange-driver
NIL
ACL2 >
```
