# fn2 C/D scout sprint — Sol

All three independent drivers pass from the final certified source closure.
Ten encountered gaps/extension seams are recorded in
[FOUNDATION-GAPS.md](FOUNDATION-GAPS.md). This scout is confined to `fn2/sprint/` on
`fn2/sprint-cd`, based on the real A foundation plus B durability primitives at
`0ec44b22a`. The coordinator originals in `build/coordinator/fn2/` and `briefs/`
were used. No foundation source, production registry or dispatcher is changed.
The shared [interface](INTERFACE.md) was written before the two agents started.

## C: ordered runs, sealing and lookup

A's `defcolumns` owns the resident `(group,article-number)` table, sealed prefix
and append tail. Exact lookup reads Message-ID octets from pool ranges; a scalar
content tag never decides identity. Searches retain row continuations. The range
cursor binary-seeks sparse keys, shares a 32-step structural quantum with output,
and caps each projected `number TAB Message-ID CRLF` batch at 32 entries / 4096
bytes. An unfinished seek retains `(lo,hi,phase)`; emitted batches resume from the
stable article-number key. The exercised group has numbers 2, 900 and 1000000.

The sealer builds one padded 64 KiB page with B's real page header and layout
interpreter, C schema layouts, inline identities and an offset directory. B's
incremental BLAKE3 hashes the physical-page domain and page bytes; B's page reader
checks the parent-held digest. A real pool output lease prevents mutation of the
sealed page. Exact page lookup then decodes the actual sealed offsets and inline
identities, including after all original identity/body fixture handles have been
released. Corruption and an unterminated-varint control exercise rejection paths.

This is a volatile dependency-page builder: it returns `:sealed-volatile`.
B3 installation/recovery, multi-page trees, caches, version pins, compaction,
reservations and physical object retirement remain unbuilt. Resident identity
lookup is a bounded scan, not a separate identity-sorted run. Ribbon belongs
before sealed-run negative probes, InfiniFilter before overlay probes; final
exact comparison stays mandatory. The equal-tag/different-octets fixture is a toy
collision control, not a constructed BLAKE3 collision or source-conflict quarantine.

## D: parser, connection and verbs

The connection is an actual A `defmachine` declaration. Because A closes its
registry before core assembly, the declared table runs beside A's core through a
sprint driver. The generated dispatcher arms are retained; only its hardwired
fallback return shape is adapted. This machine is not reachable from `fn2-turn`
or the calendar scheduler. A's pool, operations, descriptor submission, simulator
completion and harvesting paths are used directly.

A grammar data table interprets GROUP, ARTICLE, POST and QUIT from pool ranges.
The parser retains scan positions across input fragments and scans 32 octets per
step. Full-window retained tails compact through the reserved TX workspace in
two stages, at most 1024 source octets per call; a focused split-command control
checks rebasing and resumed GROUP dispatch. GROUP folds sparse C metadata; ARTICLE selects by number or exact Message-ID
and renders bounded source slices with dot stuffing. Fixture bytes are independent
of the renderer. POST separates headers from body, rejects duplicate Message-ID
headers, unstuffs body lines, checks exact identity and reserves resident C
capacity before issuing any persistence action.

The explicit POST stand-in writes each article at a fresh 4096-byte interval
selected by its non-wrapping command ordinal, within the configured 128 KiB device.
It becomes uncertain when Write is issued, waits for Write and Fence completions,
then adds the C row and emits 240. Fence failure retains uncertainty and does not
publish the row. This does not implement B's event journal, batch seals, root
selection, recovery, checkpoint or cleaner. Same-ID POST is conservatively
refused; source-conflict classification, retry identities, full article validation,
streaming upload manifests, accounts/fairness and general NNTP remain unbuilt.
The explicit supported admission profile is 1024 article octets.

## Proof scope and review recommendation

C's summary equation and exact-identity statements, and D's scoped T1/T6/T8/T9/T10
statements, are `defthm-owed` registrations, not admitted theorems. Cheap C getters
and initialization have verified guards; nontrivial runtime guard closure remains
owed. The test quanta are conservative reported bounds and bounded loops, not a
proved scalar-work certificate. The shared fixture owner `(250,0,1)` permits both
layers to access retained ranges; it does not establish connection privacy or
production ownership transfer. No skip-proofs, axioms, trust tags or program-mode
books are used.

The useful integration candidates are the C/D API, actual pool-only examples,
codec/page-reader composition, parser grammar and continuation structure. Review
the recorded foundation seams before moving this into served code. B3 is required
before either volatile runs or this POST path can claim recovered acceptance.

## Executed examples

Sol independently executed every driver after the last source change. The runner
rejects ACL2 error blocks, nonzero exits and missing standalone pass markers.
[Machine-readable results](evidence/examples.json) report all three passing with
zero ACL2 errors. C covers requested examples (a) and (b); D covers (c), at three
input fragment sizes and with a failed-fence control. The independent admission
control exercises full C capacity before Write and the whole scoped T1 invariant
antecedent/conclusion, then removes that premise with an invalid TX continuation
that remains invalid after a real transition.

```sh
python3 fn2/sprint/tests/run-examples.py \
  fn2/sprint/tests/c-examples-driver.lsp \
  fn2/sprint/tests/d-exchange-driver.lsp \
  fn2/sprint/tests/integration-driver.lsp
```

The C driver includes the certified book in ACL2, then calls its executable
functions and assertions from the Lisp REPL. D and integration use ACL2
`assert-event`. Runtime guard checking is masked for these scout examples;
this does not establish the deferred guard proofs. Full verbatim transcripts
appear below; raw files are linked alongside them.

## Certification

The final combined current-source gate completed successfully at
2026-10-28 21:15:10 UTC, after both agents froze their source:

```sh
ACL2="$PWD/fn2/sprint/acl2-readonly-slot.py" \
  sh fn2/tools/certify.sh \
  sprint/tests/c-examples.lisp sprint/d/owed.lisp \
  sprint/tests/d-exchange.lisp sprint/tests/integration.lisp
```

This closure contains all three C books, all four D books and all three test
books, plus their real A/B/simulator dependencies. Final gate log:
`build/sprint-root-final-cert-2.log`. The earlier final attempt encountered an
owed-book hash mismatch while its teeth documentation changed; triage identified
the stale certificate, then the frozen-source retry passed. There is no pending
red in the final closure.

Cold foundation work was serialized by the prescribed script. The sandbox rejects
read-write opening of global slot diagnostic files; the sprint launcher opens the
same global files read-only and takes the same exclusive flocks, preserving the
six-slot pool. It runs unchanged `tools/acl2`; G2 records the workaround and the
already-started retry that Sol accounted for with a global slot reservation.

Laptop certificates from the requested script are the sprint's gates; they are
not record-toolchain `green_check` evidence or whole-node certification.

## Sub-agents

Exactly two agents were launched with `collaboration.spawn_agent` in parallel,
then monitored with `send_message` and `wait_agent`. No additional agents were
spawned. C owned `c/`, `tests/c-*`, `gaps-C.md` and `REPORT-C.md`; D owned `d/`,
`tests/d-*`, `gaps-D.md` and `REPORT-D.md`. Both inherited the parent configuration;
no override was requested and the tool did not expose a separate model identifier.
Approximate wall times from the 20:22 UTC spawn were 49 minutes for C and
53 minutes for D, including the shared certification wait. Parallel writing
helped; cold shared certification and D's generated column proofs dominated
convergence. Parent review
added sealed-representation lookup and reclamation controls, exact budget/seek
continuations, fresh POST intervals, pre-Write capacity admission and stronger
postcondition checking. Sol owns the interface, safe launcher, independent runner,
composed admission control, reconciliation and final report. No commits or pushes.

## What did not run

The requested examples all ran. This is not the full C/D acceptance campaign:
no cold-disk cursor/cache test, multi-page compaction, logical-version concurrency,
restart/recovery, allocator retirement, full resource acquisition matrix,
calendar fairness or 10,000-seed campaign was run. B3 and its recovery lifecycle
are absent, and the corresponding mechanisms are outside this first cut.
A real same-BLAKE3-digest/different-octets source conflict was not constructed;
the exact-identity control uses equal scalar tags on unequal octets.

## Certify times

Times are cert.pl wall seconds for the final version of each scout book; cache
hits in the last combined gate retain the earlier certificate/time. The full
certificate-build timing lines, including cold dependencies and retries, are
preserved in [certification.txt](evidence/certification.txt).

| Book | Seconds |
|---|---:|
| `c/runs.lisp` | 7.777 |
| `c/seal.lisp` | 3.846 |
| `c/page-lookup.lisp` | 0.598 |
| `d/machine.lisp` | 401.929 |
| `d/parser.lisp` | 1.838 |
| `d/connection.lisp` | 2.152 |
| `d/owed.lisp` | 1.937 |
| `tests/c-examples.lisp` | 0.880 |
| `tests/d-exchange.lisp` | 4.285 |
| `tests/integration.lisp` | 3.812 |

The first cold A/simulator closure took about 31.5 minutes. Notable foundation
books: vocab 239.636 s, sim-adapter-base 504.390 s, sim 675.812 s; the D fixture's
sim/echo dependency then took 286.982 s. These exceed the stated iteration
budget and should be treated as build-design defects, not accepted steady-state
costs. Isolating D's declaration avoids repeating its expansion on continuation
edits. Its 41 generated columns took 401.929 s, 18,061,423 prover steps and about
85.1 GB cumulative allocation (not resident memory). C's 11-column table took
7.777 s. No foundation generator was edited in this scout.

## Verbatim independent driver output

The complete outputs below are from Sol's final rerun, with no trimming or
reflow inside the fences.


### c-examples-driver.lsp — 0.730 s

[Raw transcript](evidence/c-examples-driver.out). Exit 0; zero ACL2 errors.

```text
This is SBCL 2.6.8, an implementation of ANSI Common Lisp.
More information about SBCL is available at <http://www.sbcl.org/>.

SBCL is free software, provided as is, with absolutely no warranty.
It is mostly in the public domain; some portions are provided under
BSD-style licenses.  See the CREDITS and COPYING files in the
distribution for more information.

 ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
 + ACL2 Version 8.7                                                     +
 +   built September 28, 2026  14:11:32.                                +
 + Copyright (C) 2026, Regents of the University of Texas.              +
 + ACL2 comes with ABSOLUTELY NO WARRANTY.  This is free software and   +
 + you are welcome to redistribute it under certain conditions.  For    +
 + details, see the LICENSE file distributed with ACL2.                 +
 ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

Project-dir-alist:
((:FN .
      "/Users/ember/dev/fn/build/lanes/fn2/sprint-cd/")
 (:SYSTEM .
          "/Users/ember/tools/acl2-fn/acl2-8.7/books/")).
Type :help for help.
Type (quit) to quit completely out of ACL2.

ACL2 !> "ACL2"
ACL2 !> 5000000
ACL2 !> "/Users/ember/dev/fn/build/lanes/fn2/sprint-cd/fn2/sprint/tests/"
ACL2 !>
Summary
Form:  ( INCLUDE-BOOK "c-examples" ...)
Rules: NIL
Time:  0.38 seconds (prove: 0.00, print: 0.00, other: 0.38)
 "/Users/ember/dev/fn/build/lanes/fn2/sprint-cd/fn2/sprint/tests/c-examples.lisp"
ACL2 !>
Masking guard violations but still checking guards except for self-
recursive calls.  To avoid guard checking entirely, :SET-GUARD-CHECKING
:NONE.  See :DOC set-guard-checking.

ACL2 >
Exiting the ACL2 read-eval-print loop.  To re-enter, execute (LP).
* C EXAMPLES (:SEAL :SEALED-VOLATILE :SEAL-CALLS 45 :DIGEST
            (2393611324 3288274306 106488177 59901363 2559951232 2394012881
             2145352107 767565418)
            :CHECK :OK :CHECK-CALLS 19 :IMMUTABLE :STATE :CORRUPTION :BAD-HASH
            :LOOKUP
            (:PRESENT :FOUND 1 :ABSENT :ABSENT :YIELD :YIELD 1 :RESUME :FOUND 1
             :SAME-TAG T :DIFFERENT-OCTETS :DIFFERENT)
            :PAGE-LOOKUP
            (:PRESENT :FOUND 1 :TAG 42 :ABSENT :ABSENT :YIELD :YIELD 1 :RESUME
             :FOUND 1 :OTHER-ID :FOUND 0 :SAME-TAG T)
            :SOURCE-RECLAIMED T :CURSOR
            (:FIRST (:YIELD 0 2 900 54) :RESUME (:DONE 2 1 1000000 27)
             :BYTE-YIELD (:YIELD 0 1 2 27))
            :SUMMARY-CUTS T :SUMMARY-MUTANT T :MALFORMED :MALFORMED-ENTRY
            :BAD-PHASE :STATE)
C SEAL / EXACT-IDENTITY / SPARSE-CURSOR / SUMMARY PASS
SPRINT-EXAMPLE-PASS c-examples-driver
```

### d-exchange-driver.lsp — 3.525 s

[Raw transcript](evidence/d-exchange-driver.out). Exit 0; zero ACL2 errors.

```text
This is SBCL 2.6.8, an implementation of ANSI Common Lisp.
More information about SBCL is available at <http://www.sbcl.org/>.

SBCL is free software, provided as is, with absolutely no warranty.
It is mostly in the public domain; some portions are provided under
BSD-style licenses.  See the CREDITS and COPYING files in the
distribution for more information.

 ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
 + ACL2 Version 8.7                                                     +
 +   built September 28, 2026  14:11:32.                                +
 + Copyright (C) 2026, Regents of the University of Texas.              +
 + ACL2 comes with ABSOLUTELY NO WARRANTY.  This is free software and   +
 + you are welcome to redistribute it under certain conditions.  For    +
 + details, see the LICENSE file distributed with ACL2.                 +
 ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

Project-dir-alist:
((:FN .
      "/Users/ember/dev/fn/build/lanes/fn2/sprint-cd/")
 (:SYSTEM .
          "/Users/ember/tools/acl2-fn/acl2-8.7/books/")).
Type :help for help.
Type (quit) to quit completely out of ACL2.

ACL2 !> "ACL2"
ACL2 !> (PROOF-TREE PROVE EVENT SUMMARY WARNING OBSERVATION)
ACL2 !> 5000000
ACL2 !> "/Users/ember/dev/fn/build/lanes/fn2/sprint-cd/fn2/sprint/tests/"
ACL2 !> "/Users/ember/dev/fn/build/lanes/fn2/sprint-cd/fn2/sprint/tests/d-exchange.lisp"
ACL2 !>
Masking guard violations but still checking guards except for self-
recursive calls.  To avoid guard checking entirely, :SET-GUARD-CHECKING
:NONE.  See :DOC set-guard-checking.

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

### integration-driver.lsp — 3.649 s

[Raw transcript](evidence/integration-driver.out). Exit 0; zero ACL2 errors.

```text
This is SBCL 2.6.8, an implementation of ANSI Common Lisp.
More information about SBCL is available at <http://www.sbcl.org/>.

SBCL is free software, provided as is, with absolutely no warranty.
It is mostly in the public domain; some portions are provided under
BSD-style licenses.  See the CREDITS and COPYING files in the
distribution for more information.

 ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
 + ACL2 Version 8.7                                                     +
 +   built September 28, 2026  14:11:32.                                +
 + Copyright (C) 2026, Regents of the University of Texas.              +
 + ACL2 comes with ABSOLUTELY NO WARRANTY.  This is free software and   +
 + you are welcome to redistribute it under certain conditions.  For    +
 + details, see the LICENSE file distributed with ACL2.                 +
 ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

Project-dir-alist:
((:FN .
      "/Users/ember/dev/fn/build/lanes/fn2/sprint-cd/")
 (:SYSTEM .
          "/Users/ember/tools/acl2-fn/acl2-8.7/books/")).
Type :help for help.
Type (quit) to quit completely out of ACL2.

ACL2 !> "ACL2"
ACL2 !> (PROOF-TREE PROVE EVENT SUMMARY WARNING OBSERVATION)
ACL2 !> 5000000
ACL2 !> "/Users/ember/dev/fn/build/lanes/fn2/sprint-cd/fn2/sprint/tests/"
ACL2 !> "/Users/ember/dev/fn/build/lanes/fn2/sprint-cd/fn2/sprint/tests/integration.lisp"
ACL2 !>
Masking guard violations but still checking guards except for self-
recursive calls.  To avoid guard checking entirely, :SET-GUARD-CHECKING
:NONE.  See :DOC set-guard-checking.

ACL2 > :PASSED
ACL2 >SPRINT ADMISSION 
(:FULL-C-NO-WRITE T :T1-SHAPE-POSITIVE T :T1-INVARIANT-REMOVAL T)
NIL
ACL2 >SPRINT-EXAMPLE-PASS integration-driver
NIL
ACL2 >
```

## Files and line counts

Authored source, drivers and launcher total **1722 lines** (C 685; D 849;
independent admission control 72; Python support 116). Counts below also include
the review documents and captured evidence. Generated certificates/FASLs and
build scratch logs are excluded. The source tree has no tracked foundation edits.

| File relative to `fn2/sprint/` | Lines |
|---|---:|
| `FOUNDATION-GAPS.md` | 75 |
| `INTERFACE.md` | 62 |
| `REPORT-C.md` | 60 |
| `REPORT-D.md` | 60 |
| `REPORT.md` | 403 |
| `acl2-readonly-slot.py` | 59 |
| `c/page-lookup.lisp` | 65 |
| `c/runs.lisp` | 234 |
| `c/seal.lisp` | 148 |
| `d/connection.lisp` | 419 |
| `d/machine.lisp` | 38 |
| `d/owed.lisp` | 62 |
| `d/parser.lisp` | 109 |
| `evidence/c-examples-driver.out` | 58 |
| `evidence/certification.txt` | 66 |
| `evidence/d-exchange-driver.out` | 52 |
| `evidence/examples.json` | 29 |
| `evidence/integration-driver.out` | 42 |
| `gaps-C.md` | 13 |
| `gaps-D.md` | 15 |
| `tests/c-examples-driver.lsp` | 28 |
| `tests/c-examples.lisp` | 210 |
| `tests/d-exchange-driver.lsp` | 13 |
| `tests/d-exchange.lisp` | 208 |
| `tests/integration-driver.lsp` | 11 |
| `tests/integration.lisp` | 61 |
| `tests/run-examples.py` | 57 |
