# P1E — two opaque-field openers, Seat A28 ruling

At parent `b5d1f7066f4acc8aaecab3ad8a3f0f1fbce3f048`, ADT-NTH-0 becomes DEFTHMD with its immediate defining-book LOCAL enable. ADT-NTH-1+ retains the same default-disabled treatment. The census derives **62 ADT-NTH-0 enable subjects**, **53 ADT-NTH-1+ subjects**, and **65 enabled books in total** (50 use both). All six requested gates exit 0. No proof or certificate of the changed closures is claimed.

## Seat A28 ruling

The family of "peel an opaque field index into car/cdr" has exactly two members: ADT-NTH-0 and ADT-NTH-1+. They are the only rules whose LHS is NTH of an opaque record at a field index and whose RHS introduces CAR/CDR from nothing. The other fifteen rows in the initial broad scan react to selectors already present, describe ADT functions, or already end disabled. None has the same mechanism; none changes in this pass.

The initial stop concerned ADT-PSCHEMA-FACTS: its ninth written conjunct opens ADT's own recognizer and shares its DEFTHM with eight other facts. A28 resolved that stop by excluding the entire event from this pass. Its statement and theory setting stay unchanged.

## Initial broad scan and final classification

| Event | Location | Initial broad class | A28 class | Mechanism / disposition |
| --- | --- | --- | --- | --- |
| ADT-PSCHEMA-FACTS | books/proto/adt-key-lib.lisp:370 | PEELER | unrelated | Statement about ADT's own function/recognizer; unchanged |
| ADT-KFIND-OF-KSLOT | books/proto/adt-key-lib.lisp:441 | PEELER | unrelated | Statement about ADT's own function/recognizer; unchanged |
| ADT-NTH-1+ | books/proto/adt-key-lib.lisp:556 | PEELER | PEELER | Opaque NTH field opener; default-disabled with derived LOCAL enables |
| ADT-NTH-0 | books/proto/adt-key-lib.lisp:561 | PEELER | PEELER | Opaque NTH field opener; default-disabled with derived LOCAL enables |
| ADT-SET-REC-C-OPEN | books/proto/adt-key-lib.lisp:1201 | PEELER | unrelated | Already disabled; unchanged |
| ADT-CAR-OF-UPDATE-NTH | books/proto/adt-lib.lisp:326 | PEELER | unrelated | LHS already needs CAR/CDR of UPDATE-NTH; unchanged |
| ADT-CDR-OF-UPDATE-NTH | books/proto/adt-lib.lisp:330 | PEELER | unrelated | LHS already needs CAR/CDR of UPDATE-NTH; unchanged |
| ADT-NTH-CARS | books/proto/adt-lib.lisp:755 | PEELER | unrelated | Statement about ADT's own function/recognizer; unchanged |
| ADT-NTH-CDRS | books/proto/adt-lib.lisp:759 | PEELER | unrelated | Statement about ADT's own function/recognizer; unchanged |
| ADT-CARS-UPDATE-NTH | books/proto/adt-lib.lisp:764 | PEELER | unrelated | Statement about ADT's own function/recognizer; unchanged |
| ADT-CDRS-UPDATE-NTH | books/proto/adt-lib.lisp:768 | PEELER | unrelated | Statement about ADT's own function/recognizer; unchanged |
| ADT-APPEND-FIELDS-OPEN | books/proto/adt-lib.lisp:1187 | PEELER | unrelated | Already disabled; unchanged |
| ADT-SET-FIELDS-OPEN | books/proto/adt-lib.lisp:1194 | PEELER | unrelated | Already disabled; unchanged |
| ADT-GET-FIELDS-OPEN | books/proto/adt-lib.lisp:1202 | PEELER | unrelated | Already disabled; unchanged |
| ADT-GET-FIELDS-OKP-OPEN | books/proto/adt-lib.lisp:1210 | PEELER | unrelated | Already disabled; unchanged |
| ADT-COLS-SHAPE-OPEN | books/proto/adt-lib.lisp:1218 | PEELER | unrelated | Already disabled; unchanged |
| ADT-REC-P-OPEN | books/proto/adt-lib.lisp:1228 | PEELER | unrelated | Already disabled; unchanged |

## Census counts

| Rune | Dev | Qualifying other lane | Own lane (excluded) | Ancestry excluded | Historical U | Additional authorized repairs | Enabled books |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| ADT-NTH-0 | 59 | 55 | 245 | 0 | 62 | 0 | 62 |
| ADT-NTH-1+ | 49 | 43 | 215 | 0 | 51 | 2 | 53 |

Historical union: **63**; enabled-book union: **65 = 62 + 53 - 50**. The two extra ADT-NTH-1+ subjects are the previously authorized CFGROUP/CFPOLICY guard repairs, whose replay controls remain distinctly labeled rather than counted as historical certificates.

The fresh census reads the same October/all-event and September/guard-only scopes named in P1.md, including both read-only hbox reference trees. Only successful FN_CERTIFY_SUCCESS logs and Form/Rules summaries qualify; DEFTHM, DEFUN/implicit guards and explicit VERIFY-GUARDS summaries are retained. Source echoes, failed/incomplete attempts and runes outside Rules lists do not count. Qualifying lanes have ancestry exit 1 for `git -C /absolute/lane merge-base --is-ancestor f7760ab8c HEAD`; own and ancestry-descendant logs are excluded. HEAD snapshots are validated after scanning and again before applying. The seven excluded books receive no enables and are byte-identical to parent.

## Source boundary and deterministic generation

The script accepts `--runes ADT-NTH-1+ ADT-NTH-0`, canonicalizes by uppercase sorted order, and records the rune list in the census. Each log summary and evidence entry records the exact runes used. Each selected consumer gets exactly one line containing only its needed runes, replacing its committed ADT-NTH-1+ line where present: `(local (in-theory (enable adt-nth-0 adt-nth-1+)))` when both are needed. The defining library is the explicit placement exception: each opener has its own immediate LOCAL enable after DEFTHMD.

**62 books differ from the parent**: 49 consumer enable-line replacements, 12 new consumer lines, and the defining-library change. 3 ADT-NTH-1+-only subjects remain byte-identical. Consumer text is constructed from immutable HEAD by a single span insertion/replacement at its last top-level INCLUDE-BOOK, then asserted byte-identical after removing only the canonical enable lines. Existing lines must occur once at that exact anchor. The library permits exactly the ADT-NTH-0 DEFTHM-to-DEFTHMD token change plus its LOCAL enable. Every selected consumer sees the opener definitions at insertion; no undefined-at-insertion findings. Apply was repeated successfully to verify idempotence. [p1e-byte-audit.json](p1e-byte-audit.json) records the independent parent audit.

Commands: `timeout 900 python3 build/vertical-runs/one-world/p1_enables.py --runes ADT-NTH-1+ ADT-NTH-0 --scan`; `timeout 180 python3 build/vertical-runs/one-world/p1_enables.py --runes ADT-NTH-1+ ADT-NTH-0 --apply`; `timeout 30 python3 build/vertical-runs/one-world/p1_enables.py --runes ADT-NTH-1+ ADT-NTH-0 --report`. The generated selection/evidence are [p1-enables.txt](p1-enables.txt), [p1-enables.json](p1-enables.json), [p1-census.json](p1-census.json), and [P1.md](P1.md).

## Six gates

| Command | Exit | Log |
| --- | ---: | --- |
| `timeout 180 python3 tools/one_world_check.py` | 0 | [p1e-gate-one-world.log](p1e-gate-one-world.log) |
| `timeout 180 python3 tools/book_roots_check.py` | 0 | [p1e-gate-book-roots.log](p1e-gate-book-roots.log) |
| `timeout 180 python3 tools/host_check.py --attach-order` | 0 | [p1e-gate-host-attach-order.log](p1e-gate-host-attach-order.log) |
| `timeout 180 python3 tools/host_check.py --world` | 0 | [p1e-gate-host-world.log](p1e-gate-host-world.log) |
| `timeout 180 python3 tools/extract/world.py --check` | 0 | [p1e-gate-extract-world.log](p1e-gate-extract-world.log) |
| `timeout 180 python3 tools/interface_emit.py --check` | 0 | [p1e-gate-interface.log](p1e-gate-interface.log) |

Each gate has 0 findings/refusals. Book-roots retains its existing 55 explicit exclusions; host-world computed-name cases and interface source-undecidable cases retain their existing non-failing status. No proof_repl sessions, certifies, box jobs, commits, pushes or process stops occurred.

## Complete export inventory

The closure is `adt-key-lib` -> `adt-lib`, with no further non-local project include. The table inventories 253 non-local theorem events: 2 PEELER, 3 TOWARD, 248 unrelated. Nine NIL-rule-class events export no theorem rules. 53 LOCAL theorem events are excluded. There are no :elim classes or macro-generated theorem events in this closure. Predicate conclusions rewrite to T; selectors on their LHS are not RHS introductions. The scan preserves classifications per written conjunct and every formula in [p1e-rule-scan.json](p1e-rule-scan.json). No third generic constant/successor-index or explicit-CONS-input opener is exported. The local ADT-UPDATE-NTH-0, ADT-UPDATE-NTH-OF-CONS, ADT-NTHCDR-3 and ADT-NTHCDR-1 are excluded.

| Event | Location | Rule classes | A28 class |
| --- | --- | --- | --- |
| ADT-CAR-NTHCDR | books/proto/adt-key-lib.lisp:66 | `:rewrite` | TOWARD |
| ADT-CDR-NTHCDR | books/proto/adt-key-lib.lisp:70 | `:rewrite` | TOWARD |
| ADT-CONSP-NTHCDR | books/proto/adt-key-lib.lisp:74 | `:rewrite` | TOWARD |
| ADT-SEQ-P-WHEN-CORR | books/proto/adt-key-lib.lisp:95 | `:forward-chaining` | unrelated |
| ADT-TAKE-LEN-SCHEMA-OF-REC | books/proto/adt-key-lib.lisp:100 | `:rewrite` | unrelated |
| ADT-ROW-AUX-OF-CORR | books/proto/adt-key-lib.lisp:105 | `:rewrite` | unrelated |
| ADT-ROW-OF-CORR | books/proto/adt-key-lib.lisp:110 | `:rewrite` | unrelated |
| ADT-ROWS-OF-CORR | books/proto/adt-key-lib.lisp:117 | `:rewrite` | unrelated |
| ADT-ABS-OF-CORR | books/proto/adt-key-lib.lisp:122 | `:rewrite` | unrelated |
| ADT-KMEM-WHEN-KFIND | books/proto/adt-key-lib.lisp:179 | `:rewrite` | unrelated |
| ADT-KFIND-WHEN-NOT-KMEM | books/proto/adt-key-lib.lisp:182 | `:rewrite` | unrelated |
| ADT-KREMOVE-WHEN-NOT-KMEM | books/proto/adt-key-lib.lisp:185 | `:rewrite` | unrelated |
| ADT-KEYS-APPEND | books/proto/adt-key-lib.lisp:188 | `:rewrite` | unrelated |
| ADT-TRUE-LISTP-REV | books/proto/adt-key-lib.lisp:195 | `:type-prescription` | unrelated |
| ADT-REV-APPEND | books/proto/adt-key-lib.lisp:197 | `:rewrite` | unrelated |
| ADT-KEYS-REV | books/proto/adt-key-lib.lisp:200 | `:rewrite` | unrelated |
| ADT-KUNIQUE-REV | books/proto/adt-key-lib.lisp:234 | `:rewrite` | unrelated |
| ADT-KMEM-REV | books/proto/adt-key-lib.lisp:237 | `:rewrite` | unrelated |
| ADT-KFIND-APPEND | books/proto/adt-key-lib.lisp:240 | `:rewrite` | unrelated |
| ADT-KREPLACE-FOUND-APPEND | books/proto/adt-key-lib.lisp:245 | `:rewrite` | unrelated |
| ADT-KUPDATE-APPEND | books/proto/adt-key-lib.lisp:252 | `:rewrite` | unrelated |
| ADT-KMEM-CONS | books/proto/adt-key-lib.lisp:259 | `:rewrite` | unrelated |
| ADT-KMEM-NIL | books/proto/adt-key-lib.lisp:263 | `:rewrite` | unrelated |
| ADT-KUNIQUE-CONS | books/proto/adt-key-lib.lisp:267 | `:rewrite` | unrelated |
| ADT-KFIND-REV | books/proto/adt-key-lib.lisp:272 | `:rewrite` | unrelated |
| ADT-KREMOVE-ALL-WHEN-NOT-KMEM | books/proto/adt-key-lib.lisp:282 | `:rewrite` | unrelated |
| ADT-KREMOVE-IS-ALL-WHEN-UNIQUE | books/proto/adt-key-lib.lisp:285 | `:rewrite` | unrelated |
| ADT-KEYS-KREMOVE-ALL-SUB | books/proto/adt-key-lib.lisp:288 | `:rewrite` | unrelated |
| ADT-KUNIQUE-KREMOVE-ALL | books/proto/adt-key-lib.lisp:292 | `:rewrite` | unrelated |
| ADT-KREMOVE-ALL-APPEND | books/proto/adt-key-lib.lisp:296 | `:rewrite` | unrelated |
| ADT-KREMOVE-ALL-REV | books/proto/adt-key-lib.lisp:300 | `:rewrite` | unrelated |
| ADT-KREMOVE-REV | books/proto/adt-key-lib.lisp:303 | `:rewrite` | unrelated |
| ADT-KEYS-KREMOVE-SUB | books/proto/adt-key-lib.lisp:308 | `:rewrite` | unrelated |
| ADT-KUNIQUE-KREMOVE | books/proto/adt-key-lib.lisp:312 | `:rewrite` | unrelated |
| ADT-KMEM-KREMOVE-SAME | books/proto/adt-key-lib.lisp:315 | `:rewrite` | unrelated |
| ADT-KUNIQUE-INSERT | books/proto/adt-key-lib.lisp:319 | `:rewrite` | unrelated |
| ADT-KEYS-KREPLACE-FOUND | books/proto/adt-key-lib.lisp:323 | `:rewrite` | unrelated |
| ADT-KUNIQUE-KREPLACE | books/proto/adt-key-lib.lisp:326 | `:rewrite` | unrelated |
| ADT-KEYS-KUPDATE | books/proto/adt-key-lib.lisp:329 | `:rewrite` | unrelated |
| ADT-KUNIQUE-KUPDATE | books/proto/adt-key-lib.lisp:334 | `:rewrite` | unrelated |
| ADT-TRUE-LIST-FIX-WHEN-TRUE-LISTP | books/proto/adt-key-lib.lisp:338 | `:rewrite` | unrelated |
| ADT-KREPLACE-FOUND-WHEN-NOT-KMEM | books/proto/adt-key-lib.lisp:341 | `:rewrite` | unrelated |
| ADT-KUPDATE-WHEN-NOT-KMEM | books/proto/adt-key-lib.lisp:346 | `:rewrite` | unrelated |
| ADT-KREPLACE-FOUND-REV | books/proto/adt-key-lib.lisp:351 | `:rewrite` | unrelated |
| ADT-KUPDATE-REV | books/proto/adt-key-lib.lisp:356 | `:rewrite` | unrelated |
| ADT-PSCHEMA-FACTS | books/proto/adt-key-lib.lisp:370 | `:rewrite` | unrelated |
| ADT-KMEM-OF-KSLOT | books/proto/adt-key-lib.lisp:418 | `:rewrite` | unrelated |
| ADT-KSLOT-OF-FIRST-KSLOT | books/proto/adt-key-lib.lisp:430 | `:rewrite` | unrelated |
| ADT-LIVE-RECS-APPEND | books/proto/adt-key-lib.lisp:434 | `:rewrite` | unrelated |
| ADT-TRUE-LISTP-LIVE-RECS | books/proto/adt-key-lib.lisp:437 | `:type-prescription` | unrelated |
| ADT-KFIND-OF-KSLOT | books/proto/adt-key-lib.lisp:441 | `:rewrite` | unrelated |
| ADT-KREMOVE-OF-KSLOT | books/proto/adt-key-lib.lisp:447 | `:rewrite` | unrelated |
| ADT-KREPLACE-OF-KSLOT | books/proto/adt-key-lib.lisp:454 | `:rewrite` | unrelated |
| ADT-KUPDATE-OF-KSLOT | books/proto/adt-key-lib.lisp:462 | `:rewrite` | unrelated |
| ADT-NATP-KHASH | books/proto/adt-key-lib.lisp:485 | `:type-prescription` | unrelated |
| ADT-BUCKET-OF-CONS | books/proto/adt-key-lib.lisp:493 | `:rewrite` | unrelated |
| ADT-MEMBER-REMOVE-EQUAL | books/proto/adt-key-lib.lisp:497 | `:rewrite` | unrelated |
| ADT-MEMBER-TRUE-LIST-FIX | books/proto/adt-key-lib.lisp:501 | `:rewrite` | unrelated |
| ADT-KCOVERS-MEMBER | books/proto/adt-key-lib.lisp:517 | `:rewrite` | unrelated |
| ADT-KCOVERS-APPEND | books/proto/adt-key-lib.lisp:523 | `:rewrite` | unrelated |
| ADT-KCOVERS-PUT-CONS | books/proto/adt-key-lib.lisp:528 | `:rewrite` | unrelated |
| ADT-KCOVERS-REMOVE-BELOW | books/proto/adt-key-lib.lisp:532 | `:rewrite` | unrelated |
| ADT-KCOVERS-KILL | books/proto/adt-key-lib.lisp:536 | `:rewrite` | unrelated |
| ADT-KCOVERS-SAME-KEY | books/proto/adt-key-lib.lisp:543 | `:rewrite` | unrelated |
| ADT-NTH-1+ | books/proto/adt-key-lib.lisp:556 | `:rewrite` | PEELER |
| ADT-NTH-0 | books/proto/adt-key-lib.lisp:561 | `:rewrite` | PEELER |
| ADT-NATP-WHEN-KGOOD | books/proto/adt-key-lib.lisp:575 | `:forward-chaining` | unrelated |
| ADT-KWALK-SOUND | books/proto/adt-key-lib.lisp:584 | `:rewrite` | unrelated |
| ADT-KWALK-COMPLETE | books/proto/adt-key-lib.lisp:590 | `:rewrite` | unrelated |
| ADT-KGOOD-OF-CORR | books/proto/adt-key-lib.lisp:594 | `:rewrite` | unrelated |
| ADT-NTH-ABOVE-OF-PUT-FIELD | books/proto/adt-key-lib.lisp:609 | `:rewrite` | unrelated |
| ADT-NTH-ABOVE-OF-APPEND-FIELDS | books/proto/adt-key-lib.lisp:614 | `:rewrite` | unrelated |
| ADT-NTH-ABOVE-OF-SET-FIELDS | books/proto/adt-key-lib.lisp:620 | `:rewrite` | unrelated |
| ADT-NTH-ABOVE-OF-APPEND-C | books/proto/adt-key-lib.lisp:626 | `:rewrite` | unrelated |
| ADT-NTH-ABOVE-OF-SET-C | books/proto/adt-key-lib.lisp:631 | `:rewrite` | unrelated |
| ADT-CORR-OF-UPDATE-ABOVE | books/proto/adt-key-lib.lisp:648 | `:rewrite` | unrelated |
| ADT-CORR-SET-REC | books/proto/adt-key-lib.lisp:730 | `:rewrite` | unrelated |
| ADT-NTH-ABOVE-OF-SET-REC-C | books/proto/adt-key-lib.lisp:747 | `:rewrite` | unrelated |
| ADT-ROW-OKC-OF-CORR | books/proto/adt-key-lib.lisp:758 | `:rewrite` | unrelated |
| ADT-KCORR-FACTS | books/proto/adt-key-lib.lisp:831 | `:forward-chaining` | unrelated |
| ADT-LIVE-RECS-UNIQUE-OF-KVIEW | books/proto/adt-key-lib.lisp:838 | `:rewrite` | unrelated |
| ADT-KMEM-OF-KVIEW | books/proto/adt-key-lib.lisp:841 | `:rewrite` | unrelated |
| ADT-KLOOKUP-SOME | books/proto/adt-key-lib.lisp:844 | `:rewrite` | unrelated |
| ADT-KLOOKUP-NONE | books/proto/adt-key-lib.lisp:852 | `:rewrite` | unrelated |
| ADT-KUNIQUE-NIL | books/proto/adt-key-lib.lisp:888 | `:rewrite` | unrelated |
| ADT-KCORR-EMPTY | books/proto/adt-key-lib.lisp:892 | `:rewrite` | unrelated |
| ADT-KCORR-INSERT | books/proto/adt-key-lib.lisp:910 | `:rewrite` | unrelated |
| ADT-KCORR-KILL | books/proto/adt-key-lib.lisp:933 | `:rewrite` | unrelated |
| ADT-KCORR-REMOVE | books/proto/adt-key-lib.lisp:965 | `:rewrite` | unrelated |
| ADT-KIDX-OF-OPS | books/proto/adt-key-lib.lisp:988 | `:rewrite` | unrelated |
| ADT-KCORR-FIND-AT | books/proto/adt-key-lib.lisp:1004 | `:rewrite` | unrelated |
| ADT-KCORR-FIND | books/proto/adt-key-lib.lisp:1012 | `:rewrite` | unrelated |
| ADT-KCORR-GET-AT | books/proto/adt-key-lib.lisp:1026 | `:rewrite` | unrelated |
| ADT-KCORR-GET | books/proto/adt-key-lib.lisp:1039 | `:rewrite` | unrelated |
| ADT-KUNIQUE-KREPLACE-FOUND | books/proto/adt-key-lib.lisp:1053 | `:rewrite` | unrelated |
| ADT-KCORR-SETREC-AT | books/proto/adt-key-lib.lisp:1062 | `:rewrite` | unrelated |
| ADT-KCORR-KMEM | books/proto/adt-key-lib.lisp:1079 | `nil` | unrelated |
| ADT-KCORR-REPLACE | books/proto/adt-key-lib.lisp:1084 | `:rewrite` | unrelated |
| ADT-KCORR-SETFIELD-AT | books/proto/adt-key-lib.lisp:1104 | `:rewrite` | unrelated |
| ADT-KCORR-UPDATE | books/proto/adt-key-lib.lisp:1122 | `:rewrite` | unrelated |
| ADT-SEQ-P-KREMOVE | books/proto/adt-key-lib.lisp:1142 | `:rewrite` | unrelated |
| ADT-SEQ-P-KINSERT | books/proto/adt-key-lib.lisp:1145 | `:rewrite` | unrelated |
| ADT-SEQ-P-KREPLACE-FOUND | books/proto/adt-key-lib.lisp:1148 | `:rewrite` | unrelated |
| ADT-SEQ-P-KREPLACE | books/proto/adt-key-lib.lisp:1151 | `:rewrite` | unrelated |
| ADT-SEQ-P-KUPDATE | books/proto/adt-key-lib.lisp:1155 | `:rewrite` | unrelated |
| ADT-TRUE-LIST-LISTP-WHEN-SEQ-P | books/proto/adt-key-lib.lisp:1159 | `:rewrite` | unrelated |
| ADT-G-KWALK-DEF | books/proto/adt-key-lib.lisp:1172 | `nil` | unrelated |
| ADT-G-KWALK-IS-KWALK | books/proto/adt-key-lib.lisp:1185 | `:rewrite` | unrelated |
| ADT-ROW-OKC-OPEN | books/proto/adt-key-lib.lisp:1192 | `:rewrite` | unrelated |
| ADT-ROW-OKC-ZERO | books/proto/adt-key-lib.lisp:1198 | `:rewrite` | unrelated |
| ADT-SET-REC-C-OPEN | books/proto/adt-key-lib.lisp:1201 | `:rewrite` | unrelated |
| ADT-SET-REC-C-END | books/proto/adt-key-lib.lisp:1206 | `:rewrite` | unrelated |
| ADT-KCORR-MEM | books/proto/adt-key-lib.lisp:1214 | `:rewrite` | unrelated |
| ADT-NATP-KWALK | books/proto/adt-key-lib.lisp:1226 | `:rewrite` | unrelated |
| ADT-NATP-KLOOKUP | books/proto/adt-key-lib.lisp:1230 | `:rewrite` | unrelated |
| ADT-NCOLS-NATP | books/proto/adt-lib.lisp:62 | `:type-prescription` | unrelated |
| ADT-ELT-P-OF-CTYPE-ZERO | books/proto/adt-lib.lisp:148 | `:rewrite` | unrelated |
| ADT-ELT-P-OF-ENC | books/proto/adt-lib.lisp:161 | `:rewrite` | unrelated |
| ADT-DEC-OF-ENC | books/proto/adt-lib.lisp:165 | `:rewrite` | unrelated |
| ADT-TRUE-LISTP-WHEN-ALL-ELT-P | books/proto/adt-lib.lisp:169 | `:forward-chaining` | unrelated |
| ADT-ELT-P-OF-NTH-WHEN-ALL-ELT-P | books/proto/adt-lib.lisp:173 | `:rewrite` | unrelated |
| ADT-TRUE-LISTP-WHEN-OCTETSP | books/proto/adt-lib.lisp:177 | `:forward-chaining` | unrelated |
| ADT-LEN-OF-RESIZE-LIST | books/proto/adt-lib.lisp:186 | `:rewrite` | unrelated |
| ADT-NTH-OF-RESIZE-LIST | books/proto/adt-lib.lisp:204 | `:rewrite` | unrelated |
| ADT-ALL-ELT-P-OF-RESIZE-LIST | books/proto/adt-lib.lisp:212 | `:rewrite` | unrelated |
| ADT-ALL-ELT-P-OF-UPDATE-NTH | books/proto/adt-lib.lisp:217 | `:rewrite` | unrelated |
| ADT-LEN-OF-COL-ROOM | books/proto/adt-lib.lisp:232 | `:linear` | unrelated |
| ADT-NTH-OF-COL-ROOM | books/proto/adt-lib.lisp:238 | `:rewrite` | unrelated |
| ADT-ALL-ELT-P-OF-COL-ROOM | books/proto/adt-lib.lisp:242 | `:rewrite` | unrelated |
| ADT-ALL-ELT-P-OF-COL-PUT | books/proto/adt-lib.lisp:246 | `:rewrite` | unrelated |
| ADT-LEN-OF-COL-PUT | books/proto/adt-lib.lisp:250 | `:linear` | unrelated |
| ADT-NTH-OF-COL-PUT | books/proto/adt-lib.lisp:256 | `:rewrite` | unrelated |
| ADT-SCOL-CORR-BOUND | books/proto/adt-lib.lisp:282 | `nil` | unrelated |
| ADT-SCOL-CORR-GET | books/proto/adt-lib.lisp:287 | `nil` | unrelated |
| ADT-SCOL-CORR-GET-0 | books/proto/adt-lib.lisp:294 | `:rewrite` | unrelated |
| ADT-SCOL-CORR-FRAME | books/proto/adt-lib.lisp:300 | `:rewrite` | unrelated |
| ADT-SCOL-CORR-OF-COL-ROOM | books/proto/adt-lib.lisp:305 | `:rewrite` | unrelated |
| ADT-SCOL-CORR-APPEND | books/proto/adt-lib.lisp:309 | `:rewrite` | unrelated |
| ADT-SCOL-CORR-OF-COL-PUT-APPEND | books/proto/adt-lib.lisp:315 | `:rewrite` | unrelated |
| ADT-SCOL-CORR-FRAME-BELOW | books/proto/adt-lib.lisp:322 | `:rewrite` | unrelated |
| ADT-CAR-OF-UPDATE-NTH | books/proto/adt-lib.lisp:326 | `:rewrite` | unrelated |
| ADT-CDR-OF-UPDATE-NTH | books/proto/adt-lib.lisp:330 | `:rewrite` | unrelated |
| ADT-CONSP-OF-UPDATE-NTH | books/proto/adt-lib.lisp:335 | `:rewrite` | unrelated |
| ADT-SCOL-CORR-SET | books/proto/adt-lib.lisp:339 | `:rewrite` | unrelated |
| ADT-SCOL-CORR-OF-COL-PUT-SET | books/proto/adt-lib.lisp:345 | `:rewrite` | unrelated |
| ADT-LEN-OF-SLICE | books/proto/adt-lib.lisp:359 | `:rewrite` | unrelated |
| ADT-PREFIX-EQ-REFL | books/proto/adt-lib.lisp:371 | `:rewrite` | unrelated |
| ADT-PREFIX-EQ-SMALLER | books/proto/adt-lib.lisp:373 | `:rewrite` | unrelated |
| ADT-PREFIX-EQ-TRANS | books/proto/adt-lib.lisp:379 | `:rewrite` | unrelated |
| ADT-PREFIX-EQ-UPDATE-ABOVE | books/proto/adt-lib.lisp:385 | `:rewrite` | unrelated |
| ADT-PREFIX-EQ-RESIZE | books/proto/adt-lib.lisp:389 | `:rewrite` | unrelated |
| ADT-SLICE-OF-PREFIX-EQ | books/proto/adt-lib.lisp:393 | `:rewrite` | unrelated |
| ADT-LEN-OF-POOL-WRITES | books/proto/adt-lib.lisp:403 | `:rewrite` | unrelated |
| ADT-NTH-OF-POOL-WRITES-BELOW | books/proto/adt-lib.lisp:407 | `:rewrite` | unrelated |
| ADT-PREFIX-EQ-OF-POOL-WRITES | books/proto/adt-lib.lisp:411 | `:rewrite` | unrelated |
| ADT-SLICE-OF-POOL-WRITES | books/proto/adt-lib.lisp:415 | `:rewrite` | unrelated |
| ADT-ELT-P-UB8 | books/proto/adt-lib.lisp:420 | `:rewrite` | unrelated |
| ADT-ALL-ELT-P-OF-POOL-WRITES | books/proto/adt-lib.lisp:424 | `:rewrite` | unrelated |
| ADT-UPDATE-NTH-UPDATE-NTH-SAME | books/proto/adt-lib.lisp:436 | `:rewrite` | unrelated |
| ADT-POOLW-IS-POOL-WRITES | books/proto/adt-lib.lisp:440 | `:rewrite` | unrelated |
| ADT-POOLR-IS-SLICE | books/proto/adt-lib.lisp:461 | `:rewrite` | unrelated |
| ADT-NTH-OF-POOL-PUSH-OTHER | books/proto/adt-lib.lisp:486 | `:rewrite` | unrelated |
| ADT-FILL-OF-POOL-PUSH | books/proto/adt-lib.lisp:490 | `:rewrite` | unrelated |
| ADT-POOL-OF-POOL-PUSH | books/proto/adt-lib.lisp:495 | `:rewrite` | unrelated |
| ADT-OCOL-CORR-GET | books/proto/adt-lib.lisp:521 | `nil` | unrelated |
| ADT-OCOL-CORR-GET-0 | books/proto/adt-lib.lisp:530 | `:rewrite` | unrelated |
| ADT-OCOL-CORR-OF-POOL | books/proto/adt-lib.lisp:538 | `:rewrite` | unrelated |
| ADT-OCOL-CORR-FRAME | books/proto/adt-lib.lisp:544 | `:rewrite` | unrelated |
| ADT-OCOL-CORR-FRAME-BOTH | books/proto/adt-lib.lisp:550 | `:rewrite` | unrelated |
| ADT-OCOL-CORR-OF-COL-ROOM | books/proto/adt-lib.lisp:555 | `:rewrite` | unrelated |
| ADT-OCOL-CORR-APPEND | books/proto/adt-lib.lisp:560 | `:rewrite` | unrelated |
| ADT-OCOL-CORR-OF-COL-PUT-APPEND | books/proto/adt-lib.lisp:568 | `:rewrite` | unrelated |
| ADT-OCOL-CORR-SET | books/proto/adt-lib.lisp:578 | `:rewrite` | unrelated |
| ADT-OCOL-CORR-OF-COL-PUT-SET | books/proto/adt-lib.lisp:588 | `:rewrite` | unrelated |
| ADT-LEN-UPDATE-NTH-LOCAL | books/proto/adt-lib.lisp:640 | `:rewrite` | unrelated |
| ADT-NTH-OF-PUT-FIELD-OTHER | books/proto/adt-lib.lisp:644 | `:rewrite` | unrelated |
| ADT-NTH-OF-PUT-FIELD-SCALAR | books/proto/adt-lib.lisp:650 | `:rewrite` | unrelated |
| ADT-FILL-OF-PUT-FIELD | books/proto/adt-lib.lisp:654 | `:rewrite` | unrelated |
| ADT-POOL-ELTS-OF-PUT-FIELD | books/proto/adt-lib.lisp:664 | `:rewrite` | unrelated |
| ADT-FIELD-CORR-OF-PUT-FIELD-OTHER | books/proto/adt-lib.lisp:673 | `:rewrite` | unrelated |
| ADT-FIELD-CORR-OF-UPDATE-OTHER | books/proto/adt-lib.lisp:689 | `:rewrite` | unrelated |
| ADT-FIELD-CORR-OF-PUT-FIELD-APPEND | books/proto/adt-lib.lisp:696 | `:rewrite` | unrelated |
| ADT-FIELD-CORR-OF-PUT-FIELD-SET | books/proto/adt-lib.lisp:704 | `:rewrite` | unrelated |
| ADT-GET-FIELD-OF-CORR | books/proto/adt-lib.lisp:712 | `:rewrite` | unrelated |
| ADT-LEN-OF-PUT-FIELD | books/proto/adt-lib.lisp:723 | `:rewrite` | unrelated |
| ADT-TRUE-LISTP-OF-UPDATE-NTH | books/proto/adt-lib.lisp:728 | `:rewrite` | unrelated |
| ADT-TRUE-LISTP-OF-PUT-FIELD | books/proto/adt-lib.lisp:732 | `:rewrite` | unrelated |
| ADT-LEN-CARS | books/proto/adt-lib.lisp:747 | `:rewrite` | unrelated |
| ADT-LEN-CDRS | books/proto/adt-lib.lisp:748 | `:rewrite` | unrelated |
| ADT-CARS-APPEND | books/proto/adt-lib.lisp:750 | `:rewrite` | unrelated |
| ADT-CDRS-APPEND | books/proto/adt-lib.lisp:752 | `:rewrite` | unrelated |
| ADT-NTH-CARS | books/proto/adt-lib.lisp:755 | `:rewrite` | unrelated |
| ADT-NTH-CDRS | books/proto/adt-lib.lisp:759 | `:rewrite` | unrelated |
| ADT-CARS-UPDATE-NTH | books/proto/adt-lib.lisp:764 | `:rewrite` | unrelated |
| ADT-CDRS-UPDATE-NTH | books/proto/adt-lib.lisp:768 | `:rewrite` | unrelated |
| ADT-UPDATE-NTH-OF-NTH-SAME | books/proto/adt-lib.lisp:773 | `:rewrite` | unrelated |
| ADT-UPDATE-NTH-CARS-SAME | books/proto/adt-lib.lisp:778 | `:rewrite` | unrelated |
| ADT-UPDATE-NTH-CDRS-SAME | books/proto/adt-lib.lisp:783 | `:rewrite` | unrelated |
| ADT-SEQ-P-CDRS | books/proto/adt-lib.lisp:788 | `:rewrite` | unrelated |
| ADT-FIELDS-CORR-OF-PUT-FIELD-OTHER | books/proto/adt-lib.lisp:829 | `:rewrite` | unrelated |
| ADT-FIELDS-CORR-OF-UPDATE-ABOVE | books/proto/adt-lib.lisp:837 | `:rewrite` | unrelated |
| ADT-FILL-OKP-OF-PUT-FIELD | books/proto/adt-lib.lisp:842 | `:rewrite` | unrelated |
| ADT-FILL-OKP-OF-APPEND-FIELDS | books/proto/adt-lib.lisp:848 | `:rewrite` | unrelated |
| ADT-LEN-OF-APPEND-FIELDS | books/proto/adt-lib.lisp:854 | `:rewrite` | unrelated |
| ADT-TRUE-LISTP-OF-APPEND-FIELDS | books/proto/adt-lib.lisp:861 | `:rewrite` | unrelated |
| ADT-POOL-ELTS-OF-APPEND-FIELDS | books/proto/adt-lib.lisp:864 | `:rewrite` | unrelated |
| ADT-COUNT-OF-APPEND-FIELDS | books/proto/adt-lib.lisp:871 | `:rewrite` | unrelated |
| ADT-FIELD-CORR-OF-APPEND-FIELDS-ABOVE | books/proto/adt-lib.lisp:876 | `:rewrite` | unrelated |
| ADT-FIELDS-CORR-OF-APPEND-FIELDS | books/proto/adt-lib.lisp:891 | `:rewrite` | unrelated |
| ADT-SET-FIELDS-INVARIANTS | books/proto/adt-lib.lisp:910 | `:rewrite` | unrelated |
| ADT-POOL-ELTS-OF-SET-FIELDS | books/proto/adt-lib.lisp:920 | `:rewrite` | unrelated |
| ADT-FIELD-CORR-OF-SET-FIELDS-ABOVE | books/proto/adt-lib.lisp:928 | `:rewrite` | unrelated |
| ADT-FIELDS-CORR-OF-SET-FIELDS | books/proto/adt-lib.lisp:936 | `:rewrite` | unrelated |
| ADT-NTH-OF-ATOM | books/proto/adt-lib.lisp:948 | `nil` | unrelated |
| ADT-GET-FIELDS-OF-CORR | books/proto/adt-lib.lisp:957 | `:rewrite` | unrelated |
| ADT-COLS-SHAPE-OF-FIELDS-CORR | books/proto/adt-lib.lisp:975 | `:rewrite` | unrelated |
| ADT-REC-P-OF-UPDATE-NTH | books/proto/adt-lib.lisp:979 | `:rewrite` | unrelated |
| ADT-SEQ-P-OF-APPEND | books/proto/adt-lib.lisp:984 | `:rewrite` | unrelated |
| ADT-SEQ-P-OF-UPDATE-NTH | books/proto/adt-lib.lisp:988 | `:rewrite` | unrelated |
| ADT-REC-P-OF-NTH | books/proto/adt-lib.lisp:993 | `:rewrite` | unrelated |
| ADT-CORR-SHAPE | books/proto/adt-lib.lisp:1047 | `:rewrite` | unrelated |
| ADT-CORR-COUNT | books/proto/adt-lib.lisp:1050 | `:rewrite` | unrelated |
| ADT-CORR-GET | books/proto/adt-lib.lisp:1053 | `:rewrite` | unrelated |
| ADT-LEN-OF-APPEND | books/proto/adt-lib.lisp:1060 | `:rewrite` | unrelated |
| ADT-FILL-OKP-OF-UPDATE-COUNT | books/proto/adt-lib.lisp:1063 | `:rewrite` | unrelated |
| ADT-FILL-NATP-WHEN-FILL-OKP | books/proto/adt-lib.lisp:1068 | `:rewrite` | unrelated |
| ADT-CORR-APPEND | books/proto/adt-lib.lisp:1077 | `:rewrite` | unrelated |
| ADT-CORR-SET | books/proto/adt-lib.lisp:1085 | `:rewrite` | unrelated |
| ADT-SEQ-P-OF-SET-A | books/proto/adt-lib.lisp:1095 | `:rewrite` | unrelated |
| ADT-G-COLP-DEF | books/proto/adt-lib.lisp:1114 | `nil` | unrelated |
| ADT-G-COLP-IS-ALL-ELT-P | books/proto/adt-lib.lisp:1119 | `:rewrite` | unrelated |
| ADT-G-POOLW-DEF | books/proto/adt-lib.lisp:1129 | `nil` | unrelated |
| ADT-G-POOLW-IS-POOLW | books/proto/adt-lib.lisp:1143 | `:rewrite` | unrelated |
| ADT-G-POOLR-DEF | books/proto/adt-lib.lisp:1154 | `nil` | unrelated |
| ADT-G-POOLR-IS-POOLR | books/proto/adt-lib.lisp:1168 | `:rewrite` | unrelated |
| ADT-COL-PUT-EXEC | books/proto/adt-lib.lisp:1177 | `:rewrite` | unrelated |
| ADT-APPEND-FIELDS-OPEN | books/proto/adt-lib.lisp:1187 | `:rewrite` | unrelated |
| ADT-SET-FIELDS-OPEN | books/proto/adt-lib.lisp:1194 | `:rewrite` | unrelated |
| ADT-GET-FIELDS-OPEN | books/proto/adt-lib.lisp:1202 | `:rewrite` | unrelated |
| ADT-GET-FIELDS-OKP-OPEN | books/proto/adt-lib.lisp:1210 | `:rewrite` | unrelated |
| ADT-COLS-SHAPE-OPEN | books/proto/adt-lib.lisp:1218 | `:rewrite` | unrelated |
| ADT-REC-P-OPEN | books/proto/adt-lib.lisp:1228 | `:rewrite` | unrelated |
| ADT-SCHEMA-FNS-OF-ATOM | books/proto/adt-lib.lisp:1234 | `:rewrite` | unrelated |
| ADT-TRUE-LISTP-WHEN-SEQ-P | books/proto/adt-lib.lisp:1260 | `:forward-chaining` | unrelated |
| ADT-TRUE-LISTP-WHEN-REC-P | books/proto/adt-lib.lisp:1264 | `:rewrite` | unrelated |
| ADT-TRUE-LISTP-NTH-WHEN-SEQ-P | books/proto/adt-lib.lisp:1268 | `:rewrite` | unrelated |
| ADT-NAT-COL-NTH | books/proto/adt-lib.lisp:1273 | `:rewrite` | unrelated |
| ADT-CORR-EMPTY | books/proto/adt-lib.lisp:1336 | `:rewrite` | unrelated |
| ADT-CORR-OF-CLEAR-C | books/proto/adt-lib.lisp:1414 | `:rewrite` | unrelated |
| ADT-CORR-TRUE-LISTP-C | books/proto/adt-lib.lisp:1422 | `:forward-chaining` | unrelated |
| ADT-CORR-TRUE-LISTP | books/proto/adt-lib.lisp:1440 | `:forward-chaining` | unrelated |
| ADT-CORR-BUILD | books/proto/adt-lib.lisp:1445 | `:rewrite` | unrelated |
| ADT-CORR-CANON | books/proto/adt-lib.lisp:1451 | `:rewrite` | unrelated |

## Non-local function events

Definition/type-prescription/induction families (as admitted) are unrelated to this theorem :rewrite/:elim family. This inventories source events, without claiming that each function has every family or performing a new ACL2 world query.

| Function event | Location | Class |
| --- | --- | --- |
| ADT-ROW-AUX (DEFUN) | books/proto/adt-key-lib.lisp:46 | unrelated |
| ADT-ROWS (DEFUN) | books/proto/adt-key-lib.lisp:52 | unrelated |
| ADT-ABS (DEFUN) | books/proto/adt-key-lib.lisp:58 | unrelated |
| ADT-KEYS (DEFUN) | books/proto/adt-key-lib.lisp:132 | unrelated |
| ADT-KUNIQUE (DEFUN) | books/proto/adt-key-lib.lisp:136 | unrelated |
| ADT-KMEM (DEFUN) | books/proto/adt-key-lib.lisp:140 | unrelated |
| ADT-KFIND (DEFUN) | books/proto/adt-key-lib.lisp:144 | unrelated |
| ADT-KREMOVE (DEFUN) | books/proto/adt-key-lib.lisp:149 | unrelated |
| ADT-KINSERT (DEFUN) | books/proto/adt-key-lib.lisp:154 | unrelated |
| ADT-KREPLACE-FOUND (DEFUN) | books/proto/adt-key-lib.lisp:158 | unrelated |
| ADT-KREPLACE (DEFUN) | books/proto/adt-key-lib.lisp:165 | unrelated |
| ADT-KUPDATE (DEFUN) | books/proto/adt-key-lib.lisp:171 | unrelated |
| ADT-REV (DEFUN) | books/proto/adt-key-lib.lisp:191 | unrelated |
| ADT-KREMOVE-ALL (DEFUN) | books/proto/adt-key-lib.lisp:276 | unrelated |
| ADT-PSCHEMA (DEFUN) | books/proto/adt-key-lib.lisp:366 | unrelated |
| ADT-LIVE-RECS (DEFUN) | books/proto/adt-key-lib.lisp:385 | unrelated |
| ADT-KVIEW (DEFUN) | books/proto/adt-key-lib.lisp:392 | unrelated |
| ADT-KSLOT-P (DEFUN) | books/proto/adt-key-lib.lisp:396 | unrelated |
| ADT-FIRST-KSLOT (DEFUN) | books/proto/adt-key-lib.lisp:422 | unrelated |
| ADT-FNV (DEFUN) | books/proto/adt-key-lib.lisp:475 | unrelated |
| ADT-KHASH (DEFUN) | books/proto/adt-key-lib.lisp:481 | unrelated |
| ADT-BUCKET (DEFUN) | books/proto/adt-key-lib.lisp:489 | unrelated |
| ADT-KCOVERS (DEFUN) | books/proto/adt-key-lib.lisp:506 | unrelated |
| ADT-KGOOD (DEFUN) | books/proto/adt-key-lib.lisp:568 | unrelated |
| ADT-KWALK (DEFUN) | books/proto/adt-key-lib.lisp:579 | unrelated |
| ADT-SET-REC-C (DEFUN) | books/proto/adt-key-lib.lisp:655 | unrelated |
| ADT-ROW-OKC (DEFUN) | books/proto/adt-key-lib.lisp:751 | unrelated |
| ADT-KIDX (DEFUN) | books/proto/adt-key-lib.lisp:768 | unrelated |
| ADT-KPUT (DEFUN) | books/proto/adt-key-lib.lisp:772 | unrelated |
| ADT-KLOOKUP-C (DEFUN) | books/proto/adt-key-lib.lisp:776 | unrelated |
| ADT-KFIND-C (DEFUN) | books/proto/adt-key-lib.lisp:780 | unrelated |
| ADT-KGET-C (DEFUN) | books/proto/adt-key-lib.lisp:785 | unrelated |
| ADT-KINSERT-C (DEFUN) | books/proto/adt-key-lib.lisp:792 | unrelated |
| ADT-KREMOVE-C (DEFUN) | books/proto/adt-key-lib.lisp:799 | unrelated |
| ADT-KREPLACE-C (DEFUN) | books/proto/adt-key-lib.lisp:808 | unrelated |
| ADT-KUPDATE-C (DEFUN) | books/proto/adt-key-lib.lisp:815 | unrelated |
| ADT-KCORR (DEFUN) | books/proto/adt-key-lib.lisp:820 | unrelated |
| ADT-KEMPTY-C (DEFUN) | books/proto/adt-key-lib.lisp:869 | unrelated |
| ADT-KMEM-C (DEFUN) | books/proto/adt-key-lib.lisp:1210 | unrelated |
| ADT-KINDP (DEFUN) | books/proto/adt-lib.lisp:37 | unrelated |
| ADT-SCHEMAP (DEFUN) | books/proto/adt-lib.lisp:46 | unrelated |
| ADT-OCTETS-KIND-P (DEFUN) | books/proto/adt-lib.lisp:50 | unrelated |
| ADT-KIND-WIDTH (DEFUN) | books/proto/adt-lib.lisp:54 | unrelated |
| ADT-NCOLS (DEFUN) | books/proto/adt-lib.lisp:58 | unrelated |
| ADT-CTYPE (DEFUN) | books/proto/adt-lib.lisp:67 | unrelated |
| ADT-ELT-P (DEFUN) | books/proto/adt-lib.lisp:78 | unrelated |
| ADT-ALL-ELT-P (DEFUN) | books/proto/adt-lib.lisp:86 | unrelated |
| ADT-OCTETSP (DEFUN) | books/proto/adt-lib.lisp:95 | unrelated |
| ADT-VAL-OKP (DEFUN) | books/proto/adt-lib.lisp:99 | unrelated |
| ADT-REC-P (DEFUN) | books/proto/adt-lib.lisp:111 | unrelated |
| ADT-SEQ-P (DEFUN) | books/proto/adt-lib.lisp:119 | unrelated |
| ADT-INDEX (DEFUN) | books/proto/adt-lib.lisp:126 | unrelated |
| ADT-ENC (DEFUN) | books/proto/adt-lib.lisp:132 | unrelated |
| ADT-DEC (DEFUN) | books/proto/adt-lib.lisp:140 | unrelated |
| ADT-COL-ROOM (DEFUN) | books/proto/adt-lib.lisp:224 | unrelated |
| ADT-COL-PUT (DEFUN) | books/proto/adt-lib.lisp:228 | unrelated |
| ADT-SCOL-CORR (DEFUN) | books/proto/adt-lib.lisp:269 | unrelated |
| ADT-SLICE (DEFUN) | books/proto/adt-lib.lisp:355 | unrelated |
| ADT-PREFIX-EQ (DEFUN) | books/proto/adt-lib.lisp:363 | unrelated |
| ADT-POOL-WRITES (DEFUN) | books/proto/adt-lib.lisp:398 | unrelated |
| ADT-POOLW (DEFUN) | books/proto/adt-lib.lisp:429 | unrelated |
| ADT-POOLR (DEFUN) | books/proto/adt-lib.lisp:447 | unrelated |
| ADT-POOL-ROOM (DEFUN) | books/proto/adt-lib.lisp:470 | unrelated |
| ADT-POOL-PUSH (DEFUN) | books/proto/adt-lib.lisp:478 | unrelated |
| ADT-OCOL-CORR (DEFUN) | books/proto/adt-lib.lisp:511 | unrelated |
| ADT-FIELD-CORR (DEFUN) | books/proto/adt-lib.lisp:603 | unrelated |
| ADT-PUT-FIELD (DEFUN) | books/proto/adt-lib.lisp:613 | unrelated |
| ADT-GET-FIELD (DEFUN) | books/proto/adt-lib.lisp:622 | unrelated |
| ADT-GET-FIELD-OKP (DEFUN) | books/proto/adt-lib.lisp:629 | unrelated |
| ADT-FILL-OKP (DEFUN) | books/proto/adt-lib.lisp:637 | unrelated |
| ADT-CARS (DEFUN) | books/proto/adt-lib.lisp:741 | unrelated |
| ADT-CDRS (DEFUN) | books/proto/adt-lib.lisp:744 | unrelated |
| ADT-FIELDS-CORR (DEFUN) | books/proto/adt-lib.lisp:792 | unrelated |
| ADT-APPEND-FIELDS (DEFUN) | books/proto/adt-lib.lisp:798 | unrelated |
| ADT-SET-FIELDS (DEFUN) | books/proto/adt-lib.lisp:805 | unrelated |
| ADT-GET-FIELDS (DEFUN) | books/proto/adt-lib.lisp:813 | unrelated |
| ADT-GET-FIELDS-OKP (DEFUN) | books/proto/adt-lib.lisp:821 | unrelated |
| ADT-COLS-SHAPE (DEFUN) | books/proto/adt-lib.lisp:966 | unrelated |
| ADT-SHAPE-P (DEFUN) | books/proto/adt-lib.lisp:1002 | unrelated |
| ADT-CORR (DEFUN) | books/proto/adt-lib.lisp:1011 | unrelated |
| ADT-COUNT-C (DEFUN) | books/proto/adt-lib.lisp:1020 | unrelated |
| ADT-APPEND-C (DEFUN) | books/proto/adt-lib.lisp:1023 | unrelated |
| ADT-SET-C (DEFUN) | books/proto/adt-lib.lisp:1029 | unrelated |
| ADT-GET-C (DEFUN) | books/proto/adt-lib.lisp:1033 | unrelated |
| ADT-GET-OKP (DEFUN) | books/proto/adt-lib.lisp:1037 | unrelated |
| ADT-SET-A (DEFUN) | books/proto/adt-lib.lisp:1042 | unrelated |
| ADT-NILS (DEFUN) | books/proto/adt-lib.lisp:1290 | unrelated |
| ADT-EMPTY-C (DEFUN) | books/proto/adt-lib.lisp:1293 | unrelated |
| ADT-BUILD (DEFUN) | books/proto/adt-lib.lisp:1296 | unrelated |
| ADT-CANON (DEFUN) | books/proto/adt-lib.lisp:1300 | unrelated |
| ADT-CLEAR-DOWN (DEFUN) | books/proto/adt-lib.lisp:1351 | unrelated |
| ADT-CLEAR-C (DEFUN) | books/proto/adt-lib.lisp:1354 | unrelated |
