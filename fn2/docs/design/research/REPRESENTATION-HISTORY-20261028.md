# Representation history: what ember asked for, what dev has, what was lost (2026-10-28)

Read-only investigation. Tree: origin/dev = 3bbfc4dca. Transcripts read with `cv show <id> --kind prompt` over the 88 top-level fn sessions (claude cwd ~/dev/fn and ~/dev/minidregg, plus ember's Codex desktop sessions), filtered by representation keywords; session ids are cited as `<8-char prefix>#<message index>`, times UTC. Decisions are cited from `git show origin/dev:planning/decisions.md` with line numbers at that sha.

Trigger (d0d33f7b#5889, 2026-10-28T04:41Z), answering the coordinator's TigerStyle comparison ("State is cons lists and alists: the byte store is a six-element list of alists, octets are lists, and every accessor is a car/cdr chain"):

> ">octets are list — bro.. BRO. do we still have so much scar tissue that we lost our efficient stobj representation? ... This software can be great but we need an extremely methodical approach to actually take it there, and it needs to be from the bottom up ..... so that it's actually comprehensive and not piecemeal...."

## 1. What ember asked for, in order

Every quote is ember's own typed text unless marked as a decision row or a forwarded review.

| # | When (UTC) | Where | Ember, verbatim |
|---|---|---|---|
| 1 | 2026-09-18 06:41 | Codex `01a0b33a#44` (the founding Astra session) | "What do you want to do for persistent storage / data representation / etc etc be? What would be "space age"? ... I honestly think we can be ambitious and try and make a pretty big step, as long as we do a lot of the design up front" |
| 2 | 2026-09-25 01:32 | `720920b2#322` (same prompt in `bbbe7a9b#1518`, `c42b4ed8#326`) | "...a fable to look over our representation and other aspects and see if we can't get things to be using the most efficient reasonable datastructures (eg a list of octets maybe is bad?)" |
| 3 | 2026-09-25 02:20 | `720920b2#430` -> **D27** (decisions.md:1182-1215) | "Using octet lists continues to be unacceptable at runtime :) We need to have fewer bullshit restrictions. ... Octet lists are absurd amount of overhead! Let's endeavor to have efficient representations ;) Otherwise the software is not useful as a system" |
| 3a | 2026-09-25 (decision row) | D27, decisions.md:1204-1211 | Rule written from #3: "**The logical model stays octet lists; the executable path does not.** Record bodies, frames, headers, the Message-ID index and the in-memory history get concrete representations (stobj byte arrays, strings, arrays) with a correspondence theorem to the list definition at every boundary the host calls, guard-verified, and measured before and after on the same image." |
| 3b | 2026-09-25 (decision row) | D30, decisions.md:1254-1256 | Repair adopted into AGENTS.md: "representation as a named abstraction or refinement theorem at each boundary rather than a twin of every helper" |
| 4 | 2026-09-25 23:20 | `997a44b0#468` (mandate ember pasted, "fn — Fable 5.1 technical ownership and implementation mandate", section 7 "Finish D27 at the representation boundary that matters") | "the owner still retains a list representation of payload bytes. Make the next representation work remove that bottleneck rather than just moving the list conversion down one stack frame. ... An immutable byte arena with handles, suitable stobjs, and separately indexed metadata is a candidate ... Bytes do not expand into long-lived cons lists on the native hot path." (forwarded text, not ember's own words; ember issued it as the mandate) |
| 5 | 2026-09-26 19:14 | `1db4b0cd#559` | "why does we use SO MUCH RAM ...... is that part of the currently-issued working agents, to use an actual reasonable RAM layout for all this data? no cons lists of octets?" |
| 6 | 2026-09-26 23:47 | `1db4b0cd#1329` (quoted in decisions.md:1387) | "1. I don't understand how we haven't managed to replace the representation yet. That's a priority. 2. We need a better mutation scheme ..." |
| 6a | 2026-09-26 (decision row) | D33, decisions.md:1281-1282 | "the committed catalog and byte owner as one vertical slice (the arena behind an explicit abstraction, parsed byte facts, event references ...). A prototype of `attach-stobj` precedes the catalog slice." Consolidation design: attach-stobj works in ACL2 8.7, consumer books certify unchanged under the arena attachment. SUPERSEDED 2026-10-04 by D41. |
| 7 | 2026-09-27 17:47 | `1db4b0cd#4824` | "is it not possible to just store an image of our heap...??? i'm trying to understand. this serde shit is NOT houyhnhnm computing" |
| 8 | 2026-09-27 17:49 | `1db4b0cd#4833` | "i'm definitely interested in persistent arena typeish approaches and also being more Houyhnhnm" |
| 9 | 2026-09-27 18:55 | `1db4b0cd#5036` | "is there any way possible to get the heap to be only like 10MB plus whatever data arena...?" |
| 9a | 2026-09-27 (decision row) | decisions.md:1376-1388 ("Persistence: no heap images, the on-disk structure is the in-memory one") | records #7, #6, and "the arena store landed (arena-store-2 to -6)". |
| 10 | 2026-09-27 23:13 | `1db4b0cd#6058` | "overall it seems like MOST aspects of the datastructures are nonpathological, representations aren't pathetically naive, etc." (ember's belief at the time, after the arena wave) |
| 11 | 2026-10-01 00:52 | Codex `01a0eeec#31543` | "what is actually deficient about the present state of the software? the proofs dont close? dont prove enough? the representation isnt efficient? whats the actual beef" |
| 12 | 2026-10-01 08:07 | `f84a8f40#833` -> **D41** (decisions.md:1737-1739) | "i'm aggressively wanting the best possible in-memory/hybrid persistent representation because this thing is going to be part of the foundational orthogonal persistence in the rest of the system and having this component be high performance high quality high assurance via metaprogarmming, proof engineering, mechanical sympathy, and careful algorithmics and datastructures, is ... the task of the day" |
| 12a | 2026-10-01 (decision row) | D41, decisions.md:1738 | "The store's live state becomes typed u64 column pages plus a byte pool, sequence-indexed, with dense per-group number runs, per-group overview pools and a fixed frame arena filled by `pread`, so the on-disk and in-memory images are the same bytes; `fn-sn` becomes a root record ... built through generators (`def-loop`, `def-representation`, ...)". ember: "inclined to take your recommendations". D42 (history on the catalog's rows, not a third representation), D43 (relay binding "carried as typed words, not as a 48-octet list"). |
| 13 | 2026-10-05 14:42 | `9627d694#5598` | "so whats the deal why is the memory footprint so large and the cpu burn so high for such small perf numbers..?" |
| 14 | 2026-10-05 14:44 | `9627d694#5604` (recorded in EMBER.md:218-220 as be1e9dcf#2198) | after the report "Byte work done in Lisp, one octet at a time ... about 6 µs per octet ... Each 16 KiB window re-hashes the whole prefix before it": "...... byte work per octet? wat? oh my god. wait. at one point we had did an TRULY ENORMOUS development wave focused entirely on efficient concrete representation and never using a linked list of octets for any purpose whatsoever, and.... ugh, it seems like all of that got blasted away..... and we have accidentally quadratic algorithms back in play again!" |
| 15 | 2026-10-07 00:23 | `be1e9dcf#4275` -> D62, D65 (decisions.md:1832-1846) | "I think we probably should be adapting the generators ro something right?? because without simplifying these things we'll never actually finish the project. ... our memory footprint is fucking absurd lmao we have done a lot of work on concrete representations and views and everything else; it apparently isn't showing up in the bottom line." D62: `def-loop`/`def-representation` re-adopted; "The 494 loop twins and 285 representation twins are a drain-down backlog". D65: "The representation and view work has to show in the bottom line." |
| 16 | 2026-10-07 01:53 | `be1e9dcf#4425` | "128MB means ...128MB! ... (after all we're basically just streaming views over storage)." |
| 17 | 2026-10-07 22:50 | `be1e9dcf#6691` | "does our heap usage be approximately at most logn with regards to the store size? what is the actual split between memory, disk, heap, datastructre, and soforth ...?" |
| 18 | 2026-10-09 02:50 | `35f3668a#1311` | "some of these "competing representations" (a lot of them DO just need to be deleted) were originally designed to make the refinement proofs easier.... but honestly maybe this whole thing is hopeless and we really do need to light it on fire as you suggest." |
| 19 | 2026-10-09 06:33 | `35f3668a#1672` (GPT-6 review ember pasted, "which i largely agree with") | "At the action boundary, I would use an opaque buffer handle with a generation and range, rather than treating a raw stobj reference as ordinary action data" (OutstandingUse(h,g) => BytesStable(h,g)) |
| 20 | 2026-10-14 ~12:50 EDT | d5d27b94 (EMBER.md:984-988) | "we should stop grinding towards the memory bar ... set guardrails to avoid bloating more than 50% from our baseline". This relaxed the memory *target*, not D27; no later decision withdraws D27. |
| 21 | 2026-10-28 04:41 | `d0d33f7b#5889` | the trigger above: "we lost our efficient stobj representation? ... from the bottom up". |

**The through-line.** Ember asked for the same thing six times in five weeks (#2, #3, #5, #6, #12, #14) and twice more as decisions (D27, D41): no octet lists at runtime; a concrete, mechanically sympathetic representation (stobj byte arrays / arena with handles / u64 column pages plus a byte pool, the on-disk image equal to the in-memory one), the list kept only as the logical model with a correspondence theorem at each host boundary. Each time it was asked again, the request was a surprise that it had not stuck: "I don't understand how we haven't managed to replace the representation yet" (09-26), "it seems like all of that got blasted away" (10-05), "it apparently isn't showing up in the bottom line" (10-07), "we lost our efficient stobj representation?" (10-28). The 10-14 relaxation is of the memory number only.

## 2. What the tree has at origin/dev (3bbfc4dca)

### 2.1 The headline: the efficient representations exist; the list paths were never removed

There are 34 books with `defstobj`/`defabsstobj`/`attach-stobj`/`def-representation`/`def-buffer` forms on dev (`git grep -n -E '^\s*\((defstobj|defabsstobj|attach-stobj|def-representation|def-buffer)' origin/dev -- books host`, 98 forms). The octet buffer, the payload arena, the paged catalog, the linear-hashing Message-ID pages and the paged history all landed and are attached. What did not happen is the second half of each landing: deleting the list path it was built to replace. The host's list conversion is the measure. `fnn-octet-list` is `(coerce octets 'list)` (host/native/io.lisp:264-265). Direct calls `(fnn-octet-list ` in host/, counted at the last dev commit before each date (`git grep -h -o -E '\(fnn-octet-list ' $(git rev-list -1 --before=<date> origin/dev) -- host | wc -l`):

| date | dev sha | `(fnn-octet-list` calls in host |
|---|---|---|
| 2026-09-22 | ad4490a58 | 130 |
| 2026-09-25 (D27 day; octets-stobj and arena land this day) | c50ed1556 | 179 |
| 2026-09-27 (arena-store waves) | b27ab89fc | 213 |
| 2026-10-01 (D41) | beeedbf1f | 238 |
| 2026-10-05 ("all of that got blasted away") | 50ff5f43c | 242 |
| 2026-10-09 (freeze, ANATOMY) | 3a937ebc3 | 252 |
| 2026-10-14 | b5d1f7066 | 263 |
| 2026-10-17 to dev now (M1 cut) | 455710fea .. 3bbfc4dca | 263 |

The count grew in every period after D27. The cut (M1) left it unchanged, because M1 deleted books no host build reaches and these calls are in the host that runs. By file today: io.lisp 84, owner.lisp 53, bp-app.lisp 17, hybrid-control.lisp 12, control.lisp 12, bp-service.lisp 10, admin.lisp 10, pull-service.lisp 9 (`[^-a-z]`-terminated occurrences). The shrink-only lint built for this, `tools/list_codec_check.py` (lane d27-representation, 2026-09-28), has baseline `tools/list_codec_baseline.json` total **92** host codec sites handed a consed octet list. It last moved on 2026-10-02 (1776d0191). No lane has lowered it since.

**ANATOMY's "766 executable functions car/cdr-walk octet-typed data", re-measured.** I recovered ANATOMY's method from the transcript (35f3668a, 2026-10-09T03:50Z). A function counts if it is in the exec closure, its body has `(c[ad]r WORD)`, and its body matches `octet|byte|u8|fn-octetsp|nat-listp|unsigned-byte-listp`. I re-ran that regex over my own exec closure: the transitive call closure of book functions named anywhere in host/, 11,914 of 19,993 book defuns. Scripts: /private/tmp/claude-501/-Users-ember-dev-minidregg/d0d33f7b-1304-4ad3-96f2-1735fa3775b2/scratchpad/scripts/octwalk.py and anat766.py, about 3 s. The results:
- ANATOMY's regex at dev: **723** (766 at the freeze; the cut removed about 43). By family: bp 75, store 70, native 59, owner 38, peer 36, nntp 35, article 32, web 30, consumer 28, tls 24.
- The same regex with `byte` dropped (`octet|u8|unsigned-byte-listp` only): **630**.
- A typed criterion: a formal guarded by an octet recognizer (`fn-cbor-octet-listp`, `fn-octet-listp`, `fn-wire-octet-listp`, ...) and `car/cdr/endp/first/rest` applied to that formal. This gives **45**, or 75 counting `nth/len/append/take` too. Only 286 book defuns carry an octet recognizer in their declare at all (216 of them executable).

So 766 measures functions that touch octet-ish data and use car/cdr somewhere, which is the right smell, not a count of octet loops. Most of the listness sits in untyped record and alist plumbing: the records below are cons tuples read by `car (cdr (cdr ...))` chains, e.g. `fn-sf-records-field` at books/store-files.lisp:93-96, whose `:exec` is `fn-ag-car`/`fn-ag-cdr`. Their payload fields are octet lists, but no guard says so.

### 2.2 Per data kind

| Data kind | Representation at dev | Where (path:line) | Who reads it | Where a list is walked over octets |
|---|---|---|---|---|
| **Octet buffer** | `fn-octets`: abstract stobj; logic = octet list, exec = resizable `(unsigned-byte 8)` array + fill. Inline len/get/put/append. 14 `def-buffer` clones `:congruent-to fn-octets` (rx, lg, rd, pg, pub, ctl, bp, web-in/out, zin-*, dss-*, ast-ws, pgb) | books/octets-stobj.lisp:72 (`fn-octets$c`), :1160 (`defabsstobj fn-octets`); host fill `fnn-octets-fill` io.lisp:319 | the prepare (poster-bytes-buffer), log walk, extent read, checkpoint writer, deflate, control frames | `fn-octets-list` (one cons per octet, "the escape hatch": LANEDUMP-rep-octets-stobj) has 39 book sites and 2 host sites |
| **Payload arena** (retained article bytes) | `fn-arena` attachable generic over `fn-arena-extent` (`fn-arena$x`, pages of `fn-arena-page`), handles never reused; seal from list, buffer or range; reseat to log extent; forget | books/payload-arena.lisp:113 (`attach-stobj fn-arena fn-arena-extent`); payload-arena-extent.lisp:57,61,1570 | catalog held rows (by handle), extent read, checkpoint | `fn-arena-get-span` answers a **list** (payload-arena.lisp header: "the list of (nth at+k ...) one read's worth"; 8 host and 32 book sites). `fn-arena-seal-list` (seal from a list) has 5 host and 154 book sites, against `fn-arena-seal-buffer` 5/25 and `-seal-range` 1/13 |
| **Catalog** | `fn-cat` attachable generic over `fn-cat-paged`, whose foundation `fn-cat$p` holds typed row pages `fn-crow` (`def-representation`, `:pages t`: seq/txid/gen/payload-handle/charge/stamp u64, msgid `:octets` pool, `aux`/`nums` `:tree`), the dense per-group map `fn-dmap`, a withdrawals hash table, an overflow hash table, **and the old foundation `fn-cat$c` nested as a field** (`fn-cat$p-tab :type fn-cat$c`, kept "so the view is the old state exactly") | books/catalog.lisp:15-17; catalog-paged.lisp:101-113 (fn-crow), :116-144 (fn-cat$p); catalog-logic.lisp:527-549 (fn-cat$c: rows `(array t)`, Message-ID table `fn-mlh`, five `equal` hash tables) | every served read, owner, post, peer | The held record (books/catalog-record.lisp header) holds the payload as a handle, but its `aux`/`nums` are cons trees, and its logical view and `fn-held-wire-of` materialize the wire record with an octet-list payload. `fn-cat-intern-list` (open path) is in the exec closure |
| **Message-ID index** | `fn-mlh`: two-level directory of fixed 2,048-word `(unsigned-byte 61)` page stobjs (`fn-mlg`), linear hashing, one page split per add, fixnum words, measured 16 B consed per lookup | books/msgid-linear-exec.lisp:118-141 | nested in `fn-cat$c` (`fn-cat$c-mpx`) | none on the probe. The best representation in the tree |
| **History** | `fn-hist` attachable generic over `fn-hist-paged`: `fn-hist$p` = root `fn-hrecs$c` (page store `pgs-mem` + octet pool `fn-octets-pg` + an `(array t)` suffix of events) + an `eql` Message-ID hash | books/history-columns.lisp:15-17; history-paged.lisp:11-18; history-records.lisp:64-78 | readers that migrated to `fn-hrecs-read` | `fn-sf-records` (store-records-field.lisp:76-80) answers `(append (fn-hrs-disk-history handle) (fn-sl-list suffix))`: "the lazy full decode an unmigrated reader pays" (history-records-disk.lisp:8-11). `fn-own-start` (owner.lisp:996-1011, in the exec closure) passes `(fn-sf-records (fn-sn-files store))` to `fn-own-prefix-archive` with version 0, which takes none of the records (owner.lisp:861-864). Under strict evaluation, the argument is still the full decode whenever the records field is based. I did not run an open to see whether the served open reaches this with a based field. Suffix events are `:object` cons trees (history-columns-foundation.lisp:115) |
| **Byte-store crash model** | Cons record `(:byte-store unit inodes dirs pending next-ino)`, inodes an alist ino -> octet list. **A specification, by design**: specs/crash-model-v2.md section 1 | books/byte-store.lisp header | the crash proofs | Only 53 of 266 byte-store functions are executable, and they are profile, frame and txn-name helpers (byte-store-frame 35, txn-name 9, `fn-bs-take`/`fn-bs-zeros` 4, `fn-bs-scp-program` 1). The host does the real syscalls. Lists are correct here: it is the model |
| **Log records (open/replay)** | entry pread into `fn-octets-lg`, decided in place (header by index, frame digest over the window, batch lengths by index) | books/store-log-buffer.lisp header; host `fnn-log-stream-segment` | open, replay | each record is then **copied out as a cons list**, one at a time: `fn-lgb-slice` -> `fn-lgb-slice-acc` conses `(fn-octets-get ...)` per octet (store-log-buffer.lisp:314-324, :712-717). Entries under 74 octets go through the list step |
| **Checkpoint** | written through the publication buffer `fn-octets-pub` in bounded batches (owner-checkpoint-writer.lisp:85); read per segment into the octet buffer (rep-wave-d-3) | owner-checkpoint-writer.lisp, owner-checkpoint-open.lisp | open, publish | The capture takes "the record list by pointer" (owner-checkpoint-writer header). The paged checkpoint (`fn-pck-row`, paged-checkpoint.lisp:134) has **0 executable functions** on dev: realized on the host only in salvage/s-pck-host and lane/log-lc, neither merged |
| **OVER/NOV lines** | byte quanta over cached strings and "already-owned octet lists" (nov-byte-window.lisp header); spans normalized without copying (nov-span-window.lisp) | books/nov-*-window.lisp (9 exec of 23) | OVER | numeric fields and delimiters are octet lists. The column window (`nov-column-window.lisp`) was deleted unreached by M1-b 82db5c7a7 |
| **Owner / store node / view** | **Cons tuples.** `fn-own-make` = 15-element `list` (owner.lisp:652-656); store node `fn-sn` = 14-position list (store-node.lisp layout comment); view = 9-element list with an `archive` (owner-view-record.lisp:65-70); connections and feeds are lists walked by `def-loop` | as cited | every step | D41 "`fn-sn` becomes a root record" and COMPLETE-BEFORE row ST5 ("History and node lists on the same rows; `fn-sn` a root record") never landed |

### 2.3 The POST and ARTICLE paths, re-traced at dev

Traced by a sub-agent against the extracted tree at 3bbfc4dca. I spot-checked owner-host.lisp:2538, io.lisp:9474/9487, nntp-post.lisp:479 and owner.lisp:1287; all hold. Default path: plaintext NNTP POST through the mux, no carrier, compression off.

**POST, socket to log: 18 whole-article representation changes, 16 under the owner mutex** (ANATOMY's "about seven" is an undercount):

1. mux.lisp:224 `fnn-mux-read-plain`: kernel -> loop buffer -> fresh vector (`subseq`)
2. owner.lisp:7248 -> io.lisp:319 `fnn-octets-fill`: vector -> `fn-octets`
3. wire-scan.lisp:108 -> body-chunks-span.lisp:149 `fn-bch-push`: buffer -> 512-octet packed **bignum** blocks (the tail bignum is rebuilt 2-3 times per line)
4. wire.lisp:787 -> body-chunks.lisp:509 `fn-bch-lines-rev`: bignums -> a **list of line lists**
5. nntp-post.lisp:479 -> :225/:218 `fn-post-body-octets` / `fn-post-body-onto`: lines -> one flat **cons list** (2 passes). Injection (`fn-inj-decide`, injection.lisp:984-1047) then shares the body tail and copies only header-sized prefixes
6. owner.lisp:1287 -> packed-submission.lisp:163/96 `fn-psub-pack-sub`: list -> **one bignum** at enqueue, and the queue append is `fn-ag-append` (O(queue))
7. owner.lisp:2464 -> packed-submission.lisp:173 `fn-psub-unpack-sub`: bignum -> list at take
8. owner.lisp:3513 -> io.lisp:257 `fnn-octets`: list -> vector
9. owner.lisp:4147 `fnn-octets-fill`: vector -> `fn-octets` again
10. owner-host.lisp:2538 `(fn-octets-list fn-octets)`: buffer -> **list** for `fn-sn-article-record`
11. io.lisp:1985 -> payload-arena-extent.lisp:683 `fn-arena$x-seal-buffer`: buffer -> arena page (the good step)
12. owner.lisp:3529 -> owner-host.lisp:2826 -> store-intern.lisp:82 `fn-arena-payload`: arena page -> **the same list as step 10, built again**
13. records-codec-concrete.lisp:180-194 `fn-rcon-record-encode-impl`: list -> CBOR record list (the `:bytes` item copies, then a 15-way `append` copies again)
14. owner.lisp:3538 `fnn-octets`: list -> vector
15. io.lisp:9474 `fnn-log-take-verdict`: vector -> **list** (`fnn-octet-list`)
16. io.lisp:9487 `fnn-log-take`: vector -> **list** again, held in the batch and `fnn-log-members`
17. io.lisp:8122 -> store-log-kernel-concrete.lisp:334 `fn-lgc-append-octets`: records -> framed, chained entry list (2+ passes)
18. io.lisp:7602 `fnn-log-pwrite`: list -> vector, write(2)

By kind: 5 host list<->vector conversions (8, 14, 15, 16, 18), 2 buffer->list rebuilds of the same list (10, 12), 4 bignum<->list (3, 4, 6, 7), 3 list->list (5, 13, 17), 3 vector->buffer/page (2, 9, 11), 1 vector->vector (1). That is at least about 14 whole-article cons-list passes at 16 B/octet. The audit's named items: `post-body-onto` confirmed; packed-submission confirmed as a round trip (`fn-psub-pack-dc`/`-unpack-octets`; the named split/join is the small groups field); "body-chunks join" refuted (`fn-bch-join` is spec-only; the executed step is the split `fn-bch-lines-rev`); "a dozen injection helpers" refuted as whole-article copies. Not traced: web POST, IHAVE/TAKETHIS (`fnn-owner-attempt-transit`, which fills the buffer the same way), TLS (one more decrypt copy).

**ARTICLE/BODY, command to socket: 3 whole-article copies, all buffer to buffer, no octet list.** (0, cold only) extent.lisp:1302 `fnn-extent-read-entry` preads the whole log entry, digest checked in place through `fn-octets-rd`. (1) article-stream.lisp:128 -> extent.lisp:1781 `fn-arena-get-span-into` copies into `fn-ast-ws`. (2) article-stream.lisp:802 `fn-nsp-stuff` dot-stuffs into `fn-dss-out`. (3) owner.lisp:988 -> runtime-contract-host-lease.lisp:158 `fn-hld-copy` copies into the lease array. (4) mux.lisp:662/670 writes from the array range. ANATOMY's extent.lisp list coercion (now :1283, :1294-1295) is now only the 32-octet trailer. `fn-arena-get-span` (the list form) appears on this path only in the logical spec. Without a lease (COMPRESS, web, pull feed) there is one more copy out (`fnn-dss-out-octets`, owner.lisp:1050).

So **the read path is what D27 asked for, and the write path is not.** The POST path still holds the article as a list, a bignum and a list of lines. The efficient pieces (`fn-octets`, the arena seal) appear on it as two islands, each followed by a conversion back to a list.

## 3. What was lost, what never landed

**Note on shas.** The LANEDUMP shas (219fd392, 2d416f36, 48dc7bba, 0ca446c6, 389c47e4) and all 293 shas in DELETED-BRANCHES-20261027.tsv are not ancestors of origin/dev. The lane-dump shas are not even objects in this clone (`git cat-file -e` fails). Their content landed under rewritten shas. The dev-side shas below come from `git log origin/dev --diff-filter=A -- <book>` and the merge subjects.

### 3.1 The representation waves: what landed on dev, and when

| When | dev sha | What | State at dev |
|---|---|---|---|
| 09-25 | ef3dc9924 | wave B, boundary 6: `fn-octets` abstract stobj; the POST prepare reads the buffer (poster-bytes-buffer) | present, the base of everything |
| 09-25 | 94bc7c446, merge d0e869780 | wave C: subject digest over the buffer (`books/sha256-buffer.lisp`); the drain stops re-digesting | sha256-buffer **deleted** 9aedcc3ab (09-27) when BLAKE3 replaced SHA-256; re-done as `books/subject-id-buffer.lisp` (`fnn-subject-id-buffer`, io.lisp:2137). The list twin `fnn-subject-id` (io.lisp:2127, `(fnn-octet-list payload)`) is still beside it |
| 09-25 | 96e9bd59a, merge 48305f111 | wave D: payload arena `fn-arena` | present; attached to `fn-arena-extent` |
| 09-25/26 | 115fe6b1f .. e9f78dc4c; 4cb93fcde .. 34c223369 | wave D-2/D-3: checkpoint written from and read into the buffer (N=10,000 x 32 KiB reopen 4.80 -> 2.22 GB VmRSS, LANEDUMP-rep-wave-d-3) | present |
| 09-26 | e2ccfd4de, merge 17ccc4a8c | catalog-slice: the held record (payload as arena handle, two views) answering PKT-293 | present |
| 09-27 | 1129cd06e | store-log-buffer: log entry decided in the buffer | present; records still sliced out as lists (`fn-lgb-slice`) |
| 09-27/28 | arena-store-2..7, arena-offheap | arena on paged/extent foundation, history image from page file | present |
| 09-28 | e80e888d0, bea480bbd | B6: `packed-submission` (the queued article packed into **one natural**, unpacked by the committer) and `body-chunks` (fixed packed blocks) | present and executable: packed-submission 24 of 27 functions, body-chunks 33 of 42. Two more representations on the POST path, added three days after D27 |
| 09-28/29 | b71203d1c, b9b7a0520; merged, reverted, re-applied, reverted (b011b7eab, c44332a05, c99374c8a, 0518a375d, 3b2604a96) | d27-representation: boundary 9 `article-buffer` (parse the article by index), `frame-buffer`, `native-control-buffer`, the shrink-only `list_codec_check` (99 -> 92) | present (`origin/lane/d27-representation` 8487e3275 is 0 ahead of dev); article-buffer 16 executable functions. The lint has stood at 92 since 10-02 |
| 10-01 | eb481f4b1, 85461a19d, 982a8e651 | D41 stage 1/3/7: `def-representation`, paged catalog rows, linear-hash Message-ID pages | present; 10-06 c29033421 "The paged catalog is the default and only executable catalog" |
| 10-03 | cdff5e219 | P3 history roots (`fn-hist-paged`) | present; unmigrated readers still full-decode (`fn-hrs-disk-history`) |

The waves did land. Ember's 10-05 "it seems like all of that got blasted away" was not literally true. They landed beside the list paths, which kept growing: 179 -> 263 `fnn-octet-list` calls; 92 list-codec sites frozen since 10-02; `fn-arena-seal-list` with 154 book sites against `fn-arena-seal-buffer`'s 25. The design law the waves were written under (D27: "a correspondence theorem to the list definition at every boundary the host calls") made each new buffer path a **twin** of a list path, proved equal to it. The list path stayed callable, and new host code kept calling it. D62 (10-06) names the result: "494 loop twins and 285 representation twins".

### 3.2 Built, never merged

| Branch | Head | What it held | Why not on dev |
|---|---|---|---|
| `spike/mega` (deleted 10-27; tsv line 290) | ac305d2d3 | `spike/representation` merged as ad9889637 (09-25): `books/records-stobj.lisp` (**boundary 7: the record codec over the buffer**, "the encoder writes each item straight into the buffer"), `books/frame-stobj.lisp` (**boundary 8: the store frame `[header 10][record n][trailer 32]` in the buffer**), `books/article-stobj.lisp` (boundary 9), `octets-stobj` | D28: the spike never merges. Boundaries 6 and 9 were re-done on dev; **7 and 8 never were.** dev's `fn-record-encode-impl` (books/records.lisp:127-135) is still a fourteen-way `append`, and frame-fields still splits lists. BRANCH-VERDICTS:354: SUPERSEDED as an "anti-groove statement packet" |
| `lane/log-lc` | d999a7fc4 (10-16, 41 ahead) | LC: the storage format (columns, cleaning, MOVE, replay, the ID-5/ID-6 keystones), "WIP at the stop (ember 10-16) ... UNAUDITED"; contains LB 3350d0a0d | stopped for the breaking cut; an M2 input (BRANCH-VERDICTS:263). EMBER.md 10-14: "LB -> LC (the storage format; everything after stacks on it)" |
| `lane/spans-lb` -> `cut/m2a-lb` | 6db86c8a5 -> 7144f51f6 (10-27, 25 ahead) | LB catalog columns `fn-lbc` (16 u64 row words, msgid pool, overview pool, per-group number arrays, open-addressed msgid slots) | in flight as M2(a). The branch **adds 215 books and deletes none** (`git diff --name-status origin/dev...cut/m2a-lb -- books host`). It syncs `fn-lbc` from `fn-cat` (`fn-lbc-sync`, 7b9dd4ef5), so it is a **third catalog representation** beside `fn-cat$c` and `fn-cat-paged`. CUT-M2-STORAGE-DESIGN D-3 makes it a third `fn-cat` concrete (`fn-cat-lbc`); D-1 keeps the log format; the arena stays through S2 |
| `salvage/s-pck-host` | e9baa5a99 | the paged checkpoint realized on the host (`fn-pck`) | M2 input; on dev `paged-checkpoint.lisp` has 0 executable functions |
| `lane/over` | df2c3c697 (112 ahead) | OVER landing 2 | M2 input |
| `lane/s-extent-cache`, `lane/s-xc2`, `lane/p-xc-span`, `salvage/p-d26-big` | 248809ad2, -, fc1837018, - | extent-cache proof books (+8,508 lines in p-d26-big) | refused: "M2(a) LB deletes the extent cache" (BRANCH-VERDICTS:243, 253, 259, 340) |

### 3.3 Deleted by the cut (M1, 10-16/17)

M1 deleted unreached books: tier A "no host build reaches, no claim names, no surviving test" (c626d6eb7, 226 books) and tier B (82db5c7a7 reads, 6496bf5ee history, 8bec7d6a2 rest, cdb0f7114 consumer). The representation books among them were concrete paths **built and never wired**:
- `nov-column-window`, `nov-column-pieces`: cached NOV row references for byte quanta (PRF-1066).
- `served-catalog-join-host-columns` and 15 siblings: catalog column facts carried across the host protocol (lane join-f2-2).
- `history-page-reader`, `history-page-cursor`, `history-page-io` and 8 more: the incremental history page reader (PRF-1107).
- `arena-forget`: when the owner may forget a reclaimed handle. The arena export `fn-arena-forget` remains, but no book decides when to call it.
- `catalog-pool`, `filed-catalog`, `history-decoded-octet-scan`, `index-backing-table-pages`.
- 8434f025f (10-13, one-world) folded `payload-arena-attach`, `catalog-paged-attach` and `history-paged-attach` into their generics. Not a loss.

None of these was on a served path, so M1 did not delete a running efficient representation. It deleted wiring that had never been connected. **The cut also deleted no list path that was running**: the `fnn-octet-list` count is 263 before and after.

### 3.4 What the record says about why

- rep-wave-d-2 (LANEDUMP, 09-26) found the payload is read inside the transitions and the served machine (`fn-sn-finish` verdict-of-octets, the composite delta, reclaim's tombstones, `fn-nov-body-line-count` "the measured O(L) OVER", 40 books reading `fn-article-payload`). It concluded: "The record's payload and the acceptance state's article/pending payload must become handles TOGETHER (they are one list today; a list in either keeps the sixteen bytes per octet)." The catalog took handles (catalog-record). The acceptance/owner state did not. The owner, view and store node are cons tuples. The archive is the acceptance projection of a replay over `fn-sf-records`, and that is a list whenever the field is based (section 2.2, History row).
- LANEDUMP-rep-octets-stobj (09-25): "fn-octets-list is the escape hatch." It still has 39 book call sites.
- ANATOMY (10-09): "a 3 MiB POST changes representation about seven times between socket and log". Re-traced at dev in section 2.3.

## 4. The gap, in one table

| Data kind | Ember asked for | dev has | Where it diverged |
|---|---|---|---|
| Article octets in flight (POST) | "Octet lists are unacceptable at runtime" (09-25); "never using a linked list of octets for any purpose whatsoever" (10-05) | 18 representation changes, about 14 whole cons-list passes, under the mutex (2.3) | 09-28 B6 added bignum chunks and packed-submission (two new representations) instead of a buffer path. Boundaries 7 and 8 (record and frame codec over the buffer) existed on spike/mega 09-25 and were never re-done on dev |
| Article octets retained | arena with handles, "bytes do not expand into long-lived cons lists" (09-25 mandate) | `fn-arena` on extent pages: retained bytes are concrete | landed 09-25..09-28. Still `fn-arena-seal-list` 154 book sites; `fn-arena-payload` rebuilds the list at commit (step 12) |
| Article octets served (ARTICLE) | streaming views over storage (10-07) | buffer to buffer, 3 copies, no list | matches |
| Host boundary | correspondence theorem at each host boundary, list only logical (D27) | `(fnn-octet-list` 179 -> 263 calls; list-codec lint stuck at 92 since 10-02 | each buffer path landed as a proved twin of a list path, and nothing retired the list path |
| Catalog | "pages are the state": typed u64 columns + byte pool (D41) | `fn-cat-paged` u64 row pages + dense map, with the old `fn-cat$c` nested inside it; M2a adds a third (`fn-lbc`/`fn-cat-lbc`) | each stage added a foundation beside the last (D41's "one representation" became three) |
| Message-ID index | concrete index (D27) | `fn-mlh` fixnum pages, 16 B per lookup | matches |
| History | history on the catalog's rows, no third representation (D42) | `fn-hist-paged` over page store + `(array t)` suffix of cons events; unmigrated readers full-decode to a list | migration "one reader at a time" never finished |
| Owner / store node / view | `fn-sn` a root record (D41, ST5); "the on-disk structure is the in-memory one" (09-27) | 15-, 14- and 9-element cons tuples, lists of connections and feeds, car/cdr chains | ST5 never launched |
| Log records | on-disk = in-memory (09-27, D41) | entry decided in a buffer; each record sliced out as a cons list (`fn-lgb-slice`); written by list -> vector at pwrite | LC (lane/log-lc d999a7fc4) stopped unaudited on 10-16 |
| Checkpoint | dirty pages + root (D41 stage, P8) | schema-3 tables through the publication buffer; `fn-pck` 0 executable functions | paged checkpoint host (salvage/s-pck-host e9baa5a99) unmerged |
| Byte-store crash model | (a specification) | cons lists of alists, by design | correct as a model; it is not a runtime representation |

**The bottom-most decision a methodical rebuild settles first.** What *is* an article's bytes, as one value with one owner, from the socket read to the log write? Is it a handle into one byte-pool extent (written once by the read, sealed in place, framed in place, pwritten from the same pages, reseated to its log extent), with the octet list confined to `:logic` and never callable from `:exec`? Every divergence above follows from leaving this open: each layer (wire scan, injection, queue, record codec, log kernel) picked its own carrier, and the correspondence-twin discipline made each choice locally provable and globally additive. This sits below the log format (D-1 in CUT-M2-STORAGE-DESIGN keeps FNLG, which is compatible with in-place framing) and below the catalog (M2's `fn-cat-lbc` seam), because both of those consume the article's bytes. Settle it as a statement first, then delete the list paths it replaces in the same landing:
- `fnn-octet-list`'s 263 calls go to zero on the served path;
- `fn-octets-list`, `fn-arena-payload` and `fn-arena-seal-list` leave the exec closure;
- packed-submission and body-chunks are deleted, not twinned.
