# Heap bounds: the records' term from the profile's limits, the checkpoint suffix chunked, the open's chunk bounded (2026-09-28)

Lane heap-bounds (Opus 5.5), rows B2, B3 and B4 of COMPLETE-BEFORE-6.6.0. PRF-198 (the figure),
PRF-375 (the breakdown), PRF-261 (the chunked replay). D27, D35 F8.
Context: planning/evidence/f8-reservation-2026-09-28.md (findings F1, F2, F3).

## B2. The records' term is derived, not measured

`*fn-heap-record-octets*` was 12 KiB a record, a measurement on short headers. f8-reservation's long-header
curve (250-octet Message-IDs, 900-octet Subjects) retained about 27 KB a record while posting, so the figure
was not a bound: a store of such records could exceed its heap (exit 4).

What a record retains, structure by structure (books/heap-store-figure.lisp's header names each):

| per | structure | heap octets | posting copy |
|---|---|---:|---|
| record | held row spine and facts, catalog and history-column entries, extent, retention carry | fixed | |
| header octet | overview fields (Subject, From, Date, Message-ID, References) as character strings | 4 | x2 (the checkpoint base's canonical rows) |
| header octet | control words (Cancel-Lock, Cancel-Key) as octet lists | 16 | x2 |
| Message-ID octet | owner view trie (a cons and a list cell a character) | 32 | |
| Message-ID octet | the trie's rebuild while a checkpoint publishes (fn-scka-restore-base) | 32 | |
| Message-ID octet | row and overview strings | 8 | x2 |

The figure charges a fixed 4,096 a record, 32 a header octet (the control words' worst case, 2 x 16), and 48 more
a Message-ID octet (80 in all) at RFC 5536's 250 (every admission checks it: fn-af-message-idp,
fn-record-msgidp). A record's header octets are payload octets, which the history budget charges, and at
most the profile's max-header-octets. So N records holding USED payload octets retain at most

    N x 16,096 + 32 x min(USED, N x HDR)            (each twice: the collector's copy)

KEYSTONE `fn-heap-records-retained-within-the-terms` (records admissible under the profile: Message-ID within
250, header within HDR and a part of the payload). Against the measurement: the long-header shape's term is
59,296 octets a record; 222 Message-ID octets x 80 and 872 Subject octets x 8 is 24.7 KB over the short headers'
state, where 23.5 KB was measured posting. Teeth: tests/acl2/heap-figure-tests.lisp (the record at every
ceiling, tight; a Message-ID of 1,000, a header past HDR, a header outside the payload each fail; the
must-fail; the 12 KiB mutation).

**Consequences (model; measure at convergence).** The figure is a bound now, and larger:

| figure | before | after |
|---|---:|---:|
| small preset, init's reservation (d5ab87aec core) | 1,235 MiB | 1,884 MiB |
| small preset, the launcher's empty-store figure | 826 MB | 1,406 MB |
| small preset, retained state at its bounds | 401 MiB | 1,032 MiB |
| the scale gate's state (T 2^20) | 26,929 MB | 83,697 MB |
| SYNTH_100K (T 131,072, H 512 MiB), the launcher's figure for a 70,000-record store | 8,614 MB | 42,335 MB |

The header term is 64 H (every history octet a header octet whose control words are octet lists), so for a
large history it dominates: 32 GiB of SYNTH_100K's 42 GB.

- The small preset's empty-store run fits OpenBSD's 1,536 MiB login class only with a core of at most 192 MiB of
  dynamic content (the production image's is 141 MiB) and not with the threads' reservation beside it
  (1,782 MB): `fn-heap-small-profile-run-fits-a-small-machine` is restated at 192 MiB, and
  `...-fits-a-two-gib-machine` holds any core up to 512 MiB on 2,048 MiB.
- A bare `init` on a 2 GiB machine (1,536 MB after the system's share) is REFUSED by name: the floor's first run
  is 1,906 MB. On 3 GiB it writes the small preset. This is the friend's OpenBSD node (2 GB).
- The figure is within H of the costliest store (the history bound charges a payload octet two arena octets;
  the store full of header octets, now the worst case, leaves that slack): the tight witness moved from
  "the figure less 1 MiB fails" to "less 9 MiB fails".

**The levers** (each lowers a named coefficient; none is in this lane):

1. The Message-ID trie path-compressed (books/msgid-index.lisp, 814 dependents): 32 of the 80 a Message-ID octet,
   and the publication's rebuild of the base's event index another 32.
2. The control words as strings or byte vectors (control-authority): the header coefficient from 32 to 8.
3. The checkpoint base sharing the live rows instead of re-parsing them (store-checkpoint-arena-writer,
   f8-reservation's F3): halves both.
4. Rungs below the friend floor (heap-reservation's `*fn-heap-friend-rungs*`) so a 2 GiB machine gets a smaller
   store instead of a refusal: a decision on the floor.
5. The credit model (B5): the reservation stops being the admission.

## B3. The reopen's suffix was decoded whole

Over a checkpoint the open kept the suffix's records as octet vectors, then converted every one to an octet
list at once and decoded them in one `fn-store-sn-recover-records` (fn-srs-decode), then interned the whole
decode: two list copies of every suffix octet (16 heap octets an octet each) live together. The model's open
term is one chunk. F1's backtrace was in FN-SRS-DECODE.

Reproduced on hbox (native-n12-abdc0db4c developer image; /tank/fn/scratch/heap-bounds/, driver b3s.py; logs
kept): curve fixture n50000, checkpointed offline, 20,000 posts with the automatic checkpoint deferred
(FN_NATIVE_CHECKPOINT_BUDGET_TEST=1): `open=checkpoint:50000 suffix=20000`, figure 8,614 MB. The reopen at the
figure succeeded with VmHWM 4,585,000 kB; the same with a 2,000-record suffix over 100,000 (syn100k-2k) peaked
at 2,207,016 kB. The suffix alone cost about 2.4 GB transient, where the model's open term is 0.76 GB.

The cause, named: before the fix the same reopen at 3,072 MB died "Heap exhausted during garbage collection"
in FN-INTERN-EVENTS (the whole decoded suffix interned at once), and at 2,048 MB in FNN-RECOVER-LOG (the whole
suffix as octet lists and its decode). F1's backtrace was the same path (FN-SRS-DECODE). F1's exhaustion AT the
launcher's figure did not reproduce on today's image: the synthesized store's state term leaves slack below
its bounds; the transient over the model's open term did.

| reopen of the 50,000 + 20,000-suffix store | before (native-n12-abdc0db4c) | after (native-hb1, c6870ef38) |
|---|---|---|
| at 2,048 MB | heap exhausted (FNN-RECOVER-LOG) | opened, 18.2 s, VmHWM 986,136 kB |
| at 3,072 MB | heap exhausted (FN-INTERN-EVENTS) | opened, 17.6 s, VmHWM 1,218,364 kB |
| at the launcher's figure | 8,614 MB: VmHWM 4,585,000 kB | 42,335 MB (B2's figure): VmHWM 1,543,228 kB |

The 100,000-record store (syn100k-2k, checkpointed at 100,000, 1,999 posts after) reopens at its figure
(42,401 MB) with VmHWM 2,194,512 kB. Logs: hbox /tank/fn/scratch/heap-bounds/b3s-{pre,post}-*.{json,err},
the owners' stderr beside each store.

Fix: `fnn-recover-suffix-intern` (host/native/io.lisp) decodes and interns the suffix a chunk at a time
(`fnn-recover-record-chunks`, fn-srs-chunk-fullp) on top of the loaded arena with the guard-verified
fn-srs-intern-step, folding the txids from each chunk's decode; both checkpoint paths use it. Any chunking
interns what one step over the whole suffix interns (PRF-261: fn-srs-steps-are-one-step-of-the-concatenation,
fn-srs-one-step-is-the-intern-of-the-decode, for any arena), which is fn-scka-recover-rows' fn-intern-events of
the decode.

## B4. The open's chunk is bounded by the input

`fn-heap-open-chunk-bound` = min(OU, quantum + R): an empty store's open holds no chunk (the small preset's
empty-store figure loses 76 MiB). Monotone in OU and R (`fn-heap-open-chunk-bound-monotone`).

## What ran

REPL on hbox (proof_repl, --ld-local over the changed books): books heap-store-figure, heap-figure,
heap-open-nursery, heap-reservation, heap-breakdown; tests heap-figure-tests, heap-reservation-tests,
heap-breakdown-tests, heap-open-nursery-tests, all admitted. Pinned figures re-taken with tools/retake_pins.py.
Certification and natives: the lane's LANEDUMP and the commit that adds the manifests.
