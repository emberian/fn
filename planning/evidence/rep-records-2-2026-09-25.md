# Records at write and the Message-ID trie on concrete twins (D27 boundaries 4 and 5), 2026-09-25

Lane `lane/rep-records-2`, from dev `0a608298`. Design:
`planning/design-2026-09-25-representation.md` §5, wave A items 4 and 5.
Commits: `b56dbe2c`, `697b6d03` (before the laptop crash), `60c0e9c5`,
`7e268ebe`, `8e16b7e2`, `2b5f494d`, and the commit carrying this record.

## What changed

The octet-list record recognizer `fn-record-p` is no longer evaluated on the
POST path (0 of 2223 profile samples across 13 rounds, from 190 of 3560 at
the merge base), and no Message-ID is converted to a character list on the
served lookup paths.

- **Encoder at write.** `fn-rcon-store-event-encode`
  (`books/records-concrete.lisp`) dispatches on the concrete recognizer.
  The codec behind the seam is `fn-rcon-record-encode-impl`
  (`books/records-codec-concrete.lisp`): `fn-record-encode-impl` with
  `fn-rcon-record-p` in place of `fn-record-p`.
  `books/records-attach-concrete.lisp` re-attaches `fn-record-encode` to it
  in the host images, after `codec-attach`. The alternative, editing
  `books/records-attach.lisp`, would send 190 roots back to certification
  (`certify_books.py --affected-by --dry-run`) for no change in any
  theorem. The attachment is not logic, and the keystone makes the two
  attachments agree on every input. The recognizer (`fn-rcon-record-p` and
  its keystone) moved from records-concrete into records-codec-concrete, so
  the attachment book does not include the store.
- **Record wrappers and dispatchers.** The host now calls these twins:
  `fn-rcon-sbud-pending-sequence`, `fn-rcon-sn-io`, `fn-rcon-ocfg-io`
  (`books/records-concrete-owner.lisp`), and `fn-rcon-store-event-p`,
  `-sequence` and `-txid` in the store bridge.
- **The prepare.** `books/owner-prepare-carried.lisp` `fn-pcar-next-lower`
  reads the txid through `fn-rcon-store-event-txid`. `fn-pcar-spc-prepare`
  recognises, projects and binds through `fn-rcon-record-p`,
  `fn-rcon-cpe-projection-step` and `fn-rcon-sn-record-bindsp`. These were
  the list recognitions left on the after profile of `b56dbe2c`.
- **The trie.** `books/msgid-index-concrete.lisp`: `fn-mxc-lookup` walks the
  same trie by `(char msgid i)`. The reader retrieval chain
  `fn-pix-msgid-retrieval-indexed` … `fn-pix-peer-delegate-pinned`
  (`books/peer-offer-indexed.lisp`) uses it. `books/served-carried.lisp`
  `fn-scar-peer-step-pinned` (reader sessions) and
  `books/peer-guard-carried.lisp` `fn-pgc-peer-arm` (peer sessions, for what
  the peer commands do not answer) call it. The IHAVE/CHECK history test
  `fn-pix-history-hasp` uses it too, and now tests non-emptiness with
  `(< 0 (length msgid))` instead of consing the character list.

## Theorems (no hypothesis; each subject guard-verified at its reference's guard)

| Theorem | Statement | Host line reaching the subject |
| --- | --- | --- |
| `fn-rcon-record-p-is-record-p` | `(equal (fn-rcon-record-p x) (fn-record-p x))` | Every record path below |
| `fn-rcon-record-encode-impl-is-record-encode-impl` | `(equal (fn-rcon-record-encode-impl r) (fn-record-encode-impl r))` | Attached to `fn-record-encode` (host/native/build.lisp, build-dtn.lisp, tools/run_store.py); `host/owner-host.lisp:521` `fn-owner-consumer-local-poll` |
| `fn-rcon-store-event-encode-is-store-event-encode` | `(equal (fn-rcon-store-event-encode e) (fn-store-event-encode e))` | `host/owner-host.lisp:553` `fn-owner-pending-octets`; `host/store-node-host.lisp:584` |
| `fn-rcon-sbud-pending-sequence-is-sbud-pending-sequence` | `(equal (fn-rcon-sbud-pending-sequence s) (fn-sbud-pending-sequence s))` | `host/owner-host.lisp:562`; `host/store-node-host.lisp:591` |
| `fn-rcon-sn-io-is-sn-io` | `(equal (fn-rcon-sn-io s op r) (fn-sn-io s op r))` | `host/store-node-host.lisp:477` `fn-store-sn-io` |
| `fn-rcon-ocfg-io-is-ocfg-step` | `(equal (fn-rcon-ocfg-io oc op r) (fn-ocfg-step oc (list :store (list :io op r))))` | `host/owner-host.lisp:349` `fn-owner-io` |
| `fn-pcar-spc-prepare-is-spc-prepare`, `fn-pcar-next-lower-is-next-lower` (statements unchanged; bodies rerouted) | as before | `host/owner-host.lisp:398` `fn-pcar-sbud-prepare` |
| `fn-midx-concrete-lookup-is-lookup` | `(equal (fn-mxc-lookup msgid trie) (fn-midx-lookup msgid trie))` | `host/owner-host.lisp:1430` `fn-owner-chunk` → `fn-scar-ocfg-read-tls-prefix` → … `fn-scar-peer-step-pinned` |
| `fn-pix-peer-delegate-pinned-is-peer-delegate-pinned` | `(equal (fn-pix-peer-delegate-pinned …) (fn-peer-delegate-pinned …))` | the same chain; reader and peer sessions |
| `fn-pix-history-hasp-is-peer-history-hasp` (statement unchanged) | under `fn-node-statep` and `fn-midx-correspondencep` | the same chain; IHAVE/CHECK |

Registry: `planning/proof-events.json` and `planning/proofs.json` PRF-014
(records) and PRF-067 (trie).

## Teeth

- `tests/acl2/records-concrete-tests.lisp` covers:
  - On the staged record of a reachable POST, the encoder twin is non-empty
    and equals `fn-record-encode-impl` and `fn-record-encode`.
  - A shaped record with a 251-character Message-ID encodes to nil in both.
  - The 250-character one encodes in both.
  - Non-records encode to nil.
  - A `must-fail` refutes "every shaped record encodes" at the 251 record.
  - The attachment names `fn-rcon-record-encode-impl`, and the twin is
    `:common-lisp-compliant` with the reference's guard.
  - The earlier witnesses cover the dispatchers at write and the owner
    observation (`:record-directory :ok` reaches the completing owner,
    `:error` fences).
- `tests/acl2/peer-offer-indexed-tests.lisp` covers:
  - STAT 223 and 430 through the retrieval twin, equal to the reference.
  - The empty trie answers 430 for the held article. The lookup is what
    answers.
  - The empty Message-ID takes the scan in the history test.
  - With the empty trie and the matching list, the history test answers nil
    where the scan answers t.
- `tests/acl2/peer-guard-carried-tests.lisp`: a peer session's STAT
  through `fn-pgc-peer-arm` over the pinned view gives 223 for the held
  article and 430 for an absent one. ARTICLE is also checked. Each equals
  `fn-peer-step-pinned`.
- `tests/acl2/msgid-index-concrete-tests.lisp`: the index lemma's `(natp i)`
  is needed (a `must-fail` at i = −1). The top-level keystones have no
  hypothesis to remove.

## Certification (persvati, `w25/acl2-literal`, 2 jobs, 300 s, incremental from `/home/ember/fn-certcache`)

- run-20260925T025444Z-a5d9, manifest `certify-20260925T025505Z-3707333`,
  and manifest `certify-20260925T030120Z-3766397`, both before the crash.
  The second covers `msgid-index-concrete`, its tests and
  `peer-offer-indexed` at bytes these files still have.
- run-20260925T033915Z-8ae6, manifest `certify-20260925T034017Z-4130348`,
  at `60c0e9c5`. It certified records-codec-concrete plus the union of the
  `--affected-by` sets of records-codec-concrete, records-attach-concrete,
  peer-guard-carried and owner-prepare-carried. Status passed. The slowest
  book was owner-offer-indexed at 8.5 s; records-codec-concrete took 6.8 s
  and records-attach-concrete 1.8 s. All 181 source digests match the
  current tree.
- run-20260925T034429Z-9535, manifest `certify-20260925T034524Z-4177436`,
  at `7e268ebe`, `--affected-by books/peer-offer-indexed`. Passed; the
  slowest book took 6.5 s.
- run-20260925T034833Z-e873, manifest `certify-20260925T034925Z-22558`, at
  `8e16b7e2`, records-concrete-tests: passed in 4.8 s.
- `tools/green_check.py --changed-since 0a608298`: 13 changed books, 11
  books include one, 0 not green at the bytes a merge would carry.
- hbox in place (`round2/setup3.sh`, default-profile roots from
  `/tank/fn/certcache`, `w28/acl2-literal-4g`, 8 jobs) passed for the base2,
  after2 and after3 trees before each image was built.
- `tools/ledger.py --check`: the only errors are `ledger.json` and
  `ledger.md` being stale, which the coordinator regenerates.

## Measurement (hbox, developer images, 2026-09-25 03:44 to 04:02 UTC)

Images, with their `round2/images2.sha256` and `images3.sha256` hashes:

| Name | Source | Launcher |
| --- | --- | --- |
| base2 | merge base `0a608298` | `d04801eb…` |
| after | `b56dbe2c`, from before the crash | `ecbe87a8…` |
| after2 | `60c0e9c5` | `fdace73e…` |
| after3 | `7e268ebe` | `8f432186…` |

Box load was 3.3 to 3.8. hbox has no other tenant.

**POST CPU at N = 120** (`prof_post.py`: 48 POSTs from 72 to 120; SBCL
sprof at 1 ms; base2, after and after2 alternated for 13 rounds). The
shares below are summed "Total" samples over all rounds
(`round2/summary.txt`).

| | base2 | after | after2 |
| --- | ---: | ---: | ---: |
| samples per 48 POSTs, median (range) | 192 (121 to 611) | 146 (116 to 637) | 130 (124 to 544) |
| `fn-record-p` | 190 (5.3%) | 77 (2.5%) | **0** |
| `fn-record-string-octets-aux` | 230 (6.5%) | 127 (4.1%) | 18 (0.8%) |
| `fn-record-encode-impl` / twin | 33 / 0 | 29 / 0 | 0 / 16 (0.7%) |
| `fn-pcar-spc-prepare` | 116 (3.3%) | 109 (3.5%) | 39 (1.8%) |
| `fn-rcon-record-p` | 100 (2.8%) | 101 (3.2%) | 92 (4.1%) |
| `fn-frame-digest` | 41.9% | 41.4% | 43.2% |

In after2, `fn-record-string-octets-aux` is called only for the group-name
grammar (`fn-record-group-namep`), `fn-cfg-labelp`, the encoder's output
(the msgid and metadata octets it writes) and one log line. In base2 it was
called from the recognizer's metadata, octet-string and ASCII tests. The
sample count per POST falls in its median, but the rounds overlap and one
round per image is a load spike. The profiler takes about 3 samples per
POST, as the rep-intent record also found, so **the shares are the
figure**. They say the list recognitions and conversions went from about
12% of POST CPU to under 1%. What is left of the recognizer is the concrete
one (4%), which each accessor re-runs (`fn-rcon-store-event-sequence`,
`-txid` and `-p` each recognise the same record).

**POST wall and RSS on tmpfs** (`msgid_measure.py`, N = 120, 64 samples; 6
runs for base2, 3 for each after image; medians per run):

| | base2 | after | after2 | after3 |
| --- | --- | --- | --- | --- |
| POST, last quarter | 1.87 to 1.91 ms | 1.82 to 1.83 ms | 1.74 to 1.76 ms | 1.75 to 1.82 ms |
| RSS after load | 432 to 433 MiB | 422 MiB | 411 MiB | 410 MiB |

The last-quarter POST wall falls about 7% at N = 120, where tmpfs makes the
wall the CPU. This is a constant factor per POST; it changes no exponent in
N. The RSS drop is GC headroom from less transient garbage, not data
(`rep-heap-2026-09-25.md`: the owner collects every 64 MiB).

**STAT and CHECK by Message-ID at N = 120** (same runs, medians, ms):

| | base2 | after | after2 | after3 |
| --- | --- | --- | --- | --- |
| STAT, held | 0.090 to 0.092 | 0.090 | 0.090 to 0.091 | 0.091 (one run 0.179) |
| STAT, absent | 0.080 to 0.082 | 0.081 | 0.081 to 0.082 | 0.080 to 0.082 |
| CHECK, duplicate | 0.114 to 0.117 | 0.115 | 0.114 to 0.117 | 0.116 to 0.119 |
| CHECK, absent | 0.120 to 0.122 | 0.120 to 0.121 | 0.120 to 0.123 | 0.123 to 0.124 |

**No difference is measurable.** The command is a socket round trip of about
0.1 ms. The transient key list the index walk no longer builds (one cons
per character, about 1 KiB for a 65-character Message-ID) costs well below
that resolution. Occasional runs sit at 0.18 ms in every image; that is the
bimodality the representation record also saw.

**The trie's memory.** The trie's nodes do not change: `fn-mxc-extend`,
`-build` and `-refresh` equal their references, and the owner still builds
the trie with `fn-midx-refresh`. RSS after the STAT phase minus RSS after
load is 7 to 8 MiB in every image.
What went away per lookup is the transient character list only.

Raw data is in `rep-records-2-2026-09-25/round2/`: flats and graphs, `p2-*.out`,
`s2-*.json` and the scripts. The pre-crash round (`post-*`, `prof-*`,
`shm-*`) compared `b56dbe2c` with a dev `087f7213` image, which is not this
lane's merge base; its summary files are kept and its figures are not used
here.

## What remains

- The recognizer is re-run per accessor: sequence, txid, event-p and
  generation each call `fn-rcon-record-p` on the same record, and that
  recognizer walks the payload (`fn-record-payloadp`, O(L)) and the group
  names. Carrying "is a record" once, as the commit and prepare carry
  their relations, would remove most of the remaining 4%.
- The encoder's output is an octet list (`fn-record-string-octets` for the
  msgid and metadata, then `append`); that is the frame/write boundary.
- The group-name grammar still converts each name (`fn-record-group-namep`).
- The wire token is converted to a string before the lookup
  (`fn-nntp-token-string`, `fn-record-octets-string`). The owner's refresh
  (`fn-own-refresh` → `fn-midx-refresh`) and the OVER/XOVER bucket
  resolution (`books/group-bucket-article.lisp`) still walk the character
  list. Rerouting the refresh is a twin of `fn-own-refresh` under every
  owner transition, which is a freeze item.
- `records-attach` still attaches the list implementation for the proof and
  test books that include it. The host images override it. Folding the two
  into one attachment is an edit of records-attach and its closure, at a
  freeze.
- `tools/ledger.py` warns `accessor-equality` on the enabled twin
  equalities. That is the same pattern as boundary 1's twins, and the
  equalities are what rewrite twin to reference in every dependent proof.
