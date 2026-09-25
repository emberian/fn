# Representation, first boundary: the record recognizer reads its strings in place, 2026-09-25

Lane `lane/representation`, from dev `67b028c7`. Commit `e0dc3f08` (design,
book, twins, teeth, the carried commit and prepare rerouted, registry) and
the evidence commit that carries this record and `representation-2026-09-25/`.
Design: `planning/design-2026-09-25-representation.md`.

## What the cost was

`fn-record-p` (books/records-shape.lisp, `fn-defrecord`) tests the record's
four text fields through the octet-list domain. `fn-record-octet-stringp`
and `fn-record-ascii-stringp` convert the ACL2 string to its list of
char-codes (`fn-record-string-octets`: a `coerce` and one cons per
character) and walk the list; `fn-record-msgidp` and
`fn-record-metadata-bytes-p` convert it a second time for the length bound.
Eight conversions per recognition, and the POST path recognises the same
record on four paths: the prepare's candidate test, the commit's seek (a
record pair per seek), the completion gate (the binding test, the two
projection steps) and the finish (`fn-store-event-sequence` and `-txid`
three times each). On the dev base image at N = 120 that is 21 to 22% of
POST CPU in `fn-record-p`, of which `fn-record-metadata-bytes-p` alone is
13 to 15%, and `fn-record-string-octets`/`-aux` are 30 to 32% of all
samples (the rest from `fn-record-group-namep` and `fn-store-prov-post`).

## The concrete recognizer (`books/records-concrete.lisp`, prefix `fn-rcon-`)

An ACL2 character has a code in 0..255 (`char-code-linear`), so the
octet-domain test the model states over the converted list is `stringp`.
The length bound is `length` (O(1) on a simple string). The ASCII test is a
walk by index with `char` and `char-code` (`fn-rcon-ascii-from`). Nothing
is allocated. `fn-rcon-record-p` is `fn-record-p`'s conjunction with the
three string tests replaced; the payload walk (`fn-record-payloadp`) and
the group-name grammar (`fn-record-groups-validp`) are the references.

| Theorem | Statement | Host line |
| --- | --- | --- |
| `fn-rcon-record-p-is-record-p` (keystone) | `(equal (fn-rcon-record-p x) (fn-record-p x))` for every `x`. No hypothesis. Both are guard t and guard-verified | `host/owner-host.lisp` `fn-owner-finish-submission` (line 601) calls `fn-ccar-own-finish` at line 606 (books/owner-commit-carried.lisp), whose seek, completion gates and finish recognise records through the twins below; `fn-owner-prepare` (line 346) installs `fn-pcar-sbud-prepare` at line 392 (books/owner-prepare-carried.lisp), whose candidate test does |
| `fn-rcon-octet-stringp-is-stringp` (keystone, the domain) | `(equal (fn-record-octet-stringp text) (stringp text))` for every `text` | - |
| `fn-rcon-msgidp-is-msgidp`, `fn-rcon-metadata-bytes-p-is-metadata-bytes-p` | each concrete field test equals its reference for every input | - |
| `fn-rcon-store-event-p-is-store-event-p`, `fn-rcon-store-event-sequence-is-store-event-sequence`, `fn-rcon-store-event-txid-is-store-event-txid`, `fn-rcon-store-event-generation-is-store-event-generation`, `fn-rcon-sf-record-pair-is-sf-record-pair`, `fn-rcon-sn-record-bindsp-is-sn-record-bindsp`, `fn-rcon-cpe-projection-step-is-cpe-projection-step`, `fn-rcon-th-prefix-step-is-th-prefix-step` | each twin (its reference with `fn-record-p` replaced) equals its reference for every input; each guard is the reference's guard, verified | reached through `fn-ccar-seek`, `fn-ccar-completion-core-enabledp`, `fn-ccar-completion-enabledp`, `fn-ccar-sn-finish`, `fn-ccar-completion-names-submission-p` and `fn-pcar-candidatep` |

**No statement of any existing theorem changed.** `fn-ccar-own-finish-is-own-finish`,
`fn-ccar-seek-is-find-record` and `fn-pcar-sbud-prepare-is-sbud-prepare`
are proved as before, with the twin equations added to the theories of the
proofs that open the rerouted bodies. The logical model over octet lists
does not move; the twins are the only new definitions and the
correspondences the only new obligations. The local index-walk lemma
`fn-rcon-ascii-from-is-ascii-octet-listp-of-nthcdr` (a string and a
natural index) is the one lemma with hypotheses, and it is local.

**The exponent, from the definitions.** `fn-record-p` is O(M + P + G)
time with 2M + G conses per recognition, for M the characters of the four
text fields, P the payload octets and G the group-name characters.
`fn-rcon-record-p` is O(P + G + |msgid|) time with G conses: the three
metadata tests are O(1), the Message-ID walk allocates nothing, and only
the group names still convert. Per recognition of the witness record
(65-character Message-ID, metadata 73 + 77 + 77): 584 conses and eight
`coerce` calls removed, 328 payload conses walked as before.

## Teeth (`tests/acl2/records-concrete-tests.lisp`)

- **Witness.** The completing article record of `*osi-completing*`
  (owner-served-invariants-tests, reached by `fn-own-run`): Message-ID of
  65 characters, payload of 328 octets, metadata of 73, 77 and 77
  characters. The twins agree with their references on it, on a retention
  event built from its strings, and on non-records (nil, a number, a
  string, a short list); the binding test and both projection steps agree
  on the witness store.
- **Each string clause separates alone**, every other conjunct of
  `fn-record-p` intact: a Message-ID of 250 characters (accepted) against
  251; a code-200 character at position 250 of an otherwise valid
  250-character Message-ID (an octet string, not ASCII); the empty string;
  a non-string. Metadata of 256 (accepted) against 257 characters, which is
  a string and an octet string that the bound alone refuses, so the
  concrete test is more than `stringp`; the empty string; a number.
- **The hypotheses.** The keystones have none. The local index-walk lemma's
  `(natp i)` is necessary: at i = -1 the walk answers t without looking and
  the list form (nthcdr's `zp` case) sees the whole string, so on the
  high-code string they differ; the `defthm` instance is `must-fail`.
- **The executed code.** Every `fn-rcon-` function is
  `:common-lisp-compliant`, and the guards of the recognizer, the binding
  test and the sequence dispatcher are their references' guards.

## Certification

- **persvati, ACL2 8.7, toolchain `1b4169e9…4286`, 2 jobs, 300 s, the cache
  `/home/ember/fn-certcache`, no `--closure`.**
  - Run `run-20260925T021006Z-e426`, manifest
    `manifests/certify-20260925T021027Z-3265528.json`, passed: the two new
    roots, `books/records-concrete` 2.18 s and
    `tests/acl2/records-concrete-tests` 4.34 s. (`--affected-by` does not
    widen an explicit root list; hence the second run.)
  - Run `run-20260925T021137Z-d938`, manifest
    `manifests/certify-20260925T021147Z-3278480.json`, passed, `--affected-by`
    the three changed books with no explicit root: 14 roots, 12 certified
    (2 already at these bytes), 26.7 s wall. `books/owner-commit-carried`
    4.09 s, `books/owner-prepare-carried` 4.09 s, `books/owner-advance-carried`
    4.12 s, `books/owner-commit-ocl` 4.12 s, `books/owner-offer-indexed`
    5.22 s, `books/owner-recover-ocl` 4.48 s, and the six dependent test
    books (`owner-commit-carried-tests` 4.54 s, `owner-prepare-carried-tests`
    4.59 s, `owner-advance-carried-tests` 4.73 s, `owner-recover-ocl-tests`
    4.29 s, `peer-guard-carried-tests` 4.37 s, `peer-offer-indexed-tests`
    4.27 s). Every book touched or affected is under 10 s at 2 jobs.
- **hbox, in place, `w28/acl2-literal-4g`, 8 jobs, 900 s** (the
  developer-image builds): `certify-20260925T021059Z-2378605` certified
  `books/records-concrete` (2.57 s), `owner-commit-carried`,
  `owner-prepare-carried`, `owner-advance-carried`, `owner-commit-ocl` at the
  lane's bytes, status passed (`representation-2026-09-25/hbox-after-certify-*.json`);
  `proof_artifacts acquire`/`validate` loaded the default profile, 290 books.
- **Host.** `host/owner-host.lisp` (comment only) was translated by both
  image builds. `tools/host_shape_check.py`: 0 findings.
- **`make check`.** Its errors are `planning/ledger.*` stale (the
  coordinator regenerates the ledger).

## Measurement (hbox, developer images, 2026-09-25 02:07 to 02:17 UTC)

- **Images** (`representation-2026-09-25/*-image.sha256`): before = dev
  `67b028c7`, launcher `24906a1c…`, core `b580589b…`; after = lane
  `e0dc3f08`, launcher `c342d0b0…`, core `9b49be3c…`. Both built by
  `setup2.sh` (default-profile roots certified in place from
  `/tank/fn/certcache`), `build.sh` and `tools/build_native_host.sh` under
  `swarm-build`, with OpenSSL 3.5.8, and each with a profiling twin
  (`build/prof-build.lisp`, the served-path lane's sprof hook). Scratch
  `/tank/fn/scratch/representation/`; the scripts are in the evidence
  directory. Box load 1.3 to 2.4 throughout; no other tenant.
- **Client.** `tools/msgid_measure.py` at the lane's revision (the
  advance-projection client: `TCP_NODELAY`, per-read quick-ack).

**CPU per POST at N = 120** (`prof_post.py`, 48 POSTs from 72 to 120, SBCL
sprof CPU mode at 1 ms, base and after alternated, three rounds). Sample
totals and the shares of the graph "Total" column:

| round | before: samples (÷48) | after: samples (÷48) | before: `fn-record-p` | after: `fn-record-p` + `fn-rcon-record-p` | before: string conversions | after: string conversions | before: commit `fn-owner-finish-submission` | after |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| r1 | 727 (15.1) | 590 (12.3) | 21.3% | 4.1% + 3.1% | 30.7% | 6.6% | 18.7% | 5.3% |
| r2 | 682 (14.2) | 604 (12.6) | 22.1% | 5.1% + 2.6% | 31.6% | 7.6% | 19.8% | 5.6% |
| r3 | 703 (14.6) | 597 (12.4) | 21.5% | 6.2% + 2.8% | 29.7% | 10.8% | 19.6% | 5.5% |

- **Samples per POST** fell from 14.2 to 15.1 to 12.3 to 12.6: −15 to
  −19%. The sampler's rate is not calibrated to wall time (the same
  method read 4.1 samples per POST on the advance-projection session), so
  the shares and the relative change are the figures; the tmpfs wall below
  is the absolute one.
- **The recognizer.** `fn-record-p` fell from 21 to 22% to 4 to 6%. What
  remains of it is outside the rerouted chains: the record encoder's
  recognition at write (`fn-store-event-encode`, `fn-record-encode-impl`),
  `fn-sf-record-dir-result`, `fn-sbud-pending-sequence` and the host's
  `fn-store-record-sequence`/`-txid` wrappers, which still call the list
  dispatchers. `fn-rcon-record-p` is 2.6 to 3.1%, of which the payload walk
  is 1.5 to 2.7% and the group names 0.7 to 1.2%; the index walk
  (`fn-rcon-ascii-from`) is 0.5%.
- **The conversions.** `fn-record-string-octets`/`-aux` fell from 30 to
  32% of samples to 6.6 to 10.8%; the rest is `fn-record-group-namep`,
  `fn-store-prov-post` and the remaining list-dispatcher calls above.
- **The commit** (`fn-owner-finish-submission` → `fn-ccar-own-finish`)
  fell from 18.7 to 19.8% to 5.3 to 5.6% of a smaller total: in samples,
  135 to 138 to 31 to 34 per 48 POSTs (−76%). **The prepare**
  (`fn-owner-prepare`) from 40 to 45 samples to 19 to 31.
- **Unchanged, as they should be:** `fn-frame-digest` 254 to 278 samples
  before, 258 to 272 after (its share rises from 36 to 40% to 43 to 46% of
  the smaller total); `fn-owner-submission-intent` 113 to 122 before, 117
  to 120 after; `fn-own-feed-intent-id` 127 to 152 before, 131 to 142
  after. The lane touched neither; the design ranks them next.

**POST wall** (`msgid_measure.py`, 16 samples per point, medians of the
first and last quarter):

| store | N | before: last quarter | after: last quarter | before: RSS after load | after: RSS after load | before: load | after: load |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| tmpfs `/dev/shm` | 16 | 2.26 ms | 2.30 ms | 336 MiB | 323 MiB | 0.04 s | 0.05 s |
| tmpfs | 50 | 2.40 ms | 1.86 ms | 399 MiB | 358 MiB | 0.12 s | 0.10 s |
| tmpfs | 120 | 2.42 ms | 1.83 ms | 531 MiB | 433 MiB | 0.30 s | 0.22 s |
| ZFS `/tank` | 16 | 121 ms | 317 ms | 336 MiB | 323 MiB | 2.25 s | 4.49 s |
| ZFS | 50 | 200 ms | 134 ms | 399 MiB | 358 MiB | 10.8 s | 10.7 s |
| ZFS | 120 | 150 ms | 171 ms | 531 MiB | 432 MiB | 28.6 s | 23.7 s |

- **On tmpfs, where fsync is free and the wall is the CPU:** at N = 120
  the POST median fell from 2.33 to 2.42 ms (first and last quarter) to
  1.83 to 1.90 ms, −0.5 ms, −21%; at N = 50 from 2.39 to 2.40 to 1.86 to
  2.00; at N = 16 unchanged within noise (2.26 to 2.46 against 2.30 to
  3.01). The 120-article load fell from 0.30 to 0.22 s. This is the
  absolute figure for the change: about half a millisecond per POST at
  N = 120, of a 2.4 ms POST.
- **On `/tank` the wall is the medium.** 121 to 317 ms medians in both
  images, in the ZFS durable-write and delayed-ACK modes the
  advance-projection record measured (its 42 ms mode was a quieter txg
  schedule); no wall figure on `/tank` is claimed for this change.
- **RSS after load at N = 120: 531 MiB to 432 MiB (−99 MiB), at N = 50
  399 to 358, at N = 16 336 to 323.** An observation: the removed
  conversions were transient garbage, and SBCL's resident set grows with
  allocation between collections; `rss_after_load_kib` reads `VmRSS` with
  no full GC. It is not a measure of live data (the design, §3).

**The cost sentences, with their scope:**

- **The recognizer.** Before: O(M + P + G) time and 2M + G conses per
  recognition, on four paths per POST. After: O(P + G + |msgid|) and G
  conses, on the commit and the prepare; the encoder's and the host
  wrappers' recognitions (4 to 6% of POST CPU) still convert. Measured at
  N = 120: 21 to 22% of POST CPU to 7 to 9% (both recognizers together),
  −15 to −19% of POST CPU, −0.5 ms of a 2.4 ms POST on tmpfs. This holds
  for every input: the correspondences have no hypothesis.
- **Not N-dependent.** The recognizer's cost is per record; the lane
  changes no exponent in N, and the tmpfs POST wall is flat in N before and
  after within 0.1 ms.

## What remains on the POST path (after image, N = 120, share of CPU)

- **`fn-frame-digest`, 43 to 46%** (unchanged in samples): SHA-256 over
  octet lists, of which `fn-own-feed-intent-id` computed three times is 22
  to 24%, the host-direct subject and obligation identities and the frame
  trailers the rest. Design ranks 2 and 3.
- **`fn-owner-submission-intent`, 20%**: the intent identity twice in one
  host call. Design rank 2.
- **The remaining list recognitions, 4 to 6%**: the record encoder at
  write, `fn-sf-record-dir-result`, `fn-sbud-pending-sequence`, the host's
  `fn-store-record-sequence`/`-txid` (io.lisp:710, :712).
- **Inside `fn-rcon-record-p`, 3%**: the payload walk (rank 4) and the
  group names (rank 5).

## Not done

- The prepare's `fn-pcar-next-lower` fold and the `fn-sf-record-valuesp`
  guard still name the list dispatchers (guards and logic; not executed per
  POST).
- The encoder's recognition at write and the host wrappers above.
- `planning/ledger.*` not regenerated.
