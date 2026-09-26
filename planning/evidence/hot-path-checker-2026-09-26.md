# hot-path-checker, 2026-09-26: a static finder of retained-state walks, and the scaling rows that test it

Lane `lane/hot-path-checker` from dev `17ff24aa`. Brief:
`build/coordinator/queue/done/w4-hot-path-checker.txt` (PKT-334; answers
2026-09-26 §2). Ids: PKT-447 (what remains) and PKT-448 (finds that no earlier
packet owned). No book changed, so there is no PRF and no farm run.

## What changed for a user

`python3 tools/hot_path_check.py --report` prints every path from a host entry
to a traversal of retained Store history (N), held BP fragments (F) or queued
BP jobs (J). Each line gives the dimension, the walking primitive, the
book:line, the host line and a class. `--why FUNCTION` prints every host entry
that reaches a function, each with one shortest call path. `make check` runs
`--summary --strict`. Every find is listed in `planning/hot-path-findings.json`
with its owning packet. A NEW unexpected find, or a listed find that no longer
occurs, fails the check.

`python3 tools/scale_probe.py box REV` produces the one-dimension scaling rows
on hbox; `fetch REV` prints them.

The checker's silence is not a proof. §2 lists what it cannot follow.

## 1. The method (tools/hot_path_check.py, commit 0fc6dd18)

**Reading.** The checker reads with ledger's reader, through
`session_depth.Reader`'s line-keeping subclass, so a find names the line of the
walking term. It also uses ledger's `defrecord_expansion`, `declared`,
`program_mode` and `encapsulated_names`, and `reach_check.attachments` for the
`defattach` edges. It writes no parser of its own. Books under `books/`, and
host files under `host/` and `host/native/`, are read (7.6 s for the whole
tree).

**Seeds.** `tools/hot_path_dimensions.json` lists the accessors whose value is
a list growing in a dimension, whatever their argument:

| Dimension | Seeded accessors |
| --- | --- |
| N | `fn-sf-records`, `fn-sf-successes`, `fn-sn-config-history`, `fn-state-articles`, `fn-sn-verdicts`, `fn-node-bindings`, `fn-retain-pins`, `fn-retain-releases` |
| F | `fn-bpnf-held-list` |
| J | `fn-bpn-machine-state-jobs`, and the formal `offered` of `fn-bpnj-contact-next`, which the host threads across a contact |

A seeded value keeps its dimension through list-preserving operations:
`cdr`, `nthcdr`, `append`, `cons` onto it, `reverse`, `take`, `let`, `if`,
and `mv` positions. It also keeps it through every formal a caller binds it
to. The analysis is parametric: each function's summary says which formals its
walks and results derive from, and a second pass carries concrete dimensions
down from the host definitions (session_depth's seeded propagation, made
interprocedural).

The dimension files' B (request bytes) and K (reply records) are declared and
not seeded. Walking the request is input-proportional by design. No accessor
yet names a reply list, so the output-proportional class is empty (§3).

**Traversals.** A traversal is one of:

- a walking primitive applied to a seeded value: `len`, `length`, `nthcdr`,
  `nth`, `take`, `butlast`, `last`, `member*`, `assoc*`, `position*`,
  `append` (all but the last argument), `revappend`, `reverse`,
  `true-listp`, `remove*`, `no-duplicatesp*`, `subsetp*`, `strip-cars`,
  `coerce`, `fnn-octets`, `mapcar`, `find`, `sort`, `dolist`, or
  `loop ... in/on/across`;
- a self-recursive call on a shrinking seeded formal. This covers
  recognisers, encoders and replay folds.

A find is keyed `function primitive dimension`.

**The executed path** (specs/host.md, "The decimal-octet pipe": "A
`:program` wrapper therefore runs raw beneath its counterpart"):

- **Raw Lisp** runs `mbe`'s `:exec`, `mbt` is `t`, and no callee guard is
  evaluated. This covers a guard-verified body and everything beneath a
  `:program` host wrapper.
- **A native dispatch** `(fnn-core 'f ...)` (also `fnn-core-state`,
  `fnn-call`, `fnn-owner-core` and the rest, listed in the dimensions file)
  calls f's executable counterpart. **f's guard is evaluated**, then f's raw
  body runs if f is verified.
- **An unverified function entered from a counterpart** runs its `*1*` body
  (node name `f*1*`). There `mbe` runs `:logic` and every callee's guard is
  evaluated (node `g#guard`).
- **Verification.** A book's `(set-verify-guards-eagerness 0)` is honoured:
  52 books set it, and there `:guard` alone does not verify.

**Classes.** Every find gets one:

| Class | Meaning |
| --- | --- |
| cold | every entry reaching it is cold: its name has an open/recover/checkpoint/install/pack/compact word and no connection/greeting/post/arrival word, or every host caller of it is cold |
| resumable | the dimensions file names the quantum that bounds it |
| output-proportional | K only |
| unexpected | none of the other classes applies |
| uncalled | reached only from host functions that no host line, tools/*.py or tests/*.py names |
| unresolved | a seeded value handed to a constrained function without attachment, or to a `funcall` of a variable |

## 2. What it cannot follow

- **Path-insensitive.** An arm the host never selects counts as reached. For
  example, `fn-ocfg-step`'s `:complete` arm: no host line sends
  `(:complete)`.
- **Context-insensitive.** A formal carries every dimension any caller passes
  it.
- **Macros** are not expanded. Their arguments are read as forms.
- **`equal`** is treated as constant time. With structure sharing it usually
  answers at `eq`, but that is not proved.
- **Stobj exports** are not followed beyond the calls the tree names.
- **Guard evaluation at the `:program` wrapper's own counterpart** is not
  modelled. Those guards are `state-p` shapes.
- **Invariant-risk** execution of a `:program` wrapper in `*1*` mode is not
  modelled.
- **Unresolved edges.** 70 sites on reached functions, 45 distinct, none
  carrying a seeded value. They are:
  - the dispatchers' own `apply`;
  - `constrained fn-sig-verify has no attachment` (its implementation is
    host-supplied);
  - 38 `funcall`s of host callbacks: `*fnn-finish-callback*`,
    `*fnn-observe-callback*`, `*fnn-pack-recover-callback*`,
    `*fnn-reclaim-callback*`, `*fnn-tcl-deliver*`, `commit-callback`,
    `submit-callback`, `handler`, `thunk` and the rest (printed by
    `--summary`).

  A walk inside a callback's target is found from that target's own host
  definition. The link from the caller is not.
- **One cut** is taken and printed on every run. `fn-scar-node-statep` is
  `(or (equal node live) (fn-node-statep node))`, and the served session
  carries the live node itself (`fn-scar-node-statep-is-node-statep`,
  books/served-carried.lisp). Without the cut, every served read reaches the
  whole node recogniser.

## 3. The first report (planning/evidence/hot-path-checker-2026-09-26/first-report.txt and .json)

173 traversals of retained state were found, on paths from 145 host entries.
5,939 book functions are reached from a host definition.

| class | finds |
| --- | ---: |
| unexpected | 165 |
| cold | 7 |
| resumable | 0 (no bound has been named) |
| output-proportional | 0 (no K seed) |
| unresolved (carrying a seeded value) | 0; 70 unresolved edge sites in all (§2) |
| uncalled | 1 (`fn-stx-reader-lookup`, only from `fn-store-sn-verdict`) |

By owner:

| owner | finds |
| --- | ---: |
| PKT-308 (per-arrival BP) | 53 |
| PKT-324 (1)-(8) | 32 |
| PKT-330 (2) | 4 |
| PKT-223 | 3 |
| PKT-190 | 2 |
| PKT-189 | 4 |
| PKT-041 | 5 |
| PKT-448 (a)-(h) | 70 |

### 3.1 Every known find is reproduced

The table lists each item of hot-path-scans §4, PKT-330 (2), PKT-189, PKT-190
and PKT-041 as the brief names it, with how the report shows it. "On the path"
means the named function hands the seeded list to the walker the report keys
(`--why NAME` prints it).

| Named in the brief | In the first report |
| --- | --- |
| `fn-sf-next-lower` | `fn-sf-next-lower recursion N` (unexpected, PKT-330 (2)) |
| `fn-sf-candidatep` (len) | `fn-sf-candidatep len N` (unexpected, PKT-330 (2)); the carried twin `fn-pcar-candidatep len N` (PKT-324 (4)) |
| `fn-sf-record-listp` | `fn-sf-record-listp recursion N` (unexpected, PKT-448 (a): reached per BP ingress through `fn-sn-statep`) |
| `fn-sf-history-recoverablep` (replay) | on the path of `fn-replay-loop recursion N` (PKT-223): `fn-sf-prepare-record -> fn-sf-history-recoverablep -> fn-sf-replay-node -> fn-replay -> fn-replay-loop` |
| `fn-sf-record-dir-result`, `fn-rcon-sf-record-dir-result` (append) | `... append N` (unexpected, PKT-324 (2)) |
| `fn-sf-emit-success` (append) | `fn-sf-emit-success append N` (unexpected, PKT-324 (3)), reached from `fn-store-sn-finish` through the carried finish |
| `fn-sn-find-record` | `fn-sn-find-record recursion N` (PKT-448 (d)): only through the model arms of §3.2 |
| `fn-sn-completion-enabledp`, `fn-sn-finish` | model path, see §3.2 |
| `fn-pcar-next-lower` | `fn-pcar-next-lower recursion N` (unexpected, PKT-324 (4)) |
| `fn-spc-stage-record` | not reached: the host calls `fn-pcar-spc-prepare` (its walk is `fn-pcar-candidatep len N`) |
| `fn-bpaj-record-for-msgid` | `fn-bpaj-record-for-msgid recursion N` (unexpected, PKT-330 (2)) |
| `fn-cei-build` (cold) | on the path of `fn-cei-build-aux recursion N` (PKT-448 (d)); classed unexpected because `fn-sn-recover` is reachable from `fn-owner-step`'s arms (path-insensitive, §2) |
| `fn-own-refresh` (len :913) | `fn-own-refresh len N` (PKT-324 (1)) |
| `fn-gidx-build` (:916) | on the path of `fn-index-build recursion N` (PKT-324 (1)) |
| `fn-midx-refresh` / `fn-midx-build` | `fn-midx-build recursion N` (PKT-324 (1)), reached from `fn-midx-refresh`'s rebuild arm |
| `fn-ctl-refresh-visible`, `fn-ctl-refresh-withdrawn` | on the path of the `fn-ctl-*` finds (PKT-448 (b)): `fn-ctl-drop-via`, `-has-msgid-p`, `-lookup-verdict`, `-subseq-diff` |
| `fn-ctl-record-txid` | `fn-ctl-record-txid recursion N` (PKT-448 (b)) |
| `fn-find-article` | `fn-find-article recursion N` (PKT-330 (2)); host lines include `fn-owner-prepare -> fn-rcl-existing-action`, the D25 existing action (`fn-sn-existing-action` itself is no longer called: the host calls `fn-rcl-existing-action` and `fn-rclb-existing-action`) |
| `fn-all-article-memberships`, `fn-articles-freshp` | `... recursion N` (PKT-189) |
| `fn-node-articles-have-archive-bindingsp -> fn-retain-find-id` | both `... recursion N` (PKT-189) |
| `fn-bpi-node-record-committedp` and `fn-node-statep` per BP acceptance | on the path of 19 finds; `fn-bpi-host-already-durablep -> fn-bpi-adu-durably-acceptedp -> fn-bpi-node-record-committedp -> fn-find-article` and `-> fn-node-statep -> ...` (PKT-448 (a)) |
| `fn-sbud-used` | `fn-sbud-used len N` (PKT-324 (8)); host entries include `fn-owner-prepare`, `fn-owner-headroom`, `fn-owner-publication-verdict` |
| `fn-sbud-record-octets` | `fn-sbud-record-octets recursion N` (PKT-324 (5)) |
| `fn-sbud-bytes-extend` | `... len N` and `... nthcdr N` (PKT-324 (5)) |
| `fn-bpnj-contact-next` | on the path of `fn-bpnj-scan*1* recursion J`, `fn-bpn-member*1* recursion J`, `fn-bpn-find-job*1* recursion J` (PKT-324 (7)); the book sets eagerness 0, so these run their `*1*` bodies |
| `fn-bpn-member` | `fn-bpn-member*1* recursion J` (PKT-324 (7)), over OFFERED |
| `fn-bpn-resume-jobs` | `fn-bpn-resume-jobs recursion J` (PKT-308) |
| native-live-status :418, native-health :501 | `fn-nls-report len N`, `fn-nls-pins-line len N`, `fn-nh-forward-count`, `fn-cvec-debt-from` and others (PKT-324 (8)) |
| `fn-owner-record-octets` (:426) | `fn-owner-record-octets len N` (PKT-324 (5)) |
| `fn-owner-carried-usage` (:1717) | `fn-owner-carried-usage len N` and `fn-pcb-*` (PKT-324 (6)) |
| `fn-owner-prepare`'s `fn-sbud-used` | host entry of `fn-sbud-used len N` |
| PKT-041 prefix octets | `fn-sco-cpr-prefix recursion N`, `fn-sco-capture true-list-fix N` (PKT-041) |
| PKT-190 greeting | `fn-nntp-projectionp len N` from `fn-served-open-indexed` and `fn-owner-exposure-open`, and `fn-acar-nntp-projectionp len N` from `fn-owner-outcome` (PKT-190) |

**No listed find is missing.** Two named subjects are not reached, and
correctly so: `fn-spc-stage-record` and `fn-sn-existing-action`. The host
calls their carried and reclaim twins, whose walks are in the table.

### 3.2 The carried finish, and the model path

`fn-store-sn-finish` (host/store-node-host.lisp:886) calls `fn-ccar-sn-finish`
at :897, and `fn-owner-finish`/`fn-owner-finish-submission` call
`fn-ccar-ocfg-complete` and `fn-ccar-own-finish`. None of those three reaches
`fn-sn-finish`, `fn-sn-completion-enabledp` or `fn-sn-find-record`: the walk
the commit-regression profile found (88.6 per cent under `fn-sn-finish ->
fn-sn-find-record`) is **resolved on the commit path**.

`fn-sn-finish` is still reached, from two host entries only:

- **`fn-owner-step -> fn-ocfg-step -> fn-ocfg-complete -> fn-own-complete`**
  (books/owner-config.lisp:573). This is `fn-ocfg-step`'s `(:complete)` arm,
  and no host line builds `(:complete)` (grep of host/ and tools/). It is a
  path the host never takes, and the tool cannot tell (§2).
- **`fn-owner-reconfigure-complete -> fn-ocl-publish -> fn-ocl-complete ->
  fn-own-complete`** (books/config-owner-live.lisp:57). This is the arm with
  no staged record. A reconfiguration completion has one staged, so the arm is
  the "nothing staged" completion. It is reachable in principle, it is an
  admin operation, and the finish runs over the whole history there. It is
  PKT-448 (d).

The carried finish still walks, per commit:

- `fn-ccar-seek` (books/owner-commit-carried.lisp:54) skips the history by
  sequence, with no decode: a pointer walk of N. It is PKT-448 (h).
- `fn-sf-emit-success` appends to the success list: PKT-324 (3).
- The host's own `(len (fn-sf-successes ...))`, twice
  (host/store-node-host.lisp:905-906): PKT-448 (f).
- For a **retention** record, `fn-replay-apply-retention-event` evaluates
  `(fn-node-statep advanced)` (books/replay.lisp:510). That is the whole node
  recogniser, including PKT-189's quadratic archive-binding check, once per
  retention commit: PKT-448 (a).

### 3.3 New finds (PKT-448, one line each)

- **(a) Whole-node or whole-store recognisers called in bodies on served
  paths.** The finds are the `fn-acceptedp`, `fn-article-*`, `fn-node-*`,
  `fn-retain-*`, `fn-sf-*listp` and `fn-sn-verdict-listp` recursions. They
  run `fn-sn-statep`/`fn-node-statep`/`fn-statep` per request, from:
  - BP ingress: `fn-bpi-policy-appliesp` at books/bp-ingress.lisp:425;
  - the BP receipt check: `fn-bpr-store-record-acceptedp` at
    books/bp-receipt.lisp:315;
  - `fn-bpi-node-record-committedp` (:591);
  - the reader's `fn-reader-use-store`;
  - a retention commit: `fn-replay-apply-retention-event`, books/replay.lisp:510;
  - the transit decision: `fn-peer-decide-transfer -> fn-peer-history-hasp`.

  Where the node is in the recogniser, the archive-binding check makes each
  call quadratic.
- **(b) Owner commit/refresh control scans.** `fn-ctl-drop-via`,
  `fn-ctl-has-msgid-p`, `fn-ctl-lookup-verdict`, `fn-ctl-visible-filter`,
  `fn-ctl-configs-through`, `fn-ctl-articles-withdrawals`,
  `fn-ctl-subseq-diff` and `fn-ctl-record-txid` walk the article list and the
  verdicts on every `fn-own-refresh` (owner finish, io, submission).
- **(c) Served read commands walk the article list.** `fn-nntp-group-count`,
  `-low`, `-high`, `-next-number`, `-last-number`, `-range-numbers`,
  `fn-nntp-find-group-number`, `fn-nntp-available-article` and
  `fn-nntp-newnews-scan` are reached from `fn-owner-chunk`. They are the
  candidates for PKT-301's unexplained OVER term; the scaling rows (§4) test
  the growth, and a profile must name the walk.
- **(d) Model and replay arms reached path-insensitively.** These come through
  `fn-owner-step`'s event arms and the reconfigure completion (§3.2):
  `fn-cei-build-aux`, `fn-cpe-projection-replay`, `fn-th-prefix-loop`,
  `fn-stx-index-of-store`, `fn-sf-crash`, `fn-sf-crash-imagep` and
  `fn-sn-find-record`. Each arm must be shown unreached by the host or
  bounded.
- **(e) Reconfiguration replays the configuration history.**
  `fn-ocl-store-config -> fn-cpr-replay` (books/config-owner-live.lisp:32)
  and `fn-cpo-configure-durable`'s `append`/`true-listp` run over the whole
  history per reconfigure.
- **(f) Host-side counts per call.** `len` in `fn-owner-article-count`,
  `fn-owner-sco-count`, `fn-owner-sco-capture`, `fn-owner-record-debt`,
  `fn-store-sn-finish`, `fn-store-sn-article-count`, `fn-store-sn-pin-count`,
  `fn9p-servable-articles`, `fn9p-status-octets`,
  `fn-sim-acceptance-durable-okp`, `fnn-bp-profile-session` and
  `fn-nntp-index-config-digest`.
- **(g) BP receipt lookups walk the history linearly.**
  `fn-bpr-article-records`, `fn-bpr-host-find-record` and
  `fn-bpreq-find-record`.
- **(h) Carried helpers that still walk.** `fn-ccar-seek` (per commit, pointer
  only), `fn-pgc-obligation-ids` and `fn-pgc-release-ids` (per peer offer),
  and `fn-retain-remove-id`. Cold ones: `fn-own-take` and
  `fn-own-retain-find-id-unguarded` (feed reconcile). Uncalled:
  `fn-stx-reader-lookup`.

## 4. The scaling rows (tools/scale_probe.py, commit 56f94181)

One sweep, `python3 tools/scale_probe.py box 56f94181`, ran detached on hbox
(/tank/fn/scratch/hot-path-checker/results-56f94181, `done` = 0; every point
rc=0). It ran on the developer image built from 56f94181 (dev 17ff24aa plus
the tool; launcher `1795902d...`, its heap-hook twin `be36442f...`, core
`65d26058...`), certified wholly from the cache
(certify-20260926T102804Z-1396338, 380 of 380 books installed, 0 certified).
The profile is the default one. The store is on tmpfs, the process is under
`systemd-run -p MemoryMax`, and each point takes 32 samples with 3 readers.
The fetched rows and logs are in planning/evidence/hot-path-checker-2026-09-26/rows/
(SHA256SUMS there; the JSON rows: n1000-2k `c191d679...`, n4000-2k
`882ac3a5...`, n10000-2k `f0beb52f...`, n1000-16k `3f480913...`, n1000-32k
`7c0ea642...`).

**These rows are for 56f94181, not dev's current bytes.** Since that commit,
served-path-scale, hot-path-scans-2 and exposure-reply-size changed the served
path. A rerun on the merged head is owed; that is PKT-504.

Per-operation figures are the medians of 32. "bytes" is bytes consed per
operation, which the heap hook brackets over a batch of 32. Each ratio is to
the first row. OVER has no allocation counter in rep_measure.

Varying N (2 KiB articles):

| point | POST ms | POST bytes | STAT ms | STAT bytes | ARTICLE ms | ARTICLE bytes | OVER ms | greeting ms | load s | reopen s |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| n1000-2k | 2.13 | 2,456,178 | 0.09 | 50,092 | 2.69 | 498,478 | 0.88 | 0.32 | 1.99 | 1.18 |
| n4000-2k | 3.03 (x1.42) | 4,278,654 (x1.74) | 0.09 (x0.96) | 50,092 (x1.00) | 2.41 (x0.90) | 498,357 (x1.00) | 1.76 (x2.00) | 0.36 (x1.12) | 10.06 (x5.06) | 6.26 (x5.31) |
| n10000-2k | 5.34 (x2.50) | 7,925,383 (x3.23) | 0.10 (x1.09) | 50,111 (x1.00) | 2.44 (x0.91) | 498,419 (x1.00) | 3.43 (x3.89) | 0.34 (x1.07) | 37.99 (x19.12) | 30.31 (x25.74) |

Varying payload (N = 1,000):

| point | POST ms | POST bytes | STAT ms | STAT bytes | ARTICLE ms | ARTICLE bytes | OVER ms | greeting ms | load s | reopen s |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| n1000-2k | 2.13 | 2,456,178 | 0.09 | 50,092 | 2.69 | 498,478 | 0.88 | 0.32 | 1.99 | 1.18 |
| n1000-16k | 10.59 (x4.96) | 11,367,778 (x4.63) | 0.09 (x0.95) | 49,566 (x0.99) | 18.36 (x6.84) | 3,471,669 (x6.96) | 1.15 (x1.31) | 0.34 (x1.06) | 10.85 (x5.46) | 4.28 (x3.63) |
| n1000-32k | 19.63 (x9.20) | 21,546,029 (x8.77) | 0.09 (x0.94) | 49,923 (x1.00) | 35.04 (x13.05) | 6,866,286 (x13.77) | 1.66 (x1.88) | 0.35 (x1.08) | 20.55 (x10.34) | 8.40 (x7.14) |

The totals for the whole run, taken from the heap figures in the same JSON,
are bytes consed over the load and over the reopen:

| point | load bytes | per POST | reopen bytes | per article |
| --- | ---: | ---: | ---: | ---: |
| n1000-2k | 2.15 GB | 2.15 MB | 1.57 GB | 1.57 MB |
| n4000-2k | 12.22 GB | 3.06 MB | 6.69 GB | 1.67 MB |
| n10000-2k | 48.79 GB | 4.88 MB | 23.86 GB | 2.39 MB |

**What the rows confirm.** In each case below, the row confirms growth at an
entry. It never names the walk; a profile does (`rep_measure --profile`).

- **POST grows in N at a fixed request.** Allocation per POST rises from 2.46
  MB to 7.93 MB, about 608 bytes per retained article per POST. The medians
  of the load's first and last quarters at N = 10,000 are 2.07 ms and 5.05
  ms, so the load is quadratic in total: 48.8 GB over 10,000 POSTs. This
  confirms retained-state work on the POST entries: `fn-owner-prepare-buffer`
  (host/native/owner.lisp:818), `fn-owner-finish` / `-finish-submission`
  (:153/:157) and `fn-store-sn-finish`. The 38 N-finds those entries reach
  are marked `confirmed` in planning/hot-path-findings.json, with the same
  "aggregate" caveat. They include PKT-324 (1) (`fn-own-refresh`,
  `fn-index-build`, `fn-midx-build`), (3), (4) and (8), and PKT-448 (b), (f)
  and (h). The 608 B/article slope is too small for a decode of every record.
  It fits a pointer walk plus a rebuild of per-article cells, which is what
  `fn-index-build`'s full group rebuild does.
- **Reopen is superlinear in N.** It takes 1.18 s, then 6.26 s, then 30.31 s,
  and allocation per article rises from 1.57 MB to 2.39 MB. This is
  consistent with PKT-189's quadratic archive-binding check at open and
  PKT-223's replay. The 39 N-finds the open entries reach
  (`fn-owner-recover-from-store-open`, host/native/owner.lisp:490, and
  `fn-store-sn-open-extended`) are marked.
- **OVER grows in N; STAT does not.** OVER goes from 0.88 ms to 3.43 ms (x3.89)
  while STAT stays at about 50 KB and 0.09 ms, flat. Both go through
  `fn-owner-chunk`, so the growth is in OVER's arm. This is PKT-301's
  unexplained OVER term. The candidates are PKT-448 (c)'s `fn-nntp-group-*`
  and `fn-nntp-available-article` walks; the nine `fn-nntp-*` finds are
  marked as the row's candidates, not as measured individually.
- **The flat STAT row refutes, for STAT, the chunk-reached recognisers.**
  `fn-acceptedp`, `fn-node-*` and `fn-retain-*` are listed under
  `fn-owner-chunk` path-insensitively. If they ran per STAT, STAT's
  allocation would grow in N, and it does not. This is evidence for PKT-447's
  path-sensitivity item, not a removal: the listing stays until the tool can
  show the arm unreached.
- **ARTICLE and the greeting are flat in N.** ARTICLE grows with payload
  (x13.8 bytes at x16 octets): that is output-proportional in K, as it
  should be. The greeting stays at about 0.34 ms. PKT-190's `len N` in the
  greeting is below this row's resolution at N = 10,000. It is not refuted:
  a `len` of 10,000 conses takes microseconds.
- **POST grows with payload as well**: x8.8 bytes at x16 octets. That is
  per-request work in B, which a find does not predict. It is recorded here
  and not attributed.

Lock-hold time and primitive visits are absent from these rows, not
estimated (§6).

## 5. Wiring

- `make check`: `tools/hot_path_check.py --summary --strict` runs after
  reach_check (Makefile, with the comment paragraph).
- `tooling-test`: `tests.test_hot_path_check` runs on a fake tree, which
  covers:
  - a seeded list walked by `len` from a host entry;
  - a recursive walk of a bound formal;
  - an `mbe` whose `:logic` walks and whose `:exec` does not (no find);
  - a guard evaluated by a native dispatch (a find under `f#guard`);
  - a cold entry;
  - a named bound (resumable);
  - a formal seed;
  - a cut;
  - an unreached walk (no find);
  - NEW and STALE.

  It also checks, on the real tree, that every find is listed with a packet.
- docs/proof-style.md §11 documents the check, the executed-path rules and the
  limits. §4's "never recomputed" now reads with §11's caveat: the guard of
  the function a native dispatch calls is evaluated on every call.

## 6. Not done

In PKT-447:

- **Primitive visits.** They are not counted: the harness records bytes
  consed per operation as the executed-work proxy. A `--count` REPL mode is
  not built. hot-path-scans' visit counts were hand-written per function
  (`sel-scaffold.lisp`), and SBCL's self-call optimisation defeats a generic
  call-counting wrapper for recursive walkers.
- **Lock-hold time.** The owner does not expose it.
- **The fragment-count sweep** at a fixed ADU (the DTN developer image) was
  not run.
- **Classification refinements.** The resumable class is empty until a lane
  names a quantum. There is no K seed, so the output-proportional class is
  empty. Cold/served is decided by a name rule plus host callers, which is a
  heuristic.
- **Path-sensitivity** for event-dispatch arms (§2) is not built. It would
  remove PKT-448 (d)'s false paths.
