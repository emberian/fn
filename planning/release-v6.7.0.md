# Release v6.7.0: the cut checklist

**Status: NOT CUT. v6.7.0 is blocked on the fundamentals below.** ember
(relayed by the coordinator, 2026-09-27 ~02:30 UTC): "no v6.7.0 for friends
yet; the fundamentals come first." The release machinery is in the tree:
the version file, `fn --version`, the tarball names, this checklist,
`tools/cut_release.sh` and `tools/changelog.py`. A cut is when every
fundamental is MET and every gate is green on one commit.

Written from the tree at dev `87dff3138` (2026-09-27, lane release-v6.7.0).
Nothing here was run except the cut script's `--dry-run` (the lane record's
section "Dry run"). This is a checklist, not a qualification record: the
cut writes that record (section 4).

## 1. The version

- Every release of fn is **6.7.N** (ember: "all versions of fn will be
  v6.7.xyz"). N starts at 0 and rises by one per cut. There is no other
  component and no suffix.
- The version lives in ONE place: the file `VERSION` at the root of the
  tree, one line (`6.7.0`).
  - The image build reads it: host/native/build.lisp, build-dtn.lisp and
    build-store-test.lisp call `fnn-select-release-version`
    (host/native/io.lisp), which serializes it into the saved image and
    stops the build on a missing or malformed file.
  - The packaging reads it: packaging/release-tarball.sh names the tarball
    `fn-6.7.N-PLATFORM.tar.gz` from the `VERSION` in the `git archive` of
    REV. It refuses unless the staged `bin/fn --version` prints exactly
    `fn 6.7.N (REV12)`. The `--frozen` form (tests, friends harness) names
    its package `fn-6.7.N+REV12-PLATFORM.tar.gz`, which is not a release.
- `fn --version` prints `fn 6.7.N (REV12)`: the version built into the image
  and the first twelve digits of the source revision recorded beside the
  core (`libexec/fn/source-revision`). An image that records no revision
  refuses, exit 1, as before (PKT-403).
- The cut commit is tagged **`v6.7.N`** by the coordinator at the cut, never
  by a lane. Gate 01 refuses a VERSION whose tag exists on another commit or
  that is not above every earlier `v6.7.*` tag. After a cut, the next change
  to `VERSION` (6.7.N+1) is the first commit of the next release.
- `CHANGELOG.md` is generated (`python3 tools/changelog.py --write`). It has
  one line per merged lane since the Fable mandate, grouped by capability,
  and lists reverted merges apart. Its range ends at the last lane merge, so
  the cut commit regenerates it byte for byte (gate 04). Never edit it by
  hand.

## 2. Blocking fundamentals

Each row is BLOCKING. Gate 03 reads this table from REV and is red unless
every row says `MET` and its evidence path exists at REV. The evidence is a
committed record with the measurement, its scope and the image it ran on.
A row changes to MET only in the commit that adds that evidence.

<!-- fundamentals -->
| ID | fundamental | bar (measurable) | status | evidence |
| --- | --- | --- | --- | --- |
| F1 | The records freeze landed (PKT-293, PKT-635; records-freeze) | Retained heap about 1 octet per stored payload octet plus stated per-record metadata (today 16 B/octet: the history and the acceptance node hold octet lists). A reopen of the 1,000-post store under 128 MB RSS. | OPEN | - |
| F2 | The served machine reads through the catalog (catalog-slice step 7b/8) | GROUP/LISTGROUP/ARTICLE/OVER read v/fn-cat; R established at every host entry; the index lookups per served command measured on the served path, with the before/after at N = 10,000 | OPEN | - |
| F3 | The storage log (storage-log-design, PKT-636) | fsyncs per POST at batch 8 well under today's 7 barriers per commit, the figure stated by the design and measured; POST/s on the public node's edge disk stated (node-disk's mount) | OPEN | - |
| F4 | The owner scheduler (owner-scheduler, PKT-321) | Under the mixed hour (3 tight-loop readers, 1 POST every 0.5 s), every control request answered within its 10 s deadline, control p99 stated and bounded; no served read outlier past the work-quantum bound | OPEN | - |
| F5 | Connection multiplexing (connection-multiplexing) | Memory per idle connection measured and stated (today one worker thread and its stack per connection, PKT-605); the capacity check against memory | OPEN | - |
| F6 | Opens at scale | The owner's open of a 20,000- and a 40,000-article store in seconds, not tens of seconds (the coordinator reads the bar as under 10 s each; ember may set it), peak RSS stated; checkpoint-pipeline measured 28.8 s and 5.15 GB at 40,000 x 2 KiB | OPEN | - |
| F7 | BP 10 MiB validated (SCN-077, PKT-630 (7); bp-fragments-10mib) | tests.test_bp_fragment_node_native wholly OK on dtn and dtn-developer, SCN-077 delivering a 10 MiB ADU into a Store profiled for it | OPEN | - |
| F8 | The memory target (D35) | Under 256 MB reserved and under 128 MB in use after 1,000 posts on the release image, AND a reopen of that store under 256 MB (image-floor-2: 68 MiB in use after 1,000 posts, but the reopen needs 280 MB; not merged) | OPEN | - |
<!-- end fundamentals -->

## 3. The gates, in order

`tools/cut_release.sh` runs gates 01 to 16 in this order and stops at the
first red. It writes `build/cut/v6.7.N-REV12/verdict.txt`, whose last line
is `VERDICT GREEN ...` or `VERDICT RED at NN NAME`, and one log per gate.
Run it from a clean checkout at REV (a `git worktree add --detach`), never
from the shared ~/dev/fn. `--dry-run` runs the read-only local gates and
prints every other gate's commands. `--from N` resumes at gate N.

| # | gate | green when | where |
| --- | --- | --- | --- |
| 01 | version | `VERSION` at REV is 6.7.N; the tag `v6.7.N` is free or already at REV; N is above every earlier `v6.7.*` tag; this checklist exists as planning/release-v6.7.N.md | local |
| 02 | tree | HEAD is REV with no tracked change | local |
| 03 | fundamentals | every row of section 2 is MET with its evidence at REV | local |
| 04 | changelog | `CHANGELOG.md` at REV is what `tools/changelog.py --rev REV` writes | local |
| 05 | closure certified at the cut | `tools/green_check.py --strict` (every book green at its current digest in a committed manifest) and `--profile default --strict` (the image's closure). The batch cite that certified REV's closure is the manifest this reads. | local |
| 06 | make check | the registries, the current view, proof cost and the throughput comparison, as `make check` runs them | local |
| 07 | docs_check | `tools/docs_check.py --check`: every command the docs name exists with the grammar the docs give | local |
| 08 | runpath check (static) | `tools/runpath_check.py`: every process site in host/ listed, no Python in the shipped packaging | local |
| 09 | the four images; every native module | `tools/hbox_native.sh --images developer,production,dtn,dtn-developer REV` builds fn-host, fn-host-developer, fn-host-dtn and fn-host-dtn-developer from `git archive REV`, then runs every `tests/test_*native*.py` and `tests/test_bp_*.py` module except those in planning/release-module-exclusions.txt; status 0: no module FAILED, none wholly SKIPPED | hbox |
| 10 | the throughput gate, quiet | `tools/throughput_gate.py run` on REV's developer image with `--wait-quiet 1800` (never `--under-load`: a cut is measured on a quiet box), then `check` within planning/throughput-baseline.json | hbox |
| 11 | the hostile campaign | `tools/hostile_campaign.py` on REV's developer image, every family (malformed, header, body, connection, pipelining, transit, tls, bp); exit 0 = no defect | hbox |
| 12 | the Linux tarball (glibc floor) | packaging/release-tarball.sh `--runtime-from` the glibc-floor runtime builds `fn-6.7.N-linux-x86_64.tar.gz` from the archive (its own green_check, acquire, validate, production image, runpath `--tree`, `--version` check); `runpath_check.py --tarball`; installed fresh from the tarball and SHA256SUMS with `install.sh --no-service`; tests.test_release_tarball `OK` with no skip (the format-7 fixture given); `fn --version` in a bare `debian:12` container with only libssl3 prints `fn 6.7.N (REV12)` | hbox + docker |
| 13 | the OpenBSD tarball | the same build in the OpenBSD 7.9 build VM (planning/evidence/release-openbsd-2026-09-26.md section 2): `fn-6.7.N-openbsd-amd64.tar.gz`, runpath `--tarball`, installed fresh, tests.test_release_tarball `OK`. Needs `--openbsd-host` and `--openbsd-root`; without them the gate is red, not skipped | the VM |
| 14 | the power-loss cut list on the release image | tools/power_loss.py's reproduction (planning/evidence/power-loss-2026-09-26.md section 7): rig, workload of 600 POSTs, index, the cut plan `init=8,post=150,checkpoint=60,compact=60,reclaim=50,control=8` with recovery cut at 0.2, on the INSTALLED tarball's launcher; the summary's `all` row: 0 violations, controls caught > 0, 0 harness errors | hbox (sudo -n for the block layer) |
| 15 | the friends session from the tarball | tests.test_native_friends_feed with `FN_FRIEND_FN` the fresh install's `bin/fn` (the friend) and the developer image as the author: `OK` with no skip | hbox |
| 16 | the tag | prints `git tag -a v6.7.N -m 'fn 6.7.N' REV` for the coordinator; the script creates no tag | local |

What the gates do not decide (the cut's qualification record, section 4):

- **Per-test skips inside an OK module** are not evidence. The notes
  `tools/native_env.py plan` prints today name them: FN_OLD_IMAGE and
  FN_OLD_NATIVE_HOST (upgrade cases, moot under D34), FN_INN_SRC (the INN
  lab), FN_DTN7_REPO (dtn7-rs interop), FN_BUILD_OPENSSL_PREFIX
  (frozen_relocation). The record lists each one as unexercised with its
  reason.
- **The per-image split.** hbox_native.sh gives each module the variables
  it reads for the four images. A module that picks one image runs on that
  image only. The qualification of 69046a76 ran the non-BP modules on prod
  and dev and the BP modules on dtn and dtndev by hand (`env.sh`,
  PKT-499 (d)). The record says which modules ran on which image.
- **A red is classified, never re-expected.** Implementation,
  model/refinement, harness, environment, or unexercised capability, as in
  planning/evidence/qual-69046a76-2026-09-26.md section 4. The cut's module
  table is the evidence.
- **The load gates** that are measurements, not pass/fail (the mixed hour,
  the opens at scale, the memory target) are the fundamentals, measured once
  on the cut's image and cited from section 2.

## 4. The cut, step by step (the coordinator)

1. Every fundamental MET on dev (section 2), each with its record.
2. `python3 tools/changelog.py --write`; commit CHANGELOG.md (and VERSION if
   it changes) on dev. That commit is REV.
3. `git worktree add --detach build/cut-6.7.N REV`; there, `tools/cut_release.sh
   --dry-run --rev REV`, then `tools/cut_release.sh --rev REV
   --openbsd-host H --openbsd-root DIR` (start it in the background; gates 09
   to 15 take hours).
4. On `VERDICT GREEN`: write planning/evidence/qual-v6.7.N-DATE.md from the
   verdict, the logs and the module table (the shape of
   qual-69046a76-2026-09-26.md). Commit the throughput JSON gate 10 wrote
   under planning/evidence/throughput/, the verdict and the tarballs'
   SHA256SUMS.
5. Tag `v6.7.N` at REV (gate 16's line); push the tag.
6. The release notes (section 7), final, beside the tarballs. ember's go
   before any friend is sent a link.

## 5. Deploy notes (fresh install per D34)

A deploy is a reinstall from the release: stop, `store export`, remove,
install, `init` or `store import`, start. No upgrade path exists (D34).
For a node installed from v6.7.0:

1. **The node secret.** Before the first start, `fn store ROOT node-secret
   create`: the node-written Cancel-Lock keys come from it (lane
   newsreader-cancel-3; **not on dev at 87dff3138**, READY FOR BATCH).
   `store export` excludes `keys/`, so an imported store needs it too, and
   the secret must survive a reinstall to keep old locks cancellable
   (PKT-618's decision: STORE/keys/node-secret.key).
2. **Imported stores: rebind the file system once.** A store made before the
   store identity record needs `fn store ROOT rebind-filesystem` once after
   the import (lane store-mount-identity; **not on dev at 87dff3138**).
3. **Barriers on.** The store's file system honours fsync with write
   barriers: ext4 with its default barriers (never `barrier=0` or
   `nobarrier`), ZFS `sync=standard`, no volatile cache that ignores flushes
   (docs/operator.md "Storage requirements"). fn does not yet refuse a
   detectable bad mount at start (PKT-648, a decision for ember).
4. **MODE STREAM.** Peers are fed with `MODE STREAM` and `CHECK`/`TAKETHIS`
   when their peer record's streaming flag is `true` (transit-streaming,
   transit-pipelining: two articles in one read are both answered,
   PKT-600 fixed). A peer that answers `MODE STREAM` with anything but 203
   is stopped for the owner's run with a log line: re-add it with `false`.
5. **Infrastructure (ember's hand step).** The Ashburn anchor's
   systemd-networkd enable; the public node's certificate by Let's Encrypt
   (D36); `tls reload` after each renewal (no restart).

## 6. Known limitations (for the release notes)

State each in the notes with its packet. Reread the backlog's open packets
(planning/backlog-2026-09-25.md) at the cut: a fundamental that lands
removes its line here.

Capacity and cost:

- **Memory per stored octet.** The history and the acceptance node hold
  articles as octet lists: about 16 octets of heap per stored payload octet
  until the records freeze (F1; PKT-293, PKT-635). A node's heap is sized
  from its profile (heap-from-profile), not its data.
- **fsyncs per commit.** Every POST is its own durable transaction: 7
  barriers per commit. On hbox's ZFS pool with no SLOG a POST's median is
  446 ms (planning/performance-2026-09-26.md row 3), until the storage log
  and group commit (F3; PKT-636).
- **Control requests under a mixed load.** Under saturating reads, control
  socket requests can wait past their 10 s deadline and answer uncertain
  (PKT-321), until the scheduler (F4). Correctness held in the measured hour.
- **Per-connection memory.** One thread per connection (PKT-605); the
  connection cap is not checked against memory (F5).
- **Open time at scale** (F6), **the reopen's memory** (F8).
- **Linear reader folds.** HDR/XHDR, GROUP, NEXT, LAST and NEWNEWS walk the
  archive per command (NNTP gap inventory R8). OVER and reads by number are
  indexed.

Protocol and peering:

- **BP: a 10 MiB ADU is not yet validated** end to end (SCN-077, PKT-630
  (7); F7). **ION's TCPCL is not supported**: fn speaks TCPCLv4 only
  (specs/tcpcl.md section 6, "§4.3 version fallback to TCPCLv3 | deferred"),
  and ION 4.2.0 speaks TCPCLv3 only, so no exchange is possible (bp-cursors;
  PKT-650 names a spurious MSG_REJECT after the version mismatch). By
  decision, not by defect.
- **INN pushing into a login-required, TLS-only node** is not possible
  (innfeed sends AUTHINFO without TLS; PKT-611). An INN peer must be a
  source-address peer. Peers named by a dynamic IP break at renumbering
  (PKT-613).
- **TLS handshakes are not metered** by the exposure limits (the handshake
  precedes the exposure open; PKT-639), and handshake refusals go to stderr,
  not the service log (PKT-640).
- **Not served:** COMPRESS DEFLATE, AUTHINFO SASL (never, until a client
  needs SCRAM), LIST MODERATORS, moderated groups (P3), XGTITLE/XROVER/
  XTHREAD/XINDEX, newgroup/rmgroup by control article (D29). Distribution is
  ignored (P4); refused offers are not remembered (T1).
- **Header ceilings.** 64 header fields, 256 header lines and 16,384 header
  octets per article (books/article.lisp; P9, D27 debt): friends' posts fit,
  some relayed Usenet articles do not.
- **Own-post cancel from an ordinary newsreader** (Cancel-Lock, RFC 8315)
  and Injection-Info with a posting account arrive with newsreader-cancel-3
  and usenet-headers-3 (READY, not on dev at 87dff3138). Until then a
  cancel from tin files but withdraws nothing unless it is a verified signed
  cancel with a grant.
- **An anonymous read-only level** is not separate from open posting
  (PKT-405).

Operation:

- **Fresh deploys only** (D34): no in-place upgrade. A reinstall keeps data
  through `store export`/`store import`. A checkpoint file from another
  release is refused and the store replays in full.
- **An interrupted `operator CONFIG init` strands the operator**
  (`recover` faults, `init` refuses STORE-EXISTS; PKT-647): remove the
  half-made store and init again.
- **No expiry.** Articles are released only by the operator's explicit rule
  (D03); there is no per-group expiry (O3).
- **Platforms.** Linux x86-64 with glibc 2.36 or later and the system libssl
  (OpenSSL 3.0 or later); OpenBSD 7.9 amd64 with LibreSSL, from a file system
  mounted `wxallowed` (/usr/local by default). No macOS release.

## 7. Release notes (DRAFT; not for friends until the cut)

> **fn 6.7.0** (draft)
>
> fn is a news server. You and your friends read and post with an ordinary
> newsreader (tin, slrn, Thunderbird) over TLS, and your node trades
> articles with your friends' nodes. Every decision it makes about an
> article, a login, a peer or its store is taken by code that is proved
> correct in ACL2 and ships inside the program.
>
> **What you get.** One file for your machine, `fn-6.7.0-linux-x86_64.tar.gz`
> (Debian 12, Ubuntu 24.04 or newer) or `fn-6.7.0-openbsd-amd64.tar.gz`
> (OpenBSD 7.9), with its own runtime inside. Nothing else to install but
> your system's TLS library. `sh fn/install.sh` puts it in `/opt/fn`
> (`/usr/local/fn`) and sets up the service; docs/install.md walks you from
> the download to a node your friends reach.
>
> **What it does.**
> - Serves newsgroups to readers over TLS, with logins; a friend joins with
>   an invitation code, no config edit and no restart.
> - Peers with other fn nodes (and with INN) over NNTP streaming, both push
>   and pull; a node behind NAT pulls.
> - Never loses a post it said yes to: an article is accepted only once it
>   is on disk, and power cuts at 1,281 points under a busy node lost
>   nothing acknowledged (with write barriers on).
> - Shows who wrote a signed post, what evidence carried it and what your
>   node knows about the key, as separate facts.
> - Tells you what is wrong: `fn operator CONFIG health` names one of eight
>   states with its own exit code.
> - Stays up when strangers probe it: per-address limits and named refusals.
>
> **What to know first.** Updating means reinstalling and importing your
> store (`store export`, then `store import`). Keep your disk's write
> barriers on. Large nodes need more memory than they should (about 16 bytes
> per stored byte today). Section 6 of the release checklist lists
> everything else we know is missing.
>
> `fn --version` prints `fn 6.7.0 (REV)`; the source is tagged `v6.7.0`.
