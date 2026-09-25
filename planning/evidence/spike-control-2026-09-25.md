# spike/control: control messages executed end to end (2026-09-25)

(Copied to dev from spike/mega by the night deputy because dev books and briefs cite it; the spike is the specification, never merged into dev. Its logs and scripts stay on spike/mega.)

Megaspike lane (D28) for packets C2 to C4 of
[the control-message design](../design-2026-09-25-control-messages.md), on
`spike/control` from `spike/mega` `0e2173ab`. The coordinator's answers were
Q1 build group control with the signed serial, Q2 accept and hide, and Q3
authorities may withdraw unsigned articles. D29 (from the review) came in
mid-lane. On dev, C4 waits until group authority and succession are decided.
This record marks every C4-only part so it can be separated.

Nothing here is a proof claim for dev. Every shortcut is listed under
"Deferrals", with the proof or ACL2 owner it needs.

## What works (native, two nodes, hbox)

Lab `tests/test_native_control_exec.py`: two developer-image owners peer over
loopback, feeding `fn.*,control.*`. Both nodes grant principal P
(`55`x32) `cancel newgroup rmgroup checkgroups` over `fn.*`. Principal Q
(`56`x32) is enrolled but has no grant. Articles are authored on node A only.
Every decision on B is B's own, made under B's rows. The relayed article
carries its `FN-Authorship` carrier intact, and nothing in it says
"executed".

| Step | Observed on A and on B |
| --- | --- |
| unsigned cancel of Q's signed article (POST) | filed in `control.cancel`; `HDR :fn-control` = `declined unsigned`; target still 223 |
| Q's signed cancel of an unsigned article Q did not write | `declined no-grant`; target still 223 |
| P's signed cancel of the unsigned article (Q3) | target `STAT` 430, absent from `LISTGROUP fn.test`; `executed withdrawal <t-unsigned@…> authority` |
| Q's signed cancel of Q's own article | 430; `executed withdrawal <t-signed@…> author` |
| P newgroup `fn.created`, `FN-Control-Serial: 1`, Approved | `GROUP fn.created` 211, in `LIST ACTIVE`; `executed reconfigure group newgroup fn.created 1 <P>` |
| Q newgroup `fn.bad` | `declined no-grant`; `GROUP fn.bad` 411 |
| P rmgroup `fn.created` serial 2 | `executed reconfigure group rmgroup fn.created 2 <P>` |
| P newgroup `fn.created` serial 1, replayed after serial 2 | `declined stale-serial` |
| P checkgroups `fn #7` (body `fn.test`, `fn.extra`) | `report 7 fn +fn.extra`; nothing changes |
| `operator A control apply-checkgroups <g-check@…>` (live) | `fn.extra` 211 on A; still 411 on B (the operator's own act) |
| restart B | withdrawn target still 430; decision still `executed withdrawal … authority` |

- Image: source `91611b6b`, developer profile, ACL2 8.7 `w28/acl2-literal-4g`,
  0 undefined-function lines.
  - `build/fn-host-developer` sha256 `3e8d3a776d4efc43e21d9bac088ae1a8c86337d7cc498a6cafccdc910ba2f483`
  - `.core` sha256 `7a1382eb118a992b24e8853fb726763767e52d41619c7f2381ba703356a6f272`
- Lab run: test source `4a3eca46` (the commits after `91611b6b` change only the
  test), `lab rc=0`, `OK`. Log `spike-control-2026-09-25/lab-4a3eca46.log`,
  sha256 `2c7485c35b714e6759f740b13f5c3a0075f78a3f6d798c8e9038bf1bda5800ca`.
  Scripts: `spike-control-2026-09-25/cert-build.sh` and `lab.sh`.
- Certification (hbox, `/tank/fn/scratch/spike-control/tree`):
  - run `certify-20260925T084924Z-2954542`, `--incremental --pcert --jobs 14`
    under `swarm-build`, over the 133 default-profile image roots plus
    `tests/acl2/control-exec-tests` and `tests/acl2/control-tests`;
  - 151 books installed from `/tank/fn/certcache` and 172 certified, `rc=0`;
  - `proof_artifacts.py validate --profile default`: `roots=133 result=loaded`.
- These are provisional-certification certificates (`--pcert` Complete wave).
  No persvati farm run was made. The spike needs no `skip-proofs`: the three
  new NNTP lemmas are proved, and the program-mode decisions are the
  deferral.

Two findings from the lab:

- A signed group-control source whose `Newsgroups` names a group this node
  does not serve (`fn.created,fn.test`) is refused by `hybrid-author`.
  Group-control articles in the lab therefore name `fn.test`. RFC 5537 does
  not require the named group in `Newsgroups`. The refusal site was not
  isolated.
- After an executed rmgroup, `LIST ACTIVE fn.created` still lists the group
  and `GROUP` answers 211, on both nodes. The delta is the operator's own
  `:remove-group`, which sets `retired-gen`. Whether a live operator
  `group retire` behaves the same on the reader port was not checked.

## What was built (by file)

- `books/control-exec.lisp` (new, `:program`): every decision.
  - `fn-ctl-grants` reads grants from the rows. `fn-ctl-authorize` executes
    only for `:verified` with a covering grant. It declines with `unsigned`,
    `carried`, `no-grant`, `outside-namespace`, `no-approved` or
    `unsupported-verb`.
  - `fn-ctl-cancel-decision` and `fn-ctl-withdrawal-effect` apply the
    section 2.5 exact-source rule. The author basis compares the target's
    historical verdict principal (`:verified` or `:carried`) with the
    canceller's. The authority basis requires every group the target is
    stored in to lie in the grant's namespace.
  - `fn-ctl-group-decision` (C4 only): the delta is the operator's
    `fn-cfg-create-group` / `fn-cfg-remove-group`. It checks `FN-Control-Serial`
    against the `ctl-hw NAME` high-water, and declines `moderated` newgroups,
    names that are not creatable, a missing serial and stale serials.
  - `fn-ctl-checkgroups-decision` and `fn-ctl-checkgroups-apply-deltas`
    (C4 only): the scope and `#chksernr`, the body groups inside the scope,
    and the adds and retires against the live table. Apply refuses
    `:stale-serial` and `:not-a-report`.
  - `fn-ctl-owed-deltas`: the first filed control article with no decision
    row.
  - `fn-ctl-visible-view`: the served view with withdrawn targets removed,
    the trie and buckets rebuilt, and the `:fn-control` items added. It keeps
    the unfiltered base under `:fn-ctl-base`, so a re-filter never works from
    a filtered view.
- `books/native-admin.lisp`: `control grant NS P VERB...`,
  `control revoke NS P` and `control apply-checkgroups MSGID`, all
  guard-verified. `books/native-operator.lisp`: `operator CONFIG control …`
  offline and live.
- `books/hybrid-store.lisp` `fn-hsig-filed-group-strings` and
  `books/peer-authored-accept.lisp`: a signed control article is filed in
  `control.<verb>` and the replay binding agrees, which removes C1's
  `:control-signed` refusal.
- `books/nntp.lisp`, `books/peer-offer-indexed.lisp` (its twin dispatch),
  `books/nntp-verdict.lisp`: `HDR :fn-control` by Message-ID or range. The
  effects, session and no-offer lemmas are proved in `nntp-verdict`,
  `nntp-verdict-effects` and `nntp-auth-fold`.
- `host/owner-host.lisp` `fn-owner-install-ocfg`: every installed owner gets
  its visible view, so a pinned reader's first view after a commit already
  excludes a withdrawn target (D29). `host/native/admin.lisp`
  `fnn-owner-ctl-after-action` runs after each serialized action whose
  (view version, generation) key moved. It publishes the owed decision
  through the same live path as an operator verb
  (`fnn-owner-live-deltas-locked`), at most 64 per trigger.
  `host/native-admin-host.lisp`: the live apply-checkgroups arm.
- `tools/fn_web.py`: a `withdrawn by author|authority` badge on a cancel
  article, and a `control: …` badge for other decisions, both labelled as
  the node's report. `tools/fn_verify.py`, given a cancel's Message-ID,
  reports `withdrawal: T withdrawn by B`. It checks that the signed Control
  line names the node's target and that the target is no longer served.
  With `--target-copy` it also checks the author basis independently. It
  exits 2 on a disagreement.
- `tests/acl2/control-exec-tests.lisp`: authorize witnesses and must-fails,
  namespace coverage, grant parsing, and the admin plan.
  `tests/acl2/control-tests.lisp`: signed control is now filed.

### Durable home of every decision (the spike's representation)

Every decision is a `:set-policy` row in the configuration, staged and
published through `fn-ocfg-step` and `fn-ocl-publish` like any operator
change:

- `ctl-grant NS P` = verbs, or `revoked`;
- `ctl-d MSGID` = `declined R`, `cancel T P NS|- GEN`,
  `group VERB NAME SERIAL P` or `report SERIAL SCOPE ±g…`;
- `ctl-hw NAME` = serial (C4 only);
- `ctl-applied SCOPE` = serial (C4 only).

A group change and its `ctl-d` and `ctl-hw` rows are one configuration record,
so the discharge is atomic with the change. A kill between the article's
acceptance and that record leaves the article owed: it has no `ctl-d` row,
and the first action after restart discharges it once. Nothing re-decides a
recorded article, and a revoke changes only later decisions. The lab did not
exercise the kill.

### C2 / C3 / C4 separation (D29)

- C2 (on dev now): `ctl-grant` rows, the `control grant|revoke` verbs and
  `fn-ctl-authorize`. The spike's grant verb list includes the group verbs;
  a C2-only slot should admit `cancel` alone and carry no serial or
  high-water fields.
- C3: `ctl-d … cancel` records, `fn-ctl-withdrawal-effect`,
  `fn-ctl-visible-view`, `HDR :fn-control`, and signed-control filing.
- C4 only: `fn-ctl-group-decision`, `FN-Control-Serial`, the `ctl-hw` rows,
  checkgroups (report, `ctl-applied` rows, `control apply-checkgroups`), and
  the delta-publishing half of `fnn-owner-ctl-after-action`. C3 needs only
  the decision row.

## Deferrals (every `SPIKE` marker)

| Where | Deferred | Owner on dev |
| --- | --- | --- |
| `books/control-exec.lisp` (whole book) | logic-mode admission and guard verification of every `fn-ctl-` decision | `books/control-exec.lisp` |
| `control-exec.lisp` header | the withdrawal and declined-discharge Store records, and `cause` on configuration records; decisions are policy rows instead | `books/store-node.lisp`, `books/config-records.lisp` |
| `control-exec.lisp` header | record width: a decision longer than a label (256 octets) is recorded `declined record-width`. This is a data cap and breaks D27 until records replace rows | the same |
| `control-exec.lisp` `fn-ctl-owed-deltas` | the incremental owed set; this scans the archive's control articles per ask | `fn-ctl-owed` over the recovered journals, `fn-owner-recover` |
| `control-exec.lisp` `fn-ctl-visible-view` | the filter inside `fn-own-refresh` with an incremental trie and buckets; this is a full rebuild per commit while withdrawals exist, plus K1 restated over the visible view | `books/owner.lisp`, `books/owner-invariants.lisp` |
| `host/owner-host.lisp` `fn-owner-ctl-filter` | the same: the host applies the filter at install | as above |
| `host/native/admin.lisp` | the execution trigger: raw Lisp asks ACL2 after each action | the composite with acceptance and the re-stage in `fn-owner-recover` |
| `books/native-admin.lisp` | the eighth `authorities` slot and delta kinds 11/12; grants ride `:set-policy`. Also `:overlapping-authority` admissibility | `books/config.lisp`, `books/config-invariants.lisp` |
| `host/native-admin-host.lisp` | offline `apply-checkgroups` (live only) | `books/native-admin.lisp` |
| `books/hybrid-store.lisp`, `books/peer-authored-accept.lisp` | the proof that the signed record binding names the filing group | `books/hybrid-store.lisp` |
| `books/nntp-verdict.lisp` | where the `:fn-control` items come from: the host puts them in the pinned verdict list. The shape lemmas are proved | a Store record family read at `fn-own-refresh` |
| `tests/acl2/control-tests.lisp` | the signed-filing teeth: the carrier hypothesis no longer separates | `tests/acl2/control-tests.lisp` |
| `tests/acl2/control-exec-tests.lisp` | teeth over the host-called plan and the served port | the same |

Also not done:

- the `430 withdrawn` text: readers see the ordinary 430/423 lines, and the
  machine signal is `HDR :fn-control`;
- the `control evidence MSGID` and `control log` operator verbs;
- the feed does not suppress a withdrawn target (design section 3; D29 allows
  forwarding an already enqueued target);
- Supersedes: only the cancel verb withdraws, and a `Supersedes` field is
  ordinary. The obvious route is to treat it as a cancel whose cause is the
  superseding article.

## What dev must prove to own this

Each theorem's subject is the host-called function.

- `fn-ctl-authorize-requires-verified-verdict`: `:carried` and `:absent`
  never execute. The spike's teeth show the carried and unsigned witnesses.
- `fn-ctl-authorize-requires-a-grant-covering-the-namespace`, and
  `fn-cfg-grant-control-admissible-iff` with `:overlapping-authority`.
- `fn-ctl-revoke-changes-decisions-not-records`.
- The two reconfiguration headlines re-certified over grant deltas.
- `fn-own-read-is-served-step-on-visible-pinned-prefix`.
- `fn-ctl-withdrawn-article-is-430` and
  `fn-ctl-withdrawn-article-is-absent-from-every-listing`.
- `fn-ctl-cancel-executes-only-for-author-or-authority`, including the
  cross-post rule (D29).
- `fn-ctl-withdrawal-preserves-retention` and
  `fn-ctl-withdrawal-preserves-history`.
- Cancel before target (D29): the target's first published view already
  excludes it. The spike gets this by filtering at install.
- C4: `fn-ctl-group-deltas-are-the-operators`,
  `fn-ctl-owed-is-discharged-exactly-once` (with the acceptance/configuration
  cut as a model crash point), `fn-ctl-serial-order-is-arrival-independent`,
  `fn-ctl-checkgroups-never-reconfigures` and
  `fn-ctl-checkgroups-apply-is-the-report`.
- The signed binding: a signed control article's record groups are its
  filing group, and replay agrees.
