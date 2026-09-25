# Operator verdicts — 2026-09-25 (PRF-095)

Lane `operator-verdicts` from dev `534a68d3`, commits `794f0ff5`,
`d265fddd` and `98987476` (and the record commit). It takes the spike operator surface's
findings (`spike/mega:planning/evidence/spike-operator-2026-09-25.md`) and
the large-article and signed-path findings, and makes each one an ACL2
decision the host calls. Packets done: PKT-103, PKT-104, PKT-095, PKT-102,
PKT-099. Not done: PKT-098 and PKT-100. Their status is in the last section.

## PKT-103: the developer owner run serves the profile's bound

**Cause.** Recovery installs each owner's posting configuration with the
record codec's payload ceiling (4,261,412,864) as the article bound
(host/owner-host.lisp `fn-owner-post-config`). Only the operator run's
control start (`fn-owner-posting-configure`, host/native/control.lisp
`fnn-control-start`) replaced that with the profile's A. The developer
`owner run` never reaches it. So a 40 KiB article passed the wire on a store
with A = 32,768, and it was refused later with the unnamed
`441 posting failed`.

**Fix.** `books/owner-served-bound.lisp` `fn-osb-install` is now what
`fn-owner-install-profile` (host/owner-host.lisp) calls. That function runs
on every run path, from host/native/owner.lisp `fnn-owner-install`, after
recovery and before listen. It keeps the posting bit, the agent and the
groups, and sets the bound to the profile's A. `fn-own-body-limit` hands that
bound to every connection opened afterwards.

**Theorems:**
- `fn-osb-install-serves-the-profile-bound` (keystone): if
  `(fn-bs-profile-admittedp profile)`, then the verdict is `:installed` and
  `(fn-own-body-limit owner') = (fn-bs-profile-max-article-octets profile)`.
- `fn-osb-install-keeps-the-posting-configuration`: allow, agent and groups
  are unchanged.
- `fn-osb-install-keeps-configp`: a well-formed configuration stays
  well-formed.
- `fn-osb-install-refuses-unadmitted-by-definition`: not registered.

**Teeth** (tests/acl2/owner-served-bound-tests):
- Witness: the recovered owner's bound goes from 4,261,412,864 to 32,768
  under the development profile, and to 65,536 under a D27-default profile
  with A = 65,536.
- `must-fail` without admission: `nil` installs nothing and keeps the
  ceiling.
- `must-fail` without configp: `(fn-own-configure nil nil)` stays malformed.

**Developer `store ROOT init`.** It now calls `fn-nop-developer-init`
(books/native-operator.lisp, from host/native/io.lisp
`fnn-command-developer-init`). That function reads the words with the
operator's profile grammar over the development base.
- A profile flag sets its field.
- A flag-shaped word left among the groups is refused `:flag-word-as-group`.
  This is a local policy: RFC 5536 §3.1.4 permits such a name, but fn does
  not take one from a command line.
- The operator's `init` refuses the same word (`fn-nop-parse-init`).
- The theorem `fn-nop-developer-init-groups-are-not-flags-by-definition` is
  named for what it is and not registered.
- Witnesses and a `must-fail` are in tests/acl2/native-operator-tests.
- Development base plus `--max-article-octets 65536` is refused by name,
  `max-record-octets-below-the-article-record`. The development R is too
  small for it, so the native test uses `--profile default`.

**Native** (hbox, image built from `794f0ff5`, sha256 in
`operator-verdicts-2026-09-25/image.sha256`):
- `test_article_over_the_body_limit_is_refused_and_the_owner_survives`
  passes (`native-owner-oversize.log`, `845de612…`). The reply is
  `441 posting failed; the article exceeds the configured size`.
- The developer init refuses `--no-such-flag fn.test` with
  `init refused: flag-word-as-group` (exit 5). Its `status` prints
  `max-article-octets=65536` (`native-operator-verdicts.log`, `6dd6c80d…`).

## PKT-104: a native run of the 437 transit refusal line

`tests.test_native_control_filing.NativeControlFilingTests.test_transit_ihave`
now pins two things:
- The exact wire line:
  `437 transfer rejected; control message not filed: its control group is not configured here (control-not-filed)`.
- The log line: `refused transit … message-id=<c1-transit-cancel-1@…> code=437 … detail=control-not-filed`.

Both passed natively (`native-transit-437.log`, `03e7b337…`), together with
`test_served_post`. The subject is host/native/owner.lisp
`fnn-owner-transit-complete`.

## PKT-095: refused POSTs are logged on both paths

The lines are in books/owner-log.lisp.

**Served path.** `fn-olog-served-refusal-lines` is called by
host/owner-host.lisp `fn-owner-chunk` over the effects it installs, and
written by host/native/owner.lisp `fnn-owner-handle-chunk`. It gives one line
per 441 reply a read sends, of the form
`refused post path=served connection=N reason=R time=T`. The reason comes
from reading the reply back against `fn-post-refusal-line`, and is
`unnamed` when no table entry matches.

**Control path.** `fn-olog-control-refusal-line` is set by
`fn-owner-operator-submit` and written in
`fnn-owner-control-submit-serialized` right after a `:refused` submit.

**Theorems:**
- `fn-olog-served-refusal-lines-one-per-441` (keystone): the number of lines
  equals the number of 441 replies in the effects, and each line is one line
  whose first word is `refused`.
- `fn-olog-post-refusal-reason-names-the-sent-reason`: every tabled reason
  reads back as itself.
- `fn-olog-control-refusal-line-says-refused-iff-submit-refused` (keystone,
  no hypothesis): the line says refused iff
  `fn-own-operator-submit-result` is `:refused`.
- `fn-olog-served-refusal-line-is-one-line` and
  `fn-olog-control-refusal-line-is-one-line`.

**Teeth** (tests/acl2/owner-log-tests):
- Served witness: a read with 340, 441 unknown-group, 240, 441 oversize and
  an untabled 441 gives exactly three lines, with reasons unknown-group,
  oversize and unnamed.
- Control witness: `reason=control-mismatch`. The `:busy` case gets no line.
- `must-fail`s: "one line per reply", "the read-back without membership",
  and "a line for every non-submission".

**Native** (`native-operator-verdicts.log`):
```
refused post path=served connection=0 reason=unknown-group time=2026-09-25T10:03:44Z
refused post path=control message-id=<ov-control-refused@example.invalid> reason=unknown-group time=2026-09-25T10:03:44Z
accepted post path=served connection=1 message-id=<ov-served-ok@example.invalid> agent=fn.example.invalid time=2026-09-25T10:03:44Z
```

## PKT-102: set-password's answer is ACL2's

After the durable credential write, host/native/io.lisp
`fnn-store-owner-observation` takes a non-blocking shared flock of the
configured store's `writer.lock`. The observation is `:held`, `:free`,
`:absent` or `:unknown`. books/native-auth-admin.lisp
`fn-native-auth-admin-effect-word` maps it to `effective-at-next-start` or
`restart-required`. It is called from host/native/auth-admin.lisp
`fnn-native-auth-admin-result-code`. The store root comes from the new
projection `fn-native-operator-result-principal-store-octets`.

**Theorem.** `fn-native-auth-admin-effect-word-restart-unless-no-owner`
(keystone): the answer is `restart-required` iff the observation is neither
`:free` nor `:absent`.

**Teeth.** Five witnesses, plus `must-fail`s for "always restart-required"
(the spike's behaviour) and "never".

**Native:**
- Offline: `accepted operator principal set-password effective-at-next-start`.
- With an owner running: `accepted operator principal set-password restart-required`.

The path-and-login lane's `principal bind` goes through the same
`result-code`, so it inherits the verdict when it merges.

## PKT-099: `store needs-upgrade` and the rollback check

**needs-upgrade.** `fn-profile-needs-upgrade-verdict`
(books/store-profile-upgrade.lisp) is by definition the verdict of the
no-argument `upgrade-profile`. There is one owner and no second computation.
- Keystone `fn-profile-format-7-store-needs-upgrade`: every admitted
  format-7 store needs the step.
- Witnesses: both format-7 tuples answer needs-upgrade, both presets answer
  current, and `nil` answers invalid.
- `must-fail`s: one without the format-7 hypothesis, one without admission.

**Rollback check.** `fn-profile-rollback-verdict old lengths` answers
`(:sound)`, `(:refused :invalid-rollback-profile)` or
`(:refused :record-exceeds-rollback-profile INDEX LENGTH BOUND)`. The bound is
`fn-profile-rollback-record-bound`:
- for a format-8 profile, its R;
- for a format-7 tuple, H/T, which is 196,608 for scale. This is the ceiling
  format 7 derived. The translation's R, 17,138,486, is larger and is not
  what the old image enforced.

Keystone `fn-profile-rollback-sound-iff-records-within`: the check says
`:sound` iff OLD is admitted and every length is within that bound.
Witnesses: `(900 196608)` is sound under format-7 scale, and
`(900 196609 12)` is refused at index 1. `must-fail`s: soundness by
admission alone, and by the lengths alone.

**Verbs.** `fn operator CONFIG store needs-upgrade` and
`fn operator CONFIG store rollback-check /abs/kept/config.json`
(`fn-nop-parse-store`; host/native/io.lisp `fnn-command-needs-upgrade` and
`fnn-command-rollback-check`). The host reads config.json, the kept file and
the lengths of the committed transaction files, and decides nothing.

**Limitation.** bounds-join §5 also says the old image's bounded open read
is 65,538-sized. That is a constant of that image, not a field of its
profile, so this check cannot see it. For a format-7 store holding records
between 65,538 and 196,608 octets, the check can say sound when the old image
would still refuse. None of the deployed store's records are that size
(1 MiB articles were never admitted by format 7's A = 32,768). This is
recorded, not proved.

**Native** (image from d265fddd, `image-2.sha256`, developer
`2905055b…`; `native-operator-verdicts-2.log`). The run used
`test_needs_upgrade_and_rollback_check` with `FN_OLD_NATIVE_HOST` set to
c3420013's fn-host, so the store was initialised at format 7. The results, in
order:
1. `needs-upgrade`.
2. After a served POST, `store upgrade-profile` gave
   `upgraded profile=current transactions-used=1 transactions-budget=128 previous-budget=128`
   and format 8.
3. `needs-upgrade` then said `current`.
4. `rollback-check` against the kept format-7 config.json said
   `rollback sound transactions=1`.
5. `rollback-check` against a garbage file said
   `rollback refused invalid-rollback-profile` (exit 1).

All four operator-verdict tests passed on that image. The oversize test and
the whole control-filing module (3 run, 1 skipped) also passed on it.

## Certification

| Run | Rev | Scope | Result | Manifest |
| --- | --- | --- | --- | --- |
| persvati run-20260925T095638Z-2f20, w25 acl2-literal, 2 jobs, 300 s | 794f0ff5 | `--affected-by` owner-log, owner-served-bound, native-operator, native-auth-admin: 10 roots, 12 certified | 12/12 passed. owner-served-bound took 70.0 s, over the 10 s limit (two lemmas at 46.6 s and 17.3 s), and was fixed in d265fddd | `manifests/certify-20260925T095703Z-3534998.json` |

Every other book in run 2f20 is under 10 s:
- native-operator 7.7 s, owner-log 6.5 s, native-auth-admin 5.0 s;
- owner-log-tests 7.7 s, native-operator-tests 8.3 s,
  owner-served-bound-tests 5.2 s.

| persvati run-20260925T100555Z-d204 | d265fddd | `--affected-by` store-profile-upgrade, owner-served-bound, native-operator: 15 roots, 16 certified | 16/16 passed. owner-served-bound took 4.3 s; store-profile-upgrade-tests took 24.3 s (two rollback `must-fail`s at 17.2 s and 4.0 s), fixed in 98987476 | `manifests/certify-20260925T100622Z-3651094.json` |
| persvati run-20260925T101629Z-e360 | 98987476 | tests/acl2/store-profile-upgrade-tests | passed, 2.9 s | `manifests/certify-20260925T101643Z-3770218.json` |

Every book changed by this lane is now under 10 s at 2 jobs, at the final
bytes.

The hbox image build certified its default closure incrementally
(`certify-20260925T095740Z-3091894` on hbox, w28): 232 books installed from
the cache, and every remaining one passed, owner-served-bound included.

## Native logs (planning/evidence/operator-verdicts-2026-09-25/)

| File | sha256 |
| --- | --- |
| native-owner-oversize.log (PKT-103) | `845de61243179d2e8f232556a16aeb3ba3a8c4839c2c36686314f77c79ef55ec` |
| native-transit-437.log (PKT-104) | `03e7b337ac7506b7dc41b238cce762e9e3caf335b34ef3ccc8b484b2cb3a5d8f` |
| native-operator-verdicts.log (PKT-095, PKT-102, init) | `6dd6c80dd4962db1b0edb60d1a3f828c6427ba8720eef7a482cc0a68996ae03f` |
| native-owner-all.log (tests.test_native_owner, 18 run) | `399f527d87985ab32124259e161082bdac906c1edd711b5581d9e7e185f48a4a` |
| native_owner_chunk_loop_raw.log (after the stub fix) | `81faf566092699cc31286d56fea0ab5243ea9c42823e776bdaf6140ea0d67f2a` |
| native_developer_selectors_raw.log | `63a0e73b20ca8cf99771370d767dfaa545ceda27f796358b0753efe55c4355e3` |
| image.sha256 (fn-host `9089a721…`, fn-host-developer `da33b83a…`) | `6b3faaf69e4f67488872fba86aa4fbc2edc2e08350ff6c77ec4de6558f272795` |
| native-operator-verdicts-2.log (d265fddd; PKT-099 with the format-7 start, and all the others) | `ede70eae91b7dbddd1765c9b4a7214189443d1bc04f355d184931a6c073c62c7` |
| native-control-filing-2.log (d265fddd) | `e8a4771f7a6ebf9158c15f5b346e3a28300ba0196cf93dc74f7faaa769024d0c` |
| native-owner-oversize-2.log (d265fddd) | `a52918cd69bed498e774ee360c094c5071492c775b4defa95f7476d88c70ed13` |
| image-2.sha256 (d265fddd images) | `5e17d5406d76287b1d0945ee0f5aeff5545dbfa6d47a0215db760ff2a35022c2` |

**tests.test_native_owner.** 18 tests ran: 16 passed and 2 of the structure
tests failed.
- The two failures were first run under hbox's `/usr/bin/sbcl` (2.2.9), which
  lacks `sb-bsd-sockets:sockopt-error`. That is an environment defect of
  those two tests.
- Under the toolchain SBCL (`/tank/fn/sbcl`), `native_owner_chunk_loop_raw`
  failed on this lane's new `fn-owner-refusal-lines` read. Its stub now
  answers it, and it passes.
- `native_developer_selectors_raw` fails on `fnn-core` being undefined inside
  `fnn-recovery-test-fault`. That is a stub gap this lane did not touch, and
  it is open for its owner.

## Not done, and why

- **PKT-098** (node-health verdict: fault, rate, headroom, in a new book):
  not started, because the budget went to PKT-099. It now has its inputs: the
  refusal lines from PKT-095 give the rate signal. The headroom query needs
  live-status (the control-socket status) first.
- **PKT-100** (restore verb). This needs a decision, and here is why.
  - `fn-cpa-rollover-proposal` (books/checkpoint-auxiliary.lisp:75) refuses
    `:unbootstrapped` whenever the store carries no consumer incarnation.
    The fresh identity it mints is the consumer incarnation, which lets
    cursor holders tell a restored history from the original. A news-only
    store has no incarnation to roll over.
  - For an NNTP-only node, the identity a restore can betray is the per-group
    article-number allocator. A backup older than the node's last state would
    reissue numbers that readers and peers already saw, attached to
    different articles. RFC 3977 §6 forbids reusing an article number within
    a group.
  - So a fresh-identity restore for news-only stores has to choose one of
    three things. (a) Advance every group's allocator past any number the
    lost suffix could have issued; the bound is unknown without the lost
    suffix, so an operator-supplied or wall-derived gap is needed. (b) Mint
    a new group-numbering epoch that readers see as a reset. (c) Accept
    same-identity restore only from a backup known to be the latest state.
  - That choice is ember's. It is recorded here and not implemented.
- **Not touched:** PKT-091, PKT-105.
- **Also not changed:** host/native/hybrid-control.lisp
  `fn-owner-live-post-config` still hands the control-signed path the codec
  ceiling (`fn-owner-post-config`). The publication gate still enforces A
  there. It is a candidate for `fn-osb-config`.
