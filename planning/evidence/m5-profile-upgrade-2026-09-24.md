# M5: the offline store-profile upgrade (2026-09-24)

Lane `m5-profile-upgrade`, branch `lane/m5-profile-upgrade` from dev
`1b734868`. Source commit `05b96703`. The registry, documentation and
evidence follow on the same branch.

The deployed store has 128 transactions (development profile) and 7 used. Its
budget comes from the profile in `config.json`, and that profile cannot be
raised by a configuration record (m5-capacity). This packet raises it offline,
on the existing store, with the articles kept.

## The theorems

`books/store-profile-upgrade.lisp` (`fn-profile-`):

- **The relation.** `fn-profile-upgradep OLD NEW` holds when all of these do:
  - both are named profiles and NEW is not OLD;
  - field 0 (record format) and field 5 (frontier format) are equal;
  - fields 1 to 4 (capacity, payload, aggregate replay bound, transaction
    count) are no smaller in NEW;
  - the per-record ceiling (field 3 / field 4) is no smaller in NEW.

  Over the four named profiles, exactly two pairs satisfy it: development to
  scale, in format 7 and in legacy format 6. The test book checks eight of
  the sixteen pairs: both upgrades, the no-op, the downgrades, both
  cross-format pairs and a non-profile. It does not state the relation as a
  symbolic `iff`: that attempt ran out of time in clause subsumption over
  the quoted profile constants.
- **Monotone gates.** Each gate below is proved of the function the host
  calls:
  - `fn-profile-upgrade-keeps-txn-observation`: if
    `(fn-profile-txn-observation names (nth 4 OLD) lower)` is not
    `:invalid`, the observation under `(nth 4 NEW)` is equal to it. The
    subject is called from `host/store-host.lisp`
    `fn-store-txn-observation-selected`, which `host/native/io.lisp`
    `fnn-transaction-files` calls with field 4 of the loaded profile. This
    packet moved the bound from inline program-mode code into this
    logic-mode function.
  - `fn-profile-upgrade-keeps-replay-bound`:
    `(fn-profile-replay-within-boundp OLD agg)` implies the same under NEW.
    The subject is called per record from `fnn-durable-records` through
    `fn-store-profile-replay-within-bound`. It replaces the host comparison
    `(> aggregate (fnn-config-max-recovery store))`, which is deleted.
  - `fn-profile-upgrade-keeps-publication-admissibility`:
    `fn-bs-publication-admissiblep` (used by `fnn-publish`) holds under NEW
    wherever it held under OLD.
  - `fn-profile-upgrade-keeps-verdict`: if `(fn-sbud-verdict OLD kind s)` is
    `:admissible`, so is `(fn-sbud-verdict NEW kind s)`. This is the verdict
    the owner and `store post` consult.

  Replay itself (`fnn-bridge-recover`) takes no profile argument. It is a
  function of the record list, the frontier and the configuration records,
  and the upgrade writes none of them. So a store the old profile admits is
  admitted by the new one with the same observation, and it replays to the
  same state. That last step is a code fact about the call's arguments, not
  a theorem.
- **The verb writes only upgrades.** Theorem
  `fn-profile-upgrade-verdict-writes-only-upgrades`: when
  `(fn-profile-upgrade-verdict CURRENT TARGET)` is `(:upgrade OCTETS …)`,
  `(fn-bs-config-decode OCTETS)` is `(fn-bs-config-for-profile TARGET)`,
  and that value is an upgrade of CURRENT. The host calls this verdict at
  `host/native/io.lisp` `fnn-command-upgrade-profile`, through
  `host/store-host.lisp` `fn-store-profile-upgrade-verdict`. The proof
  rests on `fn-bs-config-decode-of-encode` (a named profile's frame
  decodes to itself), which holds under A-CRYPTO through
  `fn-frame-open-of-seal`.
- **Budget after reopen.** `fn-profile-upgrade-budget-after-reopen`: under
  the same hypothesis, `fn-sbud-budget` of the decoded frame equals
  `fn-sbud-budget` of the named profile. The ground fact
  `fn-profile-upgrade-development-to-scale` gives budgets `(128 4096)`,
  development to development is `(:refused :same-profile)`, and scale to
  development is `(:refused :not-an-upgrade)`.

`books/byte-store-profile-program.lisp` (`fn-bs-`):

- **`fn-bs-profile-program stage octets`**: create in `:staging`, write,
  fsync, `rename` onto `:root` `config.json`, fsync the root. A `:cut`
  follows each durable syscall. D1 to D3 are asserted on a ground instance.
- **`fn-bs-profile-program-crash-is-old-or-new`.** The hypotheses:
  - `fn-bs-profile-inputp bs stage old-ino`: the pending list is empty,
    `stage` is a string, `config.json` durably names `old-ino`,
    `old-ino` is below the next inode, and the stage name is free;
  - `octets` is a non-empty octet list;
  - `p` is a member of the successful run (outcomes `nil`).

  The conclusion: for every `choices`, the crash image
  `(fn-bs-crash (car p) choices)` names at `config.json` either `old-ino`
  with its original content, or the new inode `(fn-bs-next-ino bs)` with
  exactly `octets`. The proof takes 0.2 s.
- **`fn-bs-profile-program-crash-budget-is-old-or-new`.** Under the same
  hypotheses, the budget of the decoded `config.json` in any crash image is
  a member of `(budget-of-old-frame budget-of-new-frame)`.

**Covered scope.** Only the successful run and its crash images are covered.
When a syscall reports an error, the host classifies it: before the rename it
is a known refusal (exit 1) and `config.json` is untouched; at or after the
rename it is uncertain (exit 3). Both arms are witnessed natively below but
are not modelled. The quiet-store hypothesis holds because the verb runs in a
fresh process after open's recovery barriers. The teeth show that the
conclusion fails without it.

## Teeth

`tests/acl2/store-profile-upgrade-tests.lisp` contains:

- the relation over all named pairs;
- all five verdict answers;
- equality of the upgrade frame and the `init --profile scale` frame;
- 129 transaction names (invalid under development, valid under scale) and
  127 names (the same observation under both);
- the 24 MiB replay boundary;
- verdicts at 3, 128 and 200 used;
- a reachable byte run whose rename cut has both images (inode 3 with
  `(7 7)`, inode 5 with `(1 2 3)`), and a torn write-cut image that is never
  named.

It also has one `must-fail` per keystone hypothesis, each at constants.
Without the upgrade (scale to development), or without a valid old gate, the
conclusion fails for the observation, the replay bound, admissibility and the
verdict. Without the `:upgrade` tag, the verdict's `cadr` does not decode.
Without the quiet store, a pending `(9 9)` write to inode 3 lands as a third
content. Without the program's order (rename of an unfenced stage), the name
reaches a zeroed inode.

`tests/acl2/native-operator-tests.lisp` covers the `store upgrade-profile`
plan: both words, the plan's action and profile, and four usage errors.

## The verb

- `fn operator CONFIG store upgrade-profile development|scale`: ACL2 parses
  it (`fn-nop-parse-store`) and gives it native action `:upgrade-profile`.
  `host/native/operator.lisp` `fnn-operator-execute-store-action` then
  calls `fnn-command-upgrade-profile`.
- Developer entry: `fn --fn store ROOT upgrade-profile WORD`, with the word
  parsed by ACL2 (`fn-store-profile-word`).
- `fnn-command-upgrade-profile` opens the store with
  `fnn-open-live-store root t`, the same way `recover` does. That takes the
  exclusive writer lock (a running owner makes it fail with `store is
  already locked`, exit 1), then does full replay and the recovery barriers
  under the old profile. It then asks the verdict and writes through
  `fnn-upgrade-profile-write`. That function stages under
  `.stage-profile-<pid>-<hex>`, which is a `.stage-` name, so the recovery
  sweep owns any orphan it leaves.
- **Same profile is refused, and so is a downgrade** (exit 1, reasons
  `same-profile` and `not-an-upgrade`), and neither writes anything.
  - Why refuse the same profile rather than report success: rewriting an
    identical frame would open a crash window for nothing.
  - A retry after an uncertain outcome that did land reads as "already
    scale", which is the true answer.

## The cut coordinates

`tests/campaign/native_cuts.py` `PROFILE_CUTS` lists the cuts of
`fn-bs-profile-program` (`book=byte-store-profile-program.lisp`). They are
selected by `FN_NATIVE_PROFILE_FAULT=CUT:kill|eio`, a registered developer
selector, so a production image refuses to start with it.

| cut | step index | the next open reads |
| --- | --- | --- |
| `profile-created` | 1 | old |
| `profile-written` | 3 | old |
| `profile-staged-durable` | 5 | old |
| `profile-replaced` | 7 | either |
| `profile-durable` | 9 | new |

`verify_profile_cut_map` (part of `verify_native_cut_map`) checks three
things:
- the host declaration equals the model's `:cut` list;
- `fnn-upgrade-profile-write` reaches the cuts in program order;
- each candidate matches the program (old before the rename, either after
  it, new after the root barrier).

## Certification

- **persvati.** Run `run-20260924T175942Z-2fa9` produced manifest
  [`certify-20260924T180001Z-3124349`](manifests/certify-20260924T180001Z-3124349.json),
  status `passed`, with 2 jobs and a 300 s timeout.
  - Selection: `--affected-by books/native-operator
    --affected-by books/store-profile-upgrade
    --affected-by books/byte-store-profile-program`. This gave 6 roots;
    7 books were certified and 131 installed from the cache.
  - Toolchain `w25/acl2-literal`, identity `1b4169e9…`.
  - Book times:

    | book | seconds |
    | --- | --- |
    | `books/store-profile-upgrade` | 2.9 |
    | `books/byte-store-profile-program` | 3.0 |
    | `tests/acl2/store-profile-upgrade-tests` | 3.0 |
    | `books/native-operator` | 4.4 |
    | `tests/acl2/native-operator-tests` | 5.6 |
    | `tests/acl2/native-operator-host-tests` | 4.9 |
    | `host/native-operator-host` | 4.6 |

- **hbox (the image closure).** The tree came from `git archive 05b96703`
  in `/tank/fn/scratch/m5-profile-upgrade/tree-05b96703`. Command:
  `certify_books.py --incremental --no-publish --jobs 2` under
  `swarm-build`, with w28 `acl2-literal-4g` and `/tank/fn/certcache`.
  - 282 books installed and 2 certified (`books/native-operator` 3.8 s,
    `books/store-profile-upgrade` 2.5 s).
  - Manifest
    [`certify-20260924T180112Z-1750504`](manifests/certify-20260924T180112Z-1750504.json),
    status `passed`.
  - `proof_artifacts.py validate --profile default` reported 114 roots
    loaded.

## Native results (hbox, images from 05b96703)

Image hashes, from [image-hashes.txt](m5-profile-upgrade/image-hashes.txt):

| image | launcher | core |
| --- | --- | --- |
| production `fn-host` | `ccaa6633…` | `bcd15f7f…` |
| developer `fn-host-developer` | `41276fa6…` | `1036b70d…` |

OpenSSL 3.5.8 from `FN_OPENSSL_PREFIX`.

- [`native-profile-upgrade.log`](m5-profile-upgrade/native-profile-upgrade.log)
  (SHA-256 `b39094493ca9197772c75e25d79a73831a8b314ec5b062814c7a2bb63fefbaf0`):
  `tests.test_native_profile_upgrade`, **5 tests, OK, 9.6 s**.
  - Development store, then 3 POSTs (`240` each), then stop: headroom is
    `used=3 budget=128`.
  - `operator store upgrade-profile scale` exits 0 and prints
    `upgraded profile=scale transactions-used=3 transactions-budget=4096 previous-budget=128`.
    `config.json` then equals the scale frame `bf6e6df9…`, and `status`
    reads `used=3 budget=4096` with the charge unchanged.
  - The owner then accepts the fourth POST (`240`), and `status` reads
    `used=4 budget=4096`.
  - Through both entries: development to development is refused
    (`same-profile`); scale to development is refused (`not-an-upgrade`);
    scale to scale is refused (`same-profile`). The frame bytes are
    unchanged each time. `huge` is usage at the operator and
    `unknown-profile` at the store entry.
  - A held writer lock and a running owner both refuse the upgrade with
    `already locked`, and the frame is unchanged.
  - Every `PROFILE_CUTS` cut, with SIGKILL and with EIO, through the
    operator and the developer store entries: 20 cases.
    - Each reopen read the old frame (`dcbd90d3…`, budget 128) or the new
      one (`bf6e6df9…`, budget 4096), byte for byte, as the candidate
      column says.
    - The first three cuts read 128. `profile-replaced` read 4096 in all
      four cases, since on ext4/ZFS the rename landed. `profile-durable`
      read 4096.
    - EIO before the rename exited 1, and at or after it exited 3.
    - `recover` then emptied `staging/`. A retried upgrade ended at scale,
      and was refused as `same-profile` where the cut had already landed.
- [`native-regression-2.log`](m5-profile-upgrade/native-regression-2.log)
  (SHA-256 `fc4b544334e9f817d66cc264f457d5851e24f7458ff4c95cbfce0866eb443cd5`):
  `test_native_operator_verbs`, `test_native_recovery`,
  `test_native_cut_map` and `test_native_owner` on the same images, with
  `FN_ACL2` set. 52 tests, 2 failures. Both are
  `NativeOwnerHandlerStructureTests`, which run
  `tests/native_developer_selectors_raw.lisp` with hbox's system `sbcl`,
  and that SBCL has no `SB-BSD-SOCKETS:SOCKOPT-ERROR`. That is an
  environment defect of the box. The same class passes on the Mac: 6 tests,
  OK.

## Findings

1. **The second count** (open, not changed here). `host/native/owner.lisp`
   `fnn-owner-publish-prepared` names the transaction file at line 673 by
   `(fnn-publish store (fnn-owner-service-records service) …)`. That counter
   is a slot of the service struct (line 37), initialized from
   `(length records)` at open (line 504) and incremented at line 692 after
   each finish.
   - **ACL2 could own it now.** The pending record is already ACL2's
     (`host/owner-host.lisp:523` `fn-owner-pending-octets` reads
     `(fn-sf-record-candidate (fn-sn-files (fn-owner-store state)))`).
     `fn-sbud-candidate-takes-sequence-used` (books/store-budget.lisp)
     proves that a candidate's sequence is `fn-sbud-used` of the Store.
     So a wrapper `fn-owner-pending-sequence` returning
     `(fn-store-event-sequence candidate)` could replace the slot, its
     initialization and its increment.
   - The developer `store ROOT post` has the same shape, at
     `host/native/io.lisp` `fnn-command-post`:
     `(fnn-publish store (length records) record)`.
   - Today ACL2 refuses a mismatch (`fn-sf-candidatep`), so the second
     count is checked, not trusted.
2. **Monotone set, what it leaves out.** Two uses of field 4 are not in the
   monotone set:
   - `host/native/checkpoint.lisp` passes field 4 to
     `fn-store-checkpoint-compaction-coverage` (a selected pack) and to
     `fn-bs-pack-reclaim-plan`.
   - `host/store-host.lisp` `fn-store-txn-prefix-reclaim-plan` keeps its
     own inline `(<= (len names) maximum)`.

   Neither is on the open path of a store without a selected pack. The
   deployed node has none, as far as its record says. Proving them monotone
   is open.
3. **Host twin removed.** The replay aggregate bound was a host comparison
   against field 3. It is now ACL2's (`fn-profile-replay-within-boundp`),
   and `fnn-config-max-recovery` is deleted. `fnn-validate-post-boundary`
   still compares field 2 with `(fnn-constant :max-store)` on the host, as
   a sanity check. That remains a twin.
4. **`make check`** fails only on the generated `planning/ledger.*` being
   stale, which lanes do not write. `proofs.json`'s PRF-072 events were
   generated by `tools/ledger.py --write`.

## Procedure for the deployed node (the coordinator runs it)

The deployed image `47bdb9a4` does not have the verb. Before starting, an
image containing this branch must be built, qualified and installed beside
the current one, as `/tank/fn/node/fn-<rev>`, by
`packaging/install-native.sh`. Do not repoint `ExecStart` yet.

1. Record the starting state. `sha256sum /tank/fn/node/store/config.json`
   must equal the development frame `dcbd90d3…`. This is m5-capacity's
   coordinator check. If it differs, stop: the store's frame is not the
   format-7 development profile, and `store upgrade-profile scale` will
   refuse it or does not apply. Make a copy aside:
   `cp -p /tank/fn/node/store/config.json /tank/fn/node/config.json.development-<date>`.
2. Stop the node's unit (the one whose `ExecStart` names
   `/tank/fn/node/fn-47bdb9a4`), and confirm the process is gone.
3. `/tank/fn/node/fn-<rev>/bin/fn operator /tank/fn/node/fn.toml status`.
   Expect `headroom transactions-used=N transactions-budget=128`, with N the
   node's count (7 at the last record).
4. `/tank/fn/node/fn-<rev>/bin/fn operator /tank/fn/node/fn.toml store upgrade-profile scale`.
   Expect exit 0 and
   `upgraded profile=scale transactions-used=N transactions-budget=4096 previous-budget=128`.
   - Exit 1 `already locked` means an owner is still running; go back to
     step 2.
   - Exit 3 means the outcome is uncertain. Run step 5 anyway: it reads
     old or new. If it reads old, repeat step 4.
5. Run `status` again, and check `sha256sum` of `config.json`. Expect
   budget 4096 with N used, and the scale frame `bf6e6df9…`.
6. Start the unit, either on the new release (repoint `ExecStart`) or
   unchanged on `47bdb9a4`. `47bdb9a4` already accepts the scale frame
   (`fn-bs-meta-config-valuesp` names it) and derives 4096 from it. Then run
   the LAN probe.

Rollback of the profile is the copied development frame, put back with the
owner stopped. That is a downgrade the verb refuses. It is safe only while
used ≤ 128, and it must be done by hand.
