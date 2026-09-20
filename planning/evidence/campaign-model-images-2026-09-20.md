# Campaign against the byte model: first run

The fault campaign has always compared a recovered store with a *reference
run*. This run is the first in which the **byte-level crash model** says
what the recovered store is allowed to be, per cut, and the campaign checks
it. Every number below is a wall time on one host under its load at that
moment; none of it is a proof.

## What ran

| fact | value |
| --- | --- |
| lane | `w9/storage`, branch `w9/storage` from `dev` at `52eb0db` |
| host | hbox (the coordinator moved proof and campaign work there: persvati was at load 9 with five queued runners and zero ACL2 processes) |
| tree | `/tank/fn/lanes/w9-storage` |
| acl2 | `/tank/fn/acl2-8.7/saved_acl2`, ACL2 8.7 |
| books | `books/byte-store`, `books/byte-store-invariants`, `books/byte-store-programs` certified: `build/acl2/certify-20260920T182231Z-1039695` |
| command | `FN_ACL2=... swarm-build python3 tests/campaign/campaign.py --quick --scenario cross-post --model-images --json build/probe/campaign-model.json` |
| result | `pairs=7 failures=0 seconds=97.4` |
| output | `/tank/fn/lanes/w9-storage/build/probe/campaign.out` |

## What the model said, per cut

The model state at a cut is `fn-bs-run` over the program constant of
`books/byte-store-programs.lisp` applied to the imported template store; the
admissible set is the record counts over the whole-or-lost choices of that
state's pending list.

| cut | pending at the cut | model admits | host recovered |
| --- | --- | --- | --- |
| `store:frontier-staged-durable` | `(:SET-ENTRY :STAGING ".allocation-campaign" 8361628)` | `(1)` | 1 |
| `store:frontier-replaced` | the staging name, `(:SET-ENTRY :ROOT "allocation-frontier.json" ...)`, `(:DEL-ENTRY :STAGING ...)` | `(1)` | 1 |
| `store:record-staged-durable` | `(:SET-ENTRY :STAGING ".stage-campaign" 8361628)` | `(1)` | 1 |
| `store:record-linked` | the staging name and `(:SET-ENTRY :TRANSACTIONS "campaign.txn" ...)` | `(1, 2)` | 2 |
| `store:record-attempted` | the same two | `(1, 2)` | 2 |
| `store:recover-barrier` | `NIL` | `(1)` | 1 |

`store:finish-durable` is the seventh pair and is not model-checked:
`Store.finish` issues no syscall, so `PROGRAM_OF` maps no program to it.

**The check is not vacuous.** Four of the six sets have exactly one element,
so at those cuts the model pins the recovered record count rather than
permitting it: had the host published a record at `record-staged-durable`,
where `os.link` has not run, the run would have failed. The two two-element
sets are precisely the crash window the cut table describes in prose --
`final-link` issued and its reply not yet observed -- now computed from the
pending `:set-entry` on `:transactions` instead of asserted.

## What this run does NOT establish

* **It is the namespace envelope, not §5.1's check.** The recovered record
  *octets* are not compared with what the killed process staged: that needs
  `fn-bs-scan-store`, which is K1 and open. What is compared is the record
  count, which is what `fn-sf-crash-imagep` constrains.
* **It enumerates rather than decides.** `fn-bs-image-admissiblep` and
  `fn-bs-image-admissiblep-iff-crash-imagep` (§1.5) are open, so the harness
  enumerates the whole-or-lost choices of the pending list. Torn *selections*
  within a write are not enumerated; §5.2's variant injector is the packet
  that produces them on disk, and it was not written.
* **No known-bad host was run.** §5.5's `FN_CAMPAIGN_UNSAFE=link-before-fsync`
  demonstration -- the campaign-level tooth for K1 -- is not implemented.
  The singleton sets above are an argument that the check constrains, not a
  demonstration that it fails when the host is wrong.
* **Seven pairs, one scenario, `--quick`.** `bp-receive`, `bp-retry`,
  `capacity-refusal` and `sender-enqueue` were not run with this flag, and
  their journal and inbox cuts have model programs now but no `PROGRAM_OF`
  entry, because a journal has no `fn-sf` kernel and the count the check
  compares is the store's.
* **Process death only.** No power-loss claim, on this or any run.
