# Verdict: 8da8217 across every gate

One commit through the box gate (`make certify`, the Python suite,
`tools/gate_publish.sh`), then every harness this tree has, then this
table.  Produced by `tools/verdict.py`; the per-harness evidence files
cited below are the primary records and this one adds nothing to them.

## What ran

| fact | value |
| --- | --- |
| commit | `8da8217` (8da8217da9bdaa3501d66cf3ff0faf3672951cf3) |
| gate host | `hbox` |
| INN host | `hbox` |
| started | 2026-09-20T21:07:52Z |
| wall time | 29 s (0.0 h) |
| gate directory | `/tank/fn/gates/dev-d50c392` |
| gate lock | `/tank/fn/gates/.lock` (the one lock this box's gates take) |
| gate reused | yes |
| gate artefacts absent | none |
| certify manifest | `build/acl2/certify-20260920T180307Z-1008010/manifest.json` |
| manifest status | failed |
| per-root verdict from | `book_results` |
| acl2 | ACL2 Version 8.7 |
| platform | Linux-6.11.0-29-generic-x86_64-with-glibc2.40 |
| certify wall | 1227.03 s at 12 jobs |
| certificates written | 223 |
| python suite | FAILED of 444 tests, failures=14 errors=74 skipped=7 |

## Fibers

| fiber | host | tool | state | rc | steps | failed | not run | s | evidence |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| gate | `hbox` | `make certify + unittest + gate_publish.sh` | fail | 1 | 238 | 15 | 0 | 11 | - |
| deploy | `hbox` | `tools/deploy_gate.py` | not run | - | - | 0 | 0 | 0 | - |
| twonode | `hbox` | `tools/twonode_gate.py` | not run | - | - | 0 | 0 | 0 | - |
| inn | `hbox` | `tools/inn_lab.py` | not run | - | - | 0 | 0 | 0 | - |
| scale | `hbox` | `tools/scale_gate.py` | not run | - | - | 0 | 0 | 0 | - |

Per fiber, in its own words:

- **gate** (fail): roots 223/238 certified, suite FAILED of 444 (f=14 e=74), certify rc=2 suite rc=1 publish rc=0
  - books/checkpoint-codec (store)
  - books/checkpoint-publish (store)
  - books/ideal (nntp)
  - books/owner (nntp)
  - books/owner-invariants (nntp)
  - books/peer-config (nntp)
  - books/peer-inbound (nntp)
  - books/peer-inbound-invariants (nntp)
  - books/served (nntp)
  - tests/acl2/checkpoint-codec-tests (store)
  - tests/acl2/checkpoint-publish-tests (store)
  - tests/acl2/nntp-reader-profile-tests (nntp)
  - tests/acl2/owner-tests (nntp)
  - tests/acl2/peer-inbound-tests (nntp)
  - tests/acl2/served-tests (nntp)
- **deploy** (not run): skipped by --skip/--only
- **twonode** (not run): skipped by --skip/--only
- **inn** (not run): skipped by --skip/--only
- **scale** (not run): skipped by --skip/--only

## Certify roots by owner

| owner | roots failing | which |
| --- | --- | --- |
| nntp | 11 | `books/ideal`, `books/owner`, `books/owner-invariants`, `books/peer-config`, `books/peer-inbound`, `books/peer-inbound-invariants`, `books/served`, `tests/acl2/nntp-reader-profile-tests`, `tests/acl2/owner-tests`, `tests/acl2/peer-inbound-tests`, `tests/acl2/served-tests` |
| store | 4 | `books/checkpoint-codec`, `books/checkpoint-publish`, `tests/acl2/checkpoint-codec-tests`, `tests/acl2/checkpoint-publish-tests` |

Owners are the rows of `planning/deputies/CLUSTERS.md`, matched by
book-name prefix in `tools/verdict.py`; a root matching no row is
reported as `unassigned` rather than silently dropped.

Manifest failure line: `ACL2 did not produce complete clean certification evidence. See certify.log. Books that failed: books/checkpoint-codec, tests/acl2/checkpoint-codec-tests, books/checkpoint-publish, tests/acl2/checkpoint-publish-tests, books/peer-config, books/peer-inbound, books/peer-inbound-invariants, tests/acl2/peer-inbound-tests, books/served, tests/acl2/served-tests, books/owner, books/owner-invariants, tests/acl2/owner-tests, books/ideal, tests/acl2/nntp-reader-profile-tests`

## Python suite: the failing and erroring cases

```
FAIL: test_the_record_states_what_it_does_not_show (test_four_node_lab.FourNodeLabTests.test_the_record_states_what_it_does_not_show)
FAIL: test_inbound_directory_barrier_after_link_fences_and_reopens (test_workflow_faults.WorkflowFaultTests.test_inbound_directory_barrier_after_link_fences_and_reopens)
FAIL: test_process_restart_rediscovers_inbox_linked_before_directory_barrier (test_workflow_faults.WorkflowFaultTests.test_process_restart_rediscovers_inbox_linked_before_directory_barrier)
FAIL: test_restart_rediscovers_the_exact_durable_inbox_frame (test_workflow_faults.WorkflowFaultTests.test_restart_rediscovers_the_exact_durable_inbox_frame)
```

## What this run does NOT establish

- A certificate records that ACL2 read a book and admitted its events.
  It is not a claim that the theorem in that book is the property its
  name suggests, nor that the host calls the function it is about.
- The harness rows are live runs against real sockets and real kill
  signals. None of them is an RFC conformance audit, none qualifies
  storage hardware, and a SIGKILL is not a power loss.
- Fibers marked `not run` establish nothing at all; they are in the
  table so their absence is visible in the claim.
- This file is generated. Its numbers come from the gate manifest and
  from each harness's own stdout summary, never from typing.
- A reused gate is a reading of a directory that was already there.
  This run did not certify it, did not ship the commit that made it,
  and cannot say the tree beside those logs is the commit named above
  beyond the gate directory's own name.

## The claim

On this commit 223 of 238 Makefile roots certified under ACL2 8.7 and the Python suite ran 444 tests (FAILED); it claims nothing about anything in the 15 roots that did not certify (nntp, store), nor whatever the 14 suite failures and 74 errors cover, nor the steps the gate harness reported failing, nor anything deploy or twonode or inn or scale would have shown, which did not run.
