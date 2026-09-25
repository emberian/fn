# Python twins retired; 437 names its reason (2026-09-25)

Lane `lane/python-twins` from dev `3a1dcb34`. Audit packet 6
(planning/audit-2026-09-25-twins-fanin.md §1d) and control-c1 finding 2.

## The eight decisions tools/run_store.py owned

| # | Python twin | Now | Why |
|---|---|---|---|
| 1 | `peer_listing` renders each field | ACL2: `fn-store-cfg-peer-report` (host/store-node-host.lisp) returns `fn-native-admin-peer-report` over the replayed configuration, the line the native `peer list` prints (D23 words included). `fn-store-cfg-peer-slot-text/-nat` and `peer_names/peer_slot_*` deleted. | the native renderer exists; the Python one had already diverged |
| 2 | `config_record_path` `"{:08d}.cfg"` | ACL2: `fn-native-admin-config-name` through `fn-store-cfg-record-name` (init, owner-allocated writes) and through the publication authorization (CLI writes) | naming |
| 3 | `generation = config_generation + 1` (group, capacity, peer, policy) | ACL2: `Store.publish_config_record` asks `fn-store-cfg-publication` = `fn-native-admin-publication-authorize` (generation, name, lock, occupied name, candidate reopen). The Python second-core `_candidate_history_opens` is deleted; ACL2's candidate predicate now gates every configuration record, not only capacity. run_owner.py's RECONFIGURE keeps the owner core's generation and ACL2's name. | allocation; the native host's path |
| 4 | transaction bound (`len(files) >= max`, `records_count >= max`) | ACL2: `transaction_files` passes the bounded readdir (stopped one past the profile bound: a work bound) to `fn-store-txn-observation-selected`; `post_article`, run_bp_receive and run_bp_ingress ask `fn-store-sn-publication-verdict` (`fn-sbud-verdict`), as the native `store post` does | bounds |
| 5 | `SEQ_NAME` regex | deleted: the grammar is the observation's; `transaction_name` applies only the path-component guard (`frame_bridge.path_component`) | naming |
| 6 | profile constants (`MAX_TRANSACTION_COUNT`, `STORE_EVENT_RECORD_BYTES`, `DEFAULT/SCALE/LEGACY_*_CONFIG`) | deleted; `profile_config(name)` asks ACL2 to frame and decode a named profile. Benches and probes re-pointed. `command_post`'s read bound is ACL2's `max_store` constant (a work bound). | bounds |
| 7 | `validate_post_boundary` verdict-to-text table | deleted; the refusal relays ACL2's verdict word (`ACL2 refused the post boundary: payload-bound`) | rendering |
| 8 | `metadata`'s third value `b"unsigned-legacy-v0"` | NOT CLOSED. The POST path already takes `fn-store-prov-post`; the two BP drivers still read the label. Closing it means building `fn-prov-make-bp` evidence in the BP drivers, which changes the stored evidence bytes of every BP acceptance; left for the provenance owner (open item, unchanged). | |

`fn-store-post-boundary` (host/store-host.lisp) is deleted. The audit said
only the Python bridge called it; host/native/io.lisp `fnn-post-boundary`
called it too. Both now call `fn-sbud-post-boundary`.

Tests that existed only to lower `DEFAULT_CONFIG["max_transactions"]`
(test_media quota, test_bp_receive_faults bound, campaign capacity-refusal,
campaign child `--max-transactions`) now stand in the verdict seam
`run_store.publication_admissible` (ACL2's verdict replaced by one refusing
after N admissions); the bound itself is ACL2's. No test was deleted:
none existed only for a twin.

## 437 carries its reason

- `books/nntp-post.lisp` `fn-post-store-refusal-text`: the one reason table;
  `fn-post-store-refusal-line` = `"441 posting failed; "` + text.
- `books/peer-inbound.lisp` `fn-peer-transit-refusal-line`: `"437 transfer
  rejected; "` + the same text for a Store refusal word; bare `:refused`
  keeps `refused by acceptance`. `fn-peer-transit-code` and the IHAVE
  effects treat every `fn-post-store-refusalp` word as the refusal (code
  class unchanged, 437/439; TAKETHIS's 439 echoes the Message-ID only).
- `books/owner.lisp` `fn-own-transit-outcome` renders with
  `fn-own-outcome-rendering` (as `fn-own-outcome` does for POST); which
  outcome it is stays the completion's.
- host/native/owner.lisp `fnn-owner-transit-complete` feeds
  `fn-owner-transit-outcome` the word `fn-owner-served-carried-word` gives
  (`fn-pa-served-word` over the attempt word and the ingress detail), as
  `fnn-owner-attempt-served` does. The log line keeps word and detail.
- Keystone `fn-osp-transit-refusal-renders-its-reason`
  (books/owner-signed-post.lisp): for a relayed reason, `:want`, an IHAVE
  transit in flight on this connection and no completion consumed, the
  reply is `fn-peer-single` of `"437 transfer rejected; "` +
  `fn-post-store-refusal-text detail`; Store, ledger, feeds unchanged.
  Registered under PRF-026 (planning/proof-events.json).
- Teeth (tests/acl2/owner-signed-post-tests.lisp): witness on `*ospt-taken*`
  with an IHAVE transit in flight on the poster's connection (constructed
  the way owner-tests builds `own-fed-transit-on-connection`, not reached
  through a peer connection), for `:control-not-filed` and
  `:local-enrollment`, plus the wire octets; must-fail per hypothesis: word
  not relayed, other connection, POST in flight, TAKETHIS, `:refuse`,
  completion consumed, connection gone. peer-inbound-tests pins the new
  lines.
- INN lab and campaigns: nothing pinned `refused by acceptance`
  (tools/inn_lab.py, tests/campaign/*, tests/inn_lab_fake pin decision
  lines only, which are unchanged). No native run of the new line.

## Runs

- persvati `run-20260925T041110Z-70e3`, manifest
  `planning/evidence/manifests/certify-20260925T041232Z-243596.json`:
  ACL2 8.7, `/home/ember/fn-gates/toolchains/w25/acl2-literal`, 2 jobs,
  timeout 300 s, incremental from `/home/ember/fn-certcache`, source
  `4e3b2939`; 195 roots (the `--affected-by books/nntp-post` set, 194, plus
  tests/acl2/provenance-tests, which lds host/store-host.lisp), 199 books
  certified, 0 failures, 505.3 s. A first submission with `--affected-by`
  plus an explicit root certified nothing ("No requested book is affected");
  the explicit-roots resubmission is the run.
- provenance-tests was the one root "already certified at these bytes": the
  cache key does not cover the host file it lds.
- Python, laptop, ACL2 8.7 through tools/acl2: `tests.test_store_config`
  6/6 (after one expectation fix: ACL2 prints an absent direction as `-`).
  Other modules: see LANEDUMP.
- `make check`: only the ledger staleness errors (ledger.json/.md,
  proofs.json events), which this lane does not regenerate.

## Findings

1. The native host keeps its own verdict-to-text table
   (host/native/io.lisp `fnn-validate-post-boundary`): the same twin in host
   Lisp. Not changed here.
2. `fn-own-transit-outcome` previously collapsed every refusal word to
   `:refused`; `fn-olog-transit-code` still reads the completion, which
   gives the same code.
