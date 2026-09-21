# w13/storage-initializer — current fresh initializer checkpoint

Branch `branchw13/storage-initializer`, baseline `1501492`; initial packet
commits `2ee5166`, `20e4353`, `943ec1b`, `8820acc`. Root owns registry, ledger
and Makefile-root changes.

`books/byte-store-initializer.lisp` is the current **fresh** host subject,
not a replacement claim about `fn-bs-init-program`. The host anchor is
`tools/run_store.py:980-1024`, called by `Store.initialize`. Its executable
`fn-bsi-current-init-program` contains: `_safe_directory` creation of root,
transactions, staging and config with each parent fsync; fresh writer-lock
creation; config metadata publication; generation-1 configuration-history
publication under `config/`; the required config-directory fence; frontier
publication; and all five final barriers. A named model cut follows every
durable syscall, including helper fences missing from the historical program.

`fn-bsi-current-init-program-establishes-current-image` is the keystone that
normalizes that complete successful path to an exact **whole byte image**; it
is the result that makes the generation-1 config entry durable.
`fn-bsi-current-init-program-establishes-relation` is a narrower kernel
projection: `fn-bs-store-relation` has no `:config` or writer-lock clause.
The test deletes only `(:fsync-dir :config)` and reaches a state where the
old relation still holds while the image equality fails. It uses two separate
contracts: `fn-bsi-fresh-inputp` is the physical input/namespace contract;
`fn-bs-initial-inputp` is the metadata-to-kernel binding. The latter is not
hidden inside the former. The theorem subject runs `fn-bs-run`, the same
interpreter used for the host-program transcriptions; this is still a source
correspondence claim to the Python calls, not a theorem about Python.

`tests/acl2/byte-store-initializer-tests.lisp` has a reached successful image,
a pre-lock failure cut, and both legal outcomes of the config-directory fsync
failure. It also has independent `must-fail` values: a non-string stage name
with a valid metadata binding, and a frontier that decodes to one instead of
zero. Equal fresh stage names are a positive witness. The config-history fence
witness is non-degenerate: `:drop` leaves generation 1 absent while `:apply`
leaves the exact inode visible.

The exact fresh lock operation is represented by the byte model's fresh
create primitive. The actual host uses `open(O_CREAT)` rather than `O_EXCL`;
this refinement is valid only because `fn-bsi-fresh-inputp` names a fresh
store. Existing writer locks, existing directories/files, EEXIST from an
initial link, and `_safe_directory`/`_publish_initial_file` read-and-validate
branches are explicitly **open**, not treated as retries. General arbitrary
syscall preservation, recovery establishment and retained-history composition
also remain K0 work. Configuration-history refinement is separate follow-up
work: strengthening the global relation would require preservation and K1-K4
impact review.

The three publication families have unique model cut names. The checker now
registers `fn-bsi-current-init-program` as `store:initialize`, but its source
reader deliberately does not inline `fn-bsi-publish-steps` or evaluate label
prefixes. Its `limits` report preserves the expected mapping from the current
host fault labels to post-helper/final-barrier cuts; it does **not** claim that
the remaining model cuts are host-injectable. Adding those `faults.at` sites
is host instrumentation for its owner.

Local ACL2 8.7 evidence:

* `build/acl2/certify-20260921T071459Z-18491` —
  `books/byte-store-initializer` passed.
* `build/acl2/certify-20260921T071523Z-18976` — required concrete metadata
  frame dependency passed.
* `build/acl2/certify-20260921T071546Z-19332` — original initializer test book passed.
* `build/acl2/certify-20260921T074553Z-44991` — review repair book and test
  book passed; `python3 tools/transcribe_check.py` exits zero with the named
  initializer helper-inlining limit, four pre-existing advisory drift rows and
  no fidelity defects.

The first local closure attempt stopped at the pre-existing
`books/byte-store-invariants` inclusion of `arithmetic-5/top` under this local
ACL2 8.7 world; it is not an initializer proof failure. Hbox owned closure
`run-20260921T071619Z-ea97` passed with ACL2 8.7 on
`/tank/fn/lanes/w13-storage-initializer`, four jobs, and source/certificate
digests in
`planning/evidence/manifests/certify-20260921T071623Z-1742111.json`. It
certified the full local include closure, including
`books/byte-store-initializer` and its test book. The earlier hbox run
`run-20260921T071051Z-2934` was an obsolete pre-fix snapshot and failed at
the then-unproved representation lemma.
