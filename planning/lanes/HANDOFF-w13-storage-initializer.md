# w13/storage-initializer — current fresh initializer checkpoint

Branch `branchw13/storage-initializer`, baseline `1501492`; commits
`2ee5166` and `20e4353`. Root owns registry, ledger and Makefile-root changes.

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
normalizes that complete successful path to an exact byte representation.
`fn-bsi-current-init-program-establishes-relation` uses it with two separate
contracts: `fn-bsi-fresh-inputp` is the physical input/namespace contract;
`fn-bs-initial-inputp` is the metadata-to-kernel binding. The latter is not
hidden inside the former. The theorem subject runs `fn-bs-run`, the same
interpreter used for the host-program transcriptions; this is still a source
correspondence claim to the Python calls, not a theorem about Python.

`tests/acl2/byte-store-initializer-tests.lisp` has a reached successful image,
a pre-lock failure cut, and both legal outcomes of the config-directory fsync
failure. It also has two `must-fail` values: malformed physical input and a
frontier that decodes to one instead of zero. The config-history fence witness
is non-degenerate: `:drop` leaves generation 1 absent while `:apply` leaves
the exact inode visible.

The exact fresh lock operation is represented by the byte model's fresh
create primitive. The actual host uses `open(O_CREAT)` rather than `O_EXCL`;
this refinement is valid only because `fn-bsi-fresh-inputp` names a fresh
store. Existing writer locks, existing directories/files, EEXIST from an
initial link, and `_safe_directory`/`_publish_initial_file` read-and-validate
branches are explicitly **open**, not treated as retries. General arbitrary
syscall preservation, recovery establishment and retained-history composition
also remain K0 work.

Local ACL2 8.7 evidence:

* `build/acl2/certify-20260921T071459Z-18491` —
  `books/byte-store-initializer` passed.
* `build/acl2/certify-20260921T071523Z-18976` — required concrete metadata
  frame dependency passed.
* `build/acl2/certify-20260921T071546Z-19332` — initializer test book passed.

The first local closure attempt stopped at the pre-existing
`books/byte-store-invariants` inclusion of `arithmetic-5/top` under this local
ACL2 8.7 world; it is not an initializer proof failure. Hbox owned-closure
submission `run-20260921T071619Z-ea97` uses `/tank/fn/lanes/w13-storage-initializer`
with four jobs and must be fetched/recorded before a remote certification
claim. The earlier hbox run `run-20260921T071051Z-2934` was an obsolete
pre-fix snapshot and failed at the then-unproved representation lemma.
