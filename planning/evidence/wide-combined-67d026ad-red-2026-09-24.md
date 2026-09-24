# Frozen 67d026ad combined proof gate: failed

The clean source `67d026ada4ce8b1b959f97d54585340f680d92c3` was submitted
once to hbox at `/tank/fn/gates/wide-combined-67d026ad-20260924` as
`run-20260924T045402Z-31bd`. Root's `make check` completed with exit 0 before
submission. The command used the default Makefile roots (default, DTN and
ACL2 tests), four jobs, the shared `/tank/fn/certcache`, and
`/tank/fn/toolchains/w28/acl2-literal-4g`; it did not request `--closure`:

```sh
python3 tools/farm.py submit hbox --jobs 4 --timeout-seconds 600 \
  --cache /tank/fn/certcache \
  --acl2 /tank/fn/toolchains/w28/acl2-literal-4g \
  --remote-root /tank/fn/gates/wide-combined-67d026ad-20260924
```

The 600-second per-book setting was longer than the agreed 300-second
diagnostic bound. Live `.active.json` files and streamed logs were monitored;
no book exceeded 100 seconds, so no child needed bounded termination. The
manifest records 612 requested roots, 352 cached book certificates installed,
274 new certification attempts, and 273 clean book results. It is **failed**:
four direct theorem failures caused seven missing-certificate dependents.
Certification wall time was 379.439 seconds; submission and transport are
additional. The toolchain identity is
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`.
The unmodified manifest is
`planning/evidence/manifests/certify-20260924T045427Z-915676.json`, SHA-256
`8714972130e977a99de5de7a581c11c6f4df3135ca0dbcf610e74df56a8a4939`.

The four direct failures, with raw hbox logs under
`build/acl2/certify-20260924T045427Z-915676/`, are:

| Book log | First failed theorem |
| --- | --- |
| `books--acceptance-stamp-invariants.certify.log` | `FN-STAMP-COMPOSITE-FINISH-NODE-IS-REPLAY` |
| `books--bp-receiver-evolving-store-invariants.certify.log` | `FN-BPRV-OBSERVED-REOPEN-FACTS` (subgoal 257.8') |
| `books--byte-store-keystones.certify.log` | `FN-BS-CRASH-IMAGE-REOPENS` (subgoal 2) |
| `books--store-prepare-correspondence.certify.log` | `FN-SPC-SET-KEYRING-KEEPS-STORE-COMPONENTS` |

`books/owner-prepare-correspondence` failed because the failed
`store-prepare-correspondence` certificate was absent. The acceptance-stamp,
BP receiver, byte-store scan/sweep, owner-prepare and store-prepare ACL2 test
books then lacked their corresponding book certificates; these are not
independent passing or failing test verdicts. The exact remote log directory
remains in the gate. The run's per-book results and source digests are in the
manifest. No production/developer image was built and no native topic, consumer,
BP or checkpoint test was run from this failed source. `/tank/fn/node` was not
changed.
