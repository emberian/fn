# T3: the live Store owns the existing Message-ID decision

Source: branch `implement/store-semantics`, commits `8f6a7032` and
`7acaa919` from `b1a77f02`, plus the shared acceptance-stamp caller fix
cherry-picked as `932b1cb5` from `37e1a5f0`. The certification manifests
record exact source digests and toolchain identity.

`fn-sn-existing-action` in `books/store-node.lisp` reads the actual live
article map from `(fn-sn-node s)`. The four host sites call that function:
`host/store-node-host.lisp:460` (prepare) and `:581` (existing-action query),
and `host/owner-host.lisp:304` (prepare) and `:989` (query). The former
`fn-store-article-match` in `host/store-host.lisp` is deleted. Host code
continues to validate bounded octets and translate group codes before the
call; neither host wrapper compares the held article.

`books/store-node-existing-invariants.lisp` certifies that the called function
answers `:duplicate` exactly for a held Message-ID with equal payload octets
and ordered groups, `:conflict` exactly for a held Message-ID where either
differs, and `nil` exactly for no held Message-ID. These are direct case
properties of the called decision, not keystones for the broader allocation
or durability claims; their event names end in `-by-definition` for that
reason. `tests/acl2/store-node-existing-tests.lisp` creates a
reachable committed two-group article, then exercises each outcome and a
`must-fail` for changing payload alone, groups alone and binding alone.

On persvati, `python3 tools/farm.py submit persvati --affected-by
books/store-node --affected-by books/store-node-existing-invariants --jobs 2
--timeout-seconds 1800 --remote-root /home/ember/fn-gates/t3-store-semantics
--acl2 /home/ember/fn-gates/toolchains/w25/acl2-literal --cache
/home/ember/fn-certcache` produced run `run-20260923T164911Z-b953`:
[manifest](manifests/certify-20260923T164920Z-1846190.json), passed with
93 selected roots and no failures in 152.189 seconds. The toolchain was ACL2
8.7 on SBCL 2.6.8, identity
`1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`.
`python3 tools/green_check.py --changed-since b1a77f02 --summary --strict`
reports three changed books, 90 dependent books, zero not green. The first
focused run failed only because the new test named an invariant-book helper
without including that book; the corrected test passed in
[run `run-20260923T164830Z-876e`](manifests/certify-20260923T164832Z-1839702.json).
After the three direct case events were renamed `-by-definition`, a selected
two-root certification of the changed proof book and its test passed in
[run `run-20260923T165541Z-e9f4`](manifests/certify-20260923T165544Z-1904575.json).
The prior affected-root manifest covers the unchanged Store definition and
dependent books; the selected run covers the final theorem/test bytes.

`make check` reached the expected stale generated `planning/ledger.json` and
`planning/ledger.md` files; root generates the ledger during integration.
The local interpreted Store regression did not reach its test body: invoked
as `FN_ACL2=./tools/acl2 python3 -m unittest discover -s tests -p
test_store.py -k duplicate`, both cases timed out while `Acl2Store` waited
for the initial ACL2 prompt in `setUp`. This was a launcher configuration
error: `tools/acl2` itself reads `FN_ACL2` for its child executable, so the
setting made the wrapper recurse. It supplies no semantic runtime evidence.
Native combined-image duplicate behavior remains for the integrated gate.
