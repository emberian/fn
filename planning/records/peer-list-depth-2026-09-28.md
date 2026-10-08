# peer-list-depth, 2026-09-28 (PRF-383)

## The defect
batch AZ, tests/test_native_peer_rows_growth.py: after 1,100 accepted
`peer carries far HEX` requests (1,164 config generations), `operator peer
list` exited 4 with "INFO: Control stack guard page unprotected" at the
deployed 1,024 KiB control stack.

The path (host/native/admin.lisp fnn-admin-query ->
host/native-admin-host.lisp fn-native-admin-host-query-report ->
books/native-admin.lisp fn-native-admin-query-report ->
books/native-admin-peer-budget.lisp fn-native-admin-peer-budget-report)
had these non-tail recursions over data that grows with the requests:

| function | walks | depth at 1,100 principals |
|---|---|---|
| fn-napb-before-last | the rendered line's octets | ~90,000 (82 octets per principal): the overflow |
| fn-native-admin-peer-slot-values | the peer's rows | ~1,100 |
| fn-native-admin-peer-list-octets | the carried values | ~1,100 |
| fn-cfg-rows-with-key (via fn-cfg-peer-find, twice per peer) | the whole peer table | ~1,100 |
| fn-cfg-peer-names | the whole peer table | ~1,100 |
| fn-native-admin-peer-budget-report-rows | peer names | peers |

The same report serves books/native-live-status.lisp fn-nls-report (:peers),
the live owner's status. `control list` (fn-native-admin-control-report) and
the open's configuration-history observation (books/native-config-observation.lisp
fn-nco-decode-entries, -insert-by-generation, -sort-by-generation,
-output-entries; depth = generations, operator-set max-config-generations)
are the same class and were fixed with it.

## The fix
Loop twins, PRF-362's pattern: (mbe :logic <the recursion, unchanged> :exec
<loop>), guard-verified through a local rev-onto lemma. config.lisp and
peer-config.lisp are wide (743 and 520 dependents), so fn-cfg-rows-with-key
and fn-cfg-peer-names are not edited: the report's :exec calls
fn-napb-rows-with-key-loop / fn-napb-peer-names-loop, equal to them by
fn-napb-rows-with-key-loop-is-rev-onto / fn-napb-peer-names-loop-is-rev-onto
(non-local, cited by PRF-383). The two originals stay under "debt" for their
other callers: a candidate for the next wide-book slot on config.lisp.

Test: tests/acl2/native-admin-peer-budget-tests.lisp renders a 1,200-principal
row group and compares with a line built independently in the test.

## Why depth_check missed it
Not the closure: fn-napb-before-last was on it and was FOUND. The baseline
classified it "bounded" with "Walks one rendered 'peer list' line for one
peer; bounded peer-config-row rendering, not traffic", and the check
accepted any reason of 8 or more characters. The tool's own docstring
listed "an operator's configuration table" as an acceptable bound. Under
D27 a configuration table is data with no fixed cap (PRF-171 lifted the
peer row cap), so 128 "bounded" entries were really unbounded walks.

Fix (tools/depth_check.py check): a "bounded" reason must name its bound:
a `*constant*` the tree defines by defconst (checked against books/ and
host/), a number, or a structural bound (decimal digits / log n, fixed
width or shape, car-nesting, height). Otherwise it fails with a message
that says operator data is not a bound. Regression tests in
tests/test_depth_check.py, including fn-napb-before-last's old reason.

Re-run over the host-called closure (hbox, 1,239 roots, 9,603 functions):
377 non-tail recursions, 184 bounded, 193 debt, 0 problems. 9 entries fixed
above left the baseline; 116 moved to "debt" prefixed "D27:"; 3 argv walks
now cite *fn-native-admin-max-arguments*.

## Not covered
- Raw host code (host/native/*.lisp) is not linted at all; the peer-list
  path's raw code has no recursion, but the class is open.
- Scope is control-stack depth only; the report still scans the peer table
  once per peer (time unchanged; measure at convergence).

## Evidence
- certify: persvati run-20260928T175537Z-12ce, 62 books passed,
  planning/evidence/manifests/certify-20260928T175634Z-806289.json.
- natives: hbox native-pld1 (developer + production images at 2be74b691):
  test_native_peer_rows_growth, test_native_operator_verbs, test_native_control
  (result recorded in the lane report).
