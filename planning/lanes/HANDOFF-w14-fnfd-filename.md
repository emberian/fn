# Handoff: W14 FNFD peer filename codec

`books/feed-filename.lisp` is the sole filename codec.  Its public direction
functions are `fn-feed-filename-components` and
`fn-feed-filename-from-components`; the latter accepts only a component vector
whose exact canonical re-encoding matches.  Safe legacy peer names retain the
flat `feed/<name>.fnfd` path.  Every other accepted peer name uses the disjoint
`feed/v1/<lowercase-hex chunks>/journal.fnfd` namespace.

`host/feed-filename-host.lisp` exposes the ACL2 codec to both host adapters.
`host/native/feed-filename.lisp` calls those wrappers for component output and
inverse recovery; `host/native/owner.lisp` uses it in the live FNFD open and
recovery paths.  `tools/run_owner.py` uses the same wrappers through
`discover_journal_peers`, and does not derive a peer from a pathname itself.
Malformed, duplicate, symlink, unsafe, or unrecognized retained entries fault
without removal.  An empty `feed/v1` tree also faults and remains preserved:
this is the explicit recovery behavior for a process death after nested
directory creation but before a journal leaf exists.  It does not establish a
general physical crash-correspondence claim.

The bounded closure was certified on `hbox` with ACL2 8.7 (saved executable
SHA-256 `64030dda0b03bbb6cf50984889f5ce1e2ba867b6ce3c9a65403afc44f9b4fdb5`):

```
python3 tools/farm.py submit hbox --jobs 4 --remote-root /tank/fn/lanes/w14-fnfd-testfix --closure books/feed-filename tests/acl2/feed-filename-tests
python3 tools/farm.py wait hbox run-20260921T091829Z-f70d --wait-seconds 5 --poll-seconds 5
```

The archived [manifest](../../build/acl2/certify-20260921T091837Z-1933013/manifest.json)
records both requested roots as passed.  It pins
`books/feed-filename.lisp` to SHA-256
`43fbd566ac3ec4b3cd6dbf825959f5015de317ad4ead233742dcad9d74c4d43f` and
`tests/acl2/feed-filename-tests.lisp` to SHA-256
`14544f89b1836bd433b199ace52a53d849609a1de6332b47bb7f31b08e585460`.
The native source is wired, but this lane has not built or runtime-tested a
fresh native image; that remains for the root-coordinated frozen batch.

## Recovery observation successor

`fn-feed-filename-observation-limit` and
`fn-feed-filename-observation-remaining` now own one 8192-name observation
budget for the complete FNFD recovery walk. It is independent of configured
peer rows because a configuration delta's row cap is not a retained-peer cap,
and journals for removed peers remain recovery obligations. The raw host calls
`fnn-list-directory-bounded` with the ACL2-produced remaining count, then
returns the actual retained count to ACL2 before visiting another directory.
It faults without removal on excess or conflicting evidence. The test-only
four-name policy in `tests/native_fnfd_budget.lisp` exercises the production
raw traversal through sibling v1 directories: one sibling drains the shared
counter and the other faults before its leaf is retained.

`hbox` farm closure `run-20260921T094123Z-d7ff` passed
`books/feed-filename` and `tests/acl2/feed-filename-tests` with ACL2 8.7. Its
[manifest](../../build/acl2/certify-20260921T094207Z-1976097/manifest.json)
pins the changed book to SHA-256
`a6c3d19f6f1aa9d1d85fe95cd79b9836b2ca2e9991960a0f17ab7b870a05fdbc`
and its test root to SHA-256
`96a86a25762dfe47b215e72a03f3fd47d71eb932d7a333aac0dc9bb493e232d5`.
