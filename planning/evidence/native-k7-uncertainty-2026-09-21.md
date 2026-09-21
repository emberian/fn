# Native publication uncertainty at byte-model K7

This packet relates the native publication observations to the byte crash
model at the four uncertainty boundaries used by the host: record link,
allocator rename, transaction-directory barrier, and root-directory barrier.
The actual native call chain is `fnn-owner-attempt` to
`fnn-advance-frontier`, `fnn-publish`, and `fnn-finish`; observations enter
the composed ACL2 machine through `fn-sn-io`.  The bridge theorem
`fn-bs-native-io-is-byte-observation` equates that called subject's file
projection with `fn-sf-dispatch` for the corresponding byte-program event.

The K7 candidate keystones are:

- `fn-bs-issued-record-link-error-needs-recovery-fence`
- `fn-bs-issued-frontier-rename-error-needs-recovery-fence`
- `fn-bs-record-directory-error-resolves-choice-and-fences`
- `fn-bs-frontier-directory-error-resolves-choice-and-fences`

The exact composed-subject companions are
`fn-bs-native-record-link-error-fences-composed-subject`,
`fn-bs-native-frontier-rename-error-fences-composed-subject`,
`fn-bs-native-record-directory-error-fences-composed-subject`, and
`fn-bs-native-frontier-directory-error-fences-composed-subject`.
`tests/acl2/byte-store-fault-keystones-tests.lisp` supplies reachable
frontier and record witnesses and a violating case for each physical premise
or selected authority directory.

## Certification

| fact | value |
| --- | --- |
| command | `python3 tools/certify_books.py --jobs 2 books/byte-store-fault-keystones tests/acl2/byte-store-fault-keystones-tests` |
| result | both requested roots passed |
| evidence | `planning/evidence/manifests/certify-20260921T163427Z-46060.json` |
| tool versions and source digests | recorded in that generated manifest |

This proves logical behavior of the byte syscall transitions and the exact
ACL2 observation function called by the native adapter.  It does not qualify
a filesystem or hardware power-loss profile.  The developer-only SIGKILL
scenario that imports exact frontier and transaction inode octets into
`fn-bs-scan-store` and `fn-sn-open-observed` is implemented but awaits the
next frozen native developer image; it is not evidence in this certification.
K5, K6, K8, general K0 preservation, and physical every-cut correspondence
remain open.
