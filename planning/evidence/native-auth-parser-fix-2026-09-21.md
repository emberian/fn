# Native AUTHINFO parser correction evidence — 2026-09-21

Source revision `dfdcabc4da254770d6c08002e945bf24103b37cf` excludes quote and
backslash from the canonical login-name predicate and counts conventional
newline-terminated text lines at the documented 1,024-line ceiling.  Its three
affected files are byte-identical at landed main revision
`593ab3ad`.  The ACL2 test book exercises both malformed table-name octets and
acceptance at 1,024 lines versus refusal at 1,025 lines.

The clean source-pinned command was:

```sh
FN_ACL2=/opt/homebrew/bin/acl2 FN_ACL2_TIMEOUT_SECONDS=1800 \
  python3 tools/certify_books.py --jobs 1 \
  books/native-auth-profile tests/acl2/native-auth-profile-tests
```

It passed both requested roots as
`certify-20260921T104530Z-10362` with ACL2 8.7 on SBCL 2.6.8.  The run began
at 2026-09-21T10:45:30Z, ended at 10:45:39Z, and recorded 6.725 seconds.  The
manifest records a clean Git tree, parser SHA-256
`9871be9af9129d8251a450b5e376df0415e64d5cada600894fa9f4181379026e`,
and test SHA-256
`5607120d216501c1cde39c47b3aa63d6afe05de55ec73c4fc61f1ef94811805c`.

This evidence covers only the ACL2 parser and its executable boundary cases.
No host caller changed, so the native image and service runtime were not
rebuilt or rerun.  `fn-native-auth-load-accepted-pins-policy` remains an
unregistered local projection lemma, not host-installation correspondence.

The source-pinned manifest is
[`certify-20260921T104530Z-10362.json`](manifests/certify-20260921T104530Z-10362.json).
