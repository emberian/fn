# Isolated local ACL2(p) Arithmetic-5 probe — 2026-09-21

The Homebrew serial ACL2 8.7 executable on `nextop.local` cannot include the
installed `arithmetic-5/top`: its `deftheory-static` certificate names
`(:TYPE-PRESCRIPTION INCREMENT-TIMER@PAR)`, which is absent from the serial
world.  This was reproduced in a fresh process before any fn book was loaded
(`/tmp/fn-arithmetic-system-probe.log`).  It is an installed system-book/core
mismatch, not an fn proof result.

The installed parallel saved core has the matching world.  A fresh invocation
of the exact wrapper below included `arithmetic-5/top` successfully, and the
bounded affected-book probe passed:

```sh
FN_ACL2=/opt/homebrew/Cellar/acl2/8.7_6/libexec/saved_acl2p \
  python3 tools/certify_books.py --jobs 1 --timeout-seconds 180 \
  --no-publish books/byte-store-invariants
```

The result is [certify-20260921T104259Z-8701 manifest](manifests/certify-20260921T104259Z-8701.json): `books/byte-store-invariants` passed in 4.005 s
on source revision `00bb04db3fa02f13fc5d0099fa6eb42bea4365b9` (the manifest
records that this operator worktree also had uncommitted changes outside the
probed source closure).  It used ACL2 8.7, SBCL 2.6.8, one of the normal
machine-wide four ACL2 slots, and the tool's `--no-publish` mode.

Tool identity is explicit: `saved_acl2p` wrapper SHA-256
`c0a0dfbde5e111168673e845a6daa8d019236b14123e39e4a8548d9f592e56b9`,
its core SHA-256
`1a10a30ecb9284030dbbc1854491231a8413afd0018c86a439950319c602c0f3`,
and the installed Arithmetic-5 `top.lisp`/`top.cert` SHA-256 values are
`c40efd8ff7f2429ef58e4d2f9681fd7898305f559f4652535744f0c230f90575` /
`fbdf8c40ce3743a44b7525eeb73375e404cc5c891f89e8993b07b3386951dca3`.
This is the ACL2(p) profile; the serial wrapper/core were not modified.

This probe authorizes neither a serial saved-image build nor a deployment
claim.  Keep every local ACL2(p) run source-pinned and `--no-publish`, do not
copy its certificates into a serial image or shared default cache, and retain
the remote serial gate as the deployment authority.  No broad closure was run.
