# Local ACL2 system-book incompatibility

On 2026-09-21, root reproduced the native-admin and transaction-scan lanes'
dependency failure in a fresh ACL2 session with no fn books loaded:

```
/opt/homebrew/bin/acl2 < /tmp/fn-arithmetic-system-probe.lsp
```

The input was exactly:

```lisp
(in-package "ACL2")
(include-book "arithmetic-5/top" :dir :system)
(value-triple :fn-arithmetic-probe-end)
(good-bye)
```

ACL2 8.7 on SBCL 2.6.8 reports that `ARITHMETIC-5-CURRENT-BASE` contains
the unknown rune `(:TYPE-PRESCRIPTION INCREMENT-TIMER@PAR)` and rejects
the include as incompatible with its current world. The process exits zero
and evaluates the later marker despite that failure; neither proves success.
This reproduces the reported dependency defect without any project source.
It does not establish whether every other installed system book is compatible.

SHA-256 identities:

- `/opt/homebrew/Cellar/acl2/8.7_6/libexec/saved_acl2`: `affe37c4d9d34a5bdd17f65f991ccb2e08f99ede70e51cdde2fc7aac087ba947`
- Its `books/arithmetic-5/top.cert`: `fbdf8c40ce3743a44b7525eeb73375e404cc5c891f89e8993b07b3386951dca3`
- Captured probe output: `03bd2452bab08e36a0622505d63aeb2402020cd54d55f5fe5f32785e32a63396`

Affected lanes continue through owned remote certification closures. An isolated
local remedy is being investigated; the shared Homebrew books are not being
modified underneath concurrent jobs. Earlier source-pinned evidence retains
its recorded scope; this failure alone does not reclassify those results.
