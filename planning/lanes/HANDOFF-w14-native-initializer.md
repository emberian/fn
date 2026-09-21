# W14 native initializer fidelity handoff

Branch `w14/native-initializer`, commit `98b11a2` (`native: expose fresh
initializer cuts`), is based on native codec source anchor `37ec36b`.

`host/native/io.lisp` now puts the fresh initializer's model labels after each
successful corresponding native syscall: root/child directory creation and
parent fences, fresh lock creation, all three staged publications, the
configuration-history directory fence, and all final barriers.  The subject is
the host call `fnn-command-init` -> `fnn-initialize` -> `fnn-acquire`, not a
sibling model.  `planning/lanes/DESIGN-w14-native-initializer.md` records the
complete source-to-`fn-bsi-current-init-program` map and its scope.

`FN_NATIVE_INIT_FAULT=MODEL-CUT:eio|kill` is a developer-only environment seam,
not command-line/operator configuration.  `kill` sends SIGKILL after the named
call returned; `tests/test_native_initializer_fidelity.py` restarts using a new
native process.  The test includes a normal fresh init/recover, post-history
fence EIO routing, real SIGKILL at the history fence and lock cut, and the
second configuration-directory enumeration fault.  The static test proves the
full model-label table is attached to the actual helper calls.

The same packet fixes a real error/empty conflation: `fnn-config-record-names`
no longer catches every `fnn-os-error` as NIL.  A non-model test control before
the final enumeration demonstrates that init faults instead of continuing as
though history were absent.  This does not claim that an injected post-call EIO
models all platform EIO outcomes; the published staging content was already
file-fenced before its link.

Validation on this isolated source:

* SBCL reader with `sb-posix` and `sb-bsd-sockets`: `reader-ok forms=219`.
* `python3 -m unittest tests.test_native_initializer_fidelity`: source-map
  test passed; five runtime tests skipped because no `build/fn-host` exists.
* `git diff --check` passed.
* `tools/build_native_host.sh` stopped before raw host loading because the
  `37ec36b` worktree has no certificates for the native image closure
  (`books/replay` and dependent books are uncertified).  It is an environment
  closure limitation, not a claimed native-image result.  No ACL2 book changed,
  so there is no owned certification root in this packet.

Open: existing directories/lock/files and EEXIST/load branches; physical crash
outcome qualification; K0; and the reported frozen-image missing-`staging/`
restart divergence, whose current source path should fault and needs a separate
source/image reproduction.  No fresh exact-image or general relation theorem
was added or strengthened.
