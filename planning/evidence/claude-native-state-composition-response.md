# Disposition: native journal lifetime and retained history

The [independent Claude review](claude-native-state-composition-review.md)
inspected `622df08` in the requested interactive tmux. It found no reachable
standalone handler using the wrong Store image. Its structural warning matters
for the pending owner callback: the owner stores state in `fn-owner`, while the
standalone journal wrappers read `fn-store-sn`. A raw Store struct and a held
lock do not establish those logical images agree. The callback must take its
node from the actual owner with an explicit binding contract. A raw epoch
counter alone is not that correspondence proof.

The avoidable retained-history copy is real: the raw adapter appended each
record to a list only used for initialization checks. The repair removes the
slot and reads the already-carried ACL2 `fn-aj-initializedp` frontier instead.
It does not add a second host count or initialization policy. Recovery still
reads and validates the journal once. A reinitialization regression preserves
existing bytes and outstanding work; its integrated-image run remains pending.
The review is source inspection, not throughput or whole-program assurance.

## Repair validation

Repair source: `d5a2532`. `python3 -m py_compile tests/test_native_app_journal.py`
passed. ACL2 8.7_6 loaded the actual raw I/O then workflow files in the build
order and printed `FN_APP_RAW_LOAD_OK`; no whole-image or runtime test follows
from this load check. The standalone `host_check.py host/native/workflow.lisp`
failed because it omits the preceding I/O module that defines
`fnn-register-verb`; that failure is retained as a tool-scope limitation, not
reported as a passing isolated load. The integrated regression remains pending.

Raw load input, passed to `/opt/homebrew/bin/acl2` from the repository root:

```lisp
(in-package "ACL2")
(defttag :fn-native-host)
(progn! (set-raw-mode t)
        (load "host/native/io.lisp")
        (load "host/native/workflow.lisp")
        (format t "FN_APP_RAW_LOAD_OK~%"))
:q
```

Source digests (SHA-256):

- `host/native/io.lisp`: `9ab29ee3ec8e3119a527571ba30dc4f6335d72718c786a249ad324814019f5d3`
- `host/native/workflow.lisp`: `a6de8a33df8495e7f8c58ade4656fe50b5ad3f6d30c242a58204e0c4ac73ff52`
- `tests/test_native_app_journal.py`: `c3591a66541b9249fd1d940a048b85d3c1518ad7ec42955748d3b0fbe9ae5c4d`
