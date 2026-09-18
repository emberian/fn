# Transfer assembly work bound

Status: ACL2 work-accounting experiment for the pure transfer staging kernel.
It proves bounds for the recursive assembly and missing-byte walks after an
entry has reached the frozen kernel's valid-entry hot path. It does not provide
a host-runtime or storage/transport performance guarantee.

[`books/transfer-work.lisp`](../books/transfer-work.lisp) defines costed
executions for the actual `fn-transfer-entry-candidate` traversal and the
`fn-transfer-missing-from` traversal used by missing-range reporting. Projecting
their values is proved equal to the frozen executable functions. The work model
counts list-cell work performed by the logical recursive `len`, `nth`, chunk
scan, and declared-position functions. It does not attach a claimed counter to
an unmodified call; its worker recomputes the same branches and values.

Let `N` be declared object length, `K` the retained chunk count, and `L` an
upper bound on every retained chunk's proper octet list. ACL2 proves these
polynomial hot-path bounds:

- completion scanning: at most `N * (1 + K) * (1 + L)` units;
- assembly byte lookup: at most `N * (1 + K) * (1 + L)` units;
- candidate construction: at most `2 * N * (1 + K) * (1 + L)` units;
- missing-byte reporting: at most `N * (1 + K) * (1 + L)` units.

The per-position presence scan has the sharper proved bound
`K * (1 + L)`. The aggregate completion theorem deliberately uses the common
`(1 + K) * (1 + L)` scan budget so that completion, assembly, and missing
reporting share one simple bound. The candidate theorem covers both an early
incomplete return and the completed assembly branch.

Empty objects have zero declared-position work, including the successful empty
candidate. A gap may stop completion at its first absent position, while
missing-range reporting continues through all declared positions. Thus the
candidate bound covers an incomplete/refused-to-assemble result as well as a
candidate; it does not model public invalid-state or missing-label error
checking. A present chunk scan includes its byte-length traversal; successful
byte lookup additionally includes the actual bounded `nth` traversal. The
costed executions' values are proved equal to the frozen candidate,
completion, assembly, and missing-from functions.

The arithmetic treats ACL2 natural-number addition, comparison, and arithmetic
on bounded values as unit-cost operations. Therefore it does not establish
constant-time machine arithmetic for unbounded ACL2 integers, allocation/GC or
cache behavior, host recursion-stack limits, parser/validation work,
state-recognizer/label lookup work, public invalid-state/missing-label refusal,
persistence, or network I/O. A future public-operation bound must add those
separate validation and lookup costs; storage capacity limits alone are not a
runtime proof.
