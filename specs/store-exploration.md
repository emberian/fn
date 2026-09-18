# Bounded immutable-file kernel exploration

Status: executable bounded evidence for the logical file-publication kernel;
this is not an exhaustive result for the unbounded store and does not qualify
filesystem or power-loss behavior.

`tests/acl2/store-files-exploration-tests.lisp` explores the actual transition
functions in `books/store-files.lisp`.  It uses two fixed valid candidate
records, the two configured groups, capacity 4, a maximum durable frontier of
2, and at most two stable records.  The event set includes allocator staging,
data barriers, replacement and directory errors/successes, refusal and abort
outcomes, record publication cuts, all matching/lost/rejected completion
outcomes, success emission/loss, both old/new allocator observations, absent or
present exact record observations, recovery, uncertain recovery, and repeated
recovery/barrier events.

The explorer deduplicates states and retains an edge for every tested event
whose post-state remains inside the declared finite domain.  It asserts that
the queue empties before the fuel bound, every retained state satisfies the
kernel recognizer, and every retained edge preserves the prior stable-record
and success prefixes.  It also asserts phase coverage for all reachable
publication, completion, replay, recovery, and fenced states; both allocator
choices; all four record crash choices; and recovery barrier counts 0 through
4.  Readiness is supplied by the kernel state recognizer, which requires all
five barriers.

Evidence from the 2026-09-18 run:

```text
python3 tools/certify_books.py tests/acl2/store-files-exploration-tests --timeout-seconds 180
ACL2 Version 8.7; SBCL 2.6.8
SFE_BOUNDED_EXHAUSTIVE fuel=10000 max-frontier=2 max-records=2 states=211 edges=9038
status: passed
```

The certified source digests were `tests/acl2/store-files-exploration-tests.lisp`
SHA-256 `5d53822dfecdd9b912ad960e80102be8bb02a99adb0314634c51ec04eac7832a`
and `books/store-files.lisp` SHA-256
`067ca3fc0ffa6a643a7f3de4ff1180c2301c49b03272159a7623c0ede74b5c85`.
Certification evidence is under
`build/acl2/certify-20260918T103236Z-31531/`.

The bounded graph does not cover malformed on-disk frames, arbitrary record
contents, frontiers above 2, more than two stable records, physical namespace
reordering, or hardware power loss.  A `:fault` state from malformed recovery
input remains outside this valid reachable-domain exploration and requires its
own fault-input tests.
