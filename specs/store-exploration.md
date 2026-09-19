# Bounded immutable-file kernel exploration

Status: executable bounded evidence for the logical file-publication kernel;
this is not an exhaustive result for the unbounded store and does not qualify
filesystem or power-loss behavior.

`tests/acl2/store-files-exploration-tests.lisp` explores the actual transition
functions in `books/store-files.lisp` from `fn-sf-initial-state` under the two
configured groups, capacity 4, a maximum durable frontier of 2, and at most two
stable records. Three candidate records are in the domain: sequence 0 at txid
0, sequence 1 at txid 1, and a txid-gap record, sequence 0 at txid 1, which is
preparable only after reservation 0 was consumed by a refusal or a known abort
and reservation 1 was made durable. The event set is the cross-product of the
result cuts the host reports: allocator staging; file barrier success and known
failure; replacement and directory success and error; refusal of either
reservation; preparation of each record; record file barrier success and known
failure; prepublication abort and abort completion for each record pair; link
and directory success and error; core completion and success emission for each
record pair; all four crash choices; recovery; and recovery barrier success and
uncertainty. The event `:lose-success` is excluded because `fn-sf-lose-success`
is unreachable-in-composition (see `books/store-files.lisp`).

## What is counted

The explorer deduplicates states and retains an edge for every tested
(state, event) application whose post-state remains inside the finite domain.
Three different quantities are reported, and each is asserted against the
recorded run:

- **states**: distinct reachable kernel states inside the bounds;
- **applications**: retained (state, event) pairs, including no-op applications
  in which the kernel refused or ignored the event and returned the same state;
- **transitions**: applications whose post-state differs from the source, with
  the number of distinct (source, destination) pairs among them reported
  separately, because several events can select the same successor.

The number of states in the transient phases `:aborting` and `:completed`
(intermediate states of the composed `fn-sn-known-abort` and `fn-sn-finish`
steps, never observable between host calls) is reported and asserted as well.

## Assertions

The test asserts that the queue empties before the fuel bound, every retained
state satisfies the kernel recognizer, every retained application preserves the
prior stable-record and success prefixes, and the five counts equal the recorded
run. It asserts phase coverage for every phase of the kernel except `:fault`,
which it asserts is absent: a `:fault` state arises only from malformed recovery
input, outside this valid-domain exploration. It asserts that the txid-gap path
is explored: reservation 0 is refused, the gap record is prepared, published and
acknowledged as the pair (0 . 1), and aborted in a sibling branch. It asserts
that the two syscall-issued-unobserved crash points are genuine choices: from
`:frontier-data-durable` a crash edge reaches the candidate frontier and from
`:record-data-durable` a crash edge reaches the appended candidate, while no
crash edge changes the frontier from `:frontier-staged` or `:reserved` and no
crash edge changes the records from `:record-staged`, `:aborting`, `:completing`
or `:ready`. It asserts that both frontier choices and both record choices are
exercised from `:frontier-attempted` and `:record-attempted`, that repeated
recovery is in the event domain, and that recovery barrier counts 0 through 4
are reached; readiness is supplied by the kernel recognizer, which requires all
five barriers.

## Recorded run

Evidence from the 2026-09-19 run:

```text
python3 tools/certify_books.py tests/acl2/store-files-exploration-tests
ACL2 Version 8.7; SBCL 2.6.8
SFE_BOUNDED_EXHAUSTIVE fuel=10000 max-frontier=2 max-records=2 events=35
states=240 applications=8337 transitions=1127 transition-pairs=524
transient-states=8
status: passed
```

The certified source digests and the evidence directory are recorded in the
manifest of the integrated gate run (`build/acl2/certify-*/manifest.json`) and
in the lane handoff.

The earlier record of this test, 211 states and 9,038 edges, counted
applications including no-op self-loops over a two-record domain that had no
txid-gap record, three fenced phases the composition cannot reach, uncertain
and lost result values the host never reports, and no crash choice in the
data-durable phases. It is superseded by the run above.

## Limits

The bounded graph does not cover malformed on-disk frames, arbitrary record
contents, frontiers above 2, more than two stable records, physical namespace
reordering, torn writes within a file, directory rename or link atomicity, or
hardware power loss. Those are the named physical assumptions listed in
[store-refinement.md](store-refinement.md#assumptions-and-claim-boundary); the
exploration takes them as given through the kernel crash constructor.
