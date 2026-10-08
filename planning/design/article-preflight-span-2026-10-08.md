# ARTICLE preflight spans: statements for audit

Status: proposed statements, not proved, certified, implemented, or measured.
This checkpoint changes no executable source. P owns extent-cache.lisp and
page-window-*; their contracts will be consumed without editing those books.

## S1 — exact preflight equivalence

Proposed public theorem, with the same fuel premise as the existing scan:

```lisp
(implies (natp fuel)
  (equal (mv-list 2 (fn-ast-scan-step-span scan fuel limit fn-arena))
         (mv-list 2 (fn-ast-scan-step scan fuel fn-arena))))
```

Both the entire returned scan state and consumed-octet count must agree.
SCAN is unrestricted: no well-formed-payload, valid-header, warm-cache, or
successful-preflight premise is added. LIMIT is normalized to a positive
scheduling quantum; correctness is independent of its value.

The local span lemma states that folding the existing scan transition over
`fn-arena-get-span(h,p,n)` equals n applications of fn-ast-scan-one starting
at that source. Its range premises are established inside the caller:
fn-ast-source-readablep establishes a live handle and in-range offset, and
n is the minimum of remaining fuel, source remaining, arena bytes remaining,
and the positive quantum. The transition changes exactly the same source,
original source, pending-CR, line-start, separator, body-source, and bad fields.

When that readable-source test fails, preserve the existing literal/invalid
source behavior. With positive source remaining, this failed test also makes
fn-ast-source-byte's arena-read condition false: this fallback cannot perform
a durable scalar read. Empty fuel or source remaining returns immediately.
Thus malformed inputs retain their old answers without weakening the theorem
or leaving a scalar durable fallback on the served scan path.

## S2 — profile-owned span size

fn-ast-span-want will obtain B from
`(fn-profile-limit :read-window-octets)`, the existing profile row in
books/profile-limits.lisp. It is also the source of *fn-ew-span-capacity*
in books/page-window-span.lisp; there is no current :read-span-octets row.
The native +fnn-extent-span-capacity+ must derive from that same source,
replacing its separate 16384 literal. The renderer's literal 256 goes away.

B bounds work and temporary storage per span, not article size. Requests
also stop at fuel, source and available-window boundaries. S1 holds for every
positive quantum; neither scan validity nor header/body recognition depends
on this profile's numerical value. Profile or window splits resume without
truncation.

## S3 — decoded spans equal decoded scalar reads

For an lz extent and the existing fn-arena$x-get-span guard, require:

```lisp
(equal (fn-arena$x-get-span h p n fn-arena$x)
       (fn-arx-get-loop h p n fn-arena$x))
```

For n > 0, the optimized lz branch must invoke one bounded decoded-span
realizer for [p,p+n), rather than calling fn-durable-realize-lz-octet n times.
For n = 0, return nil without invoking a realizer. Introduce
that seam in the authorized get-span path: its logical definition is the
list of those same scalar answers, under the existing A-DURABLE-LZ model.
Its native implementation uses the authenticated decoded span entries;
its output/effect refinement remains an explicit implementation obligation,
not a theorem about real disk data inferred from the abstract model.

No decoded-span realizer currently exists. Reusing the whole-payload
fn-durable-realize-lz would remove the call count while retaining unbounded
whole-payload work/allocation, so it is not the proposed implementation.
One arena request makes one realizer call; that call makes one bounded copy
per actual cached/borrowed window intersection, at most B output octets per
copy. Misses preserve the complete cold descriptor and retry semantics.
S3 is not complete until the native seam and its consumer are connected.

## S4 — span count and the two-lock target

For a readable, fully warm range of N octets contained in one available
window, within one scan quantum, the proposed data-span call count is
K(N,B)=ceiling(N/B), with K(0,B)=0 and B positive. Derive the count from the
executed span-fetch branch: one event followed by the count for N-min(N,B)
octets. For multiple quanta or windows, sum those counts over the actual
intersections. Scalar durable-read events on this path must be zero.

Total scan work remains proportional to N. A def-cost visits row must bound
byte-transition work plus span-dispatch work, schematically a*N+b*K+c, with
constants derived from the executed body. Realizer work must be accounted
for or explicitly named unaccounted; it cannot be assigned zero to obtain
an O(K) total-work claim. Existing def-cost visits do not count native mutex
acquisitions, so they cannot alone prove a two-lock claim.

The W2L target is two data-span extent-lock acquisitions per warm 2 KiB
payload: one preflight span and one render span, when both fit their quanta
and one cached window, with B >= 2048. This excludes fixed control/ledger
locks and cold I/O, eviction races, retries, and window-boundary splits.
Measure total and data-span grabs separately on the served ARTICLE path.
This is a measurement target until that host composition is instrumented
and checked; it is not a claimed latency result or a bound on contended grabs.

## Teeth — concrete success and a failing mutation

Allocate the real arena payload `Subject: x\r\n\r\nAB\r\n` (18 octets), and
start fn-ast-preflight at its returned handle h, offset 0, remaining 18.
Use fuel 18 and a span quantum at least 18. Assert the entire antecedent,
that one fetched span contains the header/body boundary at offset 14, and
that both scans return used=18 and exactly:

```lisp
((h 18 0 nil) (h 0 18 nil) nil t 2 (h 14 4 nil) nil)
```

This positive witness uses an allocated arena payload, not a stubbed span
reader or an assumed successful scan.

The must-fail witness uses the same payload and all the same premises, but
mutates the span fold to drop its last octet, the final LF. Assert inequality
with the byte scan: the mutated source is (h 17 1 nil), pending-CR is true,
line-start is false, and separator state is 1. A must-fail equality test must
fail on this concrete counterexample; failed proof search is not the witness.
