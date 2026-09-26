# Ingress span: the wire machine's read over the octet buffer, 2026-09-26

Lane `lane/ingress-span`, from dev `dfa810fc`, under the Fable mandate
(`planning/handoff-2026-09-25-fable-mandate.md` §7; D27). Brief:
`build/coordinator/queue/done/w4-ingress-span.txt`. Registry: PRF-181,
REP-012, SCN-110, PKT-479, PKT-480. This is PKT-302 (iv), the ingress half of
rep-wave-d's program; its scope stops at the intern boundary (rep-wave-d-4's).

## 1. What a node does now that it did not before

A socket read no longer expands into a long-lived cons list on the served
hot path. Before this lane, `host/native/owner.lisp fnn-owner-handle-chunk`
coerced every socket read to a list (`fnn-octet-list`, a 512-element cons list
per read) and fed it to `fn-owner-chunk`, whose served fold
(`fn-scar-feed-counted` -> `fn-scar-feed-byte`) rebuilt the ten-field
connection record (`fn-served-make-conn-group-indexed`) once per byte and the
eight-field wire state once per byte. A 32 KiB POST allocated 20.8 MB, 635
bytes consed per payload octet, 59% of its CPU in that per-byte feed
(`planning/evidence/rep-wave-d-2026-09-25.md` §1.2).

Now the host fills the octet buffer (`fn-octets`) once from the socket byte
vector (`fnn-octets-fill`) and calls `fn-owner-chunk-span`, which reads the
range in place. `books/served-span.lisp fn-scar-feed-span` is the carried
served fold `fn-scar-feed-counted` reading the range's bytes by index
(`fn-octets-get`), so no octet of a read is ever a cons cell: the 512-element
per-read list (`fnn-octet-list`) and the list walk it drove
(`fn-ag-cdr`/`fn-wire-ag-cdr`) are gone from the served hot path. The wire
machine's own whole-span read over the buffer is proved in
`books/wire-span.lisp` (`fn-wire-feed-span`) and is the foundation the
per-framed-event served fold (PKT-479) calls.

## 2. The proof boundary

The subject the host calls is `fn-owner-chunk-span` (host/owner-host.lisp)
-> `fn-scar-ocfg-read-span` (books/served-span.lisp). The logical model stays
the octet-list byte machine of books/wire.lisp; the correspondence is proved,
not assumed.

- KEYSTONE `fn-scar-feed-span-is-feed-counted` (no hypothesis): the served
  buffer fold `fn-scar-feed-span conn i end ... fn-octets` reads the range's
  bytes by index and is EXACTLY the carried list counted fold
  `fn-scar-feed-counted conn (fn-oct-slice-list i end fn-octets)` -- byte for
  byte, the buffer's cell i being the slice's car and [i+1, end) its cdr. So
  the served read decides exactly what the list read decided. Guard-verified;
  `fn-scar-feed-span-consumed-is-natural`.
- Wire-level foundation (PKT-479): `fn-wire-feed-span (wire-state i end
  fn-octets)` (books/wire-span.lisp) is the fold of `fn-wire-feed-byte` over
  the buffer's range, and KEYSTONE `fn-wire-feed-span-is-feed-proper` (through
  `fn-wire-span-fold-is-feed-proper`) says its (state, events) equals
  `fn-wire-feed-proper` over `(fn-oct-slice-list i next)` -- the reference byte
  machine on exactly those octets, whose partition law
  `fn-wire-feed-proper-append` composes reads. This is the wire read the
  per-framed-event served fold will call; it is not on the live host path yet
  (the live fold is per byte).
- KEYSTONE for the host line
  `fn-scar-ocfg-read-span-is-reference-under-ocl-relation`: under the
  configured owner's relation (`fn-ocl-relation`) and its view trie's
  correspondence, the span read `fn-scar-ocfg-read-span oc id i end fn-octets`
  is `fn-ocfg-read-tls-prefix oc id (fn-oct-slice-list i end fn-octets)` -- the
  list read the existing served path already establishes as correct
  (`fn-scar-ocfg-read-tls-prefix-is-reference-under-ocl-relation`). The read
  keeps the store (`fn-scar-ocfg-read-span-keeps-store`) and its node premise
  (`fn-scar-ocfg-read-span-preserves-node-premise`).

Teeth (tests/acl2/wire-span-tests.lisp, served-span-tests.lisp): a ground
positive witness that a dot-stuffed line and a line split across two reads is
framed identically to the reference; the `:line-overlimit` refusal is the
reference's; one `must-fail` per guard hypothesis of each keystone (octets-p,
range-within-buffer, fast-statep; ocl-relation, view-indexedp, natp start).
`fn-scar-feed-span-is-feed-counted` has no hypothesis, so no must-fail; its
witness is the equality on ground.

## 3. Measurement

PENDING (rep_measure alloc at 32 KiB, post_owner_cpu_ms at N=120, post_n
--prof, 3 MiB wall/RSS; before/after on the matched image pair, hbox).

## 4. Native gate (SCN-110)

PENDING (tests/test_native_bounds_join.py 33k/200k/3M, test_native_owner.py
overlimit, test_native_served_cost.py, test_native_nntp_post_probe.py on hbox).

## 5. Not done

- PKT-479 (the bulk of the measured win): (a) the served fold still rebuilds
  the ten-field connection once per byte -- dispatching per FRAMED EVENT
  instead (the wire already frames a whole body in one span) removes it, but
  the byte-stepping correspondence `fn-scar-feed-span = span+dispatch` runs
  over the connection machinery and exceeded the <10 s book budget; (b) the
  wire still rebuilds the eight-field state per byte -- a per-line index scan
  (next CRLF by `fn-oct-line-end`, line limit by subtraction) removes it, but
  its scan=fold keystone did not close under the ACL2 rewriter within budget.
  Both are lemma-engineering, not soundness gaps. This lane removes the
  per-read list and the list walk (D27) and proves the buffer read is the
  reference; (a) and (b) are the residual per-byte allocation.
- PKT-480: PKT-316's collection-trigger placement is the coordinator's call
  (one line, then a matched rerun); this lane does not decide it.
- The submission still holds the article body as an octet list; the seal to a
  buffer range is rep-wave-d-4's (§interface in the LANEDUMP).

## 6. Certification

farm persvati: run-20260926T143838Z-e0fd (served-span, served-span-tests)
and run-20260926T141822Z-1776 (wire-span, wire-span-tests). Manifests in
`planning/evidence/manifests/`.
