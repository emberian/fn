# Stable history-provider addresses before activation

Status: selected by the coordinator after inspection of the actual provider
and confirmation from index and ATS owners. Design handoff; no qualification
or deployment claim. Index owns implementation in its delegated backing hunk.

The existing `books/history-event-provider.lisp` routes the low bit first:
`mod slot 2` chooses left/right, then `floor slot 2` recurses. Wrapping an old
root as the new root's left child and increasing global depth does not preserve
addresses. At depth 1, slot 1 is the old right child; at depth 2, slot 1 first
selects the new right child and never reaches the old root under the left child.
There is also no established sanctioned constant-work move-root primitive for
these nested stobjs. Do not transplant raw mutable child aliases.

The actual node's fixed stobj-table permits all three keys simultaneously:
left child, right child and event page. No inspected invariant forbids a page
at a node that also has children. The index owner confirms no genuinely issued
HEP provider/source is activated in served or cold production; existing populated
providers are source fixtures. Select the following layout before activation,
without interpreting an old fixed-depth provider under the new rule.

## Address rule

For physical slot `s`, use the immutable path of length `integer-length(s)`,
low bit first, and find its page when the remaining slot is zero. Slot zero
has its page at the root. Examples:

| Slot | Path |
| --- | --- |
| 0 | root |
| 1 | right |
| 2 | left, right |
| 3 | right, right |
| 4 | left, left, right |

Future slots may extend below an existing page. They do not move that page,
change its address length, or reinterpret any existing slot. Binary expansion
with an explicit terminal page position gives an injective address for every
natural slot; prefixes are legal because a page and children coexist.

## Exact source/API conversion

Keep `fn-hep-node-read` and `fn-hep-node-append` as internal recursive subjects
with their existing depth argument if useful. At the actual
`fn-hep-page-read` and `fn-hep-publish-current` callers, derive depth in ACL2
from `integer-length` of the authenticated leaf's physical slot. The old
`fn-hep-provider-depth` field has no physical routing or cost authority; it may
remain temporarily as a deprecated field to avoid unrelated schema churn.

The genuine page factory follows this same path. Each funded construction call
creates at most one missing child or the terminal fixed-size event page and
records the actual allocation in its existing inventory. Already present
children/pages are not replaced. A private incomplete path is unreachable
through the preceding committed forest, so old readers remain valid. Durable
publication appends the exact retained event and publishes its completed forest
and Source9 through the existing same-event owner transition.

Source9 root ID continues to identify the immutable logical forest publication;
it is not an address of a mutable physical directory. The real source issuer,
captured custody and leaf epoch/id/incarnation/base checks bind that forest to
the actual provider. A caller-supplied Source9 or leaf shape is not authority.
There is no additional physical root registry or migration copy for this growth
operation. Separate old-epoch retirement and last-borrow obligations remain.
Changing the current epoch must not silently retire held pages or refund debt.

## Physical traversal scope

The present sanctioned nested-stobj implementation does not retain a borrowed
child across scheduling calls. It preflights the full physical route before
borrowing: `integer-length(slot) + 1` node/page steps, plus its enclosing fixed
work. Insufficient fuel yields before the traversal. Logical forest lookup and
one-object construction are resumable; this does not by itself implement a
persistent physical child cursor.

For the selected concrete runtime, derive the supported physical-slot domain
and sufficient traversal quantum from its actual representation and installed
profile. Profile validation must establish representability and installed
quantum at least the maximum complete route work before serving. Logical
history ordinals and source/root identities are not physical slots: the actual
registered leaf maps them to a genuinely issued physical slot within that
domain. An unsupported profile is explicitly refused before serving. Do not
impose an arbitrary directory-depth or stored-data ceiling.
A profile requiring physical routes longer than the offered quantum must obtain
a sufficient charged traversal quantum or a genuine different locator
representation; repeatedly yielding at an impossible quantum is not progress.
No theorem should call the existing physical borrow itself resumable.
The coordinator explicitly accepted this distinction: logical forest resume
plus a bounded, nonyielding physical route for each supported profile. A
pre-borrow yield acquires no child authority.

## Required narrow evidence

- Slot-to-path injectivity, including slot zero and page/child coexistence.
- Creating a different slot's missing node/page preserves an authenticated old
  leaf's row, status and fuel result; extending below an existing page is a
  positive case, not an omitted corner.
- Held source/F/forest and exact leaf stamps still select the original events,
  including a literal NIL row at the representation boundary.
- The actual factory and publication caller use the same stable address rule
  and source-derived cost; global depth changes cannot affect a read.
- A concrete old-root wrapping counterexample prevents accidentally restoring
  the incompatible fixed-depth growth algorithm.

Preserve old fixed-layout evidence as predecessor evidence only. The new bytes
need their own affected-root guards/refinement and caller evidence.
