# Registered window worker storage

Source candidate only. The metadata frontier has not been admitted: the first
cheap check in the borrowed `mib` world found `fn-pwx-tokenp` absent, and no
candidate events were sent. There is no installed worker, native callback,
constructor allowance, or last-borrow receipt from this component.

`books/page-window-worker-storage.lisp` gives each physical worker address one
carry and the actual retained input, digest and private window children. A node
uses six fixed keys: left, right, carry, input, digest and window. Binary address
traversal and free-worker selection must be resumable; physical addresses are
not issued job identities. Reads must check child presence before selecting it.
The selected compiler's default-creator behavior at an existing-child GET is a
separate allocation obligation, even when the logical read creates nothing.

The carry has seven fields: physical worker ID, full issued window token,
worker phase, immutable query custody root, retained storage receipt, outer
borrow phase, and installed input capacity. The top-level registry retains its
installation receipt and root. Default construction leaves it uninstalled.
The declarations also create image defaults; those objects need their own
matched baseline census and cannot be charged as later factory objects.

The source-qualified factory must reserve construction before creating a node
or child, retain partial construction after an unknown result, and publish an
association only after successful construction and same-pool accounting. The
actual input, digest and window remain allocated and charged in permanent U
across successive jobs. Ending a job relinquishes its claims; it does not prove
that the reusable backing was reclaimed.

The acquisition parent derives the full query token from RH and reads CURRENT
custody before issuing a window token. An existing outer borrow yields without
spending a replacement identity. It selects a registered idle worker, derives
the window descriptor from the same authorized held row and captured source,
and persists assignment intent before native work. The query grant alone is
not construction or decoder authority. Paired readers needing simultaneous
borrows require distinct registered holder roots.

Actual worker return and the last outer scalar alias are distinct events.
Return retains the full token, buffers and charges. Only the real epilogue,
after dynamic bindings have unwound and all sanctioned aliases have returned,
may start the recipient-bound terminal cursor. Outgoing response/job roots are
separate; socket progress, a drained renderer, an ATS nonce, and a NIL native
result cannot discharge them. Exception and cancellation paths retain debt.

The current metadata functions export only status, worker ID, phase and the
borrowed immutable root. They do not install storage, return a buffer pointer,
choose a free worker, authenticate a source, or emit a settled receipt.
Decoded tokens explicitly refuse: the three retained raw-worker children do
not establish the decoder's private ring, table, output and source custody.
