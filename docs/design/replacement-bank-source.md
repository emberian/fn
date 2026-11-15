# Reserved C replacement banks

This source projection separates configured resident capacity R from two E-row
physical catalog banks. E is the supported profile's physical extent capacity,
not a bound on article count or stored history. A rebuilt source root occupies
an actual extent, so an E-row catalog bank suffices for the concurrently held
root set. Growing history is handled by the streaming producer; additional row
capacity does not repair a producer that stops when resident pages fill.

The resident installer and its free-row searches must use only `[0,R)`. The
physical installer uses `[R,R+2E)`. Actual initialization records R and E, so a
direct table initializer cannot accidentally infer a valid partition from an
arbitrary total row count. A cold opener reconstructs the authenticated selected
catalog in bank 0 only after its existing closure/hold gates succeed. Bank
position is volatile placement, never persisted authority or a recovery choice.

The live pending SUMMARY row retains its target bank. A first live adoption
uses bank 0; an adoption replacing an APPLIED catalog chooses the other bank.
The bounded FIT stage scans the actual installed rows for version priority,
but counts only FREE, nonphysical cells in the target bank. It requires the
entire E-cell bank drained. INSTALL starts at that bank's first row, advances
once per actual installed root, and refuses an occupied or out-of-bank target.
It never borrows a resident row or the old active bank. Query promotion carries
the bank into active SUMMARY0; terminal reopen compares the exact bank along
with the existing descriptor, canonical authority-consume and writer receipt.

`tools/replacement_bank_live_rewrite.py` is a named transformation over the
three frozen providers in its fixture. It preserves function formals and guards.
Its five Python controls check source replay, retained bank identity and the
actual range/drain clauses. They are source controls, not ACL2 admission,
physical-work refinement or productive two-adoption evidence.

Remaining connected obligations before this can serve:

- The constructor/C geometry/resident search packet is composed as4161477a4
  (donor c789c00f9). Eight source controls pass; its full-R constructor fixture
  is unexecuted and explicitly uses synthetic Ref scalars, not verified media.
- A bounded HELD prepublication bank check must reject or yield before durable
  Write/Fence acceptance if the inactive bank is not drained. Postpublication
  FIT alone is a safe refusal but cannot establish useful publication admission.
- The original-source inventory/retirement path must release every old row and
  its actual cache/hold obligations before that bank is reused. Observer drain
  remains exact owner/generation-bound; no third generation is available.
- A real full-R control must drive two publication/reopen transitions, delay an
  old observer and prove refusal before durable acceptance, then progress after
  actual release. Cold reconstruction must preserve old proof holds across
  recovery. Those execution/critical evidence obligations are still unrun.

The draft `checkpoint-bank-admission.lisp` supplies lower BEGIN/STEP/READY-P
functions over `(token kind owner generation snapshot summary installed job)`.
Its singleton retains the actual HELD owner/cut and active catalog identity;
STEP inspects at most one actual inactive-bank cell. An occupied cell returns
`:resources` without advancing the cursor. No pool reserve, durable mutation,
or physical Write occurs in this provider. Four source controls pass. Actual
registration, derived callback charge, MASTER post-HELD/pre-reserve routing and
typed consumer receipt propagation remain unfinished. Its READY phase is a
derived scan continuation, not a caller-supplied readiness flag.

The current-root projection is based on ROOT42aba and preserves named newer
foundation/C/reader providers. Untracked dependency leaves in this worktree
remain an incomplete source projection; this document does not qualify their
closure, enable activation, or authorize compute.
