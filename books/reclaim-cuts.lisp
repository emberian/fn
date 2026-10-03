; fn: the installing reclaim pass's cuts, as a leaf (lane def-holder,
; 2026-10-03; moved out of books/owner-reclaim-pass.lisp unchanged, so that a
; holder declaration can name a cut of the pass without that book's closure:
; books/handle-holds.lisp (:physical *fn-orcp-cuts* :cut :released :after
; :installed)).
;
; The steps in order; each is a point a process death can fall at, and the
; host names it (FN_NATIVE_RECLAIM_FAULT=<cut>:kill on a developer image;
; host/native/owner.lisp +fnn-reclaim-cuts+ mirrors this list):
;   :captured   the capture under the mutex (the log rotated, the pass the
;               publication in flight, its credit reserved);
;   :rewritten  the walk over the captured rows off the mutex;
;   :staged     the reclaimed checkpoint written and fenced in staging/;
;   :interned   the tombstoned records interned into the live arena (fresh
;               handles no row names yet);
;   :rebuilt    the rebuilt Store, catalog and history columns off the mutex;
;   :installed  the staged checkpoint renamed into place (the commit point);
;   :swapped    the owner's state replaced by the rebuilt one;
;   :released   the covered segments dropped and their blocks given back
;               (books/extent-retire.lisp).
; What each cut's outcome is (old or new publication) is decided beside the
; pass: books/owner-reclaim-pass.lisp fn-orcp-cut-outcome.
(in-package "ACL2")

(defconst *fn-orcp-cuts*
  '(:captured :rewritten :staged :interned :rebuilt :installed :swapped :released))
