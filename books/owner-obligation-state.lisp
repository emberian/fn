; The owner's installation of a configuration, and W9's obligation view
; PARKED (lane figure-and-contract, 2026-10-01, the coordinator's decision
; (B)).  The view (books/retention-obligation-view.lisp: a count and a
; subject trie over the retention pins) was rebuilt at every open and
; reclaim and updated at every install, and no served code read it: the
; admission captured it only as a token-tagged tuple.  The heap figure
; charged it 546,341,504 octets at the small profile.  The operator paid
; memory for work that bought nothing, so it is parked until its reader
; lands; W9's bounded pilot (ratified 2026-09-30) re-adds an obligation view
; WITH its reader and its heap-figure term together.  Until the host's
; captures and puts of the global go (after stage 0), the global keeps its
; name and no install writes it: it reads NIL.
(in-package "ACL2")
(include-book "state-globals")
(include-book "owner-config")
(include-book "owner-carrier")

(defun fn-owner-obligation-view (state)
  (declare (xargs :stobjs state :guard t))
  (if (boundp-global 'fn-owner-obligation-view state)
      (f-get-global 'fn-owner-obligation-view state)
    nil))

(defthm fn-owner-obligation-view-of-other-global-put
  (implies (not (equal key 'fn-owner-obligation-view))
           (equal (fn-owner-obligation-view (f-put-global key value state))
                  (fn-owner-obligation-view state))))

; The owner installer is books/owner-carrier.lisp fn-owner-install-ocfg (the
; carrier's field update); the view, a state global, is untouched by it --
; a frame the stobj discipline gives: the installer takes no STATE.

; Cold open's install: the same update (it installed a rebuilt view beside
; the owner before the park).
(defun fn-owner-install-open-ocfg (oc fn-owner-st)
  (declare (xargs :stobjs fn-owner-st))
  (fn-owner-install-ocfg oc fn-owner-st))

(defthm fn-owner-open-ocfg-effect
  (equal (fn-owner-ocfg (fn-owner-install-open-ocfg oc fn-owner-st)) oc))
(defthm fn-owner-open-owner-bound
  (fn-owner-boundp (fn-owner-install-open-ocfg oc fn-owner-st)))
(defthm fn-owner-open-ocfg-preserves-stp
  (implies (fn-owner-stp fn-owner-st)
           (fn-owner-stp (fn-owner-install-open-ocfg oc fn-owner-st))))

(in-theory (disable fn-owner-obligation-view fn-owner-install-open-ocfg))
