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

(defun fn-owner-obligation-view (state)
  (declare (xargs :stobjs state :guard t))
  (if (boundp-global 'fn-owner-obligation-view state)
      (f-get-global 'fn-owner-obligation-view state)
    nil))

(defthm fn-owner-obligation-view-of-other-global-put
  (implies (not (equal key 'fn-owner-obligation-view))
           (equal (fn-owner-obligation-view (f-put-global key value state))
                  (fn-owner-obligation-view state))))

; This is the exact host-called function, moved from owner-host. Owner
; effects are one global put.
(defun fn-owner-install-ocfg (oc state)
  (declare (xargs :stobjs state :guard t))
  (f-put-global 'fn-owner oc state))

; Cold open's install: the same put (it installed a rebuilt view beside
; the owner before the park).
(defun fn-owner-install-open-ocfg (oc state)
  (declare (xargs :stobjs state :guard t))
  (fn-owner-install-ocfg oc state))

(defthm fn-owner-installed-ocfg-effect
  (equal (f-get-global 'fn-owner (fn-owner-install-ocfg oc state)) oc))
(defthm fn-owner-installed-owner-bound
  (boundp-global 'fn-owner (fn-owner-install-ocfg oc state)))

(defthm fn-owner-installed-other-global-effect
  (implies (not (equal key 'fn-owner))
           (equal (f-get-global key (fn-owner-install-ocfg oc state))
                  (f-get-global key state))))

(defthm fn-owner-installed-other-global-bound
  (implies (not (equal key 'fn-owner))
           (equal (boundp-global key (fn-owner-install-ocfg oc state))
                  (boundp-global key state))))

; The park's frame: no install touches the obligation view.
(defthm fn-owner-install-keeps-the-obligation-view
  (equal (fn-owner-obligation-view (fn-owner-install-ocfg oc state))
         (fn-owner-obligation-view state)))

(defthm fn-owner-installed-state-p1
  (implies (state-p1 state) (state-p1 (fn-owner-install-ocfg oc state))))

(defthm fn-owner-open-ocfg-effect
  (equal (f-get-global 'fn-owner (fn-owner-install-open-ocfg oc state)) oc))
(defthm fn-owner-open-state-p1
  (implies (state-p1 state) (state-p1 (fn-owner-install-open-ocfg oc state))))
(defthm fn-owner-open-owner-bound
  (boundp-global 'fn-owner (fn-owner-install-open-ocfg oc state)))
(defthm fn-owner-open-keeps-the-obligation-view
  (equal (fn-owner-obligation-view (fn-owner-install-open-ocfg oc state))
         (fn-owner-obligation-view state)))

(in-theory (disable fn-owner-obligation-view fn-owner-install-ocfg
                    fn-owner-install-open-ocfg))
