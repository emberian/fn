; owner-carrier.lisp -- the owner's carrier: its own stobj (stage 5, the
; carrier move; planning/design-store-representation-2026-10-01.md section
; 4 stage 5, the coordinator's decision (b) of 2026-10-02).
;
; The configured owner and the retention carry lived in the ACL2 state
; globals 'fn-owner and 'fn-owner-retain-carry.  Every host entry that
; returns STATE could then have written them, so def-carried's completeness
; over the carried relation (fn-owner-retain-statep) counted all 312 such
; entries, and the 33 :program writers among them kept the relation from
; being an invariant at all.  Here they are the fields of FN-OWNER-ST.  The
; stobj discipline is the frame: a function that does not return
; FN-OWNER-ST cannot change it, so completeness counts exactly the entries
; whose stobjs-out name it -- the owner's writers -- and every other
; state-returning entry keeps the relation without a theorem.
;
; The fields: the configured owner (fn-ocfg-...), whether one was ever
; installed (the old (boundp-global 'fn-owner state): entries answer
; "owner unavailable" before the first install), and the retention carry
; (books/post-retain-carried.lisp fn-prc-..., NIL before the first refresh,
; as the unbound global read).  The only updaters are the two installers
; below; tools/owner_carrier.py rewrites the host to call them.

(in-package "ACL2")

(defstobj fn-owner-st
  (fn-ost-ocfg :initially nil)
  (fn-ost-installedp :type (satisfies booleanp) :initially nil)
  (fn-ost-carry :initially nil))

(defun fn-owner-boundp (fn-owner-st)
  (declare (xargs :stobjs fn-owner-st))
  (fn-ost-installedp fn-owner-st))

(defun fn-owner-ocfg (fn-owner-st)
  ; The configured owner, for host wrappers.
  (declare (xargs :stobjs fn-owner-st))
  (fn-ost-ocfg fn-owner-st))

(defun fn-owner-install-ocfg (oc fn-owner-st)
  ; The owner installer: the configured owner OC, now installed.
  (declare (xargs :stobjs fn-owner-st))
  (let ((fn-owner-st (update-fn-ost-ocfg oc fn-owner-st)))
    (update-fn-ost-installedp t fn-owner-st)))

(defun fn-owner-retain-carry (fn-owner-st)
  (declare (xargs :stobjs fn-owner-st))
  (fn-ost-carry fn-owner-st))

(defun fn-owner-retain-carry-put (carry fn-owner-st)
  ; The carry installer.
  (declare (xargs :stobjs fn-owner-st))
  (update-fn-ost-carry carry fn-owner-st))

; The installers' effects and frames, the only facts about the carrier the
; owner's theorems need.
(defthm fn-owner-ocfg-of-install-ocfg
  (equal (fn-owner-ocfg (fn-owner-install-ocfg oc fn-owner-st)) oc))
(defthm fn-owner-bound-of-install-ocfg
  (fn-owner-boundp (fn-owner-install-ocfg oc fn-owner-st)))
(defthm fn-owner-retain-carry-of-install-ocfg
  (equal (fn-owner-retain-carry (fn-owner-install-ocfg oc fn-owner-st))
         (fn-owner-retain-carry fn-owner-st)))
(defthm fn-owner-retain-carry-of-put
  (equal (fn-owner-retain-carry (fn-owner-retain-carry-put carry fn-owner-st))
         carry))
(defthm fn-owner-ocfg-of-retain-carry-put
  (equal (fn-owner-ocfg (fn-owner-retain-carry-put carry fn-owner-st))
         (fn-owner-ocfg fn-owner-st)))
(defthm fn-owner-bound-of-retain-carry-put
  (equal (fn-owner-boundp (fn-owner-retain-carry-put carry fn-owner-st))
         (fn-owner-boundp fn-owner-st)))
(defthm fn-owner-install-ocfg-preserves-stp
  (implies (fn-owner-stp fn-owner-st)
           (fn-owner-stp (fn-owner-install-ocfg oc fn-owner-st))))
(defthm fn-owner-retain-carry-put-preserves-stp
  (implies (fn-owner-stp fn-owner-st)
           (fn-owner-stp (fn-owner-retain-carry-put carry fn-owner-st))))

(in-theory (disable fn-owner-boundp fn-owner-ocfg fn-owner-install-ocfg
                    fn-owner-retain-carry fn-owner-retain-carry-put))
