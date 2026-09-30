; Guarded companions to exact selected owner callback bodies.
; Reader opens use captured D and restore working view; exposure and peer
; opens use the working owner. Guards do not validate whole owner/store.
; Installed runtime/source authority remains the outer selector obligation.
(in-package "ACL2")
(include-book "owner-connection-state")
(include-book "owner-obligation-state")
(include-book "owner-open-carried")
(include-book "owner-reader-view")
(include-book "owner-log")
(include-book "store-octet-entry")

(defthm fn-owner-callback-owner-bound-of-other-put
  (implies (and (boundp-global 'fn-owner state)
                (not (equal key 'fn-owner)))
           (boundp-global 'fn-owner (f-put-global key value state)))
  :hints (("Goal" :in-theory (enable boundp-global put-global))))

(defthm fn-owner-callback-state-p1-of-global-put
  (implies (and (state-p1 state)
                (symbolp key)
                (not (equal key 'current-acl2-world))
                (not (equal key 'timer-alist))
                (not (equal key 'print-base)))
           (state-p1 (f-put-global key value state)))
  :hints (("Goal" :in-theory (enable put-global))))

(defun fn-owner-callback-install-effects (effects state)
  (declare (xargs :stobjs state :guard t))
  (let* ((state (fn-owner-install-served-effects effects state)))
    (f-put-global 'fn-owner-output (fn-served-reply-octets effects) state)))

(defthm fn-owner-callback-effects-preserve-owner-bound
  (implies (boundp-global 'fn-owner state)
           (boundp-global 'fn-owner
             (fn-owner-callback-install-effects effects state)))
  :hints (("Goal" :in-theory (enable fn-owner-callback-install-effects
                                    fn-owner-install-served-effects))))

(defthm fn-owner-callback-effects-preserve-state-p1
  (implies (state-p1 state)
           (state-p1 (fn-owner-callback-install-effects effects state)))
  :hints (("Goal" :in-theory
           (e/d (fn-owner-callback-install-effects fn-owner-install-served-effects)
                (put-global)))))

(defun fn-owner-callback-exposure-limits (state)
  (declare (xargs :stobjs state :guard (boundp-global 'fn-owner state)))
  (fn-exp-limits (fn-cfg-value (fn-owner-config state))
                 (fn-own-max-conns (fn-owner-core state))
                 (fn-owner-exposure-publicp state)
                 (fn-auth-config-requiredp (fn-owner-auth state))))

(defun fn-owner-callback-at-reader-view (state)
  (declare (xargs :stobjs state :guard (boundp-global 'fn-owner state)))
  (let ((views (fn-owner-reader-views state)))
    (if (consp views)
        (fn-owner-install-ocfg (fn-ocfg-at-reader-view (fn-owner-ocfg state) views)
                               state)
      state)))

(defthm fn-owner-callback-reader-view-preserves-owner-bound
  (implies (boundp-global 'fn-owner state)
           (boundp-global 'fn-owner (fn-owner-callback-at-reader-view state)))
  :hints (("Goal"
           :use ((:instance fn-owner-installed-owner-bound
                  (oc (fn-ocfg-at-reader-view (fn-owner-ocfg state)
                                             (fn-owner-reader-views state)))))
           :in-theory (e/d (fn-owner-callback-at-reader-view)
                           (boundp-global fn-owner-installed-owner-bound)))))

(defun fn-owner-callback-at-working-view (working state)
  (declare (xargs :stobjs state :guard (boundp-global 'fn-owner state)))
  (if (consp (fn-owner-reader-views state))
      (fn-owner-install-ocfg (fn-ocfg-with-view (fn-owner-ocfg state) working) state)
    state))

(defthm fn-owner-callback-working-view-preserves-owner-bound
  (implies (boundp-global 'fn-owner state)
           (boundp-global 'fn-owner
             (fn-owner-callback-at-working-view working state)))
  :hints (("Goal"
           :use ((:instance fn-owner-installed-owner-bound
                  (oc (fn-ocfg-with-view (fn-owner-ocfg state) working))))
           :in-theory (e/d (fn-owner-callback-at-working-view)
                           (boundp-global fn-owner-installed-owner-bound)))))

(defun fn-owner-callback-open-at (state)
  (declare (xargs :stobjs state :guard (boundp-global 'fn-owner state)
                  :guard-hints (("Goal" :in-theory (disable boundp-global put-global
                           fn-owner-callback-install-effects
                           fn-owner-install-served-effects
                           fn-olog-connection-line fn-owner-auth)))))
  (let* ((before (fn-owner-core state))
         (id (fn-own-next-id before))
         ; fn-ocar-ocfg-open (books/owner-open-carried.lisp) is fn-ocfg-open
         ; under the configured owner's relation
         ; (fn-ocar-ocfg-open-is-ocfg-open-under-ocl-relation): the greeting
         ; takes the view archive's fn-statep, the store node's
         ; fn-node-statep and the configuration's fn-cfgp from the relation
         ; instead of evaluating them per connection (PKT-455 (1)).
         (opened (fn-ocar-ocfg-open (fn-owner-ocfg state)
                                    (fn-owner-auth state)))
         (state (fn-owner-install-ocfg (cdr opened) state))
         (state (fn-owner-callback-install-effects (car opened) state))
         (state (f-put-global 'fn-owner-log-line
                              (fn-olog-connection-line (fn-owner-core state)
                                                       id nil)
                              state)))
    (if (fn-own-find-conn id (fn-own-conns (fn-owner-core state)))
        (value id)
      (value nil))))

(defthm fn-owner-callback-open-at-preserves-owner-bound
  (implies (boundp-global 'fn-owner state)
           (boundp-global 'fn-owner
             (mv-nth 2 (fn-owner-callback-open-at state))))
  :hints (("Goal" :in-theory
           (e/d (fn-owner-callback-open-at)
                (boundp-global put-global fn-owner-callback-install-effects
                 fn-owner-install-served-effects fn-olog-connection-line
                 fn-owner-auth)))))

(defun fn-owner-callback-open (state)
  (declare (xargs :stobjs state :guard (boundp-global 'fn-owner state)
                  :guard-hints (("Goal" :in-theory (disable boundp-global put-global
                           fn-owner-callback-install-effects
                           fn-owner-install-served-effects
                           fn-olog-connection-line fn-owner-auth)))))
  (let* ((working (fn-own-view (fn-owner-core state)))
         (state (fn-owner-callback-at-reader-view state)))
    (mv-let (erp val state)
      (fn-owner-callback-open-at state)
      (let ((state (fn-owner-callback-at-working-view working state)))
        (mv erp val state)))))

(defun fn-owner-callback-exposure-open (family address peer-octets state)
  (declare (xargs :stobjs state
                  :guard (and (boundp-global 'fn-owner state)
                              (fn-cbor-octet-listp peer-octets))
                  :guard-hints (("Goal" :in-theory (disable boundp-global put-global
                           fn-owner-callback-install-effects
                           fn-owner-install-served-effects
                           fn-olog-connection-line fn-owner-auth
                           fn-owner-callback-exposure-limits
                           fn-owner-exposure-state fn-owner-exposure-publicp
                           fn-owner-exposure-now fn-ocar-exp-open
                           fn-exp-open-id fn-exp-open-ocfg fn-exp-open-state
                           fn-exp-open-effects fn-exp-open-refusal)))))
  (let* ((peer (and peer-octets (fn-store-octets->string peer-octets)))
         (peer (if (equal peer :bad) nil peer))
         (before (fn-owner-core state))
         (id (fn-own-next-id before))
         ; fn-ocar-exp-open is fn-exp-open under the configured owner's
         ; relation (fn-ocar-exp-open-is-exp-open-under-ocl-relation,
         ; books/owner-open-carried.lisp): its reader arm opens through
         ; fn-ocar-ocfg-open, which evaluates no whole-state recognizer.
         (r (fn-ocar-exp-open (fn-owner-ocfg state) (fn-owner-exposure-state state)
                         (fn-owner-callback-exposure-limits state) (fn-owner-auth state)
                         peer (cons family address)
                         (fn-owner-exposure-now state)))
         (state (fn-owner-install-ocfg (fn-exp-open-ocfg r) state))
         (state (f-put-global 'fn-owner-exposure (fn-exp-open-state r) state)))
    (if (fn-exp-open-id r)
        (let* ((state (fn-owner-callback-install-effects (fn-exp-open-effects r) state))
               (state (f-put-global 'fn-owner-log-line
                                    (fn-olog-connection-line
                                     (fn-owner-core state) id
                                     (and peer peer-octets))
                                    state)))
          (value (fn-exp-open-id r)))
      (let* ((state (f-put-global 'fn-owner-effects nil state))
             (state (f-put-global 'fn-owner-output
                                  (fn-exp-open-refusal r) state))
             (state (f-put-global 'fn-owner-closep
                                  (and (fn-exp-open-refusal r) t) state))
             (state (f-put-global 'fn-owner-starttlsp nil state))
             (state (f-put-global 'fn-owner-submittedp nil state)))
        (value nil)))))

(defun fn-owner-callback-open-peer (peer-octets state)
  (declare (xargs :stobjs state
                  :guard (and (boundp-global 'fn-owner state)
                              (fn-cbor-octet-listp peer-octets))
                  :guard-hints (("Goal" :in-theory (disable boundp-global put-global
                           fn-owner-callback-install-effects
                           fn-owner-install-served-effects
                           fn-olog-connection-line fn-owner-auth)))))
  (let ((peer (fn-store-octets->string peer-octets)))
    (if (equal peer :bad)
        (value nil)
      (let* ((before (fn-owner-core state))
             (id (fn-own-next-id before))
             ; The owner's AUTHINFO policy, the same value fn-owner-callback-open
             ; pins into a reader.  A peer connection was opened with no
             ; policy at all, and the owner resolves a connection to a peer
             ; by source address alone (fn-owner-peer-name-for below), so on
             ; a box where a configured peer is on loopback that was every
             ; client: the operator's credential reached nothing.
             (opened (fn-ocfg-open-peer (fn-owner-ocfg state) peer
                                        (fn-owner-auth state)))
             (state (fn-owner-install-ocfg (cdr opened) state))
             (state (fn-owner-callback-install-effects (car opened) state))
             (state (f-put-global 'fn-owner-log-line
                                  (fn-olog-connection-line
                                   (fn-owner-core state) id peer-octets)
                                  state)))
        (if (fn-own-find-conn id (fn-own-conns (fn-owner-core state)))
            (value id)
          (value nil))))))

 ; Exact generic dispatcher arm, not a supplied owner-valid flag. The
 ; FN-ARENA argument is read by other dispatcher arms, never by :CLOSE.
(defthm fn-owner-callback-close-branch-unfolds
  (equal (fn-ocfg-step oc (list :close id) fn-arena)
         (fn-ocfg-close oc id))
  :hints (("Goal" :in-theory (enable fn-ocfg-step))))

(defun fn-owner-callback-close (id fn-arena state)
  (declare (ignore fn-arena)
           (xargs :stobjs (state fn-arena) :guard (boundp-global 'fn-owner state)
                  :guard-hints (("Goal" :in-theory (disable boundp-global put-global
                           fn-owner-callback-install-effects
                           fn-owner-install-served-effects
                           fn-olog-connection-line fn-owner-auth)))))
  (let* ((state (fn-owner-install-ocfg
                (fn-ocfg-close (fn-owner-ocfg state) id) state))
         ;; Lane credits: the connection's body and queued submissions are
         ;; freed with it; what the committer took and the batch in flight
         ;; keep their credit (fn-mca-close-keeps-what-the-commit-owns).
         (state (fn-owner-put-credits (fn-mca-close (fn-owner-credits state) id) state)))
    (value :closed)))

(defun fn-owner-callback-fault (id state)
  (declare (xargs :stobjs state :guard (boundp-global 'fn-owner state)
                  :guard-hints (("Goal" :in-theory (disable boundp-global put-global
                           fn-owner-callback-install-effects
                           fn-owner-install-served-effects
                           fn-olog-connection-line fn-owner-auth)))))
  (let* ((owner (fn-owner-core state))
         (knownp (if (fn-own-find-conn id (fn-own-conns owner)) t nil))
         (result (fn-ocfg-fault (fn-owner-ocfg state) id))
         (state (fn-owner-install-ocfg (cdr result) state))
         (state (fn-owner-callback-install-effects (car result) state))
         ;; Lane credits: as a close (fn-mca-close-keeps-what-the-commit-owns).
         (state (fn-owner-put-credits (fn-mca-close (fn-owner-credits state) id) state)))
    (value (if knownp :faulted :unknown))))
