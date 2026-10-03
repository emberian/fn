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

(defun fn-owner-callback-exposure-limits (fn-owner-st state)
  (declare (xargs :stobjs (fn-owner-st state) :guard (fn-owner-boundp fn-owner-st)))
  (fn-exp-limits (fn-cfg-value (fn-owner-config fn-owner-st))
                 (fn-own-max-conns (fn-owner-core fn-owner-st))
                 (fn-owner-exposure-publicp state)
                 (fn-auth-config-requiredp (fn-owner-auth state))))

(defun fn-owner-callback-at-reader-view (fn-owner-st state)
  (declare (xargs :stobjs (fn-owner-st state) :guard (fn-owner-boundp fn-owner-st)))
  (let ((views (fn-owner-reader-views state)))
    (if (consp views)
        (fn-owner-install-ocfg (fn-ocfg-at-reader-view (fn-owner-ocfg fn-owner-st) views)
                               fn-owner-st)
      fn-owner-st)))

(defthm fn-owner-callback-reader-view-preserves-owner-bound
  (implies (fn-owner-boundp fn-owner-st)
           (fn-owner-boundp (fn-owner-callback-at-reader-view fn-owner-st state)))
  :hints (("Goal"
           :use ((:instance 
                  (oc (fn-ocfg-at-reader-view (fn-owner-ocfg fn-owner-st)
                                             (fn-owner-reader-views state)))))
           :in-theory (e/d (fn-owner-callback-at-reader-view)
                           (boundp-global )))))

(defun fn-owner-callback-at-working-view (working fn-owner-st state)
  (declare (xargs :stobjs (fn-owner-st state) :guard (fn-owner-boundp fn-owner-st)))
  (if (consp (fn-owner-reader-views state))
      (fn-owner-install-ocfg (fn-ocfg-with-view (fn-owner-ocfg fn-owner-st) working) fn-owner-st)
    fn-owner-st))

(defthm fn-owner-callback-working-view-preserves-owner-bound
  (implies (fn-owner-boundp fn-owner-st)
           (fn-owner-boundp (fn-owner-callback-at-working-view working fn-owner-st state)))
  :hints (("Goal"
           :use ((:instance 
                  (oc (fn-ocfg-with-view (fn-owner-ocfg fn-owner-st) working))))
           :in-theory (e/d (fn-owner-callback-at-working-view)
                           (boundp-global )))))

(defun fn-owner-callback-open-at (fn-owner-st state)
  (declare (xargs :stobjs (fn-owner-st state) :guard (fn-owner-boundp fn-owner-st)
                  :guard-hints (("Goal" :in-theory (disable boundp-global put-global
                           fn-owner-callback-install-effects
                           fn-owner-install-served-effects
                           fn-olog-connection-line fn-owner-auth)))))
  (let* ((before (fn-owner-core fn-owner-st))
         (id (fn-own-next-id before))
         ; fn-ocar-ocfg-open (books/owner-open-carried.lisp) is fn-ocfg-open
         ; under the configured owner's relation
         ; (fn-ocar-ocfg-open-is-ocfg-open-under-ocl-relation): the greeting
         ; takes the view archive's fn-statep, the store node's
         ; fn-node-statep and the configuration's fn-cfgp from the relation
         ; instead of evaluating them per connection (PKT-455 (1)).
         (opened (fn-ocar-ocfg-open (fn-owner-ocfg fn-owner-st)
                                    (fn-owner-auth state)))
         (fn-owner-st (fn-owner-install-ocfg (cdr opened) fn-owner-st))
         (state (fn-owner-callback-install-effects (car opened) state))
         (state (f-put-global 'fn-owner-log-line
                              (fn-olog-connection-line (fn-owner-core fn-owner-st)
                                                       id nil)
                              state)))
    (if (fn-own-find-conn id (fn-own-conns (fn-owner-core fn-owner-st)))
        (mv nil id fn-owner-st state)
      (mv nil nil fn-owner-st state))))

(defthm fn-owner-callback-open-at-preserves-owner-bound
  (implies (fn-owner-boundp fn-owner-st)
           (fn-owner-boundp (mv-nth 2 (fn-owner-callback-open-at fn-owner-st state))))
  :hints (("Goal" :in-theory
           (e/d (fn-owner-callback-open-at)
                (boundp-global put-global fn-owner-callback-install-effects
                 fn-owner-install-served-effects fn-olog-connection-line
                 fn-owner-auth)))))

(defun fn-owner-callback-open (fn-owner-st state)
  (declare (xargs :stobjs (fn-owner-st state) :guard (fn-owner-boundp fn-owner-st)
                  :guard-hints (("Goal" :in-theory (disable boundp-global put-global
                           fn-owner-callback-install-effects
                           fn-owner-install-served-effects
                           fn-olog-connection-line fn-owner-auth)))))
  (let* ((working (fn-own-view (fn-owner-core fn-owner-st)))
         (fn-owner-st (fn-owner-callback-at-reader-view fn-owner-st state)))
    (mv-let (erp val fn-owner-st state)
      (fn-owner-callback-open-at fn-owner-st state)
      (let ((fn-owner-st (fn-owner-callback-at-working-view working fn-owner-st state)))
        (mv erp val fn-owner-st state)))))

(defun fn-owner-callback-exposure-open (family address peer-octets fn-owner-st state)
  (declare (xargs :stobjs (fn-owner-st state)
                  :guard (and (fn-owner-boundp fn-owner-st)
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
         (before (fn-owner-core fn-owner-st))
         (id (fn-own-next-id before))
         ; fn-ocar-exp-open is fn-exp-open under the configured owner's
         ; relation (fn-ocar-exp-open-is-exp-open-under-ocl-relation,
         ; books/owner-open-carried.lisp): its reader arm opens through
         ; fn-ocar-ocfg-open, which evaluates no whole-state recognizer.
         (r (fn-ocar-exp-open (fn-owner-ocfg fn-owner-st) (fn-owner-exposure-state state)
                         (fn-owner-callback-exposure-limits fn-owner-st state) (fn-owner-auth state)
                         peer (cons family address)
                         (fn-owner-exposure-now fn-owner-st)))
         (fn-owner-st (fn-owner-install-ocfg (fn-exp-open-ocfg r) fn-owner-st))
         (state (f-put-global 'fn-owner-exposure (fn-exp-open-state r) state)))
    (if (fn-exp-open-id r)
        (let* ((state (fn-owner-callback-install-effects (fn-exp-open-effects r) state))
               (state (f-put-global 'fn-owner-log-line
                                    (fn-olog-connection-line
                                     (fn-owner-core fn-owner-st) id
                                     (and peer peer-octets))
                                    state)))
          (mv nil (fn-exp-open-id r) fn-owner-st state))
      (let* ((state (f-put-global 'fn-owner-effects nil state))
             (state (f-put-global 'fn-owner-output
                                  (fn-exp-open-refusal r) state))
             (state (f-put-global 'fn-owner-closep
                                  (and (fn-exp-open-refusal r) t) state))
             (state (f-put-global 'fn-owner-starttlsp nil state))
             (state (f-put-global 'fn-owner-submittedp nil state)))
        (mv nil nil fn-owner-st state)))))

(defun fn-owner-callback-open-peer (peer-octets fn-owner-st state)
  (declare (xargs :stobjs (fn-owner-st state)
                  :guard (and (fn-owner-boundp fn-owner-st)
                              (fn-cbor-octet-listp peer-octets))
                  :guard-hints (("Goal" :in-theory (disable boundp-global put-global
                           fn-owner-callback-install-effects
                           fn-owner-install-served-effects
                           fn-olog-connection-line fn-owner-auth)))))
  (let ((peer (fn-store-octets->string peer-octets)))
    (if (equal peer :bad)
        (mv nil nil fn-owner-st state)
      (let* ((before (fn-owner-core fn-owner-st))
             (id (fn-own-next-id before))
             ; The owner's AUTHINFO policy, the same value fn-owner-callback-open
             ; pins into a reader.  A peer connection was opened with no
             ; policy at all, and the owner resolves a connection to a peer
             ; by source address alone (fn-owner-peer-name-for below), so on
             ; a box where a configured peer is on loopback that was every
             ; client: the operator's credential reached nothing.
             (opened (fn-ocfg-open-peer (fn-owner-ocfg fn-owner-st) peer
                                        (fn-owner-auth state)))
             (fn-owner-st (fn-owner-install-ocfg (cdr opened) fn-owner-st))
             (state (fn-owner-callback-install-effects (car opened) state))
             (state (f-put-global 'fn-owner-log-line
                                  (fn-olog-connection-line
                                   (fn-owner-core fn-owner-st) id peer-octets)
                                  state)))
        (if (fn-own-find-conn id (fn-own-conns (fn-owner-core fn-owner-st)))
            (mv nil id fn-owner-st state)
          (mv nil nil fn-owner-st state))))))

 ; Exact generic dispatcher arm, not a supplied owner-valid flag. The
 ; FN-ARENA argument is read by other dispatcher arms, never by :CLOSE.
(defthm fn-owner-callback-close-branch-unfolds
  (equal (fn-ocfg-step oc (list :close id) fn-arena)
         (fn-ocfg-close oc id))
  :hints (("Goal" :in-theory (enable fn-ocfg-step))))

(defun fn-owner-callback-close (id fn-arena fn-owner-st state)
  (declare (ignore fn-arena)
           (xargs :stobjs (fn-owner-st state fn-arena) :guard (fn-owner-boundp fn-owner-st)
                  :guard-hints (("Goal" :in-theory (disable boundp-global put-global
                           fn-owner-callback-install-effects
                           fn-owner-install-served-effects
                           fn-olog-connection-line fn-owner-auth)))))
  (let* ((fn-owner-st (fn-owner-install-ocfg
                (fn-ocfg-close (fn-owner-ocfg fn-owner-st) id) fn-owner-st))
         ;; Lane credits: the connection's body and queued submissions are
         ;; freed with it; what the committer took and the batch in flight
         ;; keep their credit (fn-mca-close-keeps-what-the-commit-owns).
         (state (fn-owner-put-credits (fn-mca-close (fn-owner-credits state) id) state)))
    (mv nil :closed fn-owner-st state)))

(defun fn-owner-callback-fault (id fn-owner-st state)
  (declare (xargs :stobjs (fn-owner-st state) :guard (fn-owner-boundp fn-owner-st)
                  :guard-hints (("Goal" :in-theory (disable boundp-global put-global
                           fn-owner-callback-install-effects
                           fn-owner-install-served-effects
                           fn-olog-connection-line fn-owner-auth)))))
  (let* ((owner (fn-owner-core fn-owner-st))
         (knownp (if (fn-own-find-conn id (fn-own-conns owner)) t nil))
         (result (fn-ocfg-fault (fn-owner-ocfg fn-owner-st) id))
         (fn-owner-st (fn-owner-install-ocfg (cdr result) fn-owner-st))
         (state (fn-owner-callback-install-effects (car result) state))
         ;; Lane credits: as a close (fn-mca-close-keeps-what-the-commit-owns).
         (state (fn-owner-put-credits (fn-mca-close (fn-owner-credits state) id) state)))
    (mv nil (if knownp :faulted :unknown) fn-owner-st state)))
