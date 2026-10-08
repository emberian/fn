; History initialization is a startup operation. Served sync has no reload arm.
(in-package "ACL2")
(include-book "history-served-sync")
(include-book "history-served-cache")
(include-book "state-globals")
(include-book "owner-state-accessors")
(include-book "owner-obligation-state")

(defun fn-host-hist-reloadp (state)
  (declare (xargs :stobjs state :guard t))
  (and (boundp-global 'fn-store-sn-hist-reload state)
       (if (f-get-global 'fn-store-sn-hist-reload state) t nil)))

(defun fn-host-hist-startup (store fn-hist state)
  (declare (xargs :stobjs (fn-hist state) :guard t))
  (let* ((fn-hist (fn-hist-load (true-list-fix (fn-sf-records (fn-sn-files store)))
                                0 fn-hist))
         (state (f-put-global 'fn-store-sn-hist-reload nil state)))
    (mv fn-hist state)))

(defun fn-host-hist-sync (store fn-hist state)
  (declare (xargs :stobjs (fn-hist state) :guard t))
  (if (fn-host-hist-reloadp state)
      (prog2$ (er hard? 'fn-host-hist-sync "History startup synchronization missing.")
              (mv fn-hist state))
    (let ((fn-hist (fn-hist-served-sync (fn-sn-files store) fn-hist)))
      (mv fn-hist state))))

; This is the startup entry called by fnn-owner-history-sync-first.
(defun fn-owner-history-startup (fn-hist state)
  (declare (xargs :stobjs (fn-hist state)
                  :guard (boundp-global 'fn-owner state)))
  (mv-let (fn-hist state)
      (fn-host-hist-startup (fn-owner-store state) fn-hist state)
    (let ((state (fn-owner-history-cache-startup fn-hist state)))
      (mv nil :loaded fn-hist state))))

(defthm fn-host-hist-startup-consumes-reload
  (not (fn-host-hist-reloadp
        (mv-nth 1 (fn-host-hist-startup store hist st)))))

(defthm fn-owner-history-startup-consumes-reload
  (not (fn-host-hist-reloadp
        (mv-nth 3 (fn-owner-history-startup fn-hist state))))
  :hints (("Goal" :in-theory (enable fn-owner-history-cache-startup
                                    fn-owner-history-cache-put))))

(defthm fn-host-hist-sync-preserves-state
  (equal (mv-nth 1 (fn-host-hist-sync store fn-hist state)) state))

(defthm fn-host-hist-reloadp-of-other-global-put
  (implies (not (equal key 'fn-store-sn-hist-reload))
           (equal (fn-host-hist-reloadp (f-put-global key value st))
                  (fn-host-hist-reloadp st))))

(defthm fn-owner-install-ocfg-preserves-history-ready
  (equal (fn-host-hist-reloadp (fn-owner-install-ocfg oc state))
         (fn-host-hist-reloadp state)))

; The host sends these events here. Completion, recovery and I/O have
; separate entries; the generic model dispatcher is not a served capability.
(defun fn-ocfg-served-eventp (event)
  (declare (xargs :guard t))
  (and (consp event)
       (if (member-eq (car event)
                     '(:open :advance :reconfigure :take :control-submit
                       :legacy-control-submit :bp-transit-submit
                       :operator-submit :feed-conn)) t nil)))

(defun fn-ocfg-served-step (oc event fn-arena)
  (declare (ignore fn-arena) (xargs :stobjs fn-arena
                  :guard (and (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
                              (fn-ocfg-eventp oc event))
                  :guard-hints (("Goal" :in-theory (enable fn-ocfg-eventp
                                                          fn-own-eventp)))))
  (let ((o (fn-ocfg-owner oc)))
    (case (car event)
      (:open (cdr (fn-ocfg-open oc (cadr event))))
      (:advance (fn-ocfg-advance oc (cadr event)))
      (:reconfigure (fn-ocfg-reconfigure oc (cadr event) (caddr event)))
      (:take (if (fn-ocfg-staged oc) oc
               (fn-ocfg-with-owner oc (fn-own-take-submission o))))
      (:control-submit
       (fn-ocfg-with-owner oc (fn-own-control-submit o (cadr event) (caddr event)
                                                    (cadddr event))))
      (:legacy-control-submit
       (fn-ocfg-with-owner oc (fn-own-legacy-control-submit
                              o (cadr event) (caddr event) (cadddr event))))
      (:bp-transit-submit
       (fn-ocfg-with-owner oc (fn-own-bp-transit-submit
                              o (cadr event) (caddr event) (cadddr event)
                              (car (cddddr event)) (cadr (cddddr event))
                              (caddr (cddddr event)))))
      (:operator-submit
       (fn-ocfg-with-owner oc (fn-own-operator-submit
                              o (cadr event) (caddr event) (cadddr event)
                              (car (cddddr event)))))
      (:feed-conn
       (fn-ocfg-with-owner oc (fn-own-feed-connect o (cadr event) (caddr event)
                                                  (cadddr event))))
      (otherwise (prog2$ (er hard? 'fn-ocfg-served-step
                              "Event belongs to a separate owner entry.") oc)))))

(defthm fn-ocfg-served-step-is-step
  (implies (fn-ocfg-served-eventp event)
           (equal (fn-ocfg-served-step oc event fn-arena)
                  (fn-ocfg-step oc event fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-served-eventp fn-ocfg-served-step
                                    fn-ocfg-step fn-ocfg-pass fn-own-step)
                                   (fn-ocfg-open fn-ocfg-advance fn-ocfg-reconfigure
                                    fn-own-take-submission fn-own-control-submit
                                    fn-own-legacy-control-submit fn-own-bp-transit-submit
                                    fn-own-operator-submit fn-own-feed-connect)))))

(in-theory (disable fn-ocfg-served-eventp fn-ocfg-served-step))

(defun fn-owner-step (event fn-arena state)
  (declare (xargs :stobjs (state fn-arena) :guard (and (boundp-global 'fn-owner state)
                              (fn-sn-statep (fn-own-store (fn-ocfg-owner (fn-owner-ocfg state))))
                              (fn-ocfg-eventp (fn-owner-ocfg state) event))))
  (let ((state (fn-owner-install-ocfg
                (fn-ocfg-served-step (fn-owner-ocfg state) event fn-arena) state)))
    state))


(defthm fn-owner-step-preserves-history-ready
  (equal (fn-host-hist-reloadp (fn-owner-step event arena st))
         (fn-host-hist-reloadp st))
  :hints (("Goal" :in-theory (enable fn-owner-step))))

(in-theory (disable fn-host-hist-reloadp fn-host-hist-startup
                    fn-host-hist-sync fn-owner-history-startup fn-owner-step))

(defthm fn-host-hist-startup-establishes-served-prefix
  (<= (fn-hist-served-base (fn-sn-files store))
      (fn-hist-count (mv-nth 0 (fn-host-hist-startup store hist st))))
  :hints (("Goal" :use ((:instance fn-hist-served-base-is-within-record-count
                                   (files (fn-sn-files store))))
           :in-theory (e/d (fn-host-hist-startup fn-sf-records-count fn-sbud-used)
                           (fn-sf-records-count-is-used-by-definition)))))

(defthm fn-owner-history-startup-establishes-cache-ready
  (fn-owner-history-cache-statep
   (fn-hist-count (mv-nth 2 (fn-owner-history-startup hist st)))
   (mv-nth 3 (fn-owner-history-startup hist st)))
  :hints (("Goal"
           :use ((:instance fn-owner-history-cache-startup-establishes-ready
                            (hist (mv-nth 0 (fn-host-hist-startup
                                             (fn-owner-store st) hist st)))
                            (st (mv-nth 1 (fn-host-hist-startup
                                           (fn-owner-store st) hist st)))))
           :in-theory (enable fn-owner-history-startup))))

(defthm fn-owner-step-preserves-history-caches
  (equal (fn-owner-history-cache-statep count (fn-owner-step event arena st))
         (fn-owner-history-cache-statep count st))
  :hints (("Goal" :in-theory (e/d (fn-owner-step fn-owner-install-ocfg) (put-global)))))
