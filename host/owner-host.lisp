; Experimental owner bridge: :program wrappers over the proved fn-own machine.
;
; tools/run_owner.py drives one owner per store through these entry points.
; Every wrapper is one fn-own-step (or fn-own-read-step) over the global
; `fn-owner`; the host never rebuilds owner, store or session state itself.
; Marshaling reuses host/store-host.lisp (decimal octets in, symbols and
; naturals out) and host/reader-host.lisp (effect octets out).  Wire framing
; per connection stays in the host globals as in the reader host: it is
; bounded by fn-wire-initial-state, not by the owner model.
(in-package "ACL2")
(include-book "../books/owner")

(defun fn-owner-state (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-owner state)))

; The process root.  A decoded observed image opens through
; fn-sn-open-observed exactly as host/store-node-host.lisp:27 does; the owner
; is started over that state (fn-own-open-observed-start-relation).
(defun fn-owner-recover (octet-records frontier max-conns state)
  (declare (xargs :stobjs state :mode :program))
  (let ((records (fn-store-decode-records octet-records)))
    (if (or (equal records :bad) (not (natp max-conns)))
        (value :fault)
      (let ((opened (fn-sn-open-observed *fn-store-groups*
                                         *fn-store-capacity* frontier records)))
        (if (and (fn-sn-open-okp opened)
                 (equal (fn-sf-phase (fn-sn-files (fn-sn-open-state opened)))
                        :recovering))
            (let* ((state (f-put-global 'fn-owner
                                        (fn-own-start (fn-sn-open-state opened)
                                                      max-conns)
                                        state))
                   (state (f-put-global 'fn-owner-wires nil state)))
              (value :recovering))
          (value :fault))))))

(defun fn-owner-store (state)
  (declare (xargs :stobjs state :mode :program))
  (fn-own-store (f-get-global 'fn-owner state)))

(defun fn-owner-node (state)
  (declare (xargs :stobjs state :mode :program))
  (fn-sn-node (fn-owner-store state)))

(defun fn-owner-step (event state)
  (declare (xargs :stobjs state :mode :program))
  (let ((state (f-put-global 'fn-owner
                             (fn-own-step (f-get-global 'fn-owner state) event)
                             state)))
    state))

; -----------------------------------------------------------------------------
; The transaction path: the same observations run_store.py reports, each one
; a (:store ...) owner event.

(defun fn-owner-io (operation result state)
  (declare (xargs :stobjs state :mode :program))
  (let ((state (fn-owner-step (list :store (list :io operation result)) state)))
    (value (fn-sf-phase (fn-sn-files (fn-owner-store state))))))

(defun fn-owner-prepare (msgid-octets payload group-codes id-octets
                          subject-octets evidence-octets charge state)
  (declare (xargs :stobjs state :mode :program))
  (let ((groups (fn-store-groups-from-codes group-codes))
        (s (fn-owner-store state)))
    (if (or (not (fn-store-msgid-octetsp msgid-octets))
            (not (fn-octet-listp payload)) (> (len payload) *fn-store-max-payload*)
            (equal groups :bad) (null groups)
            (not (fn-store-text-octetsp id-octets))
            (not (fn-store-text-octetsp subject-octets))
            (not (fn-store-text-octetsp evidence-octets)) (not (posp charge)))
        (value :invalid)
      (let* ((node (fn-sn-node s))
             (msgid (fn-store-octets->string msgid-octets))
             (existing (fn-store-article-match msgid payload groups node)))
        (if existing
            (value existing)
          (let* ((record (fn-record-make (len (fn-sf-records (fn-sn-files s)))
                                         (fn-state-next-txid (fn-node-acceptance node))
                                         (fn-state-next-txid (fn-node-acceptance node))
                                         msgid payload groups
                                         (fn-store-octets->string id-octets)
                                         (fn-store-octets->string subject-octets)
                                         (fn-store-octets->string evidence-octets)
                                         charge))
                 (state (fn-owner-step (list :store (list :prepare record)) state)))
            (if (equal (fn-owner-store state) s)
                (value :refused)
              (value :prepared))))))))

(defun fn-owner-refuse-reservation (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((before (fn-owner-store state))
         (files (fn-sn-files before))
         (state (fn-owner-step
                 (list :store (list :refuse-reservation (1- (fn-sf-frontier files))))
                 state))
         (next (fn-owner-store state)))
    (if (and (equal (fn-sf-phase files) :reserved)
             (not (equal next before))
             (equal (fn-sf-phase (fn-sn-files next)) :ready))
        (value :refused)
      (value :fault))))

(defun fn-owner-known-abort (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((before (fn-owner-store state))
         (files (fn-sn-files before))
         (state (fn-owner-step (list :store (list :known-abort)) state))
         (next (fn-owner-store state)))
    (if (and (member-equal (fn-sf-phase files)
                           '(:record-staged :record-data-durable))
             (not (equal next before))
             (equal (fn-sf-phase (fn-sn-files next)) :ready))
        (value :aborted)
      (value :fault))))

(defun fn-owner-pending-octets (state)
  (declare (xargs :stobjs state :mode :program))
  (let ((record (fn-sf-record-candidate (fn-sn-files (fn-owner-store state)))))
    (value (if record (fn-record-encode record) nil))))

; Completion is the owner's (:complete) event: fn-sn-finish consumed once,
; its pair appended to the ledger once (fn-own-completion-consumed-once).
(defun fn-owner-finish (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((before (f-get-global 'fn-owner state))
         (before-files (fn-sn-files (fn-own-store before)))
         (state (fn-owner-step (list :complete) state))
         (after (f-get-global 'fn-owner state))
         (after-files (fn-sn-files (fn-own-store after))))
    (if (and (equal (fn-sf-phase before-files) :completing)
             (equal (fn-sf-phase after-files) :ready)
             (equal (len (fn-own-ledger after))
                    (1+ (len (fn-own-ledger before)))))
        (value :durable)
      (value :fault))))

(defun fn-owner-begin (id state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((before (f-get-global 'fn-owner state))
         (state (fn-owner-step (list :begin id) state)))
    (value (if (equal (f-get-global 'fn-owner state) before) :refused :begun))))

(defun fn-owner-next-txid (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-state-next-txid (fn-node-acceptance (fn-owner-node state)))))

(defun fn-owner-article-count (state)
  (declare (xargs :stobjs state :mode :program))
  (value (len (fn-state-articles (fn-node-acceptance (fn-owner-node state))))))

(defun fn-owner-existing-action (msgid-octets payload group-codes state)
  (declare (xargs :stobjs state :mode :program))
  (let ((groups (fn-store-groups-from-codes group-codes)))
    (if (or (not (fn-store-msgid-octetsp msgid-octets))
            (not (fn-octet-listp payload)) (equal groups :bad) (null groups))
        (value :absent)
      (let ((action (fn-store-article-match
                     (fn-store-octets->string msgid-octets) payload groups
                     (fn-owner-node state))))
        (value (if action action :absent))))))

; -----------------------------------------------------------------------------
; Connections.  One wire state per connection lives in `fn-owner-wires`.

(defun fn-owner-version (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-own-view-version (fn-own-view (f-get-global 'fn-owner state)))))

(defun fn-owner-conn-version (id state)
  (declare (xargs :stobjs state :mode :program))
  (let ((conn (fn-own-find-conn id (fn-own-conns (f-get-global 'fn-owner state)))))
    (value (if conn (fn-own-conn-version conn) nil))))

(defun fn-owner-connection-versions (conns)
  (declare (xargs :mode :program))
  (if (consp conns)
      (cons (fn-own-conn-id (car conns))
            (cons (fn-own-conn-version (car conns))
                  (fn-owner-connection-versions (cdr conns))))
    nil))

(defun fn-owner-connections (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-owner-connection-versions
          (fn-own-conns (f-get-global 'fn-owner state)))))

; Open pins the committed view (fn-own-open).  The greeting is the fixed
; reader greeting; a refused open (bound reached) installs no connection and
; returns NIL so the host closes the socket without a reply.
(defun fn-owner-open (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((before (f-get-global 'fn-owner state))
         (id (fn-own-next-id before))
         (state (fn-owner-step (list :open) state)))
    (if (fn-own-find-conn id (fn-own-conns (f-get-global 'fn-owner state)))
        (let* ((state (f-put-global 'fn-owner-wires
                                    (cons (cons id (fn-wire-initial-state 510 8192))
                                          (f-get-global 'fn-owner-wires state))
                                    state))
               (state (fn-reader-install-effects
                       (list (fn-nntp-reply-effect *fn-reader-greeting*)) state)))
          (value id))
      (value nil))))

(defun fn-owner-set-wire (id wire wires)
  (declare (xargs :mode :program))
  (if (consp wires)
      (if (equal (car (car wires)) id)
          (cons (cons id wire) (cdr wires))
        (cons (car wires) (fn-owner-set-wire id wire (cdr wires))))
    nil))

(defun fn-owner-drop-wire (id wires)
  (declare (xargs :mode :program))
  (if (consp wires)
      (if (equal (car (car wires)) id)
          (fn-owner-drop-wire id (cdr wires))
        (cons (car wires) (fn-owner-drop-wire id (cdr wires))))
    nil))

; One call consumes at most one wire event and runs exactly one
; fn-own-read-step against the connection's pinned archive
; (fn-own-reader-sees-pinned-prefix-replay).  Effects go out through the
; reader host's globals; the unconsumed suffix is returned to the host.
(defun fn-owner-chunk (id octets state)
  (declare (xargs :stobjs state :mode :program))
  (let ((entry (assoc-equal id (f-get-global 'fn-owner-wires state))))
    (if (not entry)
        (value :unknown)
      (let* ((next (fn-wire-next (cdr entry) octets))
             (wire (fn-wire-next-state next))
             (event (fn-wire-next-event next))
             (suffix (fn-wire-next-unconsumed next))
             (owner (f-get-global 'fn-owner state))
             (result (if event
                         (fn-own-read-step owner id event)
                       (cons nil owner)))
             (effects (if (fn-reader-wire-closedp wire)
                          (append (car result) (list (fn-nntp-close-effect)))
                        (car result)))
             (state (f-put-global 'fn-owner (cdr result) state))
             (state (f-put-global 'fn-owner-wires
                                  (fn-owner-set-wire id wire
                                                     (f-get-global 'fn-owner-wires state))
                                  state))
             (state (fn-reader-install-effects effects state))
             (state (f-put-global 'fn-reader-suffix suffix state)))
        (value :ok)))))

(defun fn-owner-close (id state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((state (fn-owner-step (list :close id) state))
         (state (f-put-global 'fn-owner-wires
                              (fn-owner-drop-wire id (f-get-global 'fn-owner-wires state))
                              state)))
    (value :closed)))

(defun fn-owner-advance (id state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((state (fn-owner-step (list :advance id) state)))
    (fn-owner-conn-version id state)))

; -----------------------------------------------------------------------------
; Clock observations and group facts

(defun fn-owner-observe (monotonic wall wall-error has-wall state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((before (f-get-global 'fn-owner state))
         (obs (fn-clock-observation monotonic wall wall-error has-wall))
         (state (fn-owner-step (list :observe obs) state)))
    (value (if (equal (f-get-global 'fn-owner state) before) :rejected :observed))))

(defun fn-owner-declare-group (name-octets state)
  (declare (xargs :stobjs state :mode :program))
  (if (not (fn-store-text-octetsp name-octets))
      (value :invalid)
    (let* ((before (f-get-global 'fn-owner state))
           (state (fn-owner-step
                   (list :declare-group (fn-store-octets->string name-octets))
                   state)))
      (value (if (equal (f-get-global 'fn-owner state) before) :refused :declared)))))

(defun fn-owner-group-facts (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-own-replay-facts (fn-own-facts (f-get-global 'fn-owner state)))))
