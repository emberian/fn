; The listener set of `bp-node serve' (specs/bp-node-machine.md 9.1).
;
; The loopback trust profile names a neighbour by the listener its session
; arrives on (`fn-bpaj-session-principal', books/bp-session-admission.lisp):
; a boundary's (NAME "bp-boundary-listener" "127.0.0.1" PORT) row.  A node
; with several admitted boundaries therefore needs a listener per boundary
; port, and nothing else.  This book answers that set from the live
; configuration, so the host binds exactly the ports on which some
; configuration row can admit a session, and no port on which none can.
;
; The answer is an alist (PORT . NAME), one entry per port, for each
; listener row whose port admits exactly one boundary (the singleton
; `fn-bpaj-loopback-candidates' the admission itself selects by).  A port
; two boundaries share admits nobody (:ambiguous-peer), so it is not in the
; set.  The host binds `fn-bpaj-listener-ports'.
(in-package "ACL2")
(include-book "bp-session-admission")
(include-book "def-loop")
(set-verify-guards-eagerness 0)

(defun fn-bpaj-listener-row-portp (port)
  (declare (xargs :guard t))
  (and (fn-record-uint32p port) (natp port) (< 0 port) (<= port 65535)))

(verify-guards fn-bpaj-listener-row-portp)

; The rows are operator data with no fixed cap (D27): the two walks below
; execute by loops (lane depth-debt, PRF-919), (mbe :logic <the recursion,
; unchanged> :exec <a loop>).  The listener rows are a right fold (each
; row's test reads the suffix's answer), folded over the reversed rows.
(def-loop fn-bpaj-listener-rows (rows all)
  :shape :foldr :over rows :elt r
  :combine (let* ((row r) (name (fn-cfg-row-a row)) (port (fn-cfg-row-n row)))
                 (if (and (equal (fn-cfg-row-b row) "bp-boundary-listener")
                          (equal (fn-cfg-row-c row) "127.0.0.1")
                          (fn-bpaj-listener-row-portp port)
                          (equal (fn-bpaj-loopback-candidates all all port) (list name))
                          (not (assoc-equal port acc)))
                     (cons (cons port name) acc)
                     acc))
  :init nil
  :rev fn-ag-rev-onto
  :loop-guard (alistp acc))

(defun fn-bpaj-listener-set (cfg)
  (declare (xargs :guard t))
  (if (fn-cfgp cfg)
      (let ((rows (fn-cfg-peers (fn-cfg-value cfg))))
        (fn-bpaj-listener-rows rows rows))
    nil))

(def-loop fn-bpaj-listener-port-list (set)
  :shape :map :over set :elt s
  :body (if (consp s) (car s) nil))

; The host's question: the ports `bp-node serve' binds.
(defun fn-bpaj-listener-ports (cfg)
  (declare (xargs :guard t))
  (fn-bpaj-listener-port-list (fn-bpaj-listener-set cfg)))

; The boundary a bound port admits.
(defun fn-bpaj-listener-name (cfg port)
  (declare (xargs :guard t))
  (let ((entry (assoc-equal port (fn-bpaj-listener-set cfg))))
    (if (consp entry) (cdr entry) nil)))

(defun fn-bpaj-loopback-channel (port)
  (declare (xargs :guard t))
  (list :tcp4 '(127 0 0 1) port '(127 0 0 1)))

(local (defthm alistp-of-listener-rows
  (alistp (fn-bpaj-listener-rows rows all))))

(local (defthm listener-rows-entry
  (implies (assoc-equal port (fn-bpaj-listener-rows rows all))
           (and (fn-bpaj-listener-row-portp port)
                (equal (fn-bpaj-loopback-candidates all all port)
                       (list (cdr (assoc-equal port
                                               (fn-bpaj-listener-rows rows all)))))))
  :hints (("Goal" :in-theory (disable fn-bpaj-loopback-candidates
                                      fn-bpaj-listener-row-portp)))))

(local (defthm member-port-list-is-assoc
  (implies (alistp set)
           (iff (member-equal port (fn-bpaj-listener-port-list set))
                (assoc-equal port set)))))

(local (defthm listener-set-entry
  (implies (member-equal port (fn-bpaj-listener-ports cfg))
           (and (fn-cfgp cfg)
                (fn-bpaj-listener-row-portp port)
                (equal (fn-bpaj-loopback-candidates
                        (fn-cfg-peers (fn-cfg-value cfg))
                        (fn-cfg-peers (fn-cfg-value cfg)) port)
                       (list (fn-bpaj-listener-name cfg port)))))
  :hints (("Goal" :in-theory (disable fn-bpaj-loopback-candidates
                                      fn-bpaj-listener-row-portp
                                      fn-bpaj-listener-rows)))))

; KEYSTONE.  Every session accepted on a bound listener is judged under
; exactly that listener's boundary row: admitted as that boundary when the
; announced EID is the boundary's transport-bp EID, otherwise refused
; :eid-mismatch.  It is never :ambiguous-peer or :no-trust-profile, so two
; boundaries on distinct ports never make each other ambiguous.  The host
; binds `fn-bpaj-listener-ports' (host/native/bp-node.lisp
; `fnn-bpnode-bind-listeners') and each session's admission is the call in
; `fnn-bp-deliver-node' (host/bp-native-app-host.lisp
; `fn-owner-bp-tcpcl-ingress').
(defthm fn-bpaj-listener-session-is-admitted-under-its-row
  (implies (and (member-equal port (fn-bpaj-listener-ports cfg))
                (fn-bpp-eidp announced))
           (equal (fn-bpaj-session-principal
                   cfg (fn-bpaj-loopback-channel port) announced)
                  (if (fn-bpaj-unique-boundary-rowp
                       (fn-cfg-peers (fn-cfg-value cfg))
                       (fn-bpaj-listener-name cfg port)
                       "transport-bp" (fn-bpaj-eid-text announced) 0)
                      (list :admitted
                            (fn-record-string-octets
                             (fn-bpaj-listener-name cfg port))
                            (fn-cfg-generation cfg))
                    (list :refused :eid-mismatch))))
  :hints (("Goal" :in-theory (disable fn-bpaj-listener-ports
                                      fn-bpaj-listener-name
                                      fn-bpaj-loopback-candidates
                                      fn-bpaj-unique-boundary-rowp
                                      fn-bpaj-eid-text fn-bpp-eidp
                                      fn-cfgp listener-set-entry)
           :use listener-set-entry)))

; The converse: the set leaves no admissible boundary unheard.  A session
; the admission admits arrived on a port the host binds.
(local (defthm candidate-has-its-listener-row
  (implies (member-equal name (fn-bpaj-loopback-candidates rows all port))
           (and (fn-bpaj-boundary-rowp all name "bp-boundary-listener"
                                       "127.0.0.1" port)
                (<= port 65535)))
  :hints (("Goal" :in-theory (disable fn-bpaj-boundary-rowp
                                      fn-bpaj-boundary-slot-count
                                      fn-cfg-peer-find fn-cfg-labelp)))))

(local (defthm listener-row-reaches-the-set
  (implies (and (fn-bpaj-boundary-rowp rows name "bp-boundary-listener"
                                       "127.0.0.1" port)
                (fn-bpaj-listener-row-portp port)
                (equal (fn-bpaj-loopback-candidates all all port)
                       (list name)))
           (assoc-equal port (fn-bpaj-listener-rows rows all)))
  :hints (("Goal" :in-theory (disable fn-bpaj-loopback-candidates
                                      fn-bpaj-listener-row-portp)))))

(defthm fn-bpaj-admitted-session-arrives-on-a-bound-listener
  (implies (and (equal (car (fn-bpaj-session-principal
                             cfg (fn-bpaj-loopback-channel port) announced))
                       :admitted)
                (posp port))
           (member-equal port (fn-bpaj-listener-ports cfg)))
  :hints (("Goal" :in-theory (disable fn-bpaj-loopback-candidates
                                      fn-bpaj-boundary-rowp
                                      fn-bpaj-unique-boundary-rowp
                                      fn-bpaj-eid-text fn-bpp-eidp)
           :use ((:instance candidate-has-its-listener-row
                  (rows (fn-cfg-peers (fn-cfg-value cfg)))
                  (all (fn-cfg-peers (fn-cfg-value cfg)))
                  (name (car (fn-bpaj-loopback-candidates
                              (fn-cfg-peers (fn-cfg-value cfg))
                              (fn-cfg-peers (fn-cfg-value cfg)) port))))
                 (:instance listener-row-reaches-the-set
                  (rows (fn-cfg-peers (fn-cfg-value cfg)))
                  (all (fn-cfg-peers (fn-cfg-value cfg)))
                  (name (car (fn-bpaj-loopback-candidates
                              (fn-cfg-peers (fn-cfg-value cfg))
                              (fn-cfg-peers (fn-cfg-value cfg)) port))))))))

; One listener per port.
(local (defthm no-duplicate-ports-of-listener-rows
  (no-duplicatesp-equal
   (fn-bpaj-listener-port-list (fn-bpaj-listener-rows rows all)))
  :hints (("Goal" :in-theory (disable fn-bpaj-loopback-candidates
                                      fn-bpaj-listener-row-portp)))))

(defthm fn-bpaj-listener-ports-are-distinct
  (no-duplicatesp-equal (fn-bpaj-listener-ports cfg)))

(verify-guards fn-bpaj-listener-set)
(verify-guards fn-bpaj-listener-ports)
(verify-guards fn-bpaj-listener-name)
(verify-guards fn-bpaj-loopback-channel)
