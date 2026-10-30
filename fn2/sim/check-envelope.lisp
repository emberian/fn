; ENVELOPE (layer doc 4.1.5): the execution checker over a native adapter's
; boundary trace. It replays the trace into a fresh core from the same
; profile, through the core's own entries (fn2/books/host-boundary.lisp), and
; checks at every step that the schedule is one the simulator's adapter may
; choose: each take is the replay's outbox head with the same descriptor,
; each post answers a taken and acknowledged op once per cell, lies in the
; allowed relation (4.1.2's table) and is accepted by the replay's core.
; Separately it checks the bytes: per capability the Receive octets are the
; client's, and the octets each Send moved are the replay's own borrowed
; range, whose concatenation is what the client received.
; Trace entries (fn2/host/adapter.lisp writes them):
;   (:clock mono real flags) (:signal bits) (:turn status)
;   (:take op gen kind cap nonce rslot rgen off len soff fua may-release cslot cgen deadline ogen)
;   (:ack n) (:finish op gen)
;   (:post cell op gen event outcome reason count aux0 aux1 family (port w0 w1 w2 w3) octets)
(in-package "ACL2")
(include-book "../books/host-boundary")

; ------------------------------------------------------------------------
; The allowed relation: the cell words an adapter may post for an op of
; KIND with loan length LEN (4.1.2's table). The core validates a superset.
(defun fn2-host-result-allowedp (kind outcome reason count aux0 aux1 len may-release)
  (declare (xargs :guard t))
  (let ((event (fn2-terminal-event kind)))
    (and event (natp count) (natp len) (natp aux0) (natp aux1)
         (fn2-event-statusp event outcome reason)
         (cond
          ((or (equal kind *fn2-action-accept*) (equal kind *fn2-action-connect*))
           (and (= count 0) (implies (not (equal outcome *fn2-outcome-done*)) (and (= aux0 0) (= aux1 0)))))
          ((or (equal kind *fn2-action-receive*) (equal kind *fn2-action-entropy*))
           (and (= aux0 0) (= aux1 0)
                (if (equal outcome *fn2-outcome-done*) (<= count len) (= count 0))))
          ((equal kind *fn2-action-read*)
           (and (= aux0 0) (= aux1 0)
                (cond ((equal outcome *fn2-outcome-done*) (= count len))
                      ((equal outcome *fn2-outcome-short*) (< count len))
                      (t (= count 0)))))
          ((equal kind *fn2-action-send*)
           (and (= aux1 0) (<= aux0 1) (implies (= aux0 1) (equal may-release 1))
                (cond ((equal outcome *fn2-outcome-done*) (= count len))
                      ((equal outcome *fn2-outcome-short*) (< count len))
                      (t (<= count len)))))
          ((equal kind *fn2-action-write*)
           (and (= aux0 0) (= aux1 0)
                (if (equal outcome *fn2-outcome-done*) (= count len) (<= count len))))
          (t (and (= count 0) (= aux0 0) (= aux1 0)))))))

; ------------------------------------------------------------------------
; Replay state (logic only, never on a served path): TAKEN maps an op slot
; to (gen kind cap nonce rslot rgen off len may-release acked posted0);
; CAPS maps a capability incarnation (index . nonce) to (nonce port rx tx eof closed cuts) with
; rx and tx newest first and cuts the Receive counts, newest first.
(defun fn2-env-get (k alist) (declare (xargs :verify-guards nil)) (cdr (assoc-equal k alist)))

(defun fn2-env-write-loan (k octets slot gen op opgen fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil :measure (len octets)))
  (if (atom octets) (mv :ok fn2-pool)
    (mv-let (code fn2-pool) (fn2-pool-adapter-write slot gen op opgen k (car octets) fn2-pool)
      (if (not (eq code :ok)) (mv code fn2-pool)
        (fn2-env-write-loan (+ 1 (nfix k)) (cdr octets) slot gen op opgen fn2-pool)))))
(defun fn2-env-read-range (k n slot fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil :measure (nfix (- (nfix n) (nfix k)))))
  (if (>= (nfix k) (nfix n)) nil
    (cons (fn2-pool-datai (+ (fn2-pool-slot-base slot fn2-pool) (nfix k)) fn2-pool)
          (fn2-env-read-range (+ 1 (nfix k)) n slot fn2-pool))))

(defun fn2-env-descriptor (slot fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (mv-let (code kind cap nonce rslot rgen off len soff fua may-release cslot cgen deadline ogen)
    (fn2-host-action slot fn2-core)
    (and (eq code :ok)
         (list kind cap nonce rslot rgen off len soff fua may-release cslot cgen deadline ogen))))

; CAPS is keyed by the incarnation (index . nonce), so a reused index keeps
; every earlier connection's bytes for the client check.
(defun fn2-env-cap-issued-p (index nonce caps)
  ; A pair is fresh only if its index was issued before only with smaller nonces.
  (declare (xargs :verify-guards nil))
  (cond ((atom caps) nil)
        ((and (consp (car caps)) (consp (caar caps)) (equal (car (caar caps)) index)
              (natp nonce) (natp (cdr (caar caps))) (<= nonce (cdr (caar caps)))) t)
        (t (fn2-env-cap-issued-p index nonce (cdr caps)))))
(defun fn2-env-cap-live-p (index nonce caps)
  (declare (xargs :verify-guards nil))
  (let ((c (fn2-env-get (cons index nonce) caps)))
    (and c (not (nth 5 c)))))

; One post. Result (mv failure taken caps fn2-core); FAILURE nil when legal.
; BYTES-P also compares a Send's recorded octets with the replay's range.
(defun fn2-env-post (e bytes-p taken caps fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((cell (nth 1 e)) (slot (nth 2 e)) (gen (nth 3 e)) (event (nth 4 e)) (outcome (nth 5 e))
       (reason (nth 6 e)) (count (nth 7 e)) (aux0 (nth 8 e)) (aux1 (nth 9 e)) (family (nth 10 e))
       (peer (nth 11 e)) (octets (nth 12 e))
       (tk (fn2-env-get slot taken))
       (stray0 (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (n) (fn2-ops-stray fn2-ops) n))
       ((unless (and tk (equal (nth 0 tk) gen) (nth 9 tk))) (mv :post-unacknowledged taken caps fn2-core))
       ((when (and (equal cell 1)
                   (not (and (equal (nth 1 tk) *fn2-action-send*) (equal (nth 8 tk) 1)
                             (not (nth 12 tk)) (implies (nth 10 tk) (equal (nth 11 tk) 1))))))
        (mv :release-unauthorized taken caps fn2-core))
       ((when (and (equal cell 0) (nth 10 tk))) (mv :post-twice taken caps fn2-core))
       (kind (nth 1 tk)) (cap (nth 2 tk)) (nonce (nth 3 tk))
       (rslot (nth 4 tk)) (rgen (nth 5 tk)) (off (nth 6 tk)) (len (nth 7 tk)) (may-release (nth 8 tk))
       ((unless (if (equal cell 0) (equal event (fn2-terminal-event kind))
                  (and (equal event *fn2-event-borrow-released*) (equal outcome *fn2-outcome-done*)
                       (equal reason *fn2-reason-none*) (equal count 0) (equal aux0 0) (equal aux1 0))))
        (mv :post-event taken caps fn2-core))
       ((when (equal cell 1))
        (let ((fn2-core (fn2-host-post-result 1 slot gen event outcome reason 0 0 0 fn2-core)))
          (mv (if (equal stray0 (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (n) (fn2-ops-stray fn2-ops) n))
                  nil :post-refused)
              (put-assoc-equal slot (update-nth 12 t tk) taken) caps fn2-core)))
       ((unless (fn2-host-result-allowedp kind outcome reason count aux0 aux1 len may-release))
        (mv :post-not-allowed taken caps fn2-core))
       ((when (and (or (equal kind *fn2-action-receive*) (equal kind *fn2-action-send*))
                   (not (fn2-env-cap-live-p cap nonce caps))
                   (not (equal outcome *fn2-outcome-cancelled*))))
        (mv :post-after-close taken caps fn2-core))
       (stray (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (n) (fn2-ops-stray fn2-ops) n))
       ; Receive: the recorded octets are written under the replay's loan first.
       ((mv wcode fn2-core)
        (if (and (equal kind *fn2-action-receive*) (equal outcome *fn2-outcome-done*))
            (if (not (equal (len octets) count)) (mv :receive-count fn2-core)
              (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (code fn2-pool)
                (fn2-env-write-loan off octets rslot rgen slot gen fn2-pool) (mv code fn2-core)))
          (mv :ok fn2-core)))
       ((unless (eq wcode :ok)) (mv :receive-loan taken caps fn2-core))
       ; Send: what the replay's borrowed range holds, before the post releases it.
       (sent (if (and (equal kind *fn2-action-send*) (not (equal outcome *fn2-outcome-cancelled*)))
                 (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (bytes)
                   (fn2-env-read-range off (+ off count) rslot fn2-pool) bytes)
               nil))
       ((when (and bytes-p (equal kind *fn2-action-send*) (not (equal sent octets))))
        (mv :send-bytes taken caps fn2-core))
       ((when (and (equal kind *fn2-action-accept*) (equal outcome *fn2-outcome-done*)
                   (fn2-env-cap-issued-p aux0 aux1 caps)))
        (mv :accept-capability-reused taken caps fn2-core))
       (fn2-core (if (equal kind *fn2-action-accept*)
                     (fn2-host-post-accept-result slot gen outcome reason aux0 aux1 family
                                                  (nth 0 peer) (nth 1 peer) (nth 2 peer) (nth 3 peer) (nth 4 peer)
                                                  fn2-core)
                   (fn2-host-post-result 0 slot gen event outcome reason count aux0 aux1 fn2-core)))
       ((unless (equal stray (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (n) (fn2-ops-stray fn2-ops) n)))
        (mv :post-refused taken caps fn2-core))
       (taken (put-assoc-equal slot (update-nth 11 aux0 (update-nth 10 t tk)) taken))
       (key (cons cap nonce))
       (c (fn2-env-get key caps))
       (caps (cond
              ((and (equal kind *fn2-action-accept*) (equal outcome *fn2-outcome-done*))
               (put-assoc-equal (cons aux0 aux1) (list aux1 (nth 0 peer) nil nil nil nil nil) caps))
              ((and (equal kind *fn2-action-receive*) (equal outcome *fn2-outcome-done*) c)
               (put-assoc-equal key (list (nth 0 c) (nth 1 c) (revappend octets (nth 2 c)) (nth 3 c)
                                          (or (nth 4 c) (equal count 0)) (nth 5 c) (cons count (nth 6 c)))
                                caps))
              ((and (equal kind *fn2-action-send*) c)
               (put-assoc-equal key (list (nth 0 c) (nth 1 c) (nth 2 c) (revappend sent (nth 3 c))
                                          (nth 4 c) (nth 5 c) (nth 6 c))
                                caps))
              ((and (equal kind *fn2-action-close*) c)
               (put-assoc-equal key (update-nth 5 t c) caps))
              (t caps))))
    (mv nil taken caps fn2-core)))

; The whole trace. Result (mv verdict caps fn2-core): :pass, or (FAILURE STEP).
(defun fn2-env-steps (trace i bytes-p taken caps fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (len trace)))
  (if (atom trace) (mv :pass caps fn2-core)
    (b* ((e (car trace)) (tag (and (consp e) (car e)))
         ((mv failure taken caps fn2-core)
          (case tag
            (:clock (let ((fn2-core (fn2-host-post-clock (nth 1 e) (nth 2 e) (nth 3 e) fn2-core))) (mv nil taken caps fn2-core)))
            (:signal (let ((fn2-core (fn2-host-post-signal (nth 1 e) fn2-core))) (mv nil taken caps fn2-core)))
            (:turn (mv-let (status nobs nvisits nactions fn2-core) (fn2-turn fn2-core)
                     (declare (ignore nobs nvisits nactions))
                     (mv (if (equal status (nth 1 e)) nil :turn-status) taken caps fn2-core)))
            (:take (mv-let (code slot gen) (fn2-host-outbox-peek 0 fn2-core)
                     (cond ((not (and (eq code :ok) (equal slot (nth 1 e)) (equal gen (nth 2 e))))
                            (mv :take-not-head taken caps fn2-core))
                           ((not (equal (fn2-env-descriptor slot fn2-core) (nthcdr 3 e)))
                            (mv :take-descriptor taken caps fn2-core))
                           (t (mv nil (put-assoc-equal slot (list gen (nth 3 e) (nth 4 e) (nth 5 e) (nth 6 e)
                                                                  (nth 7 e) (nth 8 e) (nth 9 e) (nth 12 e) nil nil 0 nil)
                                                       taken)
                                  caps fn2-core)))))
            (:ack (mv-let (code slot gen) (fn2-host-outbox-peek 0 fn2-core)
                    (declare (ignore gen))
                    (let ((tk (fn2-env-get slot taken)))
                      (if (not (and (eq code :ok) tk (not (nth 9 tk)) (equal (nth 1 e) 1)))
                          (mv :ack-untaken taken caps fn2-core)
                        (mv-let (acode fn2-core) (fn2-host-outbox-ack 1 fn2-core)
                          (mv (if (eq acode :ok) nil :ack-refused)
                              (put-assoc-equal slot (update-nth 9 t tk) taken) caps fn2-core))))))
            (:finish (mv-let (code fn2-core) (fn2-host-op-finish (nth 1 e) (nth 2 e) fn2-core)
                       (mv (if (eq code :ok) nil :finish-refused) taken caps fn2-core)))
            (:post (fn2-env-post e bytes-p taken caps fn2-core))
            (otherwise (mv :unknown-entry taken caps fn2-core)))))
      (if failure (mv (list failure i) caps fn2-core)
        (fn2-env-steps (cdr trace) (+ 1 i) bytes-p taken caps fn2-core)))))

(defun fn2-envelope-replay (trace profile bytes-p)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (verdict caps fn2-core)
      (let ((fn2-core (fn2-init-executor profile :echo nil fn2-core)))
        (fn2-env-steps trace 0 bytes-p nil nil fn2-core))
      ; put-assoc-equal appends a new incarnation: CAPS is in Accept order.
      (list verdict caps))))

; ------------------------------------------------------------------------
; The bytes are the clients'. CLIENTS: one (incarnation sent received closed
; port) per client, the incarnation (index . nonce) the session bound the
; client to, octet lists oldest first. Per incarnation: the Accept's peer port
; is the client's local port, the Receive octets are the client's sent octets
; (all of them when the node read EOF, else a prefix), and the Send octets
; are exactly what the client received.
(defun fn2-env-prefixp (a b)
  (declare (xargs :guard t))
  (if (atom a) t (and (consp b) (equal (car a) (car b)) (fn2-env-prefixp (cdr a) (cdr b)))))
(defun fn2-env-client (port clients)
  (declare (xargs :guard t))
  (cond ((atom clients) nil)
        ((and (consp (car clients)) (equal (car (car clients)) port)) (car clients))
        (t (fn2-env-client port (cdr clients)))))
(defun fn2-env-bytes (caps clients)
  (declare (xargs :verify-guards nil))
  (if (atom caps) :pass
    (b* ((c (cdr (car caps))) (cl (fn2-env-client (car (car caps)) clients))
         (rx (reverse (nth 2 c))) (tx (reverse (nth 3 c))))
      (cond ((null cl) (list :no-client (nth 1 c)))
            ((not (equal (nth 4 cl) (nth 1 c))) (list :peer-port-not-client (nth 1 c)))
            ((not (if (nth 4 c) (equal rx (nth 1 cl)) (fn2-env-prefixp rx (nth 1 cl))))
             (list :receive-not-client (nth 1 c)))
            ((not (equal tx (nth 2 cl))) (list :send-not-client (nth 1 c)))
            (t (fn2-env-bytes (cdr caps) clients))))))

; The input half alone: a legal replay (no Send byte comparison), then the
; clients' bytes; a changed Receive octet is refused as :receive-not-client.
(defun fn2-envelope-check-inputs (trace clients profile)
  (declare (xargs :verify-guards nil))
  (let* ((r (fn2-envelope-replay trace profile nil)))
    (if (not (eq (car r) :pass)) (car r) (fn2-env-bytes (cadr r) clients))))

(defun fn2-envelope-check (trace clients profile)
  (declare (xargs :verify-guards nil))
  (let* ((r (fn2-envelope-replay trace profile t)))
    (if (not (eq (car r) :pass)) (car r)
      (fn2-env-bytes (cadr r) clients))))
