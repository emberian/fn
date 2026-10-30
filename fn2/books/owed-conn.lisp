; Keystones T1 and T8 (RELEASE-PLAN section 4.1; layer doc section 7),
; admitted with D3 over the connection machine. Their subject is
; fn2-conn-wire-run, the logical view of the served core at its adapter
; boundary: clients, each a transcript of octets arriving in given chunk
; sizes, connect to the served listener (admitting fn2-conn), and the view
; returns each client's wire (the octets the core sent it), whether the core
; closed it, and the core's stop reason. The view drives the real core
; (fn2-turn, fn2-outbox-peek/ack, fn2-post-result) and lists exist only in
; the view, never on the served path. The interim the peer address imposes
; (no per-address refusal and no peer bit until A5r and E4) is a third
; owed row with its fixture, so it cannot be forgotten.
(in-package "ACL2")
(include-book "executor")
(fn2-book-layer :d)

(make-event (value (fn2-declare '(:operation-set fn2-conn-wire) nil nil nil)))

; A tiny profile whose pool gives every connection two slots of at least
; *fn2-conn-range-min* octets, with the served listener admitting fn2-conn.
(defconst *fn2-conn-wire-profile*
  (put-assoc-equal :listener-targets 'fn2-conn
    (put-assoc-equal :pool-classes '((8 . 1024) (4 . 256)) *fn2-profile-tiny*)))

(defun fn2-cw-chars (cs)
  (declare (xargs :verify-guards nil))
  (if (atom cs) nil (cons (char-code (car cs)) (fn2-cw-chars (cdr cs)))))
(defun fn2-cw-read-range (k n slot fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil :measure (nfix (- (nfix n) (nfix k)))))
  ; The adapter reads a lent range physically (it is no row's owner).
  (if (>= (nfix k) (nfix n)) nil
    (cons (fn2-pool-datai (+ (fn2-pool-slot-base slot fn2-pool) (nfix k)) fn2-pool)
          (fn2-cw-read-range (+ 1 (nfix k)) n slot fn2-pool))))
(defun fn2-cw-write-loan (k octets slot gen op opgen fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (if (atom octets) fn2-pool
    (mv-let (code fn2-pool) (fn2-pool-adapter-write slot gen op opgen k (car octets) fn2-pool)
      (declare (ignore code))
      (fn2-cw-write-loan (+ 1 k) (cdr octets) slot gen op opgen fn2-pool))))
(defun fn2-cw-post (cell op opgen event outcome count aux0 aux1 fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (fn2-ops) (fn2-post-result cell op opgen event outcome *fn2-reason-none* count aux0 aux1 fn2-ops)
    fn2-core))
(in-theory (disable fn2-cw-read-range fn2-cw-write-loan fn2-cw-post))

; A client is (input sizes wire closed): remaining octets, remaining chunk
; sizes, the octets received (newest first), and whether the core closed it.
(defun fn2-cw-client (i clients)
  (declare (xargs :verify-guards nil))
  (or (nth i clients) (list nil nil nil nil)))
(defun fn2-cw-set (i client clients)
  (declare (xargs :verify-guards nil))
  (update-nth i client clients))
(in-theory (disable fn2-cw-client fn2-cw-set))

; Complete the outbox head: (mv took accepted clients fn2-core). Accepts
; are completed in client order (capability index = client index, nonce
; 77) and left pending once every client is connected; a Receive is given the client's next chunk, or stays pending once the
; client has sent everything; a Send's bytes go on the client's wire and its
; terminal and release are posted; a Close marks the client closed.
(defun fn2-cw-adapter-one (accepted clients fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv code op opgen kind cap rslot rgen roff rlen fn2-core)
        (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
          (code op opgen kind cap rslot rgen roff rlen fn2-ops)
          (mv-let (code op opgen) (fn2-outbox-peek 0 fn2-ops)
            (if (not (eq code :ok)) (mv code 0 0 0 0 0 0 0 0 fn2-ops)
              (mv-let (rslot rgen roff rlen) (fn2-op-range op fn2-ops)
                (mv-let (cap nonce) (fn2-op-capability op fn2-ops)
                  (declare (ignore nonce))
                  (let ((kind (fn2-ops-kind op fn2-ops)))
                    (mv-let (ack fn2-ops) (fn2-outbox-ack 1 fn2-ops)
                      (mv ack op opgen kind cap rslot rgen roff rlen fn2-ops)))))))
          (mv code op opgen kind cap rslot rgen roff rlen fn2-core)))
       ((unless (eq code :ok)) (mv nil accepted clients fn2-core))
       (c (fn2-cw-client cap clients))
       (input (nth 0 c)) (sizes (nth 1 c)) (wire (nth 2 c)))
    (cond
     ((and (equal kind *fn2-action-accept*) (>= accepted (len clients)))
      ; No more clients: the Accept stays submitted and pending.
      (mv t accepted clients fn2-core))
     ((equal kind *fn2-action-accept*)
      (let ((fn2-core (fn2-cw-post 0 op opgen *fn2-event-accept-result* *fn2-outcome-done* 0 accepted 77 fn2-core)))
        (mv t (+ 1 accepted) clients fn2-core)))
     ((equal kind *fn2-action-receive*)
      (if (atom input) (mv t accepted clients fn2-core)
        (b* ((want (if (and (consp sizes) (posp (car sizes))) (car sizes) (len input)))
             (n (min want (min rlen (len input))))
             (fn2-core (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (fn2-pool)
                         (fn2-cw-write-loan roff (take n input) rslot rgen op opgen fn2-pool) fn2-core))
             (fn2-core (fn2-cw-post 0 op opgen *fn2-event-receive-result* *fn2-outcome-done* n 0 0 fn2-core)))
          (mv t accepted
              (fn2-cw-set cap (list (nthcdr n input) (if (consp sizes) (cdr sizes) nil) wire (nth 3 c)) clients)
              fn2-core))))
     ((equal kind *fn2-action-send*)
      (b* ((octets (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (octets)
                     (fn2-cw-read-range roff (+ roff rlen) rslot fn2-pool) octets))
           (fn2-core (fn2-cw-post 0 op opgen *fn2-event-send-result* *fn2-outcome-done* rlen 1 0 fn2-core))
           (fn2-core (fn2-cw-post 1 op opgen *fn2-event-borrow-released* *fn2-outcome-done* 0 0 0 fn2-core)))
        (mv t accepted (fn2-cw-set cap (list input sizes (revappend octets wire) (nth 3 c)) clients) fn2-core)))
     ((equal kind *fn2-action-close*)
      (let ((fn2-core (fn2-cw-post 0 op opgen *fn2-event-close-result* *fn2-outcome-done* 0 0 0 fn2-core)))
        (mv t accepted (fn2-cw-set cap (list input sizes wire t) clients) fn2-core)))
     (t (mv t accepted clients fn2-core)))))
(in-theory (disable fn2-cw-adapter-one))

; Alternate turns and adapter completions until three rounds in a row
; neither observe, visit, act nor complete anything, or the core stops.
(defun fn2-cw-loop (fuel idle accepted clients fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix fuel)))
  (if (zp fuel) (mv :fuel clients fn2-core)
    (b* (((mv & nobs nvisits nactions fn2-core) (fn2-turn fn2-core))
         ((mv took accepted clients fn2-core) (fn2-cw-adapter-one accepted clients fn2-core))
         (idle (if (or took (< 0 nobs) (< 0 nvisits) (< 0 nactions)) 0 (+ 1 idle))))
      (if (or (<= 3 idle) (not (equal (fn2-core-stop-reason fn2-core) 0)))
          (mv :quiet clients fn2-core)
        (fn2-cw-loop (- fuel 1) idle accepted clients fn2-core)))))
(in-theory (disable fn2-cw-loop))

(defun fn2-cw-clients (transcripts)
  (declare (xargs :verify-guards nil))
  (if (atom transcripts) nil
    (cons (list (car (car transcripts)) (cadr (car transcripts)) nil nil)
          (fn2-cw-clients (cdr transcripts)))))
(defun fn2-cw-results (clients)
  (declare (xargs :verify-guards nil))
  (if (atom clients) nil
    (cons (list (reverse (nth 2 (car clients))) (nth 3 (car clients)))
          (fn2-cw-results (cdr clients)))))

; The ledger after a run, beside what the runner saw (D7 3/n): (conserved
; hold rx tx live delivered sent) for the anonymous principal, every client
; on it. DELIVERED is what the adapter gave the core by Receive results,
; SENT what it took by Send results, LIVE the clients greeted and not
; closed.
(defun fn2-cw-delivered (transcripts clients)
  (declare (xargs :verify-guards nil))
  (if (atom transcripts) 0
    (+ (- (len (car (car transcripts))) (len (nth 0 (car clients))))
       (fn2-cw-delivered (cdr transcripts) (cdr clients)))))
(defun fn2-cw-sent (clients)
  (declare (xargs :verify-guards nil))
  (if (atom clients) 0 (+ (len (nth 2 (car clients))) (fn2-cw-sent (cdr clients)))))
(defun fn2-cw-greeted-p (wire)
  ; WIRE newest first: its first three octets are 200 or 201
  (declare (xargs :verify-guards nil))
  (let ((w (reverse wire)))
    (and (<= 3 (len w)) (equal (take 2 w) '(50 48)) (member (nth 2 w) '(48 49)))))
(defun fn2-cw-live (clients)
  (declare (xargs :verify-guards nil))
  (if (atom clients) 0
    (+ (if (and (fn2-cw-greeted-p (nth 2 (car clients))) (not (nth 3 (car clients)))) 1 0)
       (fn2-cw-live (cdr clients)))))
(defun fn2-cw-ledger (transcripts clients fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((d (fn2-account-holding :connection-row)))
    (list (fn2-account-core-conservedp fn2-core)
          (fn2-account-core-hold 0 d fn2-core)
          (fn2-account-core-charged 0 *fn2-account-charge-rx* fn2-core)
          (fn2-account-core-charged 0 *fn2-account-charge-tx* fn2-core)
          (+ (fn2-cw-live clients) (fn2-listener-bookings 0 fn2-core)) (fn2-cw-delivered transcripts clients) (fn2-cw-sent clients))))
(defun fn2-conn-ledger-matches-p (view)
  (declare (xargs :verify-guards nil))
  (and (equal (nth 0 view) t) (equal (nth 1 view) (nth 4 view))
       (equal (nth 2 view) (nth 5 view)) (equal (nth 3 view) (nth 6 view))))

; TRANSCRIPTS is a list of (octets sizes), one per client (at most the
; profile's C connections). Result: (status ((wire closed) ...) stop-reason
; ledger-view).
(defun fn2-conn-wire-run (transcripts)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core)
      (let ((fn2-core (fn2-init-executor *fn2-conn-wire-profile* :echo nil fn2-core)))
        (mv-let (status clients fn2-core)
          (fn2-cw-loop (+ 2000 (* 600 (len transcripts))) 0 0 (fn2-cw-clients transcripts) fn2-core)
          (mv (list status (fn2-cw-results clients) (fn2-core-stop-reason fn2-core)
                    (fn2-cw-ledger transcripts clients fn2-core))
              fn2-core)))
      result)))

; One client's wire and close state when it is alone.
(defun fn2-conn-wire-solo (octets sizes)
  (declare (xargs :verify-guards nil))
  (car (nth 1 (fn2-conn-wire-run (list (list octets sizes))))))

(defun fn2-conn-octets-transcripts-p (transcripts)
  (declare (xargs :verify-guards nil))
  (if (atom transcripts) (null transcripts)
    (and (true-listp (car transcripts)) (equal (len (car transcripts)) 2)
         (fn2-gram-octetsp (car (car transcripts))) (nat-listp (cadr (car transcripts)))
         (fn2-conn-octets-transcripts-p (cdr transcripts)))))

(defun fn2-conn-safe-p (r)
  (declare (xargs :verify-guards nil))
  (and (equal (car r) :quiet) (equal (nth 2 r) 0)))

; T1: from the initialized served core, arbitrary client octets in arbitrary
; chunks reach a quiescent core that never stopped: every run, handler and
; reached call kept its contract and guard (a guard or contract violation
; stops the core by name).
(defthm-owed fn2-turn-served-safety (transcripts)
  (implies (and (fn2-conn-octets-transcripts-p transcripts) (<= (len transcripts) 4))
           (fn2-conn-safe-p (fn2-conn-wire-run transcripts)))
  :schema :invariant :from (:operation-set fn2-conn-wire)
  :teeth (fn2-conn-test-served-safety fn2-conn-test-served-safety-negative)
  :doc "T1: arbitrary boundary octets, in arbitrary chunks, on up to C connections, leave the served core quiescent and never stopped: no run, handler or reached call violated its contract or guard.")

; The ledger matches the rows (D7 3/n; layer doc 13.5): after any client
; octets in any chunks on up to C connections, the anonymous principal's
; ledger row is conserved, holds exactly the connections greeted and not
; closed, and is charged exactly the octets the adapter delivered by
; Receive results and took by Send results (charged from the first byte,
; none erased by a close).
(defthm-owed fn2-account-ledger-matches (transcripts)
  (implies (and (fn2-conn-octets-transcripts-p transcripts) (<= (len transcripts) 4))
           (fn2-conn-ledger-matches-p (nth 3 (fn2-conn-wire-run transcripts))))
  :schema :invariant :from (:operation-set fn2-conn-wire)
  :teeth (fn2-conn-test-ledger-matches fn2-conn-test-ledger-matches-negative)
  :doc "Rule 5 over the served connection: the principal ledger stays conserved, books exactly the live greeted connections, and charges exactly the received and sent octets, from the first byte, whatever the chunking; a close erases no charge.")

; T8, fragmentation: the wire a client receives depends on its octets, not
; on how they were chunked.
(defthm-owed fn2-reply-trace-fragmentation-invariant (octets sizes)
  (implies (and (fn2-gram-octetsp octets) (nat-listp sizes))
           (equal (fn2-conn-wire-solo octets sizes) (fn2-conn-wire-solo octets nil)))
  :schema :invariant :from (:operation-set fn2-conn-wire)
  :teeth (fn2-conn-test-fragmentation fn2-conn-test-fragmentation-negative)
  :doc "T8: every split of a client's octets into chunks gives the same reply bytes and the same close.")

; T8, privacy: a client's wire is the one it gets alone, whatever the other
; connections send (D3's only shared input is the clock, which these runs
; do not post).
(defthm-owed fn2-connection-privacy (a sa b sb)
  (implies (and (fn2-gram-octetsp a) (nat-listp sa) (fn2-gram-octetsp b) (nat-listp sb))
           (equal (car (nth 1 (fn2-conn-wire-run (list (list a sa) (list b sb)))))
                  (fn2-conn-wire-solo a sa)))
  :schema :invariant :from (:operation-set fn2-conn-wire)
  :teeth (fn2-conn-test-privacy fn2-conn-test-privacy-negative)
  :doc "T8: a connection's reply bytes and close are those it gets alone, whatever another connection sends.")

; The peer-address interim (layer doc section 8): until A5r's Accept result
; carries the peer address, every connection is a reader (no peer bit) and
; no per-address 400 is given. Owed so that it is lifted, not forgotten.
(defun fn2-cw-crlf-octets (lines)
  (declare (xargs :verify-guards nil))
  (if (atom lines) nil
    (append (fn2-cw-chars (coerce (car lines) 'list)) (list 13 10) (fn2-cw-crlf-octets (cdr lines)))))
(defconst *fn2-conn-mode-stream-line* (fn2-cw-crlf-octets '("MODE STREAM")))
(defconst *fn2-conn-reader-prefix*
  (fn2-cw-crlf-octets '("201 fn-nntp experimental reader ready" "501 syntax error")))
(defun fn2-conn-reader-prefix-p (wire)
  (declare (xargs :verify-guards nil))
  (equal (take (len *fn2-conn-reader-prefix*) wire) *fn2-conn-reader-prefix*))
(defthm-owed fn2-conn-reader-only-interim (octets sizes)
  (implies (and (fn2-gram-octetsp octets) (nat-listp sizes))
           (fn2-conn-reader-prefix-p
            (car (fn2-conn-wire-solo (append *fn2-conn-mode-stream-line* octets) sizes))))
  :schema :invariant :from (:operation-set fn2-conn-wire)
  :teeth (fn2-conn-test-reader-only fn2-conn-test-reader-only-negative)
  :doc "Interim until A5r (the peer address in the Accept result) and E4 (peer records): every connection is a reader, so a first MODE STREAM is answered 501 after the reader greeting, whatever follows, and no per-address 400 exists. Lifting the interim replaces this row with the per-address refusal and peer statements.")
