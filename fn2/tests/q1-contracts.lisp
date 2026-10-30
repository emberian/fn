; Q1's honest classification, step 2 (build/coordinator/fn2/lanes/a-dm4-q1-classification.md
; section 3): the independent contract per machine kind. Q1's case rows are a refinement of the
; scheduler over shared handlers; what a kind's handlers do is claimed here, by rows whose
; oracle does not call the handler. Each row is a defthm-owed with evaluating teeth.
(in-package "ACL2")
(include-book "conn-unit")
(include-book "../sim/check-wire")
(include-book "../sim/sim-recovery")
(include-book "../sim/echo")

; ------------------------------------------------------------------------
; fn2-conn: WIRE correctness. The served connection, alone, given any client
; octets in any chunks, answers a wire that WIRE's model oracle
; (sim/check-wire.lisp, written over octet lists without calling fn2-conn's
; handlers) accepts. WIRE is permissive by design: it checks the greeting,
; the admitted reply codes per command keyword, multi-line framing and the
; close, not exact reply text. T1 (safe execution) and T8 (fragmentation,
; privacy) are other claims.
(defthm-owed fn2-conn-wire-correct (octets sizes)
  (implies (and (fn2-gram-octetsp octets) (nat-listp sizes))
           (let ((r (fn2-conn-wire-solo octets sizes)))
             (fn2-wire-pass-p octets (car r) (cadr r))))
  :schema :invariant :claim :semantic
  :teeth (fn2-conn-wire-correct-positive fn2-conn-wire-correct-negative)
  :doc "WIRE correctness of the served connection: every client's octets, in any chunks, get a wire WIRE's independent model oracle accepts (greeting, admitted codes, framing, close; not exact text).")

(defun fn2-q1c-wire-ok (octets sizes)
  (declare (xargs :verify-guards nil))
  (let ((r (fn2-conn-wire-solo octets sizes)))
    (fn2-wire-pass-p octets (car r) (cadr r))))
(defun fn2-q1c-fixtures-ok (fixtures sizes)
  (declare (xargs :verify-guards nil))
  (if (atom fixtures) t
    (and (fn2-q1c-wire-ok (nth 1 (car fixtures)) sizes)
         (fn2-q1c-fixtures-ok (cdr fixtures) sizes))))
(defun fn2-q1c-random-ok (n seed)
  (declare (xargs :verify-guards nil :measure (nfix n)))
  (if (zp n) t
    (and (fn2-q1c-wire-ok (fn2-cu-random-transcript seed) (list (+ 1 (mod seed 13))))
         (fn2-q1c-random-ok (- n 1) (+ 7919 seed)))))
; Positive: every conn-unit fixture whole and in 3-octet chunks, and six
; seeded random transcripts, satisfy the antecedent and the conclusion.
(defun fn2-conn-wire-correct-positive ()
  (declare (xargs :verify-guards nil))
  (and (fn2-q1c-fixtures-ok *fn2-cu-fixtures* nil)
       (fn2-q1c-fixtures-ok *fn2-cu-fixtures* '(3))
       (fn2-q1c-random-ok 6 101)))
; Negative: the conclusion refuses a wrong wire: the served wire of the
; pipelined fixture passes, and with its greeting code changed to 900 fails.
; (WIRE accepts that wire cut before its final 205 when the connection is
; closed: a close ends the expected replies early. That is WIRE's
; permissiveness, reported to D, not a property this row claims.)
(defun fn2-q1c-regreet (wire)
  (declare (xargs :verify-guards nil))
  (if (and (consp wire) (consp (cdr wire)) (consp (cddr wire))) (list* 57 48 48 (cdddr wire)) wire))
(defun fn2-conn-wire-correct-negative ()
  (declare (xargs :verify-guards nil))
  (let* ((octets (nth 1 (nth 1 *fn2-cu-fixtures*)))
         (r (fn2-conn-wire-solo octets nil)))
    (and (fn2-wire-pass-p octets (car r) (cadr r))
         (not (fn2-wire-pass-p octets (fn2-q1c-regreet (car r)) (cadr r))))))

; ------------------------------------------------------------------------
; fn2-echo: the served echo, alone, returns exactly the octets its client
; sent, in any chunks. The oracle is the client's own input: nothing on the
; checking side calls an echo handler. The runner is owed-conn's lossless
; adapter loop (fn2-cw-loop) on the tiny profile, whose listeners admit echo;
; the length bound keeps the run inside the loop's fuel.
(defconst *fn2-q1c-echo-profile*
  (put-assoc-equal :pool-classes '((8 . 1024) (4 . 256)) *fn2-profile-tiny*))
(defun fn2-echo-solo (input sizes)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core)
      (let ((fn2-core (fn2-init-executor *fn2-q1c-echo-profile* :echo nil fn2-core)))
        (mv-let (status clients fn2-core)
          (fn2-cw-loop 2600 0 0 (fn2-cw-clients (list (list input sizes))) fn2-core)
          (mv (list status (car (fn2-cw-results clients)) (fn2-core-stop-reason fn2-core)) fn2-core)))
      result)))
(defthm-owed fn2-echo-replies-its-input (input sizes)
  (implies (and (fn2-gram-octetsp input) (nat-listp sizes) (<= (len input) 512))
           (let ((r (fn2-echo-solo input sizes)))
             (and (equal (car r) :quiet) (equal (nth 2 r) 0)
                  (equal (car (nth 1 r)) input))))
  :schema :invariant :claim :semantic
  :teeth (fn2-echo-replies-positive fn2-echo-replies-without-octets)
  :doc "The served echo, alone, quiesces unstopped and returns exactly its client's octets, in any chunks (up to 512 octets, inside the runner's fuel); the oracle is the client's own input.")
(defun fn2-q1c-echo-ok (input sizes)
  (declare (xargs :verify-guards nil))
  (let ((r (fn2-echo-solo input sizes)))
    (and (equal (car r) :quiet) (equal (nth 2 r) 0) (equal (car (nth 1 r)) input))))
(defun fn2-q1c-echo-random-ok (n seed)
  (declare (xargs :verify-guards nil :measure (nfix n)))
  (if (zp n) t
    (and (fn2-q1c-echo-ok (fn2-cu-random-transcript seed) (list (+ 1 (mod seed 11)) (+ 2 (mod seed 5))))
         (fn2-q1c-echo-random-ok (- n 1) (+ 7919 seed)))))
; Positive: a line whole, the same line one octet at a time, and six seeded
; random transcripts in two-size chunks satisfy antecedent and conclusion.
(defun fn2-echo-replies-positive ()
  (declare (xargs :verify-guards nil))
  (and (fn2-q1c-echo-ok '(72 69 76 76 79 13 10) nil)
       (fn2-q1c-echo-ok '(72 69 76 76 79 13 10) '(1 1 1 1 1 1 1))
       (fn2-q1c-echo-random-ok 6 101)))
; Negative: without the octet hypothesis the conclusion is false: a 300 sent
; by the client cannot come back as 300 (the pool holds bytes).
(defun fn2-echo-replies-without-octets ()
  (declare (xargs :verify-guards nil))
  (and (not (fn2-gram-octetsp '(72 300 10)))
       (not (fn2-q1c-echo-ok '(72 300 10) nil))))

; ------------------------------------------------------------------------
; fn2-listener: admission within the ledger. The listener books a
; :connection-row on the principal at Accept, transfers it to the admitted
; row, and unbooks on failure; a refused booking admits the connection
; unbooked so it can answer 400 and close (machines-a-run.lisp:154). The
; oracle reads the ledger's rows and the adapter's own view of its clients,
; never a listener handler: at EVERY round of the run the ledger is
; conserved and the principal holds at most its limit of rows; at
; quiescence the hold is exactly the live greeted connections plus the
; listeners' outstanding bookings, the charges are exactly the octets
; delivered and sent; at most LIMIT clients are greeted, and every other one
; got exactly one 400 line and was closed.
(defun fn2-q1c-ledger-profile (limit)
  (declare (xargs :verify-guards nil))
  (put-assoc-equal :accounts
                   `((0 :state :anonymous :limits ((:connection-row . ,limit) (:principal-reservation . ,limit))))
                   *fn2-conn-wire-profile*))
(defun fn2-q1c-within-limit-p (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((d (fn2-account-holding :connection-row)))
    (and (fn2-account-core-conservedp fn2-core)
         (<= (fn2-account-core-hold 0 d fn2-core) (fn2-account-core-limit 0 d fn2-core)))))
(defun fn2-q1c-ledger-loop (fuel idle accepted clients ok fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix fuel)))
  (if (zp fuel) (mv :fuel clients ok fn2-core)
    (b* (((mv & nobs nvisits nactions fn2-core) (fn2-turn fn2-core))
         ((mv took accepted clients fn2-core) (fn2-cw-adapter-one accepted clients fn2-core))
         (ok (and ok (fn2-q1c-within-limit-p fn2-core)))
         (idle (if (or took (< 0 nobs) (< 0 nvisits) (< 0 nactions)) 0 (+ 1 idle))))
      (if (or (<= 3 idle) (not (equal (fn2-core-stop-reason fn2-core) 0)))
          (mv :quiet clients ok fn2-core)
        (fn2-q1c-ledger-loop (- fuel 1) idle accepted clients ok fn2-core)))))
(defun fn2-listener-ledger-run (limit transcripts)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core)
      (let ((fn2-core (fn2-init-executor (fn2-q1c-ledger-profile limit) :echo nil fn2-core)))
        (mv-let (status clients ok fn2-core)
          (fn2-q1c-ledger-loop (+ 2000 (* 600 (len transcripts))) 0 0 (fn2-cw-clients transcripts) t fn2-core)
          (mv (list status ok (fn2-cw-ledger transcripts clients fn2-core) (fn2-cw-results clients)
                    (fn2-core-stop-reason fn2-core))
              fn2-core)))
      result)))
(defun fn2-q1c-refusals-p (results greeted)
  ; (mv-like) count greeted clients; every other one's wire is one 400 line, closed.
  (declare (xargs :verify-guards nil))
  (if (atom results) (natp greeted)
    (let ((wire (car (car results))) (closed (cadr (car results))))
      (if (and (<= 3 (len wire)) (equal (take 2 wire) '(50 48)) (member (nth 2 wire) '(48 49)))
          (fn2-q1c-refusals-p (cdr results) (+ 1 greeted))
        (and closed (<= 3 (len wire)) (equal (take 3 wire) '(52 48 48))
             (fn2-q1c-refusals-p (cdr results) greeted))))))
(defun fn2-q1c-greeted (results)
  (declare (xargs :verify-guards nil))
  (if (atom results) 0
    (+ (let ((wire (car (car results))))
         (if (and (<= 3 (len wire)) (equal (take 2 wire) '(50 48)) (member (nth 2 wire) '(48 49))) 1 0))
       (fn2-q1c-greeted (cdr results)))))
(defun fn2-q1c-ledger-ok (limit transcripts)
  (declare (xargs :verify-guards nil))
  (let ((r (fn2-listener-ledger-run limit transcripts)))
    (and (equal (nth 0 r) :quiet) (equal (nth 4 r) 0) (nth 1 r)
         (fn2-conn-ledger-matches-p (nth 2 r))
         (fn2-q1c-refusals-p (nth 3 r) 0)
         (<= (fn2-q1c-greeted (nth 3 r)) limit))))
(defthm-owed fn2-listener-admits-within-ledger (limit transcripts)
  (implies (and (natp limit) (<= 1 limit) (<= limit 4)
                (fn2-conn-octets-transcripts-p transcripts) (<= (len transcripts) 4))
           (fn2-q1c-ledger-ok limit transcripts))
  :schema :invariant :claim :semantic
  :teeth (fn2-listener-ledger-positive fn2-listener-ledger-without-client-bound)
  :doc "Admission within the ledger: at every round the anonymous principal's ledger is conserved and holds at most its connection-row limit; at quiescence it books exactly the live greeted connections and the listeners' bookings and charges exactly the octets moved; at most LIMIT clients are greeted and every other one gets one 400 line and is closed.")
(defconst *fn2-q1c-ledger-clients*
  (list (list (nth 1 (nth 1 *fn2-cu-fixtures*)) nil) (list (nth 1 (nth 2 *fn2-cu-fixtures*)) '(3))
        (list (fn2-cu-random-transcript 5) nil) (list (nth 1 (nth 1 *fn2-cu-fixtures*)) '(2))))
; Positive: four clients under limits 4, 2 and 1 (none, two and three refused
; with the 400), and two random clients under limit 1.
(defun fn2-listener-ledger-positive ()
  (declare (xargs :verify-guards nil))
  (and (fn2-q1c-ledger-ok 4 *fn2-q1c-ledger-clients*)
       (fn2-q1c-ledger-ok 2 *fn2-q1c-ledger-clients*)
       (fn2-q1c-ledger-ok 1 *fn2-q1c-ledger-clients*)
       (fn2-q1c-ledger-ok 1 (list (list (fn2-cu-random-transcript 9) '(4)) (list (fn2-cu-random-transcript 31) nil)))))
; Negative: without the bound of C = 4 clients the conclusion is false: a
; fifth client is never accepted, so it is neither greeted nor refused.
(defun fn2-listener-ledger-without-client-bound ()
  (declare (xargs :verify-guards nil))
  (not (fn2-q1c-ledger-ok 4 (cons (list (nth 1 (nth 1 *fn2-cu-fixtures*)) nil) *fn2-q1c-ledger-clients*))))

; ------------------------------------------------------------------------
; fn2-scribe: what it acknowledges is on the device in the v1 format. The
; scribe's own verify reads back through fn2-scribe-byte, the function its
; writer uses, so it is a twin, not an oracle. The oracle here is
; recover-stub's independent v1 decoder (fn2-recovery-sector: magic,
; version, address, sequence = sector + 1, and a checksum it recomputes)
; over the simulator's device image copied after the run.
(defconst *fn2-q1c-scribe-profile*
  (put-assoc-equal :pool-classes `((8 . ,*fn2-format-sector-bytes*) (4 . 65536)) *fn2-profile-tiny*))
(defun fn2-q1c-outbox (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (n) (fn2-outbox-queued fn2-ops) n))
(defun fn2-q1c-scribe-rounds (fuel fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil :measure (nfix fuel)))
  (if (zp fuel) (mv fn2-core fn2-sim fn2-own)
    (b* (((mv & fn2-core fn2-sim fn2-own) (fn2-sim-take-prefix (fn2-q1c-outbox fn2-core) 0 fn2-core fn2-sim fn2-own))
         ((mv & & & & fn2-core) (fn2-turn fn2-core))
         ((when (not (equal (fn2-core-stop-reason fn2-core) 0))) (mv fn2-core fn2-sim fn2-own))
         ((mv & fn2-core fn2-sim fn2-own) (fn2-sim-take-prefix (fn2-q1c-outbox fn2-core) 0 fn2-core fn2-sim fn2-own))
         ((mv & fn2-core fn2-sim fn2-own) (fn2-sim-advance-with-clients nil nil fn2-core fn2-sim fn2-own)))
      (fn2-q1c-scribe-rounds (- fuel 1) fn2-core fn2-sim fn2-own))))
(defun fn2-q1c-copy-image (left fn2-sim fn2-recovery-image)
  (declare (xargs :stobjs (fn2-sim fn2-recovery-image) :verify-guards nil :measure (nfix left)))
  (if (zp left) (mv :ok fn2-recovery-image)
    (mv-let (code fn2-recovery-image) (fn2-sim-recovery-copy-sector (- left 1) fn2-sim fn2-recovery-image)
      (if (eq code :ok) (fn2-q1c-copy-image (- left 1) fn2-sim fn2-recovery-image) (mv code fn2-recovery-image)))))
(defun fn2-q1c-classes (i n fn2-recovery-image)
  (declare (xargs :stobjs fn2-recovery-image :verify-guards nil :measure (nfix (- (nfix n) (nfix i)))))
  (if (or (not (natp i)) (not (natp n)) (>= i n)) nil
    (cons (fn2-recovery-sector i fn2-recovery-image) (fn2-q1c-classes (+ 1 i) n fn2-recovery-image))))
; (mv stop acknowledged classes): the scribe on the simulator's fault-free storage for ROUNDS
; rounds from SEED; the device image after them, decoded sector by sector by recover-stub's
; independent v1 decoder (CORRUPT, when given, changes one payload byte of sector 0 first).
(defun fn2-scribe-served-cycle (seed rounds corrupt)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (answer fn2-core)
      (with-local-stobj fn2-sim
        (mv-let (answer fn2-core fn2-sim)
          (with-local-stobj fn2-own
            (mv-let (answer fn2-core fn2-sim fn2-own)
              (with-local-stobj fn2-recovery-image
                (mv-let (answer fn2-core fn2-sim fn2-own fn2-recovery-image)
                  (b* ((profile *fn2-q1c-scribe-profile*)
                       (fn2-core (fn2-init-executor profile :null t fn2-core))
                       (fn2-sim (fn2-sim-init seed :none "q1-contracts" profile fn2-sim))
                       (fn2-sim (fn2-sim-echo-network-reset fn2-sim))
                       (fn2-own (fn2-own-init profile fn2-own))
                       ((mv fn2-core fn2-sim fn2-own) (fn2-q1c-scribe-rounds rounds fn2-core fn2-sim fn2-own))
                       (id (fn2-machine-scribe-id fn2-core))
                       (ack (fn2-machine-completed id fn2-core))
                       (n (fn2-sim-sectors profile))
                       (fn2-recovery-image (fn2-recovery-init n fn2-recovery-image))
                       ((mv code fn2-recovery-image) (fn2-q1c-copy-image n fn2-sim fn2-recovery-image))
                       (fn2-recovery-image (if corrupt
                                               (fn2-recovery-put-byte (+ *fn2-format-payload-offset* 7) 85 fn2-recovery-image)
                                             fn2-recovery-image)))
                    (mv (list (fn2-core-stop-reason fn2-core) ack code (fn2-q1c-classes 0 n fn2-recovery-image))
                        fn2-core fn2-sim fn2-own fn2-recovery-image))
                  (mv answer fn2-core fn2-sim fn2-own)))
              (mv answer fn2-core fn2-sim)))
          (mv answer fn2-core)))
      answer)))
(defun fn2-q1c-valid-prefix-p (k classes)
  (declare (xargs :verify-guards nil))
  (or (zp k) (and (consp classes) (eq (car classes) :valid) (fn2-q1c-valid-prefix-p (- k 1) (cdr classes)))))
; Every sector the scribe acknowledged (fn2-machine-completed) decodes :valid,
; the core never stopped, and the image copied whole: on the fault-free
; device, for any seed and up to 3000 rounds.
(defthm-owed fn2-scribe-reads-back (seed rounds)
  (implies (and (natp seed) (natp rounds) (<= rounds 3000))
           (let ((r (fn2-scribe-served-cycle seed rounds nil)))
             (and (equal (nth 0 r) 0) (eq (nth 2 r) :ok)
                  (fn2-q1c-valid-prefix-p (nth 1 r) (nth 3 r)))))
  :schema :invariant :claim :semantic
  :teeth (fn2-scribe-reads-back-positive fn2-scribe-reads-back-corrupted)
  :doc "Every sector the scribe acknowledged on the fault-free simulated device decodes valid under recover-stub's independent v1 decoder (magic, version, address, sequence, recomputed checksum); the core never stops.")
(defun fn2-q1c-scribe-ok (seed rounds)
  (declare (xargs :verify-guards nil))
  (let ((r (fn2-scribe-served-cycle seed rounds nil)))
    (and (equal (nth 0 r) 0) (eq (nth 2 r) :ok) (fn2-q1c-valid-prefix-p (nth 1 r) (nth 3 r)) (nth 1 r))))
; Positive: one sector acknowledged after 400 rounds and all four after 2000,
; on two seeds, each decoding valid.
(defun fn2-scribe-reads-back-positive ()
  (declare (xargs :verify-guards nil))
  (let ((a (fn2-q1c-scribe-ok 1000 400)) (b (fn2-q1c-scribe-ok 1001 2000)))
    (and a b (<= 1 a) (= b 4))))
; Negative: the conclusion refuses a damaged device: the same run with one
; payload byte of the acknowledged sector 0 changed in the image decodes
; :torn-corrupt, so the acknowledged prefix is not valid.
(defun fn2-scribe-reads-back-corrupted ()
  (declare (xargs :verify-guards nil))
  (let ((r (fn2-scribe-served-cycle 1001 2000 t)))
    (and (<= 1 (nth 1 r)) (eq (car (nth 3 r)) :torn-corrupt)
         (not (fn2-q1c-valid-prefix-p (nth 1 r) (nth 3 r))))))

(fn2-assert-owed-teeth fn2-conn-wire-correct fn2-echo-replies-its-input fn2-listener-admits-within-ledger
                       fn2-scribe-reads-back)
(value-triple (cw "Q1 CONTRACTS: conn, echo, listener and scribe teeth PASS~%"))
