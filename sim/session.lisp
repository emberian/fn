; Layer D's simulator session for the surface harness (tests/surface/
; sim_target.py; the Python side is tests/surface/fn2_sim_session.py, which
; lds tests/sim-session.lsp: this book and the session's output settings).
; A long-lived ACL2 process holds the served core (the listener admitting
; fn2-conn) and the simulator's network as top-level stobjs; each harness
; call is one top-level form, and each answer one line
;   @@FN2SS <keyword> <hex octets> <closed 0|1> <id>@@
; Calls (deterministic given the seed of fn2-ss-start):
;   (fn2-ss-start SEED)               init core, simulator, monitor
;   (fn2-ss-open)                     admit one connection; answer its greeting
;   (fn2-ss-send ID OCTETS CHUNKS)    deliver OCTETS in CHUNKS (each delivered,
;                                     then the node runs to quiescence)
;   (fn2-ss-close ID)                 client EOF, then quiescence
;   (fn2-ss-stop)                     WIRE (sim/check-wire.lisp) per connection
; Quiescence: 64 rounds in a row in which the core's turn ended :idle (no
; machine runnable, no wake due, no observation unharvested), emitted no
; action, and no client octets moved (every round observes a clock reading). Network
; faults follow the seed; process death is excluded (probability 0).
(in-package "ACL2")
(include-book "seeded-store")
(include-book "echo")
(include-book "check-wire")

;; The session serves reading (D6) over the seeded store (seeded-store.lisp).

; Client records live in a global table (test-side): id -> (nonce sent
; received closed cap). The id is a serial number per open (the global
; fn2-ss-serial), never the capability slot: a slot's next incarnation is
; a new connection with its own record and its own WIRE verdict at stop.
; Only live records are walked: a record leaves the live table for the
; retired list (fn2-ss-retired) once its connection closed and its call
; answered, so every call costs the live connections (at most the network
; slots), never the opens so far; stop judges retired and live.
(defun fn2-ss-hex-digit (n) (declare (xargs :verify-guards nil)) (char "0123456789abcdef" n))
(defun fn2-ss-hex (octets)
  (declare (xargs :verify-guards nil))
  (if (atom octets) nil
    (list* (fn2-ss-hex-digit (floor (car octets) 16)) (fn2-ss-hex-digit (mod (car octets) 16))
           (fn2-ss-hex (cdr octets)))))
(defun fn2-ss-say (tag octets closed id)
  (declare (xargs :verify-guards nil))
  (cw "@@FN2SS ~s0 ~s1 ~x2 ~x3@@~%" tag (if octets (coerce (fn2-ss-hex octets) 'string) "-") (if closed 1 0) id))

(defun fn2-ss-outbox-count (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (n) (fn2-outbox-queued fn2-ops) n))
(defun fn2-ss-read (left cap nonce acc fn2-sim-network)
  (declare (xargs :stobjs fn2-sim-network :verify-guards nil :measure (nfix left)))
  (if (zp left) (mv acc fn2-sim-network)
    (mv-let (code byte fn2-sim-network) (fn2-network-client-read cap nonce fn2-sim-network)
      (if (not (eq code :ok)) (mv acc fn2-sim-network)
        (fn2-ss-read (- left 1) cap nonce (cons byte acc) fn2-sim-network)))))
(defun fn2-ss-feed (bytes cap nonce fn2-sim-network)
  (declare (xargs :stobjs fn2-sim-network :verify-guards nil))
  (if (atom bytes) (mv nil fn2-sim-network)
    (mv-let (code fn2-sim-network) (fn2-network-client-byte cap nonce (car bytes) fn2-sim-network)
      (if (not (eq code :ok)) (mv bytes fn2-sim-network)
        (fn2-ss-feed (cdr bytes) cap nonce fn2-sim-network)))))

; Drain every tracked connection's pipe into its record; returns whether
; any octet moved or any connection newly closed.
(defun fn2-ss-drain (clients fn2-sim)
  (declare (xargs :stobjs fn2-sim :verify-guards nil))
  (if (atom clients) (mv nil nil fn2-sim)
    (b* ((id (car (car clients))) (r (cdr (car clients)))
         (nonce (nth 0 r))
         ((mv got closed fn2-sim)
          (stobj-let ((fn2-sim-network (fn2-sim-net fn2-sim)))
            (got closed fn2-sim-network)
            (if (nth 3 r) (mv nil t fn2-sim-network)
              (mv-let (got fn2-sim-network)
                (fn2-ss-read *fn2-sim-network-capacity* (nth 4 r) nonce nil fn2-sim-network)
                (mv got (not (eq (fn2-network-cap-code (nth 4 r) nonce fn2-sim-network) :ok)) fn2-sim-network)))
            (mv got closed fn2-sim)))
         (moved (or (consp got) (and closed (not (nth 3 r)))))
         (r (list nonce (nth 1 r) (append got (nth 2 r)) closed (nth 4 r)))
         ((mv rest any fn2-sim) (fn2-ss-drain (cdr clients) fn2-sim)))
      (mv (cons (cons id r) rest) (or moved any) fn2-sim))))

(defun fn2-ss-run (fuel idle allow clients fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil :measure (nfix fuel)))
  (if (or (zp fuel) (<= 64 idle)) (mv clients fn2-core fn2-sim fn2-own)
    (b* (((mv & fn2-core fn2-sim fn2-own)
          (fn2-sim-take-prefix (fn2-ss-outbox-count fn2-core) 0 fn2-core fn2-sim fn2-own))
         ((mv status & & nactions fn2-core) (fn2-turn fn2-core))
         ((mv & fn2-core fn2-sim fn2-own)
          (fn2-sim-take-prefix (fn2-ss-outbox-count fn2-core) 0 fn2-core fn2-sim fn2-own))
         ((mv clients moved fn2-sim) (fn2-ss-drain clients fn2-sim))
         ((mv & fn2-core fn2-sim fn2-own) (fn2-sim-advance-with-clients nil allow fn2-core fn2-sim fn2-own))
         ;; a turn that ends :more (a machine runnable, a wake due, an
         ;; observation unharvested) is the node working, never idle: the
         ;; sealer's background seals share the visits a reply waits on
         (idle (if (or moved (< 0 nactions) (not (eq status :idle))
                       (not (equal (fn2-core-stop-reason fn2-core) 0)))
                   0 (+ 1 idle)))
         (idle (if (equal (fn2-core-stop-reason fn2-core) 0) idle 64)))
      (fn2-ss-run (- fuel 1) idle allow clients fn2-core fn2-sim fn2-own))))

;; The simulated device spans every extent B's allocator can name under the
;; profile (:extent-slots extents of *fn2-commit-extent-bytes*), so a seeded
;; or posted article's extent is on the device; the simulator's default
;; device (4 or 16 sectors) is smaller than one profile's extent space.
(defconst *fn2-ss-sim-profile*
  (put-assoc-equal :sim-sectors
                   (ceiling (* (fn2-b-capacity :extent-slots 16 *fn2-ss-profile*) *fn2-commit-extent-bytes*)
                            *fn2-format-sector-bytes*)
                   *fn2-ss-profile*))
;; The seeds' storage writes ((OFFSET . OCTETS) ...) put on the simulated
;; device, durable, before any client: the device the reads are served from.
;; (mv code fn2-sim-storage): the first write the device refuses is the code.
(defun fn2-ss-put-octets (addr octets fn2-sim-storage)
  (declare (xargs :stobjs fn2-sim-storage :verify-guards nil :measure (len octets)))
  (if (atom octets) (mv :ok fn2-sim-storage)
    (mv-let (code fn2-sim-storage) (fn2-storage-write-byte addr addr (car octets) 0 t nil fn2-sim-storage)
      (if (not (eq code :ok)) (mv (list :device code addr) fn2-sim-storage)
        (fn2-ss-put-octets (+ 1 addr) (cdr octets) fn2-sim-storage)))))
(defun fn2-ss-put-store (store fn2-sim)
  (declare (xargs :stobjs fn2-sim :verify-guards nil :measure (len store)))
  (if (atom store) (mv :ok fn2-sim)
    (mv-let (code fn2-sim)
      (stobj-let ((fn2-sim-storage (fn2-sim-disk fn2-sim))) (code fn2-sim-storage)
        (fn2-ss-put-octets (car (car store)) (cdr (car store)) fn2-sim-storage) (mv code fn2-sim))
      (if (not (eq code :ok)) (mv code fn2-sim) (fn2-ss-put-store (cdr store) fn2-sim)))))
; The served core of PROFILE over the seeded store on the simulated device,
; before any client: (mv code fn2-core fn2-sim fn2-own), CODE :ok or the refused
; seed or device write.
(defun fn2-ss-boot (seed profile fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
  (b* ((fn2-core (fn2-init-executor profile :echo nil fn2-core))
       ((mv seeded store fn2-core) (fn2-cs-seed-all *fn2-ss-seeds* 1 fn2-core))
       (fn2-sim (fn2-sim-init seed :crash-only "sim-session" profile fn2-sim))
       ((mv put fn2-sim) (fn2-ss-put-store store fn2-sim))
       (fn2-sim (fn2-sim-echo-network-reset fn2-sim))
       (fn2-sim (update-fn2-sim-probabilitiesi *fn2-fault-crash* 0 fn2-sim))
       (fn2-sim (update-fn2-sim-fault-budget 100000 fn2-sim))
       (fn2-own (fn2-own-init profile fn2-own)))
    (mv (if (eq seeded :ok) put (list :seed seeded)) fn2-core fn2-sim fn2-own)))
(defun fn2-ss-start (seed fn2-core fn2-sim fn2-own state)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own state) :verify-guards nil))
  (b* (((mv code fn2-core fn2-sim fn2-own) (fn2-ss-boot seed *fn2-ss-sim-profile* fn2-core fn2-sim fn2-own))
       (- (or (eq code :ok) (cw "seeding refused: ~x0~%" code)))
       (state (f-put-global 'fn2-ss-clients nil state))
       (state (f-put-global 'fn2-ss-retired nil state))
       (state (f-put-global 'fn2-ss-serial 0 state)))
    ;; a refused seed answers "unseeded": the harness's start expects "started"
    (prog2$ (fn2-ss-say (if (eq code :ok) "started" "unseeded") nil nil seed)
            (mv fn2-core fn2-sim fn2-own state))))

; Whether a record tracks slot CAP's incarnation NONCE.
(defun fn2-ss-known (cap nonce clients)
  (declare (xargs :verify-guards nil))
  (and (consp clients)
       (or (and (equal (nth 4 (cdr (car clients))) cap) (equal (nth 0 (cdr (car clients))) nonce))
           (fn2-ss-known cap nonce (cdr clients)))))
; The first open network slot whose incarnation is not yet tracked.
(defun fn2-ss-fresh (left clients fn2-sim-network)
  (declare (xargs :stobjs fn2-sim-network :verify-guards nil :measure (nfix left)))
  (if (zp left) (mv nil 0 0)
    (let* ((cap (- left 1)) (nonce (fn2-sim-network-nonce cap fn2-sim-network)))
      (if (and (eq (fn2-network-cap-code cap nonce fn2-sim-network) :ok)
               (not (fn2-ss-known cap nonce clients)))
          (mv t cap nonce)
        (fn2-ss-fresh cap clients fn2-sim-network)))))

; Admit one connection: let Accepts complete until a fresh slot is open.
(defun fn2-ss-await (fuel clients fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil :measure (nfix fuel)))
  (b* (((mv found cap nonce)
        (stobj-let ((fn2-sim-network (fn2-sim-net fn2-sim))) (found cap nonce)
          (fn2-ss-fresh (fn2-sim-network-rows fn2-sim-network) clients fn2-sim-network)
          (mv found cap nonce))))
    (if (or found (zp fuel)) (mv found cap nonce fn2-core fn2-sim fn2-own)
      (b* (((mv & fn2-core fn2-sim fn2-own)
            (fn2-sim-take-prefix (fn2-ss-outbox-count fn2-core) 0 fn2-core fn2-sim fn2-own))
           ((mv & & & & fn2-core) (fn2-turn fn2-core))
           ((mv & fn2-core fn2-sim fn2-own)
            (fn2-sim-take-prefix (fn2-ss-outbox-count fn2-core) 0 fn2-core fn2-sim fn2-own))
           ((mv & fn2-core fn2-sim fn2-own) (fn2-sim-advance-with-clients nil t fn2-core fn2-sim fn2-own)))
        (fn2-ss-await (- fuel 1) clients fn2-core fn2-sim fn2-own)))))

(defun fn2-ss-reply (id before clients retired)
  ; The octets ID received since BEFORE (its record's received list); a
  ; retired id (closed) is found in the retired list.
  (declare (xargs :verify-guards nil))
  (let ((r (cdr (or (assoc-equal id clients) (assoc-equal id retired)))))
    (mv (reverse (take (- (len (nth 2 r)) before) (nth 2 r))) (nth 3 r))))

;; Split the live table: closed records join RETIRED (consed, no append).
(defun fn2-ss-retire (clients live retired)
  (declare (xargs :verify-guards nil))
  (if (atom clients) (mv (reverse live) retired)
    (if (nth 3 (cdr (car clients)))
        (fn2-ss-retire (cdr clients) live (cons (car clients) retired))
      (fn2-ss-retire (cdr clients) (cons (car clients) live) retired))))
(defun fn2-ss-keep (clients state)
  (declare (xargs :stobjs state :verify-guards nil))
  (mv-let (live retired) (fn2-ss-retire clients nil (f-get-global 'fn2-ss-retired state))
    (let ((state (f-put-global 'fn2-ss-retired retired state)))
      (f-put-global 'fn2-ss-clients live state))))
; Admit connection ID: the first fresh open slot, its record, quiescence.
; (mv found clients fn2-core fn2-sim fn2-own)
(defun fn2-ss-admit (id clients fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
  (b* (((mv found cap nonce fn2-core fn2-sim fn2-own) (fn2-ss-await 4000 clients fn2-core fn2-sim fn2-own))
       ((unless found) (mv nil clients fn2-core fn2-sim fn2-own))
       (clients (cons (cons id (list nonce nil nil nil cap)) clients))
       ((mv clients fn2-core fn2-sim fn2-own) (fn2-ss-run 20000 0 nil clients fn2-core fn2-sim fn2-own)))
    (mv t clients fn2-core fn2-sim fn2-own)))
(defun fn2-ss-open (fn2-core fn2-sim fn2-own state)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own state) :verify-guards nil))
  (b* ((id (+ 1 (nfix (f-get-global 'fn2-ss-serial state))))
       ((mv found clients fn2-core fn2-sim fn2-own)
        (fn2-ss-admit id (f-get-global 'fn2-ss-clients state) fn2-core fn2-sim fn2-own))
       ((unless found) (prog2$ (fn2-ss-say "refused" nil t -1) (mv fn2-core fn2-sim fn2-own state)))
       (state (f-put-global 'fn2-ss-serial id state))
       ((mv got closed) (fn2-ss-reply id 0 clients (f-get-global 'fn2-ss-retired state)))
       (state (fn2-ss-keep clients state)))
    (prog2$ (fn2-ss-say "open" got closed id) (mv fn2-core fn2-sim fn2-own state))))

(defun fn2-ss-chunks (octets chunks fuel)
  ; OCTETS cut at the CHUNKS sizes; the remainder is one chunk.
  (declare (xargs :verify-guards nil :measure (nfix fuel)))
  (if (or (zp fuel) (atom octets)) nil
    (let ((k (if (and (consp chunks) (posp (car chunks))) (min (car chunks) (len octets)) (len octets))))
      (cons (take k octets) (fn2-ss-chunks (nthcdr k octets) (if (consp chunks) (cdr chunks) nil) (- fuel 1))))))

(defun fn2-ss-deliver (fuel pieces id clients fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil :measure (nfix fuel)))
  (if (or (zp fuel) (atom pieces)) (mv clients fn2-core fn2-sim fn2-own)
    (b* ((r (cdr (assoc-equal id clients)))
         ((when (or (null r) (nth 3 r))) (mv clients fn2-core fn2-sim fn2-own))
         ((mv rest fn2-sim)
          (stobj-let ((fn2-sim-network (fn2-sim-net fn2-sim))) (rest fn2-sim-network)
            (fn2-ss-feed (car pieces) (nth 4 r) (nth 0 r) fn2-sim-network) (mv rest fn2-sim)))
         (sent (take (- (len (car pieces)) (len rest)) (car pieces)))
         (clients (put-assoc-equal id (list (nth 0 r) (append (nth 1 r) sent) (nth 2 r) (nth 3 r) (nth 4 r)) clients))
         ((mv clients fn2-core fn2-sim fn2-own) (fn2-ss-run 20000 0 nil clients fn2-core fn2-sim fn2-own))
         ; A piece the pipe could not take whole is retried after the node ran.
         (pieces (if (consp rest) (cons rest (cdr pieces)) (cdr pieces))))
      (fn2-ss-deliver (- fuel 1) pieces id clients fn2-core fn2-sim fn2-own))))

;; One client send on ID: OCTETS delivered in CHUNKS, each to quiescence.
;; (mv got closed clients fn2-core fn2-sim fn2-own): GOT the octets ID
;; received meanwhile.
(defun fn2-ss-exchange (id octets chunks clients retired fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
  (b* ((before (len (nth 2 (cdr (or (assoc-equal id clients) (assoc-equal id retired))))))
       ((mv clients fn2-core fn2-sim fn2-own)
        (fn2-ss-deliver (+ 64 (* 4 (len octets))) (fn2-ss-chunks octets chunks (len octets)) id clients
                        fn2-core fn2-sim fn2-own))
       ((mv got closed) (fn2-ss-reply id before clients retired)))
    (mv got closed clients fn2-core fn2-sim fn2-own)))
(defun fn2-ss-send (id octets chunks fn2-core fn2-sim fn2-own state)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own state) :verify-guards nil))
  (b* (((mv got closed clients fn2-core fn2-sim fn2-own)
        (fn2-ss-exchange id octets chunks (f-get-global 'fn2-ss-clients state) (f-get-global 'fn2-ss-retired state)
                         fn2-core fn2-sim fn2-own))
       (state (fn2-ss-keep clients state)))
    (prog2$ (fn2-ss-say "reply" got closed id) (mv fn2-core fn2-sim fn2-own state))))

(defun fn2-ss-close (id fn2-core fn2-sim fn2-own state)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own state) :verify-guards nil))
  (b* ((clients (f-get-global 'fn2-ss-clients state))
       (r (cdr (assoc-equal id clients)))
       (before (len (nth 2 (or r (cdr (assoc-equal id (f-get-global 'fn2-ss-retired state)))))))
       ; Drain what the node already sent before the client's EOF.
       ((mv clients fn2-core fn2-sim fn2-own) (fn2-ss-run 20000 0 nil clients fn2-core fn2-sim fn2-own))
       (r (cdr (assoc-equal id clients)))
       (fn2-sim (if (and r (not (nth 3 r)))
                    (stobj-let ((fn2-sim-network (fn2-sim-net fn2-sim))) (fn2-sim-network)
                      (mv-let (code fn2-sim-network) (fn2-network-close (nth 4 r) (nth 0 r) fn2-sim-network)
                        (declare (ignore code)) fn2-sim-network)
                      fn2-sim)
                  fn2-sim))
       (clients (if r (put-assoc-equal id (list (nth 0 r) (nth 1 r) (nth 2 r) t (nth 4 r)) clients) clients))
       ((mv clients fn2-core fn2-sim fn2-own) (fn2-ss-run 20000 0 nil clients fn2-core fn2-sim fn2-own))
       ((mv got &) (fn2-ss-reply id before clients (f-get-global 'fn2-ss-retired state)))
       (state (fn2-ss-keep clients state)))
    (prog2$ (fn2-ss-say "closed" got t id) (mv fn2-core fn2-sim fn2-own state))))

(defun fn2-ss-verdict-lines (clients)
  ; One line per connection: its id and WIRE's verdict (:PASS or the failure).
  (declare (xargs :verify-guards nil))
  (if (atom clients) nil
    (let* ((id (car (car clients))) (r (cdr (car clients)))
           (v (fn2-wire-check (nth 1 r) (reverse (nth 2 r)) (nth 3 r))))
      (prog2$ (cw "@@FN2SS wire ~x0 ~x1@@~%" id v)
              (fn2-ss-verdict-lines (cdr clients))))))
(defun fn2-ss-stop (fn2-core state)
  (declare (xargs :stobjs (fn2-core state) :verify-guards nil))
  (let ((clients (f-get-global 'fn2-ss-clients state)))
    (progn$ (fn2-ss-verdict-lines (f-get-global 'fn2-ss-retired state))
            (fn2-ss-verdict-lines clients)
            (fn2-ss-say "stopped" nil nil (fn2-core-stop-reason fn2-core))
            state)))

;; A unit fixture's session (tests/read-unit.lisp): the node of PROFILE
;; boots under SEED,
;; one connection opens, and each of LINES (strings) is sent whole, CR LF
;; appended, the node run to quiescence after it. (greeting replies) with
;; each reply the octets the connection received for that line;
;; (:unseeded code) or :refused when the session could not start.
(defun fn2-ss-lines (lines id clients fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
  (if (atom lines) (mv nil fn2-core fn2-sim fn2-own)
    (b* (((mv got & clients fn2-core fn2-sim fn2-own)
          (fn2-ss-exchange id (append (fn2-cs-octets (car lines)) (list 13 10)) nil clients nil
                           fn2-core fn2-sim fn2-own))
         ((mv rest fn2-core fn2-sim fn2-own) (fn2-ss-lines (cdr lines) id clients fn2-core fn2-sim fn2-own)))
      (mv (cons got rest) fn2-core fn2-sim fn2-own))))
(defun fn2-ss-transcript (seed profile lines)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core)
      (with-local-stobj fn2-sim
        (mv-let (result fn2-core fn2-sim)
          (with-local-stobj fn2-own
            (mv-let (result fn2-core fn2-sim fn2-own)
              (b* (((mv code fn2-core fn2-sim fn2-own) (fn2-ss-boot seed profile fn2-core fn2-sim fn2-own))
                   ((unless (eq code :ok)) (mv (list :unseeded code) fn2-core fn2-sim fn2-own))
                   ((mv found clients fn2-core fn2-sim fn2-own) (fn2-ss-admit 1 nil fn2-core fn2-sim fn2-own))
                   ((unless found) (mv :refused fn2-core fn2-sim fn2-own))
                   ((mv greeting &) (fn2-ss-reply 1 0 clients nil))
                   ((mv replies fn2-core fn2-sim fn2-own) (fn2-ss-lines lines 1 clients fn2-core fn2-sim fn2-own)))
                (mv (list greeting replies) fn2-core fn2-sim fn2-own))
              (mv result fn2-core fn2-sim)))
          (mv result fn2-core)))
      result)))
