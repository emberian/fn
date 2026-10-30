; Layer D under the simulator (ROUND2 section F.2 scenario 1, its plaintext
; anonymous-reader half for D3): the served core with the listener admitting
; fn2-conn, driven by the simulator's adapter and network (fn2-sim-take-one,
; fn2-turn, fn2-sim-advance-with-clients), NNTP clients writing into and
; reading from the simulator's connection pipes, and WIRE
; (sim/check-wire.lisp) over every client's sent and received octets. The
; network fault profile delivers fragmented receives, short sends, delays
; and reordered releases; process death is excluded here (its probability
; is 0; scenario 1's death cuts come with recovery, B's). Run:
;   FN_ACL2=... tools/acl2 < fn2/tests/sim-layer-d.lsp > build/sim-layer-d.log
; and read the SIM-LAYER-D lines; it prints PASS or the first failure.
(in-package "ACL2")
(set-cbd "fn2/tests/")
(include-book "../books/owed-conn")
(include-book "../sim/echo")
(include-book "../sim/check-wire")
(include-book "conn-unit")

(defconst *fn2-sld-profile* (put-assoc-equal :trace nil *fn2-conn-wire-profile*))

; Transcripts: conn-unit's fixtures and seeded random ones, assigned to
; connections in accept order.
(defun fn2-sld-transcripts (n seed)
  (declare (xargs :verify-guards nil :measure (nfix n)))
  (if (zp n) nil
    (cons (fn2-cu-random-transcript (+ 101 (* 7919 seed)))
          (fn2-sld-transcripts (- n 1) (+ 1 seed)))))
(defun fn2-sld-octets-of (fixtures)
  (declare (xargs :verify-guards nil))
  (if (atom fixtures) nil (cons (nth 1 (car fixtures)) (fn2-sld-octets-of (cdr fixtures)))))
(defun fn2-sld-all-transcripts (nrandom)
  (declare (xargs :verify-guards nil))
  (append (fn2-sld-octets-of *fn2-cu-fixtures*) (fn2-sld-transcripts nrandom 0)))

; A client record per network slot: (nonce todo sent received closed index).
(defun fn2-sld-feed (left cap nonce bytes fn2-sim-network)
  (declare (xargs :stobjs fn2-sim-network :verify-guards nil :measure (nfix left)))
  (if (or (zp left) (atom bytes)) (mv bytes fn2-sim-network)
    (mv-let (code fn2-sim-network) (fn2-network-client-byte cap nonce (car bytes) fn2-sim-network)
      (if (not (eq code :ok)) (mv bytes fn2-sim-network)
        (fn2-sld-feed (- left 1) cap nonce (cdr bytes) fn2-sim-network)))))
(defun fn2-sld-read (left cap nonce acc fn2-sim-network)
  (declare (xargs :stobjs fn2-sim-network :verify-guards nil :measure (nfix left)))
  (if (zp left) (mv acc fn2-sim-network)
    (mv-let (code byte fn2-sim-network) (fn2-network-client-read cap nonce fn2-sim-network)
      (if (not (eq code :ok)) (mv acc fn2-sim-network)
        (fn2-sld-read (- left 1) cap nonce (cons byte acc) fn2-sim-network)))))

; One slot: a fresh nonce starts a new client on the next transcript; an
; open client reads everything available and writes its next chunk; a
; capability that is no longer open marks the client closed.
(defun fn2-sld-slot (cap record transcripts next word fn2-sim-network)
  (declare (xargs :stobjs fn2-sim-network :verify-guards nil))
  (b* ((nonce (fn2-sim-network-nonce cap fn2-sim-network))
       (fresh (and (not (equal nonce (nth 0 record)))
                   (equal (fn2-network-cap-code cap nonce fn2-sim-network) :ok)))
       ((mv record next)
        (if (and fresh (< next (len transcripts)))
            (mv (list nonce (nth next transcripts) nil nil nil next) (+ 1 next))
          (mv record next)))
       ((when (or (null (nth 5 record)) (nth 4 record))) (mv record next fn2-sim-network))
       ((unless (eq (fn2-network-cap-code cap (nth 0 record) fn2-sim-network) :ok))
        (mv (update-nth 4 t record) next fn2-sim-network))
       ((mv received fn2-sim-network)
        (fn2-sld-read *fn2-sim-network-capacity* cap (nth 0 record) (nth 3 record) fn2-sim-network))
       (chunk (+ 1 (mod (nfix word) 37)))
       ((mv todo fn2-sim-network) (fn2-sld-feed chunk cap (nth 0 record) (nth 1 record) fn2-sim-network))
       (sent (append (nth 2 record) (take (- (len (nth 1 record)) (len todo)) (nth 1 record)))))
    (mv (list (nth 0 record) todo sent received nil (nth 5 record)) next fn2-sim-network)))
(defun fn2-sld-slots (left records transcripts next word fn2-sim-network)
  (declare (xargs :stobjs fn2-sim-network :verify-guards nil :measure (nfix left)))
  (if (zp left) (mv nil next fn2-sim-network)
    (b* ((cap (- left 1))
         ((mv record next fn2-sim-network)
          (fn2-sld-slot cap (car records) transcripts next (+ (nfix word) (* 31 cap)) fn2-sim-network))
         ((mv rest next fn2-sim-network)
          (fn2-sld-slots cap (cdr records) transcripts next word fn2-sim-network)))
      (mv (cons record rest) next fn2-sim-network))))
(defun fn2-sld-client-round (records transcripts next word fn2-sim)
  (declare (xargs :stobjs fn2-sim :verify-guards nil))
  (stobj-let ((fn2-sim-network (fn2-sim-net fn2-sim)))
    (records next fn2-sim-network)
    (fn2-sld-slots (fn2-sim-network-rows fn2-sim-network) records transcripts next word fn2-sim-network)
    (mv records next fn2-sim)))
(defun fn2-sld-empty-records (n)
  (declare (xargs :verify-guards nil))
  (if (zp n) nil (cons (list -1 nil nil nil nil nil) (fn2-sld-empty-records (- n 1)))))
(defun fn2-sld-outbox-count (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (n) (fn2-outbox-queued fn2-ops) n))

; Every client the run started has been served: its octets all sent and
; either closed or its expected greeting-only/idle tail reached.
(defun fn2-sld-quiet-p (records)
  (declare (xargs :verify-guards nil))
  (if (atom records) t
    (and (or (null (nth 5 (car records))) (nth 4 (car records)) (atom (nth 1 (car records))))
         (fn2-sld-quiet-p (cdr records)))))

; Records a slot's new client displaced (kept for WIRE).
(defun fn2-sld-retired (before after)
  (declare (xargs :verify-guards nil))
  (if (or (atom before) (atom after)) nil
    (append (and (nth 5 (car before)) (not (equal (nth 5 (car before)) (nth 5 (car after))))
                 (list (car before)))
            (fn2-sld-retired (cdr before) (cdr after)))))
(defun fn2-sld-rounds (fuel idle records transcripts next done fn2-core fn2-sim fn2-own)
  (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil :measure (nfix fuel)))
  (if (zp fuel) (mv :fuel records next done fn2-core fn2-sim fn2-own)
    (b* (((mv & fn2-core fn2-sim fn2-own)
          (fn2-sim-take-prefix (fn2-sld-outbox-count fn2-core) 0 fn2-core fn2-sim fn2-own))
         ((mv & & & nactions fn2-core) (fn2-turn fn2-core))
         ((unless (equal (fn2-core-stop-reason fn2-core) 0))
          (mv (list :fail :core-stopped (fn2-stop-reason-code->keyword (fn2-core-stop-reason fn2-core)))
              records next done fn2-core fn2-sim fn2-own))
         ((mv & fn2-core fn2-sim fn2-own)
          (fn2-sim-take-prefix (fn2-sld-outbox-count fn2-core) 0 fn2-core fn2-sim fn2-own))
         ((mv word fn2-sim) (fn2-sim-random fn2-sim))
         (before records)
         ((mv records next fn2-sim) (fn2-sld-client-round records transcripts next word fn2-sim))
         ((mv & fn2-core fn2-sim fn2-own)
          (fn2-sim-advance-with-clients nil (< next (len transcripts)) fn2-core fn2-sim fn2-own))
         ; Progress is an action the core emitted or a client's octets (every round
         ; observes a clock reading, so observations are not progress); a held Accept
         ; (no client left to connect) is re-delayed by the adapter forever.
         (busy (or (not (equal before records)) (< 0 nactions)))
         (idle (if busy 0 (+ 1 idle)))
         (done (append (fn2-sld-retired before records) done)))
      (if (and (<= 64 idle) (>= next (len transcripts)) (fn2-sld-quiet-p records))
          (mv :quiet records next done fn2-core fn2-sim fn2-own)
        (fn2-sld-rounds (- fuel 1) idle records transcripts next done fn2-core fn2-sim fn2-own)))))

;; The simulator posts clock readings, so a DATE reply is 111 and a
;; 14-digit UTC date where conn-unit (no clock) has 503: the date-mode
;; fixture matches line by line except that line, which must be 111 DIGITS.
(defun fn2-sld-lines (octets cur acc)
  (declare (xargs :verify-guards nil))
  (cond ((atom octets) (reverse (if cur (cons (reverse cur) acc) acc)))
        ((and (equal (car octets) 13) (consp (cdr octets)) (equal (cadr octets) 10))
         (fn2-sld-lines (cddr octets) nil (cons (reverse cur) acc)))
        (t (fn2-sld-lines (cdr octets) (cons (car octets) cur) acc))))
(defun fn2-sld-digits-p (l)
  (declare (xargs :verify-guards nil))
  (if (atom l) t (and (natp (car l)) (<= 48 (car l)) (<= (car l) 57) (fn2-sld-digits-p (cdr l)))))
(defun fn2-sld-date-line-p (line)
  (declare (xargs :verify-guards nil))
  (and (equal (len line) 18) (equal (take 4 line) '(49 49 49 32))
       (fn2-sld-digits-p (nthcdr 4 line))))
(defun fn2-sld-fixture-match (i wire closed)
  (declare (xargs :verify-guards nil))
  (let ((want (fn2-cu-expected (nth i *fn2-cu-fixtures*))))
    (if (not (equal (car (nth i *fn2-cu-fixtures*)) 'date-mode))
        (equal (list wire closed) want)
      (let ((got (fn2-sld-lines wire nil nil)) (exp (fn2-sld-lines (car want) nil nil)))
        (and (equal closed (cadr want)) (equal (len got) (len exp))
             (equal (car got) (car exp)) (fn2-sld-date-line-p (cadr got))
             (equal (cddr got) (cddr exp)))))))

;; WIRE over every client record.
(defun fn2-sld-wire (records)
  (declare (xargs :verify-guards nil))
  (if (atom records) :pass
    (let ((r (car records)))
      (if (null (nth 5 r)) (fn2-sld-wire (cdr records))
        (let* ((wire (reverse (nth 3 r)))
               (v (fn2-wire-check (nth 2 r) wire (nth 4 r)))
               ; A fixture's client must receive exactly the fixture's reply
               ; bytes and close, under any network schedule (T8).
               (i (nth 5 r))
               (v (if (and (eq v :pass) (< i (len *fn2-cu-fixtures*))
                           (not (fn2-sld-fixture-match i wire (nth 4 r))))
                      (list :fail :fixture-bytes i wire) v)))
          (if (eq v :pass) (fn2-sld-wire (cdr records))
            (list :wire-fail (nth 5 r) v (nth 2 r) (reverse (nth 3 r)))))))))
(defun fn2-sld-count-served (records)
  (declare (xargs :verify-guards nil))
  (if (atom records) 0 (+ (if (nth 5 (car records)) 1 0) (fn2-sld-count-served (cdr records)))))

; One run: SEED, the simulator fault profile, and how many random
; transcripts follow the fixtures. Connections are at most the profile's C
; at once; the run reuses connection rows as clients close.
(defun fn2-sld-run (seed fault-profile nrandom)
  (declare (xargs :verify-guards nil))
  (let ((transcripts (fn2-sld-all-transcripts nrandom)))
    (with-local-stobj fn2-core
      (mv-let (answer fn2-core)
        (with-local-stobj fn2-sim
          (mv-let (answer fn2-core fn2-sim)
            (with-local-stobj fn2-own
              (mv-let (answer fn2-core fn2-sim fn2-own)
                (b* ((fn2-core (fn2-init-executor *fn2-sld-profile* :echo nil fn2-core))
                     (fn2-sim (fn2-sim-init seed fault-profile "sim-layer-d" *fn2-sld-profile* fn2-sim))
                     (fn2-sim (fn2-sim-echo-network-reset fn2-sim))
                     ; Network faults land (every hit spends the budget); process
                     ; death is excluded by its probability, not by the budget.
                     (fn2-sim (update-fn2-sim-probabilitiesi *fn2-fault-crash* 0 fn2-sim))
                     (fn2-sim (update-fn2-sim-fault-budget 100000 fn2-sim))
                     (fn2-own (fn2-own-init *fn2-sld-profile* fn2-own))
                     (nrows (stobj-let ((fn2-sim-network (fn2-sim-net fn2-sim))) (n)
                              (fn2-sim-network-rows fn2-sim-network) n))
                     ((mv status records next done fn2-core fn2-sim fn2-own)
                      (fn2-sld-rounds (* 4000 (+ 1 (len transcripts))) 0 (fn2-sld-empty-records nrows)
                                      transcripts 0 nil fn2-core fn2-sim fn2-own)))
                  (mv (list status next (fn2-sld-count-served (append done records)) (fn2-sld-wire (append done records))
                            (fn2-sim-deaths fn2-sim)
                            (list (fn2-sim-hitsi *fn2-fault-fragment* fn2-sim) (fn2-sim-hitsi *fn2-fault-short-send* fn2-sim)
                                  (fn2-sim-hitsi *fn2-fault-delay* fn2-sim) (fn2-sim-hitsi *fn2-fault-release-order* fn2-sim)))
                      fn2-core fn2-sim fn2-own))
                (mv answer fn2-core fn2-sim)))
            (mv answer fn2-core)))
        answer))))

(defun fn2-sld-seeds (seeds fault-profile nrandom)
  (declare (xargs :verify-guards nil))
  (if (atom seeds) :pass
    (let ((r (fn2-sld-run (car seeds) fault-profile nrandom)))
      (progn$
       (cw "SIM-LAYER-D seed=~x0 faults=~x1 status=~x2 started=~x3 served=~x4 deaths=~x5 hits(fragment short-send delay release-order)=~x7 wire=~x6~%"
           (car seeds) fault-profile (nth 0 r) (nth 1 r) (nth 2 r) (nth 4 r)
           (if (eq (nth 3 r) :pass) :pass (list (nth 0 (nth 3 r)) (nth 1 (nth 3 r)) (nth 2 (nth 3 r))))
           (nth 5 r))
       (if (and (eq (nth 0 r) :quiet) (eq (nth 3 r) :pass))
           (fn2-sld-seeds (cdr seeds) fault-profile nrandom)
         (list :fail (car seeds) r))))))

(value-triple (cw "SIM-LAYER-D NONE ~x0~%" (fn2-sld-seeds '(1 2 3) :none 8)))
(value-triple (cw "SIM-LAYER-D NETWORK ~x0~%" (fn2-sld-seeds '(11 12 13 14 15 16 17 18) :crash-only 8)))
(good-bye)
