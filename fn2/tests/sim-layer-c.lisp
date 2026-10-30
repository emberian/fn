; Layer C acceptance, first part: scenario M3 (STORAGE-DESIGN M3; EXECUTION-MODEL
; F.2 scenarios 5 and 17's IDENTITY half). Offers drawn from a seeded
; generator over a small Message-ID and content space are decided by up to
; three decisions in flight at once, their steps interleaved by the
; generator, each recorded when it finishes; the overlay is sealed into a
; run (with its Ribbon filter) at generated points while decisions are in
; flight. The staging workspace holding every offer's octets is then
; released, the overlay sealed, every (Message-ID, content) pair queried,
; and the Binding read back by the real scan of every installed run. The
; trace is judged by the independent IDENTITY checker (sim/check-identity).
; A :stale offer (decided around a later record or seal) is offered again.
; Controls: the same schedules with the stamp check defeated (the test
; refreshes a decision's stamp just before its record) give accepted second
; contents the checker refuses by name.
; Scope: the engine in the pool, every page sealed and checked by B's code;
; the device leg (run pages written through the commit batch, recovery)
; waits on C1c and B's GC2 member.
(in-package "ACL2")
(include-book "runs-assembly")
(include-book "../sim/check-identity")
(include-book "../sim/prng")

(defconst *fn2-m3-slots* 3)
(defun fn2-m3-q (d) (declare (xargs :guard (natp d))) (+ 2000 (* 300 d)))
(defun fn2-m3-digits (n k)
 (declare (xargs :verify-guards nil :measure (nfix k)))
 (if (zp k) nil (append (fn2-m3-digits (floor n 10) (- k 1)) (list (+ 48 (mod n 10))))))
(defun fn2-m3-mid (j) (declare (xargs :verify-guards nil)) (append (list 60 109) (fn2-m3-digits j 3) (list 64 99 62)))
(defun fn2-m3-content (b) (declare (xargs :verify-guards nil)) (make-list 32 :initial-element b))

;; Offers: N pairs (Message-ID in 0..5, content in 1..5) from SEED.
(defun fn2-m3-offers (n s0 s1 s2 s3)
 (declare (xargs :verify-guards nil :measure (nfix n)))
 (if (zp n) nil
  (b* (((mv j s0 s1 s2 s3) (fn2-prng-below 6 s0 s1 s2 s3))
       ((mv b s0 s1 s2 s3) (fn2-prng-below 5 s0 s1 s2 s3)))
   (cons (list (fn2-m3-mid j) (fn2-m3-content (+ 1 b))) (fn2-m3-offers (- n 1) s0 s1 s2 s3)))))

(fn2-ida-defun fn2-m3-setup ()
 (b* ((fn2-id-decides (fn2-id-decides-init *fn2-m3-slots* fn2-id-decides))
      (fn2-overlays (fn2-overlays-init 1 fn2-overlays))
      (fn2-overlay-index (fn2-overlay-index-init 256 fn2-overlay-index))
      (fn2-run-installed (fn2-run-installed-init 64 fn2-run-installed))
      (fn2-run-builds (fn2-run-builds-init 1 fn2-run-builds))
      (fn2-run-cursors (fn2-run-cursors-init *fn2-m3-slots* fn2-run-cursors))
      (fn2-run-paths (fn2-run-paths-init (* *fn2-m3-slots* *fn2-run-max-levels*) fn2-run-paths))
      (fn2-run-cache (fn2-run-cache-init 1024 fn2-run-cache))
      (fn2-run-writers (fn2-run-writers-init (+ 1 *fn2-run-max-levels*) fn2-run-writers))
      (fn2-run-restarts (fn2-run-restarts-init (* (+ 1 *fn2-run-max-levels*) *fn2-run-restart-capacity*) fn2-run-restarts))
      (fn2-fields (fn2-fields-init (fn2-m3-q *fn2-m3-slots*) fn2-fields))
      (fn2-ribbon-builds (fn2-ribbon-builds-init 1 fn2-ribbon-builds))
      (fn2-ribbon-band (fn2-ribbon-band-init (fn2-ribbon-slots 256) fn2-ribbon-band))
      (fn2-id-stamps (fn2-id-stamps-init 64 fn2-id-stamps))
      (fn2-pool (fn2-pool-init '((400 . 65536)) 1 100 fn2-pool))
      (fn2-fc (fn2-fc-init 1 fn2-fc))
      (fn2-fc-context (fn2-fc-context-init 1 fn2-fc-context))
      (fn2-b3 (fn2-b3-table-init 1 fn2-b3))
      (fn2-digests (fn2-digests-init 150 fn2-digests))
      ((mv & aslot agen fn2-pool) (fn2-pool-reserve 0 9 0 1 fn2-pool))
      ((mv code fn2-overlays fn2-pool) (fn2-ov-start 0 1 aslot agen 0 256 9 0 1 0 fn2-overlays fn2-overlay-index fn2-pool)))
  (fn2-ida-mv code)))

;; Place offer X in slot D's rows and start its decision.
(fn2-ida-defun fn2-m3-begin (d x slot gen off)
 (b* ((q (fn2-m3-q d))
      ((mv code off fn2-fields fn2-pool)
       (fn2-run-load-values *fn2-ida-offer-layout* (list (car x) (cons 1 (cadr x))) q slot gen off 9 0 1 fn2-fields fn2-pool))
      ((unless (eq code :ok)) (fn2-ida-mv (list :place code) off))
      ((mv code fn2-id-decides fn2-fields)
       (fn2-id-decide-start d q (+ q 2) (+ q 4) d (+ q 90) 9 0 1 fn2-id-decides fn2-id-stamps fn2-run-installed fn2-fields fn2-pool)))
  (fn2-ida-mv code off)))
;; Record slot D's finished decision; DEFEAT refreshes its stamp first.
(fn2-ida-defun fn2-m3-record (d defeat article)
 (b* ((fn2-id-decides (if defeat
                          (fn2-id-decides-put d (stamp (fn2-id-stamps-gen (fn2-id-decides-bucket d fn2-id-decides) fn2-id-stamps))
                                              (vrun (fn2-run-version 1 (fn2-run-installed-rows fn2-run-installed) fn2-run-installed)))
                        fn2-id-decides))
      ((mv code fn2-id-stamps fn2-overlays fn2-overlay-index fn2-fields fn2-pool)
       (fn2-id-record d 0 (+ (fn2-m3-q d) 200) article article 7 fn2-id-decides fn2-id-stamps fn2-run-installed fn2-overlays fn2-overlay-index fn2-fields fn2-pool)))
  (fn2-ida-mv code)))

;; The interleaving. INFLIGHT holds, per slot, the offer it decides (or
;; nil). Each tick: maybe seal (1 in 12, at most 40 runs), then pick a slot:
;; an idle one takes the next offer; a busy one takes one bounded step, and
;; when its decision is done it is recorded and an event is emitted.
(fn2-ida-defun fn2-m3-tick (offers inflight defeat slot gen off runs events s0 s1 s2 s3)
 (b* (((mv seal s0 s1 s2 s3) (fn2-prng-chance 1 12 s0 s1 s2 s3))
      (sealp (and seal (< runs 40) (< 0 (fn2-overlays-count 0 fn2-overlays))))
      ((mv code fn2-id-decides fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-ribbon-builds fn2-ribbon-band fn2-id-stamps)
       (if sealp (fn2-ida-call fn2-ida-seal runs) (fn2-ida-mv :ok)))
      ((unless (eq code :ok)) (fn2-ida-mv (list :seal code) offers inflight off runs events s0 s1 s2 s3))
      (events (if sealp (cons (list :seal runs) events) events))
      (runs (if sealp (+ 1 runs) runs))
      ((mv d s0 s1 s2 s3) (fn2-prng-below *fn2-m3-slots* s0 s1 s2 s3))
      (x (nth d inflight)))
  (cond
   ((and (not x) (atom offers)) (fn2-ida-mv :ok offers inflight off runs events s0 s1 s2 s3))
   ((not x)
    (b* (((mv code off fn2-id-decides fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-ribbon-builds fn2-ribbon-band fn2-id-stamps)
          (fn2-ida-call fn2-m3-begin d (car offers) slot gen off)))
     (fn2-ida-mv (if (eq code :ok) :ok (list :begin code)) (cdr offers) (update-nth d (car offers) inflight) off runs events s0 s1 s2 s3)))
   (t
    (b* (((mv budget s0 s1 s2 s3) (fn2-prng-below 8 s0 s1 s2 s3))
         ((mv answer fn2-id-decides fn2-run-cursors fn2-run-paths fn2-fields)
          (fn2-id-decide-step d (+ 1 budget) fn2-id-decides fn2-overlays fn2-overlay-index fn2-run-installed
                              fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool))
         ((when (eq answer :more)) (fn2-ida-mv :ok offers inflight off runs events s0 s1 s2 s3))
         ((unless (member-eq answer '(:stored :duplicate :evidence :conflict)))
          (fn2-ida-mv (list :step answer) offers inflight off runs events s0 s1 s2 s3))
         ((mv outcome fn2-id-decides fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-ribbon-builds fn2-ribbon-band fn2-id-stamps)
          (fn2-ida-call fn2-m3-record d defeat (+ 1 (len events)))))
     (fn2-ida-mv :ok (if (eq outcome :stale) (append offers (list x)) offers) (update-nth d nil inflight) off runs
                 (cons (list :offer (car x) (cadr x) answer outcome) events) s0 s1 s2 s3))))))
(defun fn2-m3-ticks (fuel offers inflight defeat slot gen off runs events s0 s1 s2 s3
                     fn2-id-decides fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-ribbon-builds fn2-ribbon-band fn2-id-stamps)
 (declare (xargs :stobjs (fn2-id-decides fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-ribbon-builds fn2-ribbon-band fn2-id-stamps)
                 :verify-guards nil :measure (nfix fuel) :hints (("Goal" :in-theory (disable fn2-m3-tick)))))
 (if (or (zp fuel) (and (atom offers) (not (or (nth 0 inflight) (nth 1 inflight) (nth 2 inflight)))))
     (fn2-ida-mv (if (zp fuel) :fuel :ok) runs events)
  (b* (((mv code offers inflight off runs events s0 s1 s2 s3 fn2-id-decides fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-ribbon-builds fn2-ribbon-band fn2-id-stamps)
        (fn2-ida-call fn2-m3-tick offers inflight defeat slot gen off runs events s0 s1 s2 s3)))
   (if (eq code :ok)
       (fn2-ida-call fn2-m3-ticks (- fuel 1) offers inflight defeat slot gen off runs events s0 s1 s2 s3)
     (fn2-ida-mv code runs events)))))

;; Quiescent queries through slot 0.
(fn2-ida-defun fn2-m3-query-drive (fuel off) :measure (nfix fuel)
 (if (zp fuel) (fn2-ida-mv :fuel off)
  (b* (((mv answer fn2-id-decides fn2-run-cursors fn2-run-paths fn2-fields)
        (fn2-id-decide-step 0 8 fn2-id-decides fn2-overlays fn2-overlay-index fn2-run-installed
                            fn2-run-cursors fn2-run-paths fn2-run-cache fn2-fields fn2-pool)))
   (if (eq answer :more) (fn2-ida-call fn2-m3-query-drive (- fuel 1) off) (fn2-ida-mv answer off)))))
(fn2-ida-defun fn2-m3-query (x slot gen off)
 (b* (((mv code off fn2-id-decides fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-ribbon-builds fn2-ribbon-band fn2-id-stamps)
       (fn2-ida-call fn2-m3-begin 0 x slot gen off))
      ((unless (eq code :ok)) (fn2-ida-mv (list :begin code) off)))
  (fn2-ida-call fn2-m3-query-drive 10000 off)))
(fn2-ida-defun fn2-m3-queries (xs slot gen off events)
 (if (atom xs) (fn2-ida-mv events)
  (b* (((mv answer off fn2-id-decides fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-ribbon-builds fn2-ribbon-band fn2-id-stamps)
        (fn2-ida-call fn2-m3-query (car xs) slot gen off)))
   (fn2-ida-call fn2-m3-queries (cdr xs) slot gen off (cons (list :query (car (car xs)) (cadr (car xs)) answer) events)))))
; Every (Message-ID 0..5, content 1..5) pair: K counts down from 30.
(defun fn2-m3-pairs (k)
 (declare (xargs :verify-guards nil :measure (nfix k)))
 (if (zp k) nil
  (let ((i (- 30 k)))
   (cons (list (fn2-m3-mid (floor i 5)) (fn2-m3-content (+ 1 (mod i 5)))) (fn2-m3-pairs (- k 1))))))
(defun fn2-m3-binding-facts (keys)
 (declare (xargs :verify-guards nil))
 (if (atom keys) nil (cons (list (car (car keys)) (cadr (car keys)) (caddr (car keys))) (fn2-m3-binding-facts (cdr keys)))))

(fn2-ida-defun fn2-m3-run (seed n defeat)
 (b* (((mv code fn2-id-decides fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-ribbon-builds fn2-ribbon-band fn2-id-stamps)
       (fn2-ida-call fn2-m3-setup))
      ((unless (eq code :ok)) (fn2-ida-mv (list (list :setup code))))
      ((mv s0 s1 s2 s3) (fn2-prng-seed seed))
      (offers (fn2-m3-offers n s0 s1 s2 s3))
      ((mv s0 s1 s2 s3) (fn2-prng-seed (+ 1 (* 2 seed))))
      ((mv & slot gen fn2-pool) (fn2-pool-reserve 0 9 0 1 fn2-pool))
      ((mv code runs events fn2-id-decides fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-ribbon-builds fn2-ribbon-band fn2-id-stamps)
       (fn2-ida-call fn2-m3-ticks 100000 offers (list nil nil nil) defeat slot gen 0 0 nil s0 s1 s2 s3))
      ((unless (eq code :ok)) (fn2-ida-mv (cons (list :ticks code) events)))
      ;; The bodies are gone: the staging workspace is released.
      ((mv released fn2-pool) (fn2-pool-release slot gen 9 0 1 fn2-pool))
      (events (cons (list :reclaim (list :bodies released)) events))
      ((mv code fn2-id-decides fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-ribbon-builds fn2-ribbon-band fn2-id-stamps)
       (fn2-ida-call fn2-ida-seal runs))
      ((unless (eq code :ok)) (fn2-ida-mv (cons (list :final-seal code) events)))
      (events (cons (list :seal runs) events))
      ((mv & qslot qgen fn2-pool) (fn2-pool-reserve 0 9 0 1 fn2-pool))
      ((mv events fn2-id-decides fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-ribbon-builds fn2-ribbon-band fn2-id-stamps)
       (fn2-ida-call fn2-m3-queries (fn2-m3-pairs 30) qslot qgen 0 events))
      ;; The Binding by the real scan of every installed run from the least key.
      ((mv & lslot lgen fn2-pool) (fn2-pool-reserve 0 10 0 1 fn2-pool))
      ((mv & & fn2-fields fn2-pool)
       (fn2-run-load-values *fn2-ida-offer-layout* (list nil (cons 1 nil)) *fn2-run-run-query* lslot lgen 0 10 0 1 fn2-fields fn2-pool))
      ((mv keys fn2-id-decides fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-cursors fn2-run-paths fn2-run-cache fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests fn2-ribbon-builds fn2-ribbon-band fn2-id-stamps)
       (fn2-ida-call fn2-ida-scan-runs 0 64 nil)))
  (fn2-ida-mv (reverse (cons (list :binding (fn2-m3-binding-facts keys)) events)))))
(defun fn2-m3-trace (seed n defeat)
 (declare (xargs :verify-guards nil))
 (fn2-ida-local fn2-m3-run seed n defeat))

;; Over SEEDS from FIRST: (passed refused stales seals), plus the first refusal.
(defun fn2-m3-sweep (k seed n defeat passed refused stales seals first)
 (declare (xargs :verify-guards nil :measure (nfix k)))
 (if (zp k) (list passed refused stales seals first)
  (let ((r (fn2-check-identity (fn2-m3-trace seed n defeat) *fn2-identity-contents-max*)))
   (if (eq (car r) :ok)
       (fn2-m3-sweep (- k 1) (+ 1 seed) n defeat (+ 1 passed) refused (+ stales (nth 4 r)) (+ seals (nth 2 r)) first)
     (fn2-m3-sweep (- k 1) (+ 1 seed) n defeat passed (+ 1 refused) stales seals (or first (cons seed r)))))))

;; Keystone: every interleaving the generator produces linearizes (IDENTITY).
(defthm-owed fn2-identity-linearizable (seed n)
 (implies (and (natp seed) (natp n) (<= n 64))
          (equal (car (fn2-check-identity (fn2-m3-trace seed n nil) *fn2-identity-contents-max*)) :ok))
 :teeth (fn2-identity-linearizable-positive fn2-identity-linearizable-negative)
 :schema :g2
 :doc "Offers decided by up to three interleaved decisions, recorded as each finishes, sealed into filtered runs at arbitrary points, their bodies then released: the trace (every answer and record outcome, every later query, the Binding read back by the real scan) is accepted by the independent IDENTITY checker. A :stale record (decided around a later record of its bucket or a seal) records nothing and is offered again.")
;; Positive: 40 seeds of 30 offers pass, with races exercised (stale
;; records) and runs sealed mid-flight. Negative: the same schedules with
;; the stamp and version check defeated are refused by the checker by name.
(defconst *fn2-m3-honest* (fn2-m3-sweep 40 1 30 nil 0 0 0 0 nil))
(defconst *fn2-m3-defeated* (fn2-m3-sweep 40 1 30 t 0 0 0 0 nil))
(defun fn2-identity-linearizable-positive ()
 (declare (xargs :verify-guards nil))
 (and (equal (take 2 *fn2-m3-honest*) '(40 0)) (< 0 (nth 2 *fn2-m3-honest*)) (< 0 (nth 3 *fn2-m3-honest*))))
(defun fn2-identity-linearizable-negative ()
 (declare (xargs :verify-guards nil))
 (and (< 0 (nth 1 *fn2-m3-defeated*))
      (if (member-eq (nth 3 (nth 4 *fn2-m3-defeated*)) '(:answer :outcome :binding :query)) t nil)))
(fn2-assert-owed-teeth fn2-identity-linearizable)
(value-triple (cw "fn2-m3: honest ~x0 defeated ~x1~%" (take 4 *fn2-m3-honest*) (take 4 *fn2-m3-defeated*)))
