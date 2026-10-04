(in-package "ACL2")
(include-book "../../books/page-window-read")
(include-book "page-window-executor-tests")
; Test-only bytes source follows the actual core-issued effects and digest.
(defun pwrtest-run (fuel archive s pgs-digest-state fn-ew-buffer fn-octets reads)
  (declare (xargs :stobjs (pgs-digest-state fn-ew-buffer fn-octets)
                  :measure (nfix fuel) :verify-guards nil))
  (cond ((zp fuel) (mv :fuel s pgs-digest-state fn-ew-buffer fn-octets reads))
        ((not (member-eq (nth 0 s) '(:scan :trailer)))
         (mv (nth 0 s) s pgs-digest-state fn-ew-buffer fn-octets reads))
        (t (let ((effect (fn-ews-effect s pgs-digest-state)))
             (if effect
                 (let* ((bytes (fn-b3-firstn (nth 5 effect)
                                   (fn-b3-nthcdrx (- (nth 4 effect) (nth 2 s)) archive)))
                        (fn-octets (fn-octets-from-list bytes fn-octets)))
                   (mv-let (status s pgs-digest-state fn-ew-buffer)
                     (fn-ews-read effect :ok s fn-octets pgs-digest-state fn-ew-buffer)
                     (declare (ignore status))
                     (pwrtest-run (1- fuel) archive s pgs-digest-state fn-ew-buffer fn-octets
                               (+ reads (len bytes)))))
               (mv-let (status s pgs-digest-state)
                 (fn-ews-tick s pgs-digest-state)
                 (declare (ignore status))
                 (pwrtest-run (1- fuel) archive s pgs-digest-state fn-ew-buffer fn-octets reads)))))))


(defun-nx pwrtest-request (offset expected archive)
  (let* ((descriptor (list 11 100 3 100 3 offset expected))
         (admit (fn-prw-admit *prw-registered* descriptor '(256 0 0 1 1)))
         (token (nth 1 admit))
         (acquire (fn-pwx-acquire (nth 2 admit) (fn-pxe-new 0) token))
         (begin (fn-ews-begin 11 100 3 100 3 offset (nth 1 token) 47 token
                              expected (create-pgs-digest-state)))
         (run (pwrtest-run 40 archive (car begin) (cadr begin)
                          (create-fn-ew-buffer) nil 0))
         (returned (fn-pwx-return (nth 2 acquire) (nth 1 acquire) token)))
    (list token acquire returned run)))

(defun-nx pwrtest-ready ()
  (let* ((msg '(1 2 3)) (digest (fn-blake3 msg)))
    (pwrtest-request 0 (fn-bch-pack digest) (append msg digest))))

; REACHABLE POSITIVE: actual authenticated stream, complete literal
; antecedent/conclusion of fn-pwr-byte-authorization-by-definition.
(defun-nx pwrtest-positive ()
 (let* ((r (pwrtest-ready)) (token (nth 0 r)) (returned (nth 2 r))
        (run (nth 3 r)) (s (nth 1 run)) (buffer (nth 3 run))
        (ledger (nth 2 returned)) (worker (nth 1 returned))
        (answer (fn-pwr-byte ledger worker token s 1 buffer)))
   (and (equal (nth 0 run) :verified) (equal (nth 0 returned) :returned)
        (equal (nth 0 answer) :byte)
        (fn-pwx-boundp ledger worker token :returned)
        (fn-pwr-plan-matches-token s token) (fn-ewp-publication s)
        (natp 1) (< 1 (nth 5 s)) (<= (nth 5 s) 16384)
        (equal (nth 1 answer) (nth 1 (nth 0 buffer)))
        (equal (nth 1 answer) 2))))
(defthm pwrtest-positive-witness (pwrtest-positive) :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwr-byte fn-pwr-plan-matches-token))))

; HYPOTHESIS-REMOVAL: sole antecedent fails on actually running slot;
; conclusion fails too, because exact returned ownership is absent.
(defun-nx pwrtest-removal ()
 (let* ((r (pwrtest-ready)) (token (nth 0 r)) (acquire (nth 1 r))
        (run (nth 3 r)) (s (nth 1 run)) (buffer (nth 3 run))
        (ledger (nth 2 acquire)) (worker (nth 1 acquire))
        (answer (fn-pwr-byte ledger worker token s 1 buffer)))
   (and (not (equal (nth 0 answer) :byte))
        (not (and (fn-pwx-boundp ledger worker token :returned)
                  (fn-pwr-plan-matches-token s token) (fn-ewp-publication s)
                  (natp 1) (< 1 (nth 5 s)) (<= (nth 5 s) 16384)
                  (equal (nth 1 answer) (nth 1 (nth 0 buffer))))))))

(defthm pwrtest-removal-witness (pwrtest-removal) :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwr-byte fn-pwr-plan-matches-token))))


; Payload-relative1 with requested offset1 must borrow window-relative0.
; Complete actual trajectory and original descriptor stay bound together.
(defun-nx pwrtest-coordinate-positive ()
  (let* ((digest (fn-blake3 '(1 2 3)))
         (r (pwrtest-request 1 (fn-bch-pack digest) (append '(1 2 3) digest)))
         (token (nth 0 r)) (returned (nth 2 r)) (run (nth 3 r))
         (s (nth 1 run)) (buffer (nth 3 run))
         (ledger (nth 2 returned)) (worker (nth 1 returned)))
    (and (equal (fn-pwr-outcome ledger worker token s) :ready)
         (equal (fn-pwr-byte-at ledger worker token s 11 100 3 100 3 (fn-bch-pack digest) 1 buffer)
                '(:byte 2))
         (equal (fn-pwr-byte-at ledger worker token s 11 100 3 100 3 (fn-bch-pack digest) 0 buffer)
                '(:unavailable nil))
         (equal (fn-pwr-byte-at ledger worker token s 11 100 3 101 2 (fn-bch-pack digest) 1 buffer)
                '(:unavailable nil))
         (equal (fn-pwr-cold-descriptor 11 100 3 100 3 (fn-bch-pack digest) 2)
                (list 11 100 3 100 3 2 (fn-bch-pack digest))))))
(defthm pwrtest-coordinate-positive-witness (pwrtest-coordinate-positive)
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwr-byte-at fn-pwr-byte fn-pwr-outcome fn-pwr-cold-descriptor))))

; Actual damaged-prefix/trailer/short-read failures remain explicit faults,
; not a cold-miss request that rehashes the same failed extent indefinitely.
(defun-nx pwrtest-terminal-faults ()
  (let* ((digest (fn-blake3 '(1 2 3)))
         (bad-commitment (pwrtest-request 0 0 (append '(1 2 3) digest)))
         (bad-digest (pwrtest-request 0 (fn-bch-pack digest) (append '(1 2 4) digest)))
         (short (pwrtest-request 0 (fn-bch-pack digest) '(1 2))))
    (and (equal (fn-pwr-outcome (nth 2 (nth 2 bad-commitment)) (nth 1 (nth 2 bad-commitment))
                               (nth 0 bad-commitment) (nth 1 (nth 3 bad-commitment))) '(:fault :commitment))
         (equal (fn-pwr-outcome (nth 2 (nth 2 bad-digest)) (nth 1 (nth 2 bad-digest))
                               (nth 0 bad-digest) (nth 1 (nth 3 bad-digest))) '(:fault :digest))
         (equal (fn-pwr-outcome (nth 2 (nth 2 short)) (nth 1 (nth 2 short))
                               (nth 0 short) (nth 1 (nth 3 short))) '(:fault :read))
         (equal (fn-pwr-byte-at (nth 2 (nth 2 bad-commitment)) (nth 1 (nth 2 bad-commitment))
                               (nth 0 bad-commitment) (nth 1 (nth 3 bad-commitment))
                               11 100 3 100 3 0 0 (nth 3 (nth 3 bad-commitment)))
                '((:fault :commitment) nil)))))
(defthm pwrtest-terminal-faults-witness (pwrtest-terminal-faults)
  :rule-classes nil :hints (("Goal" :in-theory (enable fn-pwr-outcome fn-pwr-byte-at))))

; Actual digest publication revoked after return. The same authentic plan and
; buffer cannot become a scalar publication, and every credit remains held.
(defun-nx pwrtest-cancelled-positive ()
  (let* ((r (pwrtest-ready)) (token (nth 0 r)) (returned (nth 2 r))
         (run (nth 3 r)) (s (nth 1 run)) (buffer (nth 3 run))
         (ledger (nth 2 returned)) (worker (nth 1 returned))
         (cancel (fn-pwx-cancel ledger worker token))
         (worker1 (nth 1 cancel)))
    (and (equal (nth 0 run) :verified) (equal (nth 0 cancel) :cancelled)
         (equal (nth 2 cancel) ledger)
         (equal (fn-pwr-outcome ledger worker1 token s) :cancelled)
         (equal (fn-pwr-byte-at ledger worker1 token s 11 100 3 100 3 (nth 8 token) 1 buffer)
                '(:cancelled nil)))))
(defthm pwrtest-cancelled-publication-witness
  (pwrtest-cancelled-positive)
  :rule-classes nil)

; Teeth of fn-pwr-a-late-fault-is-a-fault-cancelled-or-not and
; fn-pwr-a-cancelled-job-never-publishes (PRF-1057 / SCN-216, window arm).
; The request is cancelled WHILE RUNNING (its deadline passed, the 403 was
; answered), then the actual job returns: the worker is :cancelled-returned.
(defun-nx pwrtest-cancelled-then-returned (r)
  (let* ((token (nth 0 r)) (acquire (nth 1 r))
         (cancel (fn-pwx-cancel (nth 2 acquire) (nth 1 acquire) token))
         (returned (fn-pwx-return (nth 2 cancel) (nth 1 cancel) token)))
    (list token cancel returned (nth 1 (nth 3 r)))))

; REACHABLE POSITIVE, complete antecedent and conclusion: a short read and a
; damaged prefix, each returned after the cancellation, answer their faults.
(defun-nx pwrtest-late-fault-positive ()
  (let* ((digest (fn-blake3 '(1 2 3)))
         (short (pwrtest-cancelled-then-returned
                 (pwrtest-request 0 (fn-bch-pack digest) '(1 2))))
         (damaged (pwrtest-cancelled-then-returned
                   (pwrtest-request 0 (fn-bch-pack digest) (append '(1 2 4) digest)))))
    (and (equal (nth 0 (nth 1 short)) :cancelled)
         (equal (nth 0 (nth 2 short)) :returned)
         (fn-pwx-boundp (nth 2 (nth 2 short)) (nth 1 (nth 2 short)) (nth 0 short)
                        :cancelled-returned)
         (fn-pwr-plan-matches-token (nth 3 short) (nth 0 short))
         (fn-pwr-fault-phasep (nth 3 short))
         (equal (fn-pwr-outcome (nth 2 (nth 2 short)) (nth 1 (nth 2 short))
                                (nth 0 short) (nth 3 short))
                '(:fault :read))
         (fn-pwx-boundp (nth 2 (nth 2 damaged)) (nth 1 (nth 2 damaged)) (nth 0 damaged)
                        :cancelled-returned)
         (fn-pwr-plan-matches-token (nth 3 damaged) (nth 0 damaged))
         (fn-pwr-fault-phasep (nth 3 damaged))
         (equal (fn-pwr-outcome (nth 2 (nth 2 damaged)) (nth 1 (nth 2 damaged))
                                (nth 0 damaged) (nth 3 damaged))
                '(:fault :digest)))))
(defthm pwrtest-late-fault-positive-witness (pwrtest-late-fault-positive)
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwr-outcome fn-pwr-fault-phasep
                                     fn-pwr-plan-matches-token))))

; The verified job cancelled while running and then returned is :cancelled
; (never :ready, no byte): the second keystone's other disjunct.
(defun-nx pwrtest-cancelled-verified-positive ()
  (let* ((c (pwrtest-cancelled-then-returned (pwrtest-ready)))
         (ledger (nth 2 (nth 2 c))) (worker (nth 1 (nth 2 c))) (token (nth 0 c)))
    (and (fn-pwx-boundp ledger worker token :cancelled-returned)
         (not (fn-pwr-fault-phasep (nth 3 c)))
         (equal (fn-pwr-outcome ledger worker token (nth 3 c)) :cancelled))))
(defthm pwrtest-cancelled-verified-positive-witness (pwrtest-cancelled-verified-positive)
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwr-outcome fn-pwr-fault-phasep
                                     fn-pwr-plan-matches-token))))

; HYPOTHESIS REMOVALS of the first keystone, each over the same short-read
; trajectory with ONE hypothesis false, and its conclusion then false too:
; (a) the plan is not the token's (a worker stopped before its first read
;     returns no plan: NIL) -- :cancelled;
; (b) the job has not returned (cancelled, still running) -- :stale-job.
(defun-nx pwrtest-late-fault-removals ()
  (let* ((digest (fn-blake3 '(1 2 3)))
         (r (pwrtest-request 0 (fn-bch-pack digest) '(1 2)))
         (c (pwrtest-cancelled-then-returned r))
         (token (nth 0 c))
         (running (nth 1 c)))
    (and (fn-pwx-boundp (nth 2 (nth 2 c)) (nth 1 (nth 2 c)) token :cancelled-returned)
         (not (fn-pwr-plan-matches-token nil token))
         (not (equal (fn-pwr-outcome (nth 2 (nth 2 c)) (nth 1 (nth 2 c)) token nil)
                     (list :fault (nth 0 nil))))
         (equal (fn-pwr-outcome (nth 2 (nth 2 c)) (nth 1 (nth 2 c)) token nil) :cancelled)
         (not (fn-pwx-boundp (nth 2 running) (nth 1 running) token :returned))
         (not (fn-pwx-boundp (nth 2 running) (nth 1 running) token :cancelled-returned))
         (fn-pwr-fault-phasep (nth 3 c))
         (equal (fn-pwr-outcome (nth 2 running) (nth 1 running) token (nth 3 c)) :stale-job))))
(defthm pwrtest-late-fault-removals-witness (pwrtest-late-fault-removals)
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwr-outcome fn-pwr-fault-phasep
                                     fn-pwr-plan-matches-token))))

; Teeth of the verified-window cache: fn-pwc-cache-only-a-published-window,
; fn-pwc-a-hit-is-the-published-window, fn-pwc-hit-requires-a-cached-
; published-exact-window (books/page-window-read.lisp) and the lease's
; fn-prw-cache-keeps-only-the-buffer / fn-prw-cached-window-evicts-its-keep.
(defconst *pwrtest-keep* '(16 0 0 0 0))

; REACHABLE POSITIVE: the authenticated job returned :ready, is cached; its
; row is (KEEP :cached nil), its slot idle, its worker charge released; a
; cache borrow of payload byte 1 answers the job's own borrow, byte 2; a
; byte outside the published window is a miss, as the borrow's :unavailable.
(defun-nx pwrtest-cache-positive ()
  (let* ((r (pwrtest-ready)) (token (nth 0 r)) (returned (nth 2 r))
         (run (nth 3 r)) (s (nth 1 run)) (buffer (nth 3 run))
         (ledger (nth 2 returned)) (worker (nth 1 returned))
         (cached (fn-pwc-cache ledger worker token s *pwrtest-keep*))
         (ledger2 (nth 2 cached)) (trailer (nth 8 token)))
    (and (equal (fn-pwr-outcome ledger worker token s) :ready)
         (equal (nth 0 cached) :cached)
         (equal (nth 1 cached) (list (nth 0 worker) (nth 1 worker) :idle nil))
         (fn-pwc-cachedp ledger2 token)
         (equal (cdr (fn-prl-binding token (fn-prl-nth 3 ledger2))) (list *pwrtest-keep* :cached nil))
         (equal (fn-prl-nth 3 (fn-prl-nth 1 ledger2)) 0)
         (equal (fn-pwc-byte-at ledger2 token s 11 100 3 100 3 trailer 1 buffer)
                (fn-pwr-byte-at ledger worker token s 11 100 3 100 3 trailer 1 buffer))
         (equal (fn-pwc-byte-at ledger2 token s 11 100 3 100 3 trailer 1 buffer) '(:byte 2))
         (equal (fn-pwc-byte-at ledger2 token s 11 100 3 100 3 trailer 3 buffer) '(:miss nil))
         (equal (nth 0 (fn-pwr-byte-at ledger worker token s 11 100 3 100 3 trailer 3 buffer))
                :unavailable))))
(defthm pwrtest-cache-positive-witness (pwrtest-cache-positive)
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwc-cache fn-pwx-cache fn-prw-cache fn-pwc-cachedp
                                     fn-pwc-byte-at fn-pwr-byte-at fn-pwr-byte fn-pwr-outcome
                                     fn-pwr-plan-matches-token fn-prw-keep-okp))))

; HYPOTHESIS REMOVALS.
; (a) the outcome is not :ready (a short read): fn-pwc-cache refuses, the
;     ledger is unchanged and nothing is cached;
; (b) the cached row is evicted (fn-prl-evict): every borrow is a miss,
;     though the same plan and buffer are in hand;
; (c) another descriptor (POFF 101): a miss.
(defun-nx pwrtest-cache-removals ()
  (let* ((digest (fn-blake3 '(1 2 3)))
         (short (pwrtest-request 0 (fn-bch-pack digest) '(1 2)))
         (sledger (nth 2 (nth 2 short))) (sworker (nth 1 (nth 2 short)))
         (r (pwrtest-ready)) (token (nth 0 r)) (returned (nth 2 r))
         (s (nth 1 (nth 3 r))) (buffer (nth 3 (nth 3 r)))
         (cached (fn-pwc-cache (nth 2 returned) (nth 1 returned) token s *pwrtest-keep*))
         (evicted (fn-prl-evict (nth 2 cached) token))
         (trailer (nth 8 token)))
    (and (not (equal (fn-pwr-outcome sledger sworker (nth 0 short) (nth 1 (nth 3 short))) :ready))
         (equal (fn-pwc-cache sledger sworker (nth 0 short) (nth 1 (nth 3 short)) *pwrtest-keep*)
                (list :stale-job sworker sledger))
         (equal (nth 0 evicted) :evicted)
         (equal (fn-prl-nth 1 (nth 1 evicted))
                (fn-prs-release-reusable (fn-prl-nth 1 (nth 2 cached)) *pwrtest-keep*))
         (not (fn-pwc-cachedp (nth 1 evicted) token))
         (equal (fn-pwc-byte-at (nth 1 evicted) token s 11 100 3 100 3 trailer 1 buffer) '(:miss nil))
         (equal (fn-pwc-byte-at (nth 2 cached) token s 11 100 3 101 2 trailer 1 buffer) '(:miss nil)))))
(defthm pwrtest-cache-removals-witness (pwrtest-cache-removals)
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-pwc-cache fn-pwx-cache fn-prw-cache fn-pwc-cachedp
                                     fn-pwc-byte-at fn-pwr-outcome fn-pwr-plan-matches-token
                                     fn-prw-keep-okp fn-prl-evict))))
