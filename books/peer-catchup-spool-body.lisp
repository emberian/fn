;; K1 of the bounded catch-up spool controller (PRF-1335/1336): a body is
;; written only after its 335.  The window, the connection table and the
;; verdict keystones live in peer-catchup-spool; this book adds the
;; per-connection phase discipline over fn-csp-step, kept in its own book so
;; each stays under the 10 s certification budget (D26).
(in-package "ACL2")
(include-book "peer-catchup-spool")

; The controller state is a 20-element list read through FN-PULL-AT.  Left
; enabled, FN-PULL-AT unfolds all the way down on every variable state;
; folded, it opens only on an explicit cons, which is what a rebuilt state is.
(local (defthm fn-csp-pull-at-of-cons
  (equal (fn-pull-at n (cons a r))
         (if (zp n) a (fn-pull-at (1- n) r)))))
(local (defthm fn-csp-pull-at-of-nil
  (equal (fn-pull-at n nil) nil)))
(local (in-theory (disable fn-pull-at)))

(defun fn-csp-body-inv-of (mode skip resume msgid slot conns)
  ; K1's invariant over the fields it reads.  The record a body window or
  ; terminator is written for is the one whose IHAVE the local node answered
  ; 335.  While the offer awaits its 335 the slot's connection holds
  ; (msgid . :await335); while the body is spooled to the local node (a
  ; window in flight, the next window to frame, the terminator) it holds
  ; (msgid . :streaming).  A 435 record's body, skipped through the spool, is
  ; sent on no connection.  A held record and a spool write in flight carry
  ; what their resumption needs.
  (declare (xargs :guard t))
  (let ((c (fn-pull-at (nfix slot) conns)))
    (and (implies (eq mode :offer)
                  (and (natp slot) (not skip)
                       (consp c) (eq (cdr c) :await335) (equal (car c) msgid)))
         (implies (eq mode :held) (not skip))
         (implies (eq mode :write) (member-eq resume '(:hash :body)))
         (implies (eq mode :local-write)
                  (and (member-eq resume '(:terminator :replay-body)) (not skip)))
         (implies (or (member-eq mode '(:local-write :terminator))
                      (and (eq mode :replay-body) (not skip)))
                  (and (natp slot)
                       (consp c) (eq (cdr c) :streaming) (equal (car c) msgid))))))

(defun fn-csp-body-inv (s)
  (declare (xargs :guard t))
  (fn-csp-body-inv-of (fn-csp-mode s) (fn-csp-skip s) (fn-csp-resume s)
                      (fn-csp-msgid s) (fn-csp-slot s) (fn-csp-conns s)))

(local (defun fn-csp-pa-ind (k j conns)
  (declare (xargs :measure (+ (nfix k) (nfix j))))
  (if (or (zp k) (zp j)) conns
    (fn-csp-pa-ind (1- k) (1- j) (if (consp conns) (cdr conns) nil)))))

(local (defthm fn-csp-pull-at-of-conns-set
  ; A binding read back is the one just set, or untouched.
  (equal (fn-pull-at k (fn-csp-conns-set conns j c))
         (if (equal (nfix k) (nfix j)) c (fn-pull-at k conns)))
  :hints (("Goal" :in-theory (enable fn-pull-at fn-csp-conns-set)
                  :induct (fn-csp-pa-ind k j conns)))))

(local (defthm fn-csp-body-inv-of-state
  (equal (fn-csp-body-inv (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19))
         (fn-csp-body-inv-of a0 a16 a14 a7 a19 a18))
  :hints (("Goal" :in-theory (enable fn-csp-body-inv)))))

(local (in-theory (disable fn-csp-body-inv)))

(local (defthm fn-csp-body-inv-quiet
  (implies (not (member-eq (fn-csp-mode s) '(:offer :held :write :local-write :terminator :replay-body)))
           (fn-csp-body-inv s))
  :hints (("Goal" :in-theory (enable fn-csp-body-inv)))))

(local (defthm fn-csp-body-inv-of-quiet
  ; Outside the modes that carry a binding, the invariant is vacuous.
  (implies (not (member-eq mode '(:offer :held :write :local-write :terminator :replay-body)))
           (equal (fn-csp-body-inv-of mode skip resume msgid slot conns) t))))

(local (defthm fn-csp-body-inv-of-resume
  ; A spool write, or a body window taken by the local node, resumes the
  ; mode its record carried.
  (implies (and (fn-csp-body-inv-of mode skip resume msgid slot conns)
                (member-eq mode '(:write :local-write)))
           (fn-csp-body-inv-of resume skip resume msgid slot conns))))

(local (defthm fn-csp-body-inv-of-local-write
  ; A body window sent to the local node from the replay: the streaming
  ; slot stays, the window is in flight.
  (implies (and (fn-csp-body-inv-of :replay-body nil resume0 msgid slot conns)
                (member-eq resume '(:terminator :replay-body)))
           (fn-csp-body-inv-of :local-write nil resume msgid slot conns))))

(local (defthm fn-csp-body-inv-of-held
  ; A held record is not a skipped one: its offer is still to come.
  (implies (fn-csp-body-inv-of :held skip resume msgid slot conns)
           (not skip))
  :rule-classes :forward-chaining))

(local (defthm fn-csp-fail-mode
  (equal (fn-csp-mode (car (fn-csp-fail s reason))) :failed)
  :hints (("Goal" :in-theory (enable fn-csp-fail fn-csp-session-with-round)))))

(local (defthm fn-csp-fail-keeps-body-inv
  (fn-csp-body-inv (car (fn-csp-fail s reason)))
  :hints (("Goal" :use fn-csp-fail-mode :in-theory (disable fn-csp-fail-mode fn-csp-fail)))))

(local (defthm fn-csp-body-inv-of-symbol
  (implies (syntaxp (symbolp s))
           (equal (fn-csp-body-inv s)
                  (fn-csp-body-inv-of (fn-pull-at 0 s) (fn-pull-at 16 s) (fn-pull-at 14 s)
                                      (fn-pull-at 7 s) (fn-pull-at 19 s) (fn-pull-at 18 s))))
  :hints (("Goal" :in-theory (enable fn-csp-body-inv)))))

(local (defthm fn-csp-session-with-round-keeps-body-inv
  (equal (fn-csp-body-inv (fn-csp-session-with-round s r)) (fn-csp-body-inv s))
  :hints (("Goal" :in-theory (e/d (fn-csp-session-with-round fn-csp-body-inv-of-symbol) (fn-csp-body-inv))))))

(local (defthm fn-csp-batch-finish-mode
  (member-eq (fn-csp-mode (car (fn-csp-batch-finish s))) '(:done :status))
  :hints (("Goal" :in-theory (e/d (fn-csp-batch-finish) (fn-cu-next fn-csp-session-with-round))))))

(local (defthm fn-csp-batch-finish-keeps-body-inv
  (fn-csp-body-inv (car (fn-csp-batch-finish s)))
  :hints (("Goal" :use fn-csp-batch-finish-mode :in-theory (disable fn-csp-batch-finish-mode fn-csp-batch-finish)))))

(local (defthm fn-csp-record-done-mode
  (member-eq (fn-csp-mode (car (fn-csp-record-done s))) '(:replay-header :drain :done :status))
  :hints (("Goal" :in-theory (e/d (fn-csp-record-done) (fn-csp-batch-finish fn-csp-session-with-round))
                  :use (:instance fn-csp-batch-finish-mode
                         (s (fn-csp-with s :slot nil :skip nil :framer nil :msgid nil)))))))

(local (defthm fn-csp-record-done-keeps-body-inv
  (fn-csp-body-inv (car (fn-csp-record-done s)))
  :hints (("Goal" :use fn-csp-record-done-mode :in-theory (disable fn-csp-record-done-mode fn-csp-record-done)))))

(local (defthm fn-csp-write-keeps-body-inv
  (implies (member-eq resume '(:hash :body))
           (fn-csp-body-inv (car (fn-csp-write s emission resume))))
  :hints (("Goal" :in-theory (e/d (fn-csp-write fn-csp-body-inv-of-symbol)
                                  (fn-csp-body-inv fn-csp-fail))
                  :use fn-csp-fail-keeps-body-inv))))

(local (defthm fn-csp-try-offer-keeps-body-inv
  (implies (not (fn-csp-skip s))
           (fn-csp-body-inv (car (fn-csp-try-offer s))))
  :hints (("Goal" :in-theory (e/d (fn-csp-try-offer) (fn-csp-body-inv))))))

(local (defthm fn-csp-hash-effect-keeps-body-inv
  (implies (fn-csp-body-inv s) (fn-csp-body-inv (car (fn-csp-hash-effect s))))
  :hints (("Goal" :in-theory (enable fn-csp-hash-effect)))))

(local (defthm fn-csp-read-replay-keeps-body-inv
  (implies (fn-csp-body-inv s) (fn-csp-body-inv (car (fn-csp-read-replay s))))
  :hints (("Goal" :in-theory (e/d (fn-csp-read-replay fn-csp-body-inv-of-symbol)
                                  (fn-csp-record-done fn-csp-fail fn-csp-body-inv fn-csp-body-inv-of))
                  :use (fn-csp-record-done-keeps-body-inv
                        (:instance fn-csp-fail-keeps-body-inv (reason :short-spool)))))))

(local (defthm fn-csp-after-header-keeps-body-inv
  (fn-csp-body-inv (car (fn-csp-after-header s line rest used)))
  :hints (("Goal" :in-theory (e/d (fn-csp-after-header fn-csp-body-inv-of-symbol)
                                  (fn-csp-fail fn-csp-write fn-csp-try-offer fn-csp-body-inv
                                   fn-csp-body-inv-of fn-csp-body-inv-quiet binary-append fn-csp-session-with-round
                                   fn-cu-parse-status fn-cu-parse-header fn-cu-batch-end
                                   fn-cu-batch-next fn-cu-batch-morep fn-cu-batch-claim
                                   fn-cu-u64-hex fn-record-string-octets
                                   fn-cu-hex fn-cu-unhex fn-cu-u64-octets-aux fn-cu-words-aux))))))

(local (defthm fn-csp-local-window-keeps-body-inv
  (implies (fn-csp-body-inv s) (fn-csp-body-inv (car (fn-csp-local-window s j))))
  :hints (("Goal" :in-theory (e/d (fn-csp-local-window fn-csp-conn fn-csp-body-inv-of-symbol)
                                  (fn-csp-fail fn-csp-body-inv fn-csp-body-inv-of))))))

(local (defthm fn-csp-swr-field
  ; Steering the session's round moves no field the invariants read.
  (implies (member-equal k '(0 4 5 7 11 14 16 18 19))
           (equal (fn-pull-at k (fn-csp-session-with-round s r)) (fn-pull-at k s)))
  :hints (("Goal" :in-theory (enable fn-csp-session-with-round)
                  :cases ((equal k 0) (equal k 4) (equal k 5) (equal k 7) (equal k 11) (equal k 14) (equal k 16) (equal k 18))))))

(local (defthm fn-csp-nfix-nfix (equal (nfix (nfix x)) (nfix x))))

(local (defthm fn-csp-local-opened-keeps-body-inv
  (implies (and (fn-csp-body-inv s) (equal conns (fn-csp-conns s))
                (equal (fn-pull-at (nfix j) conns) :opening))
           (fn-csp-body-inv (car (fn-csp-local-opened s j code conns))))
  :hints (("Goal" :in-theory (e/d (fn-csp-local-opened fn-csp-body-inv-of-symbol fn-csp-conns)
                                  (fn-csp-fail fn-csp-body-inv nfix))
                  :use (:instance fn-csp-fail-keeps-body-inv (reason :local-refused))))))

(local (defthm fn-csp-local-verdict-keeps-body-inv
  (implies (and (fn-csp-body-inv s) (equal conns (fn-csp-conns s))
                (consp (fn-pull-at (nfix j) conns))
                (eq (cdr (fn-pull-at (nfix j) conns)) :verdict))
           (fn-csp-body-inv (car (fn-csp-local-verdict s j code conns round))))
  :hints (("Goal" :in-theory (e/d (fn-csp-local-verdict fn-csp-body-inv-of-symbol fn-csp-conns)
                                  (fn-csp-fail fn-csp-body-inv fn-csp-batch-finish
                                   fn-csp-session-with-round fn-cu-count nfix))
                  :use ((:instance fn-csp-fail-keeps-body-inv (reason :local-refused))
                        (:instance fn-csp-fail-keeps-body-inv (reason :local-deferred)))))))

(local (defthm fn-csp-local-await335-keeps-body-inv
  (implies (and (fn-csp-body-inv s) (equal conns (fn-csp-conns s))
                (equal c (fn-pull-at (nfix j) conns))
                (consp c) (eq (cdr c) :await335)
                (eq (fn-csp-mode s) :offer) (equal (fn-csp-slot s) (nfix j)))
           (fn-csp-body-inv (car (fn-csp-local-await335 s j code c conns round))))
  :hints (("Goal" :in-theory (e/d (fn-csp-local-await335 fn-csp-body-inv-of-symbol fn-csp-conns)
                                  (fn-csp-fail fn-csp-body-inv fn-csp-record-done
                                   fn-csp-session-with-round fn-cu-count nfix))
                  :use ((:instance fn-csp-fail-keeps-body-inv (reason :local-refused))
                        (:instance fn-csp-fail-keeps-body-inv (reason :local-deferred))
                        (:instance fn-csp-record-done-keeps-body-inv
                          (s (fn-csp-with (fn-csp-session-with-round
                                            s (fn-cu-with round :counts
                                                          (fn-cu-count (fn-cu-r-counts round) 1)))
                                          :conns (fn-csp-conns-set conns j :free) :slot nil))))))))

(local (defthm fn-csp-local-keeps-body-inv
  (implies (fn-csp-body-inv s)
           (fn-csp-body-inv (car (fn-csp-local s j octets))))
  :hints (("Goal" :in-theory (e/d (fn-csp-local fn-csp-conn)
                                  (fn-csp-fail fn-csp-local-opened fn-csp-local-await335
                                   fn-csp-local-verdict fn-csp-body-inv fn-csp-body-inv-of nfix))
                  :use ((:instance fn-csp-fail-keeps-body-inv (reason :local-refused))
                        (:instance fn-csp-local-opened-keeps-body-inv
                          (code (fn-pull-local-code octets)) (conns (fn-csp-conns s)))
                        (:instance fn-csp-local-await335-keeps-body-inv
                          (code (fn-pull-local-code octets)) (conns (fn-csp-conns s))
                          (c (fn-csp-conn j s)) (round (fn-cu-s-round (fn-csp-session s))))
                        (:instance fn-csp-local-verdict-keeps-body-inv
                          (code (fn-pull-local-code octets)) (conns (fn-csp-conns s))
                          (round (fn-cu-s-round (fn-csp-session s)))))))))

(local (defthm fn-csp-next-keeps-body-inv
  (implies (fn-csp-body-inv s) (fn-csp-body-inv (car (fn-csp-next s))))
  :hints (("Goal" :in-theory (e/d (fn-csp-next fn-csp-body-inv-of-symbol)
                                  (fn-csp-fail fn-csp-write fn-csp-after-header
                                   fn-csp-read-replay fn-csp-hash-effect fn-csp-header-window
                                   fn-csp-framer-window fn-csp-framer-window-accounts-for-every-octet
                                   fn-csp-record-done fn-csp-try-offer fn-csp-session-with-round
                                   fn-csp-body-inv fn-csp-body-inv-of nfix))))))

(defthm fn-csp-step-keeps-body-inv
  ; The invariant K1 reads, preserved by every step event.
  (implies (fn-csp-body-inv s)
           (fn-csp-body-inv (car (fn-csp-step s event))))
  :hints (("Goal" :in-theory (e/d (fn-csp-step fn-csp-body-inv-of-symbol)
                                  (fn-csp-fail fn-csp-next fn-csp-local fn-csp-local-window
                                   fn-cu-session-step-pair fn-cu-session-readyp
                                   fn-blake3-stobj fn-cu-chainp fn-pull-event-octets
                                   fn-csp-session fn-csp-session-with-round fn-csp-body-inv
                                   fn-csp-body-inv-of nfix)))))

(defthm fn-csp-begin-establishes-body-inv
  ; The invariant holds at the flight's begin: the round starts in :status
  ; with no slot bound.
  (fn-csp-body-inv (car (fn-csp-begin plan cursor credential limit window)))
  :hints (("Goal" :in-theory (e/d (fn-csp-begin fn-csp-body-inv-of-symbol)
                                  (fn-csp-fail fn-csp-body-inv fn-cu-session-begin-pair
                                   fn-cu-cursor-chain fn-csp-conns-of nfix)))))

(local (defthm fn-csp-free-conn-is-free
  ; The lowest :free index (counted from K) names a :free entry.
  (implies (fn-csp-free-conn conns k)
           (equal (fn-pull-at (- (fn-csp-free-conn conns k) (nfix k)) conns) :free))
  :hints (("Goal" :in-theory (enable fn-csp-free-conn fn-pull-at)
                  :induct (fn-csp-free-conn conns k)))))

(local (defthm fn-csp-try-offer-local-effect
  ; The only :local effect of the offer is the IHAVE for the bound record,
  ; on the :free connection it binds (msgid . :await335).
  (implies (member-equal (cons :local x) (cadr (fn-csp-try-offer s)))
           (let ((s2 (car (fn-csp-try-offer s))))
             (and (equal (fn-csp-mode s2) :offer)
                  (natp (fn-csp-slot s2))
                  (equal (fn-pull-at (fn-csp-slot s2) (fn-csp-conns s)) :free)
                  (equal (fn-pull-at (fn-csp-slot s2) (fn-csp-conns s2))
                         (cons (fn-csp-msgid s2) :await335))
                  (equal x (cons (fn-csp-slot s2)
                                 (fn-cu-ihave (cons (fn-csp-msgid s2) nil)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-csp-try-offer) (fn-csp-body-inv nfix))
                  :use (:instance fn-csp-free-conn-is-free (conns (fn-csp-conns s)) (k 0))))))

(local (defthm fn-csp-fail-no-local
  (not (member-eq :local (strip-cars (cadr (fn-csp-fail s reason)))))
  :hints (("Goal" :in-theory (enable fn-csp-fail fn-cu-fail)))))

(local (defthm fn-csp-write-no-local
  (not (member-eq :local (strip-cars (cadr (fn-csp-write s emission resume)))))
  :hints (("Goal" :in-theory (e/d (fn-csp-write) (fn-csp-fail))))))

(local (defthm fn-csp-hash-effect-no-local
  (not (member-eq :local (strip-cars (cadr (fn-csp-hash-effect s)))))
  :hints (("Goal" :in-theory (enable fn-csp-hash-effect)))))

(local (defthm fn-csp-batch-finish-no-local
  ; The batch is finished with nothing left to offer: the effects journal and
  ; ask, and offer nothing.
  (not (member-eq :local (strip-cars (cadr (fn-csp-batch-finish s)))))
  :hints (("Goal" :in-theory (e/d (fn-csp-batch-finish fn-cu-next) (fn-csp-session-with-round))))))

(local (defthm fn-csp-record-done-no-local
  (not (member-eq :local (strip-cars (cadr (fn-csp-record-done s)))))
  :hints (("Goal" :in-theory (e/d (fn-csp-record-done) (fn-csp-batch-finish fn-csp-session-with-round))))))

(local (defthm fn-csp-read-replay-no-local
  (not (member-eq :local (strip-cars (cadr (fn-csp-read-replay s)))))
  :hints (("Goal" :in-theory (e/d (fn-csp-read-replay) (fn-csp-record-done fn-csp-fail))))))

(local (defthm fn-csp-member-local-effect-nl
  ; An effect (:local . x) is a :local among the effects' heads: effects
  ; with no :local head hold none.
  (implies (not (member-eq :local (strip-cars effs)))
           (not (member-equal (cons :local x) effs)))))

(local (defun fn-csp-offer-shape (conns s2 x)
  ; What an IHAVE effect x of a step reaching s2 from conns says.
  (declare (xargs :guard t))
  (and (equal (fn-pull-at 0 s2) :offer)
       (natp (fn-pull-at 19 s2))
       (equal (fn-pull-at (fn-pull-at 19 s2) conns) :free)
       (equal (fn-pull-at (fn-pull-at 19 s2) (fn-pull-at 18 s2))
              (cons (fn-pull-at 7 s2) :await335))
       (equal x (cons (fn-pull-at 19 s2)
                      (fn-cu-ihave (cons (fn-pull-at 7 s2) nil)))))))

(local (defthm fn-csp-try-offer-shape
  (implies (member-equal (cons :local x) (cadr (fn-csp-try-offer s)))
           (fn-csp-offer-shape (fn-csp-conns s) (car (fn-csp-try-offer s)) x))
  :rule-classes nil
  :hints (("Goal" :use fn-csp-try-offer-local-effect
                  :in-theory (e/d (fn-csp-offer-shape) (fn-csp-try-offer nfix))))))

(local (defthm fn-csp-after-header-shape
  (implies (member-equal (cons :local x) (cadr (fn-csp-after-header s line rest used)))
           (fn-csp-offer-shape (fn-csp-conns s) (car (fn-csp-after-header s line rest used)) x))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-csp-after-header)
                                  (fn-csp-fail fn-csp-write fn-csp-try-offer fn-csp-session-with-round
                                   fn-csp-offer-shape nfix
                                   fn-cu-parse-status fn-cu-parse-header fn-cu-batch-end
                                   fn-cu-batch-next fn-cu-batch-morep fn-cu-batch-claim
                                   fn-cu-u64-hex fn-record-string-octets binary-append
                                   fn-cu-hex fn-cu-unhex fn-cu-u64-octets-aux fn-cu-words-aux))
                  :use (:instance fn-csp-try-offer-shape
                         (s (fn-csp-with
                             (fn-csp-with s :header nil :crp nil :pending rest
                                          :replay (if (eq (fn-csp-mode s) :replay-header)
                                                      (+ (nfix (fn-csp-replay s)) used)
                                                    (fn-csp-replay s)))
                             :msgid (car (fn-cu-parse-header line))
                             :framer (fn-csp-framer (cdr (fn-cu-parse-header line)) nil)
                             :skip nil))
                         (x x))))))

(local (defthm fn-csp-try-offer-shape-f
  (implies (member-equal (cons :local x) (cadr (fn-csp-try-offer s)))
           (fn-csp-offer-shape (fn-pull-at 18 s) (car (fn-csp-try-offer s)) x))
  :rule-classes :forward-chaining
  :hints (("Goal" :use fn-csp-try-offer-shape :in-theory (enable fn-csp-conns)))))

(local (defthm fn-csp-after-header-shape-f
  (implies (member-equal (cons :local x) (cadr (fn-csp-after-header s line rest used)))
           (fn-csp-offer-shape (fn-pull-at 18 s) (car (fn-csp-after-header s line rest used)) x))
  :rule-classes :forward-chaining
  :hints (("Goal" :use fn-csp-after-header-shape :in-theory (enable fn-csp-conns)))))

(local (defthm fn-csp-nfix-of-natural
  (implies (and (integerp x) (<= 0 x)) (equal (nfix x) x))))

(local (defun fn-csp-body-shape (s x)
  ; What a body-window or terminator effect x of a step from s says: s is
  ; filling a record, x names its slot, and the slot holds the record's
  ; :streaming binding.
  (declare (xargs :guard t))
  (and (member-eq (fn-pull-at 0 s) '(:replay-body :terminator))
       (consp x)
       (natp (car x))
       (equal (car x) (fn-pull-at 19 s))
       (equal (fn-pull-at (car x) (fn-pull-at 18 s))
              (cons (fn-pull-at 7 s) :streaming)))))

(local (defthm fn-csp-nfix-of-natp (implies (natp x) (equal (nfix x) x))))
(local (defthm fn-csp-body-inv-of-streaming
  (implies (and (fn-csp-body-inv-of mode skip resume msgid slot conns)
                (or (member-eq mode '(:local-write :terminator))
                    (and (eq mode :replay-body) (not skip))))
           (and (natp slot)
                (equal (fn-pull-at slot conns) (cons msgid :streaming))))
  :rule-classes ((:rewrite :corollary
                  (implies (and (fn-csp-body-inv-of mode skip resume msgid slot conns)
                                (or (member-eq mode '(:local-write :terminator))
                                    (and (eq mode :replay-body) (not skip))))
                           (integerp slot)))
                 (:rewrite :corollary
                  (implies (and (fn-csp-body-inv-of mode skip resume msgid slot conns)
                                (or (member-eq mode '(:local-write :terminator))
                                    (and (eq mode :replay-body) (not skip))))
                           (<= 0 slot)))
                 (:rewrite :corollary
                  (implies (and (fn-csp-body-inv-of mode skip resume msgid slot conns)
                                (or (member-eq mode '(:local-write :terminator))
                                    (and (eq mode :replay-body) (not skip))))
                           (equal (fn-pull-at slot conns) (cons msgid :streaming)))))
  :hints (("Goal" :in-theory (enable fn-csp-body-inv-of nfix)))))

(local (defthm fn-csp-next-shape
  (implies (and (fn-csp-body-inv s)
                (member-equal (cons :local x) (cadr (fn-csp-next s))))
           (or (fn-csp-offer-shape (fn-pull-at 18 s) (car (fn-csp-next s)) x)
               (fn-csp-body-shape s x)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-csp-next fn-csp-body-inv-of-symbol)
                                  (fn-csp-fail fn-csp-write fn-csp-after-header
                                   fn-csp-read-replay fn-csp-hash-effect fn-csp-header-window
                                   fn-csp-framer-window fn-csp-framer-window-accounts-for-every-octet
                                   fn-csp-record-done fn-csp-try-offer fn-csp-session-with-round
                                   fn-csp-body-inv fn-csp-body-inv-of fn-csp-offer-shape nfix))))))

(local (defthm fn-csp-obs-effect-no-local
  (not (member-eq :local (strip-cars (fn-cu-obs-effect kind fc security round))))
  :hints (("Goal" :in-theory (enable fn-cu-obs-effect fn-pull-tls-effect)))))

(local (defthm fn-csp-obs-effects-no-local
  (not (member-eq :local (strip-cars (fn-cu-obs-effects obs fc security round))))
  :hints (("Goal" :induct (fn-cu-obs-effects obs fc security round)
                  :in-theory (e/d (fn-cu-obs-effects) (fn-cu-obs-effect))))))

(local (defthm fn-csp-strip-cars-append
  (equal (strip-cars (append a b)) (append (strip-cars a) (strip-cars b)))))

(local (defthm fn-csp-member-append-no-local
  (iff (member-eq :local (append a b))
       (or (member-eq :local a) (member-eq :local b)))))

(local (defthm fn-csp-cu-fail-no-local
  (not (member-eq :local (strip-cars (mv-nth 1 (fn-cu-fail r reason)))))
  :hints (("Goal" :in-theory (enable fn-cu-fail)))))

(local (defthm fn-csp-session-step-pair-no-local
  (not (member-eq :local (strip-cars (cadr (fn-cu-session-step-pair s event)))))
  :hints (("Goal" :in-theory (e/d (fn-cu-session-step-pair fn-cu-session-step)
                                  (fn-cu-session-fc-events fn-fc-drive fn-fc-drive-state
                                   fn-pull-pre-okp fn-cu-obs-effects fn-cu-fail
                                   fn-cu-session-readyp fn-cu-done-p))))))

(local (defthm fn-csp-local-opened-no-local
  (not (member-eq :local (strip-cars (cadr (fn-csp-local-opened s j code conns)))))
  :hints (("Goal" :in-theory (e/d (fn-csp-local-opened) (fn-csp-fail))))))

(local (defthm fn-csp-local-await335-no-local
  (not (member-eq :local (strip-cars (cadr (fn-csp-local-await335 s j code c conns round)))))
  :hints (("Goal" :in-theory (e/d (fn-csp-local-await335) (fn-csp-fail fn-csp-record-done fn-csp-session-with-round fn-cu-count nfix))))))

(local (defthm fn-csp-local-verdict-no-local
  (not (member-eq :local (strip-cars (cadr (fn-csp-local-verdict s j code conns round)))))
  :hints (("Goal" :in-theory (e/d (fn-csp-local-verdict)
                                  (fn-csp-fail fn-csp-batch-finish fn-csp-session-with-round fn-cu-count nfix))))))

(local (defthm fn-csp-local-no-local
  (not (member-eq :local (strip-cars (cadr (fn-csp-local s j octets)))))
  :hints (("Goal" :in-theory (e/d (fn-csp-local)
                                  (fn-csp-fail fn-csp-local-opened fn-csp-local-await335 fn-csp-local-verdict nfix))))))

(local (defthm fn-csp-local-window-no-local
  (not (member-eq :local (strip-cars (cadr (fn-csp-local-window s j)))))
  :hints (("Goal" :in-theory (e/d (fn-csp-local-window) (fn-csp-fail))))))

(local (defthm fn-csp-step-local-is-next
  ; Only a tick quantum emits a :local effect.
  (implies (member-equal (cons :local x) (cadr (fn-csp-step s event)))
           (equal (fn-csp-step s event) (fn-csp-next s)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-csp-step)
                                  (fn-csp-fail fn-csp-next fn-csp-local fn-csp-local-window
                                   fn-cu-session-step-pair fn-cu-session-readyp
                                   fn-blake3-stobj fn-cu-chainp fn-pull-event-octets
                                   fn-csp-session fn-csp-session-with-round nfix))))))

(local (defthm fn-csp-step-shape
  (implies (and (fn-csp-body-inv s)
                (member-equal (cons :local x) (cadr (fn-csp-step s event))))
           (or (fn-csp-offer-shape (fn-pull-at 18 s) (car (fn-csp-step s event)) x)
               (fn-csp-body-shape s x)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-csp-step fn-csp-next fn-csp-offer-shape fn-csp-body-shape
                                      fn-csp-body-inv)
                  :use (fn-csp-step-local-is-next (:instance fn-csp-next-shape))))))

(defthm fn-csp-body-only-after-its-335
  ; KEYSTONE (PRF-1335/1336, K1: a body is written only after its 335).  Under
  ; the controller's body invariant (fn-csp-body-inv: a held record or a
  ; spool write in flight carries what its resumption needs; the slot's
  ; connection is (msgid . :await335) while the offer awaits the local node's
  ; reply and (msgid . :streaming) while the body is spooled to it), every
  ; (:local j . octets) effect of a step is one of exactly two things.  Either
  ; it is the IHAVE of the record at hand, on a connection that was :free,
  ; which the step binds to (msgid . :await335) as the one offer in flight;
  ; or it is a body window or the terminator, written only from a body mode,
  ; on the slot of the filling record, whose connection is already
  ; (msgid . :streaming) -- a binding that only a 335 reply to the IHAVE
  ; creates (fn-csp-streaming-only-from-335).  A 435 record's body, skipped
  ; through the spool, emits no :local effect at all.  The invariant holds at
  ; the begin (fn-csp-begin-establishes-body-inv) and is kept by every step
  ; (fn-csp-step-keeps-body-inv), so every reachable state satisfies it.
  (implies (and (fn-csp-body-inv s)
                (member-equal (cons :local (cons j octets))
                              (cadr (fn-csp-step s event))))
           (let ((s2 (car (fn-csp-step s event))))
             (or (and (natp j)
                      (equal (fn-csp-conn j s) :free)
                      (equal (fn-csp-mode s2) :offer)
                      (equal (fn-csp-slot s2) j)
                      (equal (fn-csp-conn j s2) (cons (fn-csp-msgid s2) :await335))
                      (equal octets (fn-cu-ihave (cons (fn-csp-msgid s2) nil))))
                 (and (natp j)
                      (member-eq (fn-csp-mode s) '(:replay-body :terminator))
                      (equal (fn-csp-slot s) j)
                      (equal (fn-csp-conn j s) (cons (fn-csp-msgid s) :streaming))))))
  :hints (("Goal" :use (:instance fn-csp-step-shape (x (cons j octets)))
                  :in-theory (e/d (fn-csp-offer-shape fn-csp-body-shape fn-csp-conn fn-csp-conns
                                   fn-csp-mode fn-csp-slot fn-csp-msgid)
                                  (fn-csp-step fn-csp-body-inv nfix)))))

(local (defun fn-csp-ko-ind (k n)
  (declare (xargs :measure (+ (nfix k) (nfix n))))
  (if (or (zp k) (zp n)) n (fn-csp-ko-ind (1- k) (1- n)))))

(local (defthm fn-csp-pull-at-of-conns-of
  ; A reset table holds no binding.
  (implies (not (consp c))
           (not (consp (fn-pull-at k (fn-csp-conns-of n c)))))
  :hints (("Goal" :in-theory (enable fn-pull-at fn-csp-conns-of)
                  :induct (fn-csp-ko-ind k n) :expand ((fn-csp-conns-of n c))))))

(local (defthm fn-csp-pull-at-of-conns-of-not-binding
  (implies (not (consp c))
           (not (equal (fn-pull-at k (fn-csp-conns-of n c)) (cons a b))))
  :hints (("Goal" :use fn-csp-pull-at-of-conns-of
                  :in-theory (disable fn-csp-pull-at-of-conns-of)))))

(local (defthm fn-csp-conns-set-of-nfix
  ; The step reads its connection index through NFIX; a non-natural index is
  ; connection 0, as in the update itself.
  (equal (fn-csp-conns-set conns (nfix j) c) (fn-csp-conns-set conns j c))
  :hints (("Goal" :in-theory (enable nfix)))))

(local (defun fn-csp-keep (c2 c j)
  ; Every :streaming binding of the table C2 is C's own at that index -- or,
  ; at distance J (the index of a 335 reply), C's :await335 binding for the
  ; same Message-ID.  Nil J admits no such index.
  (declare (xargs :verify-guards nil))
  (if (atom c2) t
    (let ((h (if (consp c) (car c) nil)))
      (and (implies (and (consp (car c2)) (eq (cdr (car c2)) :streaming))
                    (or (equal (car c2) h)
                        (and (eql j 0) (consp h) (eq (cdr h) :await335)
                             (equal (car h) (car (car c2))))))
           (fn-csp-keep (cdr c2) (if (consp c) (cdr c) nil)
                        (and (natp j) (< 0 j) (1- j))))))))

(local (defthm fn-csp-keep-refl (fn-csp-keep c c j)
  :hints (("Goal" :in-theory (enable fn-csp-keep)
                  :induct (fn-csp-keep c c j)))))

(local (defthm fn-csp-keep-weaken
  (implies (fn-csp-keep c2 c nil) (fn-csp-keep c2 c j))
  :hints (("Goal" :in-theory (enable fn-csp-keep)
                  :induct (fn-csp-keep c2 c j)))))

(local (defthm fn-csp-keep-of-set
  ; Binding a connection to anything but a :streaming binding adds none.
  (implies (not (and (consp b) (eq (cdr b) :streaming)))
           (fn-csp-keep (fn-csp-conns-set conns j b) conns nil))
  :hints (("Goal" :in-theory (enable fn-csp-keep fn-csp-conns-set)
                  :induct (fn-csp-conns-set conns j b)))))

(local (defthm fn-csp-keep-of-335
  ; The one place a :streaming binding appears: the 335 reply to the IHAVE.
  (implies (and (consp (fn-pull-at j conns)) (eq (cdr (fn-pull-at j conns)) :await335)
                (natp j))
           (fn-csp-keep (fn-csp-conns-set conns j (cons (car (fn-pull-at j conns)) :streaming))
                        conns j))
  :hints (("Goal" :in-theory (enable fn-csp-keep fn-csp-conns-set fn-pull-at)
                  :induct (fn-csp-conns-set conns j b)))))

(local (defun fn-csp-ind2 (n c)
  (declare (xargs :measure (nfix n)))
  (if (zp n) c (fn-csp-ind2 (1- n) (if (consp c) (cdr c) nil)))))

(local (defthm fn-csp-keep-of-conns-of
  (implies (not (and (consp b) (eq (cdr b) :streaming)))
           (fn-csp-keep (fn-csp-conns-of n b) conns nil))
  :hints (("Goal" :in-theory (enable fn-csp-keep fn-csp-conns-of)
                  :induct (fn-csp-ind2 n conns)))))

(local (defun fn-csp-ind3 (c2 c j k)
  (declare (xargs :verify-guards nil))
  (if (or (atom c2) (zp k)) (list c j)
    (fn-csp-ind3 (cdr c2) (if (consp c) (cdr c) nil)
                 (and (natp j) (< 0 j) (1- j)) (1- k)))))

(local (defthm fn-csp-keep-pointwise
  (implies (and (fn-csp-keep c2 c j) (natp k)
                (equal (fn-pull-at k c2) (cons m :streaming)))
           (or (equal (fn-pull-at k c) (cons m :streaming))
               (and (equal k j) (equal (fn-pull-at k c) (cons m :await335)))))
  :hints (("Goal" :in-theory (enable fn-pull-at)
                  :expand ((fn-csp-keep c2 c j))
                  :induct (fn-csp-ind3 c2 c j k)))))

(local (defthm fn-csp-fail-keep
  (fn-csp-keep (fn-pull-at 18 (car (fn-csp-fail s reason))) conns nil)
  :hints (("Goal" :in-theory (e/d (fn-csp-fail) (fn-csp-session-with-round))))))

(local (defthm fn-csp-batch-finish-conns
  (equal (fn-pull-at 18 (car (fn-csp-batch-finish s))) (fn-pull-at 18 s))
  :hints (("Goal" :in-theory (e/d (fn-csp-batch-finish) (fn-cu-next fn-csp-session-with-round))))))

(local (defthm fn-csp-record-done-conns
  (equal (fn-pull-at 18 (car (fn-csp-record-done s))) (fn-pull-at 18 s))
  :hints (("Goal" :in-theory (e/d (fn-csp-record-done) (fn-csp-batch-finish fn-csp-session-with-round))))))

(local (defthm fn-csp-write-keep
  (implies (equal conns (fn-pull-at 18 s))
           (fn-csp-keep (fn-pull-at 18 (car (fn-csp-write s emission resume))) conns nil))
  :hints (("Goal" :in-theory (e/d (fn-csp-write) (fn-csp-fail))
                  :use (:instance fn-csp-fail-keep (conns conns))))))

(local (defthm fn-csp-hash-effect-conns
  (equal (fn-pull-at 18 (car (fn-csp-hash-effect s))) (fn-pull-at 18 s))
  :hints (("Goal" :in-theory (enable fn-csp-hash-effect)))))

(local (defthm fn-csp-try-offer-keep
  (implies (equal conns (fn-pull-at 18 s))
           (fn-csp-keep (fn-pull-at 18 (car (fn-csp-try-offer s))) conns nil))
  :hints (("Goal" :in-theory (e/d (fn-csp-try-offer fn-csp-conns) (nfix))))))

(local (defthm fn-csp-read-replay-keep
  (implies (equal conns (fn-pull-at 18 s))
           (fn-csp-keep (fn-pull-at 18 (car (fn-csp-read-replay s))) conns nil))
  :hints (("Goal" :in-theory (e/d (fn-csp-read-replay) (fn-csp-record-done fn-csp-fail))
                  :use (:instance fn-csp-fail-keep (conns conns))))))

(local (defthm fn-csp-after-header-keep
  (implies (equal conns (fn-pull-at 18 s))
           (fn-csp-keep (fn-pull-at 18 (car (fn-csp-after-header s line rest used))) conns nil))
  :hints (("Goal" :in-theory (e/d (fn-csp-after-header)
                                  (fn-csp-fail fn-csp-write fn-csp-try-offer fn-csp-session-with-round
                                   fn-cu-parse-status fn-cu-parse-header fn-cu-batch-end
                                   fn-cu-batch-next fn-cu-batch-morep fn-cu-batch-claim
                                   fn-cu-u64-hex fn-record-string-octets binary-append nfix
                                   fn-cu-hex fn-cu-unhex fn-cu-u64-octets-aux fn-cu-words-aux))))))

(local (defthm fn-csp-local-window-keep
  (fn-csp-keep (fn-pull-at 18 (car (fn-csp-local-window s j))) (fn-pull-at 18 s) nil)
  :hints (("Goal" :in-theory (e/d (fn-csp-local-window fn-csp-conn) (fn-csp-fail nfix))))))

(local (defthm fn-csp-local-opened-keep
  (implies (equal conns (fn-pull-at 18 s))
           (fn-csp-keep (fn-pull-at 18 (car (fn-csp-local-opened s j code conns))) (fn-pull-at 18 s) nil))
  :hints (("Goal" :in-theory (e/d (fn-csp-local-opened) (fn-csp-fail))))))

(local (defthm fn-csp-local-verdict-keep
  (implies (equal conns (fn-pull-at 18 s))
           (fn-csp-keep (fn-pull-at 18 (car (fn-csp-local-verdict s j code conns round)))
                        (fn-pull-at 18 s) nil))
  :hints (("Goal" :in-theory (e/d (fn-csp-local-verdict)
                                  (fn-csp-fail fn-csp-batch-finish fn-csp-session-with-round fn-cu-count))))))

(local (defthm fn-csp-local-await335-keep
  (implies (and (equal conns (fn-pull-at 18 s))
                (equal c (fn-pull-at (nfix j) conns))
                (consp c) (eq (cdr c) :await335))
           (and (fn-csp-keep (fn-pull-at 18 (car (fn-csp-local-await335 s j code c conns round)))
                             (fn-pull-at 18 s) (nfix j))
                (or (equal code 335)
                    (fn-csp-keep (fn-pull-at 18 (car (fn-csp-local-await335 s j code c conns round)))
                                 (fn-pull-at 18 s) nil))))
  :hints (("Goal" :in-theory (e/d (fn-csp-local-await335)
                                  (fn-csp-fail fn-csp-record-done fn-csp-session-with-round fn-cu-count nfix))
                  :use (:instance fn-csp-keep-of-335 (j (nfix j)) (conns conns))))))

(local (defthm fn-csp-local-keep
  (or (fn-csp-keep (fn-pull-at 18 (car (fn-csp-local s j octets))) (fn-pull-at 18 s) nil)
      (and (equal (fn-pull-local-code octets) 335)
           (eq (fn-pull-at 0 s) :offer)
           (equal (fn-pull-at 19 s) (nfix j))
           (fn-csp-keep (fn-pull-at 18 (car (fn-csp-local s j octets))) (fn-pull-at 18 s) (nfix j))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-csp-local fn-csp-conn fn-csp-conns fn-csp-mode fn-csp-slot)
                                  (fn-csp-fail fn-csp-local-opened fn-csp-local-await335
                                   fn-csp-local-verdict nfix))
                  :use ((:instance fn-csp-local-await335-keep
                          (code (fn-pull-local-code octets)) (conns (fn-pull-at 18 s))
                          (c (fn-pull-at (nfix j) (fn-pull-at 18 s)))
                          (round (fn-cu-s-round (fn-csp-session s))))
                        (:instance fn-csp-local-opened-keep
                          (code (fn-pull-local-code octets)) (conns (fn-pull-at 18 s)))
                        (:instance fn-csp-local-verdict-keep
                          (code (fn-pull-local-code octets)) (conns (fn-pull-at 18 s))
                          (round (fn-cu-s-round (fn-csp-session s)))))))))

(local (defthm fn-csp-next-keep
  (fn-csp-keep (fn-pull-at 18 (car (fn-csp-next s))) (fn-pull-at 18 s) nil)
  :hints (("Goal" :in-theory (e/d (fn-csp-next)
                                  (fn-csp-fail fn-csp-write fn-csp-after-header
                                   fn-csp-read-replay fn-csp-hash-effect fn-csp-header-window
                                   fn-csp-framer-window fn-csp-framer-window-accounts-for-every-octet
                                   fn-csp-record-done fn-csp-try-offer fn-csp-session-with-round nfix))))))

(local (defthm fn-csp-step-keep
  (or (fn-csp-keep (fn-pull-at 18 (car (fn-csp-step s event))) (fn-pull-at 18 s) nil)
      (and (equal (car (fn-pull-list event)) :local)
           (equal (fn-pull-local-code (fn-csp-local-event-octets event)) 335)
           (eq (fn-pull-at 0 s) :offer)
           (equal (fn-pull-at 19 s) (nfix (nth 1 event)))
           (fn-csp-keep (fn-pull-at 18 (car (fn-csp-step s event))) (fn-pull-at 18 s)
                        (nfix (nth 1 event)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-csp-step)
                                  (fn-csp-fail fn-csp-next fn-csp-local fn-csp-local-window
                                   fn-cu-session-step-pair fn-cu-session-readyp
                                   fn-blake3-stobj fn-cu-chainp fn-pull-event-octets
                                   fn-csp-session fn-csp-session-with-round nfix))
                  :use ((:instance fn-csp-local-keep (j (nfix (nth 1 event)))
                                   (octets (fn-csp-local-event-octets event))))))))

(defthm fn-csp-streaming-only-from-335
  ; KEYSTONE (PRF-1335/1336, K1's other half).  A connection holds a
  ; (msgid . :streaming) binding after a step only if it held it before, or
  ; the step is the local node's 335 reply, on that connection, to the IHAVE
  ; (msgid . :await335) bound there -- the offer in flight, the mode :offer
  ; and the slot that connection.  No other event, reply code or phase
  ; creates a streaming binding, so fn-csp-body-only-after-its-335's body
  ; windows and terminators are written only after the 335.
  (implies (and (natp k)
                (equal (fn-csp-conn k (car (fn-csp-step s event))) (cons m :streaming)))
           (or (equal (fn-csp-conn k s) (cons m :streaming))
               (and (equal (fn-csp-conn k s) (cons m :await335))
                    (equal (car (fn-pull-list event)) :local)
                    (equal (nfix (nth 1 event)) k)
                    (equal (fn-pull-local-code (fn-csp-local-event-octets event)) 335)
                    (eq (fn-csp-mode s) :offer)
                    (equal (fn-csp-slot s) k))))
  :hints (("Goal" :use (fn-csp-step-keep
                        (:instance fn-csp-keep-pointwise
                          (c2 (fn-pull-at 18 (car (fn-csp-step s event))))
                          (c (fn-pull-at 18 s)) (j nil))
                        (:instance fn-csp-keep-pointwise
                          (c2 (fn-pull-at 18 (car (fn-csp-step s event))))
                          (c (fn-pull-at 18 s)) (j (nfix (nth 1 event)))))
                  :in-theory (e/d (fn-csp-conn fn-csp-conns fn-csp-mode fn-csp-slot)
                                  (fn-csp-step fn-csp-keep nfix)))))

;; -----------------------------------------------------------------------------
;; K3: a journal is emitted only for a settled batch (PRF-1335/1336).  The
;; drain invariant below carries the spool cursor across fn-csp-step; the
;; classification then reads every :journal effect off its two sources,
;; fn-csp-record-done after the last record and the last settling verdict of
;; a drained batch.

(defun fn-csp-drain-inv-of (mode offset replay)
  ; A drained batch's spool cursor is at its end: the controller enters
  ; :drain only from record-done, with no record left to read (replay has
  ; caught up with offset), and while it drains neither moves.
  (declare (xargs :guard t))
  (implies (eq mode :drain) (<= (nfix offset) (nfix replay))))

(defun fn-csp-drain-inv (s)
  (declare (xargs :guard t))
  (fn-csp-drain-inv-of (fn-csp-mode s) (fn-csp-offset s) (fn-csp-replay s)))

(local (defthm fn-csp-drain-inv-of-state
  (equal (fn-csp-drain-inv (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19))
         (fn-csp-drain-inv-of a0 a5 a11))
  :hints (("Goal" :in-theory (enable fn-csp-drain-inv fn-csp-mode fn-csp-offset fn-csp-replay)))))

(local (defthm fn-csp-drain-inv-of-symbol
  (implies (syntaxp (symbolp s))
           (equal (fn-csp-drain-inv s)
                  (fn-csp-drain-inv-of (fn-pull-at 0 s) (fn-pull-at 5 s) (fn-pull-at 11 s))))
  :hints (("Goal" :in-theory (enable fn-csp-drain-inv fn-csp-mode fn-csp-offset fn-csp-replay)))))

(local (in-theory (disable fn-csp-drain-inv)))

(local (defthm fn-csp-drain-inv-of-non-drain
  (implies (not (eq mode :drain)) (fn-csp-drain-inv-of mode offset replay))
  :hints (("Goal" :in-theory (enable fn-csp-drain-inv-of)))))

(local (defthm fn-csp-fail-keeps-drain-inv
  (fn-csp-drain-inv (car (fn-csp-fail s reason)))
  :hints (("Goal" :use fn-csp-fail-mode
           :in-theory (e/d (fn-csp-drain-inv fn-csp-mode fn-csp-offset fn-csp-replay)
                           (fn-csp-fail-mode fn-csp-fail))))))

(local (defthm fn-csp-body-inv-of-write-resume
  ; What a body-invariant state in a resuming mode resumes: never :drain.
  (implies (fn-csp-body-inv-of :write skip resume msgid slot conns)
           (member-eq resume '(:hash :body)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-csp-body-inv-of)))))

(local (defthm fn-csp-body-inv-of-local-write-resume
  (implies (fn-csp-body-inv-of :local-write skip resume msgid slot conns)
           (member-eq resume '(:terminator :replay-body)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-csp-body-inv-of)))))

(local (defthm fn-csp-batch-finish-keeps-drain-inv
  (fn-csp-drain-inv (car (fn-csp-batch-finish s)))
  :hints (("Goal" :use fn-csp-batch-finish-mode
           :in-theory (e/d (fn-csp-drain-inv fn-csp-mode) (fn-csp-batch-finish-mode fn-csp-batch-finish))))))

(local (defthm fn-csp-record-done-keeps-drain-inv
  ; record-done enters :drain only with the replay cursor at the batch end.
  (fn-csp-drain-inv (car (fn-csp-record-done s)))
  :hints (("Goal" :in-theory (e/d (fn-csp-record-done fn-csp-drain-inv-of-symbol)
                                  (fn-csp-batch-finish fn-csp-session-with-round fn-csp-drain-inv))
           :use (:instance fn-csp-batch-finish-keeps-drain-inv
                           (s (fn-csp-with s :slot nil :skip nil :framer nil :msgid nil)))))))

(local (defthm fn-csp-write-keeps-drain-inv
  (implies (member-eq resume '(:hash :body))
           (fn-csp-drain-inv (car (fn-csp-write s emission resume))))
  :hints (("Goal" :in-theory (e/d (fn-csp-write fn-csp-drain-inv-of-symbol)
                                  (fn-csp-drain-inv fn-csp-fail))
                  :use fn-csp-fail-keeps-drain-inv))))

(local (defthm fn-csp-try-offer-keeps-drain-inv
  (fn-csp-drain-inv (car (fn-csp-try-offer s)))
  :hints (("Goal" :in-theory (e/d (fn-csp-try-offer fn-csp-drain-inv-of-symbol) (fn-csp-drain-inv fn-csp-drain-inv-of))))))

(local (defthm fn-csp-hash-effect-keeps-drain-inv
  (implies (fn-csp-drain-inv s) (fn-csp-drain-inv (car (fn-csp-hash-effect s))))
  :hints (("Goal" :in-theory (enable fn-csp-hash-effect)))))

(local (defthm fn-csp-read-replay-keeps-drain-inv
  (implies (fn-csp-drain-inv s) (fn-csp-drain-inv (car (fn-csp-read-replay s))))
  :hints (("Goal" :in-theory (e/d (fn-csp-read-replay fn-csp-drain-inv-of-symbol)
                                  (fn-csp-record-done fn-csp-fail fn-csp-drain-inv))
                  :use (fn-csp-record-done-keeps-drain-inv
                        (:instance fn-csp-fail-keeps-drain-inv (reason :short-spool)))))))

(local (defthm fn-csp-after-header-keeps-drain-inv
  (fn-csp-drain-inv (car (fn-csp-after-header s line rest used)))
  :hints (("Goal" :in-theory (e/d (fn-csp-after-header fn-csp-drain-inv-of-symbol)
                                  (fn-csp-fail fn-csp-write fn-csp-try-offer fn-csp-drain-inv
                                   binary-append fn-csp-session-with-round
                                   fn-cu-parse-status fn-cu-parse-header fn-cu-batch-end
                                   fn-cu-batch-next fn-cu-batch-morep fn-cu-batch-claim
                                   fn-cu-u64-hex fn-record-string-octets
                                   fn-cu-hex fn-cu-unhex fn-cu-u64-octets-aux fn-cu-words-aux))))))

(local (defthm fn-csp-local-window-keeps-drain-inv
  (implies (and (fn-csp-body-inv s) (fn-csp-drain-inv s))
           (fn-csp-drain-inv (car (fn-csp-local-window s j))))
  :hints (("Goal" :in-theory (e/d (fn-csp-local-window fn-csp-conn fn-csp-body-inv-of-symbol fn-csp-drain-inv-of-symbol)
                                  (fn-csp-fail fn-csp-body-inv fn-csp-drain-inv))
                  :use (:instance fn-csp-fail-keeps-drain-inv (reason :local-refused))))))
(local (defthm fn-csp-local-opened-keeps-drain-inv
  (implies (fn-csp-drain-inv s)
           (fn-csp-drain-inv (car (fn-csp-local-opened s j code conns))))
  :hints (("Goal" :in-theory (e/d (fn-csp-local-opened fn-csp-drain-inv-of-symbol)
                                  (fn-csp-fail fn-csp-drain-inv nfix))
                  :use (:instance fn-csp-fail-keeps-drain-inv (reason :local-refused))))))

(local (defthm fn-csp-local-verdict-keeps-drain-inv
  (implies (fn-csp-drain-inv s)
           (fn-csp-drain-inv (car (fn-csp-local-verdict s j code conns round))))
  :hints (("Goal" :in-theory (e/d (fn-csp-local-verdict fn-csp-drain-inv-of-symbol)
                                  (fn-csp-fail fn-csp-drain-inv fn-csp-batch-finish
                                   fn-csp-session-with-round fn-cu-count nfix))
                  :use ((:instance fn-csp-fail-keeps-drain-inv (reason :local-refused))
                        (:instance fn-csp-fail-keeps-drain-inv (reason :local-deferred)))))))

(local (defthm fn-csp-local-await335-keeps-drain-inv
  (implies (fn-csp-drain-inv s)
           (fn-csp-drain-inv (car (fn-csp-local-await335 s j code c conns round))))
  :hints (("Goal" :in-theory (e/d (fn-csp-local-await335 fn-csp-drain-inv-of-symbol)
                                  (fn-csp-fail fn-csp-drain-inv fn-csp-record-done
                                   fn-csp-session-with-round fn-cu-count nfix))
                  :use ((:instance fn-csp-fail-keeps-drain-inv (reason :local-refused))
                        (:instance fn-csp-fail-keeps-drain-inv (reason :local-deferred))
                        (:instance fn-csp-record-done-keeps-drain-inv
                          (s (fn-csp-with (fn-csp-session-with-round
                                            s (fn-cu-with round :counts
                                                          (fn-cu-count (fn-cu-r-counts round) 1)))
                                          :conns (fn-csp-conns-set conns j :free) :slot nil))))))))

(local (defthm fn-csp-local-keeps-drain-inv
  (implies (fn-csp-drain-inv s)
           (fn-csp-drain-inv (car (fn-csp-local s j octets))))
  :hints (("Goal" :in-theory (e/d (fn-csp-local fn-csp-conn)
                                  (fn-csp-fail fn-csp-local-opened fn-csp-local-await335
                                   fn-csp-local-verdict fn-csp-drain-inv nfix))
                  :use ((:instance fn-csp-fail-keeps-drain-inv (reason :local-refused))
                        (:instance fn-csp-local-opened-keeps-drain-inv
                          (code (fn-pull-local-code octets)) (conns (fn-csp-conns s)))
                        (:instance fn-csp-local-await335-keeps-drain-inv
                          (code (fn-pull-local-code octets)) (conns (fn-csp-conns s))
                          (c (fn-csp-conn j s)) (round (fn-cu-s-round (fn-csp-session s))))
                        (:instance fn-csp-local-verdict-keeps-drain-inv
                          (code (fn-pull-local-code octets)) (conns (fn-csp-conns s))
                          (round (fn-cu-s-round (fn-csp-session s)))))))))

(local (defthm fn-csp-next-keeps-drain-inv
  (implies (fn-csp-drain-inv s) (fn-csp-drain-inv (car (fn-csp-next s))))
  :hints (("Goal" :in-theory (e/d (fn-csp-next fn-csp-drain-inv-of-symbol)
                                  (fn-csp-fail fn-csp-write fn-csp-after-header
                                   fn-csp-read-replay fn-csp-hash-effect fn-csp-header-window
                                   fn-csp-framer-window fn-csp-framer-window-accounts-for-every-octet
                                   fn-csp-record-done fn-csp-try-offer fn-csp-session-with-round
                                   fn-csp-drain-inv nfix))))))
(defthm fn-csp-step-keeps-drain-inv
  ; The drain invariant, preserved by every step event (given K1's body
  ; invariant, which says what a spool write in flight resumes).
  (implies (and (fn-csp-body-inv s) (fn-csp-drain-inv s))
           (fn-csp-drain-inv (car (fn-csp-step s event))))
  :hints (("Goal" :in-theory (e/d (fn-csp-step fn-csp-drain-inv-of-symbol fn-csp-body-inv-of-symbol)
                                  (fn-csp-fail fn-csp-next fn-csp-local fn-csp-local-window
                                   fn-cu-session-step-pair fn-cu-session-readyp
                                   fn-blake3-stobj fn-cu-chainp fn-pull-event-octets
                                   fn-csp-session fn-csp-session-with-round fn-csp-drain-inv
                                   fn-csp-body-inv fn-csp-body-inv-of nfix)))))

(defthm fn-csp-begin-establishes-drain-inv
  (fn-csp-drain-inv (car (fn-csp-begin plan cursor credential limit window)))
  :hints (("Goal" :in-theory (e/d (fn-csp-begin fn-csp-drain-inv-of-symbol)
                                  (fn-csp-fail fn-csp-drain-inv fn-cu-session-begin-pair
                                   fn-cu-cursor-chain fn-csp-conns-of nfix)))))

(local (defthm fn-csp-batch-finish-journal
  ; batch-finish's effects: one (:journal . cursor) first, naming the cursor
  ; of the round it produces, then the next request or the quit and close.
  (let* ((pair (fn-csp-batch-finish s)) (effs (cadr pair)))
    (and (consp effs)
         (eq (car (car effs)) :journal)
         (equal (cdr (car effs))
                (fn-cu-round-cursor (fn-cu-s-round (fn-csp-session (car pair)))))
         (not (member-eq :journal (strip-cars (cdr effs))))))
  :hints (("Goal" :in-theory (enable fn-csp-batch-finish fn-csp-session-with-round fn-cu-next)))))

(defun fn-csp-at-end (s)
  ; The spool cursor is at the batch end: the replay has read every octet
  ; the batch wrote.
  (declare (xargs :guard t))
  (not (< (nfix (fn-csp-replay s)) (nfix (fn-csp-offset s)))))

(defun fn-csp-jok (at-end pair)
  ; What a step's journal owes: it is the one effect journalling the produced
  ; round's cursor, led by nothing; the spool cursor stood at the batch end
  ; (AT-END, of the state the step ran from); and the state it reaches has
  ; finished the batch (:done or :status) with every connection settled.
  (declare (xargs :verify-guards nil))
  (let ((effs (cadr pair)) (s2 (car pair)))
    (implies (member-eq :journal (strip-cars effs))
             (and at-end
                  (consp effs)
                  (eq (car (car effs)) :journal)
                  (equal (cdr (car effs))
                         (fn-cu-round-cursor (fn-cu-s-round (fn-csp-session s2))))
                  (not (member-eq :journal (strip-cars (cdr effs))))
                  (member-eq (fn-csp-mode s2) '(:done :status))
                  (fn-csp-conns-idlep (fn-csp-conns s2))))))

(local (in-theory (disable fn-csp-at-end fn-csp-jok)))

(local (defthm fn-csp-jok-of-no-journal
  (implies (not (member-eq :journal (strip-cars (cadr pair))))
           (fn-csp-jok at-end pair))
  :hints (("Goal" :in-theory (enable fn-csp-jok)))))

(local (defthm fn-csp-fail-no-journal
  (not (member-eq :journal (strip-cars (cadr (fn-csp-fail s reason)))))
  :hints (("Goal" :in-theory (enable fn-csp-fail fn-cu-fail)))))

(local (defthm fn-csp-write-no-journal
  (not (member-eq :journal (strip-cars (cadr (fn-csp-write s emission resume)))))
  :hints (("Goal" :in-theory (e/d (fn-csp-write) (fn-csp-fail))))))

(local (defthm fn-csp-hash-effect-no-journal
  (not (member-eq :journal (strip-cars (cadr (fn-csp-hash-effect s)))))
  :hints (("Goal" :in-theory (enable fn-csp-hash-effect)))))

(local (defthm fn-csp-try-offer-no-journal
  (not (member-eq :journal (strip-cars (cadr (fn-csp-try-offer s)))))
  :hints (("Goal" :in-theory (enable fn-csp-try-offer)))))

(local (defthm fn-csp-after-header-no-journal
  (not (member-eq :journal (strip-cars (cadr (fn-csp-after-header s line rest used)))))
  :hints (("Goal" :in-theory (e/d (fn-csp-after-header)
                                  (fn-csp-fail fn-csp-write fn-csp-try-offer fn-csp-session-with-round
                                   binary-append
                                   fn-cu-parse-status fn-cu-parse-header fn-cu-batch-end
                                   fn-cu-batch-next fn-cu-batch-morep fn-cu-batch-claim
                                   fn-cu-u64-hex fn-record-string-octets
                                   fn-cu-hex fn-cu-unhex fn-cu-u64-octets-aux fn-cu-words-aux))))))

(local (defthm fn-csp-record-done-jok-at
  (implies (equal at-end (fn-csp-at-end s))
           (fn-csp-jok at-end (fn-csp-record-done s)))
  :hints (("Goal" :in-theory (e/d (fn-csp-record-done fn-csp-jok fn-csp-at-end)
                                  (fn-csp-batch-finish fn-csp-session-with-round))
                  :use (fn-csp-batch-finish-mode
                        (:instance fn-csp-batch-finish-journal
                                   (s (fn-csp-with s :slot nil :skip nil :framer nil :msgid nil)))
                        (:instance fn-csp-batch-finish-conns
                                   (s (fn-csp-with s :slot nil :skip nil :framer nil :msgid nil)))
                        (:instance fn-csp-batch-finish-mode
                                   (s (fn-csp-with s :slot nil :skip nil :framer nil :msgid nil))))))))

(local (defthm fn-csp-read-replay-jok
  (implies (equal at-end (fn-csp-at-end s))
           (fn-csp-jok at-end (fn-csp-read-replay s)))
  :hints (("Goal" :in-theory (e/d (fn-csp-read-replay) (fn-csp-record-done fn-csp-fail))
                  :use fn-csp-record-done-jok-at))))

(local (defthm fn-csp-at-end-of-symbol
  (implies (syntaxp (symbolp s))
           (equal (fn-csp-at-end s)
                  (not (< (nfix (fn-pull-at 11 s)) (nfix (fn-pull-at 5 s))))))
  :hints (("Goal" :in-theory (enable fn-csp-at-end fn-csp-replay fn-csp-offset)))))

(local (defthm fn-csp-at-end-of-state
  (equal (fn-csp-at-end (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19))
         (not (< (nfix a11) (nfix a5))))
  :hints (("Goal" :in-theory (enable fn-csp-at-end fn-csp-replay fn-csp-offset)))))

(local (defthm fn-csp-local-opened-jok
  (fn-csp-jok at-end (fn-csp-local-opened s j code conns))
  :hints (("Goal" :in-theory (e/d (fn-csp-local-opened) (fn-csp-fail))))))

(local (defthm fn-csp-local-window-jok
  (fn-csp-jok at-end (fn-csp-local-window s j))
  :hints (("Goal" :in-theory (e/d (fn-csp-local-window) (fn-csp-fail))))))

(local (defthm fn-csp-local-await335-jok
  (implies (equal at-end (fn-csp-at-end s))
           (fn-csp-jok at-end (fn-csp-local-await335 s j code c conns round)))
  :hints (("Goal" :in-theory (e/d (fn-csp-local-await335 fn-csp-at-end-of-symbol)
                                  (fn-csp-fail fn-csp-record-done fn-csp-session-with-round fn-cu-count nfix
                                   fn-csp-at-end))
                  :use ((:instance fn-csp-record-done-jok-at
                          (s (fn-csp-with (fn-csp-session-with-round
                                            s (fn-cu-with round :counts
                                                          (fn-cu-count (fn-cu-r-counts round) 1)))
                                          :conns (fn-csp-conns-set conns j :free) :slot nil))))))))
(local (defthm fn-csp-local-verdict-jok
  ; The final verdict of a drained batch is the settling reply that journals:
  ; the drain invariant puts the spool cursor at the batch end, and the free
  ; of the settled connection leaves the window idle.
  (implies (and (fn-csp-drain-inv s) (equal at-end (fn-csp-at-end s)))
           (fn-csp-jok at-end (fn-csp-local-verdict s j code conns round)))
  :hints (("Goal" :in-theory (e/d (fn-csp-local-verdict fn-csp-drain-inv-of-symbol fn-csp-jok
                                   fn-csp-at-end-of-symbol)
                                  (fn-csp-fail fn-csp-batch-finish fn-csp-session-with-round
                                   fn-cu-count nfix fn-csp-drain-inv fn-csp-at-end))
                  :use ((:instance fn-csp-batch-finish-journal
                          (s (fn-csp-with (fn-csp-session-with-round
                                           s (fn-cu-with round :counts
                                                         (fn-cu-count (fn-cu-r-counts round) 0)))
                                          :conns (fn-csp-conns-set conns j :free))))
                        (:instance fn-csp-batch-finish-journal
                          (s (fn-csp-with (fn-csp-session-with-round
                                           s (fn-cu-with round :counts
                                                         (fn-cu-count (fn-cu-r-counts round) 2)))
                                          :conns (fn-csp-conns-set conns j :free))))
                        (:instance fn-csp-batch-finish-mode
                          (s (fn-csp-with (fn-csp-session-with-round
                                           s (fn-cu-with round :counts
                                                         (fn-cu-count (fn-cu-r-counts round) 0)))
                                          :conns (fn-csp-conns-set conns j :free))))
                        (:instance fn-csp-batch-finish-mode
                          (s (fn-csp-with (fn-csp-session-with-round
                                           s (fn-cu-with round :counts
                                                         (fn-cu-count (fn-cu-r-counts round) 2)))
                                          :conns (fn-csp-conns-set conns j :free))))
                        (:instance fn-csp-batch-finish-conns
                          (s (fn-csp-with (fn-csp-session-with-round
                                           s (fn-cu-with round :counts
                                                         (fn-cu-count (fn-cu-r-counts round) 0)))
                                          :conns (fn-csp-conns-set conns j :free))))
                        (:instance fn-csp-batch-finish-conns
                          (s (fn-csp-with (fn-csp-session-with-round
                                           s (fn-cu-with round :counts
                                                         (fn-cu-count (fn-cu-r-counts round) 2)))
                                          :conns (fn-csp-conns-set conns j :free)))))))))
(local (defthm fn-csp-local-jok
  (implies (and (fn-csp-drain-inv s) (equal at-end (fn-csp-at-end s)))
           (fn-csp-jok at-end (fn-csp-local s j octets)))
  :hints (("Goal" :in-theory (e/d (fn-csp-local)
                                  (fn-csp-fail fn-csp-local-opened fn-csp-local-await335
                                   fn-csp-local-verdict fn-csp-drain-inv fn-csp-at-end nfix))
                  :use ((:instance fn-csp-local-verdict-jok
                          (code (fn-pull-local-code octets)) (conns (fn-csp-conns s))
                          (round (fn-cu-s-round (fn-csp-session s))))
                        (:instance fn-csp-local-await335-jok
                          (code (fn-pull-local-code octets)) (conns (fn-csp-conns s))
                          (c (fn-csp-conn j s)) (round (fn-cu-s-round (fn-csp-session s))))
                        (:instance fn-csp-local-opened-jok
                          (code (fn-pull-local-code octets)) (conns (fn-csp-conns s))))))))

(local (defthm fn-csp-conns-set-consp-not-idle
  ; A consp placed at j is a (msgid . phase) binding, and idleness is the
  ; absence of every such entry.
  (implies (consp c)
           (not (fn-csp-conns-idlep (fn-csp-conns-set conns j c))))
  :hints (("Goal" :induct (fn-csp-conns-set conns j c)
                  :in-theory (enable fn-csp-conns-set fn-csp-conns-idlep)))))

(local (defthm fn-csp-record-done-journal-idle
  ; record-done journals only from an idle window.
  (implies (member-eq :journal (strip-cars (cadr (fn-csp-record-done s))))
           (fn-csp-conns-idlep (fn-csp-conns s)))
  :hints (("Goal" :in-theory (e/d (fn-csp-jok fn-csp-conns) (fn-csp-record-done fn-csp-record-done-jok-at))
                  :use ((:instance fn-csp-record-done-jok-at (at-end (fn-csp-at-end s)))
                        fn-csp-record-done-conns)))))

(local (defthm fn-csp-terminator-no-journal
  ; The terminator binds its connection (msgid . :verdict) before it asks
  ; record-done, so the window is not idle and record-done journals nothing.
  (implies (equal (fn-csp-mode s) :terminator)
           (not (member-eq :journal (strip-cars (cadr (fn-csp-next s))))))
  :hints (("Goal"
           :in-theory (e/d (fn-csp-next)
                           (fn-csp-record-done fn-csp-batch-finish fn-csp-fail
                            fn-csp-read-replay fn-csp-write fn-csp-try-offer
                            fn-csp-after-header fn-csp-hash-effect
                            fn-csp-header-window fn-csp-framer-window
                            fn-pull-list fn-csp-record-done-journal-idle))
           :use ((:instance fn-csp-record-done-journal-idle
                  (s (fn-csp-with s :conns
                       (fn-csp-conns-set (fn-csp-conns s) (nfix (fn-csp-slot s))
                                         (cons (fn-csp-msgid s) :verdict)))))
                 (:instance fn-csp-conns-set-consp-not-idle
                  (j (nfix (fn-csp-slot s))) (c (cons (fn-csp-msgid s) :verdict))
                  (conns (fn-csp-conns s))))))))
(local (defthm fn-csp-next-jok
  (implies (equal at-end (fn-csp-at-end s))
           (fn-csp-jok at-end (fn-csp-next s)))
  :hints (("Goal" :in-theory (e/d (fn-csp-next)
                                  (fn-csp-fail fn-csp-write fn-csp-after-header
                                   fn-csp-read-replay fn-csp-hash-effect fn-csp-header-window
                                   fn-csp-framer-window fn-csp-framer-window-accounts-for-every-octet
                                   fn-csp-record-done fn-csp-try-offer fn-csp-session-with-round
                                   fn-csp-terminator-no-journal fn-csp-at-end nfix))
                  :use fn-csp-terminator-no-journal))))

(local (defthm fn-csp-obs-effect-no-journal
  (not (member-eq :journal (strip-cars (fn-cu-obs-effect kind fc security round))))
  :hints (("Goal" :in-theory (enable fn-cu-obs-effect fn-pull-tls-effect)))))

(local (defthm fn-csp-obs-effects-no-journal
  (not (member-eq :journal (strip-cars (fn-cu-obs-effects obs fc security round))))
  :hints (("Goal" :induct (fn-cu-obs-effects obs fc security round)
                  :in-theory (e/d (fn-cu-obs-effects) (fn-cu-obs-effect))))))

(local (defthm fn-csp-cu-fail-no-journal
  (not (member-eq :journal (strip-cars (mv-nth 1 (fn-cu-fail r reason)))))
  :hints (("Goal" :in-theory (enable fn-cu-fail)))))

(local (defthm fn-csp-member-append-no-journal
  (iff (member-eq :journal (append a b))
       (or (member-eq :journal a) (member-eq :journal b)))))

(local (defthm fn-csp-session-step-pair-no-journal
  (not (member-eq :journal (strip-cars (cadr (fn-cu-session-step-pair s event)))))
  :hints (("Goal" :in-theory (e/d (fn-cu-session-step-pair fn-cu-session-step)
                                  (fn-cu-session-fc-events fn-fc-drive fn-fc-drive-state
                                   fn-pull-pre-okp fn-cu-obs-effects fn-cu-fail
                                   fn-cu-session-readyp fn-cu-done-p))))))

(local (defthm fn-csp-step-jok
  (implies (and (fn-csp-drain-inv s) (equal at-end (fn-csp-at-end s)))
           (fn-csp-jok at-end (fn-csp-step s event)))
  :hints (("Goal" :in-theory (e/d (fn-csp-step)
                                  (fn-csp-fail fn-csp-next fn-csp-local fn-csp-local-window
                                   fn-cu-session-step-pair fn-cu-session-readyp
                                   fn-blake3-stobj fn-cu-chainp fn-pull-event-octets
                                   fn-csp-session fn-csp-session-with-round fn-csp-drain-inv
                                   fn-csp-at-end nfix))))))

(defthm fn-csp-journals-only-a-settled-batch
  ; KEYSTONE (PRF-1335/1336, safety).  A :journal effect of fn-csp-step is
  ; emitted only when the batch is settled.  From a state of the drain
  ; invariant (fn-csp-drain-inv: the controller enters :drain only with the
  ; replay cursor at the batch's end, and while it drains neither moves; it
  ; holds at the begin and is kept by every step), if a step's effects hold a
  ; :journal then
  ;   - the spool cursor stood at the batch end (offset <= replay);
  ;   - the journal is the one leading effect and the only one, naming the
  ;     cursor of the round the step produced;
  ;   - the step finished the batch (the mode is :done or :status) and every
  ;     connection of its window is settled -- none holds a (msgid . phase)
  ;     binding, so no verdict is outstanding.
  ; The window's settling reply that frees the last binding is itself such a
  ; step (fn-csp-step-final-verdict-journals); so is the record-done after the
  ; last record, and no other event or mode journals.
  (implies (and (fn-csp-drain-inv s)
                (member-eq :journal (strip-cars (cadr (fn-csp-step s event)))))
           (let* ((pair (fn-csp-step s event))
                  (effs (cadr pair))
                  (s2 (car pair)))
             (and (<= (nfix (fn-csp-offset s)) (nfix (fn-csp-replay s)))
                  (consp effs)
                  (eq (car (car effs)) :journal)
                  (equal (cdr (car effs))
                         (fn-cu-round-cursor (fn-cu-s-round (fn-csp-session s2))))
                  (not (member-eq :journal (strip-cars (cdr effs))))
                  (member-eq (fn-csp-mode s2) '(:done :status))
                  (fn-csp-conns-idlep (fn-csp-conns s2)))))
  :hints (("Goal" :in-theory (e/d (fn-csp-jok fn-csp-at-end) (fn-csp-step fn-csp-step-jok))
                  :use (:instance fn-csp-step-jok (at-end (fn-csp-at-end s))))))

;; -----------------------------------------------------------------------------
;; K4: at most one connection streams (PRF-1335/1336).  The streaming
;; invariant: the number of :streaming bindings is at most one, zero outside
;; the modes that fill a record's body, zero for a skipped record.

(defun fn-csp-stream-inv-of (mode skip conns)
  ; At most one connection streams its record's body to the local node, and
  ; it does so only while the controller fills that record: from the 335
  ; (:offer to a body mode) to the terminator, which turns the binding into
  ; (msgid . :verdict).  A 435 record's skipped body streams nowhere.
  (declare (xargs :guard t))
  (let ((n (fn-csp-conns-phase-count conns :streaming)))
    (and (<= n 1)
         (implies (not (member-eq mode '(:local-write :terminator :replay-body)))
                  (equal n 0))
         (implies (and (eq mode :replay-body) skip) (equal n 0)))))

(defun fn-csp-stream-inv (s)
  (declare (xargs :guard t))
  (fn-csp-stream-inv-of (fn-csp-mode s) (fn-csp-skip s) (fn-csp-conns s)))

(local (defthm fn-csp-stream-inv-of-state
  (equal (fn-csp-stream-inv (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19))
         (fn-csp-stream-inv-of a0 a16 a18))
  :hints (("Goal" :in-theory (enable fn-csp-stream-inv fn-csp-mode fn-csp-skip fn-csp-conns)))))

(local (defthm fn-csp-stream-inv-of-symbol
  (implies (syntaxp (symbolp s))
           (equal (fn-csp-stream-inv s)
                  (fn-csp-stream-inv-of (fn-pull-at 0 s) (fn-pull-at 16 s) (fn-pull-at 18 s))))
  :hints (("Goal" :in-theory (enable fn-csp-stream-inv fn-csp-mode fn-csp-skip fn-csp-conns)))))

(local (in-theory (disable fn-csp-stream-inv)))

(local (defun fn-csp-ph-is (c ph) (if (and (consp c) (eq (cdr c) ph)) 1 0)))

(local (defthm fn-csp-phase-count-of-conns-set
  ; One binding replaced: the count loses the old entry's phase and gains the
  ; new one's.
  (equal (fn-csp-conns-phase-count (fn-csp-conns-set conns j c) ph)
         (+ (fn-csp-conns-phase-count conns ph)
            (fn-csp-ph-is c ph)
            (- (fn-csp-ph-is (fn-pull-at (nfix j) conns) ph))))
  :hints (("Goal" :in-theory (enable fn-csp-conns-set fn-csp-conns-phase-count fn-pull-at nfix)
                  :induct (fn-csp-conns-set conns j c)))))

(local (defthm fn-csp-phase-count-of-conns-of
  (implies (not (and (consp c) (eq (cdr c) ph)))
           (equal (fn-csp-conns-phase-count (fn-csp-conns-of n c) ph) 0))
  :hints (("Goal" :in-theory (enable fn-csp-conns-of fn-csp-conns-phase-count)))))

(local (defthm fn-csp-fail-keeps-stream-inv
  (fn-csp-stream-inv (car (fn-csp-fail s reason)))
  :hints (("Goal" :use fn-csp-fail-mode
           :in-theory (e/d (fn-csp-fail fn-csp-stream-inv-of-symbol)
                           (fn-csp-fail-mode fn-csp-stream-inv fn-csp-session-with-round))))))

(local (defthm fn-csp-ph-is-natp (natp (fn-csp-ph-is c ph)) :rule-classes (:rewrite :type-prescription)))

(local (defthm fn-csp-ph-is-of-cons
  (equal (fn-csp-ph-is (cons a b) ph) (if (eq b ph) 1 0))
  :hints (("Goal" :in-theory (enable fn-csp-ph-is)))))

(local (defthm fn-csp-ph-is-of-atom
  (implies (not (consp c)) (equal (fn-csp-ph-is c ph) 0))
  :hints (("Goal" :in-theory (enable fn-csp-ph-is)))))

(local (in-theory (disable fn-csp-ph-is)))

(local (defthm fn-csp-body-inv-of-local-write-no-skip
  (implies (fn-csp-body-inv-of :local-write skip resume msgid slot conns)
           (not skip))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-csp-body-inv-of)))))

(local (defun fn-csp-pk-ind (k conns)
  (declare (xargs :measure (nfix k)))
  (if (or (zp k) (atom conns)) conns (fn-csp-pk-ind (1- k) (cdr conns)))))

(local (defthm fn-csp-ph-is-at-most-count
  ; An entry of the table is part of the table's count.
  (<= (fn-csp-ph-is (fn-pull-at k conns) ph) (fn-csp-conns-phase-count conns ph))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-pull-at fn-csp-conns-phase-count fn-csp-ph-is)
                  :induct (fn-csp-pk-ind k conns)))))

(local (defthm fn-csp-stream-inv-of-resume
  ; A spool write in flight streams nothing, so the mode it resumes (:hash or
  ; :body, outside the streaming modes) is in order over the same table.
  (implies (and (fn-csp-stream-inv-of :write skip conns)
                (member-eq resume '(:hash :body)))
           (fn-csp-stream-inv-of resume skip conns))
  :hints (("Goal" :in-theory (enable fn-csp-stream-inv-of)))))

(local (defthm fn-csp-stream-inv-of-quiet-move
  ; Between two modes that stream nothing the invariant is the table's alone.
  (implies (and (fn-csp-stream-inv-of mode skip conns)
                (not (member-eq mode '(:local-write :terminator :replay-body)))
                (not (member-eq mode2 '(:local-write :terminator :replay-body))))
           (fn-csp-stream-inv-of mode2 skip conns))
  :hints (("Goal" :in-theory (enable fn-csp-stream-inv-of)))))

(local (defthm fn-csp-stream-inv-of-small
  ; With no streaming connection every mode is in order.
  (implies (<= (fn-csp-conns-phase-count conns :streaming) 0)
           (fn-csp-stream-inv-of mode skip conns))))

(local (defthm fn-csp-stream-inv-of-mono
  ; The same mode and skip over conns that stream no more.
  (implies (and (fn-csp-stream-inv-of mode skip conns)
                (<= (fn-csp-conns-phase-count conns2 :streaming)
                    (fn-csp-conns-phase-count conns :streaming)))
           (fn-csp-stream-inv-of mode skip conns2))))

(local (defthm fn-csp-phase-count-natp
  (natp (fn-csp-conns-phase-count conns ph))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable fn-csp-conns-phase-count)))))

(local (defthm fn-csp-idlep-no-streaming
  (implies (fn-csp-conns-idlep conns)
           (equal (fn-csp-conns-phase-count conns ph) 0))
  :hints (("Goal" :in-theory (enable fn-csp-conns-idlep fn-csp-conns-phase-count)))))

(local (defthm fn-csp-conns-set-no-streaming-mono
  ; Binding anything but a :streaming entry never raises the count.
  (implies (not (and (consp c) (eq (cdr c) :streaming)))
           (<= (fn-csp-conns-phase-count (fn-csp-conns-set conns j c) :streaming)
               (fn-csp-conns-phase-count conns :streaming)))
  :hints (("Goal" :in-theory (disable fn-csp-phase-count-of-conns-set)
                  :use fn-csp-phase-count-of-conns-set))))

(local (defthm fn-csp-stream-inv-small
  ; A state with no streaming connection satisfies the invariant.
  (implies (<= (fn-csp-conns-phase-count (fn-pull-at 18 x) :streaming) 0)
           (fn-csp-stream-inv x))
  :hints (("Goal" :in-theory (enable fn-csp-stream-inv fn-csp-conns)))))

(local (defthm fn-csp-batch-finish-keeps-stream-inv
  (implies (fn-csp-conns-idlep (fn-pull-at 18 s))
           (fn-csp-stream-inv (car (fn-csp-batch-finish s))))
  :hints (("Goal" :in-theory (disable fn-csp-batch-finish fn-csp-stream-inv fn-csp-idlep-no-streaming)
                  :use ((:instance fn-csp-batch-finish-conns (s s))
                        (:instance fn-csp-idlep-no-streaming (conns (fn-pull-at 18 s)) (ph :streaming)))))))

(local (defthm fn-csp-record-done-keeps-stream-inv
  (implies (equal (fn-csp-conns-phase-count (fn-pull-at 18 s) :streaming) 0)
           (fn-csp-stream-inv (car (fn-csp-record-done s))))
  :hints (("Goal" :in-theory (disable fn-csp-record-done fn-csp-stream-inv)
                  :use (:instance fn-csp-record-done-conns (s s))))))

(local (defthm fn-csp-write-keeps-stream-inv
  (implies (equal (fn-csp-conns-phase-count (fn-pull-at 18 s) :streaming) 0)
           (fn-csp-stream-inv (car (fn-csp-write s emission resume))))
  :hints (("Goal" :in-theory (e/d (fn-csp-write) (fn-csp-fail fn-csp-stream-inv))
                  :use fn-csp-fail-keeps-stream-inv))))

(local (defthm fn-csp-try-offer-keeps-stream-inv
  (implies (equal (fn-csp-conns-phase-count (fn-pull-at 18 s) :streaming) 0)
           (fn-csp-stream-inv (car (fn-csp-try-offer s))))
  :hints (("Goal" :in-theory (e/d (fn-csp-try-offer fn-csp-conns) (fn-csp-stream-inv fn-csp-stream-inv-of))))))

(local (defthm fn-csp-hash-effect-keeps-stream-inv
  (implies (fn-csp-stream-inv s) (fn-csp-stream-inv (car (fn-csp-hash-effect s))))
  :hints (("Goal" :in-theory (enable fn-csp-hash-effect)))))

(local (defthm fn-csp-read-replay-keeps-stream-inv
  (implies (fn-csp-stream-inv s) (fn-csp-stream-inv (car (fn-csp-read-replay s))))
  :hints (("Goal" :in-theory (e/d (fn-csp-read-replay fn-csp-stream-inv-of-symbol)
                                  (fn-csp-record-done fn-csp-fail fn-csp-stream-inv))
                  :use (fn-csp-record-done-keeps-stream-inv
                        (:instance fn-csp-fail-keeps-stream-inv (reason :short-spool)))))))

(local (defthm fn-csp-after-header-keeps-stream-inv
  (implies (equal (fn-csp-conns-phase-count (fn-pull-at 18 s) :streaming) 0)
           (fn-csp-stream-inv (car (fn-csp-after-header s line rest used))))
  :hints (("Goal" :in-theory (e/d (fn-csp-after-header fn-csp-stream-inv-of-symbol)
                                  (fn-csp-fail fn-csp-write fn-csp-try-offer fn-csp-stream-inv
                                   fn-csp-stream-inv-of binary-append fn-csp-session-with-round
                                   fn-cu-parse-status fn-cu-parse-header fn-cu-batch-end
                                   fn-cu-batch-next fn-cu-batch-morep fn-cu-batch-claim
                                   fn-cu-u64-hex fn-record-string-octets
                                   fn-cu-hex fn-cu-unhex fn-cu-u64-octets-aux fn-cu-words-aux))
                  :use (fn-csp-fail-keeps-stream-inv)))))

(local (defthm fn-csp-local-window-keeps-stream-inv
  (implies (and (fn-csp-body-inv s) (fn-csp-stream-inv s))
           (fn-csp-stream-inv (car (fn-csp-local-window s j))))
  :hints (("Goal" :in-theory (e/d (fn-csp-local-window fn-csp-conn fn-csp-body-inv-of-symbol fn-csp-stream-inv-of-symbol)
                                  (fn-csp-fail fn-csp-body-inv fn-csp-stream-inv fn-csp-body-inv-of))
                  :use (:instance fn-csp-fail-keeps-stream-inv (reason :local-refused))))))

(local (defthm fn-csp-local-opened-keeps-stream-inv
  (implies (and (fn-csp-stream-inv s) (equal conns (fn-pull-at 18 s)))
           (fn-csp-stream-inv (car (fn-csp-local-opened s j code conns))))
  :hints (("Goal" :in-theory (e/d (fn-csp-local-opened fn-csp-stream-inv-of-symbol)
                                  (fn-csp-fail fn-csp-stream-inv nfix))
                  :use (:instance fn-csp-fail-keeps-stream-inv (reason :local-refused))))))

(local (defthm fn-csp-local-verdict-keeps-stream-inv
  (implies (and (fn-csp-stream-inv s) (equal conns (fn-pull-at 18 s)))
           (fn-csp-stream-inv (car (fn-csp-local-verdict s j code conns round))))
  :hints (("Goal" :in-theory (e/d (fn-csp-local-verdict fn-csp-stream-inv-of-symbol)
                                  (fn-csp-fail fn-csp-stream-inv fn-csp-batch-finish
                                   fn-csp-session-with-round fn-cu-count nfix))
                  :use ((:instance fn-csp-fail-keeps-stream-inv (reason :local-refused))
                        (:instance fn-csp-fail-keeps-stream-inv (reason :local-deferred)))))))

(local (defthm fn-csp-local-await335-keeps-stream-inv
  (implies (and (fn-csp-body-inv s) (fn-csp-stream-inv s)
                (equal conns (fn-pull-at 18 s))
                (equal c (fn-pull-at (nfix j) conns))
                (consp c) (eq (cdr c) :await335)
                (eq (fn-csp-mode s) :offer) (equal (fn-csp-slot s) (nfix j)))
           (fn-csp-stream-inv (car (fn-csp-local-await335 s j code c conns round))))
  :hints (("Goal" :in-theory (e/d (fn-csp-local-await335 fn-csp-stream-inv-of-symbol fn-csp-body-inv-of-symbol
                                   fn-csp-conns)
                                  (fn-csp-fail fn-csp-stream-inv fn-csp-body-inv fn-csp-record-done
                                   fn-csp-session-with-round fn-cu-count nfix))
                  :use ((:instance fn-csp-fail-keeps-stream-inv (reason :local-refused))
                        (:instance fn-csp-fail-keeps-stream-inv (reason :local-deferred))
                        (:instance fn-csp-record-done-keeps-stream-inv
                          (s (fn-csp-with (fn-csp-session-with-round
                                            s (fn-cu-with round :counts
                                                          (fn-cu-count (fn-cu-r-counts round) 1)))
                                          :conns (fn-csp-conns-set conns j :free) :slot nil))))))))

(local (defthm fn-csp-with-session-keeps-stream-inv
  (implies (fn-csp-stream-inv s)
           (fn-csp-stream-inv (fn-csp-with s :session x)))
  :hints (("Goal" :in-theory (e/d (fn-csp-stream-inv-of-symbol) (fn-csp-stream-inv))))))

(local (defthm fn-csp-local-keeps-stream-inv
  (implies (and (fn-csp-body-inv s) (fn-csp-stream-inv s))
           (fn-csp-stream-inv (car (fn-csp-local s j octets))))
  :hints (("Goal" :in-theory (e/d (fn-csp-local fn-csp-conn)
                                  (fn-csp-fail fn-csp-local-opened fn-csp-local-await335
                                   fn-csp-local-verdict fn-csp-stream-inv fn-csp-body-inv nfix))
                  :use ((:instance fn-csp-fail-keeps-stream-inv (reason :local-refused))
                        (:instance fn-csp-local-opened-keeps-stream-inv
                          (code (fn-pull-local-code octets)) (conns (fn-csp-conns s)))
                        (:instance fn-csp-local-await335-keeps-stream-inv
                          (code (fn-pull-local-code octets)) (conns (fn-csp-conns s))
                          (c (fn-csp-conn j s)) (round (fn-cu-s-round (fn-csp-session s))))
                        (:instance fn-csp-local-verdict-keeps-stream-inv
                          (code (fn-pull-local-code octets)) (conns (fn-csp-conns s))
                          (round (fn-cu-s-round (fn-csp-session s)))))))))

(local (defthm fn-csp-next-keeps-stream-inv
  (implies (and (fn-csp-body-inv s) (fn-csp-stream-inv s))
           (fn-csp-stream-inv (car (fn-csp-next s))))
  :hints (("Goal" :in-theory (e/d (fn-csp-next fn-csp-stream-inv-of-symbol fn-csp-body-inv-of-symbol)
                                  (fn-csp-fail fn-csp-write fn-csp-after-header
                                   fn-csp-read-replay fn-csp-hash-effect fn-csp-header-window
                                   fn-csp-framer-window fn-csp-framer-window-accounts-for-every-octet
                                   fn-csp-record-done fn-csp-try-offer fn-csp-session-with-round
                                   fn-csp-stream-inv fn-csp-body-inv fn-csp-body-inv-of nfix))))))

(defthm fn-csp-step-keeps-stream-inv
  ; The streaming invariant, preserved by every step event (given K1's body
  ; invariant).
  (implies (and (fn-csp-body-inv s) (fn-csp-stream-inv s))
           (fn-csp-stream-inv (car (fn-csp-step s event))))
  :hints (("Goal" :in-theory (e/d (fn-csp-step fn-csp-stream-inv-of-symbol fn-csp-body-inv-of-symbol)
                                  (fn-csp-fail fn-csp-next fn-csp-local fn-csp-local-window
                                   fn-cu-session-step-pair fn-cu-session-readyp
                                   fn-blake3-stobj fn-cu-chainp fn-pull-event-octets
                                   fn-csp-session fn-csp-session-with-round fn-csp-stream-inv fn-csp-stream-inv-of
                                   fn-csp-body-inv fn-csp-body-inv-of nfix)))))

(defthm fn-csp-begin-establishes-stream-inv
  (fn-csp-stream-inv (car (fn-csp-begin plan cursor credential limit window)))
  :hints (("Goal" :in-theory (e/d (fn-csp-begin fn-csp-stream-inv-of-symbol)
                                  (fn-csp-fail fn-csp-stream-inv fn-cu-session-begin-pair
                                   fn-cu-cursor-chain fn-csp-conns-of nfix)))))

(defthm fn-csp-at-most-one-streaming
  ; KEYSTONE (PRF-1335/1336, K1's companion).  At most one connection of the
  ; window streams a body to the local node, and it does so only while the
  ; controller fills that record: from the 335 reply (mode :offer to a body
  ; mode) until the terminator turns the binding into (msgid . :verdict).
  ; Outside the body modes -- and for a 435 record, whose body is skipped
  ; through the spool -- no connection streams.  The one filling record is
  ; what keeps the spool cursor sequential while up to W verdicts await.
  (implies (and (fn-csp-body-inv s) (fn-csp-stream-inv s))
           (let ((s2 (car (fn-csp-step s event))))
             (and (<= (fn-csp-conns-phase-count (fn-csp-conns s2) :streaming) 1)
                  (implies (not (member-eq (fn-csp-mode s2)
                                           '(:local-write :terminator :replay-body)))
                           (equal (fn-csp-conns-phase-count (fn-csp-conns s2) :streaming) 0))
                  (implies (and (eq (fn-csp-mode s2) :replay-body) (fn-csp-skip s2))
                           (equal (fn-csp-conns-phase-count (fn-csp-conns s2) :streaming) 0)))))
  :hints (("Goal" :use fn-csp-step-keeps-stream-inv
                  :in-theory (e/d (fn-csp-stream-inv fn-csp-conns fn-csp-mode fn-csp-skip)
                                  (fn-csp-step fn-csp-step-keeps-stream-inv)))))
