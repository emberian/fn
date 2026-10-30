;; The connection machine fn2-conn (layer D, quest D3; ROUND2 section B.2
;; row 1, its connection half: the listener is A's fn2-listener). The design,
;; with every arm's contract, is fn2/docs/d-machines-nntp.md section 4.2.
;; Declared through defmachine with every arm in the checked arm language
;; (none :unchecked); the decision table is conn-answer.lisp; the grammar is
;; nntp-grammar.lisp. Registration book: assembly-index includes it after
;; B's; its continuations are materialized by assembly-callbacks-d.lisp.
(in-package "ACL2")
(include-book "machines-a")
(include-book "profile")
(include-book "conn-answer")
(fn2-book-layer :d)

;; The run quantum, split statically (section 4.2): the framer examines at
;; most *fn2-conn-frame-bytes*; a framed line costs at most
;; *fn2-conn-answer-bytes* (re-read 512, status 512, fixed body 1,024); a
;; run that needs input compacts at most *fn2-conn-compact-bytes* and
;; receives at most *fn2-conn-receive-bytes*.
(defconst *fn2-conn-frame-bytes* 2048)
(defconst *fn2-conn-answer-bytes* (+ 512 512 *fn2-answer-body-bytes*))
(defconst *fn2-conn-compact-bytes* 1024)
(defconst *fn2-conn-receive-bytes* 1024)
(defconst *fn2-conn-send-bytes* 4096)
(defconst *fn2-conn-run-bytes* (+ *fn2-conn-frame-bytes* *fn2-conn-answer-bytes*))
(defconst *fn2-conn-input-bytes* (+ *fn2-conn-frame-bytes* *fn2-conn-compact-bytes* *fn2-conn-receive-bytes*))
(defconst *fn2-conn-range-min* 1024)
(assert-event (and (equal *fn2-conn-run-bytes* 4096) (equal *fn2-conn-input-bytes* 4096)
                   (<= (* 2 *fn2-nntp-line-cap*) *fn2-conn-range-min*)))

(defmachine fn2-conn
 :states (:free :greeting :command :article-input :reply :upgrading :closing :draining :retired)
 :fields ((cap-index :u32) (cap-nonce :u32)
          (rx-slot :link) (rx-gen :u60) (tx-slot :link) (tx-gen :u60)
          (start :u32) (pos :u32) (overflow :bool) (compacting :bool) (cursor :u32)
          (tx-off :u32) (after (:enum fn2-conn-after (:command :article-input :upgrading :closing)))
          (pending :u32) (borrows :u32) (mask :u8) (ordinal :u32) (access-ref :u32)
          (auth-pending (:enum fn2-conn-auth (:none :user :sasl :redeem)))
          (refused :bool) (stopped :bool) (next-free :link))
 :holds ((:greeting :connection-row :rx-range :tx-range) (:command :connection-row :rx-range :tx-range)
         (:article-input :connection-row :rx-range :tx-range) (:reply :connection-row :rx-range :tx-range)
         (:upgrading :connection-row :rx-range :tx-range) (:closing :connection-row :rx-range :tx-range)
         (:draining :connection-row :rx-range :tx-range))
 :budget (:bytes 4096 :steps 32 :descriptors 4)
 :capacity (fn2-profile-c profile)
 ;; The listener admits a connection into :greeting with its RX and TX
 ;; ranges reserved whole (A's generated fn2-machine-admit-fn2-conn).
 :admission (:phase :greeting :ranges (:rx-range :tx-range)
             :clear (start pos overflow compacting cursor tx-off pending borrows ordinal refused
                     auth-pending access-ref))
 :initial ((generation fn2-machine-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*)
           (rx-slot *fn2-none*) (tx-slot *fn2-none*) (next-free fn2-machine-initial-next-free))
 :observes ((:receive-result fn2-conn-observe-receive
             :cost (:steps *fn2-work-transition*) :writes () :from (:command) :next (:command :closing) :uses ())
            (:send-result fn2-conn-observe-send
             :cost (:steps *fn2-work-transition*) :writes (tx-off borrows) :from (:reply) :next (:reply :closing)
             :uses (fn2-machine-pool-borrows-read-code fn2-machine-pool-borrows fn2-machine-refuse-observation))
            (:borrow-released fn2-conn-observe-release
             :cost (:steps *fn2-work-transition*) :writes (borrows) :next ()
             :uses (fn2-machine-pool-borrows-read-code fn2-machine-pool-borrows fn2-machine-refuse-observation))
            (:close-result fn2-conn-observe-close
             :cost (:steps *fn2-work-transition*) :writes () :from (:closing) :next (:draining) :uses ()))
 :continuations
 ((:free fn2-conn-idle :cost (:steps (:cost fn2-machine-idle :steps)) :writes () :next (:free)
   :uses (fn2-machine-idle))
  (:greeting fn2-conn-greet :cost (:bytes 512 :steps *fn2-work-transition*)
   :writes (tx-off after mask) :tables (fn2-core-pool)
   :next (:greeting :reply) :uses (fn2-conn-run-greeting fn2-machine-refuse-phase))
  (:command fn2-conn-command
   :cost (:bytes (max (:cost fn2-conn-frame-run :bytes) (:cost fn2-conn-compact-run :bytes))
          :steps (max (:cost fn2-conn-frame-run :steps) (:cost fn2-conn-compact-run :steps))
          :descriptors (:cost fn2-conn-frame-run :descriptors))
   :writes (start pos overflow compacting cursor tx-off after auth-pending ordinal
            pending stopped wait-reason ready-prev ready-next)
   :tables (fn2-core-ops fn2-core-pool fn2-core-machines fn2-core-machine-tables)
   :next (:command :reply)
   :uses (fn2-conn-frame-run fn2-conn-compact-run))
  (:article-input fn2-conn-unreached :cost (:steps (:cost fn2-machine-refuse-phase :steps)) :writes ()
   :next (:article-input) :uses (fn2-machine-refuse-phase))
  (:reply fn2-conn-reply
   :cost (:bytes *fn2-conn-send-bytes* :steps (+ *fn2-work-mailbox* *fn2-work-mailbox*) :descriptors 1)
   :writes (tx-off borrows pending stopped wait-reason ready-prev ready-next)
   :tables (fn2-core-ops fn2-core-pool fn2-core-machines fn2-core-machine-tables)
   :next (:reply :command :closing)
   :uses (fn2-conn-fill fn2-issue-send fn2-core-reset fn2-machine-issue-result fn2-machine-refuse-phase))
  (:upgrading fn2-conn-unreached :cost (:steps (:cost fn2-machine-refuse-phase :steps)) :writes ()
   :next (:upgrading) :uses (fn2-machine-refuse-phase))
  (:closing fn2-conn-close :cost (:steps *fn2-work-transition* :descriptors 1)
   :writes (pending stopped wait-reason ready-prev ready-next)
   :tables (fn2-core-ops fn2-core-machines fn2-core-machine-tables)
   :next (:closing) :uses (fn2-issue-close fn2-machine-issue-result))
  (:draining fn2-conn-drain :cost (:steps (:cost fn2-conn-release :steps))
   :writes (generation rx-slot rx-gen tx-slot tx-gen cap-index cap-nonce start pos overflow compacting
            cursor tx-off ordinal auth-pending refused next-free wait-reason)
   :tables (fn2-core-pool fn2-core-machines)
   :next (:draining :free :retired) :uses (fn2-conn-release))
  (:retired fn2-conn-idle :cost (:steps (:cost fn2-machine-idle :steps)) :writes () :next (:retired)
   :uses (fn2-machine-idle))))

;; Declared costs of the connection's outside calls (section 4.2). Each is a
;; thin stobj-let wrapper over a pool-level function; none builds a list.
(defcost fn2-conn-frame :bytes *fn2-conn-frame-bytes* :tables (fn2-core-pool)
  :doc "Frame RX from the row's (start pos overflow): the grammar's framer under the frame quantum.")
(defcost fn2-conn-run-answer :bytes *fn2-conn-answer-bytes* :tables (fn2-core-pool)
  :doc "Parse one framed line and answer it into TX (conn-answer.lisp); reads the clock mailbox.")
(defcost fn2-conn-run-overflow :bytes 512 :tables (fn2-core-pool)
  :doc "Render the overflow refusal into TX.")
(defcost fn2-conn-run-greeting :bytes 512 :tables (fn2-core-pool)
  :doc "Render the greeting, or the capacity 400, into TX.")
(defcost fn2-conn-fill :doc "A held pool slot's fill.")
(defcost fn2-conn-cap :doc "A held pool slot's capacity.")

;; ------------------------------------------------------------------------
;; The operations and continuations, materialized after the core instance
;; (assembly-callbacks-d.lisp). The row's owner triple for every pool access
;; is (*fn2-conn-kind* id generation).
(defmacro fn2-conn-events ()
 '(progn
(defun fn2-conn-frame (slot gen start pos overflow id owner-gen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (status s p o)
    (fn2-gram-frame *fn2-conn-frame-bytes* (nfix start) (max (nfix start) (nfix pos)) (if (equal overflow 1) 1 0)
                    *fn2-nntp-line-cap* slot gen *fn2-conn-kind* id owner-gen fn2-pool)
    (mv status s p o)))

;; A held slot's fill, and its capacity (0 for a slot outside the pool).
(defun fn2-conn-fill (slot fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (n) (if (and (natp slot) (< slot (fn2-pool-rows fn2-pool))) (nfix (fn2-pool-fill slot fn2-pool)) 0)
    (nfix n)))
(defun fn2-conn-cap (slot fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (n) (if (and (natp slot) (< slot (fn2-pool-rows fn2-pool))) (nfix (fn2-pool-cap slot fn2-pool)) 0)
    (nfix n)))

(defun fn2-conn-clock (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (seen flags real)
    (mv (equal (fn2-ops-clock-seen fn2-ops) 1) (fn2-ops-clock-flags fn2-ops) (fn2-ops-clock-real fn2-ops))
    (mv seen flags real)))

(defun fn2-conn-auth-keyword (code)
  (declare (xargs :guard t))
  (cond ((equal code *fn2-conn-auth-user*) :user) ((equal code *fn2-conn-auth-sasl*) :sasl)
        ((equal code *fn2-conn-auth-redeem*) :redeem) (t :none)))
(defun fn2-conn-auth-code (pending)
  (declare (xargs :guard t))
  (case pending (:user *fn2-conn-auth-user*) (:sasl *fn2-conn-auth-sasl*)
    (:redeem *fn2-conn-auth-redeem*) (otherwise *fn2-conn-auth-none*)))
(defun fn2-conn-after-code (after)
  (declare (xargs :guard t))
  (if (eq after :closing) *fn2-conn-after-closing* *fn2-conn-after-command*))

;; One framed line [s, e) answered into TX: (mv code after pending fn2-core),
;; AFTER and PENDING as the row's enum codes.
(defun fn2-conn-run-answer (s e mask pending rslot rgen tslot tgen id owner-gen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (mv-let (seen flags real) (fn2-conn-clock fn2-core)
    (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
      (code after next fn2-pool)
      (fn2-answer (nfix s) (nfix e) mask (fn2-conn-auth-keyword pending) seen flags real
                       rslot rgen tslot tgen *fn2-conn-kind* id owner-gen fn2-pool)
      (mv code (fn2-conn-after-code after) (fn2-conn-auth-code next) fn2-core))))
(fn2-core-preserves fn2-conn-run-answer (s e mask pending rslot rgen tslot tgen id owner-gen fn2-core) :position 3 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))

(defun fn2-conn-run-greeting (refused mask tslot tgen id owner-gen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (code after fn2-pool)
    (fn2-answer-greeting (equal refused 1) mask tslot tgen *fn2-conn-kind* id owner-gen fn2-pool)
    (mv code (fn2-conn-after-code after) fn2-core)))
(fn2-core-preserves fn2-conn-run-greeting (refused mask tslot tgen id owner-gen fn2-core) :position 2 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))

(defun fn2-conn-run-overflow (mask tslot tgen id owner-gen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (code fn2-pool)
    (fn2-answer-overflow mask tslot tgen *fn2-conn-kind* id owner-gen fn2-pool)
    (mv code fn2-core)))
(fn2-core-preserves fn2-conn-run-overflow (mask tslot tgen id owner-gen fn2-core) :position 1 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
(in-theory (disable fn2-conn-frame fn2-conn-fill fn2-conn-cap fn2-conn-clock fn2-conn-run-answer
                    fn2-conn-run-greeting fn2-conn-run-overflow))

(defmachine-callback fn2-conn-idle fn2-conn (id budget) 4
  (fn2-machine-idle id fn2-core))
(defmachine-callback fn2-conn-unreached fn2-conn (id budget) 4
  (fn2-machine-refuse-phase id fn2-core))

;; :greeting renders the greeting (or the capacity 400) and moves to :reply.
(defmachine-callback fn2-conn-greet fn2-conn (id budget) 4
  (fn2-machine-with-work 512 *fn2-work-transition* 0
    (mv-let (code after fn2-core)
      (fn2-conn-run-greeting row-refused row-mask row-tx-slot row-tx-gen id row-generation fn2-core)
      (if (not (eq code :ok)) (fn2-machine-refuse-phase id fn2-core)
        ;; Every D3 connection is a reader and the anonymous principal
        ;; (section 4.4); E4's peer listener and E2's authentication set
        ;; the other bits.
        (let ((fn2-core (fn2-conn-put-core id (phase *fn2-conn-state-reply*) (tx-off 0) (after after)
                                           (mask (logior *fn2-nntp-state-reader* *fn2-nntp-state-anonymous*)))))
          (fn2-machine-result 512 *fn2-work-transition* 0 t fn2-core))))))

;; Need-more: every filled octet is examined. All consumed: reset RX. Full
;; with a retained partial line: compact (next run). Else Receive at fill.
(defmachine-callback fn2-conn-input fn2-conn (id budget) 4
  :contract (:cost (:bytes (+ *fn2-conn-frame-bytes* (max *fn2-conn-receive-bytes* (:cost fn2-conn-run-overflow :bytes)))
                    :steps (max *fn2-work-mailbox* (:cost fn2-machine-issue-result :steps)) :descriptors 1)
             :writes (start pos compacting cursor tx-off after pending stopped wait-reason ready-prev ready-next)
             :tables (fn2-core-ops fn2-core-pool fn2-core-machines fn2-core-machine-tables)
             :next (:command :reply)
             :uses (fn2-conn-fill fn2-conn-cap fn2-core-reset fn2-issue-receive fn2-machine-issue-result fn2-conn-run-overflow
                    fn2-machine-refuse-phase))
  (let ((nfill (fn2-conn-fill row-rx-slot fn2-core)) (cap (fn2-conn-cap row-rx-slot fn2-core)))
    (cond ((and (equal row-start nfill) (< 0 nfill))
           (mv-let (code fn2-core) (fn2-core-reset row-rx-slot row-rx-gen *fn2-conn-kind* id row-generation fn2-core)
             (if (not (eq code :ok)) (fn2-machine-refuse-phase id fn2-core)
               (let ((fn2-core (fn2-conn-put-core id (start 0) (pos 0))))
                 (fn2-machine-result *fn2-conn-frame-bytes* *fn2-work-mailbox* 0 t fn2-core)))))
          ((and (<= cap nfill) (< 0 row-start))
           (let ((fn2-core (fn2-conn-put-core id (compacting 1) (cursor 0))))
             (fn2-machine-result *fn2-conn-frame-bytes* *fn2-work-mailbox* 0 t fn2-core)))
          ((<= cap nfill)
           ;; A slot smaller than the line cap is full with one unfinished line:
           ;; refuse it as overlong and close (a profile check keeps served
           ;; slots at least *fn2-conn-range-min*, so this is a small-profile edge).
           (mv-let (code fn2-core) (fn2-conn-run-overflow row-mask row-tx-slot row-tx-gen id row-generation fn2-core)
             (if (not (eq code :ok)) (fn2-machine-refuse-phase id fn2-core)
               (let ((fn2-core (fn2-conn-put-core id (phase *fn2-conn-state-reply*) (tx-off 0)
                                                  (after *fn2-conn-after-closing*))))
                 (fn2-machine-result *fn2-conn-frame-bytes* *fn2-work-mailbox* 0 t fn2-core)))))
          (t (let ((len (min *fn2-conn-receive-bytes* (- cap nfill))))
               (mv-let (code op opgen fn2-core)
                 (fn2-issue-receive row-cap-index row-cap-nonce row-rx-slot row-rx-gen len
                                    *fn2-conn-kind* id row-generation row-principal-slot fn2-core)
                 (declare (ignore op opgen))
                 (fn2-machine-issue-result id code (+ *fn2-conn-frame-bytes* len) fn2-core)))))))

;; Frame from the row's continuation; at a line, answer it and move to :reply.
(defmachine-callback fn2-conn-frame-run fn2-conn (id budget) 4
  :contract (:cost (:bytes *fn2-conn-run-bytes*
                    :steps (max *fn2-work-transition* (:cost fn2-conn-input :steps))
                    :descriptors (:cost fn2-conn-input :descriptors))
             :writes (start pos overflow compacting cursor tx-off after auth-pending ordinal
                      pending stopped wait-reason ready-prev ready-next)
             :tables (fn2-core-ops fn2-core-pool fn2-core-machines fn2-core-machine-tables)
             :next (:command :reply)
             :uses (fn2-conn-frame fn2-conn-run-answer fn2-conn-run-overflow fn2-conn-input fn2-machine-refuse-phase))
  (fn2-machine-with-work *fn2-conn-run-bytes* *fn2-work-transition* 1
   (b* ((ordinal row-ordinal) (mask row-mask) (auth row-auth-pending)
        (rslot row-rx-slot) (rgen row-rx-gen) (tslot row-tx-slot) (tgen row-tx-gen) (gen row-generation)
        ((mv status s p o) (fn2-conn-frame rslot rgen row-start row-pos row-overflow id gen fn2-core)))
     (cond ((eq status :line)
            (mv-let (code after next fn2-core)
              (fn2-conn-run-answer s p mask auth rslot rgen tslot tgen id gen fn2-core)
              (if (not (eq code :ok)) (fn2-machine-refuse-phase id fn2-core)
                (let ((fn2-core (fn2-conn-put-core id (phase *fn2-conn-state-reply*) (start p) (pos p) (overflow 0)
                                                   (tx-off 0) (after after) (auth-pending next)
                                                   (ordinal (+ 1 ordinal)))))
                  (fn2-machine-result *fn2-conn-run-bytes* *fn2-work-transition* 0 t fn2-core)))))
           ((or (eq status :overflow) (eq status :long-line))
            (mv-let (code fn2-core) (fn2-conn-run-overflow mask tslot tgen id gen fn2-core)
              (if (not (eq code :ok)) (fn2-machine-refuse-phase id fn2-core)
                (let ((fn2-core (fn2-conn-put-core id (phase *fn2-conn-state-reply*) (start s) (pos p) (overflow o)
                                                   (tx-off 0) (after *fn2-conn-after-closing*))))
                  (fn2-machine-result *fn2-conn-run-bytes* *fn2-work-transition* 0 t fn2-core)))))
           ((eq status :budget)
            (let ((fn2-core (fn2-conn-put-core id (start s) (pos p) (overflow o))))
              (fn2-machine-result *fn2-conn-frame-bytes* *fn2-work-transition* 0 t fn2-core)))
           ((eq status :need-more)
            (let ((fn2-core (fn2-conn-put-core id (start s) (pos p) (overflow o))))
              (fn2-call fn2-conn-input id budget)))
           (t (fn2-machine-refuse-phase id fn2-core))))))

;; Move a retained partial line to the front of RX (R6a1's drop-prefix, a
;; bounded continuation over the row's cursor).
(defmachine-callback fn2-conn-compact-run fn2-conn (id budget) 4
  :contract (:cost (:bytes *fn2-conn-compact-bytes* :steps *fn2-work-transition*)
             :writes (start pos compacting cursor) :tables (fn2-core-pool) :next (:command)
             :uses (fn2-core-drop-prefix fn2-machine-refuse-phase))
  (fn2-machine-with-work *fn2-conn-compact-bytes* *fn2-work-transition* 0
    (mv-let (code cursor fn2-core)
      (fn2-core-drop-prefix row-rx-slot row-rx-gen row-start row-cursor *fn2-conn-compact-bytes*
                            *fn2-conn-kind* id row-generation fn2-core)
      (cond ((eq code :more)
             (let ((fn2-core (fn2-conn-put-core id (cursor cursor))))
               (fn2-machine-result *fn2-conn-compact-bytes* *fn2-work-transition* 0 t fn2-core)))
            ((eq code :ok)
             (let ((fn2-core (fn2-conn-put-core id (compacting 0) (cursor 0) (start 0) (pos cursor))))
               (fn2-machine-result *fn2-conn-compact-bytes* *fn2-work-transition* 0 t fn2-core)))
            (t (fn2-machine-refuse-phase id fn2-core))))))

(defmachine-callback fn2-conn-command fn2-conn (id budget) 4
  (cond ((not (equal row-pending 0)) (fn2-machine-result 0 *fn2-work-empty* 0 nil fn2-core))
        ((equal row-compacting 1) (fn2-call fn2-conn-compact-run id budget))
        (t (fn2-call fn2-conn-frame-run id budget))))

;; :reply sends [tx-off, fill) of TX by loan; once sent and released, TX is
;; reset and the row moves to its AFTER phase.
(defmachine-callback fn2-conn-reply fn2-conn (id budget) 4
  (cond ((not (equal row-pending 0)) (fn2-machine-result 0 *fn2-work-empty* 0 nil fn2-core))
        ((not (equal row-borrows 0)) (fn2-machine-result 0 *fn2-work-poll* 0 nil fn2-core))
        (t (b* ((off row-tx-off) (after row-after) (tslot row-tx-slot) (tgen row-tx-gen)
                (nfill (fn2-conn-fill tslot fn2-core)))
             (if (< off nfill)
                 (let ((len (min *fn2-conn-send-bytes* (- nfill off))))
                   (mv-let (code op opgen fn2-core)
                     (fn2-issue-send row-cap-index row-cap-nonce tslot tgen off len 1
                                     *fn2-conn-kind* id row-generation row-principal-slot fn2-core)
                     (declare (ignore op opgen))
                     (let ((fn2-core (if (eq code :ok) (fn2-conn-put-core id (borrows 1)) fn2-core)))
                       (fn2-machine-issue-result id code len fn2-core))))
               (mv-let (code fn2-core) (fn2-core-reset tslot tgen *fn2-conn-kind* id row-generation fn2-core)
                 (if (not (eq code :ok)) (fn2-machine-refuse-phase id fn2-core)
                   (let ((fn2-core (fn2-conn-put-core id (tx-off 0)
                                     (phase (if (equal after *fn2-conn-after-closing*)
                                                *fn2-conn-state-closing* *fn2-conn-state-command*)))))
                     (fn2-machine-result 0 *fn2-work-mailbox* 0 t fn2-core)))))))))

(defmachine-callback fn2-conn-close fn2-conn (id budget) 4
  (fn2-machine-with-work 0 *fn2-work-transition* 1
  (cond ((not (equal row-pending 0)) (fn2-machine-result 0 *fn2-work-empty* 0 nil fn2-core))
        (t (mv-let (code op opgen fn2-core)
             (fn2-issue-close row-cap-index row-cap-nonce *fn2-conn-kind* id row-generation row-principal-slot fn2-core)
             (declare (ignore op opgen))
             (fn2-machine-issue-result id code 0 fn2-core))))))

;; :draining releases TX, then RX, then the row (the connection partition's
;; reclaim), once nothing is pending or lent.
(defmachine-callback fn2-conn-release fn2-conn (id budget) 4
  :contract (:cost (:steps *fn2-work-release*)
             :writes (generation rx-slot rx-gen tx-slot tx-gen cap-index cap-nonce start pos overflow compacting
                      cursor tx-off ordinal auth-pending refused next-free wait-reason)
             :tables (fn2-core-pool fn2-core-machines) :next (:free :retired)
             ;; One use entry per operation: the two calls release TX then RX
             ;; (D0's descending order), declared together.
             :uses ((fn2-core-release :effects ((:release (:tx-range :rx-range))))
                    fn2-machine-gen-limit fn2-machine-free-head fn2-machine-reclaim-fn2-conn fn2-core-stop))
  (b* ((kind *fn2-conn-kind*) (gen row-generation)
       ((mv tcode fn2-core) (fn2-core-release row-tx-slot row-tx-gen kind id gen fn2-core))
       ((mv rcode fn2-core) (fn2-core-release row-rx-slot row-rx-gen kind id gen fn2-core)))
    (if (not (and (or (eq tcode :ok) (eq tcode :retired)) (or (eq rcode :ok) (eq rcode :retired))))
        (let ((fn2-core (fn2-core-stop *fn2-stop-reason-pool-release* fn2-core)))
          (fn2-machine-result 0 *fn2-work-state* 0 nil fn2-core))
      (b* ((retire (>= gen (fn2-machine-gen-limit fn2-core)))
           (next (fn2-machine-free-head *fn2-conn-admission-ordinal* fn2-core))
           (fn2-core (fn2-conn-put-core id
                       (phase (if retire *fn2-conn-state-retired* *fn2-conn-state-free*))
                       (generation (if retire gen (+ 1 gen)))
                       (rx-slot *fn2-none*) (rx-gen 0) (tx-slot *fn2-none*) (tx-gen 0)
                       (cap-index 0) (cap-nonce 0) (start 0) (pos 0) (overflow 0) (compacting 0)
                       (cursor 0) (tx-off 0) (ordinal 0) (auth-pending *fn2-conn-auth-none*) (refused 0)
                       (next-free next) (wait-reason *fn2-wait-none*)))
           (fn2-core (fn2-machine-reclaim-fn2-conn id retire fn2-core)))
        (fn2-machine-result 0 *fn2-work-release* 0 nil fn2-core)))))

(defmachine-callback fn2-conn-drain fn2-conn (id budget) 4
  (cond ((not (equal row-pending 0)) (fn2-machine-result 0 *fn2-work-empty* 0 nil fn2-core))
        ((equal row-borrows 0) (fn2-call fn2-conn-release id budget))
        (t (fn2-machine-result 0 *fn2-work-poll* 0 nil fn2-core))))

;; Observations (the generic router decrements PENDING at a terminal).
(defmachine-callback fn2-conn-observe-receive fn2-conn (id event outcome reason count aux0 aux1) 1
  (if (and (or (equal outcome *fn2-outcome-done*) (equal outcome *fn2-outcome-short*))
           (natp count) (< 0 count))
      (mv id fn2-core)
    (let ((fn2-core (fn2-conn-put-core id (phase *fn2-conn-state-closing*))))
      (mv id fn2-core))))

(defmachine-callback fn2-conn-observe-send fn2-conn (id event outcome reason count aux0 aux1) 1
  (if (not (eq (fn2-machine-pool-borrows-read-code row-tx-slot fn2-core) :ok))
      (fn2-machine-refuse-observation fn2-core)
    (let* ((off row-tx-off)
           (fn2-core (fn2-conn-put-core id (borrows (fn2-machine-pool-borrows row-tx-slot fn2-core)))))
      (if (and (or (equal outcome *fn2-outcome-done*) (equal outcome *fn2-outcome-short*))
               (natp count) (< 0 count))
          (let ((fn2-core (fn2-conn-put-core id (tx-off (+ off count))))) (mv id fn2-core))
        (let ((fn2-core (fn2-conn-put-core id (phase *fn2-conn-state-closing*)))) (mv id fn2-core))))))

(defmachine-callback fn2-conn-observe-release fn2-conn (id event outcome reason count aux0 aux1) 1
  (if (not (eq (fn2-machine-pool-borrows-read-code row-tx-slot fn2-core) :ok))
      (fn2-machine-refuse-observation fn2-core)
    (let ((fn2-core (fn2-conn-put-core id (borrows (fn2-machine-pool-borrows row-tx-slot fn2-core)))))
      (mv id fn2-core))))

(defmachine-callback fn2-conn-observe-close fn2-conn (id event outcome reason count aux0 aux1) 1
  (let ((fn2-core (fn2-conn-put-core id (phase *fn2-conn-state-draining*)))) (mv id fn2-core)))

(defmachine-run fn2-conn)
))
