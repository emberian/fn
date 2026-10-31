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
(include-book "accounts-core")
(include-book "upload-scan")
(include-book "upload-feed")
(include-book "machine-arms") ; defmachine-registry (MACHINE-FORM 6.5 P4)
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
;; Article input (section 14.2): at most this many RX octets fed per run
;; (each read once and written at most once).
(defconst *fn2-conn-feed-bytes* 1024)
(defconst *fn2-conn-feed-cost* (* 2 *fn2-conn-feed-bytes*))
;; The feed's mode after the terminator (upload-feed.lisp uses 0..4).
(defconst *fn2-conn-feed-done* 5)
(assert-event (and (equal *fn2-conn-run-bytes* 4096) (equal *fn2-conn-input-bytes* 4096)
                   (<= (* 2 *fn2-nntp-line-cap*) *fn2-conn-range-min*)))

(defmachine fn2-conn
 :states (:free :greeting :command :article-input :reply :upgrading :closing :draining :retired :query)
 :fields ((cap-index :u32) (cap-nonce :u32)
          (rx-slot :link) (rx-gen :u60) (tx-slot :link) (tx-gen :u60)
          (start :u32) (pos :u32) (overflow :bool) (compacting :bool) (cursor :u32)
          (tx-off :u32) (after (:enum fn2-conn-after (:command :article-input :upgrading :closing :query)))
          (pending :u32) (borrows :u32) (mask :u8) (ordinal :u32) (access-ref :u32)
          (auth-pending (:enum fn2-conn-auth (:none :user :sasl :redeem)))
          (refused :bool) (stopped :bool) (next-free :link)
          ;; article input (D4, section 14.2): the upload this connection
          ;; feeds, the block's rule, the request it answers, the feed's
          ;; continuation, the outcome word posted back, the posting switch
          (upload :link) (upload-gen :u60) (rule (:enum fn2-conn-rule (:none :post :ihave :takethis)))
          (request :u32) (feed-mode :u8) (feed-discard :u8) (fed :u60) (word :u8) (outcome-ready :bool)
          (posting :bool)
          ;; the peer the Accept reported (A5r, a-pool-host-sim.md 4.1.1):
          ;; family (the listener's fn2-peer-family code), port, the address
          ;; in network order; read by the per-address and peer policy
          ;; (D5 3/n, D7 4/n), which lifts fn2-conn-reader-only-interim
          (peer-family :u8) (peer-port :u16) (peer-w0 :u32) (peer-w1 :u32) (peer-w2 :u32) (peer-w3 :u32)
          ;; reading (D6, section 15.3): the query cursor serving the line
          ;; [line-s, line-e), and the selection it reads (group, current
          ;; article, the view pinned at GROUP or LISTGROUP)
          (query :link) (query-gen :u60) (line-s :u32) (line-e :u32) (group :u60) (current :u60) (pin :u60))
 :holds ((:greeting :connection-row :rx-range :tx-range) (:command :connection-row :rx-range :tx-range)
         (:article-input :connection-row :rx-range :tx-range) (:reply :connection-row :rx-range :tx-range)
         (:upgrading :connection-row :rx-range :tx-range) (:closing :connection-row :rx-range :tx-range)
         (:draining :connection-row :rx-range :tx-range) (:query :connection-row :rx-range :tx-range))
 :budget (:bytes 4096 :steps 32 :descriptors 4)
 :capacity (fn2-profile-c profile)
 ;; The listener admits a connection into :greeting with its RX and TX
 ;; ranges reserved whole (A's generated fn2-machine-admit-fn2-conn).
 :admission (:phase :greeting :ranges (:rx-range :tx-range)
             :copy (principal-slot account-ref peer-family peer-port peer-w0 peer-w1 peer-w2 peer-w3)
             :clear (start pos overflow compacting cursor tx-off pending borrows ordinal refused
                     auth-pending access-ref upload-gen rule request feed-mode feed-discard fed word
                     outcome-ready posting query-gen line-s line-e group current pin))
 :initial ((generation fn2-machine-initial-generation) (ready-prev *fn2-none*) (ready-next *fn2-none*)
           (rx-slot *fn2-none*) (tx-slot *fn2-none*) (account-ref *fn2-none*) (next-free fn2-machine-initial-next-free)
           (upload *fn2-none*) (query *fn2-none*))
 :observes ((:receive-result fn2-conn-observe-receive
             :cost (:steps *fn2-work-transition*) :writes () :tables (fn2-core-accounts)
             :from (:command :article-input) :next (:command :article-input :closing)
             :uses (fn2-account-charge-core fn2-machine-refuse-observation))
            (:send-result fn2-conn-observe-send
             :cost (:steps *fn2-work-transition*) :writes (tx-off borrows) :tables (fn2-core-accounts)
             :from (:reply) :next (:reply :closing)
             :uses (fn2-machine-pool-borrows-read-code fn2-machine-pool-borrows fn2-account-charge-core
                    fn2-machine-refuse-observation))
            (:borrow-released fn2-conn-observe-release
             :cost (:steps *fn2-work-transition*) :writes (borrows) :next ()
             :uses (fn2-machine-pool-borrows-read-code fn2-machine-pool-borrows fn2-machine-refuse-observation))
            (:close-result fn2-conn-observe-close
             :cost (:steps *fn2-work-transition*) :writes () :from (:closing) :next (:draining) :uses ()))
 :continuations
 ((:free fn2-conn-idle :cost (:steps (:cost fn2-machine-idle :steps)) :writes () :next (:free)
   :uses (fn2-machine-idle))
  (:greeting fn2-conn-greet :cost (:bytes 512 :steps *fn2-work-transition*)
   :writes (tx-off after mask refused account-ref posting) :tables (fn2-core-pool fn2-core-accounts)
   :next (:greeting :reply)
   :uses (fn2-account-unbook-ref fn2-conn-posting-p fn2-conn-run-greeting fn2-machine-refuse-phase))
  (:command fn2-conn-command
   :cost (:bytes (max (:cost fn2-conn-frame-run :bytes) (:cost fn2-conn-compact-run :bytes)
                      (:cost fn2-conn-open-block :bytes))
          :steps (max (:cost fn2-conn-frame-run :steps) (:cost fn2-conn-compact-run :steps)
                      (:cost fn2-conn-open-block :steps))
          :descriptors (:cost fn2-conn-frame-run :descriptors))
   :writes (start pos overflow compacting cursor tx-off after auth-pending ordinal
            pending stopped wait-reason ready-prev ready-next rule request upload upload-gen
            feed-mode feed-discard fed word outcome-ready line-s line-e)
   :tables (fn2-core-ops fn2-core-pool fn2-core-machines fn2-core-machine-tables fn2-core-accounts fn2-upload-table)
   :next (:command :reply :query)
   :uses (fn2-conn-frame-run fn2-conn-compact-run fn2-conn-open-block))
  (:article-input fn2-conn-block
   :cost (:bytes (max (:cost fn2-conn-feed-step :bytes) (:cost fn2-conn-run-outcome :bytes))
          :steps (max (:cost fn2-conn-feed-step :steps) *fn2-work-transition*)
          :descriptors (:cost fn2-conn-feed-step :descriptors))
   :writes (start pos tx-off after upload upload-gen rule word outcome-ready feed-mode feed-discard fed
            pending stopped wait-reason ready-prev ready-next)
   :tables (fn2-core-ops fn2-core-pool fn2-core-machines fn2-core-machine-tables)
   :next (:article-input :reply)
   :uses (fn2-conn-feed-step fn2-conn-run-outcome fn2-machine-refuse-phase))
  (:reply fn2-conn-reply
   :cost (:bytes *fn2-conn-send-bytes* :steps (+ *fn2-work-mailbox* *fn2-work-mailbox*) :descriptors 1)
   :writes (tx-off borrows pending stopped wait-reason ready-prev ready-next)
   :tables (fn2-core-ops fn2-core-pool fn2-core-machines fn2-core-machine-tables)
   :next (:reply :command :article-input :closing :query)
   :uses (fn2-conn-fill fn2-issue-send fn2-core-reset fn2-machine-issue-result fn2-machine-refuse-phase))
  (:upgrading fn2-conn-unreached :cost (:steps (:cost fn2-machine-refuse-phase :steps)) :writes ()
   :next (:upgrading) :uses (fn2-machine-refuse-phase))
  (:closing fn2-conn-close :cost (:steps *fn2-work-transition* :descriptors 1)
   :writes (pending stopped wait-reason ready-prev ready-next)
   :tables (fn2-core-ops fn2-core-machines fn2-core-machine-tables)
   :next (:closing) :uses (fn2-issue-close fn2-machine-issue-result))
  (:draining fn2-conn-drain :cost (:steps (:cost fn2-conn-release :steps))
   :writes (generation rx-slot rx-gen tx-slot tx-gen cap-index cap-nonce start pos overflow compacting
            cursor tx-off ordinal auth-pending refused next-free wait-reason account-ref upload query query-gen)
   :tables (fn2-core-pool fn2-core-machines fn2-core-accounts fn2-cursor-table)
   :next (:draining :free :retired) :uses (fn2-conn-release))
  (:retired fn2-conn-idle :cost (:steps (:cost fn2-machine-idle :steps)) :writes () :next (:retired)
   :uses (fn2-machine-idle))
  (:query fn2-conn-serve-query :cost (:steps (max *fn2-work-transition* (:cost fn2-machine-take-fn2-cursor :steps)))
   :writes (query query-gen tx-off after group current pin wait-reason ready-prev ready-next)
   :tables (fn2-core-pool fn2-core-machines fn2-core-machine-tables fn2-cursor-table)
   :next (:query :reply :command)
   :uses (fn2-machine-take-fn2-cursor fn2-conn-query-state fn2-conn-cursor-roff fn2-conn-cursor-go
          fn2-conn-cursor-selection fn2-conn-wake fn2-machine-refuse-phase))))

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
(defcost fn2-conn-query-state :tables (fn2-cursor-table fn2-core-pool)
 :doc "Whose move the query cursor's page is: :busy (the cursor's), :page (a page in TX), :more, :done or :gone.")
(defcost fn2-conn-reading-p :doc "Whether the profile serves reading: the cursor partition has rows.")
(defcost fn2-conn-cursor-roff :tables (fn2-cursor-table) :doc "Where the cursor's page starts in TX.")
(defcost fn2-conn-cursor-go :tables (fn2-cursor-table) :doc "Give the query cursor its move (TX is empty).")
(defcost fn2-conn-cursor-cancel :tables (fn2-cursor-table) :doc "Cancel a waiting query cursor: the connection drains.")
(defcost fn2-conn-cursor-selection :tables (fn2-cursor-table)
 :doc "The selection the cursor's reply moves the connection to: (mv update group current pin).")
(defcost fn2-conn-posting-p :doc "Whether posting is served (the input configuration; section 14.5).")
(defcost fn2-conn-run-block-open :bytes 512 :tables (fn2-core-pool) :doc "Render a block's opening reply (340) into TX.")
(defcost fn2-conn-run-outcome :bytes 512 :tables (fn2-core-pool) :doc "Render a block's outcome reply into TX.")
(defcost fn2-conn-cap :doc "A held pool slot's capacity.")

;; ------------------------------------------------------------------------
;; The operations and continuations, materialized after the core instance
;; (assembly-callbacks-d.lisp). The row's owner triple for every pool access
;; is (*fn2-conn-kind* id generation).
(defmacro fn2-conn-op-events ()
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
  (case after (:closing *fn2-conn-after-closing*) (:article-input *fn2-conn-after-article-input*)
    (:query *fn2-conn-after-query*)
    (otherwise *fn2-conn-after-command*)))

;; One framed line [s, e) answered into TX: (mv code after pending fn2-core),
;; AFTER and PENDING as the row's enum codes.
(defun fn2-conn-run-answer (s e mask pending posting reading rslot rgen tslot tgen id owner-gen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (mv-let (seen flags real) (fn2-conn-clock fn2-core)
    (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
      (code after next fn2-pool)
      (fn2-answer (nfix s) (nfix e) mask (fn2-conn-auth-keyword pending) (equal posting 1) reading seen flags real
                       rslot rgen tslot tgen *fn2-conn-kind* id owner-gen fn2-pool)
      (mv code (fn2-conn-after-code after) (fn2-conn-auth-code next) fn2-core))))
(fn2-core-preserves fn2-conn-run-answer (s e mask pending posting reading rslot rgen tslot tgen id owner-gen fn2-core) :position 3 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))

(defun fn2-conn-run-greeting (refused posting mask tslot tgen id owner-gen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (code after fn2-pool)
    (fn2-answer-greeting (equal refused 1) (equal posting 1) mask tslot tgen *fn2-conn-kind* id owner-gen fn2-pool)
    (mv code (fn2-conn-after-code after) fn2-core)))
(fn2-core-preserves fn2-conn-run-greeting (refused posting mask tslot tgen id owner-gen fn2-core) :position 2 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))

(defun fn2-conn-run-overflow (mask tslot tgen id owner-gen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (code fn2-pool)
    (fn2-answer-overflow mask tslot tgen *fn2-conn-kind* id owner-gen fn2-pool)
    (mv code fn2-core)))
(fn2-core-preserves fn2-conn-run-overflow (mask tslot tgen id owner-gen fn2-core) :position 1 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
(defun fn2-conn-posting-p (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-input-config (fn2-core-input-config fn2-core)))
    (p) (and (fn2-input-config-wfp fn2-input-config) (natp (fn2-input-config-rows fn2-input-config))
             (< 0 (fn2-input-config-rows fn2-input-config)) (equal (fn2-input-config-posting 0 fn2-input-config) 1))
    (if p 1 0)))
(defun fn2-upload-gen-of (u fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (eq (fn2-upload-snapshot-read-code u fn2-core) :ok) (fn2-machine-generation u fn2-core) 0))
(defthm fn2-conn-posting-p-bit
  (bitp (fn2-conn-posting-p fn2-core))
  :rule-classes ((:type-prescription :typed-term (fn2-conn-posting-p fn2-core))
                 (:rewrite :corollary (unsigned-byte-p 1 (fn2-conn-posting-p fn2-core)))))
(defthm fn2-upload-gen-of-u60
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (unsigned-byte-p 60 (fn2-upload-gen-of u fn2-core))))
(defun fn2-conn-run-block-open (mask tslot tgen id owner-gen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (code fn2-pool)
    (fn2-answer-block-open mask tslot tgen *fn2-conn-kind* id owner-gen fn2-pool)
    (mv code fn2-core)))
(fn2-core-preserves fn2-conn-run-block-open (mask tslot tgen id owner-gen fn2-core) :position 1 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
(defun fn2-conn-run-outcome (word mask tslot tgen id owner-gen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (code after fn2-pool)
    (fn2-answer-outcome (fn2-upload-word-of (nfix word)) mask tslot tgen *fn2-conn-kind* id owner-gen fn2-pool)
    (mv code (fn2-conn-after-code after) fn2-core)))
(fn2-core-preserves fn2-conn-run-outcome (word mask tslot tgen id owner-gen fn2-core) :position 2 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
;; Feed [start, fill) of RX into the upload's current chunk (the first while
;; it has room), at most *fn2-conn-feed-bytes* octets and no further than one
;; octet past the article bound (so a too-large block is refused, never
;; buffered). FED is what this connection has written into the window so
;; far, WHY its discard reason (0 none, 1 framing, 2 too large). The upload
;; reads FED, WHY and the terminator from this row (no cross-row write).
;; Returns (mv status start mode why copied fn2-core).
;; The pool step alone (its own preservation facts; the readers around it
;; change nothing): (mv status start mode discard copied fn2-core).
(defun fn2-conn-feed-pool (left start mode discard rslot rgen id gen slot sgen u ugen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (status start2 mode2 discard2 copied fn2-pool)
    (fn2-upload-feed (max 1 (nfix left)) (nfix start) (nfix mode) discard rslot rgen *fn2-conn-kind* id gen
                     slot sgen *fn2-upload-kind* u ugen fn2-pool)
    (mv status start2 mode2 discard2 copied fn2-core)))
(fn2-core-preserves fn2-conn-feed-pool (left start mode discard rslot rgen id gen slot sgen u ugen fn2-core)
  :position 5 :rows nil :hints (("Goal" :in-theory (enable fn2-core-wfp))))
(in-theory (disable fn2-conn-feed-pool))
(defun fn2-conn-feed-run (start mode why fed rslot rgen id gen u ugen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  ;; UGEN is the generation the take gave: the upload cannot drain while this
  ;; row feeds it, so another generation is an invariant failure (:bounds)
  (b* (((unless (and (eq (fn2-upload-snapshot-read-code u fn2-core) :ok)
                     (equal (fn2-machine-generation u fn2-core) ugen)
                     (natp start) (natp mode) (natp fed) (natp why)))
        (mv :bounds 0 0 0 0 fn2-core))
       (c0 (fn2-upload-row-c0-slot u fn2-core)) (g0 (fn2-upload-row-c0-gen u fn2-core))
       (c1 (fn2-upload-row-c1-slot u fn2-core)) (g1 (fn2-upload-row-c1-gen u fn2-core))
       (cap0 (fn2-upload-chunk-cap c0 fn2-core)) (cap1 (fn2-upload-chunk-cap c1 fn2-core))
       (bound (fn2-upload-bound cap0 cap1 fn2-core))
       (in0 (< fed cap0))
       (discard (not (equal why 0)))
       (left (if discard *fn2-conn-feed-bytes* (min *fn2-conn-feed-bytes* (nfix (- (+ 1 bound) fed)))))
       ((mv status start2 mode2 discard2 copied fn2-core)
        (fn2-conn-feed-pool left start mode discard rslot rgen id gen (if in0 c0 c1) (if in0 g0 g1) u ugen fn2-core))
       (fed2 (+ fed (nfix copied)))
       ;; the second chunk full, or past the bound: too large
       (too-large (and (not discard2) (or (< bound fed2) (and (eq status :full) (not in0)))))
       (why2 (cond (discard why) (too-large 2) (discard2 1) (t 0))))
    ;; :full is never an end: chunk 0 full switches to chunk 1 next run; chunk
    ;; 1 full is too large (WHY2), drained from then on
    (mv (if (eq status :full) :budget status) start2 mode2 why2 (nfix copied) fn2-core)))
(fn2-core-preserves fn2-conn-feed-run (start mode why fed rslot rgen id gen u ugen fn2-core) :position 5 :rows nil)
(defun fn2-conn-wake (u fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (and (unsigned-byte-p 32 u) (not (equal u *fn2-none*))) (fn2-machine-set-wake-id u fn2-core) fn2-core))
(fn2-core-preserves fn2-conn-wake (u fn2-core) :rows nil)
(in-theory (disable fn2-conn-posting-p fn2-upload-gen-of fn2-conn-run-block-open fn2-conn-run-outcome fn2-conn-feed-run
                    fn2-conn-wake))
(in-theory (disable fn2-conn-frame fn2-conn-fill fn2-conn-cap fn2-conn-clock fn2-conn-run-answer
                    fn2-conn-run-greeting fn2-conn-run-overflow))

))

;; The connection's continuations (materialized after the helpers above, in
;; their own section book: assembly-callbacks-d-conn.lisp).
(defmacro fn2-conn-events ()
 '(progn
(defmachine-callback fn2-conn-idle fn2-conn (id budget) 4
  (fn2-machine-idle id fn2-core))
(defmachine-callback fn2-conn-unreached fn2-conn (id budget) 4
  (fn2-machine-refuse-phase id fn2-core))

;; :greeting renders the greeting (or the capacity 400) and moves to :reply.
;; The listener booked the connection on its principal at Accept issue and
;; the admission copied principal-slot and account-ref (D7 13.4, A's S1).
;; An unbooked row (the principal's entitlement was refused, :limit or
;; :shared) or one admitted into the partition's reserve row gets the
;; capacity 400; the latter releases its booking first, so a 400'd
;; connection holds none. Every other greeted row keeps account-ref.
(defmachine-callback fn2-conn-greet fn2-conn (id budget) 4
  (fn2-machine-with-work 512 *fn2-work-transition* 0
    (b* ((ref row-account-ref)
         (refused (if (and (not (equal ref *fn2-none*)) (equal row-refused 0)) 0 1))
         ((mv ucode fn2-core) (fn2-account-unbook-ref (if (equal refused 1) ref *fn2-none*) fn2-core)))
      (if (not (eq ucode :ok))
          (fn2-machine-refuse-phase id fn2-core)
        (b* ((posting (fn2-conn-posting-p fn2-core))
             ((mv code after fn2-core)
              (fn2-conn-run-greeting refused posting row-mask row-tx-slot row-tx-gen id row-generation fn2-core)))
          (if (not (eq code :ok)) (fn2-machine-refuse-phase id fn2-core)
            ;; Every D3 connection is a reader and the anonymous principal
            ;; (section 4.4); E4's peer listener and E2's authentication set
            ;; the other bits.
            (let ((fn2-core (fn2-conn-put-core id (phase *fn2-conn-state-reply*) (tx-off 0) (after after)
                                               (refused refused) (posting posting)
                                               (account-ref (if (equal refused 1) *fn2-none* ref))
                                               (mask (logior *fn2-nntp-state-reader* *fn2-nntp-state-anonymous*)))))
              (fn2-machine-result 512 *fn2-work-transition* 0 t fn2-core))))))))

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

))

;; The connection's continuations, second half (assembly-callbacks-d-conn2.lisp):
;; the framer, the article input, the reply, the close and the release.
(defmacro fn2-conn-events-2 ()
 '(progn
;; Reading is served when the cursor partition has rows (read rows, :reading).
(defun fn2-conn-reading-p (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (< 0 (nfix (fn2-machine-connection-count *fn2-cursor-admission-ordinal* fn2-core))))
;; The query cursor seen from its connection (section 15.3): X is live while
;; its generation is the one the take returned.
(defun fn2-conn-cursor-live-p (x xgen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (and (unsigned-byte-p 32 x) (not (equal x *fn2-none*))
       (eq (fn2-cursor-snapshot-read-code x fn2-core) :ok)
       (equal (fn2-machine-generation x fn2-core) xgen)))
(defun fn2-conn-query-state (x xgen tslot fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (cond ((not (fn2-conn-cursor-live-p x xgen fn2-core)) :gone)
        ((equal (fn2-cursor-row-turn x fn2-core) 1) :busy)
        ((< 0 (nfix (fn2-conn-fill tslot fn2-core))) :page)
        ((equal (fn2-cursor-row-done x fn2-core) 1) :done)
        (t :more)))
(defun fn2-conn-cursor-roff (x xgen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (fn2-conn-cursor-live-p x xgen fn2-core) (nfix (fn2-cursor-row-roff x fn2-core)) 0))
(defun fn2-conn-cursor-selection (x xgen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (fn2-conn-cursor-live-p x xgen fn2-core)
      (mv (nfix (fn2-cursor-row-update x fn2-core)) (nfix (fn2-cursor-row-sel x fn2-core))
          (nfix (fn2-cursor-row-ncurrent x fn2-core)) (nfix (fn2-cursor-row-spin x fn2-core)))
    (mv 0 0 0 0)))
(defun fn2-conn-cursor-go (x xgen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (fn2-conn-cursor-live-p x xgen fn2-core) (fn2-cursor-put-core x (turn 1)) fn2-core))
(fn2-core-preserves fn2-conn-cursor-go (x xgen fn2-core) :rows nil)
(defun fn2-conn-cursor-cancel (x xgen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (fn2-conn-cursor-live-p x xgen fn2-core) (fn2-cursor-put-core x (cancel 1) (turn 1)) fn2-core))
(fn2-core-preserves fn2-conn-cursor-cancel (x xgen fn2-core) :rows nil)
(in-theory (disable fn2-conn-cursor-live-p fn2-conn-query-state fn2-conn-cursor-roff fn2-conn-cursor-selection
                    fn2-conn-cursor-go fn2-conn-cursor-cancel))

;; :query (section 15.3). No cursor yet: take one for the line [line-s,
;; line-e) with this row's TX, selection and owner (the take wakes it), or
;; wait parked for a cursor row. Then, at each wake: a page in TX is sent
;; (:reply, back to :query); an empty TX after a page gives the cursor its
;; move again, or, once the cursor is done, copies its selection back and
;; returns to :command, the cursor woken to finish.
(defmachine-callback fn2-conn-serve-query fn2-conn (id budget) 4
  (fn2-machine-with-work 0 *fn2-work-transition* 0
   (if (equal row-query *fn2-none*)
       (b* (((mv tcode x xgen fn2-core)
             (fn2-machine-take-fn2-cursor id id row-generation *fn2-conn-kind* row-mask row-rx-slot row-rx-gen
                                          row-line-s row-line-e row-tx-slot row-tx-gen row-group row-current
                                          row-pin fn2-core)))
         (if (not (eq tcode :ok))
             ;; parked by the take: no work until the grant wakes this row
             (fn2-machine-result 0 *fn2-work-transition* 0 nil fn2-core)
           (let ((fn2-core (fn2-conn-put-core id (query x) (query-gen xgen))))
             (fn2-machine-result 0 *fn2-work-transition* 0 nil fn2-core))))
     (b* ((x row-query) (xgen row-query-gen))
       (case (fn2-conn-query-state x xgen row-tx-slot fn2-core)
         (:busy (fn2-machine-result 0 *fn2-work-transition* 0 nil fn2-core))
         (:page (let ((fn2-core (fn2-conn-put-core id (phase *fn2-conn-state-reply*)
                                                   (tx-off (fn2-conn-cursor-roff x xgen fn2-core))
                                                   (after *fn2-conn-after-query*))))
                  (fn2-machine-result 0 *fn2-work-transition* 0 t fn2-core)))
         (:more (let* ((fn2-core (fn2-conn-cursor-go x xgen fn2-core))
                       (fn2-core (fn2-conn-wake x fn2-core)))
                  (fn2-machine-result 0 *fn2-work-transition* 0 nil fn2-core)))
         (:done (b* (((mv upd g c v) (fn2-conn-cursor-selection x xgen fn2-core))
                     (fn2-core (fn2-conn-cursor-go x xgen fn2-core))
                     (fn2-core (fn2-conn-wake x fn2-core))
                     (sel (equal upd 2)) (cur (or sel (equal upd 1)))
                     (fn2-core (fn2-conn-put-core id (phase *fn2-conn-state-command*) (query *fn2-none*) (query-gen 0)
                                                  (group (if sel g row-group)) (current (if cur c row-current))
                                                  (pin (if sel v row-pin)))))
                  (fn2-machine-result 0 *fn2-work-transition* 0 t fn2-core)))
         ;; a cursor gone while named: the query invariant broke
         (otherwise (fn2-machine-refuse-phase id fn2-core)))))))
;; Frame from the row's continuation; at a line, answer it and move to :reply.
(defmachine-callback fn2-conn-frame-run fn2-conn (id budget) 4
  :contract (:cost (:bytes *fn2-conn-run-bytes*
                    :steps (max *fn2-work-transition* (:cost fn2-conn-input :steps))
                    :descriptors (:cost fn2-conn-input :descriptors))
             :writes (start pos overflow compacting cursor tx-off after auth-pending ordinal
                      pending stopped wait-reason ready-prev ready-next rule request line-s line-e)
             :tables (fn2-core-ops fn2-core-pool fn2-core-machines fn2-core-machine-tables fn2-core-accounts)
             :next (:command :reply :query)
             :uses (fn2-conn-frame fn2-conn-run-answer fn2-conn-run-overflow fn2-account-charge-core fn2-conn-input fn2-conn-reading-p
                    fn2-machine-refuse-phase))
  (fn2-machine-with-work *fn2-conn-run-bytes* *fn2-work-transition* 1
   (b* ((ordinal row-ordinal) (mask row-mask) (auth row-auth-pending)
        (rslot row-rx-slot) (rgen row-rx-gen) (tslot row-tx-slot) (tgen row-tx-gen) (gen row-generation)
        ((mv status s p o) (fn2-conn-frame rslot rgen row-start row-pos row-overflow id gen fn2-core)))
     (cond ((eq status :line)
            (b* (((mv ccode fn2-core)
                  (fn2-account-charge-core row-principal-slot *fn2-account-charge-requests* 1 fn2-core))
                 ((mv code after next fn2-core)
                  (fn2-conn-run-answer s p mask auth row-posting
                                       (fn2-conn-reading-p fn2-core)
                                       rslot rgen tslot tgen id gen fn2-core)))
              (cond ((not (and (eq code :ok) (eq ccode :ok))) (fn2-machine-refuse-phase id fn2-core))
                    ;; POST where posting is served: nothing rendered yet; the
                    ;; next run takes an upload and renders 340 (section 14.2)
                    ((equal after *fn2-conn-after-article-input*)
                     (let ((fn2-core (fn2-conn-put-core id (start p) (pos p) (overflow 0) (auth-pending next)
                                                        (rule *fn2-conn-rule-post*) (request ordinal)
                                                        (ordinal (+ 1 ordinal)))))
                       (fn2-machine-result *fn2-conn-run-bytes* *fn2-work-transition* 0 t fn2-core)))
                    ;; a reader command: nothing rendered; the next run takes a
                    ;; query cursor for the line [s, p) (section 15.3)
                    ((equal after *fn2-conn-after-query*)
                     (let ((fn2-core (fn2-conn-put-core id (phase *fn2-conn-state-query*) (start p) (pos p) (overflow 0)
                                                        (auth-pending next) (line-s s) (line-e p)
                                                        (request ordinal) (ordinal (+ 1 ordinal)))))
                       (fn2-machine-result *fn2-conn-run-bytes* *fn2-work-transition* 0 t fn2-core)))
                    (t (let ((fn2-core (fn2-conn-put-core id (phase *fn2-conn-state-reply*) (start p) (pos p) (overflow 0)
                                                          (tx-off 0) (after after) (auth-pending next)
                                                          (ordinal (+ 1 ordinal)))))
                         (fn2-machine-result *fn2-conn-run-bytes* *fn2-work-transition* 0 t fn2-core))))))
           ((or (eq status :overflow) (eq status :long-line))
            (b* (((mv ccode fn2-core)
                  (fn2-account-charge-core row-principal-slot *fn2-account-charge-requests* 1 fn2-core))
                 ((mv code fn2-core) (fn2-conn-run-overflow mask tslot tgen id gen fn2-core)))
              (if (not (and (eq code :ok) (eq ccode :ok))) (fn2-machine-refuse-phase id fn2-core)
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

;; A POST line was answered :article-input: take an upload row and its
;; window (A-S7) and render 340, or wait parked on the upload kind's FIFO
;; (the take parked this row) and try again when granted (section 14.2).
(defmachine-callback fn2-conn-open-block fn2-conn (id budget) 4
  :contract (:cost (:bytes (:cost fn2-conn-run-block-open :bytes) :steps *fn2-work-transition*)
             :writes (tx-off after upload upload-gen feed-mode feed-discard fed word outcome-ready rule)
             :tables (fn2-core-pool fn2-core-machines fn2-core-machine-tables fn2-upload-table)
             :next (:command :reply)
             :uses (fn2-machine-take-fn2-upload fn2-upload-gen-of fn2-conn-run-block-open fn2-machine-refuse-phase))
  (fn2-machine-with-work 512 *fn2-work-transition* 0
    (b* (((mv tcode u ugen fn2-core)
          (fn2-machine-take-fn2-upload id id row-generation row-request *fn2-upload-rule-post* row-principal-slot fn2-core)))
      (if (not (eq tcode :ok))
          ;; parked by the take: no work until the grant wakes this row
          (fn2-machine-result 0 *fn2-work-transition* 0 nil fn2-core)
        (b* (((mv code fn2-core) (fn2-conn-run-block-open row-mask row-tx-slot row-tx-gen id row-generation fn2-core)))
          (if (not (eq code :ok)) (fn2-machine-refuse-phase id fn2-core)
            (let ((fn2-core (fn2-conn-put-core id (phase *fn2-conn-state-reply*) (tx-off 0)
                                               (after *fn2-conn-after-article-input*)
                                               (upload u) (upload-gen ugen) (feed-mode 0) (feed-discard 0) (fed 0)
                                               (word 0) (outcome-ready 0))))
              (fn2-machine-result 512 *fn2-work-transition* 0 t fn2-core))))))))

;; RX exhausted during a block: reset it when every octet was fed, else
;; Receive (the feed consumes every octet it frames, so nothing is retained).
(defmachine-callback fn2-conn-block-input fn2-conn (id budget) 4
  :contract (:cost (:bytes *fn2-conn-receive-bytes*
                    :steps (max *fn2-work-mailbox* (:cost fn2-machine-issue-result :steps)) :descriptors 1)
             :writes (start pos pending stopped wait-reason ready-prev ready-next)
             :tables (fn2-core-ops fn2-core-pool fn2-core-machines fn2-core-machine-tables)
             :next (:article-input)
             :uses (fn2-conn-fill fn2-conn-cap fn2-core-reset fn2-issue-receive fn2-machine-issue-result
                    fn2-machine-refuse-phase))
  (let ((nfill (fn2-conn-fill row-rx-slot fn2-core)) (cap (fn2-conn-cap row-rx-slot fn2-core)))
    (cond ((and (equal row-start nfill) (< 0 nfill))
           (mv-let (code fn2-core) (fn2-core-reset row-rx-slot row-rx-gen *fn2-conn-kind* id row-generation fn2-core)
             (if (not (eq code :ok)) (fn2-machine-refuse-phase id fn2-core)
               (let ((fn2-core (fn2-conn-put-core id (start 0) (pos 0))))
                 (fn2-machine-result 0 *fn2-work-mailbox* 0 t fn2-core)))))
          ((<= cap nfill) (fn2-machine-refuse-phase id fn2-core))
          (t (let ((len (min *fn2-conn-receive-bytes* (- cap nfill))))
               (mv-let (code op opgen fn2-core)
                 (fn2-issue-receive row-cap-index row-cap-nonce row-rx-slot row-rx-gen len
                                    *fn2-conn-kind* id row-generation row-principal-slot fn2-core)
                 (declare (ignore op opgen))
                 (fn2-machine-issue-result id code len fn2-core)))))))

;; Feed one quantum of the block into the upload (section 14.2), and wake it.
(defmachine-callback fn2-conn-feed-step fn2-conn (id budget) 4
  :contract (:cost (:bytes (max (:cost fn2-conn-feed-run :bytes) (:cost fn2-conn-block-input :bytes))
                    :steps (max *fn2-work-transition* (:cost fn2-conn-block-input :steps))
                    :descriptors (:cost fn2-conn-block-input :descriptors))
             :writes (start pos feed-mode feed-discard fed pending stopped wait-reason ready-prev ready-next)
             :tables (fn2-core-ops fn2-core-pool fn2-core-machines fn2-core-machine-tables)
             :next (:article-input)
             :uses (fn2-conn-feed-run fn2-conn-wake fn2-conn-block-input fn2-machine-refuse-phase))
  (b* ((u row-upload)
       ((mv status start mode why copied fn2-core)
        (fn2-conn-feed-run row-start row-feed-mode row-feed-discard row-fed row-rx-slot row-rx-gen id
                           row-generation u row-upload-gen fn2-core))
       (fed (+ row-fed (nfix copied)))
       (fn2-core (fn2-conn-wake u fn2-core)))
    (cond ((not (and (unsigned-byte-p 32 start) (unsigned-byte-p 8 mode) (unsigned-byte-p 8 why)
                     (unsigned-byte-p 60 fed)))
           (fn2-machine-refuse-phase id fn2-core))
          ((eq status :terminator)
           ;; the upload has the block; wait for its outcome (posted to this row)
           (let ((fn2-core (fn2-conn-put-core id (start start) (pos start) (feed-mode *fn2-conn-feed-done*)
                                              (feed-discard why) (fed fed))))
             (fn2-machine-result *fn2-conn-feed-cost* *fn2-work-transition* 0 nil fn2-core)))
          ((eq status :need-more)
           (let ((fn2-core (fn2-conn-put-core id (start start) (pos start) (feed-mode mode)
                                              (feed-discard why) (fed fed))))
             (fn2-call fn2-conn-block-input id budget)))
          ((eq status :budget)
           (let ((fn2-core (fn2-conn-put-core id (start start) (pos start) (feed-mode mode)
                                              (feed-discard why) (fed fed))))
             (fn2-machine-result *fn2-conn-feed-cost* *fn2-work-transition* 0 t fn2-core)))
          (t (fn2-machine-refuse-phase id fn2-core)))))

;; :article-input: feed the block; once its outcome is posted, render it.
(defmachine-callback fn2-conn-block fn2-conn (id budget) 4
  (cond ((not (equal row-pending 0)) (fn2-machine-result 0 *fn2-work-empty* 0 nil fn2-core))
        ((equal row-outcome-ready 1)
         (fn2-machine-with-work 512 *fn2-work-transition* 0
           (mv-let (code after fn2-core)
             (fn2-conn-run-outcome row-word row-mask row-tx-slot row-tx-gen id row-generation fn2-core)
             (if (not (eq code :ok)) (fn2-machine-refuse-phase id fn2-core)
               (let ((fn2-core (fn2-conn-put-core id (phase *fn2-conn-state-reply*) (tx-off 0) (after after)
                                                  (upload *fn2-none*) (upload-gen 0) (rule *fn2-conn-rule-none*)
                                                  (word 0) (outcome-ready 0) (feed-mode 0) (feed-discard 0) (fed 0))))
                 (fn2-machine-result 512 *fn2-work-transition* 0 t fn2-core))))))
        ((equal row-feed-mode *fn2-conn-feed-done*) (fn2-machine-result 0 *fn2-work-empty* 0 nil fn2-core))
        (t (fn2-call fn2-conn-feed-step id budget))))

(defmachine-callback fn2-conn-command fn2-conn (id budget) 4
  (cond ((not (equal row-pending 0)) (fn2-machine-result 0 *fn2-work-empty* 0 nil fn2-core))
        ((not (equal row-rule *fn2-conn-rule-none*)) (fn2-call fn2-conn-open-block id budget))
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
                                                *fn2-conn-state-closing*
                                              (if (equal after *fn2-conn-after-article-input*)
                                                  *fn2-conn-state-article-input*
                                                (if (equal after *fn2-conn-after-query*)
                                                    *fn2-conn-state-query* *fn2-conn-state-command*)))))))
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
                      cursor tx-off ordinal auth-pending refused next-free wait-reason account-ref upload
                      query query-gen)
             :tables (fn2-core-pool fn2-core-machines fn2-core-accounts fn2-cursor-table) :next (:free :retired)
             ;; One use entry per operation: the two calls release TX then RX
             ;; (D0's descending order), declared together.
             :uses ((fn2-core-release :effects ((:release (:tx-range :rx-range))))
                    fn2-machine-gen-limit fn2-machine-free-head fn2-account-unbook-ref fn2-conn-wake
                    fn2-machine-reclaim-fn2-conn fn2-core-stop fn2-conn-cursor-cancel))
  (b* ((kind *fn2-conn-kind*) (gen row-generation) (booked row-account-ref)
       ((mv tcode fn2-core) (fn2-core-release row-tx-slot row-tx-gen kind id gen fn2-core))
       ((mv rcode fn2-core) (fn2-core-release row-rx-slot row-rx-gen kind id gen fn2-core))
       ;; the booking goes; the charges stay with the principal (rule 5)
       ((mv acode fn2-core) (fn2-account-unbook-ref booked fn2-core))
       ;; an upload this row was feeding is woken: it sees the row move on
       ;; (its generation) and drains, posting nothing
       ;; a query cursor waiting on this row is cancelled and woken (an
       ;; upload and a query are never both live: one wake)
       (fn2-core (fn2-conn-cursor-cancel row-query row-query-gen fn2-core))
       (fn2-core (fn2-conn-wake (if (equal row-upload *fn2-none*) row-query row-upload) fn2-core)))
    (cond
     ((not (and (or (eq tcode :ok) (eq tcode :retired)) (or (eq rcode :ok) (eq rcode :retired))))
        (let ((fn2-core (fn2-core-stop *fn2-stop-reason-pool-release* fn2-core)))
          (fn2-machine-result 0 *fn2-work-state* 0 nil fn2-core)))
     ;; a booking the ledger does not hold: the ledger's invariant is broken
     ((not (eq acode :ok))
        (let ((fn2-core (fn2-core-stop *fn2-stop-reason-account* fn2-core)))
          (fn2-machine-result 0 *fn2-work-state* 0 nil fn2-core)))
     (t
      (b* ((retire (>= gen (fn2-machine-gen-limit fn2-core)))
           (next (fn2-machine-free-head *fn2-conn-admission-ordinal* fn2-core))
           (fn2-core (fn2-conn-put-core id
                       (phase (if retire *fn2-conn-state-retired* *fn2-conn-state-free*))
                       (generation (if retire gen (+ 1 gen)))
                       (rx-slot *fn2-none*) (rx-gen 0) (tx-slot *fn2-none*) (tx-gen 0)
                       (cap-index 0) (cap-nonce 0) (start 0) (pos 0) (overflow 0) (compacting 0)
                       (cursor 0) (tx-off 0) (ordinal 0) (auth-pending *fn2-conn-auth-none*) (refused 0)
                       (next-free next) (wait-reason *fn2-wait-none*) (account-ref *fn2-none*)
                       (upload *fn2-none*) (query *fn2-none*) (query-gen 0)))
           (fn2-core (fn2-machine-reclaim-fn2-conn id retire fn2-core)))
        (fn2-machine-result 0 *fn2-work-release* 0 nil fn2-core))))))

(defmachine-callback fn2-conn-drain fn2-conn (id budget) 4
  (cond ((not (equal row-pending 0)) (fn2-machine-result 0 *fn2-work-empty* 0 nil fn2-core))
        ((equal row-borrows 0) (fn2-call fn2-conn-release id budget))
        (t (fn2-machine-result 0 *fn2-work-poll* 0 nil fn2-core))))

;; Observations (the generic router decrements PENDING at a terminal).
;; A completed Receive is charged to the row's principal from its first
;; byte (D7, section 13.4: settled from the completion's count).
(defmachine-callback fn2-conn-observe-receive fn2-conn (id event outcome reason count aux0 aux1) 1
  (if (and (or (equal outcome *fn2-outcome-done*) (equal outcome *fn2-outcome-short*))
           (natp count) (< 0 count))
      (mv-let (code fn2-core) (fn2-account-charge-core row-principal-slot *fn2-account-charge-rx* count fn2-core)
        (if (eq code :ok) (mv id fn2-core) (fn2-machine-refuse-observation fn2-core)))
    (let ((fn2-core (fn2-conn-put-core id (phase *fn2-conn-state-closing*))))
      (mv id fn2-core))))

(defmachine-callback fn2-conn-observe-send fn2-conn (id event outcome reason count aux0 aux1) 1
  (if (not (eq (fn2-machine-pool-borrows-read-code row-tx-slot fn2-core) :ok))
      (fn2-machine-refuse-observation fn2-core)
    (let ((off row-tx-off) (borrows (fn2-machine-pool-borrows row-tx-slot fn2-core)))
      ;; A short send is terminal and the remainder is a new Send (ROUND2
      ;; D.1); it may have moved zero octets, which is progress deferred,
      ;; not a failure. The octets it moved are charged to the row's
      ;; principal (D7, section 13.4).
      (if (and (or (equal outcome *fn2-outcome-done*) (equal outcome *fn2-outcome-short*))
               (natp count))
          (mv-let (code fn2-core) (fn2-account-charge-core row-principal-slot *fn2-account-charge-tx* count fn2-core)
            (if (not (eq code :ok)) (fn2-machine-refuse-observation fn2-core)
              (let ((fn2-core (fn2-conn-put-core id (borrows borrows) (tx-off (+ off count))))) (mv id fn2-core))))
        (let ((fn2-core (fn2-conn-put-core id (borrows borrows) (phase *fn2-conn-state-closing*)))) (mv id fn2-core))))))

(defmachine-callback fn2-conn-observe-release fn2-conn (id event outcome reason count aux0 aux1) 1
  (if (not (eq (fn2-machine-pool-borrows-read-code row-tx-slot fn2-core) :ok))
      (fn2-machine-refuse-observation fn2-core)
    (let ((fn2-core (fn2-conn-put-core id (borrows (fn2-machine-pool-borrows row-tx-slot fn2-core)))))
      (mv id fn2-core))))

(defmachine-callback fn2-conn-observe-close fn2-conn (id event outcome reason count aux0 aux1) 1
  (let ((fn2-core (fn2-conn-put-core id (phase *fn2-conn-state-draining*)))) (mv id fn2-core)))

(defmachine-run fn2-conn)
))

; MACHINE-FORM 6.5 P4: the kind's admission in child form, proved here;
; the admission section (assembly-callbacks-a) makes its core face.
(defmachine-registry fn2-conn)
