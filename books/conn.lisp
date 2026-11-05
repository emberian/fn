;; The connection machine fn2-conn (layer D, quest D3; ROUND2 section B.2
;; row 1, its connection half: the listener is A's fn2-listener). The design,
;; with every arm's contract, is docs/d-machines-nntp.md section 4.2.
;; Declared through defmachine with every arm in the checked arm language
;; (none :unchecked); the decision table is conn-answer.lisp; the grammar is
;; nntp-grammar.lisp. Schema and partition registration live in
;; books/conn-kind.lisp; continuations are materialized by
;; assembly-callbacks-d-conn.lisp.
(in-package "ACL2")
(include-book "conn-kind")
(include-book "upload-kind")
(fn2-book-layer :d)

;; Declared costs of the connection's outside calls (section 4.2). Each is a
;; thin stobj-let wrapper over a pool-level function; none builds a list.
(defcost fn2-conn-frame :bytes *fn2-conn-frame-bytes* :tables (fn2-core-pool)
  :doc "Frame RX from the row's (start pos overflow): the grammar's framer under the frame quantum.")
(defcost fn2-conn-run-answer :bytes *fn2-conn-answer-bytes*
  :answers (:ok :bounds) :faults (:bounds) :tables (fn2-core-pool)
  :doc "Parse one framed line and answer it into TX (conn-answer.lisp); reads the clock mailbox.")
(defcost fn2-conn-run-overflow :bytes 512
  :answers (:ok :bounds) :faults (:bounds) :tables (fn2-core-pool)
  :doc "Render the overflow refusal into TX.")
(defcost fn2-conn-run-greeting :bytes 512
  :answers (:ok :bounds) :faults (:bounds) :tables (fn2-core-pool)
  :doc "Render the greeting, or the capacity 400, into TX.")
(defcost fn2-conn-fill :doc "A held pool slot's fill.")
(defcost fn2-conn-reading-p :doc "Whether the profile serves reading: the cursor partition has rows.")
(defcost fn2-conn-cursor-go :tables (fn2-cursor-table) :doc "Give the query cursor its move (TX is empty).")
(defcost fn2-conn-cursor-cancel :tables (fn2-cursor-table) :doc "Cancel a waiting query cursor: the connection drains.")
(defcost fn2-conn-posting-p :doc "Whether posting is served (the input configuration; section 14.5).")
(defcost fn2-conn-peering-p :doc "Whether peers are admitted: the peer bit on a connection with an address family (the input configuration; E4's grant replaces it).")
(defcost fn2-conn-run-block-open :bytes 512
  :answers (:ok :bounds) :faults (:bounds) :tables (fn2-core-pool)
  :doc "Render a block's opening reply (340) into TX.")
(defcost fn2-conn-run-outcome :bytes 512
  :answers (:ok :bounds) :faults (:bounds) :tables (fn2-core-pool)
  :doc "Render a block's outcome reply into TX.")
(defcost fn2-conn-cap :doc "A held pool slot's capacity.")
(defcost fn2-conn-feed-run :bytes *fn2-conn-feed-cost*
  :answers (:terminator :need-more :budget :bounds :fault)
  :faults (:bounds :fault)
  :tables (fn2-core-pool)
  :doc "Feed RX into the upload's chunk (upload-feed.lisp).")
(defcost fn2-conn-wake :tables (fn2-core-machines) :doc "Wake the upload or cursor this connection serves.")

;; ------------------------------------------------------------------------
;; The operations, materialized after the core instance
;; (assembly-callbacks-d.lisp). The row's owner triple for every pool access
;; is (*fn2-conn-kind* oslot ogen).
(defmacro fn2-conn-op-events ()
 '(progn
(defun fn2-conn-frame (slot gen start pos overflow oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (status s p o)
    (fn2-gram-frame *fn2-conn-frame-bytes* (nfix start) (max (nfix start) (nfix pos)) (if (equal overflow 1) 1 0)
                    *fn2-nntp-line-cap* slot gen *fn2-conn-kind* oslot ogen fn2-pool)
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
  (case after (:closing *fn2-conn-after-closing*)
    ((:article-input :ihave :takethis :discard) *fn2-conn-after-article-input*)
    (:query *fn2-conn-after-query*)
    (otherwise *fn2-conn-after-command*)))
(defun fn2-conn-rule-code (after)
  (declare (xargs :guard t))
  (case after (:article-input *fn2-conn-rule-post*)
    (:ihave *fn2-conn-rule-ihave*)
    (:takethis *fn2-conn-rule-takethis*)
    (otherwise *fn2-conn-rule-none*)))
(defun fn2-conn-upload-rule (rule)
  (declare (xargs :guard t))
  (cond ((equal rule *fn2-conn-rule-ihave*) *fn2-upload-rule-ihave*)
        ((equal rule *fn2-conn-rule-takethis*) *fn2-upload-rule-takethis*)
        (t *fn2-upload-rule-post*)))
(defun fn2-conn-rule-keyword (rule)
  (declare (xargs :guard t))
  (cond ((equal rule *fn2-conn-rule-ihave*) :ihave)
        ((equal rule *fn2-conn-rule-takethis*) :takethis)
        (t :post)))

;; One framed line [s, e) answered into TX: (mv code after pending rule fn2-core),
;; AFTER, PENDING and RULE as the row's enum codes.
(defun fn2-conn-run-answer (s e mask pending posting reading rslot rgen tslot tgen oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (mv-let (seen flags real) (fn2-conn-clock fn2-core)
    (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
      (code after next fn2-pool)
      (fn2-answer (nfix s) (nfix e) mask (fn2-conn-auth-keyword pending) (equal posting 1) reading seen flags real
                       rslot rgen tslot tgen *fn2-conn-kind* oslot ogen fn2-pool)
      (mv code (fn2-conn-after-code after) (fn2-conn-auth-code next) (fn2-conn-rule-code after) fn2-core))))
(fn2-core-preserves fn2-conn-run-answer (s e mask pending posting reading rslot rgen tslot tgen oslot ogen fn2-core) :position 4 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))

(defun fn2-conn-run-greeting (refused posting mask tslot tgen oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (code after fn2-pool)
    (fn2-answer-greeting (equal refused 1) (equal posting 1) mask tslot tgen *fn2-conn-kind* oslot ogen fn2-pool)
    (mv code (fn2-conn-after-code after) fn2-core)))
(fn2-core-preserves fn2-conn-run-greeting (refused posting mask tslot tgen oslot ogen fn2-core) :position 2 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))

(defun fn2-conn-run-overflow (mask tslot tgen oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (code fn2-pool)
    (fn2-answer-overflow mask tslot tgen *fn2-conn-kind* oslot ogen fn2-pool)
    (mv code fn2-core)))
(fn2-core-preserves fn2-conn-run-overflow (mask tslot tgen oslot ogen fn2-core) :position 1 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
(defun fn2-conn-posting-p (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-input-config (fn2-core-input-config fn2-core)))
    (p) (and (fn2-input-config-wfp fn2-input-config) (natp (fn2-input-config-rows fn2-input-config))
             (< 0 (fn2-input-config-rows fn2-input-config)) (equal (fn2-input-config-posting 0 fn2-input-config) 1))
    (if p 1 0)))
(defun fn2-conn-peering-p (fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-input-config (fn2-core-input-config fn2-core)))
    (p) (and (fn2-input-config-wfp fn2-input-config) (natp (fn2-input-config-rows fn2-input-config))
             (< 0 (fn2-input-config-rows fn2-input-config)) (equal (fn2-input-config-peering 0 fn2-input-config) 1))
    (if p 1 0)))
(defun fn2-upload-gen-of (u fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (eq (fn2-upload-snapshot-read-code u fn2-core) :ok) (fn2-machine-generation u fn2-core) 0))
(defthm fn2-conn-posting-p-bit
  (bitp (fn2-conn-posting-p fn2-core))
  :rule-classes ((:type-prescription :typed-term (fn2-conn-posting-p fn2-core))
                 (:rewrite :corollary (unsigned-byte-p 1 (fn2-conn-posting-p fn2-core)))))
(defthm fn2-conn-peering-p-bit
  (bitp (fn2-conn-peering-p fn2-core))
  :rule-classes ((:type-prescription :typed-term (fn2-conn-peering-p fn2-core))
                 (:rewrite :corollary (unsigned-byte-p 1 (fn2-conn-peering-p fn2-core)))))
(defthm fn2-upload-gen-of-u60
  (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
           (unsigned-byte-p 60 (fn2-upload-gen-of u fn2-core))))
(defun fn2-conn-run-block-open (rule mask tslot tgen oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (code fn2-pool)
    (fn2-answer-block-open (equal rule *fn2-conn-rule-ihave*) mask tslot tgen *fn2-conn-kind* oslot ogen fn2-pool)
    (mv code fn2-core)))
(fn2-core-preserves fn2-conn-run-block-open (rule mask tslot tgen oslot ogen fn2-core) :position 1 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
(defun fn2-conn-run-outcome (rule word mlen mask tslot tgen oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (code after fn2-pool)
    (fn2-answer-outcome (fn2-conn-rule-keyword rule) (fn2-upload-word-of (nfix word)) (nfix mlen)
                        mask tslot tgen *fn2-conn-kind* oslot ogen fn2-pool)
    (mv code (fn2-conn-after-code after) fn2-core)))
(fn2-core-preserves fn2-conn-run-outcome (rule word mlen mask tslot tgen oslot ogen fn2-core) :position 2 :rows nil
  :hints (("Goal" :in-theory (enable fn2-core-wfp))))
;; Feed [start, fill) of RX into the upload's current chunk (the first while
;; it has room), at most *fn2-conn-feed-bytes* octets and no further than one
;; octet past the article bound (so a too-large block is refused, never
;; buffered).
(defun fn2-conn-feed-pool (left start mode discard rslot rgen oslot ogen slot sgen u ugen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (status start2 mode2 discard2 copied fn2-pool)
    (fn2-upload-feed (max 1 (nfix left)) (nfix start) (nfix mode) discard rslot rgen *fn2-conn-kind* oslot ogen
                     slot sgen *fn2-upload-kind* u ugen fn2-pool)
    (mv status start2 mode2 discard2 copied fn2-core)))
(fn2-core-preserves fn2-conn-feed-pool (left start mode discard rslot rgen oslot ogen slot sgen u ugen fn2-core)
  :position 5 :rows nil :hints (("Goal" :in-theory (enable fn2-core-wfp))))
(in-theory (disable fn2-conn-feed-pool))
(defun fn2-conn-feed-run (start mode why fed rslot rgen u ugen oslot ogen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (equal u *fn2-none*)
      (if (not (and (natp start) (natp mode) (natp fed) (natp why)))
          (mv :bounds 0 0 0 0 fn2-core)
        (b* ((discard (not (equal why 0)))
             ((mv status start2 mode2 discard2 copied fn2-core)
              (fn2-conn-feed-pool *fn2-conn-feed-bytes* start mode discard rslot rgen oslot ogen *fn2-none* 0 0 0 fn2-core))
             (why2 (cond (discard why) (discard2 1) (t 0))))
          (mv (if (eq status :full) :budget status) start2 mode2 why2 (nfix copied) fn2-core)))
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
          (fn2-conn-feed-pool left start mode discard rslot rgen oslot ogen (if in0 c0 c1) (if in0 g0 g1) u ugen fn2-core))
         (fed2 (+ fed (nfix copied)))
         (too-large (and (not discard2) (or (< bound fed2) (and (eq status :full) (not in0)))))
         (why2 (cond (discard why) (too-large 2) (discard2 1) (t 0))))
      (mv (if (eq status :full) :budget status) start2 mode2 why2 (nfix copied) fn2-core))))
(fn2-core-preserves fn2-conn-feed-run (start mode why fed rslot rgen u ugen oslot ogen fn2-core) :position 5 :rows nil)
(defun fn2-conn-wake (u fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (and (unsigned-byte-p 32 u) (not (equal u *fn2-none*))) (fn2-machine-set-wake-id u fn2-core) fn2-core))
(fn2-core-preserves fn2-conn-wake (u fn2-core) :rows nil)

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
(defun fn2-conn-cursor-go (x xgen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (fn2-conn-cursor-live-p x xgen fn2-core) (fn2-cursor-put-core x (turn 1)) fn2-core))
(fn2-core-preserves fn2-conn-cursor-go (x xgen fn2-core) :rows nil)
(defun fn2-conn-cursor-cancel (x xgen fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
  (if (fn2-conn-cursor-live-p x xgen fn2-core) (fn2-cursor-put-core x (cancel 1) (turn 1)) fn2-core))
(fn2-core-preserves fn2-conn-cursor-cancel (x xgen fn2-core) :rows nil)

(in-theory (disable fn2-conn-posting-p fn2-conn-peering-p fn2-upload-gen-of fn2-conn-run-block-open fn2-conn-run-outcome fn2-conn-feed-run
                    fn2-conn-wake fn2-conn-reading-p fn2-conn-cursor-live-p fn2-conn-cursor-go fn2-conn-cursor-cancel))
(in-theory (disable fn2-conn-frame fn2-conn-fill fn2-conn-cap fn2-conn-clock fn2-conn-run-answer
                    fn2-conn-run-greeting fn2-conn-run-overflow))
))

;; The connection's continuations (materialized in assembly-callbacks-d-conn.lisp).
(defmacro fn2-conn-events ()
 '(progn
(defmachine-arms fn2-conn)
(defmachine-run fn2-conn)
))
