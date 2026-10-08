;; fn: the fold-context intern: the rows a replay holds, as a pure function.
;;
;; A held row freezes the statement keyring and generation in force BEFORE
;; its event (books/statement-recover-stream.lisp).  The host's recovery,
;; full or from a checkpoint's suffix, interns through fn-ssr-intern-step:
;; its state carries the keyring, the generation and the identity context
;; from record to record, seeded by (fn-ssr-seed identity) -- the initial
;; context for a full replay, the checkpoint's captured identity for a suffix
;; (host/store-node-host.lisp fn-store-statement-replay-seed).  A capture of
;; rows must therefore be the rows of THAT fold; interning every row at
;; keyring NIL and generation 0 (what the checkpoint capture did before this
;; book) agrees with the replay only over a history with no keyring snapshot
;; (fn-ssr-no-snapshot-p), and serves different verdict generations after a
;; rotation.
;;
;;   fn-scka-intern-one   one wire event's row at a keyring, generation and
;;                        handle (the arena's count);
;;   fn-scka-fold-at      the fold over wire events, a pure function of the
;;                        same state fn-ssr-intern-step carries;
;;   fn-scka-fold-at-is-the-ssr-step, fn-scka-fold-at-arena-is-payloads
;;                        the fold IS the host's worker: its state and its
;;                        arena effect, with no hypothesis on the history;
;;   fn-scka-fold-at-invariants, fn-scka-fold-at-seed
;;                        from a seed the carried keyring and generation are
;;                        the ones the identity context's snapshots name, and
;;                        the carried identity is the replay of the rows:
;;                        the state after a prefix IS the seed of its
;;                        identity, which is how a checkpoint's suffix can be
;;                        seeded from the captured identity alone;
;;   fn-scka-fold-at-restart, fn-scka-intern-at-of-append
;;                        a fold over a suffix, from the seed of the prefix's
;;                        identity, appends to the prefix's rows.
(in-package "ACL2")
(include-book "statement-recover-stream")
(include-book "store-checkpoint-open")

(defun fn-scka-intern-one (w keyring generation h)
  (declare (xargs :guard (and (fn-prin-keyringp keyring) (natp generation) (natp h))
                  :guard-hints (("Goal" :in-theory (enable fn-prin-keyringp)))))
  (cond ((fn-record-p w) (fn-intern-row-at w keyring generation h))
        ((fn-stxa-p w)
         (let ((a (fn-replay-composite-record w)))
           (if (fn-record-p a)
               (fn-hstxa-make w (fn-intern-row-at a keyring generation h))
             :bad)))
        ((fn-wire-event-p w) w)
        (t :bad)))

(defun fn-scka-sealsp (w)
  (declare (xargs :guard t))
  (or (fn-record-p w)
      (and (fn-stxa-p w) (fn-record-p (fn-replay-composite-record w)))))

(defun fn-scka-payload-of (w)
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-record-p w)
      (fn-record-payload w)
    (fn-record-payload (fn-replay-composite-record w))))

(defun fn-scka-payloads (ws)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom ws)
      nil
    (if (fn-scka-sealsp (car ws))
        (cons (fn-scka-payload-of (car ws)) (fn-scka-payloads (cdr ws)))
      (fn-scka-payloads (cdr ws)))))

(defun fn-scka-fold-at (acc ws h)
  (declare (xargs :guard (and (or (eq acc :bad) (fn-ssr-statep acc)) (natp h))
                  :verify-guards nil :measure (len ws)))
  (cond ((or (eq acc :bad) (eq ws :bad)) :bad)
        ((atom ws) (if (null ws) acc :bad))
        (t (let* ((wire (car ws))
                  (row (fn-scka-intern-one wire (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) h))
                  (identity (fn-replay-identity-step (fn-ssr-at 3 acc) row)))
             (if (or (eq row :bad) (not (equal (fn-stxk-context-kind identity) :ok)))
                 :bad
               (fn-scka-fold-at (fn-ssr-publish acc row wire identity) (cdr ws)
                                (if (fn-scka-sealsp wire) (+ 1 h) h)))))))
(defthm fn-scka-intern-event-row
  (equal (mv-nth 0 (fn-intern-event w keyring generation fn-arena))
         (fn-scka-intern-one w keyring generation (fn-arena-count fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-intern-event fn-scka-intern-one fn-cat-intern-list
                                   fn-intern-row-at)
                                  (fn-arena-count-is-len fn-held-make fn-held-facts-of
                                   fn-held-context-of fn-arena-seal-list-is-append)))))

(local
 (defthm fn-scka-intern-event-row-len
   (equal (mv-nth 0 (fn-intern-event w keyring generation fn-arena))
          (fn-scka-intern-one w keyring generation (len fn-arena)))
   :hints (("Goal" :use fn-scka-intern-event-row
            :in-theory (disable fn-scka-intern-event-row fn-intern-event fn-scka-intern-one)))))

(local
 (defthm fn-scka-len-seal-list
   (equal (len (fn-arena-seal-list x a)) (+ 1 (len a)))
   :hints (("Goal" :in-theory (enable fn-arena-seal-list fn-arena$a-seal-list fn-oct-snoc)))))

(local
 (defthm fn-scka-count-of-intern-event
   (implies (not (equal (fn-scka-intern-one w keyring generation h) :bad))
            (equal (len (mv-nth 1 (fn-intern-event w keyring generation fn-arena)))
                   (if (fn-scka-sealsp w) (+ 1 (len fn-arena)) (len fn-arena))))
   :hints (("Goal" :in-theory (e/d (fn-scka-intern-one fn-scka-sealsp)
                                   (fn-intern-row-at fn-held-make fn-scka-intern-event-row
                                    fn-arena-seal-list-is-append fn-hstxa-make))))))

(defthm fn-scka-seal-list-is-append
  (implies (true-listp a)
           (equal (fn-arena-seal-list x a) (append a (list x))))
  :hints (("Goal" :in-theory (enable fn-arena-seal-list fn-arena$a-seal-list fn-oct-snoc))))
(defthm fn-scka-fold-at-is-the-ssr-step
  (equal (mv-nth 0 (fn-ssr-intern-step acc ws nil nil :resident dicts fn-arena))
         (fn-scka-fold-at acc ws (len fn-arena)))
  :hints (("Goal" :induct (fn-ssr-intern-step acc ws nil nil :resident dicts fn-arena)
           :do-not '(generalize fertilize eliminate-destructors)
           :in-theory (e/d (fn-ssr-intern-step fn-scka-fold-at)
                           (fn-intern-event fn-arx-intern-event fn-lzr-intern-event
                            fn-ssr-publish fn-replay-identity-step fn-ssr-at
                            fn-stxk-context-kind fn-scka-intern-one fn-scka-sealsp
                            fn-scka-intern-event-row)))))
(local
 (defthm fn-scka-arena-of-intern-event
   (implies (and (true-listp fn-arena)
                 (not (equal (fn-scka-intern-one w keyring generation h) :bad)))
            (equal (mv-nth 1 (fn-intern-event w keyring generation fn-arena))
                   (if (fn-scka-sealsp w)
                       (append fn-arena (list (fn-scka-payload-of w)))
                     fn-arena)))
   :hints (("Goal" :in-theory (e/d (fn-intern-event fn-scka-intern-one fn-scka-sealsp
                                    fn-scka-payload-of fn-cat-intern-list)
                                   (fn-intern-row-at fn-held-make fn-hstxa-make
                                    fn-scka-intern-event-row fn-arena-seal-list-is-append
                                    fn-stxa-p fn-stxa-is-no-other-wire-event
                                    fn-replay-composite-record fn-cbor-octet-listp))))))

(defthm fn-scka-fold-at-arena-is-payloads
  (implies (and (true-listp fn-arena)
                (not (equal (fn-scka-fold-at acc ws (len fn-arena)) :bad)))
           (equal (mv-nth 1 (fn-ssr-intern-step acc ws nil nil :resident dicts fn-arena))
                  (append fn-arena (fn-scka-payloads ws))))
  :hints (("Goal" :induct (fn-ssr-intern-step acc ws nil nil :resident dicts fn-arena)
           :do-not '(generalize fertilize eliminate-destructors)
           :in-theory (e/d (fn-ssr-intern-step fn-scka-fold-at fn-scka-payloads)
                           (fn-intern-event fn-arx-intern-event fn-lzr-intern-event
                            fn-ssr-publish fn-replay-identity-step fn-ssr-at
                            fn-stxk-context-kind fn-scka-intern-one fn-scka-sealsp
                            fn-scka-payload-of fn-scka-intern-event-row
                            fn-scka-fold-at-is-the-ssr-step)))))
(local (defthm fn-scka-ctx-snapshots-of-context
  (equal (fn-stxk-context-snapshots (fn-stxk-context k n s v g tl)) s)
  :hints (("Goal" :in-theory (enable fn-stxk-context fn-stxk-context-snapshots)))))
(local (defthm fn-scka-ctx-gen-of-context
  (equal (fn-stxk-context-current-generation (fn-stxk-context k n s v g tl)) g)
  :hints (("Goal" :in-theory (enable fn-stxk-context fn-stxk-context-current-generation)))))
(local (defthm fn-scka-ctx-kind-of-context
  (equal (fn-stxk-context-kind (fn-stxk-context k n s v g tl)) k)
  :hints (("Goal" :in-theory (enable fn-stxk-context fn-stxk-context-kind)))))
(local (defthm fn-scka-ctx-next-of-context
  (equal (fn-stxk-context-next (fn-stxk-context k n s v g tl)) n)
  :hints (("Goal" :in-theory (enable fn-stxk-context fn-stxk-context-next)))))
(local (in-theory (disable fn-stxk-context-snapshots fn-stxk-context-current-generation
                           fn-stxk-context-kind fn-stxk-context-next fn-stxk-context)))
(local (defthm fn-scka-fault-keeps
  (and (equal (fn-stxk-context-snapshots (fn-stxk-fault ctx reason)) (fn-stxk-context-snapshots ctx))
        (equal (fn-stxk-context-current-generation (fn-stxk-fault ctx reason))
               (fn-stxk-context-current-generation ctx)))
  :hints (("Goal" :in-theory (enable fn-stxk-fault)))))
(local (defthm fn-scka-apply-verdict-keeps
  (and (equal (fn-stxk-context-snapshots (fn-stxk-apply-verdict ctx e)) (fn-stxk-context-snapshots ctx))
        (equal (fn-stxk-context-current-generation (fn-stxk-apply-verdict ctx e))
               (fn-stxk-context-current-generation ctx)))
  :hints (("Goal" :in-theory (enable fn-stxk-apply-verdict)))))
(local (defthm fn-scka-carried-keeps
  (and (equal (fn-stxk-context-snapshots (fn-replay-apply-carried-verdict ctx e)) (fn-stxk-context-snapshots ctx))
        (equal (fn-stxk-context-current-generation (fn-replay-apply-carried-verdict ctx e))
               (fn-stxk-context-current-generation ctx)))
  :hints (("Goal" :in-theory (enable fn-replay-apply-carried-verdict)))))
(local (defthm fn-scka-revoked-keeps
  (and (equal (fn-stxk-context-snapshots (fn-replay-apply-revoked-verdict ctx e keys)) (fn-stxk-context-snapshots ctx))
        (equal (fn-stxk-context-current-generation (fn-replay-apply-revoked-verdict ctx e keys))
               (fn-stxk-context-current-generation ctx)))
  :hints (("Goal" :in-theory (enable fn-replay-apply-revoked-verdict)))))
(local (defthm fn-scka-advance-keeps
  (and (equal (fn-stxk-context-snapshots (fn-replay-identity-advance ctx)) (fn-stxk-context-snapshots ctx))
        (equal (fn-stxk-context-current-generation (fn-replay-identity-advance ctx))
               (fn-stxk-context-current-generation ctx)))
  :hints (("Goal" :in-theory (enable fn-replay-identity-advance)))))
(local (in-theory (disable fn-stxk-fault fn-stxk-apply-verdict fn-replay-apply-carried-verdict
                           fn-replay-apply-revoked-verdict fn-replay-identity-advance)))
(defthm fn-scka-identity-step-keeps-keyring-state
  (implies (not (fn-stxk-p (fn-replay-identity-wire event)))
           (and (equal (fn-stxk-context-snapshots (fn-replay-identity-step ctx event)) (fn-stxk-context-snapshots ctx))
        (equal (fn-stxk-context-current-generation (fn-replay-identity-step ctx event))
               (fn-stxk-context-current-generation ctx))))
  :hints (("Goal" :in-theory (enable fn-replay-identity-step))))
(local (defthm fn-scka-apply-snapshot-cases
  (implies (and (fn-stxk-p e)
                (equal (fn-stxk-context-kind (fn-stxk-apply-snapshot ctx e)) :ok))
           (or (and (equal (fn-stxk-context-snapshots (fn-stxk-apply-snapshot ctx e))
                           (fn-stxk-context-snapshots ctx))
                    (equal (fn-stxk-context-current-generation (fn-stxk-apply-snapshot ctx e))
                           (fn-stxk-context-current-generation ctx)))
               (and (equal (fn-stxk-context-snapshots (fn-stxk-apply-snapshot ctx e))
                           (cons e (fn-stxk-context-snapshots ctx)))
                    (equal (fn-stxk-context-current-generation (fn-stxk-apply-snapshot ctx e))
                           (fn-stxk-keyring-generation e))
                    (not (equal (fn-stxk-context-current-generation ctx)
                                (fn-stxk-keyring-generation e)))
                    (natp (fn-stxk-keyring-generation e)))))
  :hints (("Goal" :in-theory (enable fn-stxk-apply-snapshot fn-stxk-fault)))))
(local (defthm fn-scka-held-p-of-intern-row-at
  (implies (and (fn-record-p w) (natp generation) (natp h))
           (fn-held-p (fn-intern-row-at w keyring generation h)))
  :hints (("Goal" :in-theory (enable fn-intern-row-at fn-record-p fn-held-p fn-record-internals
                                     fn-held-internals fn-hf-p fn-hc-p
                                     fn-hf-startp fn-hc-verdictp)))))
(local (defthm fn-scka-wire-event-is-not-hstxa
  (implies (fn-wire-event-p w) (not (fn-hstxa-p w)))
  :hints (("Goal" :in-theory (e/d ((:d fn-wire-event-p) fn-hstxa-is-no-wire-event) ())))))
(local (defthm fn-scka-record-not-stxk (implies (fn-record-p w) (not (fn-stxk-p w)))
  :hints (("Goal" :use (:instance fn-record-is-no-other-wire-event (x w))))))
(local (defthm fn-scka-stxa-not-stxk (implies (fn-stxa-p w) (not (fn-stxk-p w)))
  :hints (("Goal" :use (:instance fn-stxa-is-no-other-wire-event (x w))))))
(local (defthm fn-scka-held-not-stxk (implies (fn-held-p w) (not (fn-stxk-p w)))
  :hints (("Goal" :use (:instance fn-held-is-no-wire-event (x w))))))
(local (defthm fn-scka-held-not-hstxa (implies (fn-held-p w) (not (fn-hstxa-p w)))
  :hints (("Goal" :use (:instance fn-hstxa-is-not-held (x w))))))
(defthm fn-scka-intern-one-identity-wire-stxk
  (implies (and (natp g) (natp h)
                (not (equal (fn-scka-intern-one w k g h) :bad)))
           (equal (fn-stxk-p (fn-replay-identity-wire (fn-scka-intern-one w k g h)))
                  (fn-stxk-p w)))
  :hints (("Goal" :in-theory (e/d (fn-scka-intern-one fn-replay-identity-wire
                                   fn-hstxa-accessors-of-make fn-hstxa-p-of-make)
                                  (fn-intern-row-at fn-wire-event-p fn-hstxa-p fn-held-p fn-record-p fn-stxk-p fn-stxa-p))
           :use ((:instance fn-scka-held-p-of-intern-row-at (w w) (keyring k) (generation g))))))
(defun fn-scka-invp (acc)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-ssr-statep acc)
       (equal (fn-ssr-at 1 acc)
              (fn-ssk-keyring-of-snapshots (fn-stxk-context-snapshots (fn-ssr-at 3 acc))))
       (equal (fn-ssr-at 2 acc)
              (fn-ssk-generation (fn-stxk-context-snapshots (fn-ssr-at 3 acc))))))

(local (defthm fn-scka-intern-one-of-stxk
  (implies (fn-stxk-p w) (equal (fn-scka-intern-one w k g h) w))
  :hints (("Goal" :in-theory (e/d (fn-scka-intern-one)
                                  (fn-wire-event-p fn-record-p fn-stxa-p fn-intern-row-at fn-stxk-p))
           :use ((:instance fn-scka-record-not-stxk) (:instance fn-scka-stxa-not-stxk))))))

(local (defthm fn-scka-ssk-generation-of-cons
  (implies (fn-stxk-p e)
           (equal (fn-ssk-generation (cons e s)) (nfix (fn-stxk-keyring-generation e))))
  :hints (("Goal" :in-theory (enable fn-ssk-generation)))))
(local (defthm fn-scka-invp-of-publish-abstract
  (implies (and (fn-scka-invp acc)
                (equal (fn-stxk-context-kind id2) :ok)
                (implies (not (fn-stxk-p wire))
                         (and (equal (fn-stxk-context-snapshots id2)
                                     (fn-stxk-context-snapshots (fn-ssr-at 3 acc)))
                              (equal (fn-stxk-context-current-generation id2)
                                     (fn-stxk-context-current-generation (fn-ssr-at 3 acc)))))
                (implies (fn-stxk-p wire)
                         (or (and (equal (fn-stxk-context-snapshots id2)
                                         (fn-stxk-context-snapshots (fn-ssr-at 3 acc)))
                                  (equal (fn-stxk-context-current-generation id2)
                                         (fn-stxk-context-current-generation (fn-ssr-at 3 acc))))
                             (and (equal (fn-stxk-context-snapshots id2)
                                         (cons wire (fn-stxk-context-snapshots (fn-ssr-at 3 acc))))
                                  (equal (fn-stxk-context-current-generation id2)
                                         (fn-stxk-keyring-generation wire))
                                  (not (equal (fn-stxk-context-current-generation (fn-ssr-at 3 acc))
                                              (fn-stxk-keyring-generation wire)))
                                  (natp (fn-stxk-keyring-generation wire))))))
           (fn-scka-invp (fn-ssr-publish acc row wire id2)))
  :hints (("Goal" :in-theory (e/d (fn-ssr-publish fn-ssr-state)
                                  (fn-ssk-keyring-of-snapshots fn-ssk-generation fn-ssk-apply-snapshot))
           :use ((:instance fn-ssr-publish-preserves-statep (identity id2)))
           :expand ((fn-scka-invp acc))))))
(local (defthm fn-scka-invp-natp-gen
  (implies (fn-scka-invp acc) (natp (fn-ssr-at 2 acc)))
  :hints (("Goal" :in-theory (enable fn-scka-invp fn-ssr-statep)))))
(local (defthm fn-scka-identity-step-of-stxk-def
  (implies (fn-stxk-p e)
           (equal (fn-replay-identity-step ctx e)
                  (if (not (equal (fn-stxk-context-kind ctx) :ok))
                      ctx
                    (if (not (equal (fn-store-event-sequence e) (fn-stxk-context-next ctx)))
                        (fn-stxk-fault ctx :sequence)
                      (fn-stxk-apply-snapshot ctx e)))))
  :hints (("Goal" :in-theory (enable fn-replay-identity-step fn-replay-identity-wire)
           :use (:instance fn-hstxa-is-no-wire-event (x e))))))
(local (in-theory (disable fn-scka-identity-step-of-stxk-def)))
(local (defthm fn-scka-fault-kind
  (equal (fn-stxk-context-kind (fn-stxk-fault ctx r)) :fault)
  :hints (("Goal" :in-theory (enable fn-stxk-fault)))))
(local (defthm fn-scka-identity-step-cases
  (implies (and (fn-stxk-p e)
                (equal (fn-stxk-context-kind (fn-replay-identity-step ctx e)) :ok))
           (or (and (equal (fn-stxk-context-snapshots (fn-replay-identity-step ctx e))
                           (fn-stxk-context-snapshots ctx))
                    (equal (fn-stxk-context-current-generation (fn-replay-identity-step ctx e))
                           (fn-stxk-context-current-generation ctx)))
               (and (equal (fn-stxk-context-snapshots (fn-replay-identity-step ctx e))
                           (cons e (fn-stxk-context-snapshots ctx)))
                    (equal (fn-stxk-context-current-generation (fn-replay-identity-step ctx e))
                           (fn-stxk-keyring-generation e))
                    (not (equal (fn-stxk-context-current-generation ctx)
                                (fn-stxk-keyring-generation e)))
                    (natp (fn-stxk-keyring-generation e)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-scka-identity-step-of-stxk-def)
                           (fn-replay-identity-step fn-stxk-apply-snapshot fn-stxk-fault))
           :use ((:instance fn-scka-apply-snapshot-cases))))))

(local (defthm fn-scka-invp-of-publish-stxk
  (implies (and (fn-scka-invp acc) (fn-stxk-p wire)
                (equal (fn-stxk-context-kind (fn-replay-identity-step (fn-ssr-at 3 acc) wire)) :ok))
           (fn-scka-invp (fn-ssr-publish acc wire wire
                                         (fn-replay-identity-step (fn-ssr-at 3 acc) wire))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-replay-identity-step fn-stxk-apply-snapshot
                               fn-ssr-publish fn-scka-invp fn-ssr-at)
           :use ((:instance fn-scka-invp-of-publish-abstract
                            (row wire) (id2 (fn-replay-identity-step (fn-ssr-at 3 acc) wire)))
                 (:instance fn-scka-identity-step-cases (ctx (fn-ssr-at 3 acc)) (e wire)))))))

(local (defthm fn-scka-invp-of-publish-other
  (implies (and (fn-scka-invp acc) (not (fn-stxk-p wire))
                (not (fn-stxk-p (fn-replay-identity-wire row)))
                (equal (fn-stxk-context-kind (fn-replay-identity-step (fn-ssr-at 3 acc) row)) :ok))
           (fn-scka-invp (fn-ssr-publish acc row wire
                                         (fn-replay-identity-step (fn-ssr-at 3 acc) row))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-replay-identity-step fn-ssr-publish fn-scka-invp fn-ssr-at)
           :use ((:instance fn-scka-invp-of-publish-abstract
                            (id2 (fn-replay-identity-step (fn-ssr-at 3 acc) row)))
                 (:instance fn-scka-identity-step-keeps-keyring-state
                            (ctx (fn-ssr-at 3 acc)) (event row)))))))

(defthm fn-scka-invp-of-publish
  (implies (and (fn-scka-invp acc)
                (natp h)
                (not (equal (fn-scka-intern-one wire (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) h) :bad))
                (equal (fn-stxk-context-kind
                        (fn-replay-identity-step
                         (fn-ssr-at 3 acc)
                         (fn-scka-intern-one wire (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) h)))
                       :ok))
           (fn-scka-invp
            (fn-ssr-publish acc
                            (fn-scka-intern-one wire (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) h)
                            wire
                            (fn-replay-identity-step
                             (fn-ssr-at 3 acc)
                             (fn-scka-intern-one wire (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) h)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-replay-identity-step fn-scka-intern-one fn-ssr-publish
                               fn-scka-invp fn-ssr-at fn-stxk-p)
           :cases ((fn-stxk-p wire))
           :use ((:instance fn-scka-intern-one-identity-wire-stxk
                            (w wire) (k (fn-ssr-at 1 acc)) (g (fn-ssr-at 2 acc)))
                 (:instance fn-scka-intern-one-of-stxk
                            (w wire) (k (fn-ssr-at 1 acc)) (g (fn-ssr-at 2 acc)))
                 (:instance fn-scka-invp-of-publish-other
                            (row (fn-scka-intern-one wire (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) h)))))))
(defthm fn-scka-intern-one-is-store-event
  (implies (and (natp g) (natp h)
                (not (equal (fn-scka-intern-one w k g h) :bad)))
           (fn-store-event-p (fn-scka-intern-one w k g h)))
  :hints (("Goal" :in-theory (e/d (fn-scka-intern-one (:d fn-store-event-p) (:d fn-wire-event-p)
                                   fn-hstxa-p-of-make)
                                  (fn-intern-row-at fn-hstxa-p fn-held-p fn-record-p
                                   fn-stxa-p fn-stxk-p fn-stxe-p fn-store-retention-event-p
                                   fn-cpe-eventp fn-th-topic-eventp))
           :use ((:instance fn-scka-held-p-of-intern-row-at (keyring k) (generation g))))))
(local (defthm fn-scka-rev-onto
  (equal (fn-ag-rev-onto x acc) (revappend x acc))))
(local (defthm fn-scka-rows-of-publish
  (equal (fn-ssr-rows (fn-ssr-publish acc row wire id))
         (append (fn-ssr-rows acc) (list row)))
  :hints (("Goal" :in-theory (enable fn-ssr-publish fn-ssr-rows fn-ssr-state fn-ssr-at)))))
(local (defthm fn-scka-at0-of-publish
  (equal (fn-ssr-at 0 (fn-ssr-publish acc row wire id)) (cons row (fn-ssr-at 0 acc)))
  :hints (("Goal" :in-theory (enable fn-ssr-publish fn-ssr-state fn-ssr-at)))))
(local (defthm fn-scka-at3-of-publish
  (equal (fn-ssr-at 3 (fn-ssr-publish acc row wire id)) id)
  :hints (("Goal" :in-theory (enable fn-ssr-publish fn-ssr-state fn-ssr-at)))))
(local (defthm fn-scka-rows-true-listp
  (implies (not (eq acc :bad)) (true-listp (fn-ssr-rows acc)))
  :hints (("Goal" :in-theory (enable fn-ssr-rows)))))
(local (defthm fn-scka-invp-not-bad (implies (fn-scka-invp acc) (not (eq acc :bad)))
  :hints (("Goal" :in-theory (enable fn-scka-invp fn-ssr-statep)))))
(local (defthm fn-scka-loop-singleton
  (implies (fn-store-event-p x)
           (equal (fn-replay-identity-loop (list x) c) (fn-replay-identity-step c x)))
  :hints (("Goal" :in-theory (e/d (fn-replay-identity-loop) (fn-replay-identity-step fn-store-event-p))))))
(local (defthm fn-scka-step-invariants
  (implies (and (fn-scka-invp acc) (natp h) (true-listp (fn-ssr-at 0 acc))
                (equal (fn-ssr-at 3 acc) (fn-replay-identity-loop (fn-ssr-rows acc) id0))
                (not (equal (fn-scka-intern-one wire (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) h) :bad))
                (equal (fn-stxk-context-kind
                        (fn-replay-identity-step
                         (fn-ssr-at 3 acc)
                         (fn-scka-intern-one wire (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) h)))
                       :ok))
           (let ((acc2 (fn-ssr-publish acc
                                       (fn-scka-intern-one wire (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) h)
                                       wire
                                       (fn-replay-identity-step
                                        (fn-ssr-at 3 acc)
                                        (fn-scka-intern-one wire (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) h)))))
             (and (fn-scka-invp acc2)
                  (true-listp (fn-ssr-at 0 acc2))
                  (equal (fn-ssr-at 3 acc2)
                         (fn-replay-identity-loop (fn-ssr-rows acc2) id0)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-scka-invp fn-ssr-at fn-ssr-rows fn-ssr-publish fn-replay-identity-step
                               fn-replay-identity-loop fn-scka-intern-one fn-stxk-context-kind
                               fn-store-event-p fn-scka-invp-of-publish)
           :use ((:instance fn-scka-invp-of-publish)
                 (:instance fn-replay-identity-append-of-true-lists
                            (prefix (fn-ssr-rows acc))
                            (suffix (list (fn-scka-intern-one wire (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) h)))
                            (ctx id0))
                 (:instance fn-scka-loop-singleton
                            (x (fn-scka-intern-one wire (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) h))
                            (c (fn-replay-identity-loop (fn-ssr-rows acc) id0)))
                 (:instance fn-scka-intern-one-is-store-event
                            (w wire) (k (fn-ssr-at 1 acc)) (g (fn-ssr-at 2 acc))))))))
(defthm fn-scka-fold-at-invariants
  (implies (and (fn-scka-invp acc) (natp h) (true-listp (fn-ssr-at 0 acc))
                (equal (fn-ssr-at 3 acc) (fn-replay-identity-loop (fn-ssr-rows acc) id0))
                (not (equal (fn-scka-fold-at acc ws h) :bad)))
           (and (fn-scka-invp (fn-scka-fold-at acc ws h))
                (true-listp (fn-ssr-at 0 (fn-scka-fold-at acc ws h)))
                (equal (fn-ssr-at 3 (fn-scka-fold-at acc ws h))
                       (fn-replay-identity-loop (fn-ssr-rows (fn-scka-fold-at acc ws h)) id0))))
  :hints (("Goal" :induct (fn-scka-fold-at acc ws h)
           :in-theory (e/d (fn-scka-fold-at)
                           (fn-scka-invp fn-ssr-at fn-ssr-rows fn-ssr-publish fn-replay-identity-step
                            fn-replay-identity-loop fn-scka-intern-one fn-scka-sealsp
                            fn-stxk-context-kind fn-ssr-state fn-store-event-p)))))
(defun fn-scka-ctx (acc)
  (declare (xargs :guard t))
  (fn-ssr-state nil (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) (fn-ssr-at 3 acc)))

(defun fn-scka-restart-sch (rows k g id ws h)
  (declare (xargs :measure (len ws) :verify-guards nil))
  (cond ((atom ws) nil)
        (t (let* ((acc (fn-ssr-state rows k g id))
                  (wire (car ws))
                  (row (fn-scka-intern-one wire k g h))
                  (identity (fn-replay-identity-step id row)))
             (if (or (eq row :bad) (not (equal (fn-stxk-context-kind identity) :ok)))
                 nil
               (let ((acc2 (fn-ssr-publish acc row wire identity))
                     (h2 (if (fn-scka-sealsp wire) (+ 1 h) h)))
                 (list (fn-scka-restart-sch (cons row rows) (fn-ssr-at 1 acc2) (fn-ssr-at 2 acc2)
                                            (fn-ssr-at 3 acc2) (cdr ws) h2)
                       (fn-scka-restart-sch (list row) (fn-ssr-at 1 acc2) (fn-ssr-at 2 acc2)
                                            (fn-ssr-at 3 acc2) (cdr ws) h2))))))))

(defun fn-scka-newp (wire id identity)
  (declare (xargs :guard t))
  (and (fn-stxk-p wire)
       (equal (fn-stxk-context-kind identity) :ok)
       (not (equal (fn-stxk-context-current-generation id)
                   (fn-stxk-context-current-generation identity)))))
(defthm fn-scka-publish-of-state
  (equal (fn-ssr-publish (fn-ssr-state rows k g id) row wire identity)
         (fn-ssr-state (cons row rows)
                       (if (fn-scka-newp wire id identity) (fn-ssk-apply-snapshot wire k) k)
                       (if (fn-scka-newp wire id identity)
                           (nfix (fn-stxk-keyring-generation wire)) g)
                       identity))
  :hints (("Goal" :in-theory (enable fn-ssr-publish fn-ssr-state fn-ssr-at fn-scka-newp))))
(defthm fn-scka-at-of-state
  (and (equal (fn-ssr-at 0 (fn-ssr-state a b c d)) a)
       (equal (fn-ssr-at 1 (fn-ssr-state a b c d)) b)
       (equal (fn-ssr-at 2 (fn-ssr-state a b c d)) c)
       (equal (fn-ssr-at 3 (fn-ssr-state a b c d)) d))
  :hints (("Goal" :in-theory (enable fn-ssr-state fn-ssr-at))))
(local (in-theory (disable fn-scka-newp)))
(defthm fn-scka-fold-at-restart
  (equal (fn-scka-fold-at (fn-ssr-state rows k g id) ws h)
         (let ((r (fn-scka-fold-at (fn-ssr-state nil k g id) ws h)))
           (if (eq r :bad)
               :bad
             (fn-ssr-state (append (fn-ssr-at 0 r) rows) (fn-ssr-at 1 r) (fn-ssr-at 2 r)
                           (fn-ssr-at 3 r)))))
  :hints (("Goal" :induct (fn-scka-restart-sch rows k g id ws h)
           :in-theory (e/d (fn-scka-fold-at)
                           (fn-scka-intern-one fn-scka-sealsp fn-replay-identity-step
                            fn-stxk-context-kind fn-ssr-publish fn-ssr-state fn-ssr-at)))))
(defthm fn-scka-at3-of-seed (equal (fn-ssr-at 3 (fn-ssr-seed id)) id)
  :hints (("Goal" :in-theory (enable fn-ssr-seed fn-ssr-state fn-ssr-at))))
(defthm fn-scka-at0-of-seed (equal (fn-ssr-at 0 (fn-ssr-seed id)) nil)
  :hints (("Goal" :in-theory (enable fn-ssr-seed fn-ssr-state fn-ssr-at))))
(defthm fn-scka-rows-of-seed (equal (fn-ssr-rows (fn-ssr-seed id)) nil)
  :hints (("Goal" :in-theory (enable fn-ssr-rows fn-scka-at0-of-seed))))
(defthm fn-scka-loop-nil (equal (fn-replay-identity-loop nil c) c)
  :hints (("Goal" :in-theory (enable fn-replay-identity-loop))))
(defthm fn-scka-seed-is-invp
  (fn-scka-invp (fn-ssr-seed id))
  :hints (("Goal" :in-theory (enable fn-scka-invp fn-ssr-seed fn-ssr-state fn-ssr-at)
           :use ((:instance fn-ssr-seed-establishes-statep)))))
(defthm fn-scka-seed-state
  (implies (fn-scka-invp acc)
           (equal (fn-ssr-seed (fn-ssr-at 3 acc)) (fn-scka-ctx acc)))
  :hints (("Goal" :in-theory (enable fn-scka-invp fn-ssr-seed fn-scka-ctx fn-ssr-state fn-ssr-at))))
(defthm fn-scka-fold-at-seed
  (implies (and (natp h)
                (not (equal (fn-scka-fold-at (fn-ssr-seed id0) ws h) :bad)))
           (let ((r (fn-scka-fold-at (fn-ssr-seed id0) ws h)))
             (and (fn-scka-invp r)
                  (equal (fn-ssr-at 3 r) (fn-replay-identity-loop (fn-ssr-rows r) id0))
                  (equal (fn-scka-ctx r)
                         (fn-ssr-seed (fn-replay-identity-loop (fn-ssr-rows r) id0))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-scka-fold-at fn-scka-invp fn-ssr-seed fn-ssr-at fn-ssr-rows
                               fn-replay-identity-loop fn-scka-ctx)
           :use ((:instance fn-scka-fold-at-invariants (acc (fn-ssr-seed id0)))
                 (:instance fn-scka-seed-is-invp (id id0))
                 (:instance fn-scka-seed-state (acc (fn-scka-fold-at (fn-ssr-seed id0) ws h)))
                 (:instance fn-scka-at3-of-seed (id id0))
                 (:instance fn-scka-rows-of-seed (id id0)) (:instance fn-scka-loop-nil (c id0)) (:instance fn-scka-at0-of-seed (id id0))))))

(defthm fn-scka-fold-at-of-append
  (implies (and (true-listp ws) (natp h))
           (equal (fn-scka-fold-at acc (append ws vs) h)
                  (let ((m (fn-scka-fold-at acc ws h)))
                    (if (eq m :bad)
                        :bad
                      (fn-scka-fold-at m vs (+ h (len (fn-scka-payloads ws))))))))
  :hints (("Goal" :induct (fn-scka-fold-at acc ws h)
           :in-theory (e/d (fn-scka-fold-at fn-scka-payloads)
                           (fn-scka-intern-one fn-scka-sealsp fn-replay-identity-step
                            fn-stxk-context-kind fn-ssr-publish fn-ssr-at)))))

(defun fn-scka-intern-at (ws id h)
  (declare (xargs :guard (natp h) :verify-guards nil))
  (fn-ssr-rows (fn-scka-fold-at (fn-ssr-seed id) ws h)))

(local (defthm fn-scka-state-of-statep
  (implies (fn-ssr-statep acc)
           (equal (fn-ssr-state (fn-ssr-at 0 acc) (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) (fn-ssr-at 3 acc))
                  acc))
  :hints (("Goal" :in-theory (enable fn-ssr-statep fn-ssr-state fn-ssr-at)
           :expand ((len acc) (len (cdr acc)) (len (cddr acc)) (len (cdddr acc)))))))
(local (defthm fn-scka-statep-of-invp (implies (fn-scka-invp acc) (fn-ssr-statep acc))
  :hints (("Goal" :in-theory (enable fn-scka-invp)))))
(local (defthm fn-scka-ssr-rows-not-bad
  (implies (not (equal (fn-ssr-rows acc) :bad)) (not (equal acc :bad)))
  :hints (("Goal" :in-theory (enable fn-ssr-rows)))))
(local (defthm fn-scka-ssr-rows-of-state
  (equal (fn-ssr-rows (fn-ssr-state a b c d)) (revappend a nil))
  :hints (("Goal" :in-theory (enable fn-ssr-rows fn-ssr-state fn-ssr-at)))))
(local (defthm fn-scka-revappend-append
  (equal (revappend (append x y) nil) (append (revappend y nil) (revappend x nil)))))
(local (defthm fn-scka-ssr-rows-eq
  (implies (not (equal acc :bad)) (equal (fn-ssr-rows acc) (revappend (fn-ssr-at 0 acc) nil)))
  :hints (("Goal" :in-theory (enable fn-ssr-rows)))))

(local (defthm fn-scka-rows-continue
  (implies (fn-scka-invp acc)
           (equal (fn-ssr-rows (fn-scka-fold-at acc vs h))
                  (let ((r2 (fn-scka-fold-at (fn-ssr-seed (fn-ssr-at 3 acc)) vs h)))
                    (if (eq r2 :bad) :bad (append (fn-ssr-rows acc) (fn-ssr-rows r2))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-scka-fold-at fn-ssr-seed fn-ssr-at fn-ssr-rows fn-ssr-state
                               fn-scka-invp fn-scka-ctx fn-scka-fold-at-restart
                               fn-scka-state-of-statep)
           :use ((:instance fn-scka-state-of-statep)
                 (:instance fn-scka-seed-state)
                 (:instance fn-scka-fold-at-restart
                            (rows (fn-ssr-at 0 acc)) (k (fn-ssr-at 1 acc)) (g (fn-ssr-at 2 acc))
                            (id (fn-ssr-at 3 acc)) (ws vs)))
           :expand ((fn-scka-ctx acc))))))

(defthm fn-scka-intern-at-of-append
  (implies (and (true-listp ws) (natp h)
                (not (equal (fn-scka-intern-at ws id h) :bad)))
           (equal (fn-scka-intern-at (append ws vs) id h)
                  (let ((r (fn-scka-intern-at vs (fn-replay-identity-loop (fn-scka-intern-at ws id h) id)
                                              (+ h (len (fn-scka-payloads ws))))))
                    (if (equal r :bad) :bad (append (fn-scka-intern-at ws id h) r)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-scka-fold-at fn-ssr-seed fn-ssr-at fn-ssr-rows fn-ssr-state
                               fn-replay-identity-loop fn-scka-invp fn-scka-ctx
                               fn-scka-fold-at-restart fn-scka-fold-at-of-append)
           :use ((:instance fn-scka-fold-at-of-append (acc (fn-ssr-seed id)))
                 (:instance fn-scka-fold-at-seed (id0 id))
                 (:instance fn-scka-rows-continue
                            (acc (fn-scka-fold-at (fn-ssr-seed id) ws h))
                            (h (+ h (len (fn-scka-payloads ws))))))
           :expand ((fn-scka-intern-at ws id h)
                    (fn-scka-intern-at (append ws vs) id h)))))

(local (defthm fn-scka-ssr-rows-bad-iff
  (equal (equal (fn-ssr-rows acc) :bad) (equal acc :bad))
  :hints (("Goal" :in-theory (enable fn-ssr-rows)))))
(defthm fn-scka-intern-at-bad-iff
  (equal (equal (fn-scka-intern-at ws id h) :bad)
         (equal (fn-scka-fold-at (fn-ssr-seed id) ws h) :bad))
  :hints (("Goal" :in-theory (e/d (fn-scka-intern-at) (fn-ssr-rows fn-scka-fold-at fn-ssr-seed)))))
(defthm fn-scka-intern-at-of-append-bad
  (implies (and (true-listp ws) (natp h) (equal (fn-scka-intern-at ws id h) :bad))
           (equal (fn-scka-intern-at (append ws vs) id h) :bad))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-scka-fold-at fn-ssr-seed fn-ssr-at fn-ssr-rows fn-ssr-state
                               fn-scka-fold-at-of-append fn-scka-intern-at)
           :use ((:instance fn-scka-fold-at-of-append (acc (fn-ssr-seed id)))))))

(defthm fn-scka-intern-at-true-listp
  (implies (not (equal (fn-scka-intern-at ws id h) :bad))
           (true-listp (fn-scka-intern-at ws id h)))
  :hints (("Goal" :in-theory (enable fn-scka-intern-at fn-ssr-rows))))

(local (defthm fn-scka-store-eventsp-snoc
  (implies (and (fn-sco-store-eventsp p) (fn-store-event-p x))
           (fn-sco-store-eventsp (append p (list x))))
  :hints (("Goal" :in-theory (e/d (fn-sco-store-eventsp) (fn-store-event-p))))))
(local (defthm fn-scka-store-eventsp-of-publish
  (implies (and (fn-sco-store-eventsp (fn-ssr-rows acc)) (fn-store-event-p row))
           (fn-sco-store-eventsp (fn-ssr-rows (fn-ssr-publish acc row wire id))))
  :hints (("Goal" :in-theory (disable fn-ssr-publish fn-ssr-rows fn-store-event-p)
           :use ((:instance fn-scka-store-eventsp-snoc (p (fn-ssr-rows acc)) (x row)))))))

(local (defthm fn-scka-step-store-events
  (implies (and (fn-scka-invp acc) (natp h)
                (fn-sco-store-eventsp (fn-ssr-rows acc))
                (not (equal (fn-scka-intern-one wire (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) h) :bad)))
           (fn-sco-store-eventsp
            (fn-ssr-rows (fn-ssr-publish acc
                                         (fn-scka-intern-one wire (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) h)
                                         wire id))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-scka-invp fn-ssr-at fn-ssr-rows fn-ssr-publish fn-scka-intern-one
                               fn-scka-store-eventsp-of-publish fn-scka-intern-one-is-store-event)
           :use ((:instance fn-scka-intern-one-is-store-event
                            (w wire) (k (fn-ssr-at 1 acc)) (g (fn-ssr-at 2 acc)))
                 (:instance fn-scka-store-eventsp-of-publish
                            (row (fn-scka-intern-one wire (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) h))))))))

(defthm fn-scka-fold-at-store-events
  (implies (and (fn-scka-invp acc) (natp h)
                (fn-sco-store-eventsp (fn-ssr-rows acc))
                (not (equal (fn-scka-fold-at acc ws h) :bad)))
           (fn-sco-store-eventsp (fn-ssr-rows (fn-scka-fold-at acc ws h))))
  :hints (("Goal" :induct (fn-scka-fold-at acc ws h)
           :in-theory (e/d (fn-scka-fold-at)
                           (fn-scka-invp fn-ssr-at fn-ssr-rows fn-ssr-publish fn-replay-identity-step
                            fn-scka-intern-one fn-scka-sealsp fn-stxk-context-kind fn-ssr-state
                            fn-store-event-p fn-scka-store-eventsp-of-publish)))))

(defthm fn-scka-intern-at-store-eventsp
  (implies (and (natp h) (not (equal (fn-scka-intern-at ws id h) :bad)))
           (fn-sco-store-eventsp (fn-scka-intern-at ws id h)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-scka-fold-at fn-ssr-seed fn-ssr-rows fn-scka-fold-at-store-events)
           :use ((:instance fn-scka-fold-at-store-events (acc (fn-ssr-seed id))))
           :expand ((fn-scka-intern-at ws id h)))))

; The rows a replay holds after interning WS from the seed of identity ID
; are fn-scka-intern-at's, with the handles continuing from the arena's
; count: the host's worker (fn-ssr-intern-step) and the pure fold agree on
; the rows, on a refusal, and (fn-scka-fold-at-arena-is-payloads) on the arena.
(defthm fn-ssr-step-rows-are-fn-scka-intern-at
  (equal (fn-ssr-rows (mv-nth 0 (fn-ssr-intern-step (fn-ssr-seed id) ws nil nil :resident
                                                    dicts fn-arena)))
         (fn-scka-intern-at ws id (len fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-scka-intern-at) (fn-ssr-intern-step fn-ssr-seed fn-ssr-rows
                                                       fn-scka-fold-at))
           :use ((:instance fn-scka-fold-at-is-the-ssr-step (acc (fn-ssr-seed id)))))))
(defthm fn-scka-payloads-of-append
  (equal (fn-scka-payloads (append ws vs))
         (append (fn-scka-payloads ws) (fn-scka-payloads vs))))

; One row per event.
(local (defthm fn-scka-len-rows-of-publish
  (equal (len (fn-ssr-rows (fn-ssr-publish acc row wire id)))
         (+ 1 (len (fn-ssr-rows acc))))
  :hints (("Goal" :in-theory (disable fn-ssr-publish fn-ssr-rows)
           :use ((:instance fn-scka-rows-of-publish))))))

(defthm fn-scka-fold-at-len-rows
  (implies (not (equal (fn-scka-fold-at acc ws h) :bad))
           (equal (len (fn-ssr-rows (fn-scka-fold-at acc ws h)))
                  (+ (len ws) (len (fn-ssr-rows acc)))))
  :hints (("Goal" :induct (fn-scka-fold-at acc ws h)
           :in-theory (e/d (fn-scka-fold-at)
                           (fn-ssr-rows fn-ssr-publish fn-replay-identity-step fn-scka-intern-one
                            fn-scka-sealsp fn-stxk-context-kind fn-ssr-at)))))

(defthm fn-scka-len-intern-at
  (implies (not (equal (fn-scka-intern-at ws id h) :bad))
           (equal (len (fn-scka-intern-at ws id h)) (len ws)))
  :hints (("Goal" :in-theory (e/d (fn-scka-intern-at) (fn-scka-fold-at fn-ssr-seed fn-ssr-rows
                                                       fn-scka-intern-at-bad-iff))
           :use ((:instance fn-scka-fold-at-len-rows (acc (fn-ssr-seed id)))
                 (:instance fn-scka-rows-of-seed)
                 (:instance fn-scka-intern-at-bad-iff)))))

; A fold that is not refused ran over a true list: the fold of an improper
; list refuses at its tail.
(defthm fn-scka-fold-at-not-bad-true-listp
  (implies (not (equal (fn-scka-fold-at acc ws h) :bad))
           (true-listp ws))
  :rule-classes :forward-chaining
  :hints (("Goal" :induct (fn-scka-fold-at acc ws h)
           :in-theory (e/d (fn-scka-fold-at)
                           (fn-ssr-publish fn-replay-identity-step fn-scka-intern-one
                            fn-scka-sealsp fn-stxk-context-kind fn-ssr-at)))))

(defthm fn-scka-intern-at-not-bad-true-listp-input
  (implies (not (equal (fn-scka-intern-at ws id h) :bad))
           (true-listp ws))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (e/d (fn-scka-intern-at) (fn-scka-fold-at fn-ssr-seed fn-ssr-rows
                                                       fn-scka-intern-at-bad-iff))
           :use ((:instance fn-scka-fold-at-not-bad-true-listp (acc (fn-ssr-seed id)))
                 (:instance fn-scka-intern-at-bad-iff)))))
