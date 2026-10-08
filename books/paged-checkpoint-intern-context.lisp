; Identity/keyring context is independent of payload handle numbers.
; CPR roots are NOT: acceptance retains those handles.  This book proves
; only the projection needed to connect metadata interning to full replay.
(in-package "ACL2")
(include-book "paged-checkpoint-held")

(defthm pcko-identity-of-hstxa
  (implies (and (fn-stxa-p w) (fn-held-p h1) (fn-held-p h2))
           (equal (fn-replay-identity-step ctx (fn-hstxa-make w h1))
                  (fn-replay-identity-step ctx (fn-hstxa-make w h2))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-replay-identity-step fn-store-event-sequence fn-replay-identity-wire)
                           (fn-held-p fn-stxa-p fn-hsig-article-event-carried-bindsp fn-hsig-article-event-revoked-bindsp
                            fn-stxk-fault fn-replay-identity-advance fn-stxk-p fn-stxe-p))
           :use ((:instance fn-hstxa-is-no-wire-event (x (fn-hstxa-make w h1)))
                 (:instance fn-hstxa-is-no-wire-event (x (fn-hstxa-make w h2)))
                 (:instance fn-hstxa-is-not-held (x (fn-hstxa-make w h1)))
                 (:instance fn-hstxa-is-not-held (x (fn-hstxa-make w h2)))
                 (:instance fn-hstxa-p-of-make (stxa w) (held h1))
                 (:instance fn-hstxa-p-of-make (stxa w) (held h2))))))

(defthm pcko-held-p-of-row-at
  (implies (and (fn-record-p w) (natp g) (natp h))
           (fn-held-p (fn-intern-row-at w k g h)))
  :hints (("Goal" :in-theory (enable fn-record-p fn-held-p fn-record-internals fn-held-internals fn-hf-p fn-hc-p
                                     fn-hf-startp fn-hc-verdictp fn-intern-row-at))))

(local
 (defthm pckh-identity-of-held
 (implies (fn-held-p h)
  (equal (fn-replay-identity-step ctx h)
   (cond ((not (equal (fn-stxk-context-kind ctx) :ok)) ctx)
         ((not (equal (fn-record-sequence h) (fn-stxk-context-next ctx)))
          (fn-stxk-fault ctx :sequence))
         (t (fn-replay-identity-advance ctx)))))
 :hints (("Goal" :in-theory
 (union-theories (theory 'minimal-theory)
 '(fn-replay-identity-step fn-replay-identity-wire fn-store-event-sequence
   fn-hsig-article-event-carried-bindsp fn-hsig-article-event-revoked-bindsp))
 :use ((:instance fn-held-is-no-wire-event (x h))
       (:instance fn-hstxa-is-not-held (x h)))))))

(local
 (defthm pckh-identity-of-intern-row
 (implies (and (fn-record-p w) (natp g) (natp h))
  (equal (fn-replay-identity-step ctx (fn-intern-row-at w k g h))
   (cond ((not (equal (fn-stxk-context-kind ctx) :ok)) ctx)
         ((not (equal (fn-record-sequence w) (fn-stxk-context-next ctx)))
          (fn-stxk-fault ctx :sequence))
         (t (fn-replay-identity-advance ctx)))))
 :hints (("Goal" :use ((:instance pcko-held-p-of-row-at)
                     (:instance pckh-identity-of-held
                               (h (fn-intern-row-at w k g h))))
 :in-theory (e/d (fn-intern-row-at)
 (fn-replay-identity-step fn-held-make fn-held-p fn-held-facts-of fn-held-context-of
  pckh-identity-of-held fn-replay-identity-advance fn-stxk-fault))))))

(local
 (defthm pckh-intern-one-identity-handle-independent
 (implies (and (natp g) (natp a) (natp b))
  (equal (fn-replay-identity-step ctx (fn-scka-intern-one w k g a))
         (fn-replay-identity-step ctx (fn-scka-intern-one w k g b))))
 :hints (("Goal" :in-theory
 (e/d (fn-scka-intern-one)
      (fn-intern-row-at fn-replay-identity-step fn-held-p fn-hstxa-p fn-stxa-p
       fn-record-p fn-wire-event-p fn-held-make fn-hstxa-make
       fn-replay-composite-record pcko-identity-of-hstxa))
 :use ((:instance pcko-held-p-of-row-at (w (fn-replay-composite-record w)) (h a))
       (:instance pcko-held-p-of-row-at (w (fn-replay-composite-record w)) (h b))
       (:instance pcko-identity-of-hstxa
        (h1 (fn-intern-row-at (fn-replay-composite-record w) k g a))
        (h2 (fn-intern-row-at (fn-replay-composite-record w) k g b))))))))

(local
 (defthm pckh-intern-one-bad-handle-independent
 (equal (equal (fn-scka-intern-one w k g a) :bad)
        (equal (fn-scka-intern-one w k g b) :bad))
 :hints (("Goal" :in-theory
 (e/d (fn-scka-intern-one fn-intern-row-at fn-held-make fn-hstxa-make)
      (fn-held-facts-of fn-held-context-of fn-replay-composite-record
       fn-record-p fn-stxa-p fn-wire-event-p))))))
(defun fn-pck-context (st)
  (declare (xargs :guard t))
  (if (equal st :bad) :bad
    (list (fn-ssr-at 1 st) (fn-ssr-at 2 st) (fn-ssr-at 3 st))))

(defun fn-pck-context-agreep (a b)
  (declare (xargs :guard t))
  (or (and (equal a :bad) (equal b :bad))
      (and (fn-ssr-statep a) (fn-ssr-statep b)
           (equal (fn-pck-context a) (fn-pck-context b)))))
(local
 (defthm pckh-publish-agrees
 (implies (and (fn-pck-context-agreep a b) (not (equal a :bad)))
  (fn-pck-context-agreep (fn-ssr-publish a r1 w id)
                         (fn-ssr-publish b r2 w id)))
 :hints (("Goal" :in-theory (enable fn-pck-context-agreep fn-ssr-publish fn-ssr-state fn-ssr-at fn-ssr-statep)))))

(defthm pckh-context-bad
 (equal (fn-pck-context-agreep :bad b) (equal b :bad))
 :hints (("Goal" :in-theory (enable fn-pck-context-agreep fn-ssr-statep))))

(defthm pckh-context-state-parts
 (implies (and (fn-pck-context-agreep a b) (not (equal a :bad)))
  (and (not (equal b :bad)) (fn-ssr-statep a) (fn-ssr-statep b)
       (natp (fn-ssr-at 2 a))
       (equal (fn-ssr-at 1 a) (fn-ssr-at 1 b))
       (equal (fn-ssr-at 2 a) (fn-ssr-at 2 b))
       (equal (fn-ssr-at 3 a) (fn-ssr-at 3 b))))
 :hints (("Goal" :in-theory (enable fn-pck-context-agreep fn-ssr-statep))))
(defthm pckh-context-step
 (implies (and (fn-pck-context-agreep a b) (natp ha) (natp hb))
  (fn-pck-context-agreep (fn-scka-fold-at a (list w) ha)
                         (fn-scka-fold-at b (list w) hb)))
 :hints (("Goal" :do-not-induct t
 :cases ((equal a :bad))
 :in-theory (e/d (fn-scka-fold-at)
 (fn-pck-context-agreep fn-scka-intern-one fn-scka-sealsp fn-ssr-at
  fn-replay-identity-step fn-ssr-publish fn-stxk-context-kind fn-ssr-statep
  pckh-intern-one-identity-handle-independent pckh-intern-one-bad-handle-independent))
 :use (pckh-context-state-parts
 (:instance pckh-intern-one-identity-handle-independent
  (ctx (fn-ssr-at 3 a)) (k (fn-ssr-at 1 a)) (g (fn-ssr-at 2 a)) (a ha) (b hb))
 (:instance pckh-intern-one-bad-handle-independent
  (k (fn-ssr-at 1 a)) (g (fn-ssr-at 2 a)) (a ha) (b hb))))))

(defthm pckh-fold-atom
 (implies (atom ws)
  (equal (fn-scka-fold-at acc ws h) (if (equal ws nil) acc :bad)))
 :hints (("Goal" :in-theory (enable fn-scka-fold-at))))

(defthm pckh-fold-bad
 (equal (fn-scka-fold-at :bad ws h) :bad)
 :hints (("Goal" :in-theory (enable fn-scka-fold-at))))

(defthm pckh-fold-cons
 (implies (natp h)
  (equal (fn-scka-fold-at acc (cons w ws) h)
         (fn-scka-fold-at (fn-scka-fold-at acc (list w) h) ws
          (if (fn-scka-sealsp w) (+ 1 h) h))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-scka-fold-at-of-append (ws (list w)) (vs ws)))
 :in-theory (e/d (fn-scka-payloads)
 (fn-scka-fold-at fn-scka-sealsp fn-scka-payload-of)))))

(local
 (defun pckh-fold-pair-ind (a b ws ha hb)
 (declare (xargs :measure (len ws) :verify-guards nil))
 (if (atom ws) (list a b ha hb)
  (pckh-fold-pair-ind (fn-scka-fold-at a (list (car ws)) ha)
                      (fn-scka-fold-at b (list (car ws)) hb) (cdr ws)
                      (if (fn-scka-sealsp (car ws)) (+ 1 ha) ha)
                      (if (fn-scka-sealsp (car ws)) (+ 1 hb) hb)))))

(defthm fn-pck-fold-context-handle-independent
 (implies (and (fn-pck-context-agreep a b) (natp ha) (natp hb))
  (fn-pck-context-agreep (fn-scka-fold-at a ws ha)
                         (fn-scka-fold-at b ws hb)))
 :hints (("Goal" :induct (pckh-fold-pair-ind a b ws ha hb)
 :in-theory (disable fn-scka-fold-at fn-pck-context-agreep fn-scka-sealsp (tau-system)))
 ("Subgoal *1/2" :use ((:instance pckh-fold-cons (acc a) (h ha) (w (car ws)) (ws (cdr ws)))
                        (:instance pckh-fold-cons (acc b) (h hb) (w (car ws)) (ws (cdr ws)))))
 ("Subgoal *1/1" :in-theory (disable fn-scka-fold-at fn-pck-context-agreep (tau-system)))))
