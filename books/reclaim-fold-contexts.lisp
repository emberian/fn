; fn: the open interns every retained row at the context the fold decides at
; its position (lane log-premises, Builder L, 2026-10-11).
;
; The reclaim pass's prediction refines a restart's replay only when each
; retained row of the history carries the context the replay fold decides at
; its position: KEYSTONE fn-orcs-predict-rows-at-refines-the-replay
; (books/owner-reclaim-retained.lisp) assumes fn-orcr-fold-contexts-okp of
; the rows it predicts.  This book proves where that premise comes from on
; the host path.  The open's recovery, host/native/io.lisp
; fnn-bridge-recover-step and fnn-recover-suffix-intern, calls
; fn-ssr-intern-step :resident from the seed of the initial context, chunk by
; chunk (fn-ssr-resident-step-of-append joins them).  Every row it interns
; is held at a context decided under the keyring and generation of the
; identity before it, and every handle it names reads the payload the worker
; sealed.
;
; KEYSTONE fn-rfc-the-open-interns-at-the-fold-contexts: for any wire list
; WS, identity ID and arena, the rows fn-ssr-intern-step interns from the
; seed of ID satisfy fn-orcr-fold-contexts-okp from ID over the arena it
; leaves.  It has no hypothesis: a refused open answers :bad, whose rows are
; none.
;
; SCOPE.  This is the open's establishment.  The reclaim pass predicts the
; LIVE history, rewritten (fn-orc-rewrite-rows), and that history also grows
; by the owner's appends after the open.  The rewrite step and the appends
; that carry the premise from the open to the pass are owed by item
; RECLAIM-FOLD-CONTEXTS-CARRIED (owner Builder L).
(in-package "ACL2")
(include-book "owner-reclaim-retained")

(local
 (defun fn-rfc-after (rows id h)
   (declare (xargs :verify-guards nil))
   (if (atom rows)
       (mv id h)
     (let* ((w (car rows))
            (seed (fn-ssr-seed id))
            (row (if (fn-record-p w) (fn-intern-row-at w (fn-ssr-at 1 seed) (fn-ssr-at 2 seed) h) w)))
       (fn-rfc-after (cdr rows) (fn-replay-identity-loop (list row) id) (if (fn-record-p w) (+ 1 h) h))))))

(local
 (defthm fn-rfc-okp-of-append
   (equal (fn-orcr-fold-contexts-okp (append a b) id h fn-arena)
          (and (fn-orcr-fold-contexts-okp a id h fn-arena)
               (fn-orcr-fold-contexts-okp b (mv-nth 0 (fn-rfc-after a id h)) (mv-nth 1 (fn-rfc-after a id h)) fn-arena)))
   :hints (("Goal" :induct (fn-rfc-after a id h)
            :in-theory (disable fn-intern-row-at fn-ssr-seed fn-ssr-at fn-replay-identity-loop
                                fn-held-context-of fn-orcr-retained-p fn-orcr-held-part fn-row-bytes
                                fn-record-p)))))

(local
 (defthm fn-rfc-after-of-append
   (equal (fn-rfc-after (append a b) id h)
          (fn-rfc-after b (mv-nth 0 (fn-rfc-after a id h)) (mv-nth 1 (fn-rfc-after a id h))))
   :hints (("Goal" :induct (fn-rfc-after a id h)
            :in-theory (disable fn-intern-row-at fn-ssr-seed fn-ssr-at fn-replay-identity-loop fn-record-p)))))

(local
 (defthm fn-rfc-held-p-of-intern-row-at
   (implies (and (fn-record-p w) (natp g) (natp h))
            (fn-held-p (fn-intern-row-at w k g h)))
   :hints (("Goal" :in-theory (enable fn-intern-row-at fn-record-p fn-held-p fn-record-internals
                                      fn-held-internals fn-hf-p fn-hc-p
                                      fn-hf-startp fn-hc-verdictp)))))

(local
 (defthm fn-rfc-held-is-not-record
   (implies (fn-held-p x) (not (fn-record-p x)))
   :hints (("Goal" :in-theory (enable fn-record-p fn-record-shapep fn-held-p fn-held-shapep
                                      fn-record-payloadp)))))

(local
 (defthm fn-rfc-hstxa-is-not-record
   (implies (fn-hstxa-p x) (not (fn-record-p x)))
   :hints (("Goal" :in-theory (enable fn-record-p fn-record-shapep fn-hstxa-p)))))

(local
 (defthm fn-rfc-wire-event-is-not-hstxa
   (implies (fn-wire-event-p w) (not (fn-hstxa-p w)))
   :hints (("Goal" :in-theory (e/d ((:d fn-wire-event-p) fn-hstxa-is-no-wire-event) ())))))

(local
 (defthm fn-rfc-wire-event-is-not-held
   (implies (fn-wire-event-p w) (not (fn-held-p w)))
   :hints (("Goal" :in-theory (e/d ((:d fn-wire-event-p)) ())))))

(local
 (defthm fn-rfc-intern-one-not-record
   (implies (and (not (equal (fn-scka-intern-one w k g h) :bad)) (natp g) (natp h))
            (not (fn-record-p (fn-scka-intern-one w k g h))))
   :hints (("Goal" :in-theory (e/d (fn-scka-intern-one fn-hstxa-p-of-make)
                                   (fn-intern-row-at fn-hstxa-make fn-held-p fn-hstxa-p fn-record-p fn-stxa-p fn-wire-event-p))))))

(local
 (defthm fn-rfc-intern-row-at-fields
   (and (equal (fn-held-context (fn-intern-row-at w k g h)) (fn-held-context-of (fn-record-payload w) k g))
        (equal (fn-record-payload (fn-intern-row-at w k g h)) h))
   :hints (("Goal" :in-theory (enable fn-intern-row-at)))))

(local
 (defthm fn-rfc-okp-of-one-interned
   (implies (and (not (equal (fn-scka-intern-one w k g h) :bad))
                 (equal k (fn-ssr-at 1 (fn-ssr-seed id)))
                 (equal g (fn-ssr-at 2 (fn-ssr-seed id)))
                 (natp h) (natp g)
                 (implies (fn-scka-sealsp w)
                          (and (< h (len fn-arena))
                               (equal (nth h fn-arena) (fn-scka-payload-of w)))))
            (fn-orcr-fold-contexts-okp (list (fn-scka-intern-one w k g h)) id hh fn-arena))
   :hints (("Goal" :in-theory (e/d (fn-scka-intern-one fn-scka-sealsp fn-scka-payload-of
                                    fn-row-bytes fn-orcr-retained-p fn-orcr-held-part fn-hstxa-p-of-make)
                                   (fn-held-context-of fn-ssr-seed fn-ssr-at fn-intern-row-at fn-hstxa-make
                                    fn-replay-identity-loop fn-held-p fn-hstxa-p fn-record-p fn-stxa-p
                                    fn-wire-event-p))))))

(local
 (defun fn-rfc-holds (a h ws)
   (declare (xargs :verify-guards nil))
   (if (atom ws)
       t
     (and (implies (fn-scka-sealsp (car ws))
                   (and (< h (len a)) (equal (nth h a) (fn-scka-payload-of (car ws)))))
          (fn-rfc-holds a (if (fn-scka-sealsp (car ws)) (+ 1 h) h) (cdr ws))))))

(local
 (defthm fn-rfc-rows-of-publish
   (equal (fn-ssr-rows (fn-ssr-publish acc row wire id))
          (append (fn-ssr-rows acc) (list row)))
   :hints (("Goal" :in-theory (enable fn-ssr-publish fn-ssr-rows fn-ssr-state fn-ssr-at)))))

(local
 (defthm fn-rfc-id-of-publish
   (equal (fn-ssr-at 3 (fn-ssr-publish acc row wire id)) id)
   :hints (("Goal" :in-theory (enable fn-ssr-publish fn-ssr-state fn-ssr-at)))))

(local
 (defthm fn-rfc-at0-of-publish
   (equal (fn-ssr-at 0 (fn-ssr-publish acc row wire id)) (cons row (fn-ssr-at 0 acc)))
   :hints (("Goal" :in-theory (enable fn-ssr-publish fn-ssr-state fn-ssr-at)))))

(local
 (defthm fn-rfc-invp-parts
   (implies (fn-scka-invp acc)
            (and (not (equal acc :bad))
                 (natp (fn-ssr-at 2 acc))
                 (equal (fn-ssr-at 1 (fn-ssr-seed (fn-ssr-at 3 acc))) (fn-ssr-at 1 acc))
                 (equal (fn-ssr-at 2 (fn-ssr-seed (fn-ssr-at 3 acc))) (fn-ssr-at 2 acc))))
   :hints (("Goal" :in-theory (enable fn-scka-invp fn-ssr-statep fn-ssr-seed fn-ssr-state fn-ssr-at)))))

(local
 (defthm fn-rfc-loop-one-is-step
   (implies (fn-store-event-p row)
            (equal (fn-replay-identity-loop (list row) id)
                   (fn-replay-identity-step id row)))
   :hints (("Goal" :in-theory (e/d (fn-replay-identity-loop)
                                   (fn-store-event-p fn-replay-identity-step))))))

(local
 (defthm fn-rfc-after-of-one-non-record
   (implies (not (fn-record-p row))
            (equal (fn-rfc-after (list row) id h)
                   (mv (fn-replay-identity-loop (list row) id) h)))
   :hints (("Goal" :expand ((fn-rfc-after (list row) id h) (fn-rfc-after nil (fn-replay-identity-loop (list row) id) h))
            :in-theory (disable fn-replay-identity-loop fn-record-p)))))

(local
 (defthm fn-rfc-fold-okp
   (implies (and (fn-scka-invp acc) (natp h)
                 (equal (fn-ssr-at 3 acc) (mv-nth 0 (fn-rfc-after (fn-ssr-rows acc) id0 hh)))
                 (fn-orcr-fold-contexts-okp (fn-ssr-rows acc) id0 hh a)
                 (fn-rfc-holds a h ws)
                 (not (equal (fn-scka-fold-at acc ws h) :bad)))
            (fn-orcr-fold-contexts-okp (fn-ssr-rows (fn-scka-fold-at acc ws h)) id0 hh a))
   :hints (("Goal" :induct (fn-scka-fold-at acc ws h)
            :do-not '(generalize fertilize eliminate-destructors)
            :in-theory (e/d (fn-scka-fold-at)
                            (fn-scka-invp fn-ssr-at fn-ssr-rows fn-ssr-publish fn-replay-identity-step
                             fn-replay-identity-loop fn-scka-intern-one fn-scka-sealsp fn-scka-payload-of
                             fn-stxk-context-kind fn-ssr-state fn-store-event-p fn-ssr-seed
                             fn-orcr-fold-contexts-okp fn-rfc-after fn-record-p))
            :expand ((fn-rfc-holds a h ws)))
           (and stable-under-simplificationp
                '(:use ((:instance fn-scka-invp-of-publish (wire (car ws)))
                        (:instance fn-scka-intern-one-is-store-event
                         (w (car ws)) (k (fn-ssr-at 1 acc)) (g (fn-ssr-at 2 acc)))
                        (:instance fn-rfc-okp-of-one-interned
                         (w (car ws)) (k (fn-ssr-at 1 acc)) (g (fn-ssr-at 2 acc))
                         (id (fn-ssr-at 3 acc)) (fn-arena a))))))))

(local
 (defun fn-rfc-holds-ind (b ws)
   (declare (xargs :verify-guards nil))
   (if (atom ws) b
     (fn-rfc-holds-ind (if (fn-scka-sealsp (car ws)) (append b (list (fn-scka-payload-of (car ws)))) b) (cdr ws)))))

(local
 (defthm fn-rfc-holds-of-append-payloads
   (fn-rfc-holds (append b (fn-scka-payloads ws) c) (len b) ws)
   :hints (("Goal" :induct (fn-rfc-holds-ind b ws)
            :in-theory (e/d (fn-scka-payloads) (fn-scka-sealsp fn-scka-payload-of))))))

(local
 (defthm fn-rfc-okp-of-atom
   (implies (atom rows) (fn-orcr-fold-contexts-okp rows id h fn-arena))))

(local
 (defthm fn-rfc-okp-of-tlf
   (equal (fn-orcr-fold-contexts-okp rows id h (true-list-fix a))
          (fn-orcr-fold-contexts-okp rows id h a))
   :hints (("Goal" :induct (fn-orcr-fold-contexts-okp rows id h a)
            :in-theory (e/d (fn-row-bytes) (fn-intern-row-at fn-ssr-seed fn-ssr-at fn-replay-identity-loop
                                            fn-held-context-of fn-orcr-retained-p fn-orcr-held-part fn-record-p))))))

(local
 (defthm fn-rfc-tlf-of-oct-snoc
   (equal (true-list-fix (fn-oct-snoc x o)) (append (true-list-fix x) (list o)))
   :hints (("Goal" :in-theory (enable fn-oct-snoc true-list-fix)))))

(local
 (defthm fn-rfc-tlf-arena-of-intern-event
   (implies (not (equal (fn-scka-intern-one w keyring generation h) :bad))
            (equal (true-list-fix (mv-nth 1 (fn-intern-event w keyring generation fn-arena)))
                   (if (fn-scka-sealsp w)
                       (append (true-list-fix fn-arena) (list (fn-scka-payload-of w)))
                     (true-list-fix fn-arena))))
   :hints (("Goal" :in-theory (e/d (fn-intern-event fn-scka-intern-one fn-scka-sealsp
                                    fn-scka-payload-of fn-cat-intern-list fn-arena-seal-list fn-arena$a-seal-list)
                                   (fn-intern-row-at fn-held-make fn-hstxa-make
                                    fn-scka-intern-event-row fn-arena-seal-list-is-append
                                    fn-stxa-p fn-stxa-is-no-other-wire-event
                                    fn-replay-composite-record fn-cbor-octet-listp))))))

(local
 (defthm fn-rfc-len-of-tlf (equal (len (true-list-fix x)) (len x)) :hints (("Goal" :in-theory (enable true-list-fix)))))

(local
 (defthm fn-rfc-append-from-tlf
   (implies (equal (true-list-fix x) z) (equal (append x y) (append z y)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable true-list-fix)))))

(local
 (defthm fn-rfc-append-arena-of-intern-event
   (implies (not (equal (fn-scka-intern-one w keyring generation h) :bad))
            (equal (append (mv-nth 1 (fn-intern-event w keyring generation fn-arena)) y)
                   (if (fn-scka-sealsp w)
                       (append fn-arena (cons (fn-scka-payload-of w) y))
                     (append fn-arena y))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-rfc-tlf-arena-of-intern-event)
                  (:instance fn-rfc-append-from-tlf (x (mv-nth 1 (fn-intern-event w keyring generation fn-arena)))
                             (z (if (fn-scka-sealsp w)
                                    (append (true-list-fix fn-arena) (list (fn-scka-payload-of w)))
                                  (true-list-fix fn-arena)))))
            :in-theory (disable fn-rfc-tlf-arena-of-intern-event fn-intern-event fn-scka-intern-one
                                fn-scka-sealsp fn-scka-payload-of)))))

(local
 (defthm fn-rfc-tlf-arena-of-step
   (implies (not (equal (fn-scka-fold-at acc ws (len fn-arena)) :bad))
            (equal (true-list-fix (mv-nth 1 (fn-ssr-intern-step acc ws nil nil :resident dicts fn-arena)))
                   (append (true-list-fix fn-arena) (fn-scka-payloads ws))))
   :hints (("Goal" :induct (fn-ssr-intern-step acc ws nil nil :resident dicts fn-arena)
            :do-not '(generalize fertilize eliminate-destructors)
            :in-theory (e/d (fn-ssr-intern-step fn-scka-fold-at fn-scka-payloads)
                            (fn-intern-event fn-arx-intern-event fn-lzr-intern-event
                             fn-ssr-publish fn-replay-identity-step fn-ssr-at
                             fn-stxk-context-kind fn-scka-intern-one fn-scka-sealsp
                             fn-scka-payload-of
                             fn-scka-fold-at-is-the-ssr-step))))))

(local
 (defthm fn-rfc-okp-of-bad-rows
   (fn-orcr-fold-contexts-okp (fn-ssr-rows :bad) id h fn-arena)
   :hints (("Goal" :in-theory (enable fn-ssr-rows)))))

(defthm fn-rfc-the-open-interns-at-the-fold-contexts
  (fn-orcr-fold-contexts-okp
   (fn-ssr-rows (mv-nth 0 (fn-ssr-intern-step (fn-ssr-seed id) ws nil nil :resident dicts fn-arena)))
   id h
   (mv-nth 1 (fn-ssr-intern-step (fn-ssr-seed id) ws nil nil :resident dicts fn-arena)))
  :hints (("Goal" :do-not-induct t
           :cases ((equal (fn-scka-fold-at (fn-ssr-seed id) ws (len fn-arena)) :bad))
           :in-theory (disable fn-ssr-intern-step fn-scka-fold-at fn-ssr-seed fn-ssr-rows fn-scka-invp
                               fn-orcr-fold-contexts-okp fn-rfc-fold-okp fn-rfc-holds-of-append-payloads
                               fn-scka-fold-at-is-the-ssr-step fn-rfc-tlf-arena-of-step fn-rfc-holds
                               fn-rfc-okp-of-tlf)
           :use ((:instance fn-scka-fold-at-is-the-ssr-step (acc (fn-ssr-seed id)))
                 (:instance fn-rfc-tlf-arena-of-step (acc (fn-ssr-seed id)))
                 (:instance fn-rfc-okp-of-tlf
                            (rows (fn-ssr-rows (fn-scka-fold-at (fn-ssr-seed id) ws (len fn-arena))))
                            (a (mv-nth 1 (fn-ssr-intern-step (fn-ssr-seed id) ws nil nil :resident dicts fn-arena))))
                 (:instance fn-scka-seed-is-invp)
                 (:instance fn-rfc-holds-of-append-payloads (b (true-list-fix fn-arena)) (c nil))
                 (:instance fn-rfc-fold-okp (acc (fn-ssr-seed id)) (h (len fn-arena)) (id0 id) (hh h)
                            (a (append (true-list-fix fn-arena) (fn-scka-payloads ws))))))))
