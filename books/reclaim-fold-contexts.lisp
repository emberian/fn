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
; by the owner's appends after the open.  The rewrite step is carried at the
; end of this book (KEYSTONE fn-rfc-the-rewrite-keeps-the-fold-contexts).  The
; appends that carry the premise from the open to the pass remain owed by item
; RECLAIM-FOLD-CONTEXTS-CARRIED (owner Builder L).
(in-package "ACL2")
(include-book "owner-reclaim-retained")

(local
 (defthm fn-rfc-rev-onto
   (equal (fn-ag-rev-onto x acc) (revappend x acc))))

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

(local (defthm fn-rfc-nth-len-append (equal (nth (len b) (append b y)) (car y)) :hints (("Goal" :induct (len b)))))

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
 (defthm fn-rfc-len-from-tlf
   (implies (equal (true-list-fix x) y) (equal (len x) (len y)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable true-list-fix)))))

(local
 (defthm fn-rfc-len-arena-of-intern-event
   (implies (not (equal (fn-scka-intern-one w keyring generation h) :bad))
            (equal (len (mv-nth 1 (fn-intern-event w keyring generation fn-arena)))
                   (if (fn-scka-sealsp w) (+ 1 (len fn-arena)) (len fn-arena))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-rfc-tlf-arena-of-intern-event)
                  (:instance fn-rfc-len-from-tlf (x (mv-nth 1 (fn-intern-event w keyring generation fn-arena)))
                             (y (if (fn-scka-sealsp w)
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

; -----------------------------------------------------------------------------
; RECLAIM-FOLD-CONTEXTS-CARRIED, part (1): the reclaim rewrite keeps the
; premise (Builder L12, 2026-10-11).
;
; The pass rewrites a chunk (fn-orc-rewrite-rows) and predicts over the
; rewritten rows at the live arena's count.  A rewritten row is the tombstone
; of the record its wire decodes as.  The codec obstacle: a store event that
; is not a record must never decode as one, or the rewrite would turn a
; statement or keyring row into a record and move the identity the fold
; advances.  fn-rfc-only-a-record-decodes-as-a-record closes it: a record's
; decode accepts only the "fn-r" magic (books/records-seam.lisp
; fn-record-decode-exact-refuses-another-magic), and every other encoder's
; first five octets differ (retention, stxe, stxk and stxa lead with "fn-e",
; cpe with the raw "fnce", topics with "fnto").  A rewritten held or record
; row then becomes a record row whose intern is held at the same sequence,
; so the identity step agrees (fn-replay-identity-step reads a held row's
; sequence only), and a record row is not retained, so its context is not
; checked.  The premise does not depend on the handle counter
; (fn-rfc-fold-contexts-okp-any-handle), so the prediction's count may be the
; live arena's.
;
; KEYSTONE fn-rfc-the-rewrite-keeps-the-fold-contexts (at the live arena's
; count, as its consumer states the premise; any two natural counts:
; fn-rfc-the-rewrite-keeps-the-fold-contexts-any-handle).
; OWED (part 2): the owner's live appends after the open intern at the fold
; context of their position.

(local
 (defthm fn-rfc-step-of-held-rows
    (implies (and (fn-held-p x) (fn-held-p y)
                  (equal (fn-record-sequence x) (fn-record-sequence y)))
             (equal (fn-replay-identity-step ctx x)
                    (fn-replay-identity-step ctx y)))
    :hints (("Goal" :in-theory (enable fn-replay-identity-step fn-replay-identity-wire
                                       fn-store-event-sequence)
             :use ((:instance fn-held-is-no-wire-event (x x))
                   (:instance fn-held-is-no-wire-event (x y))
                   (:instance fn-hstxa-is-not-held (x x))
                   (:instance fn-hstxa-is-not-held (x y)))))
    :rule-classes nil))
(local
 (defthm fn-rfc-sequence-of-intern-row-at
    (equal (fn-record-sequence (fn-intern-row-at w k g h)) (fn-record-sequence w))
    :hints (("Goal" :in-theory (enable fn-intern-row-at)))))
(local
 (defthm fn-rfc-held-is-store-event
   (implies (fn-held-p x) (fn-store-event-p x))
   :hints (("Goal" :in-theory (enable fn-store-event-p)))))
(local
 (defthm fn-rfc-seed-generation-natp
   (natp (fn-ssr-at 2 (fn-ssr-seed id)))
   :rule-classes :type-prescription
   :hints (("Goal" :use ((:instance fn-ssr-seed-establishes-statep (identity id)))
            :in-theory (enable fn-ssr-statep)))))
(local
 (defthm fn-rfc-loop-of-intern-any-handle
   (implies (and (fn-record-p w) (natp h1) (natp h2))
            (equal (fn-replay-identity-loop (list (fn-intern-row-at w (fn-ssr-at 1 (fn-ssr-seed id)) (fn-ssr-at 2 (fn-ssr-seed id)) h1)) id)
                   (fn-replay-identity-loop (list (fn-intern-row-at w (fn-ssr-at 1 (fn-ssr-seed id)) (fn-ssr-at 2 (fn-ssr-seed id)) h2)) id)))
   :rule-classes nil
   :hints (("Goal" :expand ((:free (r) (fn-replay-identity-loop (list r) id)))
            :use ((:instance fn-rfc-step-of-held-rows (ctx id)
                   (x (fn-intern-row-at w (fn-ssr-at 1 (fn-ssr-seed id)) (fn-ssr-at 2 (fn-ssr-seed id)) h1))
                   (y (fn-intern-row-at w (fn-ssr-at 1 (fn-ssr-seed id)) (fn-ssr-at 2 (fn-ssr-seed id)) h2))))
            :in-theory (disable fn-intern-row-at fn-ssr-seed fn-ssr-at fn-replay-identity-step fn-record-p fn-store-event-p)))))
(local
 (defun fn-rfc-next (w id h)
   (declare (xargs :verify-guards nil))
   (let ((seed (fn-ssr-seed id)))
     (fn-replay-identity-loop
      (list (if (fn-record-p w) (fn-intern-row-at w (fn-ssr-at 1 seed) (fn-ssr-at 2 seed) h) w))
      id))))
(local
 (defun fn-rfc-ok1 (w id fn-arena)
   (declare (xargs :stobjs fn-arena :verify-guards nil))
   (let ((seed (fn-ssr-seed id)))
     (or (not (fn-orcr-retained-p w))
         (equal (fn-held-context (fn-orcr-held-part w))
                (fn-held-context-of (fn-row-bytes (fn-orcr-held-part w) fn-arena)
                                    (fn-ssr-at 1 seed) (fn-ssr-at 2 seed)))))))
(local
 (defthm fn-rfc-next-any-handle
   (implies (and (syntaxp (not (equal h ''0))) (natp h))
            (equal (fn-rfc-next w id h) (fn-rfc-next w id 0)))
   :hints (("Goal" :cases ((fn-record-p w))
            :in-theory (union-theories '(fn-rfc-next fn-rfc-seed-generation-natp natp)
                                       (theory 'minimal-theory)))
           ("Subgoal 1" :use ((:instance fn-rfc-loop-of-intern-any-handle (h1 h) (h2 0)))))))
(local
 (defthm fn-rfc-okp-unfold
   (implies (consp rows)
            (equal (fn-orcr-fold-contexts-okp rows id h fn-arena)
                   (and (fn-rfc-ok1 (car rows) id fn-arena)
                        (fn-orcr-fold-contexts-okp (cdr rows) (fn-rfc-next (car rows) id h)
                                                   (if (fn-record-p (car rows)) (+ 1 h) h) fn-arena))))
   :hints (("Goal" :in-theory (union-theories '(fn-orcr-fold-contexts-okp fn-rfc-ok1 fn-rfc-next)
                                              (theory 'minimal-theory))))))
(local
 (defun fn-rfc-okp-free (rows id fn-arena)
   (declare (xargs :stobjs fn-arena :verify-guards nil))
   (if (atom rows) t
     (and (fn-rfc-ok1 (car rows) id fn-arena)
          (fn-rfc-okp-free (cdr rows) (fn-rfc-next (car rows) id 0) fn-arena)))))
(local
 (defun fn-rfc-okpf-ind (rows id h)
   (declare (xargs :verify-guards nil))
   (if (atom rows) (list id h)
     (fn-rfc-okpf-ind (cdr rows) (fn-rfc-next (car rows) id 0) (if (fn-record-p (car rows)) (+ 1 h) h)))))
(local
 (defthm fn-rfc-okp-is-free
   (implies (natp h)
            (equal (fn-orcr-fold-contexts-okp rows id h fn-arena)
                   (fn-rfc-okp-free rows id fn-arena)))
   :hints (("Goal" :induct (fn-rfc-okpf-ind rows id h)
            :in-theory (disable fn-orcr-fold-contexts-okp fn-rfc-next fn-rfc-ok1 fn-record-p))
           ("Subgoal *1/1" :expand ((fn-orcr-fold-contexts-okp rows id h fn-arena))))))
(defthm fn-rfc-fold-contexts-okp-any-handle
  (implies (and (natp h1) (natp h2))
           (equal (fn-orcr-fold-contexts-okp rows id h1 fn-arena)
                  (fn-orcr-fold-contexts-okp rows id h2 fn-arena)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-rfc-okp-is-free) (fn-orcr-fold-contexts-okp fn-rfc-okp-free)))))
(local
 (defthm fn-rfc-stxe-prefix
   (implies (fn-stxe-p e) (not (equal (take 5 (fn-stxe-encode e)) *fn-record-magic-octets*)))
   :hints (("Goal" :in-theory (e/d (fn-stxe-encode fn-stxe-items fn-stxe-encode-items fn-stxe-encode-items-bounded) (fn-stxe-p))))))
(local
 (defthm fn-rfc-stxk-prefix
   (implies (fn-stxk-p e) (not (equal (take 5 (fn-stxk-encode e)) *fn-record-magic-octets*)))
   :hints (("Goal" :in-theory (e/d (fn-stxk-encode fn-stxk-items fn-stxe-encode-items fn-stxe-encode-items-bounded) (fn-stxk-p))))))
(local
 (defthm fn-rfc-stxa-prefix
   (implies (fn-stxa-p e) (not (equal (take 5 (fn-stxa-encode e)) *fn-record-magic-octets*)))
   :hints (("Goal" :in-theory (e/d (fn-stxa-encode fn-stxa-items fn-stxe-encode-items fn-stxe-encode-items-bounded) (fn-stxa-p))))))
(local
 (defthm fn-rfc-retention-prefix
   (implies (fn-store-retention-event-p e) (not (equal (take 5 (fn-store-retention-event-encode e)) *fn-record-magic-octets*)))
   :hints (("Goal" :in-theory (e/d (fn-store-retention-event-encode) (fn-store-retention-event-p))))))
(local
 (defthm fn-rfc-cpe-prefix
   (implies (fn-cpe-eventp e) (not (equal (take 5 (fn-cpe-encode e)) *fn-record-magic-octets*)))
   :hints (("Goal" :in-theory (e/d (fn-cpe-encode) (fn-cpe-eventp))))))
(local
 (defthm fn-rfc-topic-prefix
   (implies (fn-th-topic-eventp e) (not (equal (take 5 (fn-th-topic-event-encode e)) *fn-record-magic-octets*)))
   :hints (("Goal" :in-theory (e/d (fn-th-topic-event-encode fn-th-topic-event-items fn-stxe-encode-items) (fn-th-topic-eventp))))))
(local
 (defthm fn-rfc-non-record-encoding-prefix
   (implies (not (fn-record-p e))
            (not (equal (take 5 (fn-store-event-encode e)) *fn-record-magic-octets*)))
   :hints (("Goal" :in-theory (e/d (fn-store-event-encode) (fn-record-p fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p fn-cpe-eventp fn-th-topic-eventp
      fn-stxe-encode fn-stxk-encode fn-stxa-encode fn-cpe-encode fn-th-topic-event-encode fn-store-retention-event-encode))))))
(defthm fn-rfc-only-a-record-decodes-as-a-record
  (implies (fn-record-result-okp (fn-record-decode-exact (fn-store-event-encode e)))
           (and (fn-record-p e)
                (equal (fn-record-result-record (fn-record-decode-exact (fn-store-event-encode e))) e)))
  :hints (("Goal" :cases ((fn-record-p e))
           :use ((:instance fn-record-decode-exact-refuses-another-magic (octets (fn-store-event-encode e)))
                 (:instance fn-record-round-trip-succeeds (record e)))
           :in-theory (disable fn-record-p fn-store-event-encode))))
(local
 (defthm fn-rfc-held-wire-sequence
   (equal (fn-record-sequence (fn-held-wire h p)) (fn-record-sequence h))
   :hints (("Goal" :in-theory (enable fn-held-wire)))))
(local
 (defthm fn-rfc-stxa-is-not-record
   (implies (fn-stxa-p w) (not (fn-record-p w)))
   :hints (("Goal" :in-theory (enable fn-stxa-p fn-record-p fn-stxa-shapep fn-record-shapep)))))
(local
 (defthm fn-rfc-hstxa-wire-is-not-record
   (implies (fn-hstxa-p w) (not (fn-record-p (fn-hstxa-stxa w))))
   :hints (("Goal" :in-theory (e/d (fn-hstxa-p fn-hstxa-stxa) (fn-record-p fn-stxa-p fn-held-p))))))
(local
 (defthm fn-rfc-tombstoned-sequence
   (equal (fn-record-sequence (fn-rclp-tombstoned r)) (fn-record-sequence r))
   :hints (("Goal" :in-theory (enable fn-rclp-tombstoned)))))
(local
 (defthm fn-rfc-loop-of-held-rows
   (implies (and (fn-held-p x) (fn-held-p y)
                 (equal (fn-record-sequence x) (fn-record-sequence y)))
            (equal (fn-replay-identity-loop (list x) id)
                   (fn-replay-identity-loop (list y) id)))
   :rule-classes nil
   :hints (("Goal" :expand ((:free (r) (fn-replay-identity-loop (list r) id)))
            :use ((:instance fn-rfc-step-of-held-rows (ctx id)))
            :in-theory (disable fn-replay-identity-step fn-store-event-p fn-held-p)))))
(local
 (defthm fn-rfc-rewrite-row-when-rewritten
   (implies (fn-rclp-rewrites-p (fn-orc-row-octets w fn-arena) ctx)
            (and (fn-record-p (fn-row-wire-of w fn-arena))
                 (equal (fn-orc-rewrite-row w ctx fn-arena)
                        (fn-rclp-tombstoned (fn-row-wire-of w fn-arena)))
                 (fn-record-p (fn-orc-rewrite-row w ctx fn-arena))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-rfc-only-a-record-decodes-as-a-record
                                    (e (fn-row-wire-of w fn-arena))))
            :in-theory (e/d (fn-orc-rewrite-row fn-orc-row-octets fn-rclp-rewrites-p fn-record-result-okp fn-record-result-record)
                            (fn-record-p fn-row-wire-of fn-store-event-encode fn-rclp-tombstoned
                             fn-rclp-ctx-reclaimable fn-rcl-payload-profilep fn-rcl-tombstonep))))))
(local
 (defthm fn-rfc-rewrite-row-when-kept
   (implies (not (fn-rclp-rewrites-p (fn-orc-row-octets w fn-arena) ctx))
            (equal (fn-orc-rewrite-row w ctx fn-arena) w))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-orc-rewrite-row) (fn-rclp-rewrites-p fn-orc-row-octets))))))
(local
 (defthm fn-rfc-held-p-of-tomb-intern
   (implies (fn-record-p tt)
            (fn-held-p (fn-intern-row-at tt (fn-ssr-at 1 (fn-ssr-seed id)) (fn-ssr-at 2 (fn-ssr-seed id)) 0)))
   :hints (("Goal" :in-theory (disable fn-intern-row-at fn-record-p fn-held-p fn-ssr-seed fn-ssr-at)))))
(local
 (defthm fn-rfc-next-of-a-non-record
   (implies (not (fn-record-p w))
            (equal (fn-rfc-next w id h) (fn-replay-identity-loop (list w) id)))
   :hints (("Goal" :in-theory (union-theories '(fn-rfc-next) (theory 'minimal-theory))))))
(local
 (defthm fn-rfc-next-of-a-record
   (implies (fn-record-p w)
            (equal (fn-rfc-next w id h)
                   (fn-replay-identity-loop
                    (list (fn-intern-row-at w (fn-ssr-at 1 (fn-ssr-seed id)) (fn-ssr-at 2 (fn-ssr-seed id)) h)) id)))
   :hints (("Goal" :in-theory (union-theories '(fn-rfc-next) (theory 'minimal-theory))))))
(local
 (defthm fn-rfc-next-rewritten-held
   (implies (and (fn-held-p w)
                 (fn-rclp-rewrites-p (fn-orc-row-octets w fn-arena) ctx))
            (equal (fn-rfc-next (fn-orc-rewrite-row w ctx fn-arena) id 0)
                   (fn-rfc-next w id 0)))
   :hints (("Goal"
            :use ((:instance fn-rfc-rewrite-row-when-rewritten)
                  (:instance fn-rfc-held-is-not-record (x w))
                  (:instance fn-rfc-loop-of-held-rows
                             (x (fn-intern-row-at (fn-rclp-tombstoned (fn-row-wire-of w fn-arena))
                                                  (fn-ssr-at 1 (fn-ssr-seed id)) (fn-ssr-at 2 (fn-ssr-seed id)) 0))
                             (y w)))
            :in-theory (union-theories
                        '(fn-rfc-next-of-a-record fn-rfc-next-of-a-non-record fn-rfc-held-p-of-tomb-intern
                          fn-rfc-sequence-of-intern-row-at fn-rfc-tombstoned-sequence fn-rfc-held-wire-sequence
                          fn-row-wire-of)
                        (theory 'minimal-theory))))))
(local
 (defthm fn-rfc-next-rewritten-other
   (implies (and (not (fn-held-p w))
                 (fn-rclp-rewrites-p (fn-orc-row-octets w fn-arena) ctx))
            (equal (fn-rfc-next (fn-orc-rewrite-row w ctx fn-arena) id 0)
                   (fn-rfc-next w id 0)))
   :hints (("Goal"
            :use ((:instance fn-rfc-rewrite-row-when-rewritten)
                  (:instance fn-rfc-hstxa-wire-is-not-record)
                  (:instance fn-rfc-loop-of-held-rows
                             (x (fn-intern-row-at (fn-rclp-tombstoned w)
                                                  (fn-ssr-at 1 (fn-ssr-seed id)) (fn-ssr-at 2 (fn-ssr-seed id)) 0))
                             (y (fn-intern-row-at w (fn-ssr-at 1 (fn-ssr-seed id)) (fn-ssr-at 2 (fn-ssr-seed id)) 0))))
            :in-theory (union-theories
                        '(fn-rfc-next-of-a-record fn-rfc-next-of-a-non-record fn-rfc-held-p-of-tomb-intern
                          fn-rfc-sequence-of-intern-row-at fn-rfc-tombstoned-sequence
                          fn-row-wire-of)
                        (theory 'minimal-theory))))))
(local
 (defthm fn-rfc-next-of-rewrite-row
   (equal (fn-rfc-next (fn-orc-rewrite-row w ctx fn-arena) id 0)
          (fn-rfc-next w id 0))
   :hints (("Goal" :cases ((and (fn-rclp-rewrites-p (fn-orc-row-octets w fn-arena) ctx) (fn-held-p w))
                           (and (fn-rclp-rewrites-p (fn-orc-row-octets w fn-arena) ctx) (not (fn-held-p w))))
            :use ((:instance fn-rfc-rewrite-row-when-kept))
            :in-theory (union-theories '(fn-rfc-next-rewritten-held fn-rfc-next-rewritten-other)
                                       (theory 'minimal-theory))))))
(local
 (defthm fn-rfc-record-is-not-retained
   (implies (fn-record-p x) (not (fn-orcr-retained-p x)))
   :hints (("Goal" :use ((:instance fn-rfc-stxa-is-not-record (w x)))
            :in-theory (enable fn-orcr-retained-p fn-hstxa-p fn-record-p fn-record-shapep fn-held-p fn-held-shapep fn-record-payloadp)))))
(local
 (defthm fn-rfc-ok1-of-a-record
   (implies (fn-record-p x) (fn-rfc-ok1 x id fn-arena))
   :hints (("Goal" :in-theory (union-theories '(fn-rfc-ok1 fn-rfc-record-is-not-retained) (theory 'minimal-theory))))))
(local
 (defthm fn-rfc-ok1-of-rewrite-row
   (implies (fn-rfc-ok1 w id fn-arena)
            (fn-rfc-ok1 (fn-orc-rewrite-row w ctx fn-arena) id fn-arena))
   :hints (("Goal" :cases ((fn-rclp-rewrites-p (fn-orc-row-octets w fn-arena) ctx))
            :use ((:instance fn-rfc-rewrite-row-when-rewritten) (:instance fn-rfc-rewrite-row-when-kept))
            :in-theory (union-theories '(fn-rfc-ok1-of-a-record) (theory 'minimal-theory))))))
(local
 (defthm fn-rfc-okp-free-of-rewrite
   (implies (fn-rfc-okp-free rows id fn-arena)
            (fn-rfc-okp-free (fn-orc-rewrite-rows rows ctx fn-arena) id fn-arena))
   :hints (("Goal" :induct (fn-rfc-okp-free rows id fn-arena)
            :in-theory (e/d (fn-orc-rewrite-rows) (fn-orc-rewrite-row fn-rfc-next fn-rfc-ok1 fn-rclp-rewrites-p fn-orc-row-octets))))))
(defthm fn-rfc-the-rewrite-keeps-the-fold-contexts-any-handle
  (implies (and (natp h) (natp h2)
                (fn-orcr-fold-contexts-okp rows id h fn-arena))
           (fn-orcr-fold-contexts-okp (fn-orc-rewrite-rows rows ctx fn-arena) id h2 fn-arena))
  :hints (("Goal" :in-theory (e/d (fn-rfc-okp-is-free) (fn-orc-rewrite-rows fn-rfc-okp-free fn-orcr-fold-contexts-okp)))))

; KEYSTONE, in the terms of its consumer (fn-orcs-predict-rows-at-refines-the-
; replay states the premise at the live arena's count): the rows the pass
; predicts, rewritten, keep the premise the unrewritten rows had.
(defthm fn-rfc-the-rewrite-keeps-the-fold-contexts
  (implies (fn-orcr-fold-contexts-okp rows id (fn-arena-count fn-arena) fn-arena)
           (fn-orcr-fold-contexts-okp (fn-orc-rewrite-rows rows ctx fn-arena) id
                                      (fn-arena-count fn-arena) fn-arena))
  :hints (("Goal" :use ((:instance fn-rfc-the-rewrite-keeps-the-fold-contexts-any-handle
                                   (h (fn-arena-count fn-arena)) (h2 (fn-arena-count fn-arena))))
           :in-theory (disable fn-rfc-the-rewrite-keeps-the-fold-contexts-any-handle
                               fn-orcr-fold-contexts-okp fn-orc-rewrite-rows))))
