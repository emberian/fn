; fn: the reclaim prediction over a MIXED history refines the replay of its
; wire projection (repair item OWNER-RECLAIM-PREDICT-RETAINED-ROWS-BRIDGE).
;
; The reclaim pass predicts its rows off the mutex (books/owner-reclaim-seal.lisp
; fn-orcs-predict-rows-at): each plain record of the rewritten history (a
; tombstone) is interned at the seed of the identity before it and at the next
; handle of the live arena; every other row is kept as it is.  The rewritten
; history is mixed: besides the tombstones it keeps the store's RETAINED rows,
; held articles (fn-held-p) and accepted-statement rows (fn-hstxa-p), whose
; handles point into the live arena and whose contexts were decided when they
; were interned.  fn-orcs-predict-rows-at-is-the-fold covers only histories
; with no retained row (fn-orcs-fold-rowsp).  A restart does not see the
; predicted rows; it replays their wire projection (fn-rows-wire-of, books/
; store-intern.lisp) through the fold (fn-scka-fold-at, books/
; store-checkpoint-fold.lisp), which re-interns every article at a fresh handle
; of the replay arena and in the fold context.
;
; KEYSTONE fn-orcs-predict-rows-at-refines-the-replay: when every retained
; row's context is the one the fold decides at its position
; (fn-orcr-fold-contexts-okp), the predicted rows over the sealed live arena
; and the replay's rows over the replay arena stand for the same wire events
; (so each article's handle reads the same bytes on both sides), and they
; carry the same contexts, row by row.  The context premise has teeth: a row
; recontexted at a later keyring generation, as fn-sn-set-keyring does
; (books/store-node.lisp), is a history whose prediction serves a context the
; restart does not (tests/acl2/store-checkpoint-fold-tests.lisp).
(in-package "ACL2")
(include-book "owner-reclaim-seal")
(include-book "history-fold-refinement")

; -----------------------------------------------------------------------------
; 1. The vocabulary.

(defun fn-orcr-retained-p (row)
  (declare (xargs :guard t))
  (or (fn-held-p row) (fn-hstxa-p row)))

; The held record a retained row carries: itself, or a statement row's article.
(defun fn-orcr-held-part (row)
  (declare (xargs :guard t))
  (if (fn-hstxa-p row) (fn-hstxa-held row) row))

; Row by row, the context a retained row carries; :none for any other row.
(defun fn-orcr-contexts (rows)
  (declare (xargs :guard t))
  (if (atom rows)
      nil
    (cons (if (fn-orcr-retained-p (car rows))
              (fn-held-context (fn-orcr-held-part (car rows)))
            :none)
          (fn-orcr-contexts (cdr rows)))))

; Every retained row's context is the context of its bytes under the keyring
; and generation of the seed of the identity before it: the context the fold
; decides at that position.  The identity advances as the predictor's does.
(defun fn-orcr-fold-contexts-okp (rows id h fn-arena)
  (declare (xargs :stobjs fn-arena :guard (natp h) :verify-guards nil))
  (if (atom rows)
      t
    (let* ((w (car rows))
           (seed (fn-ssr-seed id))
           (k (fn-ssr-at 1 seed))
           (g (fn-ssr-at 2 seed))
           (row (if (fn-record-p w) (fn-intern-row-at w k g h) w)))
      (and (or (not (fn-orcr-retained-p w))
               (equal (fn-held-context (fn-orcr-held-part w))
                      (fn-held-context-of (fn-row-bytes (fn-orcr-held-part w) fn-arena) k g)))
           (fn-orcr-fold-contexts-okp (cdr rows) (fn-replay-identity-loop (list row) id)
                                      (if (fn-record-p w) (+ 1 h) h) fn-arena)))))

; -----------------------------------------------------------------------------
; 2. One row: the fold's row and the predicted row advance the identity alike
; and carry the same context.

(local
 (defthm fn-orcr-step-of-held-rows
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
 (defthm fn-orcr-step-of-hstxa-rows
   (implies (and (fn-hstxa-p x) (fn-hstxa-p y)
                 (equal (fn-hstxa-stxa x) (fn-hstxa-stxa y)))
            (equal (fn-replay-identity-step ctx x)
                   (fn-replay-identity-step ctx y)))
   :hints (("Goal" :in-theory (enable fn-replay-identity-step fn-replay-identity-wire
                                      fn-store-event-sequence)
            :use ((:instance fn-hstxa-is-not-held (x x))
                  (:instance fn-hstxa-is-not-held (x y)))))
   :rule-classes nil))

(local
 (defthm fn-orcr-contexts-of-append
   (equal (fn-orcr-contexts (append a b))
          (append (fn-orcr-contexts a) (fn-orcr-contexts b)))))

(local
 (defthm fn-orcr-context-of-intern-row-at
   (equal (fn-held-context (fn-intern-row-at w k g h))
          (fn-held-context-of (fn-record-payload w) k g))
   :hints (("Goal" :in-theory (enable fn-intern-row-at)))))

(local
 (defthm fn-orcr-sequence-of-intern-row-at
   (equal (fn-record-sequence (fn-intern-row-at w k g h))
          (fn-record-sequence w))
   :hints (("Goal" :in-theory (enable fn-intern-row-at)))))

(local
 (defthm fn-orcr-payload-of-intern-row-at
   (equal (fn-record-payload (fn-intern-row-at w k g h)) h)
   :hints (("Goal" :in-theory (enable fn-intern-row-at)))))

(local
 (defthm fn-orcr-held-p-of-intern-row-at
   (implies (and (fn-record-p w) (natp g) (natp h))
            (fn-held-p (fn-intern-row-at w k g h)))
   :hints (("Goal" :in-theory (enable fn-intern-row-at fn-record-p fn-held-p fn-record-internals
                                      fn-held-internals fn-hf-p fn-hc-p
                                      fn-hf-startp fn-hc-verdictp)))))

(local
 (defthm fn-orcr-held-wire-payload
   (equal (fn-record-payload (fn-held-wire h p)) p)
   :hints (("Goal" :in-theory (enable fn-held-wire)))))

(local
 (defthm fn-orcr-held-wire-sequence
   (equal (fn-record-sequence (fn-held-wire h p)) (fn-record-sequence h))
   :hints (("Goal" :in-theory (enable fn-held-wire)))))

(local
 (defthm fn-orcr-row-identity
   (implies (and (fn-row-composite-okp r a) (natp g) (natp hf) (natp g2) (natp hp)
                 (not (equal (fn-scka-intern-one (fn-row-wire-of r a) k g hf) :bad)))
            (equal (fn-replay-identity-step
                    id (fn-scka-intern-one (fn-row-wire-of r a) k g hf))
                   (fn-replay-identity-loop
                    (list (if (fn-record-p r) (fn-intern-row-at r k2 g2 hp) r)) id)))
   :hints (("Goal" :cases ((fn-record-p r) (fn-held-p r) (fn-hstxa-p r))
            :in-theory (e/d (fn-scka-intern-one fn-row-composite-okp fn-row-wire-of
                             fn-replay-identity-loop (:d fn-store-event-p) (:d fn-wire-event-p))
                            (fn-intern-row-at fn-held-wire fn-replay-identity-step
                             fn-held-p fn-hstxa-p fn-record-p fn-stxa-p fn-stxk-p fn-stxe-p
                             fn-store-retention-event-p fn-cpe-eventp fn-th-topic-eventp
                             fn-replay-composite-record fn-row-bytes))
            :use ((:instance fn-held-is-no-wire-event (x r))
                  (:instance fn-hstxa-is-no-wire-event (x r))
                  (:instance fn-hstxa-is-not-held (x r))
                  (:instance fn-hfr-held-wire-is-no-composite (h r) (payload (fn-row-bytes r a)))
                  (:instance fn-orcr-step-of-held-rows (ctx id)
                             (x (fn-intern-row-at r k g hf)) (y (fn-intern-row-at r k2 g2 hp)))
                  (:instance fn-orcr-step-of-held-rows (ctx id)
                             (x (fn-intern-row-at (fn-held-wire r (fn-row-bytes r a)) k g hf)) (y r))
                  (:instance fn-orcr-step-of-hstxa-rows (ctx id)
                             (x (fn-hstxa-make (fn-hstxa-stxa r)
                                               (fn-intern-row-at (fn-replay-composite-record
                                                                  (fn-hstxa-stxa r))
                                                                 k g hf)))
                             (y r)))))
   :rule-classes nil))

(local
 (defthm fn-orcr-row-context
   (implies (and (fn-row-composite-okp r a) (natp g) (natp hf) (natp hp)
                 (or (not (fn-orcr-retained-p r))
                     (equal (fn-held-context (fn-orcr-held-part r))
                            (fn-held-context-of (fn-row-bytes (fn-orcr-held-part r) a) k g)))
                 (not (equal (fn-scka-intern-one (fn-row-wire-of r a) k g hf) :bad)))
            (equal (fn-orcr-contexts (list (fn-scka-intern-one (fn-row-wire-of r a) k g hf)))
                   (fn-orcr-contexts (list (if (fn-record-p r) (fn-intern-row-at r k g hp) r)))))
   :hints (("Goal" :cases ((fn-record-p r) (fn-held-p r) (fn-hstxa-p r))
            :in-theory (e/d (fn-scka-intern-one fn-row-composite-okp fn-row-wire-of
                             (:d fn-wire-event-p))
                            (fn-intern-row-at fn-held-wire fn-replay-identity-step
                             fn-held-p fn-hstxa-p fn-record-p fn-stxa-p fn-stxk-p fn-stxe-p
                             fn-store-retention-event-p fn-cpe-eventp fn-th-topic-eventp
                             fn-replay-composite-record fn-row-bytes fn-held-context-of))
            :use ((:instance fn-held-is-no-wire-event (x r))
                  (:instance fn-hstxa-is-no-wire-event (x r))
                  (:instance fn-hstxa-is-not-held (x r))
                  (:instance fn-hfr-held-wire-is-no-composite (h r) (payload (fn-row-bytes r a)))
                  (:instance fn-orcr-held-wire-payload (h (fn-hstxa-held r))
                             (p (fn-row-bytes (fn-hstxa-held r) a))))))
   :rule-classes nil))

; -----------------------------------------------------------------------------
; 3. The contexts: the fold over the wire projection, from any invariant
; state, appends the predicted rows' contexts.

(local
 (defun fn-orcr-ind (rows acc hp hf fn-arena)
   (declare (xargs :stobjs fn-arena :measure (len rows) :verify-guards nil))
   (if (atom rows)
       (list acc hp hf)
     (let* ((wire (fn-row-wire-of (car rows) fn-arena))
            (row (fn-scka-intern-one wire (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) hf))
            (identity (fn-replay-identity-step (fn-ssr-at 3 acc) row)))
       (fn-orcr-ind (cdr rows) (fn-ssr-publish acc row wire identity)
                    (if (fn-record-p (car rows)) (+ 1 hp) hp)
                    (if (fn-scka-sealsp wire) (+ 1 hf) hf) fn-arena)))))

(local
 (defthm fn-orcr-rev-onto
   (equal (fn-ag-rev-onto x acc) (revappend x acc))))
(local
 (defthm fn-orcr-rows-of-publish
   (equal (fn-ssr-rows (fn-ssr-publish acc row wire id))
          (append (fn-ssr-rows acc) (list row)))
   :hints (("Goal" :in-theory (enable fn-ssr-publish fn-ssr-rows fn-ssr-state fn-ssr-at)))))
(local
 (defthm fn-orcr-id-of-publish
   (equal (fn-ssr-at 3 (fn-ssr-publish acc row wire id)) id)
   :hints (("Goal" :in-theory (enable fn-ssr-publish fn-ssr-state fn-ssr-at)))))
(local
 (defthm fn-orcr-invp-parts
   (implies (fn-scka-invp acc)
            (and (not (equal acc :bad))
                 (natp (fn-ssr-at 2 acc))
                 (equal (fn-ssr-at 1 (fn-ssr-seed (fn-ssr-at 3 acc))) (fn-ssr-at 1 acc))
                 (equal (fn-ssr-at 2 (fn-ssr-seed (fn-ssr-at 3 acc))) (fn-ssr-at 2 acc))))
   :hints (("Goal" :in-theory (enable fn-scka-invp fn-ssr-statep fn-ssr-seed fn-ssr-state
                                      fn-ssr-at)))))
(local
 (defthm fn-orcr-wire-of-cons
   (equal (fn-rows-wire-of (cons r rows) fn-arena)
          (cons (fn-row-wire-of r fn-arena) (fn-rows-wire-of rows fn-arena)))))
(local
 (defthm fn-orcr-wire-of-atom
   (implies (atom rows) (equal (fn-rows-wire-of rows fn-arena) nil))))

(local
 (defthm fn-orcr-contexts-from
   (implies (and (fn-rows-composites-okp rows fn-arena)
                 (fn-orcr-fold-contexts-okp rows (fn-ssr-at 3 acc) hp fn-arena)
                 (fn-scka-invp acc) (natp hp) (natp hf)
                 (not (equal (fn-scka-fold-at acc (fn-rows-wire-of rows fn-arena) hf) :bad)))
            (equal (fn-orcr-contexts
                    (fn-ssr-rows (fn-scka-fold-at acc (fn-rows-wire-of rows fn-arena) hf)))
                   (append (fn-orcr-contexts (fn-ssr-rows acc))
                           (fn-orcr-contexts
                            (fn-orcs-predict-rows-at rows (fn-ssr-at 3 acc) hp)))))
   :hints (("Goal" :induct (fn-orcr-ind rows acc hp hf fn-arena)
            :do-not '(generalize fertilize eliminate-destructors)
            :expand ((fn-rows-wire-of rows fn-arena))
            :in-theory (e/d (fn-scka-fold-at fn-rows-composites-okp)
                            (fn-intern-row-at fn-ssr-seed fn-ssr-at fn-ssr-publish fn-row-wire-of
                             fn-ssr-rows fn-scka-invp fn-record-p fn-stxa-p fn-scka-intern-one
                             fn-wire-event-p fn-store-event-p fn-replay-identity-step
                             fn-replay-identity-loop fn-stxk-context-kind fn-scka-sealsp
                             fn-orcr-retained-p fn-orcr-held-part fn-row-bytes
                             fn-held-context-of fn-rows-wire-of fn-row-composite-okp)))
           (and stable-under-simplificationp
                '(:use ((:instance fn-scka-invp-of-publish
                                   (wire (fn-row-wire-of (car rows) fn-arena)) (h hf))
                        (:instance fn-orcr-row-identity (r (car rows)) (a fn-arena)
                                   (id (fn-ssr-at 3 acc))
                                   (k (fn-ssr-at 1 acc)) (g (fn-ssr-at 2 acc))
                                   (k2 (fn-ssr-at 1 acc)) (g2 (fn-ssr-at 2 acc)))
                        (:instance fn-orcr-row-context (r (car rows)) (a fn-arena)
                                   (k (fn-ssr-at 1 acc)) (g (fn-ssr-at 2 acc)))))))))

; -----------------------------------------------------------------------------
; 4. The wire: the predicted rows over the sealed arena, and the fold's rows
; over the replay arena, stand for the wire projection.

(local
 (defthm fn-orcr-held-wire-of-intern-row-at
   (implies (fn-record-p w)
            (equal (fn-held-wire (fn-intern-row-at w k g h) (fn-record-payload w)) w))
   :hints (("Goal" :in-theory (e/d (fn-intern-row-at fn-held-wire fn-record-p)
                                   (fn-held-wire-of-wire-record))
            :use ((:instance fn-held-wire-of-wire-record))))))

(local
 (defthm fn-orcr-nth-of-append-low
   (implies (and (natp n) (< n (len a)))
            (equal (nth n (append a b)) (nth n a)))))
(local
 (defthm fn-orcr-nth-of-append-at-len
   (equal (nth (len a) (append a b)) (car b))))
(local
 (defthm fn-orcr-row-bytes-of-append
   (implies (fn-row-handle-inp h a)
            (equal (fn-row-bytes h (append a b)) (fn-row-bytes h a)))
   :hints (("Goal" :in-theory (enable fn-row-bytes fn-row-handle-inp)))))
(local
 (defthm fn-orcr-handle-inp-of-append
   (implies (fn-row-handle-inp h a) (fn-row-handle-inp h (append a b)))
   :hints (("Goal" :in-theory (enable fn-row-handle-inp)))))
(local
 (defthm fn-orcr-handles-inp-of-append
   (implies (fn-rows-handles-inp rows a) (fn-rows-handles-inp rows (append a b)))
   :hints (("Goal" :in-theory (e/d (fn-rows-handles-inp) (fn-row-handle-inp))))))
(local
 (defthm fn-orcr-rows-wire-of-of-append-arena
   (implies (fn-rows-handles-inp rows a)
            (equal (fn-rows-wire-of rows (append a b)) (fn-rows-wire-of rows a)))
   :hints (("Goal" :in-theory (e/d (fn-rows-handles-inp fn-row-wire-of)
                                   (fn-row-handle-inp fn-row-bytes fn-held-wire))))))
(local
 (defthm fn-orcr-rows-wire-of-append
   (equal (fn-rows-wire-of (append x y) fn-arena)
          (append (fn-rows-wire-of x fn-arena) (fn-rows-wire-of y fn-arena)))))

(local
 (defun fn-orcr-pind (rows id a)
   (declare (xargs :verify-guards nil))
   (if (atom rows)
       (list id a)
     (let* ((w (car rows))
            (seed (fn-ssr-seed id))
            (row (if (fn-record-p w)
                     (fn-intern-row-at w (fn-ssr-at 1 seed) (fn-ssr-at 2 seed) (len a))
                   w)))
       (fn-orcr-pind (cdr rows) (fn-replay-identity-loop (list row) id)
                     (if (fn-record-p w) (append a (list (fn-record-payload w))) a))))))

(local
 (defthm fn-orcr-len-append-one
   (equal (len (append a (list x))) (+ 1 (len a)))))

(local
 (defthm fn-orcr-held-p-of-intern-row-at-seed
   (implies (and (fn-record-p w) (natp h))
            (fn-held-p (fn-intern-row-at w (fn-ssr-at 1 (fn-ssr-seed id))
                                         (fn-ssr-at 2 (fn-ssr-seed id)) h)))
   :hints (("Goal" :use ((:instance fn-orcp-seed-pair)
                         (:instance fn-orcr-held-p-of-intern-row-at
                                    (k (fn-ssr-at 1 (fn-ssr-seed id)))
                                    (g (fn-ssr-at 2 (fn-ssr-seed id)))))
            :in-theory (disable fn-orcr-held-p-of-intern-row-at fn-orcp-seed-pair
                                fn-intern-row-at fn-ssr-seed fn-ssr-at fn-held-p)))))

(local
 (defthm fn-orcr-predict-wire
   (implies (fn-rows-handles-inp rows a)
            (equal (fn-rows-wire-of (fn-orcs-predict-rows-at rows id (len a))
                                    (append a (fn-orcs-payloads rows)))
                   (fn-rows-wire-of rows a)))
   :hints (("Goal" :induct (fn-orcr-pind rows id a)
            :in-theory (e/d (fn-rows-handles-inp fn-row-wire-of fn-row-bytes fn-row-handle-inp)
                            (fn-intern-row-at fn-ssr-seed fn-ssr-at fn-record-p fn-held-p
                             fn-hstxa-p fn-replay-identity-loop fn-held-wire)))
           (and stable-under-simplificationp
                '(:use ((:instance fn-orcr-rows-wire-of-of-append-arena
                                   (rows (cdr rows))
                                   (b (list (fn-record-payload (car rows)))))))))))

(local
 (defthm fn-orcr-row-wire-of-fold-row
   (implies (and (natp g) (natp hf) (equal hf (len r0))
                 (not (equal (fn-scka-intern-one w k g hf) :bad)))
            (equal (fn-row-wire-of (fn-scka-intern-one w k g hf)
                                   (append r0 (if (fn-scka-sealsp w)
                                                  (cons (fn-scka-payload-of w) rest)
                                                rest)))
                   w))
   :hints (("Goal" :cases ((fn-record-p w) (fn-stxa-p w))
            :in-theory (e/d (fn-scka-intern-one fn-scka-sealsp fn-scka-payload-of fn-row-wire-of
                             fn-row-bytes (:d fn-wire-event-p))
                            (fn-intern-row-at fn-held-wire fn-held-p fn-hstxa-p fn-record-p
                             fn-stxa-p fn-stxk-p fn-stxe-p fn-store-retention-event-p
                             fn-cpe-eventp fn-th-topic-eventp fn-replay-composite-record))
            :use ((:instance fn-hstxa-is-no-wire-event (x w))
                  (:instance fn-held-is-no-wire-event (x w)))))))

(local
 (defun fn-orcr-find (acc ws r0)
   (declare (xargs :measure (len ws) :verify-guards nil))
   (cond ((or (eq acc :bad) (eq ws :bad)) (list acc r0))
         ((atom ws) (list acc r0))
         (t (let* ((wire (car ws))
                   (row (fn-scka-intern-one wire (fn-ssr-at 1 acc) (fn-ssr-at 2 acc) (len r0)))
                   (identity (fn-replay-identity-step (fn-ssr-at 3 acc) row)))
              (fn-orcr-find (fn-ssr-publish acc row wire identity) (cdr ws)
                            (if (fn-scka-sealsp wire)
                                (append r0 (list (fn-scka-payload-of wire)))
                              r0)))))))

(local
 (defthm fn-orcr-append-assoc-one
   (equal (append (append r0 (list x)) y) (append r0 (cons x y)))))

(local
 (defthm fn-orcr-fold-wire
   (implies (and (fn-scka-invp acc)
                 (not (equal (fn-scka-fold-at acc ws (len r0)) :bad)))
            (equal (fn-rows-wire-of (fn-ssr-rows (fn-scka-fold-at acc ws (len r0)))
                                    (append r0 (append (fn-scka-payloads ws) tail)))
                   (append (fn-rows-wire-of (fn-ssr-rows acc)
                                            (append r0 (append (fn-scka-payloads ws) tail)))
                           ws)))
   :hints (("Goal" :induct (fn-orcr-find acc ws r0)
            :in-theory (e/d (fn-scka-fold-at fn-scka-payloads)
                            (fn-intern-row-at fn-ssr-seed fn-ssr-at fn-ssr-publish fn-row-wire-of
                             fn-ssr-rows fn-scka-invp fn-record-p fn-stxa-p fn-scka-intern-one
                             fn-wire-event-p fn-store-event-p fn-replay-identity-step
                             fn-stxk-context-kind fn-scka-sealsp fn-scka-payload-of)))
           (and stable-under-simplificationp
                '(:use ((:instance fn-scka-invp-of-publish (wire (car ws)) (h (len r0)))
                        (:instance fn-orcr-row-wire-of-fold-row (w (car ws)) (hf (len r0))
                                   (k (fn-ssr-at 1 acc)) (g (fn-ssr-at 2 acc))
                                   (rest (append (fn-scka-payloads (cdr ws)) tail)))))))))

(local
 (defthm fn-orcr-payloads-octets
   (fn-arn-payload-listp (fn-orcs-payloads rows))
   :hints (("Goal" :in-theory (enable fn-record-p fn-record-payloadp)))))

(local
 (defthm fn-orcr-snoc
   (equal (fn-oct-snoc xs o) (append (true-list-fix xs) (list o)))
   :hints (("Goal" :in-theory (enable fn-oct-snoc)))))

(local
 (defthm fn-orcr-tlf-of-payload-list
   (implies (fn-arn-payload-listp ps) (equal (true-list-fix ps) ps))))

; The host's seal of the predicted payloads appends them to the live arena.
(local
 (defthm fn-orcr-seal-is-append
   (implies (fn-arn-payload-listp ps)
            (equal (true-list-fix (fn-orcs-seal ps fn-arena))
                   (append (true-list-fix fn-arena) ps)))
   :hints (("Goal" :induct (fn-orcs-seal ps fn-arena)
            :in-theory (enable fn-orcs-seal fn-arena-seal-list fn-arena$a-seal-list)))))

; A row's wire form reads the arena only through its length and its elements.
(local
 (defthm fn-orcr-wire-of-tlf
   (equal (fn-rows-wire-of rows (true-list-fix a)) (fn-rows-wire-of rows a))
   :hints (("Goal" :in-theory (enable fn-row-wire-of fn-row-bytes)))))

(local
 (defthm fn-orcr-tlf-append
   (implies (true-listp b)
            (equal (append (true-list-fix a) b) (true-list-fix (append a b))))))

; -----------------------------------------------------------------------------
; 5. KEYSTONE.  FN-ARENA is the live arena the prediction reads; R0 is the
; replay arena before the fold (empty for a full open).

(defthm fn-orcs-predict-rows-at-refines-the-replay
  (implies (and (fn-rows-handles-inp rows fn-arena)
                (fn-rows-composites-okp rows fn-arena)
                (fn-orcr-fold-contexts-okp rows id (fn-arena-count fn-arena) fn-arena)
                (not (equal (fn-scka-intern-at (fn-rows-wire-of rows fn-arena) id (len r0))
                            :bad)))
           (and (equal (fn-rows-wire-of (fn-orcs-predict-rows-at rows id (fn-arena-count fn-arena))
                                        (fn-orcs-seal (fn-orcs-payloads rows) fn-arena))
                       (fn-rows-wire-of rows fn-arena))
                (equal (fn-rows-wire-of (fn-scka-intern-at (fn-rows-wire-of rows fn-arena) id
                                                           (len r0))
                                        (append r0 (fn-scka-payloads
                                                    (fn-rows-wire-of rows fn-arena))))
                       (fn-rows-wire-of rows fn-arena))
                (equal (fn-orcr-contexts (fn-orcs-predict-rows-at rows id
                                                                  (fn-arena-count fn-arena)))
                       (fn-orcr-contexts (fn-scka-intern-at (fn-rows-wire-of rows fn-arena) id
                                                            (len r0))))))
  :hints (("Goal" :use ((:instance fn-orcr-predict-wire (a fn-arena))
                        (:instance fn-orcr-wire-of-tlf
                                   (rows (fn-orcs-predict-rows-at rows id (len fn-arena)))
                                   (a (append fn-arena (fn-orcs-payloads rows))))
                        (:instance fn-orcr-wire-of-tlf
                                   (rows (fn-orcs-predict-rows-at rows id (len fn-arena)))
                                   (a (fn-orcs-seal (fn-orcs-payloads rows) fn-arena)))
                        (:instance fn-orcr-fold-wire (acc (fn-ssr-seed id))
                                   (ws (fn-rows-wire-of rows fn-arena)) (tail nil))
                        (:instance fn-orcr-contexts-from (acc (fn-ssr-seed id))
                                   (hp (len fn-arena)) (hf (len r0))))
           :in-theory (e/d (fn-scka-intern-at)
                           (fn-orcr-predict-wire fn-orcr-fold-wire fn-orcr-contexts-from
                            fn-orcr-wire-of-tlf fn-scka-fold-at fn-orcs-predict-rows-at fn-rows-wire-of
                            fn-orcr-fold-contexts-okp fn-orcr-contexts fn-ssr-seed fn-ssr-at
                            fn-rows-handles-inp fn-rows-composites-okp fn-orcs-seal)))))
