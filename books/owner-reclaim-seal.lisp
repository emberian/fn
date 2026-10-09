; fn: the reclaim pass seals its tombstones only when the swap is taken
; (lane arena-forget, 2026-10-03; row "deferred reclaim leaks sealed
; tombstone payloads", Astra c08).
;
; The pass used to intern the rewritten rows' tombstoned records into the
; live arena in owner quanta BEFORE the swap loop (fn-orcp-intern-rows,
; books/owner-reclaim-pass.lisp), then defer by name when the swap word
; answered :delta, :busy or :readers.  A deferred pass finished without the
; swap, so its fresh handles were named by no row and released by nothing:
; every deferred reclaim grew the arena by its tombstones, for the life of
; the process.
;
; Now the pass PREDICTS the interned rows off the mutex (fn-orcs-predict:
; each record row is the held record fn-cat-intern-list makes, at handle
; BASE + i, where BASE is the live arena's count read under the mutex), and
; the swap quantum seals the predicted payloads (fn-orcs-seal) only after
; fn-orcs-seal-word answered :swap -- which needs the arena's count to still
; be BASE.  A deferred pass has sealed nothing.
;
; KEYSTONE fn-orcs-seal-is-the-intern: over an arena whose count is BASE,
; the predicted rows are exactly the rows fn-orcp-intern-rows answers and
; the sealed arena is exactly the arena it leaves.  So the rebuild, the
; catalog and the history columns made off the mutex from the predicted
; rows describe the arena the swap quantum makes, as they described the
; interned one before.
; KEYSTONE fn-orcs-seal-word-swap-means-base: a :swap from the seal word
; means the swap word answered :swap and the count is BASE.

(in-package "ACL2")
(include-book "owner-reclaim-pass")

; -----------------------------------------------------------------------------
; 1. The prediction.

; Each row is predicted from the identity BEFORE that event. A one-row
; replay uses the same invalid-record fault as the capture accumulator.
(defun fn-orcs-predict-rows-at (rows id h)
  (declare (xargs :guard (natp h)
                  :guard-hints (("Goal" :in-theory (enable fn-ssr-statep)))))
  (if (atom rows)
      nil
    (let* ((w (car rows))
           (seed (fn-ssr-seed id))
           (row (if (fn-record-p w)
                    (fn-intern-row-at w (fn-ssr-at 1 seed) (fn-ssr-at 2 seed) h)
                  w)))
      (cons row
            (fn-orcs-predict-rows-at
             (cdr rows) (fn-replay-identity-loop (list row) id)
             (if (fn-record-p w) (+ 1 h) h))))))

(defun fn-orcs-payloads (rows)
  (declare (xargs :guard t))
  (cond ((atom rows) nil)
        ((fn-record-p (car rows))
         (cons (fn-record-payload (car rows)) (fn-orcs-payloads (cdr rows))))
        (t (fn-orcs-payloads (cdr rows)))))

(defun fn-orcs-predict-loop (rows id h racc pacc)
  (declare (xargs :guard (and (natp h) (true-listp racc) (true-listp pacc))
                  :guard-hints (("Goal" :in-theory (enable fn-ssr-statep)))))
  (if (atom rows)
      (list (revappend racc nil) (revappend pacc nil))
    (let* ((w (car rows))
           (seed (fn-ssr-seed id))
           (row (if (fn-record-p w)
                    (fn-intern-row-at w (fn-ssr-at 1 seed) (fn-ssr-at 2 seed) h)
                  w)))
      (fn-orcs-predict-loop
       (cdr rows) (fn-replay-identity-loop (list row) id)
       (if (fn-record-p w) (+ 1 h) h)
       (cons row racc)
       (if (fn-record-p w) (cons (fn-record-payload w) pacc) pacc)))))

; Whether a row IS the intern's refusal word (any value; no list needed).
(defun fn-orcs-has-bad (rows)
  (declare (xargs :guard t))
  (and (consp rows)
       (or (eq (car rows) :bad)
           (fn-orcs-has-bad (cdr rows)))))

; The host's call, off the owner mutex: (list ROWS PAYLOADS), or (list :bad
; nil) when a row is the intern's refusal word itself (the intern answered
; :bad then; the host defers :unencodable, as before).
(defun fn-orcs-predict (rows id h)
  (declare (xargs :guard (natp h)
                  :verify-guards nil))
  (if (fn-orcs-has-bad rows)
      (list :bad nil)
    (mbe :logic (list (fn-orcs-predict-rows-at rows id h)
                      (fn-orcs-payloads rows))
         :exec (fn-orcs-predict-loop rows id h nil nil))))

(defthm fn-orcs-predict-loop-is-predict
  (equal (fn-orcs-predict-loop rows id h racc pacc)
         (list (revappend racc (fn-orcs-predict-rows-at rows id h))
               (revappend pacc (fn-orcs-payloads rows)))))

(verify-guards fn-orcs-predict)

; -----------------------------------------------------------------------------
; 2. The seal, in the swap quantum.

(defun fn-orcs-payload-listp (ps)
  (declare (xargs :guard t))
  (if (atom ps)
      (null ps)
    (and (fn-cbor-octet-listp (car ps))
         (fn-orcs-payload-listp (cdr ps)))))

; The host's call under the owner mutex: every payload sealed in order.
; (Not fn-arn-seal-many: its guard asks for the payload list's recognizer,
; which the host's argument does not carry; here each seal's guard is
; checked as the loop goes.)
(defun fn-orcs-seal (payloads fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (cond ((atom payloads) fn-arena)
        ((fn-cbor-octet-listp (car payloads))
         (let ((fn-arena (fn-arena-seal-list (car payloads) fn-arena)))
           (fn-orcs-seal (cdr payloads) fn-arena)))
        (t (fn-orcs-seal (cdr payloads) fn-arena))))

; -----------------------------------------------------------------------------
; 3. The prediction is the intern.

(local
 (defthm fn-orcs-record-payload-octets
   (implies (fn-record-p w)
            (fn-cbor-octet-listp (fn-record-payload w)))
   :hints (("Goal" :in-theory (enable fn-record-p fn-record-payloadp)))))

(local
 (defthm fn-orcs-seal-is-the-intern-at
   (implies (not (fn-orcs-has-bad rows))
            (equal (fn-orcp-intern-rows-at rows id h fn-arena)
                   (mv (fn-orcs-predict-rows-at rows id h)
                       (fn-orcs-seal (fn-orcs-payloads rows) fn-arena))))
   :hints (("Goal" :induct (fn-orcp-intern-rows-at rows id h fn-arena)
            :in-theory (disable fn-intern-row-at fn-replay-identity-loop
                                fn-ssr-seed fn-ssr-at fn-record-p
                                fn-arena-seal-list-is-append fn-arena-count-is-len)))))

; KEYSTONE. No row is the intern's refusal word itself.
(defthm fn-orcs-seal-is-the-intern
  (implies (not (fn-orcs-has-bad rows))
           (equal (fn-orcp-intern-rows rows id fn-arena)
                  (mv (fn-orcs-predict-rows-at rows id (fn-arena-count fn-arena))
                      (fn-orcs-seal (fn-orcs-payloads rows) fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-orcp-intern-rows)
                                  (fn-orcp-intern-rows-at fn-orcs-predict-rows-at
                                   fn-orcs-seal fn-orcs-payloads)))))

; Boundary of the host-called tuple prediction and its arena sealing effect.
(defthm fn-orcs-predict-seal-refines-intern
  (implies (not (fn-orcs-has-bad rows))
           (equal (fn-orcp-intern-rows rows id fn-arena)
                  (mv (car (fn-orcs-predict rows id
                                           (fn-arena-count fn-arena)))
                      (fn-orcs-seal
                       (cadr (fn-orcs-predict rows id
                                             (fn-arena-count fn-arena)))
                       fn-arena))))
  :hints (("Goal"
           :use ((:instance fn-orcs-seal-is-the-intern))
           :in-theory (e/d (fn-orcs-predict)
                           (fn-orcs-seal-is-the-intern fn-orcp-intern-rows
                            fn-orcs-seal fn-orcs-predict-rows-at fn-orcs-payloads)))))

; -----------------------------------------------------------------------------
; 4. The seal word.

; WORD the swap word (fn-owner-orcp-swap-word); COUNT the live arena's count
; now; BASE the count the prediction used.  A :swap over an arena some other
; seal moved (a POST prepare's staged buffer) is deferred by name (:moved):
; the predicted handles would be wrong, and nothing has been sealed.
(defun fn-orcs-seal-word (word count base)
  (declare (xargs :guard t))
  (if (and (eq word :swap) (not (equal count base)))
      :moved
    word))

(defthm fn-orcs-seal-word-swap-means-base
  (implies (equal (fn-orcs-seal-word word count base) :swap)
           (and (equal word :swap)
                (equal count base)))
  :rule-classes nil)

; Any other answer seals nothing: the host seals only on :swap, so a
; deferred pass leaves the arena as it found it.
(defthm fn-orcs-seal-word-otherwise-is-word-or-moved
  (implies (not (equal (fn-orcs-seal-word word count base) :swap))
           (member-equal (fn-orcs-seal-word word count base)
                         (list word :moved)))
  :rule-classes nil)

(defthm fn-orcs-predict-rows-at-true-listp
  (true-listp (fn-orcs-predict-rows-at rows id h))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (disable fn-intern-row-at fn-replay-identity-loop
                                     fn-ssr-seed fn-ssr-at fn-record-p))))

(local
 (defthm fn-orcs-identity-loop-cons
   (implies (and (true-listp xs) (syntaxp (not (equal xs ''nil))))
            (equal (fn-replay-identity-loop (cons x xs) id)
                   (fn-replay-identity-loop xs (fn-replay-identity-loop (list x) id))))
   :hints (("Goal" :use ((:instance fn-replay-identity-append-of-true-lists
                                    (prefix (list x)) (suffix xs) (ctx id)))
            :in-theory (disable fn-replay-identity-append-of-true-lists
                                fn-replay-identity-loop)))))

(local
 (defthm fn-orcs-identity-loop-nil
   (equal (fn-replay-identity-loop nil id) id)
   :hints (("Goal" :in-theory (enable fn-replay-identity-loop)))))

(defthm fn-orcs-predict-rows-at-of-append
  (implies (natp h)
           (equal (fn-orcs-predict-rows-at (append a b) id h)
                  (append
                   (fn-orcs-predict-rows-at a id h)
                   (fn-orcs-predict-rows-at
                    b (fn-replay-identity-loop (fn-orcs-predict-rows-at a id h) id)
                    (+ h (len (fn-orcs-payloads a)))))))
  :hints (("Goal" :induct (fn-orcs-predict-rows-at a id h)
           :in-theory (disable fn-intern-row-at fn-replay-identity-loop
                               fn-ssr-seed fn-ssr-at fn-record-p))))

; Exactly the fold's plain-record and unchanged-wire-event arms.
(defun fn-orcs-fold-rowsp (rows)
  (declare (xargs :guard t))
  (if (atom rows)
      (null rows)
    (and (or (fn-record-p (car rows))
             (and (not (fn-stxa-p (car rows))) (fn-wire-event-p (car rows))))
         (fn-orcs-fold-rowsp (cdr rows)))))

(local
 (defthm fn-orcs-rev-onto
   (equal (fn-ag-rev-onto x acc) (revappend x acc))))

(local
 (defthm fn-orcs-rows-of-publish
   (equal (fn-ssr-rows (fn-ssr-publish acc row wire id))
          (append (fn-ssr-rows acc) (list row)))
   :hints (("Goal" :in-theory (enable fn-ssr-publish fn-ssr-rows fn-ssr-state fn-ssr-at)))))
(local
 (defthm fn-orcs-id-of-publish
   (equal (fn-ssr-at 3 (fn-ssr-publish acc row wire id)) id)
   :hints (("Goal" :in-theory (enable fn-ssr-publish fn-ssr-state fn-ssr-at)))))
(local
 (defthm fn-orcs-rows-true-listp
   (implies (not (equal acc :bad)) (true-listp (fn-ssr-rows acc)))
   :hints (("Goal" :in-theory (enable fn-ssr-rows)))))
(local
 (defthm fn-orcs-invp-parts
   (implies (fn-scka-invp acc)
            (and (not (equal acc :bad))
                 (natp (fn-ssr-at 2 acc))
                 (equal (fn-ssr-at 1 (fn-ssr-seed (fn-ssr-at 3 acc)))
                        (fn-ssr-at 1 acc))
                 (equal (fn-ssr-at 2 (fn-ssr-seed (fn-ssr-at 3 acc)))
                        (fn-ssr-at 2 acc))))
   :hints (("Goal" :in-theory (enable fn-scka-invp fn-ssr-statep fn-ssr-seed
                                     fn-ssr-state fn-ssr-at)))))
(local
 (defthm fn-orcs-loop-one-is-step
   (implies (fn-store-event-p row)
            (equal (fn-replay-identity-loop (list row) id)
                   (fn-replay-identity-step id row)))
   :hints (("Goal" :in-theory (e/d (fn-replay-identity-loop)
                                   (fn-store-event-p fn-replay-identity-step))))))

(local
 (defthm fn-orcs-predict-is-fold-from
   (implies (and (fn-orcs-fold-rowsp rows) (fn-scka-invp acc) (natp h)
                 (not (equal (fn-scka-fold-at acc rows h) :bad)))
            (equal (fn-ssr-rows (fn-scka-fold-at acc rows h))
                   (append (fn-ssr-rows acc)
                           (fn-orcs-predict-rows-at rows (fn-ssr-at 3 acc) h))))
   :hints (("Goal" :induct (fn-scka-fold-at acc rows h)
            :in-theory (e/d (fn-scka-fold-at fn-scka-intern-one fn-scka-sealsp)
                            (fn-intern-row-at fn-ssr-seed fn-ssr-at fn-ssr-publish
                             fn-ssr-rows fn-scka-invp fn-record-p fn-stxa-p
                             fn-wire-event-p fn-store-event-p fn-replay-identity-step
                             fn-replay-identity-loop fn-stxk-context-kind)))
           (and stable-under-simplificationp
                '(:use ((:instance fn-scka-invp-of-publish (wire (car rows)))
                        (:instance fn-scka-intern-one-is-store-event
                         (w (car rows)) (k (fn-ssr-at 1 acc)) (g (fn-ssr-at 2 acc)))))))))

; KEYSTONE: exact row equality with the replay fold, handles included.
(defthm fn-orcs-predict-rows-at-is-the-fold
  (implies (and (fn-orcs-fold-rowsp rows) (natp h)
                (not (equal (fn-scka-intern-at rows id h) :bad)))
           (equal (fn-orcs-predict-rows-at rows id h)
                  (fn-scka-intern-at rows id h)))
  :hints (("Goal" :use ((:instance fn-orcs-predict-is-fold-from
                                  (acc (fn-ssr-seed id))))
           :in-theory (e/d (fn-scka-intern-at fn-ssr-rows)
                           (fn-scka-fold-at fn-orcs-predict-rows-at
                            fn-ssr-at fn-ssr-seed fn-orcs-predict-is-fold-from)))))
