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

; The held record fn-cat-intern-list makes from W at handle H, without
; sealing.
(defun fn-orcs-held-of (w keyring generation h)
  (declare (xargs :guard (and (fn-record-p w) (fn-prin-keyringp keyring) (natp generation))
                  :guard-hints (("Goal" :in-theory (enable fn-record-p fn-record-payloadp)))))
  (let ((bytes (fn-record-payload w)))
    (fn-held-make (fn-record-sequence w) (fn-record-txid w)
                  (fn-record-generation w) (fn-record-msgid w) h
                  (fn-record-groups w) (fn-record-obligation-id w)
                  (fn-record-content-subject w) (fn-record-release-evidence w)
                  (fn-record-charge w) (fn-record-stamp w)
                  (fn-held-facts-of bytes)
                  (fn-held-context-of bytes keyring generation)
                  nil nil)))

(defthm fn-orcs-intern-list-is-held-of
  (equal (fn-cat-intern-list w keyring generation fn-arena)
         (mv (fn-orcs-held-of w keyring generation (fn-arena-count fn-arena))
             (fn-arena-seal-list (fn-record-payload w) fn-arena)))
  :hints (("Goal" :in-theory (enable fn-cat-intern-list))))

(in-theory (disable fn-orcs-held-of))

; The predicted rows and, in order, the payloads the swap seals.  Executes
; by a loop (the rewritten rows are store data).
(defun fn-orcs-predict-rows (rows keyring generation h)
  (declare (xargs :guard (and (fn-prin-keyringp keyring) (natp generation) (natp h))))
  (cond ((atom rows) nil)
        ((fn-record-p (car rows))
         (cons (fn-orcs-held-of (car rows) keyring generation h)
               (fn-orcs-predict-rows (cdr rows) keyring generation (+ 1 h))))
        (t (cons (car rows) (fn-orcs-predict-rows (cdr rows) keyring generation h)))))

(defun fn-orcs-payloads (rows)
  (declare (xargs :guard t))
  (cond ((atom rows) nil)
        ((fn-record-p (car rows))
         (cons (fn-record-payload (car rows)) (fn-orcs-payloads (cdr rows))))
        (t (fn-orcs-payloads (cdr rows)))))

(defun fn-orcs-predict-loop (rows keyring generation h racc pacc)
  (declare (xargs :guard (and (fn-prin-keyringp keyring) (natp generation) (natp h)
                              (true-listp racc) (true-listp pacc))))
  (cond ((atom rows) (list (revappend racc nil) (revappend pacc nil)))
        ((fn-record-p (car rows))
         (fn-orcs-predict-loop (cdr rows) keyring generation (+ 1 h)
                               (cons (fn-orcs-held-of (car rows) keyring generation h) racc)
                               (cons (fn-record-payload (car rows)) pacc)))
        (t (fn-orcs-predict-loop (cdr rows) keyring generation h
                                 (cons (car rows) racc) pacc))))

; Whether a row IS the intern's refusal word (any value; no list needed).
(defun fn-orcs-has-bad (rows)
  (declare (xargs :guard t))
  (and (consp rows)
       (or (eq (car rows) :bad)
           (fn-orcs-has-bad (cdr rows)))))

; The host's call, off the owner mutex: (list ROWS PAYLOADS), or (list :bad
; nil) when a row is the intern's refusal word itself (the intern answered
; :bad then; the host defers :unencodable, as before).
(defun fn-orcs-predict (rows keyring generation h)
  (declare (xargs :guard (and (fn-prin-keyringp keyring) (natp generation) (natp h))
                  :verify-guards nil))
  (if (fn-orcs-has-bad rows)
      (list :bad nil)
    (mbe :logic (list (fn-orcs-predict-rows rows keyring generation h)
                      (fn-orcs-payloads rows))
         :exec (fn-orcs-predict-loop rows keyring generation h nil nil))))

(defthm fn-orcs-predict-loop-is-predict
  (equal (fn-orcs-predict-loop rows keyring generation h racc pacc)
         (list (revappend racc (fn-orcs-predict-rows rows keyring generation h))
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

; KEYSTONE.  The hypothesis is the predict's own test (a row that IS the
; word :bad makes the intern answer :bad).
(defthm fn-orcs-seal-is-the-intern
  (implies (not (fn-orcs-has-bad rows))
  (equal (fn-orcp-intern-rows rows keyring generation fn-arena)
         (mv (fn-orcs-predict-rows rows keyring generation (fn-arena-count fn-arena))
             (fn-orcs-seal (fn-orcs-payloads rows) fn-arena))))
  :hints (("Goal" :induct (fn-orcp-intern-rows rows keyring generation fn-arena)
           :in-theory (e/d (fn-intern-event) (fn-arena-seal-list-is-append
                                              fn-arena-count-is-len)))))

; Boundary of the host-called tuple prediction and its arena sealing effect.
(defthm fn-orcs-predict-seal-refines-intern
  (implies (not (fn-orcs-has-bad rows))
           (equal (fn-orcp-intern-rows rows keyring generation fn-arena)
                  (mv (car (fn-orcs-predict rows keyring generation
                                           (fn-arena-count fn-arena)))
                      (fn-orcs-seal
                       (cadr (fn-orcs-predict rows keyring generation
                                             (fn-arena-count fn-arena)))
                       fn-arena))))
  :hints (("Goal"
           :use ((:instance fn-orcs-seal-is-the-intern))
           :in-theory (e/d (fn-orcs-predict)
                           (fn-orcs-seal-is-the-intern fn-orcp-intern-rows
                            fn-orcs-seal fn-orcs-predict-rows fn-orcs-payloads)))))

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
