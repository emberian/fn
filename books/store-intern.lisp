; fn: THE INTERN AT THE ENTRIES (records-flip, 2026-09-27; PKT-635; D27).
;
; The store machine (books/store-node.lisp) retains ROWS: an article is a held
; record whose payload position holds a handle into the arena
; (books/held-record.lisp, books/payload-arena.lisp), an accepted statement
; is the wire composite beside its article interned (fn-hstxa-p).  The wire
; events the codec decodes (fn-wire-event-p, books/store-events.lisp) never
; reach the machine: every entry interns first, and this book is that
; intern and its theorems.
;
;   fn-intern-event / fn-intern-events   a decoded wire event (the journal open,
;                                        the checkpoint's suffix, a transit
;                                        record) to its row; the payload sealed
;                                        once, the byte facts and the context
;                                        decided from the bytes under the
;                                        keyring and generation in force.
;   fn-row-wire-of / fn-rows-wire-of     ALPHA: the wire event a row stands for,
;                                        read through the arena.
;   fn-contexts-of-rows                  the rows' contexts under a NEW keyring
;                                        (fn-sn-set-keyring zips them: the one
;                                        reconfiguration that re-reads bytes).
;   fn-store-set-keyring                 that entry.
;
; KEYSTONES.  (1) alpha of the intern is the identity: the rows materialize
; to the wire events they were interned from (fn-intern-events-materializes).
; (2) The rows are retained events with the wire events' coordinates
; (fn-intern-events-are-store-events, fn-intern-events-keep-coordinates), so
; the history's shape facts (fn-sn-observed-historyp) read the same on
; both views.  (3) Every row's context is the context of its bytes under the
; keyring and generation of the intern (fn-intern-events-contexts-okp), which
; is what makes the store's index fold over rows (fn-sn-index-of-rows) the
; wire view's index (fn-stx-index-of-store; books/records-freeze.lisp's
; fn-rfz-replay-index-over-both-views is the theorem, restated here over
; the retained history in fn-rows-index-is-the-wire-index).
;
; The keyring at open is NIL and the generation 0 (books/config-observed.lisp
; opens with fn-stx-index-of-store ... nil; the seed's generation is 0); the
; host installs the operator's keyring afterwards through
; fn-store-set-keyring, which recontexts every row through the arena.
(in-package "ACL2")
(include-book "catalog-record")
(include-book "store-node")

; -----------------------------------------------------------------------------
; 1. One wire event to its row.

(defun fn-intern-event (w keyring generation fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (fn-prin-keyringp keyring) (natp generation))))
  (cond ((fn-record-p w) (fn-cat-intern-list w keyring generation fn-arena))
        ((fn-stxa-p w)
         (let ((a (fn-replay-composite-record w)))
           (if (fn-record-p a)
               (mv-let (held fn-arena)
                 (fn-cat-intern-list a keyring generation fn-arena)
                 (mv (fn-hstxa-make w held) fn-arena))
             (mv :bad fn-arena))))
        ((fn-wire-event-p w) (mv w fn-arena))
        (t (mv :bad fn-arena))))

; The events in order; :bad if any is refused (a composite whose article does
; not decode, or a value the codec does not produce).
(defun fn-intern-events (ws keyring generation fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (fn-prin-keyringp keyring) (natp generation))))
  (if (atom ws)
      (mv nil fn-arena)
    (mv-let (row fn-arena)
      (fn-intern-event (car ws) keyring generation fn-arena)
      (if (eq row :bad)
          (mv :bad fn-arena)
        (mv-let (rest fn-arena)
          (fn-intern-events (cdr ws) keyring generation fn-arena)
          (if (eq rest :bad)
              (mv :bad fn-arena)
            (mv (cons row rest) fn-arena)))))))

; -----------------------------------------------------------------------------
; 2. ALPHA.  A row's bytes (total: a handle outside the arena reads as no
; bytes), the wire event a row stands for, the rows' wire events.

(defun fn-row-bytes (h fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (and (natp (fn-record-payload h))
           (< (fn-record-payload h) (fn-arena-count fn-arena)))
      (fn-arena-payload (fn-record-payload h) fn-arena)
    nil))

(defun fn-row-wire-of (row fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (cond ((fn-held-p row) (fn-held-wire row (fn-row-bytes row fn-arena)))
        ((fn-hstxa-p row) (fn-hstxa-stxa row))
        (t row)))

(defun fn-rows-wire-of (rows fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (atom rows)
      nil
    (cons (fn-row-wire-of (car rows) fn-arena)
          (fn-rows-wire-of (cdr rows) fn-arena))))

; -----------------------------------------------------------------------------
; 3. The context invariant, and the recontext for a new keyring.

; Every article row's context, and every composite row's article's, is the
; context of its bytes under KEYRING and GENERATION.
(defun fn-row-context-okp (h keyring generation fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (fn-prin-keyringp keyring) (natp generation))))
  (equal (fn-held-context h)
         (fn-held-context-of (fn-row-bytes h fn-arena) keyring generation)))

(defun fn-rows-contexts-okp (rows keyring generation fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (fn-prin-keyringp keyring) (natp generation))))
  (cond ((atom rows) t)
        ((fn-held-p (car rows))
         (and (fn-row-context-okp (car rows) keyring generation fn-arena)
              (fn-rows-contexts-okp (cdr rows) keyring generation fn-arena)))
        ((fn-hstxa-p (car rows))
         (and (fn-row-context-okp (fn-hstxa-held (car rows)) keyring generation fn-arena)
              (fn-rows-contexts-okp (cdr rows) keyring generation fn-arena)))
        (t (fn-rows-contexts-okp (cdr rows) keyring generation fn-arena))))

; The contexts fn-sn-set-keyring zips onto the rows (books/store-node.lisp
; fn-sn-recontext-rows): one per article or composite row, oldest first.
(defun fn-contexts-of-rows (rows keyring generation fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (fn-prin-keyringp keyring) (natp generation))))
  (cond ((atom rows) nil)
        ((fn-held-p (car rows))
         (cons (fn-held-context-of (fn-row-bytes (car rows) fn-arena) keyring generation)
               (fn-contexts-of-rows (cdr rows) keyring generation fn-arena)))
        ((fn-hstxa-p (car rows))
         (cons (fn-held-context-of (fn-row-bytes (fn-hstxa-held (car rows)) fn-arena)
                                   keyring generation)
               (fn-contexts-of-rows (cdr rows) keyring generation fn-arena)))
        (t (fn-contexts-of-rows (cdr rows) keyring generation fn-arena))))

; The entry: the store's keyring installed, every row recontexted through
; the arena.  Refused (S unchanged) outside :ready or for a malformed keyring,
; by fn-sn-set-keyring.
(defun fn-store-set-keyring (s keyring fn-arena)
  (declare (xargs :stobjs fn-arena :guard (fn-sn-statep s)
                  :guard-hints (("Goal" :in-theory (e/d (fn-sn-statep) (fn-sf-statep fn-node-statep))))))
  (if (fn-prin-keyringp keyring)
      (fn-sn-set-keyring s keyring
                         (fn-contexts-of-rows (fn-sf-records (fn-sn-files s)) keyring
                                              (1+ (fn-sn-keyring-generation s)) fn-arena))
    s))

; -----------------------------------------------------------------------------
; 4. THE THEOREMS.

(local (in-theory (enable fn-sn-row-delta fn-sn-index-fold fn-sn-index-of-rows)))

; A row's handle is inside the arena.
(defun fn-row-handle-inp (h fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (and (natp (fn-record-payload h))
       (< (fn-record-payload h) (fn-arena-count fn-arena))))

(defun fn-rows-handles-inp (rows fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (cond ((atom rows) t)
        ((fn-held-p (car rows))
         (and (fn-row-handle-inp (car rows) fn-arena)
              (fn-rows-handles-inp (cdr rows) fn-arena)))
        ((fn-hstxa-p (car rows))
         (and (fn-row-handle-inp (fn-hstxa-held (car rows)) fn-arena)
              (fn-rows-handles-inp (cdr rows) fn-arena)))
        (t (fn-rows-handles-inp (cdr rows) fn-arena))))

; The arena's logical view (books/payload-arena.lisp): a list of payloads, a
; seal an append, a read an nth.  What a row reads survives every later seal.
(local (defthm fn-row-bytes-survives-seal
  (implies (and (fn-arena-p fn-arena) (fn-row-handle-inp h fn-arena))
           (equal (fn-row-bytes h (fn-arena-seal-list xs fn-arena))
                  (fn-row-bytes h fn-arena)))
  :hints (("Goal" :in-theory (enable fn-row-bytes fn-row-handle-inp)))))

(local (defthm fn-row-handle-inp-survives-seal
  (implies (and (fn-arena-p fn-arena) (fn-row-handle-inp h fn-arena))
           (fn-row-handle-inp h (fn-arena-seal-list xs fn-arena)))
  :hints (("Goal" :in-theory (enable fn-row-handle-inp)))))

(local (defthm fn-arena-p-of-seal-list
  (implies (and (fn-arena-p fn-arena) (fn-cbor-octet-listp xs))
           (fn-arena-p (fn-arena-seal-list xs fn-arena)))
  :hints (("Goal" :in-theory (enable fn-arena-p-is-payload-listp fn-arn-payload-listp)))))

; -- 4.1 One event.

; The row is a retained event, or :bad.
(defthm fn-intern-event-is-store-event
  (implies (and (natp generation)
                (not (equal (mv-nth 0 (fn-intern-event w keyring generation fn-arena)) :bad)))
           (fn-store-event-p (mv-nth 0 (fn-intern-event w keyring generation fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-intern-event fn-store-event-p fn-wire-event-p)
                                  (fn-cat-intern-list)))))

; The row reads the wire event's coordinates.
(defthm fn-intern-event-keeps-coordinates
  (implies (and (natp generation)
                (not (equal (mv-nth 0 (fn-intern-event w keyring generation fn-arena)) :bad)))
           (let ((row (mv-nth 0 (fn-intern-event w keyring generation fn-arena))))
             (and (equal (fn-store-event-sequence row) (fn-wire-event-sequence w))
                  (equal (fn-store-event-txid row) (fn-wire-event-txid w))
                  (equal (fn-store-event-generation row) (fn-wire-event-generation w))
                  (equal (fn-store-event-kind row) (fn-wire-event-kind w)))))
  :hints (("Goal" :in-theory (e/d (fn-intern-event fn-store-event-p fn-wire-event-p
                                   fn-store-event-sequence fn-wire-event-sequence
                                   fn-store-event-txid fn-wire-event-txid
                                   fn-store-event-generation fn-wire-event-generation
                                   fn-store-event-kind fn-wire-event-kind
                                   fn-cat-intern-list)
                                  ()))))

; The new arena is the old one with the row's bytes sealed (the wire record's
; payload, or the composite's article's), or unchanged.
(defthm fn-intern-event-arena
  (equal (mv-nth 1 (fn-intern-event w keyring generation fn-arena))
         (cond ((fn-record-p w) (fn-arena-seal-list (fn-record-payload w) fn-arena))
               ((and (fn-stxa-p w) (fn-record-p (fn-replay-composite-record w)))
                (fn-arena-seal-list (fn-record-payload (fn-replay-composite-record w)) fn-arena))
               (t fn-arena)))
  :hints (("Goal" :in-theory (enable fn-intern-event))))

; The row's handle is in the new arena.
(defthm fn-intern-event-handle-in
  (implies (and (fn-arena-p fn-arena) (natp generation)
                (not (equal (mv-nth 0 (fn-intern-event w keyring generation fn-arena)) :bad)))
           (fn-rows-handles-inp (list (mv-nth 0 (fn-intern-event w keyring generation fn-arena)))
                                (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-intern-event fn-row-handle-inp fn-wire-event-p
                                   fn-store-event-p)
                                  (fn-cat-intern-list)))))

; ALPHA of one row is its wire event (KEYSTONE 1, one event).
(defthm fn-intern-event-materializes
  (implies (and (fn-arena-p fn-arena) (natp generation)
                (not (equal (mv-nth 0 (fn-intern-event w keyring generation fn-arena)) :bad)))
           (equal (fn-row-wire-of (mv-nth 0 (fn-intern-event w keyring generation fn-arena))
                                  (mv-nth 1 (fn-intern-event w keyring generation fn-arena)))
                  w))
  :hints (("Goal" :in-theory (e/d (fn-intern-event fn-row-wire-of fn-row-bytes
                                   fn-wire-event-p fn-store-event-p fn-record-p)
                                  (fn-cat-intern-list fn-arena-payload-is-nth
                                   fn-arena-count-is-len fn-arena-seal-list-is-append))
           :use ((:instance fn-cat-intern-list-materializes)
                 (:instance fn-cat-intern-list-materializes (w (fn-replay-composite-record w)))
                 (:instance fn-arena-seal-new-handle (xs (fn-record-payload w)))
                 (:instance fn-arena-seal-new-handle
                            (xs (fn-record-payload (fn-replay-composite-record w))))))))

; The row's context is the context of its bytes (KEYSTONE 3, one event).
(defthm fn-intern-event-context-okp
  (implies (and (fn-arena-p fn-arena) (natp generation)
                (not (equal (mv-nth 0 (fn-intern-event w keyring generation fn-arena)) :bad)))
           (fn-rows-contexts-okp (list (mv-nth 0 (fn-intern-event w keyring generation fn-arena)))
                                 keyring generation
                                 (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-intern-event fn-row-context-okp fn-row-bytes
                                   fn-wire-event-p fn-store-event-p fn-cat-intern-list)
                                  (fn-arena-payload-is-nth fn-arena-count-is-len
                                   fn-arena-seal-list-is-append))
           :use ((:instance fn-arena-seal-new-handle (xs (fn-record-payload w)))
                 (:instance fn-arena-seal-new-handle
                            (xs (fn-record-payload (fn-replay-composite-record w))))))))

; -- 4.2 The list.

; What a row reads is stable under every later seal, so a list interned in
; order materializes to its wire events in the final arena (KEYSTONE 1).
(local (defthm fn-row-wire-of-survives-seal
  (implies (and (fn-arena-p fn-arena) (fn-rows-handles-inp (list row) fn-arena))
           (equal (fn-row-wire-of row (fn-arena-seal-list xs fn-arena))
                  (fn-row-wire-of row fn-arena)))
  :hints (("Goal" :in-theory (enable fn-row-wire-of fn-rows-handles-inp)))))

(local (defthm fn-rows-handles-inp-survives-seal
  (implies (and (fn-arena-p fn-arena) (fn-rows-handles-inp rows fn-arena))
           (fn-rows-handles-inp rows (fn-arena-seal-list xs fn-arena)))
  :hints (("Goal" :induct (fn-rows-handles-inp rows fn-arena)
           :in-theory (enable fn-rows-handles-inp)))))

(local (defthm fn-rows-contexts-okp-survives-seal
  (implies (and (fn-arena-p fn-arena) (fn-rows-handles-inp rows fn-arena)
                (fn-rows-contexts-okp rows keyring generation fn-arena))
           (fn-rows-contexts-okp rows keyring generation (fn-arena-seal-list xs fn-arena)))
  :hints (("Goal" :induct (fn-rows-handles-inp rows fn-arena)
           :in-theory (enable fn-rows-handles-inp fn-rows-contexts-okp fn-row-context-okp)))))

(local (defthm fn-rows-wire-of-survives-seal
  (implies (and (fn-arena-p fn-arena) (fn-rows-handles-inp rows fn-arena))
           (equal (fn-rows-wire-of rows (fn-arena-seal-list xs fn-arena))
                  (fn-rows-wire-of rows fn-arena)))
  :hints (("Goal" :induct (fn-rows-handles-inp rows fn-arena)
           :in-theory (enable fn-rows-handles-inp fn-rows-wire-of fn-row-wire-of)))))

; The intern of one event seals at most one octet list, so the arena stays one.
(local (defthm fn-arena-p-of-intern-event
  (implies (and (fn-arena-p fn-arena) (fn-wire-event-p w))
           (fn-arena-p (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-intern-event fn-wire-event-p fn-record-p fn-record-payloadp)
                                  (fn-cat-intern-list fn-arena-seal-list-is-append))))))

(defun fn-wire-event-listp (ws)
  (declare (xargs :guard t))
  (if (atom ws) (null ws) (and (fn-wire-event-p (car ws)) (fn-wire-event-listp (cdr ws)))))

(defthm fn-intern-events-arena-p
  (implies (and (fn-arena-p fn-arena) (fn-wire-event-listp ws))
           (fn-arena-p (mv-nth 1 (fn-intern-events ws keyring generation fn-arena))))
  :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
           :in-theory (e/d (fn-intern-events) (fn-intern-event)))))

(defthm fn-intern-events-handles-in
  (implies (and (fn-arena-p fn-arena) (natp generation) (fn-wire-event-listp ws)
                (not (equal (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)) :bad)))
           (fn-rows-handles-inp (mv-nth 0 (fn-intern-events ws keyring generation fn-arena))
                                (mv-nth 1 (fn-intern-events ws keyring generation fn-arena))))
  :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
           :in-theory (e/d (fn-intern-events fn-rows-handles-inp)
                           (fn-intern-event fn-row-handle-inp)))))

; KEYSTONE 1: alpha of the intern is the identity on the wire events.
(defthm fn-intern-events-materializes
  (implies (and (fn-arena-p fn-arena) (natp generation) (fn-wire-event-listp ws)
                (not (equal (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)) :bad)))
           (equal (fn-rows-wire-of (mv-nth 0 (fn-intern-events ws keyring generation fn-arena))
                                   (mv-nth 1 (fn-intern-events ws keyring generation fn-arena)))
                  ws))
  :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
           :in-theory (e/d (fn-intern-events fn-rows-wire-of)
                           (fn-intern-event fn-row-wire-of fn-rows-handles-inp)))))

; KEYSTONE 2: the rows are retained events with the wire events' coordinates.
(defun fn-wire-coordinates (ws)
  (declare (xargs :guard t))
  (if (atom ws) nil
    (cons (list (fn-wire-event-kind (car ws)) (fn-wire-event-sequence (car ws))
                (fn-wire-event-txid (car ws)) (fn-wire-event-generation (car ws)))
          (fn-wire-coordinates (cdr ws)))))

(defun fn-row-coordinates (rows)
  (declare (xargs :guard t))
  (if (atom rows) nil
    (cons (list (fn-store-event-kind (car rows)) (fn-store-event-sequence (car rows))
                (fn-store-event-txid (car rows)) (fn-store-event-generation (car rows)))
          (fn-row-coordinates (cdr rows)))))

(defthm fn-intern-events-are-store-events
  (implies (and (natp generation)
                (not (equal (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)) :bad)))
           (fn-sf-record-valuesp (mv-nth 0 (fn-intern-events ws keyring generation fn-arena))))
  :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
           :in-theory (e/d (fn-intern-events fn-sf-record-valuesp) (fn-intern-event)))))

(defthm fn-intern-events-keep-coordinates
  (implies (and (natp generation)
                (not (equal (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)) :bad)))
           (equal (fn-row-coordinates (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)))
                  (fn-wire-coordinates ws)))
  :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
           :in-theory (e/d (fn-intern-events) (fn-intern-event)))))

; KEYSTONE 3: every row's context is the context of its bytes under the
; keyring and generation of the intern.
(defthm fn-intern-events-contexts-okp
  (implies (and (fn-arena-p fn-arena) (natp generation) (fn-wire-event-listp ws)
                (not (equal (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)) :bad)))
           (fn-rows-contexts-okp (mv-nth 0 (fn-intern-events ws keyring generation fn-arena))
                                 keyring generation
                                 (mv-nth 1 (fn-intern-events ws keyring generation fn-arena))))
  :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
           :in-theory (e/d (fn-intern-events fn-rows-contexts-okp)
                           (fn-intern-event fn-row-context-okp fn-rows-handles-inp)))))

; -- 4.3 The index over both views.

; The rows' articles as the wire store lists them (fn-stx-store: newest
; first), each with its bytes read by handle: what fn-stx-index-of-store
; (books/stx-index.lisp), the wire view's index, folds.
(defun fn-rows-articles-newest-first (rows fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (cond ((atom rows) nil)
        ((fn-held-p (car rows))
         (append (fn-rows-articles-newest-first (cdr rows) fn-arena)
                 (list (fn-make-article (fn-record-msgid (car rows))
                                        (fn-row-bytes (car rows) fn-arena)
                                        (fn-record-groups (car rows))
                                        (fn-held-numbers (car rows)) t
                                        (fn-record-stamp (car rows))))))
        ((fn-hstxa-p (car rows))
         (let ((h (fn-hstxa-held (car rows))))
           (append (fn-rows-articles-newest-first (cdr rows) fn-arena)
                   (list (fn-make-article (fn-record-msgid h) (fn-row-bytes h fn-arena)
                                          (fn-record-groups h) (fn-held-numbers h) t
                                          (fn-record-stamp h))))))
        (t (fn-rows-articles-newest-first (cdr rows) fn-arena))))

; The wire index with a seed: fn-stx-index-of-store is the fold from the
; empty index, oldest article innermost.
(local (defun fn-stx-index-of-store-from (articles index keyring)
  (declare (xargs :guard (fn-prin-keyringp keyring)))
  (if (consp articles)
      (fn-stx-index-add (fn-stx-index-of-store-from (cdr articles) index keyring)
                        (fn-stx-delta (fn-article-payload (car articles)) keyring))
    index)))

(local (defthm fn-stx-index-of-store-is-from-empty
  (equal (fn-stx-index-of-store articles keyring)
         (fn-stx-index-of-store-from articles (fn-stx-index-empty) keyring))
  :hints (("Goal" :in-theory (enable fn-stx-index-of-store)))))

(local (defthm fn-stx-index-of-store-from-append-one
  (equal (fn-stx-index-of-store-from (append articles (list a)) index keyring)
         (fn-stx-index-of-store-from articles
                                     (fn-stx-index-add index (fn-stx-delta (fn-article-payload a) keyring))
                                     keyring))))

(local (defthm fn-article-payload-of-make-article
  (equal (fn-article-payload (fn-make-article msgid payload groups memberships pin stamp))
         payload)
  :hints (("Goal" :in-theory (enable fn-make-article fn-article-payload)))))

(local (defthm fn-hc-delta-of-held-context-of
  (equal (fn-hc-delta (fn-held-context-of bytes keyring generation))
         (fn-stx-delta bytes keyring))
  :hints (("Goal" :in-theory (enable fn-held-context-of)))))

; Under the context invariant the store's fold of the rows' contexts is the
; wire view's fold of their bytes, from any seed.
(local (defthm fn-rows-index-fold-is-the-wire-fold
  (implies (fn-rows-contexts-okp rows keyring generation fn-arena)
           (equal (fn-sn-index-fold rows index)
                  (fn-stx-index-of-store-from (fn-rows-articles-newest-first rows fn-arena)
                                              index keyring)))
  :hints (("Goal" :induct (fn-rows-contexts-okp rows keyring generation fn-arena)
           :in-theory (e/d (fn-rows-contexts-okp fn-row-context-okp fn-rows-articles-newest-first)
                           (fn-stx-index-add fn-stx-delta fn-held-context-of fn-row-bytes
                            fn-stx-index-of-store-is-from-empty))))))

; KEYSTONE: the index fn-sn-recover computes from the rows (fn-sn-index-of-rows,
; books/store-node.lisp) is the index the wire view recomputes from the bytes
; of the same rows' articles (fn-stx-index-of-store, the function the old
; recover called over fn-stx-store).  The hypothesis is the context
; invariant, which the intern establishes (fn-intern-events-contexts-okp) and
; the keyring installation re-establishes (fn-contexts-of-rows).
(defthm fn-rows-index-is-the-wire-index
  (implies (fn-rows-contexts-okp rows keyring generation fn-arena)
           (equal (fn-sn-index-of-rows rows)
                  (fn-stx-index-of-store (fn-rows-articles-newest-first rows fn-arena) keyring)))
  :hints (("Goal" :in-theory (e/d (fn-sn-index-of-rows) (fn-stx-index-of-store fn-sn-index-fold)))))
