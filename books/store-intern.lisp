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
(include-book "store-reclaim")
(include-book "stx-node-lace")

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
; Executes by a loop (lane depth-debt, PRF-919): the recursion took one
; control-stack frame per element of data with no fixed cap.  The :logic is
; the recursion, unchanged; the :exec is the loop, equal by the lemma below.
(defun fn-intern-events-loop (ws keyring generation acc fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (fn-prin-keyringp keyring) (natp generation))))
  (if (atom ws)
      (mv (fn-ag-rev-onto acc nil) fn-arena)
    (mv-let (row fn-arena)
      (fn-intern-event (car ws) keyring generation fn-arena)
      (if (eq row :bad)
          (mv :bad fn-arena)
        (fn-intern-events-loop (cdr ws) keyring generation (cons row acc) fn-arena)))))

(defun fn-intern-events (ws keyring generation fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (fn-prin-keyringp keyring) (natp generation))
                  :verify-guards nil))
  (mbe :logic
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
                 (mv (cons row rest) fn-arena))))))
       :exec (fn-intern-events-loop ws keyring generation nil fn-arena)))

(defthm fn-intern-events-loop-is-rev-onto
  (equal (fn-intern-events-loop ws keyring generation acc fn-arena)
         (mv-let (r a) (fn-intern-events ws keyring generation fn-arena)
           (mv (if (eq r :bad) :bad (fn-ag-rev-onto acc r)) a)))
  :hints (("Goal" :induct (fn-intern-events-loop ws keyring generation acc fn-arena)
                  :in-theory (disable fn-intern-event))))

(verify-guards fn-intern-events
  :hints (("Goal" :in-theory (disable fn-intern-event))))

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

; The arena is read through its interface (a sealed handle keeps its bytes,
; a seal adds one handle), never through the opened list view, whose
; append/nth rewrites send these inductions into the payload lists.
(local (in-theory (disable fn-arena-payload-is-nth fn-arena-count-is-len
                           fn-arena-seal-list-is-append fn-arena-p-is-payload-listp
                           fn-arena-get-is-nth fn-arena-payload-len-is-len-nth)))

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
  :hints (("Goal" :in-theory (enable fn-arena-p-is-payload-listp fn-arn-payload-listp fn-arena-seal-list-is-append)))))

; -- 4.1 One event.

; The row is a retained event, or :bad.
; The wire vocabularies' disjointness (PKT-745): proved once in
; books/store-events.lisp, disabled there, enabled here as this book always
; exported them (the fifth it withdrew at its end, so it is enabled locally).
(in-theory (enable fn-hstxa-is-no-wire-event fn-held-is-no-wire-event
                   fn-hstxa-is-not-held fn-record-is-no-other-wire-event))
(local (in-theory (enable fn-stxa-is-no-other-wire-event)))

(local (defthm fn-intern-list-row-fields
  (let ((row (car (fn-cat-intern-list w keyring generation fn-arena))))
    (and (equal (fn-record-sequence row) (fn-record-sequence w))
         (equal (fn-record-txid row) (fn-record-txid w))
         (equal (fn-record-generation row) (fn-record-generation w))
         (equal (fn-record-payload row) (fn-arena-count fn-arena))
         (equal (fn-held-wire row bytes) (fn-held-wire w bytes))))
  :hints (("Goal" :in-theory (enable fn-cat-intern-list fn-held-wire)))))

(local (defthm fn-intern-list-arena
  (equal (mv-nth 1 (fn-cat-intern-list w keyring generation fn-arena))
         (fn-arena-seal-list (fn-record-payload w) fn-arena))
  :hints (("Goal" :in-theory (enable fn-cat-intern-list)))))

(defthm fn-intern-event-is-store-event
  (implies (and (natp generation)
                (not (equal (mv-nth 0 (fn-intern-event w keyring generation fn-arena)) :bad)))
           (fn-store-event-p (mv-nth 0 (fn-intern-event w keyring generation fn-arena))))
  :hints (("Goal" :cases ((fn-record-p w) (fn-stxa-p w))
           :in-theory (e/d (fn-intern-event)
                           (fn-cat-intern-list fn-held-p-of-intern-list fn-wire-event-p
                            fn-replay-composite-record fn-stxa-p fn-record-p))
           :use ((:instance fn-held-p-of-intern-list)
                 (:instance fn-held-p-of-intern-list (w (fn-replay-composite-record w)))))
          ("Subgoal 1" :in-theory (e/d (fn-intern-event fn-store-event-p fn-wire-event-p)
                                       (fn-cat-intern-list fn-replay-composite-record
                                        fn-stxa-p fn-record-p)))))

;; The row reads the wire event's coordinates.  One lemma per arm over closed
;; recognizers (opened together the proof took 4 to 7 s).
(local (defun fn-si-coordinates (x retained)
  (if retained
      (list (fn-store-event-sequence x) (fn-store-event-txid x)
            (fn-store-event-generation x) (fn-store-event-kind x))
    (list (fn-wire-event-sequence x) (fn-wire-event-txid x)
          (fn-wire-event-generation x) (fn-wire-event-kind x)))))

(local (defthm fn-si-coordinates-of-held
  (implies (fn-held-p x)
           (equal (fn-si-coordinates x t)
                  (list (fn-record-sequence x) (fn-record-txid x)
                        (fn-record-generation x) :article)))
  :hints (("Goal" :in-theory (union-theories '(fn-si-coordinates fn-store-event-sequence
                                               fn-store-event-txid fn-store-event-generation
                                               fn-store-event-kind)
                                             (theory 'minimal-theory))))))

(local (defthm fn-si-coordinates-of-record
  (implies (fn-record-p x)
           (equal (fn-si-coordinates x nil)
                  (list (fn-record-sequence x) (fn-record-txid x)
                        (fn-record-generation x) :article)))
  :hints (("Goal" :in-theory (union-theories '(fn-si-coordinates fn-wire-event-sequence
                                               fn-wire-event-txid fn-wire-event-generation
                                               fn-wire-event-kind)
                                             (theory 'minimal-theory))))))

(local (defthm fn-si-coordinates-of-hstxa
  (implies (fn-hstxa-p x)
           (equal (fn-si-coordinates x t)
                  (fn-si-coordinates (fn-hstxa-stxa x) nil)))
  :hints (("Goal" :use ((:instance fn-hstxa-is-no-wire-event)
                        (:instance fn-hstxa-is-not-held)
                        (:instance fn-hstxa-p-fields)
                        (:instance fn-stxa-is-no-other-wire-event (x (fn-hstxa-stxa x))))
           :in-theory (union-theories '(fn-si-coordinates fn-store-event-sequence
                                        fn-store-event-txid fn-store-event-generation
                                        fn-store-event-kind fn-wire-event-sequence
                                        fn-wire-event-txid fn-wire-event-generation
                                        fn-wire-event-kind)
                                      (theory 'minimal-theory))))))

(local (defthm fn-si-coordinates-of-other
  (implies (and (fn-wire-event-p x) (not (fn-record-p x)) (not (fn-stxa-p x)))
           (equal (fn-si-coordinates x t) (fn-si-coordinates x nil)))
  :hints (("Goal" :use ((:instance fn-held-is-no-wire-event)
                        (:instance fn-hstxa-is-no-wire-event))
           :cases ((fn-held-p x) (fn-hstxa-p x))
           :in-theory (union-theories '(fn-si-coordinates fn-wire-event-p fn-store-event-sequence
                                        fn-store-event-txid fn-store-event-generation
                                        fn-store-event-kind fn-wire-event-sequence
                                        fn-wire-event-txid fn-wire-event-generation
                                        fn-wire-event-kind)
                                      (theory 'minimal-theory))))))

(local (defthm fn-si-intern-event-coordinates
  (implies (and (natp generation)
                (not (equal (mv-nth 0 (fn-intern-event w keyring generation fn-arena)) :bad)))
           (equal (fn-si-coordinates (mv-nth 0 (fn-intern-event w keyring generation fn-arena)) t)
                  (fn-si-coordinates w nil)))
  :hints (("Goal" :cases ((fn-record-p w) (fn-stxa-p w))
           :use ((:instance fn-held-p-of-intern-list)
                 (:instance fn-held-p-of-intern-list (w (fn-replay-composite-record w))))
           :in-theory (e/d (fn-intern-event)
                           (fn-si-coordinates fn-cat-intern-list fn-held-p-of-intern-list
                            fn-wire-event-p fn-replay-composite-record fn-stxa-p fn-record-p
                            fn-held-p fn-hstxa-p fn-hstxa-make))))))

(defthm fn-intern-event-keeps-coordinates
  (implies (and (natp generation)
                (not (equal (mv-nth 0 (fn-intern-event w keyring generation fn-arena)) :bad)))
           (let ((row (mv-nth 0 (fn-intern-event w keyring generation fn-arena))))
             (and (equal (fn-store-event-sequence row) (fn-wire-event-sequence w))
                  (equal (fn-store-event-txid row) (fn-wire-event-txid w))
                  (equal (fn-store-event-generation row) (fn-wire-event-generation w))
                  (equal (fn-store-event-kind row) (fn-wire-event-kind w)))))
  :hints (("Goal" :use fn-si-intern-event-coordinates
           :in-theory (union-theories '(fn-si-coordinates car-cons cdr-cons)
                                      (theory 'minimal-theory)))))

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
  :hints (("Goal" :cases ((fn-record-p w) (fn-stxa-p w))
           :in-theory (e/d (fn-intern-event fn-row-handle-inp fn-rows-handles-inp)
                           (fn-cat-intern-list fn-held-p-of-intern-list fn-wire-event-p
                            fn-replay-composite-record fn-stxa-p fn-record-p))
           :use ((:instance fn-held-p-of-intern-list)
                 (:instance fn-held-p-of-intern-list (w (fn-replay-composite-record w)))))
          ("Subgoal 1" :in-theory (e/d (fn-intern-event fn-wire-event-p fn-rows-handles-inp)
                                       (fn-cat-intern-list fn-replay-composite-record
                                        fn-stxa-p fn-record-p))
           :use ((:instance fn-held-is-no-wire-event (x w))
                 (:instance fn-hstxa-is-no-wire-event (x w))))))

; ALPHA of one row is its wire event (KEYSTONE 1, one event).

(local (defthm fn-row-wire-of-held-is-held-wire-of
  (implies (and (fn-held-p h) (fn-row-handle-inp h fn-arena))
           (equal (fn-row-wire-of h fn-arena) (fn-held-wire-of h fn-arena)))
  :hints (("Goal" :in-theory (enable fn-row-wire-of fn-row-bytes fn-held-wire-of fn-row-handle-inp)))))

(local (defthm fn-intern-list-materializes-in-seal
  (implies (and (fn-record-p w) (natp generation))
           (equal (fn-row-wire-of (mv-nth 0 (fn-cat-intern-list w keyring generation fn-arena))
                                  (fn-arena-seal-list (fn-record-payload w) fn-arena))
                  w))
  :hints (("Goal" :in-theory (e/d (fn-row-wire-of fn-row-bytes fn-record-p)
                                  (fn-cat-intern-list fn-cat-intern-list-materializes
                                   fn-held-p-of-intern-list))
           :use ((:instance fn-cat-intern-list-materializes)
                 (:instance fn-held-p-of-intern-list))))))

(local (defthm fn-intern-list-materializes-in-seal-car
  (implies (and (fn-record-p w) (natp generation))
           (equal (fn-row-wire-of (car (fn-cat-intern-list w keyring generation fn-arena))
                                  (fn-arena-seal-list (fn-record-payload w) fn-arena))
                  w))
  :hints (("Goal" :use fn-intern-list-materializes-in-seal
           :in-theory (disable fn-intern-list-materializes-in-seal fn-row-wire-of fn-cat-intern-list)))))

(local (defthm fn-other-wire-event-is-its-own-row
  (implies (and (fn-wire-event-p w) (not (fn-record-p w)) (not (fn-stxa-p w)))
           (equal (fn-row-wire-of w fn-arena) w))
  :hints (("Goal" :cases ((fn-held-p w) (fn-hstxa-p w))
           :in-theory (union-theories '(fn-wire-event-p fn-row-wire-of) (theory 'minimal-theory))
           :use ((:instance fn-held-is-no-wire-event (x w))
                 (:instance fn-hstxa-is-no-wire-event (x w)))))))

(local (defthm fn-row-wire-of-hstxa-make
  (implies (and (fn-stxa-p w) (fn-held-p h))
           (equal (fn-row-wire-of (fn-hstxa-make w h) fn-arena) w))
  :hints (("Goal" :in-theory (e/d (fn-row-wire-of) (fn-held-p))
           :use ((:instance fn-held-p-forward-natural-head (x (fn-hstxa-make w h)))
                 (:instance fn-hstxa-p-forward-shape (x (fn-hstxa-make w h))))))))

(defthm fn-intern-event-materializes
  (implies (and (fn-arena-p fn-arena) (natp generation)
                (not (equal (mv-nth 0 (fn-intern-event w keyring generation fn-arena)) :bad)))
           (equal (fn-row-wire-of (mv-nth 0 (fn-intern-event w keyring generation fn-arena))
                                  (mv-nth 1 (fn-intern-event w keyring generation fn-arena)))
                  w))
  :hints (("Goal" :cases ((fn-record-p w) (fn-stxa-p w))
           :in-theory (e/d (fn-intern-event)
                           (fn-cat-intern-list fn-row-wire-of fn-held-p-of-intern-list
                            fn-wire-event-p))
           :use ((:instance fn-held-p-of-intern-list (w (fn-replay-composite-record w)))))))

; The row's context is the context of its bytes (KEYSTONE 3, one event).
(local (defthm fn-intern-list-row-context
  (equal (fn-held-context (car (fn-cat-intern-list w keyring generation fn-arena)))
         (fn-held-context-of (fn-record-payload w) keyring generation))
  :hints (("Goal" :in-theory (enable fn-cat-intern-list)))))

(local (defthm fn-intern-list-context-okp-in-seal
  (fn-row-context-okp (car (fn-cat-intern-list w keyring generation fn-arena))
                      keyring generation
                      (fn-arena-seal-list (fn-record-payload w) fn-arena))
  :hints (("Goal" :in-theory (e/d (fn-row-context-okp fn-row-bytes) (fn-cat-intern-list))))))

(local (defthm fn-rows-contexts-okp-of-atom
  (implies (atom rows) (equal (fn-rows-contexts-okp rows keyring generation fn-arena) t))
  :hints (("Goal" :in-theory (enable fn-rows-contexts-okp)))))

(local (defthm fn-rows-contexts-okp-of-list
  (equal (fn-rows-contexts-okp (list r) keyring generation fn-arena)
         (cond ((fn-held-p r) (fn-row-context-okp r keyring generation fn-arena))
               ((fn-hstxa-p r) (fn-row-context-okp (fn-hstxa-held r) keyring generation fn-arena))
               (t t)))
  :hints (("Goal" :expand ((fn-rows-contexts-okp (list r) keyring generation fn-arena))
           :in-theory (disable fn-held-p fn-hstxa-p fn-row-context-okp)))))

; One lemma per arm, each over closed recognizers (with them open the single
; proof took 76 s: persvati r1 of flip-L1).
(local (defthm fn-intern-event-context-okp-record
  (implies (and (fn-record-p w) (natp generation))
           (fn-rows-contexts-okp (list (mv-nth 0 (fn-intern-event w keyring generation fn-arena)))
                                 keyring generation
                                 (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-intern-event)
                                  (fn-cat-intern-list fn-row-context-okp fn-held-p-of-intern-list
                                   fn-wire-event-p fn-record-p fn-stxa-p fn-held-p fn-hstxa-p
                                   fn-rows-contexts-okp))
           :use ((:instance fn-held-p-of-intern-list))))))

(local (defthm fn-intern-event-context-okp-composite
  (implies (and (fn-stxa-p w) (natp generation)
                (fn-record-p (fn-replay-composite-record w)))
           (fn-rows-contexts-okp (list (mv-nth 0 (fn-intern-event w keyring generation fn-arena)))
                                 keyring generation
                                 (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-intern-event)
                                  (fn-cat-intern-list fn-row-context-okp fn-held-p-of-intern-list
                                   fn-wire-event-p fn-record-p fn-stxa-p fn-held-p fn-hstxa-p
                                   fn-hstxa-make fn-replay-composite-record
                                   fn-rows-contexts-okp))
           :use ((:instance fn-held-p-of-intern-list (w (fn-replay-composite-record w)))
                 (:instance fn-hstxa-is-not-held
                            (x (fn-hstxa-make w (car (fn-cat-intern-list
                                                      (fn-replay-composite-record w)
                                                      keyring generation fn-arena)))))
                 (:instance fn-stxa-is-no-other-wire-event (x w)))))))

(local (defthm fn-intern-event-context-okp-other
  (implies (and (not (fn-record-p w)) (not (fn-stxa-p w)))
           (fn-rows-contexts-okp (list (mv-nth 0 (fn-intern-event w keyring generation fn-arena)))
                                 keyring generation
                                 (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-intern-event)
                                  (fn-cat-intern-list fn-row-context-okp
                                   fn-wire-event-p fn-record-p fn-stxa-p fn-held-p fn-hstxa-p
                                   fn-rows-contexts-okp))
           :use ((:instance fn-held-is-no-wire-event (x w))
                 (:instance fn-hstxa-is-no-wire-event (x w))
                 (:instance fn-held-is-no-wire-event (x :bad))
                 (:instance fn-hstxa-is-no-wire-event (x :bad)))))))

(defthm fn-intern-event-context-okp
  (implies (and (fn-arena-p fn-arena) (natp generation)
                (not (equal (mv-nth 0 (fn-intern-event w keyring generation fn-arena)) :bad)))
           (fn-rows-contexts-okp (list (mv-nth 0 (fn-intern-event w keyring generation fn-arena)))
                                 keyring generation
                                 (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))
  :hints (("Goal" :cases ((fn-record-p w)
                           (and (fn-stxa-p w) (fn-record-p (fn-replay-composite-record w)))
                           (fn-stxa-p w))
           :use (fn-intern-event-context-okp-record fn-intern-event-context-okp-composite
                 fn-intern-event-context-okp-other)
           :in-theory (union-theories '(natp) (theory 'minimal-theory)))
          ("Subgoal 1" :in-theory (e/d (fn-intern-event)
                                       (fn-rows-contexts-okp fn-record-p fn-stxa-p
                                        fn-cat-intern-list fn-replay-composite-record
                                        fn-intern-event-arena)))))

; -- 4.2 The list.

; What a row reads is stable under every later seal, so a list interned in
; order materializes to its wire events in the final arena (KEYSTONE 1).
(local (defthm fn-row-wire-of-survives-seal
  (implies (and (fn-arena-p fn-arena) (fn-rows-handles-inp (list row) fn-arena))
           (equal (fn-row-wire-of row (fn-arena-seal-list xs fn-arena))
                  (fn-row-wire-of row fn-arena)))
  :hints (("Goal" :in-theory (enable fn-row-wire-of fn-rows-handles-inp fn-held-wire-of
                                     fn-row-handle-inp fn-row-bytes)))))

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
(local (defthm fn-record-p-payload-octets
  (implies (fn-record-p w) (fn-cbor-octet-listp (fn-record-payload w)))
  :hints (("Goal" :in-theory (enable fn-record-p fn-record-payloadp)))))

(local (defthm fn-arena-p-of-intern-event
  (implies (and (fn-arena-p fn-arena) (fn-wire-event-p w))
           (fn-arena-p (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))
  :hints (("Goal" :in-theory (disable fn-intern-event fn-wire-event-p fn-record-p)))))

(defun fn-wire-event-listp (ws)
  (declare (xargs :guard t))
  (if (atom ws) (null ws) (and (fn-wire-event-p (car ws)) (fn-wire-event-listp (cdr ws)))))

(defthm fn-intern-events-arena-p
  (implies (and (fn-arena-p fn-arena) (fn-wire-event-listp ws))
           (fn-arena-p (mv-nth 1 (fn-intern-events ws keyring generation fn-arena))))
  :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
           :in-theory (e/d (fn-intern-events)
                           (fn-intern-event fn-intern-event-arena fn-wire-event-p
                            fn-record-p fn-stxa-p fn-arena-p)))))

(local (defthm fn-rows-handles-inp-survives-intern-event
  (implies (and (fn-arena-p fn-arena) (fn-rows-handles-inp rows fn-arena))
           (fn-rows-handles-inp rows (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))
  :hints (("Goal" :in-theory (disable fn-intern-event fn-rows-handles-inp)))))

(local (defthm fn-rows-handles-inp-survives-intern-events
  (implies (and (fn-arena-p fn-arena) (fn-wire-event-listp ws) (fn-rows-handles-inp rows fn-arena))
           (fn-rows-handles-inp rows (mv-nth 1 (fn-intern-events ws keyring generation fn-arena))))
  :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
           :in-theory (e/d (fn-intern-events)
                           (fn-intern-event fn-rows-handles-inp fn-intern-event-arena
                            fn-wire-event-p fn-record-p fn-stxa-p fn-arena-p))))))

(local (defthm fn-rows-handles-inp-of-cons
  (implies (syntaxp (not (equal rs ''nil)))
           (equal (fn-rows-handles-inp (cons r rs) fn-arena)
                  (and (fn-rows-handles-inp (list r) fn-arena) (fn-rows-handles-inp rs fn-arena))))
  :hints (("Goal" :in-theory (enable fn-rows-handles-inp)))))

(local (defthm fn-intern-events-step-handle
  (implies (and (fn-arena-p fn-arena) (natp generation) (fn-wire-event-p w)
                (fn-wire-event-listp ws)
                (not (equal (car (fn-intern-event w keyring generation fn-arena)) :bad)))
           (fn-rows-handles-inp
            (list (car (fn-intern-event w keyring generation fn-arena)))
            (mv-nth 1 (fn-intern-events ws keyring generation
                                        (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))))
  :hints (("Goal" :in-theory (disable fn-intern-event fn-intern-events fn-rows-handles-inp
                                      fn-intern-event-handle-in
                                      fn-rows-handles-inp-survives-intern-events)
           :use ((:instance fn-intern-event-handle-in)
                 (:instance fn-rows-handles-inp-survives-intern-events
                  (rows (list (car (fn-intern-event w keyring generation fn-arena))))
                  (fn-arena (mv-nth 1 (fn-intern-event w keyring generation fn-arena)))))))))

(defthm fn-intern-events-handles-in
  (implies (and (fn-arena-p fn-arena) (natp generation) (fn-wire-event-listp ws)
                (not (equal (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)) :bad)))
           (fn-rows-handles-inp (mv-nth 0 (fn-intern-events ws keyring generation fn-arena))
                                (mv-nth 1 (fn-intern-events ws keyring generation fn-arena))))
  :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
           :in-theory (e/d (fn-intern-events)
                           (fn-intern-event fn-intern-event-arena fn-row-handle-inp
                            fn-wire-event-p)))))

; KEYSTONE 1: alpha of the intern is the identity on the wire events.
(local (defthm fn-row-wire-of-survives-intern-event
  (implies (and (fn-arena-p fn-arena) (fn-rows-handles-inp (list row) fn-arena))
           (equal (fn-row-wire-of row (mv-nth 1 (fn-intern-event w keyring generation fn-arena)))
                  (fn-row-wire-of row fn-arena)))
  :hints (("Goal" :in-theory (disable fn-intern-event fn-rows-handles-inp fn-row-wire-of)))))

(local (defthm fn-row-wire-of-survives-intern-events
  (implies (and (fn-arena-p fn-arena) (fn-wire-event-listp ws)
                (fn-rows-handles-inp (list row) fn-arena))
           (equal (fn-row-wire-of row (mv-nth 1 (fn-intern-events ws keyring generation fn-arena)))
                  (fn-row-wire-of row fn-arena)))
  :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
           :in-theory (e/d (fn-intern-events)
                           (fn-intern-event fn-rows-handles-inp fn-row-wire-of fn-intern-event-arena))))))

(local (defthm fn-intern-events-step-wire
  (implies (and (fn-arena-p fn-arena) (natp generation) (fn-wire-event-p w)
                (fn-wire-event-listp ws)
                (not (equal (car (fn-intern-event w keyring generation fn-arena)) :bad)))
           (equal (fn-row-wire-of
                   (car (fn-intern-event w keyring generation fn-arena))
                   (mv-nth 1 (fn-intern-events ws keyring generation
                                               (mv-nth 1 (fn-intern-event w keyring generation fn-arena)))))
                  w))
  :hints (("Goal" :in-theory (disable fn-intern-event fn-intern-events fn-rows-handles-inp
                                      fn-row-wire-of fn-intern-event-arena
                                      fn-intern-event-handle-in fn-intern-event-materializes
                                      fn-row-wire-of-survives-intern-events)
           :use ((:instance fn-intern-event-handle-in)
                 (:instance fn-intern-event-materializes)
                 (:instance fn-row-wire-of-survives-intern-events
                  (row (car (fn-intern-event w keyring generation fn-arena)))
                  (fn-arena (mv-nth 1 (fn-intern-event w keyring generation fn-arena)))))))))

(defthm fn-intern-events-materializes
  (implies (and (fn-arena-p fn-arena) (natp generation) (fn-wire-event-listp ws)
                (not (equal (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)) :bad)))
           (equal (fn-rows-wire-of (mv-nth 0 (fn-intern-events ws keyring generation fn-arena))
                                   (mv-nth 1 (fn-intern-events ws keyring generation fn-arena)))
                  ws))
  :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
           :in-theory (e/d (fn-intern-events fn-rows-wire-of)
                           (fn-intern-event fn-row-wire-of fn-rows-handles-inp
                            fn-intern-event-arena fn-wire-event-p)))))

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

(local (defthm fn-intern-event-row-facts-car
  (implies (and (natp generation)
                (not (equal (car (fn-intern-event w keyring generation fn-arena)) :bad)))
           (let ((row (car (fn-intern-event w keyring generation fn-arena))))
             (and (fn-store-event-p row)
                  (equal (fn-store-event-sequence row) (fn-wire-event-sequence w))
                  (equal (fn-store-event-txid row) (fn-wire-event-txid w))
                  (equal (fn-store-event-generation row) (fn-wire-event-generation w))
                  (equal (fn-store-event-kind row) (fn-wire-event-kind w)))))
  :hints (("Goal" :use (fn-intern-event-is-store-event fn-intern-event-keeps-coordinates)
           :in-theory (disable fn-intern-event fn-intern-event-is-store-event
                               fn-intern-event-keeps-coordinates fn-store-event-p
                               fn-store-event-sequence fn-store-event-txid
                               fn-store-event-generation fn-store-event-kind
                               fn-wire-event-sequence fn-wire-event-txid
                               fn-wire-event-generation fn-wire-event-kind)))))

(defthm fn-intern-events-are-store-events
  (implies (and (natp generation)
                (not (equal (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)) :bad)))
           (fn-sf-record-valuesp (mv-nth 0 (fn-intern-events ws keyring generation fn-arena))))
  :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
           :in-theory (e/d (fn-intern-events fn-sf-record-valuesp)
                           (fn-intern-event fn-intern-event-arena fn-store-event-p)))))

(defthm fn-intern-events-keep-coordinates
  (implies (and (natp generation)
                (not (equal (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)) :bad)))
           (equal (fn-row-coordinates (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)))
                  (fn-wire-coordinates ws)))
  :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
           :in-theory (e/d (fn-intern-events)
                           (fn-intern-event fn-intern-event-arena fn-store-event-p
                            fn-store-event-sequence fn-store-event-txid
                            fn-store-event-generation fn-store-event-kind
                            fn-wire-event-sequence fn-wire-event-txid
                            fn-wire-event-generation fn-wire-event-kind)))))

; KEYSTONE 3: every row's context is the context of its bytes under the
; keyring and generation of the intern.
(local (defthm fn-rows-contexts-okp-of-cons
  (implies (syntaxp (not (equal rs ''nil)))
           (equal (fn-rows-contexts-okp (cons r rs) keyring generation fn-arena)
                  (and (fn-rows-contexts-okp (list r) keyring generation fn-arena)
                       (fn-rows-contexts-okp rs keyring generation fn-arena))))
  :hints (("Goal" :in-theory (enable fn-rows-contexts-okp)))))

(local (defthm fn-rows-contexts-okp-survives-intern-event
  (implies (and (fn-arena-p fn-arena) (fn-rows-handles-inp rows fn-arena)
                (fn-rows-contexts-okp rows keyring generation fn-arena))
           (fn-rows-contexts-okp rows keyring generation
                                 (mv-nth 1 (fn-intern-event w k2 g2 fn-arena))))
  :hints (("Goal" :in-theory (disable fn-intern-event fn-rows-handles-inp fn-rows-contexts-okp)))))

(local (defthm fn-rows-contexts-okp-survives-intern-events
  (implies (and (fn-arena-p fn-arena) (fn-wire-event-listp ws) (fn-rows-handles-inp rows fn-arena)
                (fn-rows-contexts-okp rows keyring generation fn-arena))
           (fn-rows-contexts-okp rows keyring generation
                                 (mv-nth 1 (fn-intern-events ws k2 g2 fn-arena))))
  :hints (("Goal" :induct (fn-intern-events ws k2 g2 fn-arena)
           :in-theory (e/d (fn-intern-events)
                           (fn-intern-event fn-rows-handles-inp fn-rows-contexts-okp
                            fn-intern-event-arena))))))

(local (defthm fn-intern-events-step-context
  (implies (and (fn-arena-p fn-arena) (natp generation) (fn-wire-event-p w)
                (fn-wire-event-listp ws)
                (not (equal (car (fn-intern-event w keyring generation fn-arena)) :bad)))
           (fn-rows-contexts-okp
            (list (car (fn-intern-event w keyring generation fn-arena)))
            keyring generation
            (mv-nth 1 (fn-intern-events ws keyring generation
                                        (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))))
  :hints (("Goal" :in-theory (disable fn-intern-event fn-intern-events fn-rows-handles-inp
                                      fn-rows-contexts-okp fn-intern-event-arena
                                      fn-intern-event-handle-in fn-intern-event-context-okp
                                      fn-rows-contexts-okp-survives-intern-events)
           :use ((:instance fn-intern-event-handle-in)
                 (:instance fn-intern-event-context-okp)
                 (:instance fn-rows-contexts-okp-survives-intern-events
                  (rows (list (car (fn-intern-event w keyring generation fn-arena))))
                  (k2 keyring) (g2 generation)
                  (fn-arena (mv-nth 1 (fn-intern-event w keyring generation fn-arena)))))))))

(defthm fn-intern-events-contexts-okp
  (implies (and (fn-arena-p fn-arena) (natp generation) (fn-wire-event-listp ws)
                (not (equal (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)) :bad)))
           (fn-rows-contexts-okp (mv-nth 0 (fn-intern-events ws keyring generation fn-arena))
                                 keyring generation
                                 (mv-nth 1 (fn-intern-events ws keyring generation fn-arena))))
  :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
           :in-theory (e/d (fn-intern-events)
                           (fn-intern-event fn-row-context-okp fn-rows-handles-inp
                            fn-rows-contexts-okp fn-intern-event-arena fn-wire-event-p)))))

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
(fn-payload-kind fn-stx-index-of-store-from :wire "its articles are fn-rows-articles-newest-first's, built with fn-row-bytes (octets)")
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
(local (defthm fn-stx-index-add-of-nil
  (equal (fn-stx-index-add index nil) index)
  :hints (("Goal" :in-theory (enable fn-stx-index-add)))))

(local (defthm fn-rows-index-fold-is-the-wire-fold
  (implies (fn-rows-contexts-okp rows keyring generation fn-arena)
           (equal (fn-sn-index-fold rows index)
                  (fn-stx-index-of-store-from (fn-rows-articles-newest-first rows fn-arena)
                                              index keyring)))
  :hints (("Goal" :induct (fn-sn-index-fold rows index)
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
  :hints (("Goal" :use ((:instance fn-rows-index-fold-is-the-wire-fold (index (fn-stx-index-empty)))
                        (:instance fn-stx-index-of-store-is-from-empty
                         (articles (fn-rows-articles-newest-first rows fn-arena))))
           :in-theory '(fn-sn-index-of-rows))))

; KEYSTONES (PRF-023, the served queries, restated over alpha after the
; flip).  The store's statement lookup and equivocator question read the
; carried index and nothing else (fn-sn-statement-lookup, fn-sn-equivocatorp,
; books/store-node.lisp; host/store-node-host.lisp fn-store-sn-statement and
; fn-store-sn-equivocator call them on the 'fn-store-sn global).  Under the
; carried-index invariant (fn-sn-indexedp) and the context invariant of the
; indexed rows, each answers exactly as the linear lace of the indexed rows'
; articles, their bytes read through the arena.  Before the flip these were
; stated over fn-stx-lace of the node, whose articles now carry handles.
(defthm fn-store-statement-lookup-is-the-lace-lookup
  (implies (and (fn-sn-indexedp s)
                (fn-rows-contexts-okp (fn-sn-indexed-rows s) (fn-sn-keyring s)
                                      generation fn-arena))
           (equal (fn-sn-statement-lookup s id)
                  (fn-lace-lookup
                   (fn-stx-lace-of-store
                    (fn-rows-articles-newest-first (fn-sn-indexed-rows s) fn-arena)
                    (fn-sn-keyring s))
                   id)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-rows-index-is-the-wire-index
                                   (rows (fn-sn-indexed-rows s))
                                   (keyring (fn-sn-keyring s)))
                        (:instance fn-stx-index-bindings-agree
                                   (articles (fn-rows-articles-newest-first
                                              (fn-sn-indexed-rows s) fn-arena))
                                   (keyring (fn-sn-keyring s))))
           :in-theory '(fn-sn-indexedp fn-sn-statement-lookup))))

(defthm fn-store-equivocatorp-is-the-lace-equivocator
  (implies (and (fn-sn-indexedp s)
                (fn-rows-contexts-okp (fn-sn-indexed-rows s) (fn-sn-keyring s)
                                      generation fn-arena))
           (iff (fn-sn-equivocatorp s creator incarnation)
                (fn-lace-equivocatorp
                 (fn-stx-lace-of-store
                  (fn-rows-articles-newest-first (fn-sn-indexed-rows s) fn-arena)
                  (fn-sn-keyring s))
                 creator incarnation)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-rows-index-is-the-wire-index
                                   (rows (fn-sn-indexed-rows s))
                                   (keyring (fn-sn-keyring s)))
                        (:instance fn-stx-index-equivocators-agree
                                   (articles (fn-rows-articles-newest-first
                                              (fn-sn-indexed-rows s) fn-arena))
                                   (keyring (fn-sn-keyring s))
                                   (p creator) (i incarnation)))
           :in-theory '(fn-sn-indexedp fn-sn-equivocatorp))))

; -----------------------------------------------------------------------------
; 5. THE PREPARE ENTRY (POST, transit): stage the row the intern WOULD make,
; and seal its bytes only when the store took it.  The row's handle is the
; arena's count before the seal, which is the handle the seal then returns
; (fn-arena-seal-new-handle): a refused prepare leaves the arena as it was,
; so no refused article's bytes are retained.

(defun fn-intern-row-at (w keyring generation h)
  (declare (xargs :guard (and (fn-record-p w) (fn-prin-keyringp keyring)
                              (natp generation) (natp h))
                  :guard-hints (("Goal" :in-theory (enable fn-record-p fn-record-payloadp)))))
  (let ((bytes (fn-record-payload w)))
    (fn-held-make (fn-record-sequence w) (fn-record-txid w)
                  (fn-record-generation w) (fn-record-msgid w) h
                  (fn-record-groups w) (fn-record-obligation-id w)
                  (fn-record-content-subject w) (fn-record-release-evidence w)
                  (fn-record-charge w) (fn-record-stamp w)
                  (fn-held-facts-of bytes)
                  (fn-held-context-of bytes keyring generation)
                  nil nil (fn-row-binding w))))

; The intern is the row at the old count, and the seal.
(defthm fn-cat-intern-list-is-row-at-count
  (and (equal (mv-nth 0 (fn-cat-intern-list w keyring generation fn-arena))
              (fn-intern-row-at w keyring generation (fn-arena-count fn-arena)))
       (equal (mv-nth 1 (fn-cat-intern-list w keyring generation fn-arena))
              (fn-arena-seal-list (fn-record-payload w) fn-arena)))
  :hints (("Goal" :in-theory (enable fn-cat-intern-list fn-intern-row-at))))

(defun fn-store-prepare-interned (s w fn-arena)
  (declare (xargs :stobjs fn-arena :guard (fn-sn-statep s) :verify-guards nil))
  (if (and (fn-record-p w) (fn-prin-keyringp (fn-sn-keyring s))
           (natp (fn-sn-keyring-generation s)))
      (let* ((row (fn-intern-row-at w (fn-sn-keyring s) (fn-sn-keyring-generation s)
                                    (fn-arena-count fn-arena)))
             (next (fn-sn-prepare s row)))
        (if (equal next s)
            (mv s fn-arena)
          (let ((fn-arena (fn-arena-seal-list (fn-record-payload w) fn-arena)))
            (mv next fn-arena))))
    (mv s fn-arena)))

; KEYSTONE (the prepare entry): the entry is the intern followed by the
; store's prepare, except that a refused prepare does not seal.
; The entry the host calls executes guard-verified.
(verify-guards fn-store-prepare-interned
  :hints (("Goal" :in-theory (e/d (fn-sn-statep)
                                  (fn-sf-statep fn-node-statep fn-sn-prepare
                                   fn-intern-row-at fn-record-p)))))

;; The keyring and generation conjuncts of the entry's gate are fn-sn-statep's:
;; off a statep store both the entry and fn-sn-prepare return S, so the
;; keystone needs only that W is a wire record.
(local (defthm fn-si-prepare-off-state-is-identity
  (implies (not (fn-sn-statep s)) (equal (fn-sn-prepare s row) s))
  :hints (("Goal" :in-theory (enable fn-sn-prepare)))))

(local (defthm fn-si-statep-keyring-fields
  (implies (fn-sn-statep s)
           (and (fn-prin-keyringp (fn-sn-keyring s))
                (natp (fn-sn-keyring-generation s))))
  :hints (("Goal" :in-theory (e/d (fn-sn-statep) (fn-sf-statep fn-node-statep))))))

(defthm fn-store-prepare-interned-is-intern-then-prepare
  (implies (fn-record-p w)
           (let* ((k (fn-sn-keyring s)) (g (fn-sn-keyring-generation s))
                  (row (mv-nth 0 (fn-cat-intern-list w k g fn-arena)))
                  (next (fn-sn-prepare s row)))
             (and (equal (mv-nth 0 (fn-store-prepare-interned s w fn-arena)) next)
                  (equal (mv-nth 1 (fn-store-prepare-interned s w fn-arena))
                         (if (equal next s)
                             fn-arena
                           (mv-nth 1 (fn-cat-intern-list w k g fn-arena)))))))
  :hints (("Goal" :cases ((fn-sn-statep s))
           :in-theory (e/d (fn-store-prepare-interned)
                           (fn-sn-prepare fn-intern-row-at fn-sn-statep)))))

;; What the entry does to the arena, stated on its own: a refused prepare
;; leaves the arena exactly as it was (no refused article's bytes are
;; retained); an accepted one seals exactly one payload, the wire record's
;; bytes, at the handle the staged row names (the arena's count before).
(defthm fn-store-prepare-interned-refusal-keeps-the-arena
  (implies (equal (mv-nth 0 (fn-store-prepare-interned s w fn-arena)) s)
           (equal (mv-nth 1 (fn-store-prepare-interned s w fn-arena)) fn-arena))
  :hints (("Goal" :in-theory (e/d (fn-store-prepare-interned)
                                  (fn-sn-prepare fn-intern-row-at)))))

(local (defthm fn-si-nth-len-of-append-one
  (equal (nth (len xs) (append xs (list y))) y)))

(defthm fn-store-prepare-interned-acceptance-seals-one-payload
  (implies (and (fn-arena-p fn-arena)
                (not (equal (mv-nth 0 (fn-store-prepare-interned s w fn-arena)) s)))
           (let ((after (mv-nth 1 (fn-store-prepare-interned s w fn-arena))))
             (and (fn-record-p w)
                  (equal (fn-arena-count after) (+ 1 (fn-arena-count fn-arena)))
                  (equal (fn-arena-payload (fn-arena-count fn-arena) after)
                         (fn-record-payload w)))))
  :hints (("Goal" :in-theory (e/d (fn-store-prepare-interned fn-arena-count-is-len
                                   fn-arena-payload-is-nth fn-arena-seal-list-is-append
                                   fn-arena-p-is-payload-listp)
                                  (fn-sn-prepare fn-intern-row-at fn-record-p))
           :do-not-induct t)))

; -----------------------------------------------------------------------------
; 6. THE DUPLICATE/CONFLICT ENTRY (a POST of a Message-ID the store holds).
; The acceptance state's article carries a handle; the verdict compares the
; offered payload with the bytes the handle denotes, read through the arena.
; ALPHA of the acceptance articles: each article's handle replaced by its
; bytes (a handle outside the arena reads as no bytes, as fn-row-bytes).

; fn-handle-bytes (the octets at a handle, nil outside the arena) is defined
; in books/payload-arena.lisp, beside the arena, so the owner reads it too;
; fn-articles-wire-of, ALPHA itself, is books/stx-node-lace.lisp's since
; 2026-09-29 (the node lace reads it too, PKT-892).

(defun fn-store-existing-action (msgid payload groups s fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (let ((article (fn-find-article
                  msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s))))))
    (if article
        (if (and (fn-rcl-same-articlep (fn-record-string-octets msgid) payload
                                       (fn-handle-bytes (fn-article-payload article) fn-arena))
                 (equal groups (fn-article-groups article)))
            :duplicate
          :conflict)
      nil)))

(verify-guards fn-store-existing-action)

(local (defthm fn-find-article-of-articles-wire-of
  (implies (stringp msgid)
  (equal (fn-find-article msgid (fn-articles-wire-of articles fn-arena))
         (let ((a (fn-find-article msgid articles)))
           (and a
                (fn-make-article (fn-article-msgid a)
                                 (fn-handle-bytes (fn-article-payload a) fn-arena)
                                 (fn-article-groups a) (fn-article-memberships a)
                                 (fn-article-pin a) (fn-article-stamp a))))))
  :hints (("Goal" :in-theory (e/d (fn-find-article fn-articles-wire-of) (fn-handle-bytes))))))

; KEYSTONE: the entry's verdict is D25's verdict (fn-rcl-action-over, the
; verdict over the article list) over ALPHA of the acceptance articles: the
; same answer the store gave when it retained the bytes themselves.  The
; Message-ID is a string (the host passes the parsed header's); a NIL
; Message-ID would match a NIL list element, which alpha makes an article.
(defthm fn-store-existing-action-is-the-verdict-over-alpha
  (implies (stringp msgid)
  (equal (fn-store-existing-action msgid payload groups s fn-arena)
         (fn-rcl-action-over msgid payload groups
                             (fn-articles-wire-of
                              (fn-state-articles (fn-node-acceptance (fn-sn-node s)))
                              fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-store-existing-action fn-rcl-action-over)
                                  (fn-handle-bytes fn-rcl-same-articlep)))))

;; Withdrawn from includers (lane rule-hygiene, tools/rule_cost.py).
;; Each is tried in includers' proofs and pays for its frames in
;; almost none (planning/evidence/rule-cost-*.json has the counts;
;; docs/proof-style.md section 8).  An includer that needs one
;; enables it where it is used.
(in-theory (disable (:rewrite fn-intern-event-arena)))
