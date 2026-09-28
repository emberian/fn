; fn: the history budget's octets are the stored octets (records-flip,
; 2026-09-27).
;
; After the flip a retained article row holds a HANDLE into the payload
; arena, not its octets (books/held-record.lisp).  `fn-sbud-record-octets'
; (books/store-budget.lisp), the sum the history bound H is checked against,
; counts such a row by `fn-sbud-row-octets': the facts' octets, which the
; intern decided once from the bytes it sealed.  This book states what that
; number IS, over the arena: the extent of the row's handle.  The relation
; `fn-sbud-rows-extents-okp' (every held row's facts octets are its handle's
; extent, the handle inside the arena) is established by the intern that
; builds every retained row at open and recovery (`fn-intern-events',
; books/store-intern.lisp), survives every later seal, and under it the
; budget's octets are the sum of the stored payloads' lengths.
;
; The host line: host/owner-host.lisp `fn-owner-publication-verdict' reads
; `fn-sbud-bytes-carried', which is `fn-sbud-bytes-used' under the carried
; index (`fn-sbud-bytes-carried-is-the-fold'), which is the sum here.
(in-package "ACL2")
(include-book "store-budget")
(include-book "store-intern")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:rewrite fn-stxa-is-no-other-wire-event))))

; One row's stored charge, read from the arena: a held row's handle extent
; (0 for a handle outside the arena), a composite row's wire composite, any
; other row its wire encoding; and an article row (held or composite) its
; memberships at `*fn-sbud-membership-octets*' each (lane membership-budget:
; the groups it is filed in, read from the row, not the arena).
(defun fn-sbud-row-stored-octets (row fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (+ (cond ((fn-held-p row)
            (if (fn-row-handle-inp row fn-arena)
                (fn-arena-payload-len (fn-record-payload row) fn-arena)
              0))
           ((fn-hstxa-p row) (len (fn-store-event-encode (fn-hstxa-stxa row))))
           (t (len (fn-store-event-encode row))))
     (* *fn-sbud-membership-octets* (fn-sbud-row-memberships row))))

; Executes by a loop (PKT-876, lane open-depth): one frame per row, read at
; the owner's start.  The :logic is the recursion, unchanged; equal by the
; guard proof.
(defun fn-sbud-stored-octets-acc (rows fn-arena acc)
  (declare (xargs :stobjs fn-arena :guard (acl2-numberp acc)))
  (if (consp rows)
      (fn-sbud-stored-octets-acc (cdr rows) fn-arena
                                 (+ acc (fn-sbud-row-stored-octets (car rows) fn-arena)))
    acc))

(defun fn-sbud-stored-octets (rows fn-arena)
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (mbe :logic
       (if (consp rows)
           (+ (fn-sbud-row-stored-octets (car rows) fn-arena)
              (fn-sbud-stored-octets (cdr rows) fn-arena))
         0)
       :exec (fn-sbud-stored-octets-acc rows fn-arena 0)))

(encapsulate ()
  (local
   (defthm fn-sbud-stored-octets-acc-is-plus
     (implies (acl2-numberp acc)
              (equal (fn-sbud-stored-octets-acc rows fn-arena acc)
                     (+ acc (fn-sbud-stored-octets rows fn-arena))))
     :hints (("Goal" :in-theory (disable fn-sbud-row-stored-octets)))))
  (verify-guards fn-sbud-stored-octets
    :hints (("Goal" :in-theory (disable fn-sbud-row-stored-octets)))))

; The relation: every held row's facts octets are its handle's extent.
(defun fn-sbud-row-extent-okp (h fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (and (fn-row-handle-inp h fn-arena)
       (equal (nfix (fn-hf-octets (fn-held-facts h)))
              (fn-arena-payload-len (fn-record-payload h) fn-arena))))

(defun fn-sbud-rows-extents-okp (rows fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (cond ((atom rows) t)
        ((fn-held-p (car rows))
         (and (fn-sbud-row-extent-okp (car rows) fn-arena)
              (fn-sbud-rows-extents-okp (cdr rows) fn-arena)))
        (t (fn-sbud-rows-extents-okp (cdr rows) fn-arena))))

; -----------------------------------------------------------------------------
; KEYSTONE (the budget's octets are the stored charges).  Under the relation,
; the sum `fn-sbud-record-octets' is the sum of the rows' stored charges:
; each held row counts its payload's extent in the arena and its
; memberships (restated by lane membership-budget, 2026-09-27).
(defthm fn-sbud-record-octets-is-the-stored-octets
  (implies (fn-sbud-rows-extents-okp rows fn-arena)
           (equal (fn-sbud-record-octets rows)
                  (fn-sbud-stored-octets rows fn-arena)))
  :hints (("Goal" :induct (fn-sbud-rows-extents-okp rows fn-arena)
           :expand ((fn-sbud-record-octets rows)
                    (fn-sbud-stored-octets rows fn-arena))
           :in-theory (e/d (fn-sbud-row-octets fn-sbud-row-memberships)
                           (fn-store-event-encode fn-row-handle-inp
                            fn-arena-payload-len)))))

; The same over the store: the committed record octets the host reads.
(defthm fn-sbud-bytes-used-is-the-stored-octets
  (implies (fn-sbud-rows-extents-okp (fn-sf-records (fn-sn-files s)) fn-arena)
           (equal (fn-sbud-bytes-used s)
                  (fn-sbud-stored-octets (fn-sf-records (fn-sn-files s)) fn-arena)))
  :hints (("Goal" :in-theory (e/d (fn-sbud-bytes-used)
                                  (fn-sbud-record-octets fn-sbud-stored-octets
                                   fn-sbud-rows-extents-okp)))))

; -----------------------------------------------------------------------------
; The intern establishes the relation.
(local (defthm fn-sbud-nth-of-append-at-len
  (equal (nth (len a) (append a (list x))) x)))

; The arena is read through its interface here (a seal keeps every sealed
; handle), the list view opened only in the two one-row lemmas.
(local (in-theory (disable fn-arena-payload-is-nth fn-arena-count-is-len
                           fn-arena-seal-list-is-append fn-arena-p-is-payload-listp
                           fn-arena-get-is-nth fn-arena-payload-len-is-len-nth)))

; A sealed handle keeps its extent and stays inside the arena.
(local (defthm fn-sbud-nth-of-append-below
  (implies (and (natp i) (< i (len a)))
           (equal (nth i (append a b)) (nth i a)))))

(local (defthm fn-sbud-row-extent-okp-survives-seal
  (implies (and (fn-arena-p fn-arena) (fn-sbud-row-extent-okp h fn-arena))
           (fn-sbud-row-extent-okp h (fn-arena-seal-list xs fn-arena)))
  :hints (("Goal" :in-theory (enable fn-row-handle-inp fn-arena-count-is-len
                                     fn-arena-payload-len-is-len-nth
                                     fn-arena-seal-list-is-append
                                     fn-arena-p-is-payload-listp)))))

; Exported: the POST's seal keeps every retained row's extent
; (books/store-budget-stored-post.lisp).
(defthm fn-sbud-rows-extents-okp-survives-seal
  (implies (and (fn-arena-p fn-arena) (fn-sbud-rows-extents-okp rows fn-arena))
           (fn-sbud-rows-extents-okp rows (fn-arena-seal-list xs fn-arena)))
  :hints (("Goal" :in-theory (disable fn-sbud-row-extent-okp))))

(local (defthm fn-sbud-rows-extents-okp-survives-intern-event
  (implies (and (fn-arena-p fn-arena) (fn-sbud-rows-extents-okp rows fn-arena))
           (fn-sbud-rows-extents-okp
            rows (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))
  :hints (("Goal" :in-theory (disable fn-sbud-rows-extents-okp fn-record-p fn-stxa-p
                                      fn-replay-composite-record)))))

; One event's intern leaves an arena (from the exported list form).
(local (defthm fn-sbud-arena-p-of-intern-event
  (implies (and (fn-arena-p fn-arena) (fn-wire-event-p w))
           (fn-arena-p (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))
  :hints (("Goal" :use ((:instance fn-intern-events-arena-p (ws (list w))))
           :expand ((fn-intern-events (list w) keyring generation fn-arena))
           :in-theory (disable fn-intern-events-arena-p fn-intern-event
                               fn-wire-event-p fn-intern-event-arena)))))

(local (defthm fn-sbud-rows-extents-okp-survives-intern-events
  (implies (and (fn-arena-p fn-arena) (fn-wire-event-listp ws)
                (fn-sbud-rows-extents-okp rows fn-arena))
           (fn-sbud-rows-extents-okp
            rows (mv-nth 1 (fn-intern-events ws keyring generation fn-arena))))
  :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
           :in-theory (e/d (fn-intern-events)
                           (fn-intern-event fn-intern-event-arena
                            fn-sbud-rows-extents-okp fn-wire-event-p))))))

; The row one event interns satisfies the relation in the arena it leaves.
(local (defthm fn-sbud-intern-list-extent
  (implies (and (fn-arena-p fn-arena) (fn-record-p w))
           (fn-sbud-row-extent-okp
            (mv-nth 0 (fn-cat-intern-list w keyring generation fn-arena))
            (mv-nth 1 (fn-cat-intern-list w keyring generation fn-arena))))
  :hints (("Goal" :in-theory (e/d (fn-cat-intern-list fn-held-facts-of
                                   fn-row-handle-inp fn-arena-count-is-len
                                   fn-arena-payload-len-is-len-nth
                                   fn-arena-seal-list-is-append)
                                  (fn-held-context-of fn-hf-split-index
                                   fn-hf-body-lines-of))))))

; A composite row is not a held row (its head is :hstxa, a held row's a
; natural).
(local (defthm fn-sbud-hstxa-make-is-not-held
  (not (fn-held-p (fn-hstxa-make stxa held)))
  :hints (("Goal" :use ((:instance fn-held-p-forward-natural-head
                                   (x (fn-hstxa-make stxa held))))
           :in-theory (e/d (fn-hstxa-make) (fn-held-p fn-held-p-forward-natural-head))))))

(local (defthm fn-sbud-intern-event-extent
  (implies (and (fn-arena-p fn-arena) (natp generation)
                (not (equal (mv-nth 0 (fn-intern-event w keyring generation fn-arena)) :bad)))
           (fn-sbud-rows-extents-okp
            (list (mv-nth 0 (fn-intern-event w keyring generation fn-arena)))
            (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))
  :hints (("Goal" :cases ((fn-record-p w) (fn-stxa-p w))
           :use ((:instance fn-sbud-intern-list-extent)
                 (:instance fn-sbud-intern-list-extent (w (fn-replay-composite-record w)))
                 (:instance fn-held-p-of-intern-list)
                 (:instance fn-held-is-no-wire-event (x w)))
           :in-theory (e/d (fn-intern-event)
                           (fn-cat-intern-list fn-sbud-row-extent-okp
                            fn-sbud-intern-list-extent fn-held-p-of-intern-list
                            fn-held-is-no-wire-event fn-held-p
                            fn-replay-composite-record fn-stxa-p fn-record-p))))))

(local (defthm fn-sbud-rows-extents-okp-of-cons
  (implies (syntaxp (not (equal rs ''nil)))
           (equal (fn-sbud-rows-extents-okp (cons r rs) fn-arena)
                  (and (fn-sbud-rows-extents-okp (list r) fn-arena)
                       (fn-sbud-rows-extents-okp rs fn-arena))))))

(local (defthm fn-sbud-intern-events-step-extent
  (implies (and (fn-arena-p fn-arena) (natp generation) (fn-wire-event-p w)
                (fn-wire-event-listp ws)
                (not (equal (car (fn-intern-event w keyring generation fn-arena)) :bad)))
           (fn-sbud-rows-extents-okp
            (list (car (fn-intern-event w keyring generation fn-arena)))
            (mv-nth 1 (fn-intern-events ws keyring generation
                                        (mv-nth 1 (fn-intern-event w keyring generation fn-arena))))))
  :hints (("Goal" :in-theory (disable fn-intern-event fn-intern-events fn-sbud-rows-extents-okp
                                      fn-sbud-intern-event-extent fn-intern-event-arena
                                      fn-sbud-rows-extents-okp-survives-intern-events)
           :use ((:instance fn-sbud-intern-event-extent)
                 (:instance fn-sbud-rows-extents-okp-survives-intern-events
                  (rows (list (car (fn-intern-event w keyring generation fn-arena))))
                  (fn-arena (mv-nth 1 (fn-intern-event w keyring generation fn-arena)))))))))

(local (defthm fn-sbud-rows-extents-okp-of-atom
  (implies (atom rows) (fn-sbud-rows-extents-okp rows fn-arena))))

(defthm fn-intern-events-extents-okp
  (implies (and (fn-arena-p fn-arena) (natp generation) (fn-wire-event-listp ws)
                (not (equal (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)) :bad)))
           (fn-sbud-rows-extents-okp (mv-nth 0 (fn-intern-events ws keyring generation fn-arena))
                                     (mv-nth 1 (fn-intern-events ws keyring generation fn-arena))))
  :hints (("Goal" :induct (fn-intern-events ws keyring generation fn-arena)
           :in-theory (e/d (fn-intern-events)
                           (fn-intern-event fn-intern-event-arena
                            fn-sbud-rows-extents-okp fn-wire-event-p)))))

; KEYSTONE (from the open).  The rows the intern builds from the store's wire
; events count, against the history bound, exactly the octets they store:
; each held row its payload's extent in the arena the intern leaves.  No
; refusal hypothesis: a refused intern (:bad) holds no row and both sums are
; 0 (the weakened statement, proved; the relation lemma above keeps it).
(defthm fn-intern-events-budget-octets-are-the-stored-octets
  (implies (and (fn-arena-p fn-arena) (natp generation) (fn-wire-event-listp ws))
           (equal (fn-sbud-record-octets (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)))
                  (fn-sbud-stored-octets (mv-nth 0 (fn-intern-events ws keyring generation fn-arena))
                                         (mv-nth 1 (fn-intern-events ws keyring generation fn-arena)))))
  :hints (("Goal" :cases ((equal (mv-nth 0 (fn-intern-events ws keyring generation fn-arena)) :bad))
           :use (fn-intern-events-extents-okp)
           :in-theory (disable fn-intern-events fn-intern-events-extents-okp
                               fn-sbud-rows-extents-okp))))

(in-theory (disable fn-sbud-row-stored-octets fn-sbud-row-extent-okp))
