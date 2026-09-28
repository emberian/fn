; fn: the statement lace of the RETAINED store (records-flip, 2026-09-27).
;
; books/stx-lace.lisp projects the lace from a node's accepted articles by
; reading each article's octets (fn-stx-lace-of-store).  After the flip the
; acceptance state's article carries an arena HANDLE, not octets, so that
; projection of a live store's node reads no statement at all: it is the
; lace of a WIRE node, the specification.  The store retains ROWS
; (books/store-intern.lisp) whose context was decided from their bytes at
; the intern, so the lace of the retained store is the rows' context deltas
; in history order, and no byte is re-read:
;
;   fn-sn-lace-of-rows      the rows' deltas (fn-sn-row-delta), oldest first:
;                           the lace fn-sn-index-of-rows (books/store-node.lisp)
;                           is the incremental twin of.
;
; KEYSTONES.  (1) fn-sn-lace-of-rows-is-the-wire-lace: under the context
; invariant (fn-rows-contexts-okp, established by the intern and re-established
; by fn-store-set-keyring) the rows' lace IS the wire lace of the rows'
; articles read through the arena (fn-rows-articles-newest-first), the same
; ALPHA books/store-intern.lisp's fn-rows-index-is-the-wire-index uses.
; (2) fn-sn-index-of-rows-agrees-with-lace: S3-3 over the retained store --
; the index the store keeps answers lookup and the equivocator question as
; the rows' lace does.  (3) fn-sn-lace-of-rows-of-accept-is-merge: a history
; that grows by one article row (the store's completion moves the staged row
; into fn-sf-records) grows its lace by a lace merge of the row's delta when
; that delta is fresh; S3-1 and S3-2 then hold over rows as over the wire
; (fn-sn-rows-transit-ids-are-union, fn-sn-rows-transit-equivocation-
; survives).
(in-package "ACL2")
(include-book "store-intern")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-sn-completion-is-last-p))))

(local (in-theory (enable fn-sn-row-delta)))
(local (in-theory (disable fn-arena-payload-is-nth fn-arena-count-is-len
                           fn-arena-seal-list-is-append fn-arena-p-is-payload-listp
                           fn-arena-get-is-nth fn-arena-payload-len-is-len-nth)))

(defun fn-sn-lace-of-rows (rows)
  (declare (xargs :guard t))
  (if (atom rows)
      nil
    (append (fn-sn-row-delta (car rows))
            (fn-sn-lace-of-rows (cdr rows)))))

(local (defthm fn-slr-lace-p-of-append
  (implies (and (fn-lace-p a) (fn-lace-p b))
           (fn-lace-p (append a b)))
  :hints (("Goal" :in-theory (enable fn-lace-p)))))

(defthm fn-sn-lace-of-rows-is-lace
  (fn-lace-p (fn-sn-lace-of-rows rows))
  :hints (("Goal" :in-theory (disable fn-sn-row-delta))))

(defthm fn-sn-lace-of-rows-is-true-list
  (true-listp (fn-sn-lace-of-rows rows)))

(defthm fn-sn-lace-of-rows-of-append
  (equal (fn-sn-lace-of-rows (append a b))
         (append (fn-sn-lace-of-rows a) (fn-sn-lace-of-rows b)))
  :hints (("Goal" :in-theory (disable fn-sn-row-delta))))

; -----------------------------------------------------------------------------
; (1) The rows' lace is the wire lace of their articles.

(local (defthm fn-slr-lace-of-store-of-append-one
  (equal (fn-stx-lace-of-store (append articles (list a)) keyring)
         (append (fn-stx-delta (fn-article-payload a) keyring)
                 (fn-stx-lace-of-store articles keyring)))
  :hints (("Goal" :in-theory (disable fn-stx-delta)))))

(local (defthm fn-slr-article-payload-of-make-article
  (equal (fn-article-payload (fn-make-article msgid payload groups memberships pin stamp))
         payload)
  :hints (("Goal" :in-theory (enable fn-make-article fn-article-payload)))))

(local (defthm fn-slr-hc-delta-of-held-context-of
  (equal (fn-hc-delta (fn-held-context-of bytes keyring generation))
         (fn-stx-delta bytes keyring))
  :hints (("Goal" :in-theory (enable fn-held-context-of)))))

(local (defthm fn-slr-lace-of-store-of-nil
  (equal (fn-stx-lace-of-store nil keyring) nil)))

; A row whose context is the context of its bytes has its bytes' delta.
(local (defthm fn-slr-delta-of-okp-context
  (implies (fn-row-context-okp h keyring generation fn-arena)
           (equal (fn-hc-delta (fn-held-context h))
                  (fn-stx-delta (fn-row-bytes h fn-arena) keyring)))
  :hints (("Goal" :in-theory (e/d (fn-row-context-okp)
                                  (fn-stx-delta fn-held-context-of fn-row-bytes))))))

(defthm fn-sn-lace-of-rows-is-the-wire-lace
  (implies (fn-rows-contexts-okp rows keyring generation fn-arena)
           (equal (fn-sn-lace-of-rows rows)
                  (fn-stx-lace-of-store (fn-rows-articles-newest-first rows fn-arena)
                                        keyring)))
  :hints (("Goal" :induct (fn-sn-lace-of-rows rows)
           :in-theory (e/d (fn-rows-contexts-okp fn-rows-articles-newest-first)
                           (fn-stx-delta fn-held-context-of fn-row-bytes fn-row-context-okp
                            fn-stx-lace-of-store)))))

; -----------------------------------------------------------------------------
; (2) S3-3 over the retained store: the store's index agrees with the rows'
; lace.  fn-rows-index-is-the-wire-index and (1) put both on the same wire
; articles, where books/stx-index.lisp's agreement holds.

(defthm fn-sn-index-of-rows-agrees-with-lace
  (implies (fn-rows-contexts-okp rows keyring generation fn-arena)
           (and (equal (fn-stx-index-lookup (fn-sn-index-of-rows rows) id)
                       (fn-lace-lookup (fn-sn-lace-of-rows rows) id))
                (iff (fn-stx-index-equivocatorp (fn-sn-index-of-rows rows) p i)
                     (fn-lace-equivocatorp (fn-sn-lace-of-rows rows) p i))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-rows-index-is-the-wire-index)
                        (:instance fn-sn-lace-of-rows-is-the-wire-lace)
                        (:instance fn-stx-index-bindings-agree
                         (articles (fn-rows-articles-newest-first rows fn-arena)))
                        (:instance fn-stx-index-equivocators-agree
                         (articles (fn-rows-articles-newest-first rows fn-arena))))
           :in-theory (disable fn-rows-index-is-the-wire-index
                               fn-sn-lace-of-rows-is-the-wire-lace
                               fn-stx-index-bindings-agree fn-stx-index-equivocators-agree
                               fn-sn-index-of-rows fn-sn-lace-of-rows
                               fn-rows-articles-newest-first fn-rows-contexts-okp
                               fn-stx-index-of-store fn-stx-lace-of-store
                               fn-stx-index-lookup fn-stx-index-equivocatorp
                               (:d fn-lace-equivocatorp)))))

;
; THE SERVED QUERIES (S3-3's subject gap, PRF-023).  The host's
; fn-store-sn-statement and fn-store-sn-equivocator (host/store-node-host.lisp)
; call fn-sn-statement-lookup and fn-sn-equivocatorp, which read the carried
; index and nothing else.  Under the carried index invariant fn-sn-indexedp
; (the index is fn-sn-index-of-rows of the indexed rows) and the context
; invariant of those rows, each answers exactly as the lace of the retained
; store; by (1) that is the wire lace of the rows' articles read through the
; arena.  Restated here over rows (records-flip): the pre-flip statement
; equated them with fn-stx-lace of the node, which reads no statement from a
; node whose articles carry handles.
(defthm fn-sn-statement-lookup-is-the-lace-lookup
  (implies (and (fn-sn-indexedp s)
                (fn-rows-contexts-okp (fn-sn-indexed-rows s) keyring generation fn-arena))
           (equal (fn-sn-statement-lookup s id)
                  (fn-lace-lookup (fn-sn-lace-of-rows (fn-sn-indexed-rows s)) id)))
  :hints (("Goal" :use ((:instance fn-sn-index-of-rows-agrees-with-lace
                         (rows (fn-sn-indexed-rows s)) (p nil) (i nil)))
           :in-theory (e/d (fn-sn-indexedp fn-sn-statement-lookup)
                           (fn-sn-statep fn-sn-index-of-rows fn-sn-indexed-rows
                            fn-sn-lace-of-rows fn-rows-contexts-okp
                            fn-stx-index-lookup fn-lace-lookup)))))

(defthm fn-sn-equivocatorp-is-the-lace-equivocator
  (implies (and (fn-sn-indexedp s)
                (fn-rows-contexts-okp (fn-sn-indexed-rows s) keyring generation fn-arena))
           (iff (fn-sn-equivocatorp s creator incarnation)
                (fn-lace-equivocatorp (fn-sn-lace-of-rows (fn-sn-indexed-rows s))
                                      creator incarnation)))
  :hints (("Goal" :use ((:instance fn-sn-index-of-rows-agrees-with-lace
                         (rows (fn-sn-indexed-rows s)) (p creator) (i incarnation)))
           :in-theory (e/d (fn-sn-indexedp fn-sn-equivocatorp)
                           (fn-sn-statep fn-sn-index-of-rows fn-sn-indexed-rows
                            fn-sn-lace-of-rows fn-rows-contexts-okp
                            fn-stx-index-equivocatorp (:d fn-lace-equivocatorp))))))

; -----------------------------------------------------------------------------
; (3) The transit bridge over rows.  A row whose context is the context of
; its bytes contributes a delta that is nil or one statement.

(local (defthm fn-slr-row-delta-of-okp-row
  (implies (fn-rows-contexts-okp (list row) keyring generation fn-arena)
           (equal (fn-sn-row-delta row)
                  (cond ((fn-held-p row) (fn-stx-delta (fn-row-bytes row fn-arena) keyring))
                        ((fn-hstxa-p row)
                         (fn-stx-delta (fn-row-bytes (fn-hstxa-held row) fn-arena) keyring))
                        (t nil))))
  :hints (("Goal" :in-theory (e/d (fn-rows-contexts-okp fn-row-context-okp)
                                  (fn-stx-delta fn-held-context-of fn-row-bytes))))))

(defthm fn-sn-row-delta-is-nil-or-singleton
  (implies (fn-rows-contexts-okp (list row) keyring generation fn-arena)
           (and (true-listp (fn-sn-row-delta row))
                (not (consp (cdr (fn-sn-row-delta row))))))
  :hints (("Goal" :in-theory (disable fn-sn-row-delta fn-row-bytes fn-rows-contexts-okp)
           :use ((:instance fn-slr-row-delta-of-okp-row)))))

(defthm fn-sn-lace-of-rows-of-accept-is-merge
  (implies (and (fn-rows-contexts-okp (list row) keyring generation fn-arena)
                (fn-stx-delta-freshp (fn-sn-lace-of-rows rows) (fn-sn-row-delta row)))
           (equal (fn-sn-lace-of-rows (append rows (list row)))
                  (fn-lace-merge (fn-sn-lace-of-rows rows) (fn-sn-row-delta row))))
  :hints (("Goal" :in-theory (disable fn-sn-row-delta fn-lace-merge fn-stx-delta-freshp
                                      fn-sn-lace-of-rows fn-rows-contexts-okp
                                      fn-stx-merge-of-fresh-short-delta)
           :use ((:instance fn-sn-row-delta-is-nil-or-singleton)
                 (:instance fn-stx-merge-of-fresh-short-delta
                  (lace (fn-sn-lace-of-rows rows)) (delta (fn-sn-row-delta row)))
                 (:instance fn-sn-lace-of-rows-of-append (a rows) (b (list row)))))
          ("Subgoal 1" :in-theory (enable fn-sn-lace-of-rows))))

; S3-1 over rows (corollary of fn-lace-merge-ids-are-union and the bridge).
(defthm fn-sn-rows-transit-ids-are-union
  (implies (and (fn-rows-contexts-okp (list row) keyring generation fn-arena)
                (fn-stx-delta-freshp (fn-sn-lace-of-rows rows) (fn-sn-row-delta row)))
           (iff (member-equal h (fn-lace-ids (fn-sn-lace-of-rows (append rows (list row)))))
                (or (member-equal h (fn-lace-ids (fn-sn-lace-of-rows rows)))
                    (member-equal h (fn-lace-ids (fn-sn-row-delta row))))))
  :hints (("Goal" :use ((:instance fn-sn-lace-of-rows-of-accept-is-merge)
                        (:instance fn-lace-merge-ids-are-union
                         (lace (fn-sn-lace-of-rows rows)) (delta (fn-sn-row-delta row))))
           :in-theory (disable fn-sn-lace-of-rows-of-accept-is-merge fn-lace-merge-ids-are-union
                               fn-sn-lace-of-rows fn-sn-row-delta fn-lace-merge
                               fn-stx-delta-freshp fn-rows-contexts-okp
                               fn-sn-lace-of-rows-of-append))))

; S3-2's survival half over rows: a later accepted row never erases a fork.
(defthm fn-sn-rows-transit-equivocation-survives
  (implies (and (fn-rows-contexts-okp (list row) keyring generation fn-arena)
                (fn-stx-delta-freshp (fn-sn-lace-of-rows rows) (fn-sn-row-delta row))
                (fn-lace-equivocatorp (fn-sn-lace-of-rows rows) p i))
           (fn-lace-equivocatorp (fn-sn-lace-of-rows (append rows (list row))) p i))
  :hints (("Goal" :use ((:instance fn-sn-lace-of-rows-of-accept-is-merge)
                        (:instance fn-lace-merge-preserves-equivocation
                         (lace (fn-sn-lace-of-rows rows)) (delta (fn-sn-row-delta row))))
           :in-theory (disable fn-sn-lace-of-rows-of-accept-is-merge
                               fn-lace-merge-preserves-equivocation
                               fn-sn-lace-of-rows fn-sn-row-delta fn-lace-merge
                               fn-stx-delta-freshp fn-rows-contexts-okp
                               fn-sn-lace-of-rows-of-append (:d fn-lace-equivocatorp)))))

(in-theory (disable fn-sn-lace-of-rows))
