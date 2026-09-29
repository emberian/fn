; fn: the acceptance node's articles ARE the retained rows' (W5b, lane
; stx-model-2, 2026-09-29): the carried correspondence PRF-995 named.
;
; books/stx-lace-rows.lisp fn-stx-lace-of-node-is-the-rows-lace (PRF-995)
; equates the node lace (books/stx-node-lace.lisp fn-stx-lace, the octet
; model over each handle's bytes) with the retained rows' lace under a
; hypothesis nothing carried: that ALPHA of the acceptance node's articles is
; the rows' articles read through the same arena.  The lace reads one field
; of an article -- its payload -- so what the served path must carry is
; arena-free: the node's articles and the indexed rows name the same
; Message-IDs and the same HANDLES, in the same (newest-first) order.  That
; is fn-snc-correspondp below, a relation between two fields of the store
; state, carried the way books/store-node.lisp carries fn-sn-indexedp
; (deliberately NOT a conjunct of fn-sn-statep, the guard the host checks on
; every call: D20, D21) and stated over the same rows, fn-sn-indexed-rows --
; in :completing the last row is durable but the node has not installed it
; (fn-install-pending and the record move are two steps of one completion),
; after a crash the node is the empty one and no row is indexed.
;
; The keystone fn-snc-node-lace-is-the-rows-lace: under the carried
; correspondence and the rows' context invariant, fn-stx-lace of the node IS
; fn-sn-lace-of-rows of the indexed rows -- PRF-995's conclusion with its
; open hypothesis replaced by the carried one.  The lace depends on the
; payloads alone (fn-snc-lace-of-store-reads-only-payloads), the payloads of
; ALPHA are the handles' bytes, and so are the rows' articles' payloads
; (fn-row-bytes is fn-handle-bytes of the row's handle).
;
; Establishment and preservation: fn-sn-initial (no articles, no rows) and
; fn-sn-crash (the empty node, no indexed row) are here; the recovery (the
; replay equality: acceptance-payload-ref.lisp's induction with
; fn-apr-article-arm-installs-the-record-payload gives each consed article
; its record's Message-ID and payload), the finish (its article arm is gated
; on fn-sn-record-bindsp, which names the pending's Message-ID and payload
; as the completion record's), prepare, the I/O steps, set-keyring
; (fn-sn-recontext-rows changes contexts only), refuse-reservation,
; known-abort and sweep-staging are the successor lane's, listed in
; build/coordinator/lanedumps/stx-model-2.md.
(in-package "ACL2")
(include-book "store-node-invariants")
(include-book "stx-lace-rows")

; -----------------------------------------------------------------------------
; The keys: (Message-ID . handle), newest first on both sides

(defun fn-snc-article-keys (articles)
  (declare (xargs :guard t))
  (if (atom articles)
      nil
    (cons (cons (fn-article-msgid (car articles))
                (fn-article-payload (car articles)))
          (fn-snc-article-keys (cdr articles)))))

(defun fn-snc-row-key (row)
  (declare (xargs :guard t))
  (cons (fn-record-msgid row) (fn-record-payload row)))

; Mirrors store-intern.lisp fn-rows-articles-newest-first arm for arm.
(defun fn-snc-row-keys-newest-first (rows)
  (declare (xargs :guard t))
  (cond ((atom rows) nil)
        ((fn-held-p (car rows))
         (append (fn-snc-row-keys-newest-first (cdr rows))
                 (list (fn-snc-row-key (car rows)))))
        ((fn-hstxa-p (car rows))
         (append (fn-snc-row-keys-newest-first (cdr rows))
                 (list (fn-snc-row-key (fn-hstxa-held (car rows))))))
        (t (fn-snc-row-keys-newest-first (cdr rows)))))

; THE CARRIED CORRESPONDENCE.
(defun fn-snc-correspondp (s)
  (declare (xargs :guard t))
  (equal (fn-snc-article-keys (fn-stx-store (fn-sn-node s)))
         (fn-snc-row-keys-newest-first (fn-sn-indexed-rows s))))

; -----------------------------------------------------------------------------
; The lace reads the payloads alone

(defun fn-snc-payloads (articles)
  (declare (xargs :guard t))
  (if (atom articles)
      nil
    (cons (fn-article-payload (car articles)) (fn-snc-payloads (cdr articles)))))

(defun fn-snc-lace-of-payloads (payloads keyring)
  (declare (xargs :guard (fn-prin-keyringp keyring)))
  (if (consp payloads)
      (append (fn-snc-lace-of-payloads (cdr payloads) keyring)
              (fn-stx-delta (car payloads) keyring))
    nil))

(defthm fn-snc-lace-of-store-reads-only-payloads
  (equal (fn-stx-lace-of-store articles keyring)
         (fn-snc-lace-of-payloads (fn-snc-payloads articles) keyring))
  :hints (("Goal" :in-theory (e/d ((:d fn-stx-lace-of-store)) (fn-stx-delta)))))

; The bytes each handle denotes, in order.
(defun fn-snc-bytes-of-handles (handles fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (atom handles)
      nil
    (cons (fn-handle-bytes (car handles) fn-arena)
          (fn-snc-bytes-of-handles (cdr handles) fn-arena))))

(defthm fn-snc-payloads-of-alpha
  (equal (fn-snc-payloads (fn-articles-wire-of articles fn-arena))
         (fn-snc-bytes-of-handles (strip-cdrs (fn-snc-article-keys articles)) fn-arena))
  :hints (("Goal" :in-theory (e/d (fn-articles-wire-of) (fn-handle-bytes)))))

(local (defthm fn-snc-row-bytes-is-handle-bytes
  (equal (fn-row-bytes row fn-arena)
         (fn-handle-bytes (fn-record-payload row) fn-arena))
  :hints (("Goal" :in-theory (enable fn-row-bytes fn-handle-bytes)))))

(local (defthm fn-snc-payloads-of-append
  (equal (fn-snc-payloads (append a b))
         (append (fn-snc-payloads a) (fn-snc-payloads b)))))

(local (defthm fn-snc-bytes-of-handles-of-append
  (equal (fn-snc-bytes-of-handles (append a b) fn-arena)
         (append (fn-snc-bytes-of-handles a fn-arena)
                 (fn-snc-bytes-of-handles b fn-arena)))))

(local (defthm fn-snc-strip-cdrs-of-append
  (equal (strip-cdrs (append a b)) (append (strip-cdrs a) (strip-cdrs b)))))

(defthm fn-snc-payloads-of-the-rows-articles
  (equal (fn-snc-payloads (fn-rows-articles-newest-first rows fn-arena))
         (fn-snc-bytes-of-handles (strip-cdrs (fn-snc-row-keys-newest-first rows)) fn-arena))
  :hints (("Goal" :in-theory (e/d (fn-rows-articles-newest-first)
                                  (fn-handle-bytes fn-row-bytes fn-held-p fn-hstxa-p)))))

; -----------------------------------------------------------------------------
; KEYSTONE: under the carried correspondence the node lace is the rows' lace.

(defthm fn-snc-node-lace-is-the-rows-lace
  (implies (and (fn-snc-correspondp s)
                (fn-rows-contexts-okp (fn-sn-indexed-rows s) keyring generation fn-arena))
           (equal (fn-stx-lace (fn-sn-node s) keyring fn-arena)
                  (fn-sn-lace-of-rows (fn-sn-indexed-rows s))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-sn-lace-of-rows-is-the-wire-lace
                            (rows (fn-sn-indexed-rows s)))
                 (:instance fn-snc-lace-of-store-reads-only-payloads
                            (articles (fn-articles-wire-of (fn-stx-store (fn-sn-node s)) fn-arena)))
                 (:instance fn-snc-lace-of-store-reads-only-payloads
                            (articles (fn-rows-articles-newest-first (fn-sn-indexed-rows s) fn-arena))))
           :in-theory (e/d (fn-stx-lace fn-snc-correspondp)
                           (fn-sn-lace-of-rows-is-the-wire-lace fn-sn-lace-of-rows
                            fn-stx-lace-of-store fn-rows-articles-newest-first
                            fn-rows-contexts-okp fn-articles-wire-of fn-sn-indexed-rows
                            fn-snc-article-keys fn-snc-row-keys-newest-first
                            fn-snc-lace-of-store-reads-only-payloads fn-stx-store)))))

; -----------------------------------------------------------------------------
; Establishment at the initial store; preservation by a crash

(defthm fn-snc-initial-corresponds
  (fn-snc-correspondp (fn-sn-initial groups capacity))
  :hints (("Goal" :in-theory (enable fn-sn-initial fn-sn-indexed-rows fn-sn-indexed-rows-of
                                     fn-stx-store fn-node-initial-state fn-initial-state
                                     fn-sf-initial-state))))

(local (defthm fn-snc-statep-files
  (implies (fn-sn-statep s) (fn-sf-statep (fn-sn-files s)))
  :hints (("Goal" :in-theory (e/d (fn-sn-statep) (fn-sf-statep fn-node-statep))))))

; -by-recomputation, as fn-sn-crash-preserves-indexedp-by-recomputation: the
; node is reset to the empty one and no row is indexed after a crash.
(defthm fn-snc-crash-preserves-correspondp-by-recomputation
  (implies (and (fn-sn-statep s) (fn-snc-correspondp s))
           (fn-snc-correspondp (fn-sn-crash s frontier-choice record-choice)))
  :hints (("Goal" :in-theory (e/d (fn-sn-crash fn-sn-indexed-rows fn-stx-store
                                   fn-node-initial-state fn-initial-state)
                                  (fn-sn-statep fn-sf-crash fn-sf-crash-choicep
                                   fn-sn-indexed-rows-of))
           :use ((:instance fn-sn-indexed-rows-of-crash (files (fn-sn-files s)))))))

(in-theory (disable (:d fn-snc-correspondp)))
