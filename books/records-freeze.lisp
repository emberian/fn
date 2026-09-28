; fn: the records freeze (PKT-293/167; D27, D33; lane records-freeze,
; 2026-09-26): the retained record view's extent and projection, the replay
; over both views, and payload identity across reclamation.
;
; The two views of one record are books/catalog-record.lisp's: the WIRE
; record (`fn-record-p', an octet-list payload, the codec's domain,
; unchanged) and the HELD record (`fn-held-p', the same eleven positions
; read by the same accessors, the payload a HANDLE into `fn-arena', then the
; byte facts and the context decided once at intern).  Alpha is
; `fn-held-wire-of' (materialize by handle); intern is `fn-cat-intern-list'
; / `fn-cat-intern'; `fn-cat-intern-list-materializes' says alpha of intern
; is the identity on the wire record.  This book states what the freeze
; owes on top of that, each over the arena's GENERIC (books/payload-arena
; .lisp), so it holds of every implementation attached to it:
;
;   1. The handle's three coordinates (gpt-6's byte owner): IDENTITY, the
;      handle names the sealed bytes (`fn-rfz-served-bytes-by-definition':
;      the octets the served ARTICLE writes from the handle are the wire
;      payload); EXTENT, `fn-arena-payload-len' of the handle is the octets
;      fact decided at intern (`fn-rfz-intern-extent': no walk of the bytes
;      to know their length); LIFETIME, the handle resolves to the same
;      bytes after any later seals (section 3).  The served projection's
;      bytes: the codec over the materialized record is the wire encoding
;      (`fn-rfz-projection-bytes-by-definition').
;
;   2. REPLAY OVER BOTH VIEWS.  `fn-sn-finish' (books/store-node.lisp)
;      reads a finished record's bytes for exactly two things: the identity
;      delta it adds to the index (`fn-stx-index-add' of `fn-stx-delta',
;      recomputed over the whole store at open by `fn-stx-index-of-store' in
;      `fn-sn-recover') and the statement verdict it conses onto the verdict
;      list (`fn-stx-verdict-of-octets'); every other position it
;      transports.  The shared transition `fn-sn-finish-held'
;      (books/catalog-commit.lisp) reads both from the record's CONTEXT
;      instead.  The theorems here close the loop over a HISTORY: the fold
;      of the rows' contexts equals the store's own fold over the bytes,
;      `fn-rfz-replay-index-over-both-views' (the subject is
;      `fn-stx-index-of-store', the function `fn-sn-recover' calls) and
;      `fn-rfz-replay-verdicts-over-both-views', under the context
;      invariant `fn-rfz-contexts-okp' (every row's context is the context
;      of its bytes under the keyring and generation), which the intern
;      establishes for the row it builds (`fn-rfz-intern-context'), later
;      seals keep (`fn-rfz-contexts-okp-survives-seals') and the load fold
;      `fn-cat-load' establishes for the whole catalog
;      (`fn-rfz-load-establishes-contexts').  So replay over the retained
;      view (contexts, no bytes) is replay over the wire view (bytes).
;
;   3. PAYLOAD IDENTITY ACROSS RECLAMATION (the wave-5 review, section 1).
;      A reclaim (D13) seals the tombstone as a NEW handle and points the
;      row at it; the old handle is not removed (the arena has no delete
;      export; the bytes go at the next open's rebuild).  Two forms, both
;      proved: immutable references in the view -- a pinned row list
;      materializes the same after the reclaim's seal and any later seals
;      (`fn-rfz-pinned-rows-survive-seals'); and the versioned mapping --
;      a row's redirects ((version . handle) ...) resolve, for a reader at
;      version V, to the newest redirect at a version below V, so a view
;      pinned before the reclaim reads the original and one after reads
;      the tombstone (`fn-rfz-resolve-before-reclaim',
;      `fn-rfz-resolve-after-reclaim'; both handles keep their bytes under
;      later seals by the arena's `fn-arena-seals-keep-sealed'), and the
;      new row materializes to the tombstone
;      (`fn-rfz-reclaim-new-row-reads-the-tombstone').  Which form
;      the catalog's export takes is catalog-slice-5's; the rebuild at open
;      is `fn-cat-load-from-empty' (cited, not restated).
;
; Prefix `fn-rfz-'.  No skip-proofs; every executable function is
; guard-verified (asserted in tests/acl2/records-freeze-tests.lisp).

(in-package "ACL2")
(include-book "catalog-relation")
(include-book "records-seam")

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

; The export vocabulary stays closed here: the arena's opened view (nth, len,
; append) would take the keystones' left-hand sides apart.
(local (in-theory (disable fn-arena-payload-is-nth fn-arena-count-is-len
                           fn-arena-payload-len-is-len-nth fn-arena-get-is-nth
                           fn-arena-seal-list-is-append fn-arena-seal-buffer-is-append
                           fn-arn-seal-many-is-append fn-arena-p-is-payload-listp)))

; -----------------------------------------------------------------------------
; 1. The handle's coordinates, and the projection's bytes.

; The extent is the length of the payload.
(local (defthm fn-rfz-payload-len-is-len-payload
   (equal (fn-arena-payload-len h fn-arena) (len (fn-arena-payload h fn-arena)))
   :hints (("Goal" :in-theory (enable fn-arena-payload-len-is-len-nth fn-arena-payload-is-nth)))))

; The accessors of alpha's constructor.
(local (defthm fn-rfz-accessors-of-held-wire
   (and (equal (fn-record-payload (fn-held-wire h p)) p)
        (equal (fn-record-msgid (fn-held-wire h p)) (fn-record-msgid h))
        (equal (fn-record-groups (fn-held-wire h p)) (fn-record-groups h))
        (equal (fn-record-stamp (fn-held-wire h p)) (fn-record-stamp h)))
   :hints (("Goal" :in-theory (enable fn-held-wire fn-record-internals)))))

; IDENTITY: the bytes the served ARTICLE writes from the interned handle are
; the wire payload (fn-arena-seal-new-handle at the intern's handle).
(defthm fn-rfz-served-bytes-by-definition
  (mv-let (held fn-arena2)
    (fn-cat-intern-list w keyring generation fn-arena)
    (equal (fn-arena-payload (fn-record-payload held) fn-arena2)
           (fn-record-payload w)))
  :hints (("Goal" :in-theory (e/d (fn-cat-intern-list) ()))))

; EXTENT: the handle's length in the arena is the octets fact the intern
; decided; no walk of the bytes answers it.  No hypothesis.
(defthm fn-rfz-intern-extent
  (mv-let (held fn-arena2)
    (fn-cat-intern-list w keyring generation fn-arena)
    (equal (fn-arena-payload-len (fn-record-payload held) fn-arena2)
           (fn-hf-octets (fn-held-facts held))))
  :hints (("Goal" :in-theory (e/d (fn-cat-intern-list fn-held-facts-of) ()))))

; The served projection's BYTES: the codec over the materialized held record
; is the wire record's encoding (alpha of intern is the identity:
; fn-cat-intern-list-materializes; then the codec is applied to equals).
(defthm fn-rfz-projection-bytes-by-definition
  (implies (fn-record-shapep w)
           (mv-let (held fn-arena2)
             (fn-cat-intern-list w keyring generation fn-arena)
             (equal (fn-record-encode (fn-held-wire-of held fn-arena2))
                    (fn-record-encode w))))
  :hints (("Goal" :use ((:instance fn-cat-intern-list-materializes))
           :in-theory (disable fn-cat-intern-list-materializes))))

; -----------------------------------------------------------------------------
; 2. Replay over both views.

; Every row's handle names a sealed payload.
(defun fn-rfz-handles-inp (rows fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (atom rows)
      t
    (and (natp (fn-record-payload (car rows)))
         (< (fn-record-payload (car rows)) (fn-arena-count fn-arena))
         (fn-rfz-handles-inp (cdr rows) fn-arena))))

; The rows materialized (alpha, row by row): what a pinned view reads.
(defun fn-rfz-wire-rows (rows fn-arena)
  (declare (xargs :stobjs fn-arena :guard (fn-rfz-handles-inp rows fn-arena)))
  (if (atom rows)
      nil
    (cons (fn-held-wire-of (car rows) fn-arena)
          (fn-rfz-wire-rows (cdr rows) fn-arena))))

; The rows as the acceptance articles the store's index fold walks
; (fn-stx-store: fn-state-articles, newest first; the payload by handle,
; the numbers as memberships, the archive pin: catalog-view's
; fn-cat-row-article over a row list).
(defun fn-rfz-articles-of-rows (rows fn-arena)
  (declare (xargs :stobjs fn-arena :guard (fn-rfz-handles-inp rows fn-arena)))
  (if (atom rows)
      nil
    (let ((h (car rows)))
      (cons (fn-make-article (fn-record-msgid h)
                             (fn-arena-payload (fn-record-payload h) fn-arena)
                             (fn-record-groups h) (fn-held-numbers h) t
                             (fn-record-stamp h))
            (fn-rfz-articles-of-rows (cdr rows) fn-arena)))))

; The context invariant: every row's context is the context of its bytes
; under KEYRING and GENERATION.
(defun fn-rfz-contexts-okp (rows keyring generation fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (fn-prin-keyringp keyring) (natp generation)
                              (fn-rfz-handles-inp rows fn-arena))))
  (if (atom rows)
      t
    (and (equal (fn-held-context (car rows))
                (fn-held-context-of (fn-arena-payload (fn-record-payload (car rows)) fn-arena)
                                    keyring generation))
         (fn-rfz-contexts-okp (cdr rows) keyring generation fn-arena))))

; The retained view's folds: contexts read, no bytes.  Newest first, the
; order fn-stx-index-of-store folds (the oldest innermost) and the order
; fn-sn-verdicts is consed in (fn-sn-update-accepted: the newest at the head).
; Every row's context delta is a lace (what fn-snh-enabledp checks before
; the held finish adds it: books/catalog-commit.lisp); the index fold's guard.
(defun fn-rfz-lacesp (rows)
  (declare (xargs :guard t))
  (if (atom rows)
      t
    (and (fn-lace-p (fn-hc-delta (fn-held-context (car rows))))
         (fn-rfz-lacesp (cdr rows)))))

(defun fn-rfz-index-of-rows (rows)
  (declare (xargs :guard (fn-rfz-lacesp rows)))
  (if (atom rows)
      (fn-stx-index-empty)
    (fn-stx-index-add (fn-rfz-index-of-rows (cdr rows))
                      (fn-hc-delta (fn-held-context (car rows))))))

(defun fn-rfz-verdicts-of-rows (rows)
  (declare (xargs :guard t))
  (if (atom rows)
      nil
    (cons (cons (fn-record-msgid (car rows)) (fn-hc-verdict (fn-held-context (car rows))))
          (fn-rfz-verdicts-of-rows (cdr rows)))))

; The wire view's verdict fold: the bytes read, per record, as fn-sn-finish
; reads them (fn-stx-verdict-of-octets of the payload under the store's
; keyring and generation).  The wire view's index fold IS
; fn-stx-index-of-store (books/stx-index.lisp), the store's own definition.
(defun fn-rfz-verdicts-of-wire (wires keyring generation)
  (declare (xargs :guard (fn-prin-keyringp keyring)))
  (if (atom wires)
      nil
    (cons (cons (fn-record-msgid (car wires))
                (fn-stx-verdict-of-octets (fn-record-payload (car wires)) keyring generation))
          (fn-rfz-verdicts-of-wire (cdr wires) keyring generation))))

(local (defthm fn-rfz-context-of-fields
   (and (equal (fn-hc-delta (fn-held-context-of bytes keyring generation))
               (fn-stx-delta bytes keyring))
        (equal (fn-hc-verdict (fn-held-context-of bytes keyring generation))
               (fn-stx-verdict-of-octets bytes keyring generation)))
   :hints (("Goal" :in-theory (enable fn-held-context-of)))))

; The invariant read at a row, as rewrite rules over the closed definition:
; a non-variable equality in a hypothesis is not a rewrite rule, so the
; context of the first row is rewritten to the context of its bytes here.
(local (defthm fn-rfz-contexts-okp-cdr
   (implies (fn-rfz-contexts-okp rows keyring generation fn-arena)
            (fn-rfz-contexts-okp (cdr rows) keyring generation fn-arena))
   :hints (("Goal" :expand ((fn-rfz-contexts-okp rows keyring generation fn-arena))))))

(local (defthm fn-rfz-contexts-okp-context
   (implies (and (fn-rfz-contexts-okp rows keyring generation fn-arena) (consp rows))
            (equal (fn-held-context (car rows))
                   (fn-held-context-of (fn-arena-payload (fn-record-payload (car rows)) fn-arena)
                                       keyring generation)))
   :hints (("Goal" :expand ((fn-rfz-contexts-okp rows keyring generation fn-arena))))))

(local (in-theory (disable fn-rfz-contexts-okp)))

; KEYSTONE.  Under the context invariant, the index the retained view
; answers from its contexts is the index the store recomputes from the
; bytes of the same rows' articles: fn-stx-index-of-store, the function
; fn-sn-recover calls over fn-stx-store of the replayed node.  The
; invariant alone is the hypothesis: fn-rfz-handles-inp is the GUARD's
; requirement (fn-arena-payload's), not the theorem's (the weakened
; theorem was proved; the test book records the witness).
(defthm fn-rfz-replay-index-over-both-views
  (implies (fn-rfz-contexts-okp rows keyring generation fn-arena)
           (equal (fn-rfz-index-of-rows rows)
                  (fn-stx-index-of-store (fn-rfz-articles-of-rows rows fn-arena) keyring)))
  :hints (("Goal" :induct (fn-rfz-articles-of-rows rows fn-arena)
           :in-theory (disable fn-stx-index-add fn-stx-delta fn-held-context-of))))

; KEYSTONE.  The verdict list the retained view answers from its contexts
; is the wire view's, each verdict decided from the bytes as fn-sn-finish
; decides it.
(defthm fn-rfz-replay-verdicts-over-both-views
  (implies (fn-rfz-contexts-okp rows keyring generation fn-arena)
           (equal (fn-rfz-verdicts-of-rows rows)
                  (fn-rfz-verdicts-of-wire (fn-rfz-wire-rows rows fn-arena) keyring generation)))
  :hints (("Goal" :induct (fn-rfz-wire-rows rows fn-arena)
           :in-theory (e/d (fn-held-wire-of)
                           (fn-stx-verdict-of-octets fn-held-context-of)))))

; The invariant's life.  The intern establishes it for the row it builds
; (the handle is the old count, which after the seal denotes the payload,
; and the context is the context of that payload).
(defthm fn-rfz-intern-context
  (mv-let (held fn-arena2)
    (fn-cat-intern-list w keyring generation fn-arena)
    (and (fn-rfz-handles-inp (list held) fn-arena2)
         (fn-rfz-contexts-okp (list held) keyring generation fn-arena2)))
  :hints (("Goal" :in-theory (e/d (fn-cat-intern-list fn-rfz-contexts-okp)
                                  (fn-rfz-contexts-okp-context)))))

; Later seals keep it: every handle below the count reads the same bytes
; (fn-arena-seals-keep-sealed), and the count only grows.
(local (defthm fn-rfz-count-of-seal-many
   (implies (true-listp payloads)
            (equal (fn-arena-count (fn-arn-seal-many payloads fn-arena))
                   (+ (len payloads) (fn-arena-count fn-arena))))
   :hints (("Goal" :in-theory (enable fn-arn-seal-many-is-append fn-arena-count-is-len)))))

(defthm fn-rfz-handles-inp-survives-seals
  (implies (and (fn-rfz-handles-inp rows fn-arena) (true-listp payloads))
           (fn-rfz-handles-inp rows (fn-arn-seal-many payloads fn-arena)))
  :hints (("Goal" :induct (fn-rfz-handles-inp rows fn-arena)
           :in-theory (disable fn-arn-seal-many))))

(defthm fn-rfz-contexts-okp-survives-seals
  (implies (and (fn-rfz-handles-inp rows fn-arena)
                (fn-rfz-contexts-okp rows keyring generation fn-arena))
           (fn-rfz-contexts-okp rows keyring generation (fn-arn-seal-many payloads fn-arena)))
  :hints (("Goal" :induct (fn-rfz-handles-inp rows fn-arena)
           :in-theory (e/d (fn-rfz-contexts-okp)
                           (fn-held-context-of fn-rfz-contexts-okp-context)))))

; Neither invariant reads a row's numbers, withdrawal or context slot other
; than through fn-held-context, so the commit's assignment keeps both.
(local (defthm fn-rfz-assign-fields
   (and (equal (fn-record-payload (fn-cat-assign h c)) (fn-record-payload h))
        (equal (fn-held-context (fn-cat-assign h c)) (fn-held-context h)))
   :hints (("Goal" :in-theory (enable fn-cat-assign fn-held-with-numbers
                                      fn-record-internals fn-held-internals)))))

(local (defthm fn-rfz-handles-inp-of-append
   (equal (fn-rfz-handles-inp (append a b) fn-arena)
          (and (fn-rfz-handles-inp a fn-arena) (fn-rfz-handles-inp b fn-arena)))))

(local (defthm fn-rfz-contexts-okp-of-append
   (equal (fn-rfz-contexts-okp (append a b) keyring generation fn-arena)
          (and (fn-rfz-contexts-okp a keyring generation fn-arena)
               (fn-rfz-contexts-okp b keyring generation fn-arena)))
   :hints (("Goal" :induct (append a b)
            :in-theory (e/d (fn-rfz-contexts-okp)
                            (fn-held-context-of fn-rfz-contexts-okp-context))))))

; One row loaded: the catalog's rows keep the invariant and gain a row
; that has it.  The catalog's logical value is its row list
; (fn-cat-commit-is-append under fn-cat-p).
(local (defthm fn-rfz-seal-list-is-seal-many-one
   (equal (fn-arena-seal-list xs fn-arena) (fn-arn-seal-many (list xs) fn-arena))
   :hints (("Goal" :in-theory (enable fn-arn-seal-many)))))

; The invariant of one row, opened (the definition is closed above).
(local (defthm fn-rfz-contexts-okp-singleton
   (equal (fn-rfz-contexts-okp (list h) keyring generation fn-arena)
          (equal (fn-held-context h)
                 (fn-held-context-of (fn-arena-payload (fn-record-payload h) fn-arena)
                                     keyring generation)))
   :hints (("Goal" :expand ((fn-rfz-contexts-okp (list h) keyring generation fn-arena)
                            (fn-rfz-contexts-okp nil keyring generation fn-arena))
            :in-theory (disable fn-rfz-contexts-okp-context fn-held-context-of)))))

; The recognizers are kept by the two stobjs' own exports (their
; {preserved} obligations).
(local (defthm fn-rfz-cat-p-of-commit
   (implies (and (fn-cat-p fn-cat) (fn-held-p h))
            (fn-cat-p (fn-cat-commit h fn-cat)))
   :hints (("Goal" :use ((:instance fn-cat-commit{preserved}))
            :in-theory (e/d (fn-cat-p fn-cat-commit)
                            (fn-cat-p-is-rowsp fn-cat-commit-is-append))))))

(local (defthm fn-rfz-load-row-keeps-contexts
   (implies (and (fn-cat-p fn-cat)
                 (fn-rfz-handles-inp fn-cat fn-arena)
                 (fn-rfz-contexts-okp fn-cat keyring generation fn-arena)
                 (fn-record-p w) (natp generation))
            (mv-let (fn-arena2 fn-cat2)
              (fn-cat-load-row w keyring generation fn-arena fn-cat)
              (and (fn-cat-p fn-cat2)
                   (fn-rfz-handles-inp fn-cat2 fn-arena2)
                   (fn-rfz-contexts-okp fn-cat2 keyring generation fn-arena2))))
   :hints (("Goal" :in-theory (e/d (fn-cat-load-row)
                                   (fn-cat-intern-list fn-held-context-of
                                    fn-rfz-handles-inp-survives-seals
                                    fn-rfz-contexts-okp-survives-seals
                                    fn-rfz-intern-context fn-rfz-cat-p-of-commit
                                    fn-cat-p-is-rowsp))
            :use ((:instance fn-rfz-intern-context)
                  (:instance fn-held-p-of-intern-list)
                  (:instance fn-intern-list-arena)
                  (:instance fn-rfz-cat-p-of-commit
                             (h (mv-nth 0 (fn-cat-intern-list w keyring generation fn-arena))))
                  (:instance fn-rfz-handles-inp-survives-seals
                             (rows fn-cat) (payloads (list (fn-record-payload w))))
                  (:instance fn-rfz-contexts-okp-survives-seals
                             (rows fn-cat) (payloads (list (fn-record-payload w)))))
            :do-not-induct t))))

(local (defun fn-rfz-load-ind (records keyring generation fn-arena fn-cat)
   (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
   (if (consp records)
       (if (fn-record-p (car records))
           (mv-let (fn-arena fn-cat)
             (fn-cat-load-row (car records) keyring generation fn-arena fn-cat)
             (fn-rfz-load-ind (cdr records) keyring generation fn-arena fn-cat))
         (fn-rfz-load-ind (cdr records) keyring generation fn-arena fn-cat))
     (mv fn-arena fn-cat))))

; KEYSTONE.  The load (the host's open, from the journal or a checkpoint:
; fn-cat-load, books/catalog-relation.lisp) establishes the context
; invariant for every row it commits, under the keyring and generation it
; interns with.  So the retained catalog's folds are the store's, by the
; two theorems above.
(defthm fn-rfz-load-establishes-contexts
  (implies (and (fn-cat-p fn-cat)
                (fn-rfz-handles-inp fn-cat fn-arena)
                (fn-rfz-contexts-okp fn-cat keyring generation fn-arena)
                (natp generation))
           (mv-let (fn-arena2 fn-cat2)
             (fn-cat-load records keyring generation fn-arena fn-cat)
             (and (fn-cat-p fn-cat2)
                  (fn-rfz-handles-inp fn-cat2 fn-arena2)
                  (fn-rfz-contexts-okp fn-cat2 keyring generation fn-arena2))))
  :hints (("Goal" :induct (fn-rfz-load-ind records keyring generation fn-arena fn-cat)
           :expand ((fn-cat-load records keyring generation fn-arena fn-cat))
           :in-theory (e/d (fn-cat-load)
                           (fn-cat-load-row fn-rfz-handles-inp fn-rfz-contexts-okp
                            fn-held-context-of fn-cat-p-is-rowsp)))
          ("Subgoal *1/1" :use ((:instance fn-rfz-load-row-keeps-contexts (w (car records)))))))

(defthm fn-rfz-load-from-empty-establishes-contexts
  (implies (natp generation)
           (mv-let (fn-arena2 fn-cat2)
             (fn-cat-load records keyring generation (create-fn-arena) (create-fn-cat))
             (and (fn-rfz-handles-inp fn-cat2 fn-arena2)
                  (fn-rfz-contexts-okp fn-cat2 keyring generation fn-arena2))))
  :hints (("Goal" :use ((:instance fn-rfz-load-establishes-contexts
                                   (fn-arena (create-fn-arena)) (fn-cat (create-fn-cat))))
           :expand ((fn-rfz-contexts-okp nil keyring generation nil))
           :in-theory (e/d (create-fn-cat create-fn-arena fn-cat-p fn-arena-p)
                           (fn-cat-load fn-rfz-load-establishes-contexts)))))

(local (in-theory (disable fn-rfz-seal-list-is-seal-many-one)))

; -----------------------------------------------------------------------------
; 3. Payload identity across reclamation.

; Immutable references in the view: a pinned row list materializes the same
; after the reclaim's seal (the tombstone) and any later seals.
(defthm fn-rfz-pinned-rows-survive-seals
  (implies (fn-rfz-handles-inp rows fn-arena)
           (equal (fn-rfz-wire-rows rows (fn-arn-seal-many payloads fn-arena))
                  (fn-rfz-wire-rows rows fn-arena)))
  :hints (("Goal" :induct (fn-rfz-wire-rows rows fn-arena)
           :in-theory (e/d (fn-held-wire-of) (fn-arn-seal-many)))))

; The reclaim's row update: the row pointed at a new handle (the tombstone's).
(defun fn-rfz-row-with-handle (h handle)
  (declare (xargs :guard t))
  (fn-held-make (fn-record-sequence h) (fn-record-txid h) (fn-record-generation h)
                (fn-record-msgid h) handle (fn-record-groups h)
                (fn-record-obligation-id h) (fn-record-content-subject h)
                (fn-record-release-evidence h) (fn-record-charge h)
                (fn-record-stamp h) (fn-held-facts h) (fn-held-context h)
                (fn-held-numbers h) (fn-held-withdrawn h)))

; The old row (its original handle) reads the original bytes after the
; tombstone's seal; the new row reads the tombstone.  No hypothesis on the
; second: the tombstone's handle is the count before its seal.
(defthm fn-rfz-reclaim-old-view-reads-the-original
  (implies (and (natp (fn-record-payload r))
                (< (fn-record-payload r) (fn-arena-count fn-arena)))
           (equal (fn-held-wire-of r (fn-arena-seal-list tomb fn-arena))
                  (fn-held-wire-of r fn-arena)))
  :hints (("Goal" :in-theory (enable fn-held-wire-of))))

(defthm fn-rfz-reclaim-new-row-reads-the-tombstone
  (equal (fn-held-wire-of (fn-rfz-row-with-handle r (fn-arena-count fn-arena))
                          (fn-arena-seal-list tomb fn-arena))
         (fn-held-wire r tomb))
  :hints (("Goal" :in-theory (enable fn-held-wire-of fn-held-wire fn-rfz-row-with-handle
                                     fn-record-internals fn-held-internals))))

; The versioned mapping: a row's redirects ((version . handle) ...), newest
; first, each recorded at the catalog count when the reclaim committed.  A
; reader at version V resolves to the newest redirect whose version is
; below V, else to the original handle.
(defun fn-rfz-redirectsp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (consp (car x)) (natp (car (car x))) (natp (cdr (car x)))
         (fn-rfz-redirectsp (cdr x)))))

(defun fn-rfz-resolve (h redirects v)
  (declare (xargs :guard (and (natp h) (fn-rfz-redirectsp redirects) (natp v))))
  (if (atom redirects)
      h
    (if (< (car (car redirects)) v)
        (cdr (car redirects))
      (fn-rfz-resolve h (cdr redirects) v))))

; A view pinned at or before the reclaim's version W reads the original.
(defthm fn-rfz-resolve-before-reclaim
  (implies (<= v w)
           (equal (fn-rfz-resolve h (list (cons w tomb)) v) h)))

; A view taken after it reads the tombstone.
(defthm fn-rfz-resolve-after-reclaim
  (implies (< w v)
           (equal (fn-rfz-resolve h (list (cons w tomb)) v) tomb)))

; Both resolve to sealed bytes in the arena after the reclaim, whatever is
; sealed later: the original handle (below the count before the reclaim's
; seal) and the tombstone's (the count at the seal) are kept by every later
; seal: fn-arena-seals-keep-sealed (books/payload-arena.lisp), cited, not
; restated.

(in-theory (disable fn-rfz-wire-rows fn-rfz-articles-of-rows fn-rfz-contexts-okp
                    fn-rfz-index-of-rows fn-rfz-verdicts-of-rows fn-rfz-verdicts-of-wire
                    fn-rfz-row-with-handle fn-rfz-resolve))
