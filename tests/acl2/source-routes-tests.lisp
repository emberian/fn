; Witnesses and teeth for books/source-routes.lisp: one authored source keeps
; one identity through the served POST, the operator post and the
; hybrid-author routes (all fn-inj-decide), before and after reclamation.
;
; The subject is fn-store-existing-action (books/store-intern.lisp), which
; the host calls at host/owner-host.lisp fn-owner-existing-action and
; fn-owner-prepare, and through fn-pidx-existing-action
; (fn-pidx-existing-action-is-store-existing-action) at
; fn-owner-existing-action-buffer; it reads the held bytes through the arena
; (srt-action below runs it over the arena of SPEC).  The articles are the corpus
; shapes (tests/fixtures/source-corpus): a supplied Date, a generated Date,
; a client-supplied Path (D32, recipe v3), unknown headers and an 8-bit MIME
; body, injected by the real fn-inj-decide at two clock readings 37 s apart
; and held by the real Store; the tombstone is fn-rcl-tombstone-of's, placed
; by fn-rcl-reclaim-state.
(in-package "ACL2")
(include-book "held-rows-tests")
(include-book "../../books/source-routes")
(include-book "../../books/codec-attach")
(include-book "must-fail-checked")

(defun srt-text (s) (fn-record-string-octets s))
(defconst *srt-agent* (srt-text "hbox.ember.software"))
(defconst *srt-config*
  (fn-inj-make-config t *srt-agent* (list (srt-text "fn.test")) 32768))
(defconst *srt-a* (fn-clock-observation 5000000 843004800000 0 t))
(defconst *srt-b* (fn-clock-observation 5037000 843004837000 0 t))
(defconst *srt-no-wall* (fn-clock-observation 5037000 nil 0 t))

(defconst *srt-msgid* "<sc@example.invalid>")
(defconst *srt-mo* (srt-text *srt-msgid*))
(defconst *srt-crlf* '(13 10))
(defun srt-source (path date msgid extra body)
  (append (if path (append (srt-text "Path: ") (srt-text path) *srt-crlf*) nil)
          (srt-text "From: poster@example.invalid") *srt-crlf*
          (srt-text "Newsgroups: fn.test") *srt-crlf*
          (srt-text "Subject: corpus") *srt-crlf*
          (if date (append (srt-text "Date: Fri, 25 Sep 2026 12:00:00 +0000") *srt-crlf*) nil)
          (if msgid (append (srt-text "Message-ID: ") (srt-text msgid) *srt-crlf*) nil)
          extra
          *srt-crlf* body))

(defconst *srt-body* (append (srt-text "caf") '(195 169) *srt-crlf*))   ; 8-bit UTF-8
(defconst *srt-unknown*
  (append (srt-text "X-Corpus-Unknown: kept") *srt-crlf*
          (srt-text "MIME-Version: 1.0") *srt-crlf*
          (srt-text "Content-Type: text/plain; charset=utf-8") *srt-crlf*))
(defconst *srt-dated* (srt-source nil t *srt-msgid* *srt-unknown* *srt-body*))
(defconst *srt-dateless* (srt-source nil nil *srt-msgid* nil *srt-body*))
(defconst *srt-pathed* (srt-source "poster.example.invalid!not-for-mail" t *srt-msgid*
                                   nil *srt-body*))
; One authored byte changed (the body's last letter).
(defconst *srt-changed*
  (srt-source nil t *srt-msgid* *srt-unknown* (append (srt-text "caf") '(195 168) *srt-crlf*)))
; A changed supplied Path tail is a changed source (D32).
(defconst *srt-repathed* (srt-source "other.example.invalid!not-for-mail" t *srt-msgid*
                                     nil *srt-body*))
(defconst *srt-idless* (srt-source nil t nil nil *srt-body*))

(defun srt-d (source obs) (fn-inj-decide source *srt-config* obs))
(defun srt-o (source obs) (fn-inj-decision-octets (srt-d source obs)))

(assert-event (and (fn-inj-injectedp (srt-d *srt-dated* *srt-a*))
                   (fn-inj-injectedp (srt-d *srt-dated* *srt-b*))
                   (fn-inj-injectedp (srt-d *srt-dateless* *srt-a*))
                   (fn-inj-injectedp (srt-d *srt-dateless* *srt-b*))
                   (fn-inj-injectedp (srt-d *srt-pathed* *srt-a*))
                   (fn-inj-injectedp (srt-d *srt-pathed* *srt-b*))
                   (fn-inj-injectedp (srt-d *srt-changed* *srt-b*))
                   (fn-inj-injectedp (srt-d *srt-repathed* *srt-b*))
                   (fn-inj-injectedp (srt-d *srt-idless* *srt-a*))
                   (fn-inj-injectedp (srt-d *srt-idless* *srt-b*))
                   (not (fn-inj-injectedp (srt-d *srt-dateless* *srt-no-wall*)))))
; The node-added fields move with the clock: the generated Date and
; Injection-Date differ between A and B, so the stored octets differ.
(assert-event (not (equal (srt-o *srt-dateless* *srt-a*) (srt-o *srt-dateless* *srt-b*))))
; The supplied Path gets the agent spliced in (recipe v3).
(assert-event (fn-inj-infixp (append (srt-text "Path: hbox.ember.software!poster.example.invalid")
                                     nil)
                             (srt-o *srt-pathed* *srt-a*)))

; -----------------------------------------------------------------------------
; A Store holding one payload under *srt-msgid*, through the real Store.

(defconst *srt-groups* '("fn.test"))
; The store retains held rows (records-flip, books/held-record.lisp): the
; record the entry interns on a fresh arena (handle 0).  An ARENA SPEC is
; (PRIOR . SEALED): the wire records the arena interned, then the byte lists
; sealed after them (a reclaimed article's tombstone, sealed by the reclaim
; entry: books/store-reclaim.lisp fn-rcl-reclaim-state takes its handle).
(defun srt-record-wire (msgid payload)
  (fn-record-make 0 0 0 msgid payload *srt-groups*
                  "srt-pin" "srt-subject" "srt-release" 2 841000000))
(defun srt-spec (payload) (list (list (srt-record-wire *srt-msgid* payload))))
(defun srt-store-row (row)
  (fn-sn-finish
   (fn-sn-io (fn-sn-io (fn-sn-io
     (fn-sn-prepare
      (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io
        (fn-sn-initial *srt-groups* 10) :start-frontier nil)
        :frontier-file :ok) :frontier-replace :ok) :frontier-directory :ok)
      row)
     :record-file :ok) :record-link :ok) :record-directory :ok)))
(defun srt-store (payload)
  (declare (xargs :verify-guards nil))
  (srt-store-row (car (fn-hrt-rows (car (srt-spec payload)) nil 0))))
(defun srt-held (s)
  (fn-find-article *srt-msgid* (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))

; The arena of SPEC, and alpha (handles to bytes) read through it.
(defun srt-seal-all (xs fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (atom xs)
      fn-arena
    (let ((fn-arena (fn-arena-seal-list (car xs) fn-arena)))
      (srt-seal-all (cdr xs) fn-arena))))
(defun srt-bytes-in (spec h fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (rows fn-arena)
    (fn-hrt-events (car spec) nil 0 fn-arena)
    (declare (ignore rows))
    (let ((fn-arena (srt-seal-all (cdr spec) fn-arena)))
      (mv (fn-hrt-handle-bytes h fn-arena) fn-arena))))
(defun srt-bytes (spec h)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (bytes fn-arena) (srt-bytes-in spec h fn-arena) bytes)))
(defun srt-alpha-in (spec articles fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (rows fn-arena)
    (fn-hrt-events (car spec) nil 0 fn-arena)
    (declare (ignore rows))
    (let ((fn-arena (srt-seal-all (cdr spec) fn-arena)))
      (mv (fn-hrt-articles-alpha articles fn-arena) fn-arena))))
(defun srt-alpha (spec articles)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (as fn-arena) (srt-alpha-in spec articles fn-arena) as)))
; by specification: the flip -- the stored payload is a handle; the verdict
; the host asks is fn-store-existing-action over the arena of SPEC (D25's
; over alpha of the acceptance articles by its keystone
; fn-store-existing-action-is-the-verdict-over-alpha).  With nothing sealed
; it is held-rows-tests' fn-hrt-existing-action (asserted below).
(defun srt-action-in (spec msgid payload groups s fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (rows fn-arena)
    (fn-hrt-events (car spec) nil 0 fn-arena)
    (declare (ignore rows))
    (let ((fn-arena (srt-seal-all (cdr spec) fn-arena)))
      (mv (fn-store-existing-action msgid payload groups s fn-arena) fn-arena))))
(defun srt-action (spec msgid payload groups s)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (r fn-arena) (srt-action-in spec msgid payload groups s fn-arena) r)))

(defun srt-index-of (x xs i)
  (declare (xargs :guard (natp i) :verify-guards nil))
  (if (consp xs) (if (equal (car xs) x) i (srt-index-of x (cdr xs) (1+ i))) nil))
; S with the held payload replaced by `tomb' (the handle of the sealed
; tombstone bytes), as `store reclaim' would.
(defun srt-reclaimed (s tomb)
  (let* ((node (fn-sn-node s))
         (acc (fn-node-acceptance node))
         (k (srt-index-of acc node 0)))
    (update-nth 3 (update-nth k (fn-rcl-reclaim-state acc *srt-msgid* tomb) node) s)))

(defconst *srt-s-dated* (srt-store (srt-o *srt-dated* *srt-a*)))
(defconst *srt-s-dateless* (srt-store (srt-o *srt-dateless* *srt-a*)))
(defconst *srt-s-pathed* (srt-store (srt-o *srt-pathed* *srt-a*)))
(assert-event (and (fn-sn-statep *srt-s-dated*) (fn-sn-statep *srt-s-dateless*)
                   (fn-sn-statep *srt-s-pathed*)))
(defconst *srt-tomb-dateless* (fn-rcl-tombstone-of (srt-o *srt-dateless* *srt-a*) *srt-mo*))
(defconst *srt-tomb-pathed* (fn-rcl-tombstone-of (srt-o *srt-pathed* *srt-a*) *srt-mo*))
; by specification: the flip -- the tombstone is sealed after the record
; (handle 1) and the held payload is that handle; the bytes under it are the
; tombstone, the old expected value.
(defconst *srt-s-dated-spec* (srt-spec (srt-o *srt-dated* *srt-a*)))
(defconst *srt-s-dateless-spec* (srt-spec (srt-o *srt-dateless* *srt-a*)))
(defconst *srt-s-pathed-spec* (srt-spec (srt-o *srt-pathed* *srt-a*)))
(defconst *srt-t-dateless-spec* (cons (car *srt-s-dateless-spec*) (list *srt-tomb-dateless*)))
(defconst *srt-t-pathed-spec* (cons (car *srt-s-pathed-spec*) (list *srt-tomb-pathed*)))
(defconst *srt-t-dateless* (srt-reclaimed *srt-s-dateless* 1))
(defconst *srt-t-pathed* (srt-reclaimed *srt-s-pathed* 1))
(assert-event (and (equal (fn-article-payload (srt-held *srt-t-dateless*)) 1)
                   (equal (fn-article-payload (srt-held *srt-t-pathed*)) 1)))
(assert-event (and (equal (srt-bytes *srt-t-dateless-spec* (fn-article-payload (srt-held *srt-t-dateless*)))
                          *srt-tomb-dateless*)
                   (equal (srt-bytes *srt-t-pathed-spec* (fn-article-payload (srt-held *srt-t-pathed*)))
                          *srt-tomb-pathed*)))
; The unreclaimed stores hold their injection under handle 0, and the
; verdict here is held-rows-tests' fn-hrt-existing-action when nothing is sealed.
(assert-event (and (equal (fn-article-payload (srt-held *srt-s-dated*)) 0)
                   (equal (srt-bytes *srt-s-dated-spec* 0) (srt-o *srt-dated* *srt-a*))
                   (equal (srt-action *srt-s-dated-spec* *srt-msgid* (srt-o *srt-dated* *srt-b*)
                                      *srt-groups* *srt-s-dated*)
                          (fn-hrt-existing-action (car *srt-s-dated-spec*) *srt-msgid*
                                                  (srt-o *srt-dated* *srt-b*)
                                                  *srt-groups* *srt-s-dated*))))

; -----------------------------------------------------------------------------
; fn-sr-an-injection-is-not-a-tombstone: every decision, injected or refused.
(assert-event (and (not (fn-rcl-tombstonep (srt-o *srt-dated* *srt-a*)))
                   (not (fn-rcl-tombstonep (srt-o *srt-pathed* *srt-b*)))
                   (not (fn-rcl-tombstonep (srt-o *srt-dateless* *srt-no-wall*)))
                   (fn-rcl-tombstonep *srt-tomb-dateless*)))
; fn-sr-an-injection-is-a-cons; without injection, a refusal has no octets.
(assert-event (and (consp (srt-o *srt-dated* *srt-a*))
                   (not (consp (srt-o *srt-dateless* *srt-no-wall*)))))

; -----------------------------------------------------------------------------
; fn-sr-a-retry-is-already-stored: the complete antecedent and the conclusion,
; for a supplied Date, a generated Date and a supplied Path.
; by specification: the flip -- the held payload hypothesis reads the bytes
; under the held handle through the arena of SPEC.
(defun srt-retry-antecedent (spec s msgid source a b groups)
  (declare (xargs :verify-guards nil))
  (let ((held (fn-find-article msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
        (da (srt-d source a)) (db (srt-d source b)))
    (and (equal (srt-bytes spec (fn-article-payload held)) (fn-inj-decision-octets da))
         (fn-inj-injectedp da) (fn-inj-injectedp db)
         (equal (fn-inj-decision-msgid da) (fn-record-string-octets msgid))
         (equal (fn-inj-decision-msgid db) (fn-record-string-octets msgid))
         (equal groups (fn-article-groups held)))))
(assert-event
 (and (srt-retry-antecedent *srt-s-dated-spec* *srt-s-dated* *srt-msgid* *srt-dated* *srt-a* *srt-b* *srt-groups*)
      (equal (srt-action *srt-s-dated-spec* *srt-msgid* (srt-o *srt-dated* *srt-b*) *srt-groups*
                                     *srt-s-dated*) :duplicate)
      (srt-retry-antecedent *srt-s-dateless-spec* *srt-s-dateless* *srt-msgid* *srt-dateless* *srt-a* *srt-b*
                            *srt-groups*)
      (equal (srt-action *srt-s-dateless-spec* *srt-msgid* (srt-o *srt-dateless* *srt-b*) *srt-groups*
                                     *srt-s-dateless*) :duplicate)
      (srt-retry-antecedent *srt-s-pathed-spec* *srt-s-pathed* *srt-msgid* *srt-pathed* *srt-a* *srt-b* *srt-groups*)
      (equal (srt-action *srt-s-pathed-spec* *srt-msgid* (srt-o *srt-pathed* *srt-b*) *srt-groups*
                                     *srt-s-pathed*) :duplicate)))
; The byte-identity decision D25 replaced answers conflict on the same retry.
; by specification: the flip -- fn-sn-existing-action's comparison, with the
; stored bytes read through the arena.
(defun srt-bytes-action (spec msgid payload groups s)
  (declare (xargs :verify-guards nil))
  (let ((article (fn-find-article
                  msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s))))))
    (if article
        (if (and (equal payload (srt-bytes spec (fn-article-payload article)))
                 (equal groups (fn-article-groups article)))
            :duplicate
          :conflict)
      nil)))
(assert-event (equal (srt-bytes-action *srt-s-dateless-spec* *srt-msgid* (srt-o *srt-dateless* *srt-b*)
                                       *srt-groups* *srt-s-dateless*)
                     :conflict))

; Hypothesis removed: the held payload is not the injection at A (it is
; another source's), every other hypothesis kept; the verdict is conflict.
(assert-event
 (let ((held (srt-held *srt-s-dated*)) (da (srt-d *srt-changed* *srt-a*))
       (db (srt-d *srt-changed* *srt-b*)))
   (and (not (equal (srt-bytes *srt-s-dated-spec* (fn-article-payload held))
                    (fn-inj-decision-octets da)))
        (fn-inj-injectedp da) (fn-inj-injectedp db)
        (equal (fn-inj-decision-msgid da) *srt-mo*) (equal (fn-inj-decision-msgid db) *srt-mo*)
        (equal *srt-groups* (fn-article-groups held))
        (equal (srt-action *srt-s-dated-spec* *srt-msgid* (fn-inj-decision-octets db) *srt-groups*
                                       *srt-s-dated*) :conflict))))
; Hypothesis removed: other groups; the verdict is conflict.
(assert-event
 (and (not (equal '("fn.other") (fn-article-groups (srt-held *srt-s-dated*))))
      (equal (srt-action *srt-s-dated-spec* *srt-msgid* (srt-o *srt-dated* *srt-b*) '("fn.other")
                                     *srt-s-dated*) :conflict)))
; Hypothesis removed: the Message-ID at A is not the held one.  A source
; with no Message-ID gets a generated one per clock; the Store holds the A
; injection under B's Message-ID.  Every other hypothesis kept; conflict.
(defconst *srt-idless-mo-b* (fn-inj-decision-msgid (srt-d *srt-idless* *srt-b*)))
(defun srt-chars (xs)
  (declare (xargs :verify-guards nil))
  (if (consp xs) (cons (code-char (nfix (car xs))) (srt-chars (cdr xs))) nil))
(defconst *srt-idless-msgid-b* (coerce (srt-chars *srt-idless-mo-b*) 'string))
(defconst *srt-s-idless-spec*
  (list (list (srt-record-wire *srt-idless-msgid-b* (srt-o *srt-idless* *srt-a*)))))
(defconst *srt-s-idless*
  (srt-store-row (car (fn-hrt-rows (car *srt-s-idless-spec*) nil 0))))
(assert-event
 (let ((held (fn-find-article *srt-idless-msgid-b*
                              (fn-state-articles (fn-node-acceptance (fn-sn-node *srt-s-idless*)))))
       (da (srt-d *srt-idless* *srt-a*)) (db (srt-d *srt-idless* *srt-b*)))
   (and (equal (fn-record-string-octets *srt-idless-msgid-b*) *srt-idless-mo-b*)
        (equal (srt-bytes *srt-s-idless-spec* (fn-article-payload held))
               (fn-inj-decision-octets da))
        (fn-inj-injectedp da) (fn-inj-injectedp db)
        (not (equal (fn-inj-decision-msgid da) *srt-idless-mo-b*))
        (equal (fn-inj-decision-msgid db) *srt-idless-mo-b*)
        (equal *srt-groups* (fn-article-groups held))
        (equal (srt-action *srt-s-idless-spec* *srt-idless-msgid-b* (fn-inj-decision-octets db)
                                       *srt-groups* *srt-s-idless*) :conflict))))

(must-fail-checked
 (defthm srt-retry-without-the-held-payload
   (let ((held (fn-find-article msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
         (da (fn-inj-decide source config a)) (db (fn-inj-decide source config b)))
     (implies (and (fn-inj-injectedp da) (fn-inj-injectedp db)
                   (equal (fn-inj-decision-msgid da) (fn-record-string-octets msgid))
                   (equal (fn-inj-decision-msgid db) (fn-record-string-octets msgid))
                   (equal groups (fn-article-groups held)))
              (equal (fn-store-existing-action msgid (fn-inj-decision-octets db) groups s fn-arena)
                     :duplicate)))
   :hints (("Goal" :in-theory (disable fn-inj-decide fn-store-existing-action))))
 )
(must-fail-checked
 (defthm srt-retry-without-the-groups
   (let ((held (fn-find-article msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
         (da (fn-inj-decide source config a)) (db (fn-inj-decide source config b)))
     (implies (and (equal (fn-handle-bytes (fn-article-payload held) fn-arena) (fn-inj-decision-octets da))
                   (fn-inj-injectedp da) (fn-inj-injectedp db)
                   (equal (fn-inj-decision-msgid da) (fn-record-string-octets msgid))
                   (equal (fn-inj-decision-msgid db) (fn-record-string-octets msgid)))
              (equal (fn-store-existing-action msgid (fn-inj-decision-octets db) groups s fn-arena)
                     :duplicate)))
   :hints (("Goal" :in-theory (disable fn-inj-decide fn-store-existing-action)))))
(must-fail-checked
 (defthm srt-retry-without-the-first-message-id
   (let ((held (fn-find-article msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
         (da (fn-inj-decide source config a)) (db (fn-inj-decide source config b)))
     (implies (and (equal (fn-handle-bytes (fn-article-payload held) fn-arena) (fn-inj-decision-octets da))
                   (fn-inj-injectedp da) (fn-inj-injectedp db)
                   (equal (fn-inj-decision-msgid db) (fn-record-string-octets msgid))
                   (equal groups (fn-article-groups held)))
              (equal (fn-store-existing-action msgid (fn-inj-decision-octets db) groups s fn-arena)
                     :duplicate)))
   :hints (("Goal" :in-theory (disable fn-inj-decide fn-store-existing-action)))))

; -----------------------------------------------------------------------------
; fn-sr-a-changed-source-is-a-conflict: one changed body byte, a changed
; supplied Path tail (D32), an authored Date removed.
(assert-event
 (and (not (equal *srt-changed* *srt-dated*))
      (equal (srt-action *srt-s-dated-spec* *srt-msgid* (srt-o *srt-changed* *srt-b*) *srt-groups*
                                     *srt-s-dated*) :conflict)
      (not (equal *srt-repathed* *srt-pathed*))
      (equal (srt-action *srt-s-pathed-spec* *srt-msgid* (srt-o *srt-repathed* *srt-b*) *srt-groups*
                                     *srt-s-pathed*) :conflict)
      (equal (srt-action *srt-s-dated-spec* *srt-msgid* (srt-o *srt-dateless* *srt-b*) *srt-groups*
                                     *srt-s-dated*) :conflict)))
; Hypothesis removed: the sources are equal; the verdict is duplicate (the
; retry witness above, every other hypothesis kept).
(must-fail-checked
 (defthm srt-conflict-without-distinct-sources
   (let ((da (fn-inj-decide source1 config a)) (db (fn-inj-decide source2 config b))
         (held (fn-find-article msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s))))))
     (implies (and (equal (fn-handle-bytes (fn-article-payload held) fn-arena) (fn-inj-decision-octets da))
                   (fn-inj-injectedp da) (fn-inj-injectedp db)
                   (equal (fn-inj-decision-msgid da) (fn-record-string-octets msgid))
                   (equal (fn-inj-decision-msgid db) (fn-record-string-octets msgid)))
              (equal (fn-store-existing-action msgid (fn-inj-decision-octets db) groups s fn-arena)
                     :conflict)))
   :hints (("Goal" :in-theory (disable fn-inj-decide fn-store-existing-action)))))

; -----------------------------------------------------------------------------
; fn-sr-the-tombstone-keeps-the-source (unreachable-in-composition until a
; program writes tombstones: `store reclaim' is not implemented).
(assert-event
 (let ((tomb *srt-tomb-pathed*))
   (and (fn-inj-injectedp (srt-d *srt-pathed* *srt-a*))
        (fn-rcl-tombstonep tomb) (fn-rcl-tomb-sourcep tomb)
        (equal (fn-rcl-tomb-source-digest tomb) (fn-sha256 *srt-pathed*))
        (equal (fn-rcl-tomb-agent tomb) *srt-agent*)
        (equal (fn-rcl-tomb-octets-digest tomb) (fn-sha256 (srt-o *srt-pathed* *srt-a*))))))
; Hypothesis removed: a refused decision's tombstone names no source.
(assert-event
 (let* ((d (srt-d *srt-dateless* *srt-no-wall*))
        (tomb (fn-rcl-tombstone-of (fn-inj-decision-octets d) (fn-inj-decision-msgid d))))
   (and (not (fn-inj-injectedp d)) (not (fn-rcl-tomb-sourcep tomb)))))

; fn-sr-a-retry-after-reclaim-is-already-stored and
; fn-sr-a-changed-source-after-reclaim-is-a-conflict.
(assert-event
 (and (equal (srt-action *srt-t-dateless-spec* *srt-msgid* (srt-o *srt-dateless* *srt-b*) *srt-groups*
                                     *srt-t-dateless*) :duplicate)
      (equal (srt-action *srt-t-pathed-spec* *srt-msgid* (srt-o *srt-pathed* *srt-b*) *srt-groups*
                                     *srt-t-pathed*) :duplicate)
      (equal (srt-action *srt-t-pathed-spec* *srt-msgid* (srt-o *srt-repathed* *srt-b*) *srt-groups*
                                     *srt-t-pathed*) :conflict)
      (not (fn-rcl-collisionp *srt-repathed* *srt-pathed*))
      (equal (srt-action *srt-t-pathed-spec* *srt-msgid* (srt-o *srt-pathed* *srt-b*) '("fn.other")
                                     *srt-t-pathed*) :conflict)))
; Hypothesis removed: the tombstone is another source's; conflict.
(assert-event
 (equal (srt-action (cons (car *srt-s-dated-spec*)
                         (list (fn-rcl-tombstone-of (srt-o *srt-dated* *srt-a*) *srt-mo*)))
                   *srt-msgid* (srt-o *srt-changed* *srt-b*) *srt-groups*
                   (srt-reclaimed *srt-s-dated* 1))
        :conflict))
(must-fail-checked
 (defthm srt-conflict-after-reclaim-without-distinct-sources
   (let ((da (fn-inj-decide source1 config a)) (db (fn-inj-decide source2 config b))
         (held (fn-find-article msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s))))))
     (implies (and (equal (fn-handle-bytes (fn-article-payload held) fn-arena)
                          (fn-rcl-tombstone-of (fn-inj-decision-octets da)
                                               (fn-record-string-octets msgid)))
                   (fn-inj-injectedp da) (fn-inj-injectedp db)
                   (equal (fn-inj-decision-msgid da) (fn-record-string-octets msgid))
                   (equal (fn-inj-decision-msgid db) (fn-record-string-octets msgid)))
              (or (equal (fn-store-existing-action msgid (fn-inj-decision-octets db) groups s fn-arena)
                         :conflict)
                  (fn-rcl-collisionp source2 source1))))
   :hints (("Goal" :in-theory (disable fn-inj-decide fn-store-existing-action)))))

; -----------------------------------------------------------------------------
; fn-sr-a-signed-retry-is-already-stored (PKT-166): the hybrid-author route's
; stored octets, fn-hsig-injected-carrier-octets, at A and at B 37 s later,
; over a real rendered dual-signature carrier (the signatures are opaque
; octets here: rendering does not verify, the route verifies before it).
(defconst *srt-principal* (make-list 32 :initial-element 7))
(defconst *srt-keys* (list (cons :ed25519 (make-list 32 :initial-element 11))
                           (cons :ml-dsa-65 (make-list 1952 :initial-element 13))))
(defconst *srt-sigs* (list (cons :ed25519 (make-list 64 :initial-element 17))
                           (cons :ml-dsa-65 (make-list 3309 :initial-element 19))))
(defconst *srt-signed-source* (srt-source nil t *srt-msgid* nil *srt-body*))
(defun srt-carrier-plan (source obs)
  (fn-hsig-injected-carrier-plan source *srt-principal* *srt-keys* *srt-sigs*
                                 *srt-config* obs))
(defun srt-carrier (source obs)
  (fn-hsig-injected-carrier-octets source *srt-principal* *srt-keys* *srt-sigs*
                                   *srt-config* obs))
; Rendering calls the statement codec's attachment, which a defconst's
; evaluation may not; make-event evaluates each value once (as
; tests/acl2/hybrid-store-tests does) and the checks read the constants.
(make-event `(defconst *srt-carrier-a* ',(srt-carrier *srt-signed-source* *srt-a*)))
(make-event `(defconst *srt-carrier-b* ',(srt-carrier *srt-signed-source* *srt-b*)))
(make-event `(defconst *srt-carrier-changed-a* ',(srt-carrier *srt-changed* *srt-a*)))
(make-event `(defconst *srt-carrier-msgids*
               ',(list (fn-inj-decision-msgid (srt-carrier-plan *srt-signed-source* *srt-a*))
                       (fn-inj-decision-msgid (srt-carrier-plan *srt-signed-source* *srt-b*)))))
(make-event `(defconst *srt-carrier-disabled*
               ',(fn-hsig-injected-carrier-octets
                  *srt-signed-source* *srt-principal* *srt-keys* *srt-sigs*
                  (fn-inj-make-config nil *srt-agent* (list (srt-text "fn.test")) 32768)
                  *srt-b*)))
(defconst *srt-s-signed-spec* (srt-spec *srt-carrier-a*))
(defconst *srt-s-signed* (srt-store *srt-carrier-a*))
(assert-event
 (let ((held (srt-held *srt-s-signed*)))
   (and *srt-carrier-a* *srt-carrier-b*
        (equal (srt-bytes *srt-s-signed-spec* (fn-article-payload held)) *srt-carrier-a*)
        (equal *srt-carrier-msgids* (list *srt-mo* *srt-mo*))
        (equal *srt-groups* (fn-article-groups held))
        (equal (srt-action *srt-s-signed-spec* *srt-msgid* *srt-carrier-b* *srt-groups* *srt-s-signed*)
               :duplicate))))
; Hypothesis removed: the carrier of another source is held; conflict.
(assert-event
 (and (not (equal *srt-carrier-changed-a* *srt-carrier-a*))
      (equal (srt-action (srt-spec *srt-carrier-changed-a*) *srt-msgid* *srt-carrier-b* *srt-groups*
                         (srt-store *srt-carrier-changed-a*))
             :conflict)))
; Hypothesis removed: other groups; conflict.
(assert-event
 (equal (srt-action *srt-s-signed-spec* *srt-msgid* *srt-carrier-b* '("fn.other") *srt-s-signed*)
        :conflict))
; Hypothesis removed: no octets at B (injection disabled).
(assert-event (null *srt-carrier-disabled*))
(must-fail-checked
 (defthm srt-signed-retry-without-the-held-payload
   (let ((pa (fn-hsig-injected-carrier-plan source principal keys signatures config a))
         (pb (fn-hsig-injected-carrier-plan source principal keys signatures config b))
         (oa (fn-hsig-injected-carrier-octets source principal keys signatures config a))
         (ob (fn-hsig-injected-carrier-octets source principal keys signatures config b))
         (held (fn-find-article msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s))))))
     (implies (and oa ob
                   (equal (fn-inj-decision-msgid pa) (fn-record-string-octets msgid))
                   (equal (fn-inj-decision-msgid pb) (fn-record-string-octets msgid))
                   (equal groups (fn-article-groups held)))
              (equal (fn-store-existing-action msgid ob groups s fn-arena) :duplicate)))
   :hints (("Goal" :in-theory (disable fn-hsig-injected-carrier-octets
                                       fn-hsig-injected-carrier-plan fn-store-existing-action)))))
(must-fail-checked
 (defthm srt-signed-retry-without-the-groups
   (let ((pa (fn-hsig-injected-carrier-plan source principal keys signatures config a))
         (pb (fn-hsig-injected-carrier-plan source principal keys signatures config b))
         (oa (fn-hsig-injected-carrier-octets source principal keys signatures config a))
         (ob (fn-hsig-injected-carrier-octets source principal keys signatures config b))
         (held (fn-find-article msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s))))))
     (implies (and oa ob (equal (fn-handle-bytes (fn-article-payload held) fn-arena) oa)
                   (equal (fn-inj-decision-msgid pa) (fn-record-string-octets msgid))
                   (equal (fn-inj-decision-msgid pb) (fn-record-string-octets msgid)))
              (equal (fn-store-existing-action msgid ob groups s fn-arena) :duplicate)))
   :hints (("Goal" :in-theory (disable fn-hsig-injected-carrier-octets
                                       fn-hsig-injected-carrier-plan fn-store-existing-action)))))
