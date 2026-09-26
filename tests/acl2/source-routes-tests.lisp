; Witnesses and teeth for books/source-routes.lisp: one authored source keeps
; one identity through the served POST, the operator post and the
; hybrid-author routes (all fn-inj-decide), before and after reclamation.
;
; The subject is fn-rcl-existing-action, which the host calls at
; host/owner-host.lisp fn-owner-existing-action and fn-owner-prepare, and
; through fn-rclb-existing-action (fn-rclb-existing-action-is-rcl-existing-
; action) at fn-owner-existing-action-buffer.  The articles are the corpus
; shapes (tests/fixtures/source-corpus): a supplied Date, a generated Date,
; a client-supplied Path (D32, recipe v3), unknown headers and an 8-bit MIME
; body, injected by the real fn-inj-decide at two clock readings 37 s apart
; and held by the real Store; the tombstone is fn-rcl-tombstone-of's, placed
; by fn-rcl-reclaim-state.
(in-package "ACL2")
(include-book "../../books/source-routes")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

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
(defun srt-store (payload)
  (fn-sn-finish
   (fn-sn-io (fn-sn-io (fn-sn-io
     (fn-sn-prepare
      (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io
        (fn-sn-initial *srt-groups* 10) :start-frontier nil)
        :frontier-file :ok) :frontier-replace :ok) :frontier-directory :ok)
      (fn-record-make 0 0 0 *srt-msgid* payload *srt-groups*
                      "srt-pin" "srt-subject" "srt-release" 2 841000000))
     :record-file :ok) :record-link :ok) :record-directory :ok)))
(defun srt-held (s)
  (fn-find-article *srt-msgid* (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))

(defun srt-index-of (x xs i)
  (declare (xargs :guard (natp i) :verify-guards nil))
  (if (consp xs) (if (equal (car xs) x) i (srt-index-of x (cdr xs) (1+ i))) nil))
; S with the held payload replaced by `tomb', as `store reclaim' would.
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
(defconst *srt-t-dateless* (srt-reclaimed *srt-s-dateless* *srt-tomb-dateless*))
(defconst *srt-t-pathed* (srt-reclaimed *srt-s-pathed* *srt-tomb-pathed*))
(assert-event (and (equal (fn-article-payload (srt-held *srt-t-dateless*)) *srt-tomb-dateless*)
                   (equal (fn-article-payload (srt-held *srt-t-pathed*)) *srt-tomb-pathed*)))

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
(defun srt-retry-antecedent (s msgid source a b groups)
  (let ((held (fn-find-article msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
        (da (srt-d source a)) (db (srt-d source b)))
    (and (equal (fn-article-payload held) (fn-inj-decision-octets da))
         (fn-inj-injectedp da) (fn-inj-injectedp db)
         (equal (fn-inj-decision-msgid da) (fn-record-string-octets msgid))
         (equal (fn-inj-decision-msgid db) (fn-record-string-octets msgid))
         (equal groups (fn-article-groups held)))))
(assert-event
 (and (srt-retry-antecedent *srt-s-dated* *srt-msgid* *srt-dated* *srt-a* *srt-b* *srt-groups*)
      (equal (fn-rcl-existing-action *srt-msgid* (srt-o *srt-dated* *srt-b*) *srt-groups*
                                     *srt-s-dated*) :duplicate)
      (srt-retry-antecedent *srt-s-dateless* *srt-msgid* *srt-dateless* *srt-a* *srt-b*
                            *srt-groups*)
      (equal (fn-rcl-existing-action *srt-msgid* (srt-o *srt-dateless* *srt-b*) *srt-groups*
                                     *srt-s-dateless*) :duplicate)
      (srt-retry-antecedent *srt-s-pathed* *srt-msgid* *srt-pathed* *srt-a* *srt-b* *srt-groups*)
      (equal (fn-rcl-existing-action *srt-msgid* (srt-o *srt-pathed* *srt-b*) *srt-groups*
                                     *srt-s-pathed*) :duplicate)))
; The byte-identity decision D25 replaced answers conflict on the same retry.
(assert-event (equal (fn-sn-existing-action *srt-msgid* (srt-o *srt-dateless* *srt-b*)
                                            *srt-groups* *srt-s-dateless*)
                     :conflict))

; Hypothesis removed: the held payload is not the injection at A (it is
; another source's), every other hypothesis kept; the verdict is conflict.
(assert-event
 (let ((held (srt-held *srt-s-dated*)) (da (srt-d *srt-changed* *srt-a*))
       (db (srt-d *srt-changed* *srt-b*)))
   (and (not (equal (fn-article-payload held) (fn-inj-decision-octets da)))
        (fn-inj-injectedp da) (fn-inj-injectedp db)
        (equal (fn-inj-decision-msgid da) *srt-mo*) (equal (fn-inj-decision-msgid db) *srt-mo*)
        (equal *srt-groups* (fn-article-groups held))
        (equal (fn-rcl-existing-action *srt-msgid* (fn-inj-decision-octets db) *srt-groups*
                                       *srt-s-dated*) :conflict))))
; Hypothesis removed: other groups; the verdict is conflict.
(assert-event
 (and (not (equal '("fn.other") (fn-article-groups (srt-held *srt-s-dated*))))
      (equal (fn-rcl-existing-action *srt-msgid* (srt-o *srt-dated* *srt-b*) '("fn.other")
                                     *srt-s-dated*) :conflict)))
; Hypothesis removed: the Message-ID at A is not the held one.  A source
; with no Message-ID gets a generated one per clock; the Store holds the A
; injection under B's Message-ID.  Every other hypothesis kept; conflict.
(defconst *srt-idless-mo-b* (fn-inj-decision-msgid (srt-d *srt-idless* *srt-b*)))
(defun srt-chars (xs)
  (declare (xargs :verify-guards nil))
  (if (consp xs) (cons (code-char (nfix (car xs))) (srt-chars (cdr xs))) nil))
(defconst *srt-idless-msgid-b* (coerce (srt-chars *srt-idless-mo-b*) 'string))
(defconst *srt-s-idless*
  (fn-sn-finish
   (fn-sn-io (fn-sn-io (fn-sn-io
     (fn-sn-prepare
      (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io
        (fn-sn-initial *srt-groups* 10) :start-frontier nil)
        :frontier-file :ok) :frontier-replace :ok) :frontier-directory :ok)
      (fn-record-make 0 0 0 *srt-idless-msgid-b* (srt-o *srt-idless* *srt-a*) *srt-groups*
                      "srt-pin" "srt-subject" "srt-release" 2 841000000))
     :record-file :ok) :record-link :ok) :record-directory :ok)))
(assert-event
 (let ((held (fn-find-article *srt-idless-msgid-b*
                              (fn-state-articles (fn-node-acceptance (fn-sn-node *srt-s-idless*)))))
       (da (srt-d *srt-idless* *srt-a*)) (db (srt-d *srt-idless* *srt-b*)))
   (and (equal (fn-record-string-octets *srt-idless-msgid-b*) *srt-idless-mo-b*)
        (equal (fn-article-payload held) (fn-inj-decision-octets da))
        (fn-inj-injectedp da) (fn-inj-injectedp db)
        (not (equal (fn-inj-decision-msgid da) *srt-idless-mo-b*))
        (equal (fn-inj-decision-msgid db) *srt-idless-mo-b*)
        (equal *srt-groups* (fn-article-groups held))
        (equal (fn-rcl-existing-action *srt-idless-msgid-b* (fn-inj-decision-octets db)
                                       *srt-groups* *srt-s-idless*) :conflict))))

(must-fail
 (defthm srt-retry-without-the-held-payload
   (let ((held (fn-find-article msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
         (da (fn-inj-decide source config a)) (db (fn-inj-decide source config b)))
     (implies (and (fn-inj-injectedp da) (fn-inj-injectedp db)
                   (equal (fn-inj-decision-msgid da) (fn-record-string-octets msgid))
                   (equal (fn-inj-decision-msgid db) (fn-record-string-octets msgid))
                   (equal groups (fn-article-groups held)))
              (equal (fn-rcl-existing-action msgid (fn-inj-decision-octets db) groups s)
                     :duplicate)))
   :hints (("Goal" :in-theory (disable fn-inj-decide fn-rcl-existing-action))))
 )
(must-fail
 (defthm srt-retry-without-the-groups
   (let ((held (fn-find-article msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
         (da (fn-inj-decide source config a)) (db (fn-inj-decide source config b)))
     (implies (and (equal (fn-article-payload held) (fn-inj-decision-octets da))
                   (fn-inj-injectedp da) (fn-inj-injectedp db)
                   (equal (fn-inj-decision-msgid da) (fn-record-string-octets msgid))
                   (equal (fn-inj-decision-msgid db) (fn-record-string-octets msgid)))
              (equal (fn-rcl-existing-action msgid (fn-inj-decision-octets db) groups s)
                     :duplicate)))
   :hints (("Goal" :in-theory (disable fn-inj-decide fn-rcl-existing-action)))))
(must-fail
 (defthm srt-retry-without-the-first-message-id
   (let ((held (fn-find-article msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
         (da (fn-inj-decide source config a)) (db (fn-inj-decide source config b)))
     (implies (and (equal (fn-article-payload held) (fn-inj-decision-octets da))
                   (fn-inj-injectedp da) (fn-inj-injectedp db)
                   (equal (fn-inj-decision-msgid db) (fn-record-string-octets msgid))
                   (equal groups (fn-article-groups held)))
              (equal (fn-rcl-existing-action msgid (fn-inj-decision-octets db) groups s)
                     :duplicate)))
   :hints (("Goal" :in-theory (disable fn-inj-decide fn-rcl-existing-action)))))

; -----------------------------------------------------------------------------
; fn-sr-a-changed-source-is-a-conflict: one changed body byte, a changed
; supplied Path tail (D32), an authored Date removed.
(assert-event
 (and (not (equal *srt-changed* *srt-dated*))
      (equal (fn-rcl-existing-action *srt-msgid* (srt-o *srt-changed* *srt-b*) *srt-groups*
                                     *srt-s-dated*) :conflict)
      (not (equal *srt-repathed* *srt-pathed*))
      (equal (fn-rcl-existing-action *srt-msgid* (srt-o *srt-repathed* *srt-b*) *srt-groups*
                                     *srt-s-pathed*) :conflict)
      (equal (fn-rcl-existing-action *srt-msgid* (srt-o *srt-dateless* *srt-b*) *srt-groups*
                                     *srt-s-dated*) :conflict)))
; Hypothesis removed: the sources are equal; the verdict is duplicate (the
; retry witness above, every other hypothesis kept).
(must-fail
 (defthm srt-conflict-without-distinct-sources
   (let ((da (fn-inj-decide source1 config a)) (db (fn-inj-decide source2 config b))
         (held (fn-find-article msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s))))))
     (implies (and (equal (fn-article-payload held) (fn-inj-decision-octets da))
                   (fn-inj-injectedp da) (fn-inj-injectedp db)
                   (equal (fn-inj-decision-msgid da) (fn-record-string-octets msgid))
                   (equal (fn-inj-decision-msgid db) (fn-record-string-octets msgid)))
              (equal (fn-rcl-existing-action msgid (fn-inj-decision-octets db) groups s)
                     :conflict)))
   :hints (("Goal" :in-theory (disable fn-inj-decide fn-rcl-existing-action)))))

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
 (and (equal (fn-rcl-existing-action *srt-msgid* (srt-o *srt-dateless* *srt-b*) *srt-groups*
                                     *srt-t-dateless*) :duplicate)
      (equal (fn-rcl-existing-action *srt-msgid* (srt-o *srt-pathed* *srt-b*) *srt-groups*
                                     *srt-t-pathed*) :duplicate)
      (equal (fn-rcl-existing-action *srt-msgid* (srt-o *srt-repathed* *srt-b*) *srt-groups*
                                     *srt-t-pathed*) :conflict)
      (not (fn-rcl-collisionp *srt-repathed* *srt-pathed*))
      (equal (fn-rcl-existing-action *srt-msgid* (srt-o *srt-pathed* *srt-b*) '("fn.other")
                                     *srt-t-pathed*) :conflict)))
; Hypothesis removed: the tombstone is another source's; conflict.
(assert-event
 (equal (fn-rcl-existing-action *srt-msgid* (srt-o *srt-changed* *srt-b*) *srt-groups*
                                (srt-reclaimed *srt-s-dated*
                                               (fn-rcl-tombstone-of (srt-o *srt-dated* *srt-a*)
                                                                    *srt-mo*)))
        :conflict))
(must-fail
 (defthm srt-conflict-after-reclaim-without-distinct-sources
   (let ((da (fn-inj-decide source1 config a)) (db (fn-inj-decide source2 config b))
         (held (fn-find-article msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s))))))
     (implies (and (equal (fn-article-payload held)
                          (fn-rcl-tombstone-of (fn-inj-decision-octets da)
                                               (fn-record-string-octets msgid)))
                   (fn-inj-injectedp da) (fn-inj-injectedp db)
                   (equal (fn-inj-decision-msgid da) (fn-record-string-octets msgid))
                   (equal (fn-inj-decision-msgid db) (fn-record-string-octets msgid)))
              (or (equal (fn-rcl-existing-action msgid (fn-inj-decision-octets db) groups s)
                         :conflict)
                  (fn-rcl-collisionp source2 source1))))
   :hints (("Goal" :in-theory (disable fn-inj-decide fn-rcl-existing-action)))))

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
(defconst *srt-s-signed* (srt-store (srt-carrier *srt-signed-source* *srt-a*)))
(assert-event
 (let ((held (srt-held *srt-s-signed*)))
   (and (srt-carrier *srt-signed-source* *srt-a*)
        (srt-carrier *srt-signed-source* *srt-b*)
        (equal (fn-article-payload held) (srt-carrier *srt-signed-source* *srt-a*))
        (equal (fn-inj-decision-msgid (srt-carrier-plan *srt-signed-source* *srt-a*)) *srt-mo*)
        (equal (fn-inj-decision-msgid (srt-carrier-plan *srt-signed-source* *srt-b*)) *srt-mo*)
        (equal *srt-groups* (fn-article-groups held))
        (equal (fn-rcl-existing-action *srt-msgid* (srt-carrier *srt-signed-source* *srt-b*)
                                       *srt-groups* *srt-s-signed*)
               :duplicate))))
; Hypothesis removed: the carrier of another source is held; conflict.
(assert-event
 (equal (fn-rcl-existing-action *srt-msgid* (srt-carrier *srt-signed-source* *srt-b*)
                                *srt-groups*
                                (srt-store (srt-carrier *srt-changed* *srt-a*)))
        :conflict))
; Hypothesis removed: other groups; conflict.
(assert-event
 (equal (fn-rcl-existing-action *srt-msgid* (srt-carrier *srt-signed-source* *srt-b*)
                                '("fn.other") *srt-s-signed*)
        :conflict))
; Hypothesis removed: no octets at B (injection disabled); no verdict of a
; duplicate is claimed, and the octets are nil.
(assert-event
 (null (fn-hsig-injected-carrier-octets
        *srt-signed-source* *srt-principal* *srt-keys* *srt-sigs*
        (fn-inj-make-config nil *srt-agent* (list (srt-text "fn.test")) 32768) *srt-b*)))
(must-fail
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
              (equal (fn-rcl-existing-action msgid ob groups s) :duplicate)))
   :hints (("Goal" :in-theory (disable fn-hsig-injected-carrier-octets
                                       fn-hsig-injected-carrier-plan fn-rcl-existing-action)))))
(must-fail
 (defthm srt-signed-retry-without-the-groups
   (let ((pa (fn-hsig-injected-carrier-plan source principal keys signatures config a))
         (pb (fn-hsig-injected-carrier-plan source principal keys signatures config b))
         (oa (fn-hsig-injected-carrier-octets source principal keys signatures config a))
         (ob (fn-hsig-injected-carrier-octets source principal keys signatures config b))
         (held (fn-find-article msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s))))))
     (implies (and oa ob (equal (fn-article-payload held) oa)
                   (equal (fn-inj-decision-msgid pa) (fn-record-string-octets msgid))
                   (equal (fn-inj-decision-msgid pb) (fn-record-string-octets msgid)))
              (equal (fn-rcl-existing-action msgid ob groups s) :duplicate)))
   :hints (("Goal" :in-theory (disable fn-hsig-injected-carrier-octets
                                       fn-hsig-injected-carrier-plan fn-rcl-existing-action)))))
