; Canonical submission fields under the exact names consumed by owner take.
; fn-owner-take -> fn-own-take-submission -> fn-own-sub-make-author;
; fn-owner-take/ABI reads fn-own-sub-source-context from that same record.
; This field/effects boundary does not establish ingress authority or an owner invariant.
(in-package "ACL2")
(include-book "acceptance-alloc")
(include-book "packed-submission")

; -----------------------------------------------------------------------------
; The submission record: (id version mark decision login account context).  A served read of
; connection `id`, pinned at `version`, injected `decision` (an
; fn-inj-injectedp decision record: the article's octets, Message-ID and
; groups, books/injection.lisp).  `mark` is nil in the queue and the length
; of the ledger at the moment fn-own-take-submission moved it into the durable path.

(defun fn-own-sub-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 7)))
(defun fn-own-sub-id (x)
  (declare (xargs :guard t))
  (mbe :logic (car x) :exec (fn-ag-car x)))
(defun fn-own-sub-version (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))
(defun fn-own-sub-mark (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr x))) :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))
(defun fn-own-sub-decision (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr x))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))
(defun fn-own-sub-source-context (x)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
               (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))))

(defun fn-own-sub-make (id version mark decision context)
  (declare (xargs :guard t))
  (list id version mark decision nil nil context))

(defthm fn-own-sub-source-context-of-make
  (equal (fn-own-sub-source-context
          (fn-own-sub-make id version mark decision context)) context))

(defthm fn-own-sub-shapep-of-fn-own-sub-make
  (fn-own-sub-shapep (fn-own-sub-make id version mark decision context)))
(defthm fn-own-sub-id-of-fn-own-sub-make
  (equal (fn-own-sub-id (fn-own-sub-make id version mark decision context)) id))
(defthm fn-own-sub-version-of-fn-own-sub-make
  (equal (fn-own-sub-version (fn-own-sub-make id version mark decision context)) version))
(defthm fn-own-sub-mark-of-fn-own-sub-make
  (equal (fn-own-sub-mark (fn-own-sub-make id version mark decision context)) mark))
(defthm fn-own-sub-decision-of-fn-own-sub-make
  (equal (fn-own-sub-decision (fn-own-sub-make id version mark decision context)) decision))
(defthm fn-own-sub-shapep-forward-shape
  (implies (fn-own-sub-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)
(defthm fn-own-sub-make-is-consp
  (consp (fn-own-sub-make id version mark decision context))
  :rule-classes (:rewrite :type-prescription))

; The author of a served submission (SEC-006, PRF-210): the AUTHINFO USER
; name (LOGIN) and the principal id (ACCOUNT, books/nntp-auth.lisp
; fn-auth-session-subject) the connection had authenticated as BEFORE the
; read that completed the article (the session fn-own-finish-read is
; handed, not the one the read leaves: an AUTHINFO later in the same read
; never claims an article posted before it), recorded when it is enqueued.
; The account keys the RFC 8315 Cancel-Lock the stored octets carry, even
; when the connection is gone by the time the writer takes it; the login
; is what the posting-policy gate reads (books/login-binding.lisp
; fn-lb-inflight-login, PKT-619).  A submission without an author
; (control, BP, transit, an unauthenticated POST) carries nil login/account
; in the same seven-field shape: fn-own-sub-make-author with a nil login IS
; fn-own-sub-make, preserving the supplied source context.
(defun fn-own-sub-login (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr (cdr x)))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))
(defun fn-own-sub-account (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr (cdr (cdr x))))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))))
(defun fn-own-sub-make-author (id version mark decision login account context)
  (declare (xargs :guard t))
  (if login
      (list id version mark decision login account context)
    (fn-own-sub-make id version mark decision context)))

(defthm fn-own-sub-source-context-of-make-author
  (equal (fn-own-sub-source-context
          (fn-own-sub-make-author id version mark decision login account context))
         context))

(defthm fn-own-sub-make-author-of-no-login-by-definition
  (equal (fn-own-sub-make-author id version mark decision nil account context)
         (fn-own-sub-make id version mark decision context)))
(defthm fn-own-sub-login-of-fn-own-sub-make
  (equal (fn-own-sub-login (fn-own-sub-make id version mark decision context)) nil))
(defthm fn-own-sub-account-of-fn-own-sub-make
  (equal (fn-own-sub-account (fn-own-sub-make id version mark decision context)) nil))
(defthm fn-own-sub-shapep-of-fn-own-sub-make-author
  (fn-own-sub-shapep (fn-own-sub-make-author id version mark decision login account context)))
(defthm fn-own-sub-id-of-fn-own-sub-make-author
  (equal (fn-own-sub-id (fn-own-sub-make-author id version mark decision login account context)) id))
(defthm fn-own-sub-version-of-fn-own-sub-make-author
  (equal (fn-own-sub-version (fn-own-sub-make-author id version mark decision login account context))
         version))
(defthm fn-own-sub-mark-of-fn-own-sub-make-author
  (equal (fn-own-sub-mark (fn-own-sub-make-author id version mark decision login account context)) mark))
(defthm fn-own-sub-decision-of-fn-own-sub-make-author
  (equal (fn-own-sub-decision (fn-own-sub-make-author id version mark decision login account context))
         decision))
(defthm fn-own-sub-login-of-fn-own-sub-make-author
  (equal (fn-own-sub-login (fn-own-sub-make-author id version mark decision login account context))
         login))
(defthm fn-own-sub-account-of-fn-own-sub-make-author
  (equal (fn-own-sub-account (fn-own-sub-make-author id version mark decision login account context))
         (if login account nil)))
(defthm fn-own-sub-make-author-is-consp
  (consp (fn-own-sub-make-author id version mark decision login account context))
  :rule-classes (:rewrite :type-prescription))

(in-theory (disable (:d fn-own-sub-shapep) (:d fn-own-sub-id) (:d fn-own-sub-version)
                    (:d fn-own-sub-mark) (:d fn-own-sub-decision) (:d fn-own-sub-make)
                    (:d fn-own-sub-login) (:d fn-own-sub-account)
                    (:d fn-own-sub-make-author) (:d fn-own-sub-source-context)))

; The queued (packed) submission's fields (lane chunked-body-2, B6b;
; fn-own-enqueue packs, fn-own-take-submission unpacks): the packing touches
; only the decision's octets and an injection's groups.
(defthm fn-own-sub-fields-of-pack
  (and (equal (fn-own-sub-id (fn-psub-pack-sub x)) (fn-own-sub-id x))
       (equal (fn-own-sub-version (fn-psub-pack-sub x)) (fn-own-sub-version x))
       (equal (fn-own-sub-mark (fn-psub-pack-sub x)) (fn-own-sub-mark x))
       (equal (fn-own-sub-login (fn-psub-pack-sub x)) (fn-own-sub-login x))
       (equal (fn-own-sub-account (fn-psub-pack-sub x)) (fn-own-sub-account x))
       (equal (fn-own-sub-source-context (fn-psub-pack-sub x))
              (fn-own-sub-source-context x))
       (equal (fn-own-sub-decision (fn-psub-pack-sub x))
              (fn-psub-pack-decision (fn-own-sub-decision x)))
       (equal (fn-own-sub-shapep (fn-psub-pack-sub x)) (fn-own-sub-shapep x))
       (equal (consp (fn-psub-pack-sub x)) (consp x)))
  :hints (("Goal" :in-theory (enable fn-own-sub-id fn-own-sub-version fn-own-sub-mark
                                     fn-own-sub-login fn-own-sub-account fn-own-sub-source-context
                                     fn-own-sub-decision fn-own-sub-shapep
                                     fn-psub-pack-sub fn-psub-pack-decision))))

(defthm fn-own-sub-fields-of-unpack
  (and (equal (fn-own-sub-id (fn-psub-unpack-sub x)) (fn-own-sub-id x))
       (equal (fn-own-sub-version (fn-psub-unpack-sub x)) (fn-own-sub-version x))
       (equal (fn-own-sub-mark (fn-psub-unpack-sub x)) (fn-own-sub-mark x))
       (equal (fn-own-sub-login (fn-psub-unpack-sub x)) (fn-own-sub-login x))
       (equal (fn-own-sub-account (fn-psub-unpack-sub x)) (fn-own-sub-account x))
       (equal (fn-own-sub-source-context (fn-psub-unpack-sub x))
              (fn-own-sub-source-context x))
       (equal (fn-own-sub-decision (fn-psub-unpack-sub x))
              (fn-psub-unpack-decision (fn-own-sub-decision x)))
       (equal (consp (fn-psub-unpack-sub x)) (consp x)))
  :hints (("Goal" :in-theory (enable fn-own-sub-id fn-own-sub-version fn-own-sub-mark
                                     fn-own-sub-login fn-own-sub-account fn-own-sub-source-context
                                     fn-own-sub-decision
                                     fn-psub-unpack-sub fn-psub-unpack-decision))))

