; fn: own-post cancel for unsigned posts, RFC 8315 Cancel-Lock keyed by the
; posting login (SEC-006, PRF-210; PKT-576's default, the coordinator's
; decision of 2026-09-26).
;
; The login is the principal of an unsigned article on the node that
; injected it (planning/decisions.md, path-and-login).  Nothing durable
; names that login (the Store's kind-4 record does not, and D34 forbids
; adding it), so the node writes the login's material into the article's own
; octets, as RFC 8315 section 3.1 lets an injecting agent do for a posting
; agent without Cancel-Lock support:
;
;   K    = Base64(HMAC-SHA256(S, "fn cancel-lock v1" || 0x00 || MSGID || LOGIN))
;                                                       (RFC 8315 section 4;
;                                                        books/node-secret.lisp)
;   lock = Base64(SHA-256(K))                           (section 2.1)
;
; S is the node secret (books/node-secret.lisp: STORE/keys/node-secret.key,
; written by init, carried by the owner as fn-own-node-secret, never served
; and never written into a record).  On a served POST from login L the owner puts
; `Cancel-Lock: sha256:lock(S, MSGID, L)' in front of the injected octets;
; on a served cancel or Supersedes from L naming TARGET it also puts
; `Cancel-Key: sha256:K(S, TARGET, L)' (section 3.3's MUST for an agent
; that added the lock).  The withdrawal decision (books/control-authority.lisp
; `fn-ctl-withdrawal-effect', the :poster arm) then reads the two articles
; only: the same login's key opens the lock, on this node and on every peer
; the two articles reach; another login's key is K(S, TARGET, L') and opens
; it only if SHA-256 of two distinct HMAC outputs collide.
;
; A proto-article that already carries Cancel-Lock (tin does, with its own
; secret) gets no lock from the node (section 2: the field occurs at most
; once; the node does not rewrite the poster's field), and one that already
; carries Cancel-Key gets no key: the poster's own RFC 8315 keys decide.
; An unauthenticated POST, a control or BP submission, and a node without a
; readable secret add nothing: the article is filed and a cancel by login
; withdraws nothing, as before SEC-006.
;
; Prefix `fn-cl-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "cancel-lock-lines")
(include-book "node-secret")
(include-book "control-authority")

; -----------------------------------------------------------------------------
; The login's key and lock for one Message-ID.  MSGID and LOGIN are octets;
; a Message-ID ends with ">" and contains no other, so MSGID || LOGIN is
; read back uniquely.

(defun fn-cl-secretp (s)
  (declare (xargs :guard t))
  (fn-ns-secretp s))

; The node secret's Cancel-Lock use (books/node-secret.lisp: HMAC-SHA256
; under the label "fn cancel-lock v1", separated from every other use).
(defun fn-cl-key (secret msgid login)
  (declare (xargs :guard t))
  (fn-stx-b64-encode (fn-ns-cancel-lock-mac secret (fn-cll-append msgid login))))

(defun fn-cl-lock (secret msgid login)
  (declare (xargs :guard t))
  (fn-ctl-lock-of-key (fn-cl-key secret msgid login)))

; -----------------------------------------------------------------------------
; The served payload: the served arm of books/owner-served-invariants.lisp
; fn-own-sub-stored-octets, which host/owner-host.lisp fn-owner-take stages
; for the Store and fn-owner-finish-submission's completion gate compares
; with the durable record.  SECRET the owner's fn-own-node-secret (nil
; before the host installed one), LOGIN the submission's recorded login
; (fn-own-sub-login, nil when none), MSGID the injected Message-ID's
; octets, PAYLOAD the injected octets.

(defun fn-cl-lock-wanted-p (secret login fields)
  (declare (xargs :guard t))
  (and (fn-cl-secretp secret)
       (fn-cbor-octet-listp login) (consp login)
       (not (consp (fn-ctl-fields-named *fn-ctl-cancel-lock-name* fields)))))

; The target a key is added for: the article's cancel or Supersedes target,
; when it carries no Cancel-Key of its own.
(defun fn-cl-key-target (secret login fields)
  (declare (xargs :guard t))
  (and (fn-cl-secretp secret)
       (fn-cbor-octet-listp login) (consp login)
       (not (consp (fn-ctl-fields-named *fn-ctl-cancel-key-name* fields)))
       (fn-ctl-article-target fields)))

; The Cancel-Key line for the target of a cancel or Supersedes (nil when
; there is none, or the poster wrote their own Cancel-Key).
(defun fn-cl-key-lines (secret login fields)
  (declare (xargs :guard t))
  (let ((target (fn-cl-key-target secret login fields)))
    (if target
        (fn-cll-line *fn-cll-key-head*
                     (fn-cl-key secret (fn-record-string-octets target) login))
      nil)))

(defun fn-cl-served-payload (secret login msgid payload)
  (declare (xargs :guard t))
  (let* ((fields (fn-ctl-received-fields payload))
         (target (fn-cl-key-target secret login fields)))
    (if (or (fn-cl-lock-wanted-p secret login fields) target)
        (fn-cll-insert
         (fn-cll-append
          (if (fn-cl-lock-wanted-p secret login fields)
              (fn-cll-line *fn-cll-lock-head* (fn-cl-lock secret msgid login))
            nil)
          (fn-cl-key-lines secret login fields))
         payload)
      payload)))

; -----------------------------------------------------------------------------
; Theorems.

; Without a login, or without a secret, the payload is stored as injected.
(defthm fn-cl-served-payload-without-a-login-is-the-payload
  (implies (or (not (consp login)) (not (fn-cl-secretp secret)))
           (equal (fn-cl-served-payload secret login msgid payload) payload)))

; The lines are well formed: a key and a lock are 44 Base64 characters
; (RFC 8315 section 2's c-lock-string).
(defthm fn-cl-b64-encode-valuep
  (fn-cll-valuep (fn-stx-b64-encode x))
  :hints (("Goal" :in-theory (enable fn-stx-b64-encode fn-stx-b64-sextet))))

(local
 (defun fn-cl-b64-length (n)
   (declare (xargs :measure (nfix n)))
   (if (zp n) 0 (if (< n 3) 4 (+ 4 (fn-cl-b64-length (- n 3)))))))

(local
 (defthm fn-cl-b64-encode-exact-length
   (equal (len (fn-stx-b64-encode x)) (fn-cl-b64-length (len x)))
   :hints (("Goal" :induct (fn-stx-b64-encode x)
            :in-theory (enable fn-stx-b64-encode)))))

(defthm fn-cl-b64-encode-true-listp
  (true-listp (fn-stx-b64-encode x))
  :hints (("Goal" :in-theory (enable fn-stx-b64-encode))))

(defthm fn-cl-key-shape
  (and (fn-cll-valuep (fn-cl-key secret msgid login))
       (true-listp (fn-cl-key secret msgid login))
       (equal (len (fn-cl-key secret msgid login)) *fn-cll-value-length*)))

(defthm fn-cl-lock-shape
  (and (fn-cll-valuep (fn-cl-lock secret msgid login))
       (true-listp (fn-cl-lock secret msgid login))
       (equal (len (fn-cl-lock secret msgid login)) *fn-cll-value-length*)))

; KEYSTONE (SEC-006, the same login is accepted).  The key the node writes
; into login L's cancel of TARGET opens the lock it wrote into L's article
; TARGET, whatever other keys and locks the two articles carry; so, by
; `fn-ctl-withdrawal-authority-is-exactly-signer-or-poster', the record of an
; unsigned cancel carrying that key withdraws that article.  The subject is
; the pair the effect compares: `fn-ctl-some-key-opens-p' over the entries
; `fn-cl-served-payload' writes.  The step from the written line to the
; parsed entry (the article parser over the prepended line) is not a
; theorem here: the teeth book checks it on served articles, and the record
; names it open (planning/evidence/newsreader-cancel-2026-09-26.md).
(defthm fn-cl-lock-memberp-of-append-cons
  (fn-ctl-lock-memberp x (append a (cons x b))))

(defthm fn-cl-login-key-opens-login-lock
  (implies (member-equal (fn-cl-key secret target login) keys)
           (fn-ctl-some-key-opens-p
            keys (append locks (list (fn-cl-lock secret target login)) more)))
  :hints (("Goal" :induct (len keys)
           :in-theory (disable fn-cl-key fn-ctl-lock-of-key))))

; The lines a served POST under LOGIN gets, when the node holds a secret and
; the poster wrote no Cancel-Lock of their own: exactly one Cancel-Lock line,
; LOGIN's lock for this Message-ID, then the Cancel-Key line of a cancel, at
; the end of the node's Injection-Info line; every other octet as injected.
(defthm fn-cl-served-payload-writes-one-login-lock
  (let ((fields (fn-ctl-received-fields payload))
        (k (fn-cll-info-end payload 0 :start)))
    (implies (and (fn-ns-secretp secret)
                  (fn-cbor-octet-listp login) (consp login)
                  (not (consp (fn-ctl-fields-named *fn-ctl-cancel-lock-name* fields))))
             (equal (fn-cl-served-payload secret login msgid payload)
                    (if k
                        (append (fn-cll-take k payload)
                                (fn-cll-line *fn-cll-lock-head*
                                             (fn-cl-lock secret msgid login))
                                (fn-cl-key-lines secret login fields)
                                (fn-cll-drop k payload))
                      payload))))
  :hints (("Goal" :in-theory (e/d (fn-cl-secretp)
                                  (fn-cl-lock fn-cl-key-lines fn-cl-key-target
                                   fn-ctl-received-fields fn-cll-line
                                   fn-cll-info-end fn-cll-take fn-cll-drop))
           :use ((:instance fn-cll-insert-adds-only-the-lines
                            (x payload)
                            (lines (append (fn-cll-line *fn-cll-lock-head*
                                                        (fn-cl-lock secret msgid login))
                                           (fn-cl-key-lines secret login
                                                            (fn-ctl-received-fields payload)))))))))

; KEYSTONE (SEC-006, exactly the login's key opens the login's lock).  Over
; the one lock the node writes for LOGIN: the key the node derives for a
; login L2 opens it exactly when L2's lock for this Message-ID is LOGIN's.
; So LOGIN's own key opens it (L2 = LOGIN), and another login's key opens it
; only when SHA-256 of the two HMAC-SHA256 outputs collide under the node
; secret: that is the cryptographic assumption no theorem states
; (planning/evidence/newsreader-cancel-2026-09-26.md, the pessimistic
; figure), and the teeth show a concrete other login refused.
(defthm fn-cl-login-key-opens-exactly-its-lock
  (iff (fn-ctl-some-key-opens-p (list (fn-cl-key secret msgid l2))
                                (list (fn-cl-lock secret msgid login)))
       (equal (fn-cl-lock secret msgid l2) (fn-cl-lock secret msgid login)))
  :hints (("Goal" :in-theory (disable fn-cl-key fn-ctl-lock-of-key))))
