; fn: own-post cancel for unsigned posts, RFC 8315 Cancel-Lock keyed by the
; posting ACCOUNT (SEC-006, PRF-210; PKT-576's default, the coordinator's
; decisions of 2026-09-26; gpt-6's wave-5 review section 3, binding).
;
; The account is the principal of an unsigned article on the node that
; injected it.  Nothing durable names that account (the Store's kind-4
; record does not, and D34 forbids adding it), so the node writes the
; account's material into the article's own octets, as RFC 8315 section 3.1
; lets an injecting agent do for a posting agent without Cancel-Lock
; support (RFC 8315 section 4, K = HMAC(sec, uid+mid)):
;
;   sec  = the cancel-lock purpose key of the key epoch E
;          (books/node-secret.lisp fn-ns-cancel-lock-key: HKDF-SHA256 of the
;          epoch's root, salt the node identity, info "fn/cancel-lock/v1")
;   uid  = the account id in lowercase hex (no angle brackets, section 4)
;   mid  = the Message-ID with its angle brackets
;   K    = HMAC-SHA256(sec, uid || mid); the c-key-string is Base64(K)
;   lock = Base64(SHA-256(Base64(K)))   (section 2.1: the hash is over the
;          Base64-encoded key; `fn-ctl-lock-of-key' hashes the key entry's
;          octets as they are written, RFC 8315 section 5.2's example in the
;          teeth)
;
; The account id is the principal the connection authenticated as
; (books/nntp-auth.lisp fn-auth-session-subject), recorded on the
; submission when it is enqueued (books/owner.lisp fn-own-sub-account): the
; credential's configured principal, or for a redeemed account its local
; principal, which no later record changes or reassigns
; (fn-acct-redeemed-row-stays-across-replay).  Not the login spelling.
;
; On a served POST from account A the owner puts `Cancel-Lock:
; sha256:lock(E, A, MSGID)' under the CURRENT epoch E in front of the
; injected octets; on a served cancel or Supersedes from A naming TARGET it
; also puts `Cancel-Key:' with one key K(E', A, TARGET) per RETAINED epoch
; E', current first, so an article locked before a rotation stays
; cancellable by its poster (`fn-cl-ring-keys-open-every-retained-lock').
; The lines stand in front of the injected block, outside the authored
; source (books/cancel-lock-lines.lisp; D25): a same-source retry from
; another account or after a rotation is the article already stored, its
; lock unchanged, and the retrying account gets no key that opens it.
;
; The withdrawal decision (books/control-authority.lisp
; `fn-ctl-withdrawal-effect', the :poster arm) reads the two articles only:
; A's key opens A's lock, on this node and on every peer the two articles
; reach; another account's key opens it only if SHA-256 of two distinct HMAC
; outputs collide.
;
; A proto-article that already carries Cancel-Lock (tin does, with its own
; secret) gets no lock from the node (section 2: the field occurs at most
; once; the poster's field is the poster's input and is never rewritten),
; one that already carries Cancel-Key gets no key, and a signed article
; (an FN-Authorship carrier) gets neither: its signer is its principal and
; its signed bytes are never edited.  An unauthenticated POST, a control or
; BP submission, and an owner without a key ring add nothing.
;
; Prefix `fn-cl-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "cancel-lock-lines")
(include-book "node-secret")
(include-book "control-authority")
(include-book "identity")

; -----------------------------------------------------------------------------
; RFC 8315 section 4 over an explicit secret: Base64(HMAC-SHA256(SEC, UID ||
; MID)).  Section 5.2's example is in the teeth.

(defun fn-cl-rfc8315-key (sec uid mid)
  (declare (xargs :guard t))
  (fn-stx-b64-encode (fn-ns-hmac-sha256 sec (fn-cll-append uid mid))))

; The account id's uid: its lowercase hex.
(defun fn-cl-uid (account)
  (declare (xargs :guard t))
  (if (fn-cbor-octet-listp account) (fn-id-hex-octets account) nil))

; The key and lock of ACCOUNT for Message-ID MSGID under key epoch ENTRY.
(defun fn-cl-key (entry account msgid)
  (declare (xargs :guard t))
  (fn-cl-rfc8315-key (fn-ns-cancel-lock-key entry) (fn-cl-uid account) msgid))

(defun fn-cl-lock (entry account msgid)
  (declare (xargs :guard t))
  (fn-ctl-lock-of-key (fn-cl-key entry account msgid)))

; One key per retained epoch of RING, current first.
(defun fn-cl-ring-keys (ring account msgid)
  (declare (xargs :guard t))
  (if (consp ring)
      (cons (fn-cl-key (car ring) account msgid)
            (fn-cl-ring-keys (cdr ring) account msgid))
    nil))

; -----------------------------------------------------------------------------
; The served payload: the served arm of books/owner-served-invariants.lisp
; fn-own-sub-stored-octets, which host/owner-host.lisp fn-owner-take stages
; for the Store and fn-owner-finish-submission's completion gate compares
; with the durable record.  RING the owner's fn-own-node-secret (nil before
; the host installed one), ACCOUNT the submission's recorded account
; (fn-own-sub-account, nil when none), MSGID the injected Message-ID's
; octets, PAYLOAD the injected octets.

; "fn-authorship", the signed carrier's field (books/hybrid-carrier.lisp).
(defconst *fn-cl-authorship-name*
  '(102 110 45 97 117 116 104 111 114 115 104 105 112))

(defun fn-cl-accountp (account)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp account) (consp account)))

(defun fn-cl-unsigned-p (fields)
  (declare (xargs :guard t))
  (not (consp (fn-ctl-fields-named *fn-cl-authorship-name* fields))))

(defun fn-cl-lock-wanted-p (ring account fields)
  (declare (xargs :guard t))
  (and (fn-ns-ringp ring) (fn-cl-accountp account) (fn-cl-unsigned-p fields)
       (not (consp (fn-ctl-fields-named *fn-ctl-cancel-lock-name* fields)))))

; The target a key is added for: the article's cancel or Supersedes target,
; when it carries no Cancel-Key of its own.
(defun fn-cl-key-target (ring account fields)
  (declare (xargs :guard t))
  (and (fn-ns-ringp ring) (fn-cl-accountp account) (fn-cl-unsigned-p fields)
       (not (consp (fn-ctl-fields-named *fn-ctl-cancel-key-name* fields)))
       (fn-ctl-article-target fields)))

(defun fn-cl-lock-value (ring account msgid fields)
  (declare (xargs :guard t))
  (if (fn-cl-lock-wanted-p ring account fields)
      (fn-cl-lock (fn-ns-current ring) account msgid)
    nil))

(defun fn-cl-key-values (ring account fields)
  (declare (xargs :guard t))
  (let ((target (fn-cl-key-target ring account fields)))
    (if target
        (fn-cl-ring-keys ring account (fn-record-string-octets target))
      nil)))

(defun fn-cl-served-payload (ring account msgid payload)
  (declare (xargs :guard t))
  (let ((fields (fn-ctl-received-fields payload)))
    (fn-cll-append (fn-cll-lines (fn-cl-lock-value ring account msgid fields)
                                 (fn-cl-key-values ring account fields))
                   payload)))

; -----------------------------------------------------------------------------
; Theorems.

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
  (and (fn-cll-valuep (fn-cl-key entry account msgid))
       (true-listp (fn-cl-key entry account msgid))
       (equal (len (fn-cl-key entry account msgid)) *fn-cll-value-length*)))

(defthm fn-cl-lock-shape
  (and (fn-cll-valuep (fn-cl-lock entry account msgid))
       (true-listp (fn-cl-lock entry account msgid))
       (equal (len (fn-cl-lock entry account msgid)) *fn-cll-value-length*)))

(defthm fn-cl-lock-is-a-cons
  (consp (fn-cl-lock entry account msgid))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use fn-cl-lock-shape :in-theory (disable fn-cl-lock fn-cl-lock-shape))))

(defthm fn-cl-ring-keys-are-values
  (fn-cll-values-p (fn-cl-ring-keys ring account msgid)))

(defthm fn-cl-key-values-are-values
  (fn-cll-values-p (fn-cl-key-values ring account fields)))

(defthm fn-cl-lock-value-is-a-value
  (fn-cll-valuep (fn-cl-lock-value ring account msgid fields)))

(in-theory (disable fn-cl-key fn-cl-lock))

; Without an account, or without a ring, the payload is stored as injected.
(defthm fn-cl-served-payload-without-an-account-is-the-payload
  (implies (or (not (fn-cl-accountp account)) (not (fn-ns-ringp ring)))
           (equal (fn-cl-served-payload ring account msgid payload) payload)))

; By definition: the generated lines, then the injected octets.
(defthm fn-cl-served-payload-is-the-lines-then-the-payload-by-definition
  (equal (fn-cl-served-payload ring account msgid payload)
         (append (fn-cll-lines (fn-cl-lock-value ring account msgid
                                                 (fn-ctl-received-fields payload))
                               (fn-cl-key-values ring account
                                                 (fn-ctl-received-fields payload)))
                 payload))
  :rule-classes nil)

; KEYSTONE (D25, the generated lines are outside the authored source).
; For every key ring and account, the D25 projection of the served payload
; is the injected octets: the lock and keys never enter the comparison.
; Subject: fn-cl-served-payload, the local arm of fn-own-sub-stored-octets
; (host/owner-host.lisp fn-owner-take); the projection is fn-cll-skip,
; called by books/poster-bytes.lisp.  The hypothesis holds of every
; injection (it opens with its block: books/source-routes.lisp
; fn-sr-a-block-opens-with-a-field-name).
(defthm fn-cl-served-payload-projects-to-the-injected-octets
  (implies (not (equal (car payload) 67))
           (equal (fn-cll-skip (fn-cl-served-payload ring account msgid payload))
                  payload))
  :hints (("Goal" :use ((:instance fn-cll-skip-of-the-generated-lines
                                   (lock (fn-cl-lock-value ring account msgid
                                                           (fn-ctl-received-fields payload)))
                                   (keys (fn-cl-key-values ring account
                                                           (fn-ctl-received-fields payload)))
                                   (x payload)))
           :in-theory (disable fn-cll-lines fn-cl-lock-value fn-cl-key-values
                               fn-ctl-received-fields))))

; The lock line a served POST under ACCOUNT gets, when the owner holds a
; ring, the poster wrote no Cancel-Lock and signed nothing: exactly one
; Cancel-Lock line, ACCOUNT's lock for this Message-ID under the current
; epoch, then the Cancel-Key line of a cancel, then the injected octets.
(defthm fn-cl-served-payload-writes-one-account-lock
  (let ((fields (fn-ctl-received-fields payload)))
    (implies (fn-cl-lock-wanted-p ring account fields)
             (equal (fn-cl-served-payload ring account msgid payload)
                    (append (fn-cll-line *fn-cll-lock-head*
                                         (fn-cl-lock (fn-ns-current ring) account msgid))
                            (if (consp (fn-cl-key-values ring account fields))
                                (fn-cll-key-line (fn-cl-key-values ring account fields))
                              nil)
                            payload))))
  :hints (("Goal" :in-theory (disable fn-cl-key-values fn-ctl-received-fields
                                      fn-cl-lock-wanted-p fn-cll-line fn-cll-key-line))))

(defthm fn-cl-lock-memberp-of-append-cons
  (fn-ctl-lock-memberp x (append a (cons x b))))

(local
 (defthm fn-cl-some-key-opens-of-member
   (implies (and (member-equal k keys)
                 (fn-ctl-lock-memberp (fn-ctl-lock-of-key k) locks))
            (fn-ctl-some-key-opens-p keys locks))))

; KEYSTONE (rotation retains service).  Whatever retained epoch ENTRY of
; RING an article's lock was made under, the keys the node writes into its
; account's cancel of it (one per retained epoch) include one that opens it.
; Subject: fn-cl-ring-keys, the key line of fn-cl-served-payload.
(defthm fn-cl-ring-keys-open-every-retained-lock
  (implies (and (member-equal entry ring)
                (fn-ctl-lock-memberp (fn-cl-lock entry account msgid) locks))
           (fn-ctl-some-key-opens-p (fn-cl-ring-keys ring account msgid) locks))
  :hints (("Goal" :induct (fn-cl-ring-keys ring account msgid)
           :in-theory (e/d (fn-cl-lock) (fn-ctl-lock-of-key)))))

; KEYSTONE (exactly the account's key opens the account's lock).  Over the
; one lock the node writes for ACCOUNT under ENTRY: the key it derives for
; an account A2 opens it exactly when A2's lock for this Message-ID is
; ACCOUNT's.  So ACCOUNT's own key opens it, and another account's key
; opens it only when SHA-256 of the two HMAC-SHA256 outputs collide under
; the purpose key: the cryptographic assumption no theorem states
; (planning/evidence/newsreader-cancel-2026-09-26.md, the pessimistic
; figure); the teeth show a concrete retrying account refused.
(defthm fn-cl-account-key-opens-exactly-its-lock
  (iff (fn-ctl-some-key-opens-p (list (fn-cl-key entry a2 msgid))
                                (list (fn-cl-lock entry account msgid)))
       (equal (fn-cl-lock entry a2 msgid) (fn-cl-lock entry account msgid)))
  :hints (("Goal" :in-theory (enable fn-cl-lock))))
