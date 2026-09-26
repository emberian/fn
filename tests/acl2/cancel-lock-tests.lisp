; Teeth for SEC-006 (PRF-210): own-post cancel by RFC 8315 Cancel-Lock keyed
; by the posting login (books/cancel-lock.lisp, books/cancel-lock-lines.lisp,
; the :poster arm of books/control-authority.lisp).  Per keystone a reachable
; witness asserting the complete antecedent and conclusion, and per
; hypothesis a removal witness (AGENTS.md, "Teeth ship with each keystone").
; The articles are parsed by the article parser the served path uses, so the
; witnesses also check the step no theorem covers: the line the owner writes
; parses back as the entry the decision reads.
(in-package "ACL2")
(include-book "../../books/cancel-lock")
(include-book "../../books/control-visible")
(include-book "std/testing/must-fail" :dir :system)

(defun clt-octets (s) (fn-record-string-octets s))
(defun clt-crlf-join (lines)
  (if (consp lines)
      (append (clt-octets (car lines)) (list 13 10) (clt-crlf-join (cdr lines)))
    nil))

; ---------------------------------------------------------------------------
; HMAC-SHA256 against RFC 4231 test cases 2 and 6 (a key over the block
; length is hashed first).
(defun clt-hex (octets)
  (if (consp octets)
      (let ((d "0123456789abcdef"))
        (concatenate 'string (string (char d (floor (car octets) 16)))
                     (string (char d (mod (car octets) 16)))
                     (clt-hex (cdr octets))))
    ""))
(assert-event
 (equal (clt-hex (fn-ns-hmac-sha256 (clt-octets "Jefe")
                                    (clt-octets "what do ya want for nothing?")))
        "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"))
(assert-event
 (equal (clt-hex (fn-ns-hmac-sha256
                  (make-list 131 :initial-element 170)
                  (clt-octets "Test Using Larger Than Block-Size Key - Hash Key First")))
        "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54"))

; ---------------------------------------------------------------------------
; Two logins on one node, one secret.
(defconst *clt-secret* (make-list 32 :initial-element 7))
(defconst *clt-alice* (clt-octets "alice"))
(defconst *clt-bob* (clt-octets "bob"))
(defconst *clt-t-id* "<t1@fn.test>")

; An injected article (recipe v2 block) and cancels of it, as injected.
(defconst *clt-t*
  (clt-crlf-join (list "Path: fn.test!not-for-mail" "Injection-Info: fn.test"
                       "From: alice <alice@example.invalid>"
                       "Newsgroups: local.general" "Subject: mine"
                       "Message-ID: <t1@fn.test>" "" "hello")))
(defun clt-cancel (id)
  (clt-crlf-join (list "Path: fn.test!not-for-mail" "Injection-Info: fn.test"
                       "From: someone <someone@example.invalid>"
                       "Newsgroups: local.general" "Subject: cmsg cancel <t1@fn.test>"
                       "Control: cancel <t1@fn.test>"
                       (concatenate 'string "Message-ID: " id) "" "cancel")))
(defconst *clt-c-alice* (clt-cancel "<c1@fn.test>"))
(defconst *clt-c-bob* (clt-cancel "<c2@fn.test>"))

; What the owner stores (fn-cl-served-payload, the host's call).
(defconst *clt-t-stored*
  (fn-cl-served-payload *clt-secret* *clt-alice* (clt-octets *clt-t-id*) *clt-t*))
(defconst *clt-c-alice-stored*
  (fn-cl-served-payload *clt-secret* *clt-alice* (clt-octets "<c1@fn.test>")
                        *clt-c-alice*))
(defconst *clt-c-bob-stored*
  (fn-cl-served-payload *clt-secret* *clt-bob* (clt-octets "<c2@fn.test>")
                        *clt-c-bob*))

; The written lines parse back as the entries: the target's one lock is
; alice's lock for its Message-ID; each cancel's one key is its login's key
; for the target; the cancel also gets its own lock.
(assert-event
 (equal (fn-ctl-locks-octets *clt-t-stored*)
        (list (fn-cl-lock *clt-secret* (clt-octets *clt-t-id*) *clt-alice*))))
(assert-event
 (equal (fn-ctl-keys-octets *clt-c-alice-stored*)
        (list (fn-cl-key *clt-secret* (clt-octets *clt-t-id*) *clt-alice*))))
(assert-event
 (equal (fn-ctl-keys-octets *clt-c-bob-stored*)
        (list (fn-cl-key *clt-secret* (clt-octets *clt-t-id*) *clt-bob*))))
(assert-event
 (equal (fn-ctl-locks-octets *clt-c-alice-stored*)
        (list (fn-cl-lock *clt-secret* (clt-octets "<c1@fn.test>") *clt-alice*))))
(assert-event (equal (fn-ctl-target-octets *clt-c-alice-stored*) *clt-t-id*))
(assert-event (null (fn-ctl-keys-octets *clt-t-stored*)))

; ---------------------------------------------------------------------------
; fn-ctl-withdrawal-authority-is-exactly-signer-or-poster: the positive
; witness (an unsigned cause, no verified principal, its key opens the
; target's lock; the record withdraws, :poster).
(defconst *clt-cfg* (fn-cfg-initial))
(defconst *clt-w-alice*
  (fn-ctl-withdrawal-plan "<c1@fn.test>" nil *clt-t-id*
                          (fn-ctl-keys-octets *clt-c-alice-stored*) *clt-cfg*))
(assert-event
 (and (null (fn-ctl-verified-principal nil))
      *clt-t-id* (not (equal *clt-t-id* "<c1@fn.test>"))
      (fn-ctl-some-key-opens-p (fn-ctl-keys-octets *clt-c-alice-stored*)
                               (fn-ctl-locks-octets *clt-t-stored*))
      (fn-ctl-withdrawalp *clt-w-alice*)
      (equal (fn-ctl-w-principal *clt-w-alice*)
             (cons :cancel-key (fn-ctl-keys-octets *clt-c-alice-stored*)))
      (equal (fn-ctl-withdrawal-effect *clt-w-alice* (list "local.general") nil
                                       *clt-t-stored*)
             :poster)))

; Removal of "the key opens a lock": bob's cancel (another login on the same
; node) makes a record and is refused by name.
(defconst *clt-w-bob*
  (fn-ctl-withdrawal-plan "<c2@fn.test>" nil *clt-t-id*
                          (fn-ctl-keys-octets *clt-c-bob-stored*) *clt-cfg*))
(assert-event
 (and (fn-ctl-withdrawalp *clt-w-bob*)
      (not (fn-ctl-some-key-opens-p (fn-ctl-keys-octets *clt-c-bob-stored*)
                                    (fn-ctl-locks-octets *clt-t-stored*)))
      (equal (fn-ctl-withdrawal-effect *clt-w-bob* (list "local.general") nil
                                       *clt-t-stored*)
             (list :decline :no-lock-match))))

; Removal of the lock: the same key against the article as injected, with no
; lock (a post made before SEC-006, or unauthenticated).
(assert-event
 (and (null (fn-ctl-locks-octets *clt-t*))
      (equal (fn-ctl-withdrawal-effect *clt-w-alice* (list "local.general") nil
                                       *clt-t*)
             (list :decline :no-lock-match))))

; Removal of the key: an unsigned cancel carrying none declines :unsigned,
; as before SEC-006.
(assert-event
 (and (null (fn-ctl-keys-octets *clt-c-alice*))
      (equal (fn-ctl-withdrawal-plan "<c1@fn.test>" nil *clt-t-id*
                                     (fn-ctl-keys-octets *clt-c-alice*) *clt-cfg*)
             (list :decline :unsigned))))

; Removal of "target other than itself".
(assert-event
 (equal (fn-ctl-withdrawal-plan "<c1@fn.test>" nil "<c1@fn.test>"
                                (fn-ctl-keys-octets *clt-c-alice-stored*) *clt-cfg*)
        (list :decline :self-target)))

; Must-fail: the keystone without its conclusion's poster disjunct.
(must-fail
 (defthm clt-poster-arm-is-necessary
   (let ((w (fn-ctl-withdrawal-plan cause verdict target keys cfg)))
     (implies (and (fn-ctl-withdrawalp w)
                   (fn-ctl-effect-withdrawsp
                    (fn-ctl-withdrawal-effect w t-groups t-verdict t-received)))
              (fn-ctl-verified-principal verdict)))
   :hints (("Goal" :in-theory (disable fn-ctl-some-key-opens-p
                                       fn-ctl-locks-octets)))))

; ---------------------------------------------------------------------------
; fn-ctl-verified-cause-ignores-its-keys: a signed canceller unchanged.
(defconst *clt-p* (make-list 32 :initial-element 17))
(defconst *clt-p-verified* (fn-stx-make-verdict :verified *clt-p* 1))
(assert-event
 (let ((keys (fn-ctl-keys-octets *clt-c-alice-stored*)))
   (and (fn-ctl-verified-principal *clt-p-verified*)
        (consp keys)
        (equal (fn-ctl-withdrawal-plan "<c1@fn.test>" *clt-p-verified* *clt-t-id*
                                       keys *clt-cfg*)
               (fn-ctl-withdrawal-plan "<c1@fn.test>" *clt-p-verified* *clt-t-id*
                                       nil *clt-cfg*))
        (equal (fn-ctl-w-principal
                (fn-ctl-withdrawal-plan "<c1@fn.test>" *clt-p-verified* *clt-t-id*
                                        keys *clt-cfg*))
               (fn-ctl-verified-principal *clt-p-verified*)))))
; Removal of the verified principal: the same cause unsigned is a key record.
(assert-event
 (not (equal (fn-ctl-withdrawal-plan "<c1@fn.test>" nil *clt-t-id*
                                     (fn-ctl-keys-octets *clt-c-alice-stored*)
                                     *clt-cfg*)
             (fn-ctl-withdrawal-plan "<c1@fn.test>" nil *clt-t-id* nil *clt-cfg*))))
; A signed record (the verified principal, no grant) does not withdraw an
; unsigned target even when the target carries a lock the cause's key opens:
; the signed arm decides, and it names no author and no grant.
(assert-event
 (equal (fn-ctl-withdrawal-effect
         (fn-ctl-withdrawal-plan "<c1@fn.test>" *clt-p-verified* *clt-t-id*
                                 (fn-ctl-keys-octets *clt-c-alice-stored*) *clt-cfg*)
         (list "local.general") nil *clt-t-stored*)
        (list :decline :no-grant)))

; ---------------------------------------------------------------------------
; fn-ctl-key-record-without-an-opened-lock-declines-by-definition: covered by bob
; above; removal of "key record": a principal record declines by its own arms.
(assert-event
 (equal (fn-ctl-withdrawal-effect
         (fn-ctl-withdrawal-make *clt-t-id* "<c1@fn.test>" "abc" nil 1)
         (list "local.general") nil *clt-t-stored*)
        (list :decline :no-grant)))

; ---------------------------------------------------------------------------
; fn-cl-login-key-opens-login-lock: witness with other entries around.
(assert-event
 (let ((k (fn-cl-key *clt-secret* (clt-octets *clt-t-id*) *clt-alice*)))
   (and (member-equal k (list (clt-octets "zz") k))
        (fn-ctl-some-key-opens-p
         (list (clt-octets "zz") k)
         (append (list (clt-octets "other"))
                 (list (fn-cl-lock *clt-secret* (clt-octets *clt-t-id*) *clt-alice*))
                 nil)))))
; Removal of the membership: bob's key alone does not open alice's lock.
(assert-event
 (not (fn-ctl-some-key-opens-p
       (list (fn-cl-key *clt-secret* (clt-octets *clt-t-id*) *clt-bob*))
       (list (fn-cl-lock *clt-secret* (clt-octets *clt-t-id*) *clt-alice*)))))
; Another secret (another node's) gives another key for the same login.
(assert-event
 (not (equal (fn-cl-key *clt-secret* (clt-octets *clt-t-id*) *clt-alice*)
             (fn-cl-key (make-list 32 :initial-element 8)
                        (clt-octets *clt-t-id*) *clt-alice*))))

; ---------------------------------------------------------------------------
; fn-cll-insert-adds-only-the-lines: the lock sits directly after the
; Injection-Info line (position 52 of *clt-t*), and taking it out gives the
; injected octets.
(assert-event
 (let* ((k (fn-cll-info-end *clt-t* 0 :start))
        (lines (fn-cll-line *fn-cll-lock-head*
                            (fn-cl-lock *clt-secret* (clt-octets *clt-t-id*) *clt-alice*))))
   (and (equal k (len (clt-crlf-join (list "Path: fn.test!not-for-mail"
                                           "Injection-Info: fn.test"))))
        (equal *clt-t-stored*
               (append (fn-cll-take k *clt-t*) lines (fn-cll-drop k *clt-t*)))
        (equal (append (fn-cll-take k *clt-t*)
                       (fn-cll-drop k (fn-cll-drop (len lines)
                                                   (append lines (fn-cll-drop k *clt-t*)))))
               (append (fn-cll-take k *clt-t*) (fn-cll-drop k (fn-cll-drop k *clt-t*))))
        (equal (append (fn-cll-take k *clt-t*) (fn-cll-drop k *clt-t*)) *clt-t*))))
; Removal of the Injection-Info line: octets this node did not inject get no
; lines, even from an authenticated login.
(defconst *clt-foreign*
  (clt-crlf-join (list "Path: elsewhere!not-for-mail" "From: x <x@example.invalid>"
                       "Newsgroups: local.general" "Subject: s"
                       "Message-ID: <f1@elsewhere>" "" "body")))
(assert-event
 (and (null (fn-cll-info-end *clt-foreign* 0 :start))
      (equal (fn-cl-served-payload *clt-secret* *clt-alice* (clt-octets "<f1@elsewhere>")
                                   *clt-foreign*)
             *clt-foreign*)))
; An Injection-Info in the body is not a header line.
(assert-event
 (null (fn-cll-info-end (clt-crlf-join (list "Path: x!y" "Subject: s" ""
                                             "Injection-Info: fn.test"))
                        0 :start)))

; fn-cl-served-payload-without-a-login-is-the-payload.
(assert-event
 (and (equal (fn-cl-served-payload *clt-secret* nil (clt-octets *clt-t-id*) *clt-t*)
             *clt-t*)
      (equal (fn-cl-served-payload (make-list 31 :initial-element 7) *clt-alice*
                                   (clt-octets *clt-t-id*) *clt-t*)
             *clt-t*)))

; A poster's own Cancel-Lock (tin) is kept and the node adds none.
(defconst *clt-t-tin*
  (clt-crlf-join (list "Path: fn.test!not-for-mail" "Injection-Info: fn.test"
                       "From: tin <tin@example.invalid>" "Newsgroups: local.general"
                       "Subject: mine" "Message-ID: <t3@fn.test>"
                       "Cancel-Lock: sha256:OWNLOCKOWNLOCKOWNLOCKOWNLOCKOWNLOCKOWNLOCK123="
                       "" "hello")))
(assert-event
 (equal (fn-cl-served-payload *clt-secret* *clt-alice* (clt-octets "<t3@fn.test>")
                              *clt-t-tin*)
        *clt-t-tin*))

; ---------------------------------------------------------------------------
; The visible view (fn-ctl-visible-articles, the owner refresh's definition):
; alice's cancel withdraws her post; bob's does not.
(defun clt-art (msgid groups payload)
  (fn-make-article msgid payload groups nil t nil))
(defconst *clt-a-t* (clt-art *clt-t-id* (list "local.general") *clt-t-stored*))
(defconst *clt-a-ca* (clt-art "<c1@fn.test>" (list "control.cancel") *clt-c-alice-stored*))
(defconst *clt-a-cb* (clt-art "<c2@fn.test>" (list "control.cancel") *clt-c-bob-stored*))
(assert-event
 (let* ((arts (list *clt-a-ca* *clt-a-t*))
        (ws (fn-ctl-articles-withdrawals arts nil nil nil)))
   (and (equal ws (list *clt-w-alice*))
        (equal (fn-ctl-visible-articles arts ws nil) (list *clt-a-ca*)))))
(assert-event
 (let* ((arts (list *clt-a-cb* *clt-a-t*))
        (ws (fn-ctl-articles-withdrawals arts nil nil nil)))
   (and (equal (len ws) 1)
        (equal (fn-ctl-visible-articles arts ws nil) arts))))

; ---------------------------------------------------------------------------
; fn-cl-served-payload-writes-one-login-lock: witness (alice's post: the
; secret, a login, no poster lock; the node's Injection-Info line present)
; and the conclusion in its stated form; then per hypothesis a removal.
(defun clt-one-lock-form (secret login msgid payload)
  (let ((fields (fn-ctl-received-fields payload))
        (k (fn-cll-info-end payload 0 :start)))
    (equal (fn-cl-served-payload secret login msgid payload)
           (if k
               (append (fn-cll-take k payload)
                       (fn-cll-line *fn-cll-lock-head* (fn-cl-lock secret msgid login))
                       (fn-cl-key-lines secret login fields)
                       (fn-cll-drop k payload))
             payload))))
(assert-event
 (and (fn-ns-secretp *clt-secret*) (consp *clt-alice*)
      (fn-cbor-octet-listp *clt-alice*)
      (not (consp (fn-ctl-fields-named *fn-ctl-cancel-lock-name*
                                       (fn-ctl-received-fields *clt-t*))))
      (fn-cll-info-end *clt-t* 0 :start)
      (clt-one-lock-form *clt-secret* *clt-alice* (clt-octets *clt-t-id*) *clt-t*)
      (not (equal *clt-t-stored* *clt-t*))))
; No secret: nothing written, the conclusion's lock is absent.
(assert-event
 (not (clt-one-lock-form (make-list 31 :initial-element 7) *clt-alice*
                         (clt-octets *clt-t-id*) *clt-t*)))
(must-fail
 (assert-event (clt-one-lock-form (make-list 31 :initial-element 7) *clt-alice*
                                  (clt-octets *clt-t-id*) *clt-t*)))
; No login.
(assert-event (not (clt-one-lock-form *clt-secret* nil (clt-octets *clt-t-id*) *clt-t*)))
(must-fail
 (assert-event (clt-one-lock-form *clt-secret* nil (clt-octets *clt-t-id*) *clt-t*)))
; The poster's own Cancel-Lock (tin): the node writes none.
(assert-event
 (not (clt-one-lock-form *clt-secret* *clt-alice* (clt-octets "<t3@fn.test>") *clt-t-tin*)))
(must-fail
 (assert-event
  (clt-one-lock-form *clt-secret* *clt-alice* (clt-octets "<t3@fn.test>") *clt-t-tin*)))

; fn-cl-login-key-opens-exactly-its-lock: alice's key opens alice's lock
; (the iff's two sides true); bob's does not (both sides false: his lock
; is another value).
(assert-event
 (and (fn-ctl-some-key-opens-p
       (list (fn-cl-key *clt-secret* (clt-octets *clt-t-id*) *clt-alice*))
       (list (fn-cl-lock *clt-secret* (clt-octets *clt-t-id*) *clt-alice*)))
      (not (fn-ctl-some-key-opens-p
            (list (fn-cl-key *clt-secret* (clt-octets *clt-t-id*) *clt-bob*))
            (list (fn-cl-lock *clt-secret* (clt-octets *clt-t-id*) *clt-alice*))))
      (not (equal (fn-cl-lock *clt-secret* (clt-octets *clt-t-id*) *clt-bob*)
                  (fn-cl-lock *clt-secret* (clt-octets *clt-t-id*) *clt-alice*)))))
; The Cancel-Lock key is the node secret's labelled use, not the bare HMAC.
(assert-event
 (not (equal (fn-cl-key *clt-secret* (clt-octets *clt-t-id*) *clt-alice*)
             (fn-stx-b64-encode
              (fn-ns-hmac-sha256 *clt-secret*
                                 (append (clt-octets *clt-t-id*) *clt-alice*))))))
