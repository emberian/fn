; Teeth for SEC-006 (PRF-210): own-post cancel by RFC 8315 Cancel-Lock keyed
; by the posting ACCOUNT under BLAKE3-derived purpose keys (books/cancel-lock.lisp,
; books/cancel-lock-lines.lisp, the :poster arm of books/control-authority.lisp).
; Per keystone a reachable witness asserting the complete antecedent and
; conclusion, and per hypothesis a removal witness (AGENTS.md, "Teeth ship
; with each keystone").  The articles are parsed by the article parser the
; served path uses, so the witnesses also check the step no theorem covers:
; the line the owner writes parses back as the entry the decision reads.
(in-package "ACL2")
(include-book "../../books/cancel-lock")
(include-book "../../books/control-visible")
(include-book "../../books/catalog-record")   ; fn-held-facts-of: the rows' facts
(include-book "must-fail-checked")

(defun clt-octets (s) (fn-record-string-octets s))
(defun clt-crlf-join (lines)
  (if (consp lines)
      (append (clt-octets (car lines)) (list 13 10) (clt-crlf-join (cdr lines)))
    nil))

; ---------------------------------------------------------------------------
; RFC 8315 section 5.2's example, the part every verifier computes: the key
; string "yM0ep490Fzt83CLYYAytm3S2HasHhYG4LAeAlmuSEys=" (Base64 of the
; example's K) locks as Base64(SHA-256(Base64(K))): the hash is over the
; Base64-ENCODED key (sections 2.1, 2.2).
(assert-event
 (equal (fn-ctl-lock-of-key (clt-octets "yM0ep490Fzt83CLYYAytm3S2HasHhYG4LAeAlmuSEys="))
        (clt-octets "NSBTz7BfcQFTCen+U4lQ0VS8VIlZao2b8mxD/xJaaeE=")))
; fn's own K (section 4's shape, the MAC keyed BLAKE3; only this node
; recomputes it): Base64(keyed_hash(SEC, "JaneDoe" || "<12345@mid.example>"))
; under a 32-octet SEC of 3s, and its lock, both the Rust blake3 crate's and
; Python hashlib's values, not this tree's.
(assert-event
 (let ((k (fn-cl-rfc8315-key (make-list 32 :initial-element 3) (clt-octets "JaneDoe")
                             (clt-octets "<12345@mid.example>"))))
   (and (equal k (clt-octets "AHgYG/bOZiCz1yKys8ePeJb1O5h+G11F3Zn5B721+uo="))
        (equal (fn-ctl-lock-of-key k)
               (clt-octets "y82iWYXdH6rE7tUMxXJ0wfVJW3DPrCHnxE54JD8utXY=")))))
; A lock of the RAW key would differ (the encoding is not optional).
(assert-event
 (not (equal (fn-stx-b64-encode
              (fn-sha256 (fn-ns-mac (make-list 32 :initial-element 3)
                                    (clt-octets "JaneDoe<12345@mid.example>"))))
             (clt-octets "y82iWYXdH6rE7tUMxXJ0wfVJW3DPrCHnxE54JD8utXY="))))

; ---------------------------------------------------------------------------
; Two accounts on one node (principal ids, 32 octets), one key ring: epoch 1,
; then epoch 2 after a rotation.
(defconst *clt-e1* (fn-ns-create-entry (clt-octets "fn.test") (make-list 32 :initial-element 7)))
(defconst *clt-e2* (fn-ns-rotate-entry *clt-e1* nil (make-list 32 :initial-element 9)))
(defconst *clt-secret* (list *clt-e1*))
(defconst *clt-ring2* (list *clt-e2* *clt-e1*))
(defconst *clt-alice* (make-list 32 :initial-element 1))
(defconst *clt-bob* (make-list 32 :initial-element 2))
(defconst *clt-t-id* "<t1@fn.test>")
(assert-event (and (fn-ns-ringp *clt-secret*) (fn-ns-ringp *clt-ring2*)))
; The uid is the account's lowercase hex: no angle brackets (section 4).
(assert-event (and (equal (len (fn-cl-uid *clt-alice*)) 64)
                   (not (member 60 (fn-cl-uid *clt-alice*)))
                   (not (member 62 (fn-cl-uid *clt-alice*)))))

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
; alice's lock for its Message-ID; each cancel's one key is its account's
; key for the target; the cancel also gets its own lock.
(assert-event
 (equal (fn-ctl-locks-octets *clt-t-stored*)
        (list (fn-cl-lock *clt-e1* *clt-alice* (clt-octets *clt-t-id*)))))
(assert-event
 (equal (fn-ctl-keys-octets *clt-c-alice-stored*)
        (list (fn-cl-key *clt-e1* *clt-alice* (clt-octets *clt-t-id*)))))
(assert-event
 (equal (fn-ctl-keys-octets *clt-c-bob-stored*)
        (list (fn-cl-key *clt-e1* *clt-bob* (clt-octets *clt-t-id*)))))
(assert-event
 (equal (fn-ctl-locks-octets *clt-c-alice-stored*)
        (list (fn-cl-lock *clt-e1* *clt-alice* (clt-octets "<c1@fn.test>")))))
(assert-event (equal (fn-ctl-target-octets *clt-c-alice-stored*) *clt-t-id*))
(assert-event (null (fn-ctl-keys-octets *clt-t-stored*)))
; The lock is the FIRST header line, in front of the block.
(assert-event
 (equal (take 20 *clt-t-stored*) (clt-octets "Cancel-Lock: sha256:")))

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
      (equal (fn-ctl-withdrawal-effect
              (fn-ctl-w-with-tlocks *clt-w-alice* (fn-ctl-locks-octets *clt-t-stored*))
              (list "local.general") nil nil)
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
      (equal (fn-ctl-withdrawal-effect
              (fn-ctl-w-with-tlocks *clt-w-bob* (fn-ctl-locks-octets *clt-t-stored*))
              (list "local.general") nil nil)
             (list :decline :no-lock-match))))

; Removal of the lock: the same key against the article as injected, with no
; lock (a post made before SEC-006, or unauthenticated).
(assert-event
 (and (null (fn-ctl-locks-octets *clt-t*))
      (equal (fn-ctl-withdrawal-effect
              (fn-ctl-w-with-tlocks *clt-w-alice* (fn-ctl-locks-octets *clt-t*))
              (list "local.general") nil nil)
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
(must-fail-checked
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
; The visible view (fn-ctl-visible-articles, the owner refresh's definition):
; alice's cancel withdraws her post; bob's does not.
; After the records flip an archive article holds a HANDLE; the control
; facts are its row's in the Store's history (flip-L8-2).  A row of stored
; BYTES at sequence (and handle) SEQ.
(defun clt-art (msgid groups handle)
  (fn-make-article msgid handle groups nil t nil))
(defun clt-row (seq msgid groups bytes)
  (fn-held-make seq seq 1 msgid seq groups "a" "s" "e" 2 :legacy
                (fn-held-facts-of bytes)
                (fn-hc-make (fn-stx-make-verdict :absent nil 0) nil 0) nil nil))
(defconst *clt-a-t* (clt-art *clt-t-id* (list "local.general") 0))
(defconst *clt-a-ca* (clt-art "<c1@fn.test>" (list "control.cancel") 1))
(defconst *clt-a-cb* (clt-art "<c2@fn.test>" (list "control.cancel") 2))
(defconst *clt-hist*
  (list (clt-row 0 *clt-t-id* (list "local.general") *clt-t-stored*)
        (clt-row 1 "<c1@fn.test>" (list "control.cancel") *clt-c-alice-stored*)
        (clt-row 2 "<c2@fn.test>" (list "control.cancel") *clt-c-bob-stored*)))
(assert-event
 (let* ((arts (list *clt-a-ca* *clt-a-t*))
        (ws (fn-ctl-articles-withdrawals arts nil *clt-hist* nil)))
   (and (equal ws (list (fn-ctl-w-with-tlocks *clt-w-alice*
                                              (fn-ctl-locks-octets *clt-t-stored*))))
        (equal (fn-ctl-visible-articles arts ws nil) (list *clt-a-ca*)))))
(assert-event
 (let* ((arts (list *clt-a-cb* *clt-a-t*))
        (ws (fn-ctl-articles-withdrawals arts nil *clt-hist* nil)))
   (and (equal (len ws) 1)
        (equal (fn-ctl-visible-articles arts ws nil) arts))))

; ---------------------------------------------------------------------------
; fn-cl-served-payload-writes-one-account-lock: witness (alice's post: a
; ring, an account, unsigned, no poster lock) with the conclusion in its
; stated form; then per hypothesis a removal: the payload is then stored as
; injected (a positive check of the retained hypotheses, the omitted one
; false, the conclusion false).
(defun clt-one-lock-form (ring account msgid payload)
  (let ((fields (fn-ctl-received-fields payload)))
    (append (fn-cll-line *fn-cll-lock-head*
                         (fn-cl-lock (fn-ns-current ring) account msgid))
            (if (consp (fn-cl-key-values ring account fields))
                (fn-cll-key-line (fn-cl-key-values ring account fields))
              nil)
            payload)))
(assert-event
 (let ((fields (fn-ctl-received-fields *clt-t*)))
   (and (fn-cl-lock-wanted-p *clt-secret* *clt-alice* fields)
        (equal (fn-cl-served-payload *clt-secret* *clt-alice* (clt-octets *clt-t-id*) *clt-t*)
               (clt-one-lock-form *clt-secret* *clt-alice* (clt-octets *clt-t-id*) *clt-t*)))))
; Removal of the ring.
(assert-event
 (and (fn-cl-accountp *clt-alice*) (not (fn-ns-ringp nil))
      (equal (fn-cl-served-payload nil *clt-alice* (clt-octets *clt-t-id*) *clt-t*) *clt-t*)
      (not (equal *clt-t* (clt-one-lock-form *clt-secret* *clt-alice*
                                             (clt-octets *clt-t-id*) *clt-t*)))))
; Removal of the account (an unauthenticated POST).
(assert-event
 (and (fn-ns-ringp *clt-secret*) (not (fn-cl-accountp nil))
      (equal (fn-cl-served-payload *clt-secret* nil (clt-octets *clt-t-id*) *clt-t*) *clt-t*)))
; Removal of "no poster Cancel-Lock": tin's article keeps its own lock and
; gets none from the node (the poster's field is user input, never rewritten).
(defconst *clt-t-tin*
  (clt-crlf-join (list "Path: fn.test!not-for-mail" "Injection-Info: fn.test"
                       "From: alice <alice@example.invalid>"
                       "Newsgroups: local.general" "Subject: tin"
                       "Cancel-Lock: sha256:tinlocktinlocktinlocktinlocktinlocktinlock0="
                       "Message-ID: <t3@fn.test>" "" "hello")))
(assert-event
 (and (fn-ns-ringp *clt-secret*) (fn-cl-accountp *clt-alice*)
      (not (fn-cl-lock-wanted-p *clt-secret* *clt-alice* (fn-ctl-received-fields *clt-t-tin*)))
      (equal (fn-cl-served-payload *clt-secret* *clt-alice* (clt-octets "<t3@fn.test>")
                                   *clt-t-tin*)
             *clt-t-tin*)
      (equal (fn-ctl-locks-octets *clt-t-tin*)
             (list (clt-octets "tinlocktinlocktinlocktinlocktinlocktinlock0=")))))
; Removal of "unsigned": a signed article (an FN-Authorship carrier) gets
; neither a lock nor a key: its signed bytes are never edited.
(defconst *clt-t-signed*
  (clt-crlf-join (list "Path: fn.test!not-for-mail" "Injection-Info: fn.test"
                       "From: alice <alice@example.invalid>"
                       "Newsgroups: local.general" "Subject: signed"
                       "FN-Authorship: v1 x"
                       "Message-ID: <t4@fn.test>" "" "hello")))
(assert-event
 (and (fn-ns-ringp *clt-secret*) (fn-cl-accountp *clt-alice*)
      (not (fn-cl-unsigned-p (fn-ctl-received-fields *clt-t-signed*)))
      (equal (fn-cl-served-payload *clt-secret* *clt-alice* (clt-octets "<t4@fn.test>")
                                   *clt-t-signed*)
             *clt-t-signed*)))

; ---------------------------------------------------------------------------
; fn-cl-served-payload-projects-to-the-injected-octets (D25): witness (the
; payload opens with its block, not "C"); the projection of what alice and
; bob store for the same source is the injected octets, though the stored
; octets differ (their locks differ).
(defconst *clt-t-stored-bob*
  (fn-cl-served-payload *clt-secret* *clt-bob* (clt-octets *clt-t-id*) *clt-t*))
(defconst *clt-t-stored-e2*
  (fn-cl-served-payload *clt-ring2* *clt-alice* (clt-octets *clt-t-id*) *clt-t*))
(assert-event
 (and (not (equal (car *clt-t*) 67))
      (not (equal *clt-t-stored* *clt-t-stored-bob*))
      (not (equal *clt-t-stored* *clt-t-stored-e2*))
      (equal (fn-cll-skip *clt-t-stored*) *clt-t*)
      (equal (fn-cll-skip *clt-t-stored-bob*) *clt-t*)
      (equal (fn-cll-skip *clt-t-stored-e2*) *clt-t*)
      (equal (fn-cll-skip *clt-c-alice-stored*) *clt-c-alice*)))
; Removal: a payload that itself opens with a Cancel-Lock line (no
; injection does) loses that line to the projection.
(assert-event
 (let ((x (append (clt-octets "Cancel-Lock: sha256:x") '(13 10) *clt-t*)))
   (and (equal (car x) 67)
        (not (equal (fn-cll-skip (fn-cl-served-payload *clt-secret* *clt-alice*
                                                       (clt-octets *clt-t-id*) x))
                    x)))))

; ---------------------------------------------------------------------------
; fn-cl-ring-keys-open-every-retained-lock (rotation): alice's post locked
; under epoch 1; after the rotation her cancel carries one key per retained
; epoch (2 then 1), and one of them opens the old lock.
(defconst *clt-c-alice-e2-stored*
  (fn-cl-served-payload *clt-ring2* *clt-alice* (clt-octets "<c5@fn.test>")
                        (clt-cancel "<c5@fn.test>")))
(assert-event
 (let ((keys (fn-ctl-keys-octets *clt-c-alice-e2-stored*))
       (locks (fn-ctl-locks-octets *clt-t-stored*)))
   (and (member-equal *clt-e1* *clt-ring2*)
        (fn-ctl-lock-memberp (fn-cl-lock *clt-e1* *clt-alice* (clt-octets *clt-t-id*)) locks)
        (equal keys (fn-cl-ring-keys *clt-ring2* *clt-alice* (clt-octets *clt-t-id*)))
        (equal (len keys) 2)
        (fn-ctl-some-key-opens-p keys locks))))
; Removal of "retained": a ring that dropped epoch 1 has no key for it.
(assert-event
 (let ((locks (fn-ctl-locks-octets *clt-t-stored*)))
   (and (not (member-equal *clt-e1* (list *clt-e2*)))
        (not (fn-ctl-some-key-opens-p (fn-cl-ring-keys (list *clt-e2*) *clt-alice*
                                                       (clt-octets *clt-t-id*))
                                      locks)))))
; Removal of "the lock is the entry's lock for this account": bob's keys over
; the same ring open nothing.
(assert-event
 (not (fn-ctl-some-key-opens-p (fn-cl-ring-keys *clt-ring2* *clt-bob* (clt-octets *clt-t-id*))
                               (fn-ctl-locks-octets *clt-t-stored*))))

; ---------------------------------------------------------------------------
; fn-cl-account-key-opens-exactly-its-lock: alice's key opens alice's lock
; (the equality holds); bob's does not (the equality fails): the retrying
; account's cancel is refused.
(assert-event
 (and (fn-ctl-some-key-opens-p
       (list (fn-cl-key *clt-e1* *clt-alice* (clt-octets *clt-t-id*)))
       (list (fn-cl-lock *clt-e1* *clt-alice* (clt-octets *clt-t-id*))))
      (not (fn-ctl-some-key-opens-p
            (list (fn-cl-key *clt-e1* *clt-bob* (clt-octets *clt-t-id*)))
            (list (fn-cl-lock *clt-e1* *clt-alice* (clt-octets *clt-t-id*)))))
      (not (equal (fn-cl-lock *clt-e1* *clt-bob* (clt-octets *clt-t-id*))
                  (fn-cl-lock *clt-e1* *clt-alice* (clt-octets *clt-t-id*))))))
; The key is RFC 8315's shape over the purpose key, not a bare MAC under the root.
(assert-event
 (not (equal (fn-cl-key *clt-e1* *clt-alice* (clt-octets *clt-t-id*))
             (fn-stx-b64-encode
              (fn-ns-mac (fn-ns-entry-root *clt-e1*)
                                 (append (fn-cl-uid *clt-alice*) (clt-octets *clt-t-id*)))))))

; books/control-authority.lisp fn-ctl-control-of-fields (PRF-210; no
; hypothesis; keystone-audit 2026-09-27: it had no witness).  The one-pass
; control fact the catalog row carries (books/catalog-record.lisp) is the
; three separate parses, on the stored cancel (a target, one key, one lock:
; every field non-empty) and on the stored target (no target, no key).
(assert-event
 (let ((c (fn-ctl-control-of *clt-c-alice-stored*)))
   (and (equal (fn-ctl-control-target c) *clt-t-id*)
        (equal (fn-ctl-control-target c) (fn-ctl-target-octets *clt-c-alice-stored*))
        (consp (fn-ctl-control-keys c))
        (equal (fn-ctl-control-keys c) (fn-ctl-keys-octets *clt-c-alice-stored*))
        (consp (fn-ctl-control-locks c))
        (equal (fn-ctl-control-locks c) (fn-ctl-locks-octets *clt-c-alice-stored*)))))
(assert-event
 (let ((c (fn-ctl-control-of *clt-t-stored*)))
   (and (equal (fn-ctl-control-target c) (fn-ctl-target-octets *clt-t-stored*))
        (null (fn-ctl-control-keys c))
        (equal (fn-ctl-control-keys c) (fn-ctl-keys-octets *clt-t-stored*))
        (consp (fn-ctl-control-locks c))
        (equal (fn-ctl-control-locks c) (fn-ctl-locks-octets *clt-t-stored*)))))
