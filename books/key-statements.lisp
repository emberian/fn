; fn: key statements -- succession and revocation executed by the owner at
; acceptance (PRF-098; planning/evidence/spike-peering-2026-09-25.md,
; theorems 2 and 3; the spike's reader-side poller, spike/mega's tools/fn_peering.py (it does not exist on dev)
; keys-process is what this replaces).
;
; A key statement is an ordinary signed article in a group the operator's
; authorities rows grant the verb "keys" over (fn.keys by convention).  Its
; authored source's body carries the statement:
;
;   (body lines of the authored source; a long value spans several lines of
;   the same name, concatenated)
;   FN-Key-Statement: succession-v1 | revocation-v1
;   FN-Key-Principal: HEX64                 the principal the statement is about
;   FN-Key-Old-Ed25519: HEX64               succession: the key it retires
;   FN-Key-New-Ed25519: HEX64               succession: the new key pair
;   FN-Key-New-ML-DSA-65: HEX3904
;   FN-Key-PoP-Ed25519: HEX128              succession: the proof of possession,
;   FN-Key-PoP-ML-DSA-65: HEX6618           a hybrid signature by the NEW keys
;
; The proof of possession is the D09 hybrid signature (books/hybrid-signature
; fn-hsig-authorize) of the principal under the NEW key set over
; `fn-ks-pop-source': a domain tag, the statement's own Message-ID and the old
; Ed25519 key.  So a PoP binds the new keys to exactly one statement: it does
; not verify over another Message-ID.
;
; The decision is C2's shape (books/control-authority.lisp fn-ctl-authorize):
; the statement's STORED verdict is :verified here, and a grant of the verb
; "keys" covers every group the statement names.  Then: the statement names
; the verified principal; the verdict's keyring generation is that
; principal's current enrollment (so a superseded or replayed statement
; declines); for a succession the old key is that enrollment's Ed25519 key,
; the new key set differs from it, and the PoP's two primitive observations
; (made by the host over the preimage ACL2 names) verified.  The resulting
; kind-3 event is fn-hl-enroll-event / fn-hl-revoke-event at
; fn-hl-next-generation: the generation is ACL2's.
;
; Host: host/owner-host.lisp fn-owner-key-statement-request and
; fn-owner-key-statement-event, called by host/native/owner.lisp
; fnn-owner-key-statement after the statement's kind-4 commit.
;
; Prefix `fn-ks-' (docs/prefixes.md).
(in-package "ACL2")
(include-book "control-authority")
(include-book "peer-authored-accept")

(defconst *fn-ks-verb* "keys")

(defconst *fn-ks-statement-name*   ; FN-Key-Statement:
  '(70 78 45 75 101 121 45 83 116 97 116 101 109 101 110 116 58 32))
(defconst *fn-ks-principal-name*   ; FN-Key-Principal:
  '(70 78 45 75 101 121 45 80 114 105 110 99 105 112 97 108 58 32))
(defconst *fn-ks-old-ed-name*   ; FN-Key-Old-Ed25519:
  '(70 78 45 75 101 121 45 79 108 100 45 69 100 50 53 53 49 57 58 32))
(defconst *fn-ks-new-ed-name*   ; FN-Key-New-Ed25519:
  '(70 78 45 75 101 121 45 78 101 119 45 69 100 50 53 53 49 57 58 32))
(defconst *fn-ks-new-ml-name*   ; FN-Key-New-ML-DSA-65:
  '(70 78 45 75 101 121 45 78 101 119 45 77 76 45 68 83 65 45 54 53 58 32))
(defconst *fn-ks-pop-ed-name*   ; FN-Key-PoP-Ed25519:
  '(70 78 45 75 101 121 45 80 111 80 45 69 100 50 53 53 49 57 58 32))
(defconst *fn-ks-pop-ml-name*   ; FN-Key-PoP-ML-DSA-65:
  '(70 78 45 75 101 121 45 80 111 80 45 77 76 45 68 83 65 45 54 53 58 32))
(defconst *fn-ks-succession-v1*    ; succession-v1
  '(115 117 99 99 101 115 115 105 111 110 45 118 49))
(defconst *fn-ks-revocation-v1*    ; revocation-v1
  '(114 101 118 111 99 97 116 105 111 110 45 118 49))
(defconst *fn-ks-pop-tag*          ; fn-key-succession-pop-v1
  '(102 110 45 107 101 121 45 115 117 99 99 101 115 115 105 111 110 45 112
    111 112 45 118 49))

; -----------------------------------------------------------------------------
; Field values.  The statement is in the authored source's BODY, one line
; per field, `Name: value' with the exact spelling above; a long value is
; split over several lines of the same name, concatenated in order (a line
; is at most 998 octets, and the carrier holds the source's header in a
; bounded header field, so the key material cannot live in the header).
; Hex is lowercase.

(defun fn-ks-prefix-rest (prefix line)
  (declare (xargs :guard t))
  (if (consp prefix)
      (if (and (consp line) (equal (car line) (car prefix)))
          (fn-ks-prefix-rest (cdr prefix) (cdr line))
        :no)
    line))

; The body's lines, split at LF, a CR before it dropped; LINE is the current
; line reversed.
(defun fn-ks-lines (octets line)
  (declare (xargs :guard (true-listp line)))
  (if (consp octets)
      (if (equal (car octets) 10)
          (cons (reverse (if (and (consp line) (equal (car line) 13))
                             (cdr line) line))
                (fn-ks-lines (cdr octets) nil))
        (fn-ks-lines (cdr octets) (cons (car octets) line)))
    (if (consp line) (list (reverse line)) nil)))

; The concatenated values of the lines named PREFIX, and whether any was.
(defun fn-ks-values (prefix lines)
  (declare (xargs :guard t))
  (if (consp lines)
      (let ((rest (fn-ks-prefix-rest prefix (car lines)))
            (more (fn-ks-values prefix (cdr lines))))
        (if (equal rest :no) more
          (cons t (append (if (true-listp rest) rest nil) (cdr more)))))
    (cons nil nil)))

(defun fn-ks-field (lines prefix)
  (declare (xargs :guard t))
  (let ((v (fn-ks-values prefix lines)))
    (if (car v) (cdr v) nil)))

(defun fn-ks-unhex-exact (octets n)
  (declare (xargs :guard (natp n)))
  (if (and (fn-id-hex-listp octets) (equal (len octets) (* 2 n)))
      (fn-id-unhex octets)
    nil))

; (:succession principal old-ed new-keys pop-signatures), (:revocation
; principal), or nil (not a statement, or a malformed one).
(defun fn-ks-statement (source)
  (declare (xargs :guard t))
  (let ((parsed (fn-article-parse source)))
    (if (not (fn-article-result-okp parsed)) nil
      (let* ((article (fn-article-result-article parsed))
             (lines (fn-ks-lines (and (true-listp article)
                                      (fn-article-body article))
                                 nil))
             (kind (fn-ks-field lines *fn-ks-statement-name*))
             (principal (fn-ks-unhex-exact
                         (fn-ks-field lines *fn-ks-principal-name*) 32)))
        (cond
         ((not (fn-hsig-exact-octets-p principal 32)) nil)
         ((equal kind *fn-ks-revocation-v1*) (list :revocation principal))
         ((equal kind *fn-ks-succession-v1*)
          (let ((old-ed (fn-ks-unhex-exact
                         (fn-ks-field lines *fn-ks-old-ed-name*) 32))
                (new-ed (fn-ks-unhex-exact
                         (fn-ks-field lines *fn-ks-new-ed-name*) 32))
                (new-ml (fn-ks-unhex-exact
                         (fn-ks-field lines *fn-ks-new-ml-name*) 1952))
                (pop-ed (fn-ks-unhex-exact
                         (fn-ks-field lines *fn-ks-pop-ed-name*) 64))
                (pop-ml (fn-ks-unhex-exact
                         (fn-ks-field lines *fn-ks-pop-ml-name*) 3309)))
            (if (and (fn-hsig-exact-octets-p old-ed 32)
                     (fn-hsig-exact-octets-p new-ed 32)
                     (fn-hsig-exact-octets-p new-ml 1952)
                     (fn-hsig-exact-octets-p pop-ed 64)
                     (fn-hsig-exact-octets-p pop-ml 3309))
                (list :succession principal old-ed
                      (list (cons :ed25519 new-ed) (cons :ml-dsa-65 new-ml))
                      (list (cons :ed25519 pop-ed) (cons :ml-dsa-65 pop-ml)))
              nil)))
         (t nil))))))

; The octets the proof of possession signs (as the authored source of a D09
; hybrid signature by the principal under the NEW keys): the tag, LF, the
; statement's Message-ID, LF, the old Ed25519 key.  The tag line keeps it
; from ever parsing as an article.
(defun fn-ks-pop-source (msgid old-ed)
  (declare (xargs :guard t))
  (append *fn-ks-pop-tag* (list 10)
          (fn-record-string-octets msgid) (list 10)
          (if (true-listp old-ed) old-ed nil)))

; -----------------------------------------------------------------------------
; The statement composite: the kind-4 event the owner committed.  Its stored
; verdict, as the reader pin would hold it, and its Message-ID.

(defun fn-ks-evidence (event)
  (declare (xargs :guard t))
  (let ((decoded (fn-stxe-decode-exact (fn-stxa-verdict-event event))))
    (if (and (fn-stxa-p event) (fn-stmt-okp decoded)
             (fn-stxe-p (fn-stmt-value decoded)))
        (fn-stmt-value decoded)
      nil)))

(defun fn-ks-verdict (event)
  (declare (xargs :guard t))
  (let ((e (fn-ks-evidence event)))
    (if e
        (fn-stx-make-verdict (fn-stxe-token e) (fn-stxe-detail e)
                             (fn-stxe-keyring-generation e))
      nil)))

(defun fn-ks-msgid (event)
  (declare (xargs :guard t))
  (let ((e (fn-ks-evidence event)))
    (if e (fn-stxe-msgid e) nil)))

(defun fn-ks-source (event)
  (declare (xargs :guard t))
  (if (fn-stxa-p event) (fn-stxa-authored-source event) nil))

; The primitive request the host serves before the decision: for a
; succession, (principal new-keys pop-source pop-signatures), the D09
; subject the host computes the preimage of (fn-hsig-host-preimage) and
; observes; nil otherwise (no observation is taken).
(defun fn-ks-pop-request (event)
  (declare (xargs :guard t))
  (let ((statement (fn-ks-statement (fn-ks-source event))))
    (if (and (consp statement) (eq (car statement) :succession))
        (list (nth 1 statement) (nth 3 statement)
              (fn-ks-pop-source (fn-ks-msgid event) (nth 2 statement))
              (nth 4 statement))
      nil)))

; -----------------------------------------------------------------------------
; The decision.  nil: not a key statement (nothing to do).  (:decline
; REASON): a statement that does not act.  (:enroll principal new-keys) or
; (:revoke principal): the keyring change it asks for.

(defun fn-ks-plan (event snapshots rows observed-ml-key ed-observation
                         ml-observation)
  (declare (xargs :guard t))
  (let ((statement (fn-ks-statement (fn-ks-source event))))
    (if (not (consp statement)) nil
      (let* ((verdict (fn-ks-verdict event))
             (fields (fn-hsig-authored-source-fields (fn-ks-source event)))
             (authorized (fn-ctl-authorize verdict *fn-ks-verb*
                                           (cadr fields) rows))
             (principal (nth 1 statement))
             (enrolled (fn-hl-current-enrollment
                        (fn-stx-verdict-generation verdict) snapshots)))
        (cond
         ((not (equal (car authorized) :execute))
          (list :decline (if (consp (cdr authorized)) (cadr authorized)
                           :unauthorized)))
         ((not (equal (fn-stx-verdict-detail verdict) principal))
          (list :decline :another-principal))
         ((not (and (consp enrolled) (equal (cadr enrolled) principal)))
          (list :decline :not-current))
         ((eq (car statement) :revocation) (list :revoke principal))
         (t
          (let ((old-ed (nth 2 statement))
                (new-keys (nth 3 statement))
                (old-keys (caddr enrolled)))
            (cond
             ((not (and (consp old-keys) (consp (car old-keys))
                        (equal old-ed (cdr (car old-keys)))))
              (list :decline :old-key))
             ((equal new-keys old-keys) (list :decline :same-keys))
             ((not (fn-hsig-authorize principal new-keys
                                      (fn-ks-pop-source (fn-ks-msgid event)
                                                        old-ed)
                                      (nth 4 statement) observed-ml-key
                                      ed-observation ml-observation))
              (list :decline :proof-of-possession))
             (t (list :enroll principal new-keys))))))))))

; The kind-3 event the owner commits, or nil.
(defun fn-ks-event (plan sequence txid store-generation snapshots)
  (declare (xargs :guard t))
  (cond ((and (true-listp plan) (consp plan) (eq (car plan) :enroll))
         (fn-hl-enroll-event sequence txid store-generation
                             (fn-hl-next-generation snapshots)
                             (nth 1 plan) (nth 2 plan) snapshots))
        ((and (true-listp plan) (consp plan) (eq (car plan) :revoke))
         (fn-hl-revoke-event sequence txid store-generation
                             (fn-hl-next-generation snapshots)
                             (nth 1 plan) snapshots))
        (t nil)))

(defun fn-ks-execute (event snapshots rows observed-ml-key ed-observation
                            ml-observation sequence txid store-generation)
  (declare (xargs :guard t))
  (fn-ks-event (fn-ks-plan event snapshots rows observed-ml-key ed-observation
                           ml-observation)
               sequence txid store-generation snapshots))

; -----------------------------------------------------------------------------
; Keystones.  Subject: fn-ks-plan and fn-ks-execute, which
; host/owner-host.lisp fn-owner-key-statement-event calls.

(defthm fn-ks-authorize-is-execute-or-decline
  (let ((a (fn-ctl-authorize verdict verb groups rows)))
    (or (equal (car a) :execute) (equal (car a) :decline)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ctl-authorize))))

(defthm fn-ks-plan-shape
  (let ((plan (fn-ks-plan event snapshots rows observed ed ml)))
    (or (null plan)
        (equal (car plan) :decline)
        (equal (car plan) :enroll)
        (equal (car plan) :revoke)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ctl-authorize)
                                  (fn-ks-statement fn-ks-verdict
                                   fn-hsig-authored-source-fields
                                   fn-hl-current-enrollment fn-hsig-authorize
                                   fn-ctl-grant-scope fn-ctl-covers-every-p
                                   fn-ctl-verified-principal)))))

; KEYSTONE (C2 shape).  A statement acts only on its own stored :verified
; verdict naming the principal it is about, and only when a grant of "keys"
; covers every group it names.  So a :carried, :revoked, :unverified or
; :absent statement never changes a keyring: carrying is not authority.
(defthm fn-ks-plan-acts-only-on-a-verified-granted-statement
  (let ((plan (fn-ks-plan event snapshots rows observed ed ml))
        (verdict (fn-ks-verdict event))
        (groups (cadr (fn-hsig-authored-source-fields (fn-ks-source event)))))
    (implies (or (equal (car plan) :enroll) (equal (car plan) :revoke))
             (and (equal (fn-stx-verdict-token verdict) :verified)
                  (equal (car (fn-ctl-authorize verdict *fn-ks-verb* groups
                                                rows))
                         :execute)
                  (equal (fn-stx-verdict-detail verdict) (nth 1 plan))
                  (equal (nth 1 plan)
                         (nth 1 (fn-ks-statement (fn-ks-source event)))))))
  :hints (("Goal" :in-theory (e/d ()
                                  (fn-ks-statement fn-ks-verdict fn-ctl-authorize
                                   fn-hsig-authored-source-fields fn-ks-source
                                   fn-stxa-p
                                   fn-hl-current-enrollment fn-hsig-authorize))
           :use ((:instance fn-ks-authorize-is-execute-or-decline
                            (verdict (fn-ks-verdict event))
                            (verb *fn-ks-verb*)
                            (groups (cadr (fn-hsig-authored-source-fields
                                           (fn-ks-source event)))))
                 (:instance fn-ctl-authorize-requires-verified-verdict
                            (verdict (fn-ks-verdict event))
                            (verb *fn-ks-verb*)
                            (groups (cadr (fn-hsig-authored-source-fields
                                           (fn-ks-source event)))))))))

(defthm fn-ks-execute-needs-an-acting-plan
  (implies (fn-ks-execute event snapshots rows observed ed ml
                          sequence txid store-generation)
           (let ((plan (fn-ks-plan event snapshots rows observed ed ml)))
             (or (equal (car plan) :enroll) (equal (car plan) :revoke))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ks-execute fn-ks-event)
                                  (fn-ks-plan fn-hl-enroll-event
                                   fn-hl-revoke-event)))))

(defthm fn-ks-carried-or-revoked-statement-never-changes-a-keyring
  (implies (not (equal (fn-stx-verdict-token (fn-ks-verdict event)) :verified))
           (equal (fn-ks-execute event snapshots rows observed ed ml
                                 sequence txid store-generation)
                  nil))
  :hints (("Goal" :in-theory (disable fn-ks-execute fn-ks-plan fn-ks-verdict)
           :use (fn-ks-execute-needs-an-acting-plan
                 fn-ks-plan-acts-only-on-a-verified-granted-statement))))

; KEYSTONE (theorem 2, the old key was current).  A statement acts only when
; the keyring generation its :verified verdict was made under is its
; principal's current enrollment; a succession's old key is that
; enrollment's Ed25519 key and its new key set differs from it.
(defthm fn-ks-plan-old-key-was-the-current-enrollment
  (let* ((plan (fn-ks-plan event snapshots rows observed ed ml))
         (enrolled (fn-hl-current-enrollment
                    (fn-stx-verdict-generation (fn-ks-verdict event))
                    snapshots))
         (statement (fn-ks-statement (fn-ks-source event))))
    (implies (or (equal (car plan) :enroll) (equal (car plan) :revoke))
             (and (consp enrolled)
                  (equal (cadr enrolled) (nth 1 plan))
                  (implies (equal (car plan) :enroll)
                           (and (equal (nth 2 statement)
                                       (cdr (car (caddr enrolled))))
                                (equal (nth 2 plan) (nth 3 statement))
                                (not (equal (nth 2 plan)
                                            (caddr enrolled))))))))
  :hints (("Goal" :in-theory (disable fn-ks-statement fn-ks-verdict
                                      fn-ctl-authorize fn-ks-source fn-stxa-p
                                      fn-hsig-authored-source-fields
                                      fn-hl-current-enrollment
                                      fn-hsig-authorize))))

; KEYSTONE (the PoP binds the new keys to the statement by Message-ID).  A
; succession acts only when both primitive observations verified a D09
; signature of its principal under the NEW key set over fn-ks-pop-source of
; THIS statement's Message-ID and old key.
(defthm fn-ks-plan-pop-binds-the-new-keys-to-the-statement
  (let ((plan (fn-ks-plan event snapshots rows observed ed ml))
        (statement (fn-ks-statement (fn-ks-source event))))
    (implies (equal (car plan) :enroll)
             (and (fn-hsig-authorize (nth 1 plan) (nth 2 plan)
                                     (fn-ks-pop-source (fn-ks-msgid event)
                                                       (nth 2 statement))
                                     (nth 4 statement) observed ed ml)
                  (equal ed :verified)
                  (equal ml :verified))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-hsig-authorize)
                                  (fn-ks-statement fn-ks-verdict
                                   fn-ctl-authorize fn-ks-source fn-stxa-p
                                   fn-hsig-authored-source-fields
                                   fn-hl-current-enrollment
                                   fn-hsig-subject-p fn-hsig-signatures-p
                                   fn-ks-pop-source fn-ks-msgid)))))

;; The two succession facts over the event constructor, for any plan.
(defthm fn-ks-event-of-an-enrollment-is-selected
  (let ((ev (fn-ks-event plan sequence txid store-generation snapshots)))
    (implies (and ev (equal (car plan) :enroll))
             (equal (fn-hl-current-enrollment (fn-hl-next-generation snapshots)
                                              (cons ev snapshots))
                    (list ev (nth 1 plan) (nth 2 plan)))))
  :hints (("Goal" :in-theory (e/d (fn-ks-event fn-hl-current-enrollment
                                   fn-stxk-find)
                                  (fn-hl-enroll-event
                                   fn-hsig-keyring-snapshot-value
                                   fn-hl-snapshot-principal fn-stxk-p
                                   fn-hl-next-generation))
           :use ((:instance fn-hl-enroll-event-enrolls-its-keys
                            (keyring-generation (fn-hl-next-generation snapshots))
                            (principal (nth 1 plan))
                            (keys (nth 2 plan)))))))

(defthm fn-ks-event-of-an-enrollment-refuses-other-keys
  (let ((ev (fn-ks-event plan sequence txid store-generation snapshots))
        (form (fn-pa-carrier-form received)))
    (implies (and ev (equal (car plan) :enroll)
                  (equal (car form) :ok)
                  (equal (nth 2 form) (nth 1 plan))
                  (not (equal (nth 3 form) (nth 2 plan))))
             (equal (fn-pa-current-plan received (cons ev snapshots)
                                        carried transitp)
                    (list :refused :local-enrollment))))
  :hints (("Goal" :in-theory (e/d (fn-ks-event fn-pa-current-plan
                                   fn-pa-revoked-tombstonep
                                   fn-hl-current-enrollment fn-stxk-find)
                                  (fn-hl-enroll-event
                                   fn-hsig-keyring-snapshot-value
                                   fn-hl-snapshot-principal fn-stxk-p
                                   fn-pa-carrier-form fn-pa-carriesp
                                   fn-hsig-enrolled-keys-of-principalp
                                   fn-hl-next-generation))
           :use ((:instance fn-hl-enroll-event-enrolls-its-keys
                            (keyring-generation (fn-hl-next-generation snapshots))
                            (principal (nth 1 plan))
                            (keys (nth 2 plan)))
                 (:instance fn-hsig-keyring-snapshot-value-requires-the-key-profile
                            (snapshot (fn-ks-event plan sequence txid
                                                   store-generation snapshots)))))))

; KEYSTONE (theorem 2, the new keys are selected).  The succession's kind-3
; event, once it is the newest snapshot, is what fn-hl-current-enrollment
; selects at the next generation: the principal with the new key set.
(defthm fn-ks-succession-selects-the-new-keys
  (let ((plan (fn-ks-plan event snapshots rows observed ed ml))
        (ev (fn-ks-execute event snapshots rows observed ed ml
                           sequence txid store-generation)))
    (implies (and ev (equal (car plan) :enroll))
             (equal (fn-hl-current-enrollment (fn-hl-next-generation snapshots)
                                              (cons ev snapshots))
                    (list ev (nth 1 plan) (nth 2 plan)))))
  :hints (("Goal" :in-theory (union-theories '(fn-ks-execute)
                                             (theory 'minimal-theory))
           :use ((:instance fn-ks-event-of-an-enrollment-is-selected
                            (plan (fn-ks-plan event snapshots rows observed
                                              ed ml)))))))

; KEYSTONE (theorem 2, the old keys are refused).  After the succession's
; event is the newest snapshot, a carrier naming the principal under any key
; set but the new one -- in particular the old one -- is refused
; :local-enrollment by the acceptance plan on every path: it is not :ok, not
; :carried (the principal has a snapshot) and not :revoked (the newest
; snapshot is a key snapshot, not a tombstone).
(defthm fn-ks-succession-refuses-other-keys
  (let ((plan (fn-ks-plan event snapshots rows observed ed ml))
        (ev (fn-ks-execute event snapshots rows observed ed ml
                           sequence txid store-generation))
        (form (fn-pa-carrier-form received)))
    (implies (and ev (equal (car plan) :enroll)
                  (equal (car form) :ok)
                  (equal (nth 2 form) (nth 1 plan))
                  (not (equal (nth 3 form) (nth 2 plan))))
             (equal (fn-pa-current-plan received (cons ev snapshots)
                                        carried transitp)
                    (list :refused :local-enrollment))))
  :hints (("Goal" :in-theory (union-theories '(fn-ks-execute)
                                             (theory 'minimal-theory))
           :use ((:instance fn-ks-event-of-an-enrollment-refuses-other-keys
                            (plan (fn-ks-plan event snapshots rows observed
                                              ed ml)))))))

(defthm fn-ks-succession-refuses-the-old-keys
  (let* ((plan (fn-ks-plan event snapshots rows observed ed ml))
         (ev (fn-ks-execute event snapshots rows observed ed ml
                            sequence txid store-generation))
         (enrolled (fn-hl-current-enrollment
                    (fn-stx-verdict-generation (fn-ks-verdict event))
                    snapshots))
         (form (fn-pa-carrier-form received)))
    (implies (and ev (equal (car plan) :enroll)
                  (equal (car form) :ok)
                  (equal (nth 2 form) (nth 1 plan))
                  (equal (nth 3 form) (caddr enrolled)))
             (equal (fn-pa-current-plan received (cons ev snapshots)
                                        carried transitp)
                    (list :refused :local-enrollment))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use (fn-ks-succession-refuses-other-keys
                 fn-ks-plan-old-key-was-the-current-enrollment))))

(defthm fn-ks-event-of-a-revocation-leaves-no-ok-plan
  (let ((ev (fn-ks-event plan sequence txid store-generation snapshots)))
    (implies (and ev (equal (car plan) :revoke)
                  (equal (nth 2 (fn-pa-carrier-form received)) (nth 1 plan)))
             (not (equal (car (fn-pa-current-plan received (cons ev snapshots)
                                                  carried transitp))
                         :ok))))
  :hints (("Goal" :in-theory (e/d (fn-ks-event)
                                  (fn-hl-revoke-event fn-hl-enroll-event
                                   fn-pa-current-plan fn-pa-carrier-form
                                   fn-hl-next-generation))
           :use ((:instance fn-pa-revocation-leaves-no-ok-plan
                            (g (fn-hl-next-generation snapshots))
                            (principal (nth 1 plan)))))))

; KEYSTONE (theorem 3 over the executor).  A revocation statement's event is
; the principal's tombstone at the next generation; with it the newest
; snapshot, no plan for that principal is :ok
; (fn-pa-revocation-leaves-no-ok-plan applies to exactly this event).
(defthm fn-ks-revocation-leaves-no-ok-plan
  (let ((plan (fn-ks-plan event snapshots rows observed ed ml))
        (ev (fn-ks-execute event snapshots rows observed ed ml
                           sequence txid store-generation)))
    (implies (and ev (equal (car plan) :revoke)
                  (equal (nth 2 (fn-pa-carrier-form received)) (nth 1 plan)))
             (not (equal (car (fn-pa-current-plan received (cons ev snapshots)
                                                  carried transitp))
                         :ok))))
  :hints (("Goal" :in-theory (union-theories '(fn-ks-execute)
                                             (theory 'minimal-theory))
           :use ((:instance fn-ks-event-of-a-revocation-leaves-no-ok-plan
                            (plan (fn-ks-plan event snapshots rows observed
                                              ed ml)))))))

; -----------------------------------------------------------------------------
; The crash cut between the statement's commit and the key change's.
;
; The owner commits a statement in two Store transactions: the kind-4
; composite (the article, fnn-owner-identity-commit in
; fnn-owner-attempt-transit), then the kind-3 key change fn-ks-execute builds
; (fnn-owner-key-statement).  A process death between the two leaves the
; statement accepted and its change unmade.  The model below names that cut
; (fn-ks-cut) beside the uninterrupted protocol (fn-ks-accept) and the
; recovery the owner runs at open (fn-ks-recover): it executes the NEWEST
; Store record if that record is a statement (fn-ks-pending).  Nothing is
; committed between the two transactions (they run back to back under the
; owner mutex), so a statement whose change the cut lost is exactly the
; newest record at the next open.  A statement that declined is also the
; newest record until the next commit; recovery decides it again under the
; open's configuration and observations, which is the decision an
; uninterrupted acceptance at that instant would make.
;
; STATE is (RECORDS . SNAPSHOTS): the Store's records newest first and its
; keyring snapshots (fn-sn-keyring-snapshots) newest first.
;
; Host: host/native/owner.lisp fnn-owner-install calls
; host/owner-host.lisp fn-owner-key-statement-pending over the newest record
; the open read, then fnn-owner-key-statement (fn-ks-plan, fn-ks-execute)
; exactly as at acceptance.

(defun fn-ks-pending (record)
  (declare (xargs :guard t))
  (if (fn-ks-statement (fn-ks-source record)) record nil))

(defun fn-ks-accept (records snapshots event rows observed ed ml
                             sequence txid store-generation)
  (declare (xargs :guard t))
  (let ((ev (fn-ks-execute event snapshots rows observed ed ml
                           sequence txid store-generation)))
    (if ev
        (cons (list* ev event records) (cons ev snapshots))
      (cons (cons event records) snapshots))))

(defun fn-ks-cut (records snapshots event)
  (declare (xargs :guard t))
  (cons (cons event records) snapshots))

(defun fn-ks-recover (st rows observed ed ml sequence txid store-generation)
  (declare (xargs :guard t))
  (let* ((records (and (consp st) (car st)))
         (snapshots (and (consp st) (cdr st)))
         (pending (and (consp records) (fn-ks-pending (car records))))
         (ev (and pending
                  (fn-ks-execute pending snapshots rows observed ed ml
                                 sequence txid store-generation))))
    (if ev
        (cons (cons ev records) (cons ev snapshots))
      st)))

(defthm fn-ks-execute-needs-a-statement
  (implies (not (fn-ks-statement (fn-ks-source event)))
           (not (fn-ks-execute event snapshots rows observed ed ml
                               sequence txid store-generation)))
  :hints (("Goal" :in-theory (e/d (fn-ks-execute fn-ks-event fn-ks-plan)
                                  (fn-ks-statement fn-ks-source
                                   fn-hl-enroll-event fn-hl-revoke-event)))))

; KEYSTONE (the cut is a model crash point).  Death between the statement's
; commit and its change's, then the open's recovery, reaches exactly the
; state of the uninterrupted acceptance under the recovery's configuration
; and observations.
(defthm fn-ks-recover-completes-the-cut
  (equal (fn-ks-recover (fn-ks-cut records snapshots event)
                        rows observed ed ml sequence txid store-generation)
         (fn-ks-accept records snapshots event rows observed ed ml
                       sequence txid store-generation))
  :hints (("Goal" :in-theory (e/d (fn-ks-recover fn-ks-cut fn-ks-accept
                                   fn-ks-pending)
                                  (fn-ks-execute fn-ks-statement fn-ks-source))
           :use fn-ks-execute-needs-a-statement)))

; The facts an acting plan carries about its statement.
(defthm fn-ks-plan-acting-facts
  (let ((plan (fn-ks-plan event snapshots rows observed ed ml))
        (statement (fn-ks-statement (fn-ks-source event))))
    (implies (or (equal (car plan) :enroll) (equal (car plan) :revoke))
             (and (equal (nth 1 plan) (nth 1 statement))
                  (iff (equal (car plan) :revoke)
                       (equal (car statement) :revocation))
                  (implies (equal (car plan) :enroll)
                           (equal (nth 2 plan) (nth 3 statement))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ks-plan)
                                  (fn-ks-statement fn-ks-verdict
                                   fn-ctl-authorize fn-ks-source fn-stxa-p
                                   fn-hsig-authored-source-fields
                                   fn-hl-current-enrollment
                                   fn-hsig-authorize)))))

; The kind-3 event of an acting plan: a snapshot of the plan's principal,
; with no value (a tombstone) for a revocation and the new keys for an
; enrollment.
(defthm fn-ks-event-facts
  (let ((ev (fn-ks-event plan sequence txid store-generation snapshots)))
    (implies ev
             (and (fn-stxk-p ev)
                  (equal (fn-hl-snapshot-principal ev) (nth 1 plan))
                  (if (equal (car plan) :revoke)
                      (not (fn-hsig-keyring-snapshot-value ev))
                    (equal (fn-hsig-keyring-snapshot-value ev)
                           (list (nth 1 plan) (nth 2 plan)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ks-event)
                                  (fn-hl-enroll-event fn-hl-revoke-event
                                   fn-stxk-p fn-hsig-keyring-snapshot-value
                                   fn-hl-snapshot-principal
                                   fn-hl-next-generation))
           :use ((:instance fn-hl-enroll-event-enrolls-its-keys
                            (keyring-generation (fn-hl-next-generation snapshots))
                            (principal (nth 1 plan)) (keys (nth 2 plan)))
                 (:instance fn-hl-revoke-event-is-the-principals-tombstone
                            (keyring-generation (fn-hl-next-generation snapshots))
                            (principal (nth 1 plan)))))))

; With a snapshot EV of principal P newest, an enrollment of P that
; fn-hl-current-enrollment selects is EV itself.
(defthm fn-ks-current-enrollment-after-a-snapshot-of-its-principal
  (let ((en (fn-hl-current-enrollment g (cons ev s))))
    (implies (and (fn-stxk-p ev)
                  (equal (fn-hl-snapshot-principal ev) p)
                  en
                  (equal (cadr en) p))
             (equal (car en) ev)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-hl-current-enrollment fn-stxk-find)
                                  (fn-hsig-keyring-snapshot-value
                                   fn-hl-snapshot-principal fn-stxk-p)))))

; A statement never acts against snapshots headed by a snapshot of its own
; principal that holds the keys it asks for (or, for a revocation, none).
(defthm fn-ks-plan-after-its-own-change-does-not-act
  (let ((statement (fn-ks-statement (fn-ks-source event))))
    (implies (and (fn-stxk-p ev)
                  (equal (fn-hl-snapshot-principal ev) (nth 1 statement))
                  (if (equal (car statement) :revocation)
                      (not (fn-hsig-keyring-snapshot-value ev))
                    (equal (fn-hsig-keyring-snapshot-value ev)
                           (list (nth 1 statement) (nth 3 statement)))))
             (let ((plan (fn-ks-plan event (cons ev s) rows observed ed ml)))
               (not (or (equal (car plan) :enroll)
                        (equal (car plan) :revoke))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ks-plan)
                                  (fn-ks-statement fn-ks-verdict
                                   fn-ctl-authorize fn-ks-source fn-stxa-p
                                   fn-hsig-authored-source-fields
                                   fn-hl-current-enrollment
                                   fn-hsig-authorize fn-stxk-p
                                   fn-hsig-keyring-snapshot-value
                                   fn-hl-snapshot-principal))
           :use ((:instance fn-ks-current-enrollment-after-a-snapshot-of-its-principal
                            (g (fn-stx-verdict-generation (fn-ks-verdict event)))
                            (p (nth 1 (fn-ks-statement (fn-ks-source event)))))
                 (:instance fn-hl-current-enrollment-selects-an-enrolled-snapshot
                            (requested (fn-stx-verdict-generation
                                        (fn-ks-verdict event)))
                            (snapshots (cons ev s)))))))

; KEYSTONE (idempotence).  Executing a statement whose key change is already
; the newest snapshot changes nothing, under any configuration, observations
; and coordinates: a succession then finds its own new keys current (it
; declines :old-key or :same-keys), a revocation finds its principal's
; tombstone (it declines :not-current).
(defthm fn-ks-execute-is-idempotent
  (let ((ev (fn-ks-execute event snapshots rows observed ed ml
                           sequence txid store-generation)))
    (implies ev
             (equal (fn-ks-execute event (cons ev snapshots) rows2 observed2
                                   ed2 ml2 sequence2 txid2 store-generation2)
                    nil)))
  :hints (("Goal" :in-theory (union-theories '(fn-ks-execute)
                                             (theory 'minimal-theory))
           :use ((:instance fn-ks-execute-needs-an-acting-plan)
                 (:instance fn-ks-plan-acting-facts)
                 (:instance fn-ks-event-facts
                            (plan (fn-ks-plan event snapshots rows observed ed ml)))
                 (:instance fn-ks-plan-after-its-own-change-does-not-act
                            (ev (fn-ks-execute event snapshots rows observed ed ml
                                               sequence txid store-generation))
                            (s snapshots) (rows rows2) (observed observed2)
                            (ed ed2) (ml ml2))
                 (:instance fn-ks-execute-needs-an-acting-plan
                            (snapshots
                             (cons (fn-ks-execute event snapshots rows observed
                                                  ed ml sequence txid
                                                  store-generation)
                                   snapshots))
                            (rows rows2) (observed observed2) (ed ed2) (ml ml2)
                            (sequence sequence2) (txid txid2)
                            (store-generation store-generation2))))))

; A kind-3 snapshot is not a kind-4 composite, so it is never pending.
(defthm fn-ks-snapshot-is-not-a-composite
  (implies (fn-stxk-p ev) (not (fn-stxa-p ev)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-stxk-p fn-stxa-p
                                               fn-stxk-shapep fn-stxa-shapep)
                                             (theory 'minimal-theory)))))

(defthm fn-ks-snapshot-is-never-pending
  (implies (fn-stxk-p ev) (not (fn-ks-pending ev)))
  :hints (("Goal" :in-theory (union-theories '(fn-ks-pending fn-ks-source
                                               (:e fn-ks-statement))
                                             (theory 'minimal-theory))
           :use fn-ks-snapshot-is-not-a-composite)))

(defthm fn-ks-execute-is-a-snapshot
  (let ((ev (fn-ks-execute event snapshots rows observed ed ml
                           sequence txid store-generation)))
    (implies ev (fn-stxk-p ev)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ks-execute) (fn-ks-event fn-ks-plan fn-stxk-p))
           :use ((:instance fn-ks-event-facts
                            (plan (fn-ks-plan event snapshots rows observed ed ml)))))))

; KEYSTONE (recovery after a completed acceptance changes nothing).  When
; the acceptance acted, its change is the newest record and the open's
; recovery leaves the state as it is, under any configuration and
; observations.
(defthm fn-ks-recover-after-an-acting-acceptance-changes-nothing
  (let ((st (fn-ks-accept records snapshots event rows observed ed ml
                          sequence txid store-generation)))
    (implies (fn-ks-execute event snapshots rows observed ed ml
                            sequence txid store-generation)
             (equal (fn-ks-recover st rows2 observed2 ed2 ml2
                                   sequence2 txid2 store-generation2)
                    st)))
  :hints (("Goal" :in-theory (e/d (fn-ks-recover fn-ks-accept)
                                  (fn-ks-execute fn-ks-pending fn-stxk-p))
           :use ((:instance fn-ks-snapshot-is-never-pending
                            (ev (fn-ks-execute event snapshots rows observed
                                               ed ml sequence txid
                                               store-generation)))
                 fn-ks-execute-is-a-snapshot))))

;; =============================================================================
;; Packet 7 (PRF-124): a declined statement stays declined across a restart.
;;
;; The newest-record recovery above decides the pending statement under the
;; OPEN's configuration.  A statement that declined at acceptance (no
;; `keys' grant, say) is still the newest Store record after a restart, and
;; configuration records live in their own journal (fn-sn-config-history),
;; so a grant added across the restart made the open's recovery ACT on it:
;; an old decline silently became new authority (the handoff's flag; the
;; native trace in planning/evidence/peering-compose-2026-09-25.md).
;;
;; The recorded disposition: the reopen decides a statement under the
;; configuration in force at the statement's OWN Store txid, the
;; configuration journal's fold through that txid (C3's `fn-ctl-config-at',
;; books/control-authority.lisp) -- exactly what the uninterrupted acceptance
;; decided under.  The statement record and the journal are durable, so the
;; disposition is a pure function of durable records and the observations
;; over the stored bytes: a decline replays as a decline, and the cut the
;; recovery exists for still completes as the acceptance would have.
;; Re-evaluating an old statement under today's grants is then an explicit
;; act: a new statement (or the operator's own key change), never a restart.
;;
;; The reopen is recorded by definition; there is no policy switch (gpt-6's
;; review of wave 2, section 5: a switch that recreates retroactive authority
;; is not an engineering benefit).  The pre-packet behaviour survives only as
;; the counterexample fixture in tests/acl2/key-statements-tests.lisp.  The
;; replay rule is part of the Store format's meaning: the statement record
;; plus the configuration journal determine the disposition only under this
;; rule, so changing it is a format version with its own reader, never an
;; edit here that reinterprets bytes already written.
;;
;; The reconstruction reads exactly the configuration journal the open
;; installs (fn-sn-config-history: every configuration record from
;; generation 1, contiguous, or the open faults `:config-sequence' in
;; books/config-physical-replay.lisp fn-cpr-loop); no transition removes a
;; configuration record (reclaim and compaction write none,
;; books/checkpoint-compaction-preservation.lisp), and the profile's
;; `max-config-generations' refuses a new record rather than dropping an old
;; one, so the prefix through any statement's txid is always present.

; A statement's Store txid: its kind-4 composite's (what
; books/store-events.lisp fn-store-event-txid answers for a composite).
(defun fn-ks-txid (event)
  (declare (xargs :guard t))
  (if (fn-stxa-p event) (fn-stxa-txid event) nil))

; The grants a statement is decided under: at acceptance, the live
; configuration's LIVE-ROWS; at open (AT-OPEN), the configuration in force at
; the statement's own txid, the fold of the journal CONFIGS through it.
; Host: host/owner-host.lisp fn-owner-key-statement-rows (the plan and the
; kind-3 event of fnn-owner-key-statement, acceptance and open alike).
(defun fn-ks-statement-rows (event at-open live-rows configs)
  (declare (xargs :guard t))
  (if at-open
      (fn-cfg-authorities
       (fn-cfg-value (fn-ctl-config-at (fn-ks-txid event) configs)))
    live-rows))

; The open's recovery under the recorded disposition: the pending statement
; is decided under the grants of the configuration in force at its txid.
; Host: host/native/owner.lisp fnn-owner-key-statement-recover calls
; fnn-owner-key-statement with AT-OPEN, whose rows are
; host/owner-host.lisp fn-owner-key-statement-rows = fn-ks-statement-rows.
(defun fn-ks-recover-recorded (st configs observed ed ml sequence txid
                                  store-generation)
  (declare (xargs :guard t))
  (let* ((records (and (consp st) (car st)))
         (pending (and (consp records) (fn-ks-pending (car records)))))
    (fn-ks-recover st (fn-ks-statement-rows pending t nil configs)
                   observed ed ml sequence txid store-generation)))

(defun fn-ks-configs-after-p (txid more)
  ; Every configuration record of MORE is later than TXID.
  (declare (xargs :guard t))
  (or (not (consp more))
      (< (nfix txid) (nfix (fn-cfg-record-txid (car more))))))

; KEYSTONE (packet 7: replay reproduces the recorded disposition).  A
; configuration record appended after the pending statement's txid -- a new
; `keys' grant, a revocation of one, anything -- does not change what the
; open's recovery does with that statement.  Subject:
; `fn-ks-recover-recorded', which the open runs.
(defthm fn-ks-reopen-is-blind-to-later-configuration
  (let ((pending (fn-ks-pending (car (car st)))))
    (implies (fn-ks-configs-after-p (fn-ks-txid pending) more)
             (equal (fn-ks-recover-recorded st (append configs more) observed
                                            ed ml sequence txid
                                            store-generation)
                    (fn-ks-recover-recorded st configs observed ed ml
                                            sequence txid store-generation))))
  :hints (("Goal" :in-theory (e/d (fn-ctl-config-at)
                                  (fn-ks-recover fn-ks-pending
                                   fn-ctl-apply-records))
           :use ((:instance fn-ctl-configs-through-of-later-append
                            (txid (fn-ks-txid
                                   (fn-ks-pending (car (car st))))))))))

(defthm fn-ks-plan-needs-a-statement
  (implies (fn-ks-plan event snapshots rows observed ed ml)
           (fn-ks-statement (fn-ks-source event)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ks-plan)
                                  (fn-ks-statement fn-ks-source fn-ks-verdict
                                   fn-ks-msgid fn-ks-pop-source
                                   fn-hsig-authored-source-fields
                                   fn-ctl-authorize fn-hl-current-enrollment
                                   fn-hsig-authorize fn-stx-verdict-generation
                                   fn-stx-verdict-detail)))))

(defthm fn-ks-declining-plan-executes-nothing
  (implies (equal (car (fn-ks-plan event snapshots rows observed ed ml))
                  :decline)
           (not (fn-ks-execute event snapshots rows observed ed ml
                               sequence txid store-generation)))
  :hints (("Goal" :in-theory (e/d (fn-ks-execute fn-ks-event)
                                  (fn-ks-plan)))))

; KEYSTONE (packet 7: a decline replays as a decline).  A statement EVENT
; whose plan declined when it was accepted under the grants of the
; configuration in force at its own txid is left exactly as the acceptance
; left it by the open's recovery over that journal with any later
; configuration records appended, whatever coordinates the recovery holds.
; The observations are the ones over the same stored bytes (the primitive
; is a function of its inputs; A-CRYPTO).
(defthm fn-ks-a-decline-replays-as-a-decline
  (let* ((rows (fn-cfg-authorities
                (fn-cfg-value (fn-ctl-config-at (fn-ks-txid event)
                                                configs))))
         (st (fn-ks-accept records snapshots event rows observed ed ml
                           sequence txid store-generation)))
    (implies (and (equal (car (fn-ks-plan event snapshots rows observed ed ml))
                         :decline)
                  (fn-ks-configs-after-p (fn-ks-txid event) more))
             (equal (fn-ks-recover-recorded st (append configs more) observed
                                            ed ml sequence2 txid2
                                            store-generation2)
                    st)))
  :hints (("Goal" :in-theory (e/d (fn-ks-accept fn-ks-recover
                                   fn-ks-recover-recorded fn-ks-statement-rows
                                   fn-ks-pending fn-ctl-config-at)
                                  (fn-ks-execute fn-ks-plan fn-ks-statement
                                   fn-ks-source fn-ctl-apply-records
                                   fn-ctl-configs-through))
           :use ((:instance fn-ctl-configs-through-of-later-append
                            (txid (fn-ks-txid event)))
                 (:instance fn-ks-plan-needs-a-statement
                            (rows (fn-cfg-authorities
                                   (fn-cfg-value
                                    (fn-ctl-config-at
                                     (fn-ks-txid event) configs)))))
                 (:instance fn-ks-declining-plan-executes-nothing
                            (rows (fn-cfg-authorities
                                   (fn-cfg-value
                                    (fn-ctl-config-at
                                     (fn-ks-txid event) configs)))))
                 (:instance fn-ks-declining-plan-executes-nothing
                            (rows (fn-cfg-authorities
                                   (fn-cfg-value
                                    (fn-ctl-config-at
                                     (fn-ks-txid event) configs))))
                            (sequence sequence2) (txid txid2)
                            (store-generation store-generation2))))))

(defthm fn-ks-recover-without-a-pending-record
  (implies (not (fn-ks-pending (car (car st))))
           (equal (fn-ks-recover st rows observed ed ml sequence txid
                                 store-generation)
                  st))
  :hints (("Goal" :in-theory (e/d (fn-ks-recover) (fn-ks-pending)))))

; KEYSTONE (packet 7: the cut still completes as the acceptance would).
; When every configuration record precedes the statement's txid and the
; journal replays, the configuration in force at the txid IS the live one
; the acceptance read, so death at the cut followed by the recorded
; recovery reaches the uninterrupted acceptance under the live grants.
(defthm fn-ks-recorded-recovery-completes-the-cut
  (implies (and (fn-ctl-configs-all-through-p (fn-ks-txid event)
                                              configs)
                (true-listp configs)
                (not (equal (fn-config-replay reserved ceiling configs) :fault)))
           (equal (fn-ks-recover-recorded (fn-ks-cut records snapshots event)
                                          configs observed ed ml sequence txid
                                          store-generation)
                  (fn-ks-accept records snapshots event
                                (fn-cfg-authorities
                                 (fn-cfg-value
                                  (fn-config-replay reserved ceiling configs)))
                                observed ed ml sequence txid
                                store-generation)))
  :hints (("Goal" :do-not-induct t
           :cases ((fn-ks-statement (fn-ks-source event)))
           :in-theory (e/d (fn-ks-recover-recorded fn-ks-statement-rows
                                   fn-ks-cut fn-ks-pending)
                                  (fn-ks-recover fn-ks-accept fn-ks-execute
                                   fn-ks-statement fn-ks-source
                                   fn-ctl-config-at fn-config-replay
                                   fn-ctl-configs-all-through-p))
           :use ((:instance fn-ks-execute-needs-a-statement
                            (rows (fn-cfg-authorities
                                   (fn-cfg-value
                                    (fn-config-replay reserved ceiling
                                                      configs)))))
                 (:instance fn-ks-recover-completes-the-cut
                            (rows (fn-cfg-authorities
                                   (fn-cfg-value
                                    (fn-config-replay reserved ceiling
                                                      configs)))))
                 (:instance fn-ctl-config-at-after-every-record-is-the-replay
                            (txid (fn-ks-txid event)))))))

;; =============================================================================
;; PRF-140: an accepted statement finishes under its own admission context.
;;
;; The statement was accepted (its kind-4 composite committed) while the
;; configuration journal was CONFIGS, every record at or before its txid, so
;; the acceptance read the live configuration, CONFIGS' replay.  The process
;; died at the cut (fn-ks-cut: the key change never committed).  Before the
;; restart the operator published MORE, every record later than the txid (a
;; `keys' grant revoked, say).  The open's recorded recovery over the whole
;; journal then makes exactly the change the uninterrupted acceptance would
;; have made under the ORIGINAL configuration -- never one decided under
;; today's.  Built on fn-ks-recorded-recovery-completes-the-cut (the cut
;; completes under the journal it was accepted under) and
;; fn-ks-reopen-is-blind-to-later-configuration.  Subject:
;; `fn-ks-recover-recorded' (host: fnn-owner-key-statement-recover, rows
;; host/owner-host.lisp fn-owner-key-statement-rows).

(defthm fn-ks-recover-recorded-without-a-pending-record
  (implies (not (fn-ks-pending (car (car st))))
           (equal (fn-ks-recover-recorded st configs observed ed ml sequence
                                          txid store-generation)
                  st))
  :hints (("Goal" :in-theory (e/d (fn-ks-recover-recorded)
                                  (fn-ks-pending fn-ks-recover
                                   fn-ks-statement-rows)))))

; A journal that replays is a true list (the replay faults on an improper
; tail), so PRF-140 needs no separate true-listp hypothesis.
(defthm fn-ks-config-replay-loop-needs-a-true-list
  (implies (not (equal (fn-config-replay-loop cfg reserved ceiling records)
                       :fault))
           (true-listp records))
  :rule-classes nil
  :hints (("Goal" :induct (fn-config-replay-loop cfg reserved ceiling records)
           :in-theory (e/d (fn-config-replay-loop)
                           (fn-cfg-record-acceptablep fn-cfg-apply-record)))))

(defthm fn-ks-config-replay-needs-a-true-list
  (implies (not (equal (fn-config-replay reserved ceiling records) :fault))
           (true-listp records))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-config-replay)
           :use ((:instance fn-ks-config-replay-loop-needs-a-true-list
                            (cfg (fn-cfg-initial)))))))

; KEYSTONE (PRF-140).
(defthm fn-ks-accepted-statement-finishes-under-its-admission-context
  (implies (and (fn-ctl-configs-all-through-p (fn-ks-txid event) configs)
                (not (equal (fn-config-replay reserved ceiling configs) :fault))
                (fn-ks-configs-after-p (fn-ks-txid event) more))
           (equal (fn-ks-recover-recorded (fn-ks-cut records snapshots event)
                                          (append configs more)
                                          observed ed ml sequence txid
                                          store-generation)
                  (fn-ks-accept records snapshots event
                                (fn-cfg-authorities
                                 (fn-cfg-value
                                  (fn-config-replay reserved ceiling configs)))
                                observed ed ml sequence txid
                                store-generation)))
  :hints (("Goal" :do-not-induct t
           :cases ((fn-ks-statement (fn-ks-source event)))
           :in-theory (e/d (fn-ks-cut fn-ks-pending fn-ks-accept)
                           (fn-ks-recover-recorded fn-ks-recover
                            fn-ks-execute fn-ks-statement fn-ks-source
                            fn-ctl-config-at fn-config-replay
                            fn-ctl-configs-all-through-p fn-ks-configs-after-p))
           :use ((:instance fn-ks-reopen-is-blind-to-later-configuration
                            (st (fn-ks-cut records snapshots event)))
                 fn-ks-recorded-recovery-completes-the-cut
                 (:instance fn-ks-config-replay-needs-a-true-list
                            (records configs))
                 (:instance fn-ks-recover-recorded-without-a-pending-record
                            (st (fn-ks-cut records snapshots event))
                            (configs (append configs more)))
                 (:instance fn-ks-execute-needs-a-statement
                            (rows (fn-cfg-authorities
                                   (fn-cfg-value
                                    (fn-config-replay reserved ceiling
                                                      configs)))))))))

; The owner log line for a statement's outcome (host/native/owner.lisp
; fnn-owner-key-statement writes it and decides nothing).  OUTCOME is the
; kind-3 commit's: :committed, :refused (the Store refused the key change;
; the statement article itself stays accepted), or nil (none attempted).
; AT-OPEN marks the recovery's execution of the newest record at open.
(defun fn-ks-word (x)
  (declare (xargs :guard t))
  (cond ((eq x :enroll) "enrol-successor")
        ((eq x :revoke) "revoke")
        ((eq x :decline) "declined")
        ((eq x :unsigned) "unsigned")
        ((eq x :carried) "carried")
        ((eq x :legacy-verdict) "legacy-verdict")
        ((eq x :unverified) "unverified")
        ((eq x :verb-not-granted) "verb-not-granted")
        ((eq x :no-grant) "no-grant")
        ((eq x :no-groups) "no-groups")
        ((eq x :outside-namespace) "outside-namespace")
        ((eq x :another-principal) "another-principal")
        ((eq x :not-current) "not-current")
        ((eq x :old-key) "old-key")
        ((eq x :same-keys) "same-keys")
        ((eq x :proof-of-possession) "proof-of-possession")
        ((eq x :committed) "committed")
        ((eq x :refused) "refused")
        ((eq x :not-a-key-statement) "not-a-key-statement")
        ((eq x :already-acted) "already-acted")
        (t "other")))

(defun fn-ks-log-line (plan outcome at-open)
  (declare (xargs :guard t))
  (fn-record-string-octets
   (concatenate 'string "key-statement "
                (if (consp plan) (fn-ks-word (car plan)) "none")
                (if (and (consp plan) (eq (car plan) :decline) (consp (cdr plan)))
                    (concatenate 'string " " (fn-ks-word (cadr plan)))
                  "")
                (if (member-eq outcome '(:committed :refused))
                    (concatenate 'string " " (fn-ks-word outcome))
                  "")
                (if at-open " at-open" ""))))

(in-theory (disable (:d fn-ks-prefix-rest) (:d fn-ks-lines) (:d fn-ks-values)
                    (:d fn-ks-unhex-exact) (:d fn-ks-field)
                    (:d fn-ks-statement) (:d fn-ks-pop-source)
                    (:d fn-ks-evidence) (:d fn-ks-verdict) (:d fn-ks-msgid)
                    (:d fn-ks-source) (:d fn-ks-pop-request) (:d fn-ks-plan)
                    (:d fn-ks-event) (:d fn-ks-execute) (:d fn-ks-pending)
                    (:d fn-ks-accept) (:d fn-ks-cut) (:d fn-ks-recover)))

;; =============================================================================
;; PKT-325, PRF-166: `operator CONFIG keys redecide MSGID' -- the operator
;; re-decides a stored key statement (specs/peering.md 7.4).
;;
;; A statement that declined (no `keys' grant yet, say) is not re-decided by
;; the open (PRF-124: the recorded reopen is blind to later configuration).
;; The operator asks for it explicitly, over the control socket, and the owner
;; decides it under its mutex as a NEW acceptance of the stored statement: the
;; plan is `fn-ks-plan' over the stored composite, the Store's keyring now and
;; the grants of the configuration in force at the redecide's OWN txid (the
;; live configuration, which is the replay of the whole journal:
;; fn-ks-redecide-decides-under-the-configuration-at-its-own-txid).
;;
;; The record: when the plan acts, the one durable record is the kind-3 key
;; change itself, committed at the redecide's own coordinates; no statement is
;; re-filed and no new record kind exists.  So there is no cut: the change is
;; durable or it never happened, and the next open's recorded recovery sees a
;; newest record that is no statement and repeats nothing
;; (fn-ks-reopen-after-a-redecide); PRF-124 and PRF-140 carry over unchanged
;; (a redecide that did not act left the Store exactly as it was).
;;
;; Refused by name, with the Store unchanged: MSGID names no stored key
;; statement (:not-a-key-statement), or the change the statement asks for is
;; already in the keyring at a generation after the statement's own
;; (:already-acted).  A statement that is merely superseded declines
;; `not-current' through the plan.
;;
;; Host: host/native/keys.lisp fnn-keys-owner-redecide calls
;; host/owner-host.lisp fn-owner-key-statement-redecide-find, -request, -plan
;; and -event, which are fn-ks-find-statement, fn-ks-pop-request,
;; fn-ks-redecide-plan and fn-ks-redecide-event over the owner's Store records,
;; keyring snapshots and live authorities rows.

; The stored statement MSGID names among the Store's RECORDS, or nil.
; Message-IDs are unique in a Store, so the scan's order does not matter.
(defun fn-ks-find-statement (msgid records)
  (declare (xargs :guard t))
  (if (consp records)
      (if (and (fn-ks-pending (car records))
               (equal (fn-ks-msgid (car records)) msgid))
          (car records)
        (fn-ks-find-statement msgid (cdr records)))
    nil))

; SNAPSHOT is the change STATEMENT asks for: a revocation of its principal,
; or an enrolment of its principal under its new keys.
(defun fn-ks-change-snapshotp (statement snapshot)
  (declare (xargs :guard t))
  (and (consp statement)
       (true-listp statement)
       (fn-stxk-p snapshot)
       (equal (fn-hl-snapshot-principal snapshot) (nth 1 statement))
       (if (eq (car statement) :revocation)
           (equal (fn-stxk-profile snapshot) *fn-hl-revoked-profile*)
         (let ((value (fn-hsig-keyring-snapshot-value snapshot)))
           (and (consp value) (consp (cdr value))
                (equal (cadr value) (nth 3 statement)))))))

(defun fn-ks-acted-in (statement generation snapshots)
  (declare (xargs :guard t))
  (if (consp snapshots)
      (or (and (fn-stxk-p (car snapshots))
               (< (nfix generation)
                  (nfix (fn-stxk-keyring-generation (car snapshots))))
               (fn-ks-change-snapshotp statement (car snapshots)))
          (fn-ks-acted-in statement generation (cdr snapshots)))
    nil))

; The statement EVENT already acted: its change is in the keyring at a
; generation after the one its stored verdict was decided against.
(defun fn-ks-acted-p (event snapshots)
  (declare (xargs :guard t))
  (fn-ks-acted-in (fn-ks-statement (fn-ks-source event))
                  (fn-stx-verdict-generation (fn-ks-verdict event))
                  snapshots))

(defun fn-ks-redecide-plan (event snapshots rows observed-ml-key ed-observation
                                  ml-observation)
  (declare (xargs :guard t))
  (cond ((not (fn-ks-pending event)) (list :refused :not-a-key-statement))
        ((fn-ks-acted-p event snapshots) (list :refused :already-acted))
        (t (fn-ks-plan event snapshots rows observed-ml-key ed-observation
                       ml-observation))))

; The kind-3 event the redecide commits, or nil.
(defun fn-ks-redecide-event (event snapshots rows observed-ml-key
                                   ed-observation ml-observation sequence txid
                                   store-generation)
  (declare (xargs :guard t))
  (fn-ks-event (fn-ks-redecide-plan event snapshots rows observed-ml-key
                                    ed-observation ml-observation)
               sequence txid store-generation snapshots))

; The model transition over STATE (RECORDS . SNAPSHOTS), newest first.
(defun fn-ks-redecide (st msgid rows observed ed ml sequence txid
                          store-generation)
  (declare (xargs :guard t))
  (let* ((records (and (consp st) (car st)))
         (snapshots (and (consp st) (cdr st)))
         (ev (fn-ks-redecide-event (fn-ks-find-statement msgid records)
                                   snapshots rows observed ed ml sequence txid
                                   store-generation)))
    (if ev
        (cons (cons ev records) (cons ev snapshots))
      st)))

; The grants of the configuration in force at TXID, the fold of the journal.
(defun fn-ks-redecide-rows (txid configs)
  (declare (xargs :guard t))
  (fn-cfg-authorities (fn-cfg-value (fn-ctl-config-at txid configs))))

(defun fn-ks-redecide-log-line (plan outcome)
  (declare (xargs :guard t))
  (fn-record-string-octets
   (concatenate 'string "key-statement redecide "
                (if (consp plan) (fn-ks-word (car plan)) "none")
                (if (and (consp plan) (member-eq (car plan) '(:decline :refused))
                         (consp (cdr plan)))
                    (concatenate 'string " " (fn-ks-word (cadr plan)))
                  "")
                (if (member-eq outcome '(:committed :refused))
                    (concatenate 'string " " (fn-ks-word outcome))
                  ""))))

(defthm fn-ks-a-keyring-record-is-no-composite
  (implies (fn-stxk-p x) (not (fn-stxa-p x)))
  :hints (("Goal" :in-theory (enable fn-stxk-p fn-stxa-p fn-stxk-shapep
                                     fn-stxa-shapep))))

(defthm fn-ks-a-key-change-is-no-pending-statement
  (not (fn-ks-pending (fn-ks-event plan sequence txid store-generation
                                   snapshots)))
  :hints (("Goal" :in-theory (enable fn-ks-pending fn-ks-source fn-ks-event
                                     fn-hl-enroll-event fn-hl-revoke-event
                                     fn-hsig-keyring-event))))

; KEYSTONE (PRF-166 1: the redecide's own txid).  The live configuration the
; owner holds is the replay of its whole journal; every record of that journal
; precedes the redecide's own TXID, so the grants the host passes (the live
; rows) are the grants of the configuration in force at TXID.  Subject:
; `fn-ks-redecide', whose plan and event host/owner-host.lisp
; fn-owner-key-statement-redecide-plan/-event compute over the live rows.
(defthm fn-ks-redecide-decides-under-the-configuration-at-its-own-txid
  (implies (and (fn-ctl-configs-all-through-p txid configs)
                (not (equal (fn-config-replay reserved ceiling configs) :fault)))
           (equal (fn-ks-redecide st msgid
                                  (fn-cfg-authorities
                                   (fn-cfg-value
                                    (fn-config-replay reserved ceiling configs)))
                                  observed ed ml sequence txid store-generation)
                  (fn-ks-redecide st msgid (fn-ks-redecide-rows txid configs)
                                  observed ed ml sequence txid
                                  store-generation)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ks-redecide-rows)
                           (fn-ks-redecide fn-ctl-config-at fn-config-replay
                            fn-ctl-configs-all-through-p))
           :use ((:instance fn-ks-config-replay-needs-a-true-list
                            (records configs))
                 fn-ctl-config-at-after-every-record-is-the-replay))))

; KEYSTONE (PRF-166 2: the next open repeats nothing).  After a redecide that
; acted, the open's recorded recovery -- under ANY journal, so under any
; configuration published later -- leaves the Store as the redecide left it;
; after one that did not act it is the recovery of the unchanged Store
; (PRF-124, PRF-140 apply as before).
(defthm fn-ks-reopen-after-a-redecide
  (equal (fn-ks-recover-recorded
          (fn-ks-redecide st msgid rows observed ed ml sequence txid
                          store-generation)
          configs observed2 ed2 ml2 sequence2 txid2 store-generation2)
         (if (fn-ks-redecide-event (fn-ks-find-statement msgid (car st))
                                   (cdr st) rows observed ed ml sequence txid
                                   store-generation)
             (fn-ks-redecide st msgid rows observed ed ml sequence txid
                             store-generation)
           (fn-ks-recover-recorded st configs observed2 ed2 ml2 sequence2
                                   txid2 store-generation2)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ks-redecide fn-ks-redecide-event)
                           (fn-ks-recover-recorded fn-ks-event
                            fn-ks-redecide-plan fn-ks-find-statement))
           :use ((:instance fn-ks-recover-recorded-without-a-pending-record
                            (st (fn-ks-redecide st msgid rows observed ed ml
                                                sequence txid store-generation))
                            (observed observed2) (ed ed2) (ml ml2)
                            (sequence sequence2) (txid txid2)
                            (store-generation store-generation2))
                 (:instance fn-ks-a-key-change-is-no-pending-statement
                            (plan (fn-ks-redecide-plan
                                   (fn-ks-find-statement msgid (car st))
                                   (cdr st) rows observed ed ml))
                            (snapshots (cdr st)))))))

(defthm fn-ks-find-statement-is-a-statement
  (implies (fn-ks-find-statement msgid records)
           (and (fn-ks-pending (fn-ks-find-statement msgid records))
                (equal (fn-ks-msgid (fn-ks-find-statement msgid records))
                       msgid)))
  :hints (("Goal" :in-theory (disable fn-ks-pending fn-ks-msgid))))

(defthm fn-ks-acted-p-needs-a-statement
  (implies (not (fn-ks-statement (fn-ks-source event)))
           (not (fn-ks-acted-p event snapshots)))
  :hints (("Goal" :in-theory (disable fn-ks-statement fn-ks-source))))

; KEYSTONE (PRF-166 3: refused by name, nothing changed).
(defthm fn-ks-redecide-of-no-stored-statement-is-refused-by-name
  (implies (not (fn-ks-find-statement msgid (car st)))
           (and (equal (fn-ks-redecide-plan (fn-ks-find-statement msgid (car st))
                                            (cdr st) rows observed ed ml)
                       '(:refused :not-a-key-statement))
                (equal (fn-ks-redecide st msgid rows observed ed ml sequence txid
                                       store-generation)
                       st)))
  :hints (("Goal" :in-theory (e/d (fn-ks-redecide fn-ks-redecide-event
                                   fn-ks-event)
                                  (fn-ks-find-statement)))))

; No separate "MSGID names a statement" hypothesis: an acted statement is one
; (fn-ks-acted-p-needs-a-statement).
(defthm fn-ks-redecide-of-an-acted-statement-is-refused-by-name
  (implies (fn-ks-acted-p (fn-ks-find-statement msgid (car st)) (cdr st))
           (and (equal (fn-ks-redecide-plan (fn-ks-find-statement msgid (car st))
                                            (cdr st) rows observed ed ml)
                       '(:refused :already-acted))
                (equal (fn-ks-redecide st msgid rows observed ed ml sequence txid
                                       store-generation)
                       st)))
  :hints (("Goal" :in-theory (e/d (fn-ks-redecide fn-ks-redecide-event
                                   fn-ks-event fn-ks-pending)
                                  (fn-ks-find-statement fn-ks-acted-p
                                   fn-ks-statement fn-ks-source))
           :cases ((fn-ks-find-statement msgid (car st)))
           :use ((:instance fn-ks-acted-p-needs-a-statement
                            (event (fn-ks-find-statement msgid (car st)))
                            (snapshots (cdr st)))))))

; KEYSTONE (PRF-166 4: a redecide is the acceptance's decision).  For a stored
; statement that has not acted, the redecide's plan and kind-3 event are
; exactly `fn-ks-plan' and `fn-ks-execute' of that statement -- so every
; PRF-098 keystone over them (acts only on a verified, granted statement about
; its own current principal, with a valid proof of possession) holds of it.
(defthm fn-ks-redecide-of-an-unacted-statement-is-its-acceptance-decision
  (let ((event (fn-ks-find-statement msgid records)))
    (implies (and event (not (fn-ks-acted-p event snapshots)))
             (and (equal (fn-ks-redecide-plan event snapshots rows observed ed
                                              ml)
                         (fn-ks-plan event snapshots rows observed ed ml))
                  (equal (fn-ks-redecide-event event snapshots rows observed ed
                                               ml sequence txid
                                               store-generation)
                         (fn-ks-execute event snapshots rows observed ed ml
                                        sequence txid store-generation)))))
  :hints (("Goal" :in-theory (e/d (fn-ks-execute)
                                  (fn-ks-find-statement fn-ks-acted-p
                                   fn-ks-plan)))))

(defthm fn-ks-statement-shape
  (let ((s (fn-ks-statement source)))
    (implies s (and (consp s) (true-listp s)
                    (member-equal (car s) '(:succession :revocation)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-ks-statement))))

(defthm fn-ks-acting-plan-is-the-statement-change
  (let ((plan (fn-ks-plan event snapshots rows observed ed ml))
        (s (fn-ks-statement (fn-ks-source event))))
    (and (implies (equal (car plan) :enroll)
                  (and (consp s) (true-listp s) (equal (car s) :succession)
                       (equal (nth 1 plan) (nth 1 s))
                       (equal (nth 2 plan) (nth 3 s))))
         (implies (equal (car plan) :revoke)
                  (and (consp s) (true-listp s) (equal (car s) :revocation)
                       (equal (nth 1 plan) (nth 1 s))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ks-plan)
                                  (fn-ks-statement fn-ks-source fn-ks-verdict
                                   fn-ks-msgid fn-ks-pop-source
                                   fn-hsig-authored-source-fields
                                   fn-ctl-authorize fn-hl-current-enrollment
                                   fn-hsig-authorize fn-stx-verdict-generation
                                   fn-stx-verdict-detail))
           :use ((:instance fn-ks-statement-shape
                            (source (fn-ks-source event)))))))

(defthm fn-ks-enrol-event-is-the-change
  (let ((ev (fn-hl-enroll-event sequence txid store-generation
                                (fn-hl-next-generation snapshots)
                                principal keys snapshots)))
    (implies (and ev (consp s) (true-listp s) (equal (car s) :succession)
                  (equal principal (nth 1 s)) (equal keys (nth 3 s)))
             (and (fn-stxk-p ev)
                  (equal (fn-stxk-keyring-generation ev)
                         (fn-hl-next-generation snapshots))
                  (fn-ks-change-snapshotp s ev))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-hl-enroll-event fn-ks-change-snapshotp
                                   fn-hl-snapshot-principal
                                   fn-hsig-keyring-event)
                                  (fn-hsig-keyring-snapshot-value
                                   fn-hl-next-generation))
           :use ((:instance fn-hsig-keyring-snapshot-value-of-keyring-event
                            (generation store-generation)
                            (keyring-generation (fn-hl-next-generation snapshots)))))))

(defthm fn-ks-revoke-event-is-the-change
  (let ((ev (fn-hl-revoke-event sequence txid store-generation
                                (fn-hl-next-generation snapshots)
                                principal snapshots)))
    (implies (and ev (consp s) (true-listp s) (equal (car s) :revocation)
                  (equal principal (nth 1 s)))
             (and (fn-stxk-p ev)
                  (equal (fn-stxk-keyring-generation ev)
                         (fn-hl-next-generation snapshots))
                  (fn-ks-change-snapshotp s ev))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-hl-revoke-event fn-ks-change-snapshotp
                                   fn-hl-snapshot-principal)
                                  (fn-hsig-keyring-snapshot-value
                                   fn-hl-next-generation))
           :use ((:instance fn-hsig-keyring-snapshot-value-requires-the-key-profile
                            (snapshot (fn-stxk-make sequence txid store-generation
                                                    (fn-hl-next-generation snapshots)
                                                    *fn-hl-revoked-profile*
                                                    principal)))))))

; KEYSTONE (PRF-166 5: an acted statement is recognized).  A redecide that
; committed its change leaves a Store in which the same MSGID is refused
; :already-acted, whatever the grants then (the statement's generation precedes
; the keyring's next one in every Store the owner serves).
(defthm fn-ks-a-redecide-that-acted-is-refused-the-second-time
  (let* ((event (fn-ks-find-statement msgid (car st)))
         (st2 (fn-ks-redecide st msgid rows observed ed ml sequence txid
                              store-generation)))
    (implies (and (fn-ks-redecide-event event (cdr st) rows observed ed ml
                                        sequence txid store-generation)
                  (< (nfix (fn-stx-verdict-generation (fn-ks-verdict event)))
                     (fn-hl-next-generation (cdr st))))
             (equal (fn-ks-redecide-plan (fn-ks-find-statement msgid (car st2))
                                         (cdr st2) rows2 observed2 ed2 ml2)
                    '(:refused :already-acted))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ks-redecide fn-ks-redecide-event fn-ks-event
                            fn-ks-redecide-plan fn-ks-acted-p fn-ks-acted-in
                            fn-ks-find-statement)
                           (fn-ks-plan fn-ks-statement fn-ks-source
                            fn-ks-verdict fn-ks-msgid fn-hl-enroll-event
                            fn-hl-revoke-event fn-ks-change-snapshotp
                            fn-hl-next-generation fn-ks-pending))
           :use ((:instance fn-ks-plan-shape (snapshots (cdr st))
                            (event (fn-ks-find-statement msgid (car st))))
                 (:instance fn-ks-acting-plan-is-the-statement-change
                            (snapshots (cdr st))
                            (event (fn-ks-find-statement msgid (car st))))
                 (:instance fn-ks-enrol-event-is-the-change
                            (snapshots (cdr st))
                            (s (fn-ks-statement (fn-ks-source (fn-ks-find-statement msgid (car st)))))
                            (principal (nth 1 (fn-ks-plan (fn-ks-find-statement msgid (car st)) (cdr st) rows observed ed ml)))
                            (keys (nth 2 (fn-ks-plan (fn-ks-find-statement msgid (car st)) (cdr st) rows observed ed ml))))
                 (:instance fn-ks-revoke-event-is-the-change
                            (snapshots (cdr st))
                            (s (fn-ks-statement (fn-ks-source (fn-ks-find-statement msgid (car st)))))
                            (principal (nth 1 (fn-ks-plan (fn-ks-find-statement msgid (car st)) (cdr st) rows observed ed ml))))
                 (:instance fn-ks-a-key-change-is-no-pending-statement
                            (plan (fn-ks-redecide-plan
                                   (fn-ks-find-statement msgid (car st))
                                   (cdr st) rows observed ed ml))
                            (snapshots (cdr st)))))))

(in-theory (disable (:d fn-ks-find-statement) (:d fn-ks-change-snapshotp)
                    (:d fn-ks-acted-in) (:d fn-ks-acted-p)
                    (:d fn-ks-redecide-plan) (:d fn-ks-redecide-event)
                    (:d fn-ks-redecide) (:d fn-ks-redecide-rows)))
