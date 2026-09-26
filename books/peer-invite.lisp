; fn: peering invitations -- issue, accept, confirm (PRF-097).
;
; Two nodes that share no key agree to peer by exchanging two signed
; documents: an invitation signed by the inviting node's principal, and an
; acceptance signed by the accepting node's principal.  Each document is an
; ordinary authored source carried by FN-Authorship (books/hybrid-carrier),
; whose body is `Key: value' lines.  This book owns every decision about
; them; the host reads files and keys, draws the nonce, reads the clock and
; makes the two primitive signature observations (specs/peering.md section 9).
;
;   issue    the inviter records the invitation it signed: a ninth-slot
;            configuration row keyed on the nonce (books/config.lisp
;            :issue-invitation), through the assured reconfiguration path.
;   accept   the invitee enrols the inviter's principal P with key set K only
;            if the invitation's carrier verifies under K, the body names P
;            and K, and P is the genesis identity of K and the body's token.
;   confirm  the inviter enrols the acceptor only if the acceptance verifies
;            under the key set it names, names P and K, and names a nonce this
;            node issued and has not consumed, the principal that signed that
;            invitation and that invitation's ACL2 authored-source identity.
;            The consumption is one configuration record (:consume-invitation)
;            published before the enrolment; a crash between the two leaves a
;            consumed row naming this very acceptance, and the next confirm of
;            it enrols without consuming again.
;
; What is not claimed: that a signature is unforgeable or a digest collision
; resistant (A-CRYPTO, books/crypto-seam.lisp); that the primitives observed
; what they report; that the operator holding the control socket is honest.

(in-package "ACL2")
(include-book "hybrid-lifecycle")
(include-book "native-hybrid-control")
(include-book "principal")
(include-book "injection")
(include-book "config")
; PRF-124: the peer record the confirm step configures.
(include-book "peer-config")

; -----------------------------------------------------------------------------
; Total selectors and octet helpers

(defun fn-pinv-at (i x)
  (declare (xargs :guard (natp i)))
  (if (atom x) nil
    (if (zp i) (car x) (fn-pinv-at (1- i) (cdr x)))))

(defun fn-pinv-tl (x)
  (declare (xargs :guard t))
  (if (true-listp x) x nil))

(defun fn-pinv-text (s)
  (declare (xargs :guard t))
  (fn-record-string-octets s))

(defun fn-pinv-hex (octets)
  ; Lowercase hexadecimal octets of an octet list, or nil.
  (declare (xargs :guard t))
  (if (fn-cbor-octet-listp octets) (fn-id-hex-octets octets) nil))

(defun fn-pinv-unhex (octets)
  ; The octets an even-length lowercase hexadecimal list spells, or nil.
  (declare (xargs :guard t))
  (if (and (fn-id-hex-listp octets) (evenp (len octets)))
      (fn-id-unhex octets)
    nil))

(defun fn-pinv-hex-string (octets)
  (declare (xargs :guard t))
  (fn-record-octets-string (fn-pinv-hex octets)))

(defun fn-pinv-ed (keys)
  (declare (xargs :guard t))
  (fn-cbor-ag-cdr (fn-cbor-ag-car keys)))

(defun fn-pinv-ml (keys)
  (declare (xargs :guard t))
  (fn-cbor-ag-cdr (fn-cbor-ag-car (fn-cbor-ag-cdr keys))))

; -----------------------------------------------------------------------------
; The body of a document: the octets after the first empty line, split into
; CRLF-terminated lines.  Work is linear in the source, which the carrier
; codec already bounds.

(defun fn-pinv-crlfp (x)
  (declare (xargs :guard t))
  (and (consp x) (equal (car x) 13) (consp (cdr x)) (equal (cadr x) 10)))

(defun fn-pinv-body (x)
  (declare (xargs :guard t))
  (if (atom x) nil
    (if (and (fn-pinv-crlfp x) (fn-pinv-crlfp (cddr x)))
        (cddddr x)
      (fn-pinv-body (cdr x)))))

(defun fn-pinv-line (x)
  (declare (xargs :guard t))
  (if (atom x) nil
    (if (fn-pinv-crlfp x) nil
      (cons (car x) (fn-pinv-line (cdr x))))))

(defun fn-pinv-rest (x)
  (declare (xargs :guard t))
  (if (atom x) nil
    (if (fn-pinv-crlfp x) (cddr x)
      (fn-pinv-rest (cdr x)))))

(defthm fn-pinv-rest-is-shorter
  (implies (consp x) (< (len (fn-pinv-rest x)) (len x)))
  :rule-classes :linear)

(defun fn-pinv-lines (x)
  (declare (xargs :guard t :measure (len x)))
  (if (consp x)
      (cons (fn-pinv-line x) (fn-pinv-lines (fn-pinv-rest x)))
    nil))

(defun fn-pinv-prefixp (p x)
  (declare (xargs :guard t))
  (if (consp p)
      (and (consp x) (equal (car p) (car x)) (fn-pinv-prefixp (cdr p) (cdr x)))
    t))

(defun fn-pinv-after (p x)
  (declare (xargs :guard t))
  (if (and (consp p) (consp x)) (fn-pinv-after (cdr p) (cdr x)) x))

(defun fn-pinv-lookup (key lines)
  (declare (xargs :guard t))
  (if (consp lines)
      (if (fn-pinv-prefixp key (car lines))
          (fn-pinv-after key (car lines))
        (fn-pinv-lookup key (cdr lines)))
    nil))

; "NAME: "
(defun fn-pinv-key (name)
  (declare (xargs :guard t))
  (append (fn-pinv-text name) '(58 32)))

; The value of the first body line `NAME: value', or nil.
(defun fn-pinv-field (name source)
  (declare (xargs :guard t))
  (fn-pinv-lookup (fn-pinv-key name) (fn-pinv-lines (fn-pinv-body source))))

; The specification a keystone states: the body HAS the line `NAME: VALUE'.
(defun fn-pinv-body-names-p (source name value)
  (declare (xargs :guard t))
  (and (consp value)
       (member-equal (append (fn-pinv-key name) value)
                     (fn-pinv-lines (fn-pinv-body source)))
       t))

(defthm fn-pinv-line-is-a-true-list
  (true-listp (fn-pinv-line x)))

(defthm fn-pinv-prefix-then-after-is-the-line
  (implies (and (fn-pinv-prefixp p x) (true-listp p))
           (equal (append p (fn-pinv-after p x)) x)))

(defthm fn-pinv-lookup-is-a-line
  (implies (and (consp (fn-pinv-lookup key lines))
                (true-listp key))
           (member-equal (append key (fn-pinv-lookup key lines)) lines)))

(defthm fn-pinv-field-is-a-body-line
  (implies (consp (fn-pinv-field name source))
           (fn-pinv-body-names-p source name (fn-pinv-field name source)))
  :hints (("Goal" :in-theory (e/d (fn-pinv-field fn-pinv-body-names-p)
                                  (fn-pinv-lines fn-pinv-body
                                                 fn-pinv-lookup-is-a-line))
           :use ((:instance fn-pinv-lookup-is-a-line
                            (key (fn-pinv-key name))
                            (lines (fn-pinv-lines (fn-pinv-body source))))))))

(in-theory (disable fn-pinv-field fn-pinv-body-names-p))

; -----------------------------------------------------------------------------
; Rendering a document's authored source.  Values are printable ASCII (32
; to 126), so no value can end a line or begin another field.

(defun fn-pinv-visiblep (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (integerp (car x)) (<= 32 (car x)) (<= (car x) 126)
           (fn-pinv-visiblep (cdr x)))
    (null x)))

(defun fn-pinv-valuep (x)
  (declare (xargs :guard t))
  (and (consp x) (fn-pinv-visiblep x)))

(defun fn-pinv-values-p (fields)
  (declare (xargs :guard t))
  (if (consp fields)
      (and (consp (car fields))
           (stringp (caar fields))
           (fn-pinv-valuep (cdar fields))
           (fn-pinv-values-p (cdr fields)))
    (null fields)))

(defun fn-pinv-render-lines (fields)
  (declare (xargs :guard (fn-pinv-values-p fields)))
  (if (consp fields)
      (append (fn-pinv-key (caar fields)) (cdar fields) '(13 10)
              (fn-pinv-render-lines (cdr fields)))
    nil))

(defconst *fn-pinv-group* "fn.peering")
(defconst *fn-pinv-invitation-kind* "invitation fn-peering-v1")
(defconst *fn-pinv-acceptance-kind* "acceptance fn-peering-v1")

; DATE-MS is the wall reading in milliseconds since 2000-01-01 (the DTN
; epoch the owner's clock uses); the Date field is RFC 5536's 31 octets.
(defun fn-pinv-source (subject msgid date-ms fields)
  (declare (xargs :guard t))
  (if (not (and (fn-pinv-values-p fields) (natp date-ms)
                (fn-pinv-valuep msgid)))
      nil
    (append (fn-pinv-text "From: fn-peering@fn-peering.invalid")
            '(13 10)
            (fn-pinv-text "Date: ") (fn-inj-date-octets (fn-inj-instant-of date-ms))
            '(13 10)
            (fn-pinv-text "Newsgroups: ") (fn-pinv-text *fn-pinv-group*) '(13 10)
            (fn-pinv-text "Subject: ") (fn-pinv-text subject) '(13 10)
            (fn-pinv-text "Message-ID: ") msgid '(13 10 13 10)
            (fn-pinv-render-lines fields))))

; -----------------------------------------------------------------------------
; A received document: the carrier decoded by ACL2, and the verified source.

(defun fn-pinv-received-source (received)
  (declare (xargs :guard t))
  (let ((plan (fn-hc-received-plan received)))
    (if (fn-hc-okp plan) (fn-pinv-at 0 (fn-hc-value plan)) nil)))

(defun fn-pinv-received-carrier (received)
  (declare (xargs :guard t))
  (let ((plan (fn-hc-received-plan received)))
    (if (fn-hc-okp plan) (fn-pinv-at 1 (fn-hc-value plan)) nil)))

(defun fn-pinv-received-principal (received)
  (declare (xargs :guard t))
  (fn-pinv-at 0 (fn-pinv-received-carrier received)))

(defun fn-pinv-received-keys (received)
  (declare (xargs :guard t))
  (fn-pinv-at 1 (fn-pinv-received-carrier received)))

(defun fn-pinv-received-signatures (received)
  (declare (xargs :guard t))
  (fn-pinv-at 2 (fn-pinv-received-carrier received)))

; What the host must observe: (:observe principal keys preimage signatures),
; the preimage over the carrier's own key set.  The observations answer
; whether the carrier verifies under the key set it names.
(defun fn-pinv-observation-subject (received)
  (declare (xargs :guard t))
  (let* ((source (fn-pinv-received-source received))
         (principal (fn-pinv-received-principal received))
         (keys (fn-pinv-received-keys received))
         (version (fn-hsig-source-version source)))
    (if (and (fn-hc-okp (fn-hc-received-plan received))
             (fn-hsig-subject-at-p version principal keys source))
        (list :observe principal keys
              (fn-hsig-signed-preimage-at version principal keys source)
              (fn-pinv-received-signatures received))
      (list :refused :carrier))))

; The carrier verifies under the key set it names: ACL2's selected-profile
; conjunction over the two primitive observations.
(defun fn-pinv-verifiedp (received observed-ml ed-observation ml-observation)
  (declare (xargs :guard t))
  (let ((source (fn-pinv-received-source received)))
    (and (fn-hc-okp (fn-hc-received-plan received))
         (fn-hsig-authorize-at (fn-hsig-source-version source)
                               (fn-pinv-received-principal received)
                               (fn-pinv-received-keys received)
                               source
                               (fn-pinv-received-signatures received)
                               observed-ml ed-observation ml-observation)
         t)))

; The body names the carrier's principal and both of its keys.
(defun fn-pinv-names-keysp (source principal keys)
  (declare (xargs :guard t))
  (and (equal (fn-pinv-field "Principal" source) (fn-pinv-hex principal))
       (equal (fn-pinv-field "Ed25519" source) (fn-pinv-hex (fn-pinv-ed keys)))
       (equal (fn-pinv-field "ML-DSA-65" source)
              (fn-pinv-hex (fn-pinv-ml keys)))
       (consp (fn-pinv-hex principal))
       (consp (fn-pinv-hex (fn-pinv-ed keys)))
       (consp (fn-pinv-hex (fn-pinv-ml keys)))))

; The genesis binding (books/principal.lisp): the principal is the tagged
; digest of the key set's two public keys and the body's Genesis-Token.
(defun fn-pinv-genesis-key (keys)
  (declare (xargs :guard t))
  (if (true-listp (fn-pinv-ed keys))
      (append (fn-pinv-ed keys) (fn-pinv-ml keys))
    nil))

(defun fn-pinv-genesis-token (source)
  (declare (xargs :guard t))
  (fn-pinv-unhex (fn-pinv-field "Genesis-Token" source)))

(defun fn-pinv-genesis-okp (source principal keys)
  (declare (xargs :guard t))
  (let ((pk (fn-pinv-genesis-key keys))
        (token (fn-pinv-genesis-token source)))
    (and (fn-sig-public-key-p pk)
         (fn-prin-tokenp token)
         (fn-prin-genesis-bindsp principal pk token))))

; The principal a key set and token name: what `peer genesis' writes.
(defun fn-pinv-genesis-principal (ed ml token)
  (declare (xargs :guard t))
  (if (and (fn-hsig-exact-octets-p ed *fn-hsig-ed25519-public-key-octets*)
           (fn-hsig-exact-octets-p ml *fn-hsig-ml-dsa-65-public-key-octets*)
           (true-listp ed)
           (fn-sig-public-key-p (append ed ml))
           (fn-prin-tokenp token))
      (fn-prin-id (append ed ml) token)
    nil))

(defun fn-pinv-kindp (source kind)
  (declare (xargs :guard t))
  (equal (fn-pinv-field "FN-Peering" source) (fn-pinv-text kind)))

(defun fn-pinv-hex-fieldp (value n)
  (declare (xargs :guard (natp n)))
  (and (fn-id-hex-listp value) (equal (len value) n)))

; The checks both documents share.  (:ok source principal keys) or
; (:refused reason).
(defun fn-pinv-document (received observed-ml ed ml kind)
  (declare (xargs :guard t))
  (let* ((source (fn-pinv-received-source received))
         (principal (fn-pinv-received-principal received))
         (keys (fn-pinv-received-keys received)))
    (cond ((not (fn-pinv-verifiedp received observed-ml ed ml))
           (list :refused :unverified))
          ((not (fn-pinv-kindp source kind)) (list :refused :document-kind))
          ((not (fn-pinv-names-keysp source principal keys))
           (list :refused :claimed-keys))
          ((not (fn-pinv-genesis-okp source principal keys))
           (list :refused :genesis))
          ((not (fn-pinv-hex-fieldp (fn-pinv-field "Nonce" source) 32))
           (list :refused :nonce))
          (t (list :ok source principal keys)))))

; -----------------------------------------------------------------------------
; Issue (the inviter).  The invitation the operator signed becomes one
; :issue-invitation row: the nonce, the principal that signed it, and its
; authored-source identity.

; PRF-160: the last two lines are the inviter's own reachable address, so the
; accepting node can configure the inviter as a peer; `-' in both says the
; inviter gave none (the accept then enrols and configures nothing, as
; before).  They are signed body lines like the rest: the address is the
; inviter principal's statement, not the carrier's.
(defun fn-pinv-invitation-fields (nonce principal token keys name path groups
                                        host port inviter-host inviter-port)
  (declare (xargs :guard t))
  (list (cons "FN-Peering" (fn-pinv-text *fn-pinv-invitation-kind*))
        (cons "Nonce" (fn-pinv-hex nonce))
        (cons "Principal" (fn-pinv-hex principal))
        (cons "Genesis-Token" (if (consp token) (fn-pinv-hex token) '(45)))
        (cons "Ed25519" (fn-pinv-hex (fn-pinv-ed keys)))
        (cons "ML-DSA-65" (fn-pinv-hex (fn-pinv-ml keys)))
        (cons "Invitee" name)
        (cons "Inviter-Path" path)
        (cons "Groups" groups)
        (cons "Host" host)
        (cons "Port" port)
        (cons "Inviter-Host" inviter-host)
        (cons "Inviter-Port" inviter-port)))

(defun fn-pinv-invitation-source (date-ms nonce principal token keys name path
                                          groups host port inviter-host
                                          inviter-port)
  (declare (xargs :guard t))
  (fn-pinv-source "fn-invitation"
                  (append (fn-pinv-text "<fn-invite-") (fn-pinv-hex nonce)
                          (fn-pinv-text "@fn-peering.invalid>"))
                  date-ms
                  (fn-pinv-invitation-fields nonce principal token keys name
                                             path groups host port
                                             inviter-host inviter-port)))

(defun fn-pinv-source-id (source)
  (declare (xargs :guard t))
  (fn-hsig-authored-source-id source))

(defun fn-pinv-issue-plan (received observed-ml ed ml invitations)
  (declare (xargs :guard t))
  (let ((doc (fn-pinv-document received observed-ml ed ml
                               *fn-pinv-invitation-kind*)))
    (if (not (equal (car doc) :ok)) doc
      (let* ((source (fn-pinv-at 1 doc))
             (nonce (fn-record-octets-string (fn-pinv-field "Nonce" source)))
             (sid (fn-pinv-source-id source)))
        (cond ((not (fn-hsig-exact-octets-p sid 48)) (list :refused :source-id))
              ((consp (fn-cfg-rows-with-key invitations nonce))
               (list :refused :invitation-nonce-reused))
              (t (list :issue
                       (fn-cfg-issue-invitation
                        nonce (fn-pinv-hex-string (fn-pinv-at 2 doc))
                        (fn-pinv-hex-string sid)))))))))

; -----------------------------------------------------------------------------
; Accept (the invitee)

(defun fn-pinv-accept-plan (received observed-ml ed ml)
  ; (:enrol principal keys nonce-hex invitation-source-id) or (:refused why)
  (declare (xargs :guard t))
  (let ((doc (fn-pinv-document received observed-ml ed ml
                               *fn-pinv-invitation-kind*)))
    (if (not (equal (car doc) :ok)) doc
      (let* ((source (fn-pinv-at 1 doc))
             (sid (fn-pinv-source-id source)))
        (if (not (fn-hsig-exact-octets-p sid 48))
            (list :refused :source-id)
          (list :enrol (fn-pinv-at 2 doc) (fn-pinv-at 3 doc)
                (fn-pinv-field "Nonce" source) sid))))))

; This node's keyring already holds exactly this enrolment as P's current one.
(defun fn-pinv-enrolled-withp (principal keys snapshots)
  (declare (xargs :guard t))
  (let ((value (fn-hsig-keyring-snapshot-value
                (fn-hl-current-for-principal principal snapshots))))
    (and (consp value)
         (equal (fn-pinv-at 0 value) principal)
         (equal (fn-pinv-at 1 value) keys))))

; The owner's accept step: the kind-3 enrolment at ACL2's next generation,
; or (:refused why).  host/native/peer-invite.lisp calls it.
(defun fn-pinv-accept-step (sequence txid generation received observed-ml ed ml
                                     snapshots)
  (declare (xargs :guard t))
  (let ((plan (fn-pinv-accept-plan received observed-ml ed ml)))
    (cond ((not (equal (car plan) :enrol)) plan)
          ((fn-pinv-enrolled-withp (fn-pinv-at 1 plan) (fn-pinv-at 2 plan)
                                   snapshots)
           (list :refused :already-enrolled))
          (t (let ((event (fn-hl-enroll-event sequence txid generation
                                              (fn-hl-next-generation snapshots)
                                              (fn-pinv-at 1 plan)
                                              (fn-pinv-at 2 plan)
                                              snapshots)))
               (if event (list :enrol event) (list :refused :event)))))))

(defun fn-pinv-acceptance-fields (nonce invitation-sid inviter principal token
                                        keys path reachable)
  (declare (xargs :guard t))
  (list (cons "FN-Peering" (fn-pinv-text *fn-pinv-acceptance-kind*))
        (cons "Nonce" nonce)
        (cons "Invitation-Source-Id" (fn-pinv-hex invitation-sid))
        (cons "Inviter-Principal" (fn-pinv-hex inviter))
        (cons "Principal" (fn-pinv-hex principal))
        (cons "Genesis-Token" (if (consp token) (fn-pinv-hex token) '(45)))
        (cons "Ed25519" (fn-pinv-hex (fn-pinv-ed keys)))
        (cons "ML-DSA-65" (fn-pinv-hex (fn-pinv-ml keys)))
        (cons "Acceptor-Path" path)
        (cons "Reachable" reachable)))

; The acceptance's authored source, from the accept plan of the invitation
; it answers: its nonce, its source identity and its principal are the ones
; the plan verified, never words the host supplies.
(defun fn-pinv-acceptance-source (date-ms received observed-ml ed ml principal
                                          token keys path reachable)
  (declare (xargs :guard t))
  (let ((plan (fn-pinv-accept-plan received observed-ml ed ml)))
    (if (not (equal (car plan) :enrol)) nil
      (fn-pinv-source "fn-acceptance"
                      (append (fn-pinv-text "<fn-accept-") (fn-pinv-tl (fn-pinv-at 3 plan))
                              (fn-pinv-text "@fn-peering.invalid>"))
                      date-ms
                      (fn-pinv-acceptance-fields
                       (fn-pinv-at 3 plan) (fn-pinv-at 4 plan)
                       (fn-pinv-at 1 plan) principal token keys path
                       reachable)))))

; -----------------------------------------------------------------------------
; Confirm (the inviter)

(defun fn-pinv-acceptance (received observed-ml ed ml)
  (declare (xargs :guard t))
  (let ((doc (fn-pinv-document received observed-ml ed ml
                               *fn-pinv-acceptance-kind*)))
    (cond ((not (equal (car doc) :ok)) doc)
          ((not (fn-pinv-hex-fieldp
                 (fn-pinv-field "Invitation-Source-Id" (fn-pinv-at 1 doc)) 96))
           (list :refused :invitation-source-id))
          ((not (fn-pinv-hex-fieldp
                 (fn-pinv-field "Inviter-Principal" (fn-pinv-at 1 doc)) 64))
           (list :refused :inviter-principal))
          ((not (fn-hsig-exact-octets-p (fn-pinv-source-id (fn-pinv-at 1 doc))
                                        48))
           (list :refused :source-id))
          (t doc))))

; (:consume delta) | (:enrol principal keys) | (:refused why).
(defun fn-pinv-confirm-plan (received observed-ml ed ml invitations snapshots)
  (declare (xargs :guard t))
  (let ((doc (fn-pinv-acceptance received observed-ml ed ml)))
    (if (not (equal (car doc) :ok)) doc
      (let* ((source (fn-pinv-at 1 doc))
             (principal (fn-pinv-at 2 doc))
             (keys (fn-pinv-at 3 doc))
             (nonce (fn-record-octets-string (fn-pinv-field "Nonce" source)))
             (acceptor (fn-pinv-hex-string principal))
             (asid (fn-pinv-hex-string (fn-pinv-source-id source)))
             (row (fn-cfg-invitation-row invitations nonce)))
        (cond
         ((not (consp row)) (list :refused :no-such-invitation))
         ((equal (fn-cfg-row-n row) 0)
          (cond ((not (equal (fn-cfg-row-b row)
                             (fn-record-octets-string
                              (fn-pinv-field "Inviter-Principal" source))))
                 (list :refused :another-inviter))
                ((not (equal (fn-cfg-row-c row)
                             (fn-record-octets-string
                              (fn-pinv-field "Invitation-Source-Id" source))))
                 (list :refused :another-invitation))
                (t (list :consume
                         (fn-cfg-consume-invitation nonce acceptor asid)))))
         ((and (equal (fn-cfg-row-n row) 1)
               (equal (fn-cfg-row-b row) acceptor)
               (equal (fn-cfg-row-c row) asid))
          (if (fn-pinv-enrolled-withp principal keys snapshots)
              (list :refused :already-confirmed)
            (list :enrol principal keys)))
         (t (list :refused :invitation-consumed)))))))

; The owner's enrolment for a confirmed acceptance.  It is asked after the
; consumption is durable (and again after a crash): only a row consumed by
; exactly this acceptance yields an event.
(defun fn-pinv-confirm-step (sequence txid generation received observed-ml ed
                                      ml invitations snapshots)
  (declare (xargs :guard t))
  (let ((plan (fn-pinv-confirm-plan received observed-ml ed ml invitations
                                    snapshots)))
    (if (not (equal (car plan) :enrol)) plan
      (let ((event (fn-hl-enroll-event sequence txid generation
                                       (fn-hl-next-generation snapshots)
                                       (fn-pinv-at 1 plan) (fn-pinv-at 2 plan)
                                       snapshots)))
        (if event (list :enrol event) (list :refused :event))))))

; -----------------------------------------------------------------------------
; Keystones.  From here the definitions are closed; each proof opens what it
; decodes.

(in-theory (disable fn-pinv-accept-plan fn-pinv-accept-step
                    fn-pinv-confirm-plan fn-pinv-confirm-step
                    fn-pinv-issue-plan fn-pinv-document fn-pinv-acceptance
                    fn-pinv-verifiedp fn-pinv-names-keysp fn-pinv-genesis-okp
                    fn-pinv-enrolled-withp fn-pinv-received-source
                    fn-pinv-received-principal fn-pinv-received-keys
                    fn-pinv-received-signatures fn-pinv-received-carrier
                    fn-pinv-kindp fn-pinv-hex-fieldp fn-pinv-source-id
                    fn-hl-enroll-event fn-hl-next-generation
                    fn-hsig-authorize-at fn-hc-received-plan
                    fn-prin-genesis-bindsp fn-pinv-genesis-key
                    fn-pinv-genesis-token fn-pinv-hex fn-pinv-hex-string
                    fn-hsig-authored-source-id fn-hsig-exact-octets-p))

; The shared checks answer :ok or :refused and nothing a plan answers.
(defthm fn-pinv-document-answers-no-plan
  (and (not (equal (car (fn-pinv-document received observed-ml ed ml kind))
                   :enrol))
       (not (equal (car (fn-pinv-document received observed-ml ed ml kind))
                   :issue))
       (not (equal (car (fn-pinv-document received observed-ml ed ml kind))
                   :consume)))
  :hints (("Goal" :in-theory (enable fn-pinv-document))))

(defthm fn-pinv-acceptance-answers-no-plan
  (and (not (equal (car (fn-pinv-acceptance received observed-ml ed ml))
                   :enrol))
       (not (equal (car (fn-pinv-acceptance received observed-ml ed ml))
                   :consume)))
  :hints (("Goal" :in-theory (enable fn-pinv-acceptance))))

; What a document that passed the shared checks is bound to: the carrier
; verifies under the key set it names (ACL2's conjunction over the two
; observations), the body has the kind line and names the principal and
; both keys, and the principal is the genesis identity of the keys.
(defun fn-pinv-bound-document-p (received observed-ml ed ml kind)
  (declare (xargs :guard t))
  (let* ((source (fn-pinv-received-source received))
         (principal (fn-pinv-received-principal received))
         (keys (fn-pinv-received-keys received)))
    (and (fn-hsig-authorize-at (fn-hsig-source-version source) principal keys
                               source (fn-pinv-received-signatures received)
                               observed-ml ed ml)
         (fn-pinv-body-names-p source "FN-Peering" (fn-pinv-text kind))
         (fn-pinv-body-names-p source "Principal" (fn-pinv-hex principal))
         (fn-pinv-body-names-p source "Ed25519"
                               (fn-pinv-hex (fn-pinv-ed keys)))
         (fn-pinv-body-names-p source "ML-DSA-65"
                               (fn-pinv-hex (fn-pinv-ml keys)))
         (fn-sig-public-key-p (fn-pinv-genesis-key keys))
         (fn-prin-tokenp (fn-pinv-genesis-token source))
         (fn-prin-genesis-bindsp principal (fn-pinv-genesis-key keys)
                                 (fn-pinv-genesis-token source))
         (fn-pinv-body-names-p source "Nonce" (fn-pinv-field "Nonce" source)))))

(defthm fn-pinv-document-ok-is-bound
  (implies (and (equal (car (fn-pinv-document received observed-ml ed ml kind))
                      :ok)
                (consp (fn-pinv-text kind)))
           (and (fn-pinv-bound-document-p received observed-ml ed ml kind)
                (equal (fn-pinv-at 1 (fn-pinv-document received observed-ml ed
                                                       ml kind))
                       (fn-pinv-received-source received))
                (equal (fn-pinv-at 2 (fn-pinv-document received observed-ml ed
                                                       ml kind))
                       (fn-pinv-received-principal received))
                (equal (fn-pinv-at 3 (fn-pinv-document received observed-ml ed
                                                       ml kind))
                       (fn-pinv-received-keys received))))
  :hints (("Goal"
           :in-theory (e/d (fn-pinv-document fn-pinv-verifiedp
                                             fn-pinv-names-keysp
                                             fn-pinv-genesis-okp fn-pinv-kindp
                                             fn-pinv-hex-fieldp)
                           (fn-pinv-field-is-a-body-line))
           :use ((:instance fn-pinv-field-is-a-body-line
                            (name "FN-Peering")
                            (source (fn-pinv-received-source received)))
                 (:instance fn-pinv-field-is-a-body-line
                            (name "Principal")
                            (source (fn-pinv-received-source received)))
                 (:instance fn-pinv-field-is-a-body-line
                            (name "Ed25519")
                            (source (fn-pinv-received-source received)))
                 (:instance fn-pinv-field-is-a-body-line
                            (name "ML-DSA-65")
                            (source (fn-pinv-received-source received)))
                 (:instance fn-pinv-field-is-a-body-line
                            (name "Nonce")
                            (source (fn-pinv-received-source received)))))))

(in-theory (disable fn-pinv-bound-document-p))

; KEYSTONE (accept, theorem 1).  The owner's accept step enrols principal P
; with key set K -- its event is the kind-3 enrolment of exactly P and K at
; ACL2's next generation -- only if the invitation's carrier verifies under
; K and its body names P and K, P being K's genesis identity.  Called by
; host/native/peer-invite.lisp `fnn-pinv-owner-accept'.
(defthm fn-pinv-accept-step-enrols-only-a-bound-invitation
  (let ((step (fn-pinv-accept-step sequence txid generation received
                                   observed-ml ed ml snapshots)))
    (implies (equal (car step) :enrol)
             (and (fn-pinv-bound-document-p received observed-ml ed ml
                                            *fn-pinv-invitation-kind*)
                  (not (fn-pinv-enrolled-withp
                        (fn-pinv-received-principal received)
                        (fn-pinv-received-keys received) snapshots))
                  (equal (fn-pinv-at 1 step)
                         (fn-hl-enroll-event
                          sequence txid generation
                          (fn-hl-next-generation snapshots)
                          (fn-pinv-received-principal received)
                          (fn-pinv-received-keys received) snapshots))
                  (fn-pinv-at 1 step))))
  :hints (("Goal" :in-theory (enable fn-pinv-accept-step fn-pinv-accept-plan)
           :use ((:instance fn-pinv-document-ok-is-bound
                            (kind *fn-pinv-invitation-kind*))))))

; KEYSTONE (issue).  An issued row records the nonce the body names, the
; principal whose carrier verified, and that invitation's source identity.
(defthm fn-pinv-issue-plan-records-the-signed-invitation
  (let ((plan (fn-pinv-issue-plan received observed-ml ed ml invitations))
        (source (fn-pinv-received-source received)))
    (implies (equal (car plan) :issue)
             (and (fn-pinv-bound-document-p received observed-ml ed ml
                                            *fn-pinv-invitation-kind*)
                  (not (consp (fn-cfg-rows-with-key
                               invitations
                               (fn-record-octets-string
                                (fn-pinv-field "Nonce" source)))))
                  (equal (fn-pinv-at 1 plan)
                         (fn-cfg-issue-invitation
                          (fn-record-octets-string
                           (fn-pinv-field "Nonce" source))
                          (fn-pinv-hex-string
                           (fn-pinv-received-principal received))
                          (fn-pinv-hex-string (fn-pinv-source-id source)))))))
  :hints (("Goal" :in-theory (enable fn-pinv-issue-plan)
           :use ((:instance fn-pinv-document-ok-is-bound
                            (kind *fn-pinv-invitation-kind*))))))

; What confirm binds an acceptance to, beyond its own document checks: the
; invitation row its Nonce keys names the Inviter-Principal and the
; Invitation-Source-Id the body carries.
(defun fn-pinv-acceptance-names-row-p (source row)
  (declare (xargs :guard t))
  (and (fn-pinv-body-names-p source "Inviter-Principal"
                             (fn-pinv-field "Inviter-Principal" source))
       (equal (fn-cfg-row-b row)
              (fn-record-octets-string
               (fn-pinv-field "Inviter-Principal" source)))
       (fn-pinv-body-names-p source "Invitation-Source-Id"
                             (fn-pinv-field "Invitation-Source-Id" source))
       (equal (fn-cfg-row-c row)
              (fn-record-octets-string
               (fn-pinv-field "Invitation-Source-Id" source)))))

(defthm fn-pinv-acceptance-ok-is-a-document
  (implies (equal (car (fn-pinv-acceptance received observed-ml ed ml)) :ok)
           (and (equal (fn-pinv-acceptance received observed-ml ed ml)
                       (fn-pinv-document received observed-ml ed ml
                                         *fn-pinv-acceptance-kind*))
                (consp (fn-pinv-field "Inviter-Principal"
                                      (fn-pinv-received-source received)))
                (consp (fn-pinv-field "Invitation-Source-Id"
                                      (fn-pinv-received-source received)))))
  :hints (("Goal" :in-theory (enable fn-pinv-acceptance fn-pinv-hex-fieldp)
           :use ((:instance fn-pinv-document-ok-is-bound
                            (kind *fn-pinv-acceptance-kind*))))))

; KEYSTONE (confirm, the consumption).  Confirm consumes an invitation only
; for an acceptance bound to its key set, and only an invitation this node
; issued that is still pending, naming the principal that signed it and its
; authored-source identity.  The delta names the acceptor and the
; acceptance's own source identity.  Called by `fnn-pinv-owner-confirm'.
(defthm fn-pinv-confirm-consumes-only-a-pending-named-invitation
  (let* ((plan (fn-pinv-confirm-plan received observed-ml ed ml invitations
                                     snapshots))
         (source (fn-pinv-received-source received))
         (nonce (fn-record-octets-string (fn-pinv-field "Nonce" source)))
         (row (fn-cfg-invitation-row invitations nonce)))
    (implies (equal (car plan) :consume)
             (and (fn-pinv-bound-document-p received observed-ml ed ml
                                            *fn-pinv-acceptance-kind*)
                  (fn-cfg-invitation-pendingp invitations nonce)
                  (fn-pinv-acceptance-names-row-p source row)
                  (equal (fn-pinv-at 1 plan)
                         (fn-cfg-consume-invitation
                          nonce
                          (fn-pinv-hex-string
                           (fn-pinv-received-principal received))
                          (fn-pinv-hex-string (fn-pinv-source-id source)))))))
  :hints (("Goal" :in-theory (e/d (fn-pinv-confirm-plan
                                   fn-cfg-invitation-pendingp)
                                  (fn-pinv-field-is-a-body-line
                                   fn-pinv-acceptance-ok-is-a-document))
           :use ((:instance fn-pinv-acceptance-ok-is-a-document)
                 (:instance fn-pinv-document-ok-is-bound
                            (kind *fn-pinv-acceptance-kind*))
                 (:instance fn-pinv-field-is-a-body-line
                            (name "Inviter-Principal")
                            (source (fn-pinv-received-source received)))
                 (:instance fn-pinv-field-is-a-body-line
                            (name "Invitation-Source-Id")
                            (source (fn-pinv-received-source received)))))))

; KEYSTONE (confirm, the enrolment).  The owner's confirm step enrols the
; acceptor's principal P with key set K only if the acceptance is bound to
; K and names P and K, and the invitation row its nonce keys was consumed
; by exactly this acceptance: P and this acceptance's source identity.
; Called by `fnn-pinv-owner-confirm' after the consumption is durable.
(defthm fn-pinv-confirm-step-enrols-only-the-consuming-acceptance
  (let* ((step (fn-pinv-confirm-step sequence txid generation received
                                     observed-ml ed ml invitations snapshots))
         (source (fn-pinv-received-source received))
         (nonce (fn-record-octets-string (fn-pinv-field "Nonce" source)))
         (row (fn-cfg-invitation-row invitations nonce)))
    (implies (equal (car step) :enrol)
             (and (fn-pinv-bound-document-p received observed-ml ed ml
                                            *fn-pinv-acceptance-kind*)
                  (consp row)
                  (equal (fn-cfg-row-n row) 1)
                  (equal (fn-cfg-row-b row)
                         (fn-pinv-hex-string
                          (fn-pinv-received-principal received)))
                  (equal (fn-cfg-row-c row)
                         (fn-pinv-hex-string (fn-pinv-source-id source)))
                  (not (fn-pinv-enrolled-withp
                        (fn-pinv-received-principal received)
                        (fn-pinv-received-keys received) snapshots))
                  (equal (fn-pinv-at 1 step)
                         (fn-hl-enroll-event
                          sequence txid generation
                          (fn-hl-next-generation snapshots)
                          (fn-pinv-received-principal received)
                          (fn-pinv-received-keys received) snapshots))
                  (fn-pinv-at 1 step))))
  :hints (("Goal" :in-theory (e/d (fn-pinv-confirm-step fn-pinv-confirm-plan)
                                  (fn-pinv-acceptance-ok-is-a-document))
           :use ((:instance fn-pinv-acceptance-ok-is-a-document)
                 (:instance fn-pinv-document-ok-is-bound
                            (kind *fn-pinv-acceptance-kind*))))))

; -----------------------------------------------------------------------------
; Once-only consumption, over the configuration the owner replays.

(defun fn-cfg-invitation-consumedp (rows nonce)
  (declare (xargs :guard t))
  (let ((row (fn-cfg-invitation-row rows nonce)))
    (and (consp row) (not (equal (fn-cfg-row-n row) 0)))))

(defthm fn-pinv-rows-with-key-of-append
  (equal (fn-cfg-rows-with-key (append a b) k)
         (append (fn-cfg-rows-with-key a k) (fn-cfg-rows-with-key b k)))
  :hints (("Goal" :in-theory (enable fn-cfg-rows-with-key))))

(defthm fn-pinv-rows-with-key-of-rows-without-key
  (equal (fn-cfg-rows-with-key (fn-cfg-rows-without-key rows k) k) nil)
  :hints (("Goal" :in-theory (enable fn-cfg-rows-with-key
                                     fn-cfg-rows-without-key))))

(defthm fn-pinv-rows-with-other-key-of-rows-without-key
  (implies (not (equal j k))
           (equal (fn-cfg-rows-with-key (fn-cfg-rows-without-key rows j) k)
                  (fn-cfg-rows-with-key rows k)))
  :hints (("Goal" :in-theory (enable fn-cfg-rows-with-key
                                     fn-cfg-rows-without-key))))

(defthm fn-pinv-first-row-kept-by-append
  (implies (consp (fn-cfg-rows-with-key a k))
           (equal (fn-cfg-ag-car (append (fn-cfg-rows-with-key a k) b))
                  (fn-cfg-ag-car (fn-cfg-rows-with-key a k))))
  :hints (("Goal" :in-theory (enable fn-cfg-ag-car))))

(defthm fn-pinv-invitations-of-apply-delta
  (equal (fn-cfg-invitations (fn-cfg-apply-delta v gen stamp d))
         (if (or (equal (fn-cfg-delta-kind d) :issue-invitation)
                 (equal (fn-cfg-delta-kind d) :consume-invitation))
             (append (fn-cfg-rows-without-key (fn-cfg-invitations v)
                                              (fn-cfg-delta-a d))
                     (fn-cfg-delta-rows d))
           (fn-cfg-invitations v)))
  :hints (("Goal" :in-theory (enable fn-cfg-apply-delta fn-cfg-set-groups))))

; An admitted delta keeps a consumed invitation consumed: the issue and
; consume kinds touch another nonce only (reuse and non-pending are refused),
; and no other kind writes the slot.
(defthm fn-pinv-consumed-stays-consumed-by-a-delta
  (implies (and (fn-cfg-invitation-consumedp (fn-cfg-invitations v) nonce)
                (not (fn-cfg-delta-reason v gen stamp reserved ceiling d)))
           (fn-cfg-invitation-consumedp
            (fn-cfg-invitations (fn-cfg-apply-delta v gen stamp d)) nonce))
  :hints (("Goal" :in-theory (enable fn-cfg-delta-reason
                                     fn-cfg-invitation-consumedp
                                     fn-cfg-invitation-row
                                     fn-cfg-invitation-pendingp
                                     fn-cfg-ag-car)
           :cases ((equal (fn-cfg-delta-a d) nonce)))))

(defthm fn-pinv-consumed-stays-consumed
  (implies (and (fn-cfg-invitation-consumedp (fn-cfg-invitations v) nonce)
                (fn-cfg-admissiblep v gen stamp reserved ceiling deltas))
           (fn-cfg-invitation-consumedp
            (fn-cfg-invitations (fn-cfg-apply v gen stamp deltas)) nonce))
  :hints (("Goal" :induct (fn-cfg-apply v gen stamp deltas)
           :in-theory (e/d (fn-cfg-admissiblep fn-cfg-admissible-reason
                                               fn-cfg-apply)
                           (fn-cfg-invitation-consumedp fn-cfg-delta-reason
                                                        fn-cfg-apply-delta
                                                        fn-pinv-invitations-of-apply-delta)))))

; KEYSTONE (once only).  Across the configuration history the owner replays
; at open, an invitation consumed by one record stays consumed after every
; later acceptable record; a consumed invitation refuses every further
; consumption (`fn-pinv-consumed-refuses-consumption').  Subject: the replay
; fold `fn-config-replay-loop' and the admission `fn-cfg-delta-reason' that
; `fn-ocfg-step' and replay call.
(defthm fn-pinv-consumed-stays-consumed-across-replay
  (implies (and (fn-cfgp cfg)
                (fn-cfg-invitation-consumedp (fn-cfg-invitations (fn-cfg-value cfg))
                                             nonce)
                (not (equal (fn-config-replay-loop cfg reserved ceiling records)
                            :fault)))
           (fn-cfg-invitation-consumedp
            (fn-cfg-invitations
             (fn-cfg-value (fn-config-replay-loop cfg reserved ceiling records)))
            nonce))
  :hints (("Goal" :induct (fn-config-replay-loop cfg reserved ceiling records)
           :in-theory (e/d (fn-config-replay-loop fn-cfg-apply-record
                                                  fn-cfg-record-acceptablep)
                           (fn-cfg-invitation-consumedp fn-cfg-apply
                                                        fn-cfg-admissiblep)))))

(defthm fn-pinv-consumed-refuses-consumption
  (implies (and (fn-cfg-invitation-consumedp (fn-cfg-invitations v)
                                             (fn-cfg-delta-a d))
                (equal (fn-cfg-delta-kind d) :consume-invitation))
           (fn-cfg-delta-reason v gen stamp reserved ceiling d))
  :hints (("Goal" :in-theory (enable fn-cfg-delta-reason
                                     fn-cfg-invitation-consumedp
                                     fn-cfg-invitation-pendingp))))

(defthm fn-pinv-consumption-consumes
  (implies (and (equal (fn-cfg-delta-kind d) :consume-invitation)
                (not (fn-cfg-delta-reason v gen stamp reserved ceiling d)))
           (fn-cfg-invitation-consumedp
            (fn-cfg-invitations (fn-cfg-apply-delta v gen stamp d))
            (fn-cfg-delta-a d)))
  :hints (("Goal" :in-theory (enable fn-cfg-delta-reason
                                     fn-cfg-invitation-consumedp
                                     fn-cfg-invitation-row
                                     fn-cfg-invitation-delta-rowp
                                     fn-cfg-ag-car fn-cfg-ag-cdr
                                     fn-cfg-rows-with-key))))

; KEYSTONE (crash between consumption and enrolment).  Once the owner's
; consumption of an acceptance is durable, the same acceptance's next
; confirm is an enrolment and never a second consumption: the model's crash
; point after the configuration record and before the kind-3 record.
(defthm fn-pinv-confirm-after-its-consumption-enrols
  (let ((plan (fn-pinv-confirm-plan received observed-ml ed ml
                                    (fn-cfg-invitations v) snapshots)))
    (implies (and (equal (car plan) :consume)
                  (not (fn-pinv-enrolled-withp
                        (fn-pinv-received-principal received)
                        (fn-pinv-received-keys received) snapshots)))
             (equal (car (fn-pinv-confirm-plan
                          received observed-ml ed ml
                          (fn-cfg-invitations
                           (fn-cfg-apply-delta v gen stamp (fn-pinv-at 1 plan)))
                          snapshots))
                    :enrol)))
  :hints (("Goal" :in-theory (e/d (fn-pinv-confirm-plan
                                   fn-cfg-consume-invitation
                                   fn-cfg-invitation-row
                                   fn-cfg-rows-with-key fn-cfg-ag-car)
                                  (fn-pinv-acceptance-ok-is-a-document
                                   fn-record-octets-string))
           :use ((:instance fn-pinv-acceptance-ok-is-a-document)
                 (:instance fn-pinv-document-ok-is-bound
                            (kind *fn-pinv-acceptance-kind*))))))

;; A second confirm of an acceptance whose enrolment is this node's current
;; one enrols nothing (with the consumption above: nor consumes again).
(defthm fn-pinv-confirm-step-never-enrols-twice
  (implies (fn-pinv-enrolled-withp (fn-pinv-received-principal received)
                                   (fn-pinv-received-keys received) snapshots)
           (not (equal (car (fn-pinv-confirm-step sequence txid generation
                                                  received observed-ml ed ml
                                                  invitations snapshots))
                       :enrol)))
  :hints (("Goal" :use fn-pinv-confirm-step-enrols-only-the-consuming-acceptance
           :in-theory (disable
                       fn-pinv-confirm-step-enrols-only-the-consuming-acceptance))))

; -----------------------------------------------------------------------------
; The control requests: one carrier each (kinds 9 issue, 10 accept, 11
; confirm; kinds 4 to 8 are books/native-hybrid-control.lisp's).

(defconst *fn-pinv-issue-kind* 9)
(defconst *fn-pinv-accept-kind* 10)
(defconst *fn-pinv-confirm-kind* 11)
(defconst *fn-pinv-request-spec* '(:blob))

; Issue and accept carry one carrier.  Confirm carries two (PRF-124): the
; acceptance and the invitation it answers, below.
(defun fn-pinv-request-kindp (kind)
  (declare (xargs :guard t))
  (member-equal kind (list *fn-pinv-issue-kind* *fn-pinv-accept-kind*)))

(defun fn-pinv-request-encode (kind received)
  (declare (xargs :guard t))
  (if (not (and (fn-pinv-request-kindp kind) (fn-cbor-octet-listp received)
                (consp received)))
      :bad
    (fn-nhctrl-seal kind *fn-pinv-request-spec* (list received))))

(defun fn-pinv-request-decode (kind octets)
  (declare (xargs :guard t))
  (if (not (fn-pinv-request-kindp kind)) nil
    (let ((v (fn-nhctrl-open-values octets kind *fn-pinv-request-spec*)))
      (if (and (true-listp v) (equal (len v) 1)
               (fn-cbor-octet-listp (car v)) (consp (car v)))
          (car v)
        nil))))
;; Confirm's request (kind 11): the acceptance, then the invitation.
(defconst *fn-pinv-confirm-request-spec* '(:blob :blob))

(defun fn-pinv-confirm-request-encode (acceptance invitation)
  (declare (xargs :guard t))
  (if (not (and (fn-cbor-octet-listp acceptance) (consp acceptance)
                (fn-cbor-octet-listp invitation) (consp invitation)))
      :bad
    (fn-nhctrl-seal *fn-pinv-confirm-kind* *fn-pinv-confirm-request-spec*
                    (list acceptance invitation))))

(defun fn-pinv-confirm-request-decode (octets)
  (declare (xargs :guard t))
  (let ((v (fn-nhctrl-open-values octets *fn-pinv-confirm-kind*
                                  *fn-pinv-confirm-request-spec*)))
    (if (and (true-listp v) (equal (len v) 2)
             (fn-cbor-octet-listp (car v)) (consp (car v))
             (fn-cbor-octet-listp (cadr v)) (consp (cadr v)))
        v
      nil)))

;; PRF-166 (PKT-325): `keys redecide MSGID' (kind 12), the Message-ID's
;; octets.  The owner's handler (host/native/keys.lisp) decides it with
;; books/key-statements.lisp fn-ks-redecide-plan; this is only its frame.
(defconst *fn-pinv-redecide-kind* 12)
(defconst *fn-pinv-max-redecide-msgid* 250)

(defun fn-pinv-redecide-request-encode (msgid)
  (declare (xargs :guard t))
  (if (not (and (fn-cbor-octet-listp msgid) (consp msgid)
                (<= (len msgid) *fn-pinv-max-redecide-msgid*)))
      :bad
    (fn-nhctrl-seal *fn-pinv-redecide-kind* *fn-pinv-request-spec*
                    (list msgid))))

(defun fn-pinv-redecide-request-decode (octets)
  (declare (xargs :guard t))
  (let ((v (fn-nhctrl-open-values octets *fn-pinv-redecide-kind*
                                  *fn-pinv-request-spec*)))
    (if (and (true-listp v) (equal (len v) 1)
             (fn-cbor-octet-listp (car v)) (consp (car v))
             (<= (len (car v)) *fn-pinv-max-redecide-msgid*))
        (car v)
      nil)))

;; PKT-221: `principal bind|unbind' against a running owner (kind 14).  The
;; frame carries one fixed word and no data: the owner re-reads the
;; credential file it was started with and publishes its bindings
;; (books/login-binding-live.lisp fn-lb-sync-plan, host/native/login-bindings
;; .lisp).  Kind 13 is invitation-code accounts' (PRF-164).
(defconst *fn-pinv-bindings-kind* 14)
(defconst *fn-pinv-bindings-word* (fn-record-string-octets "login-bindings"))

(defun fn-pinv-bindings-request-encode ()
  (declare (xargs :guard t))
  (fn-nhctrl-seal *fn-pinv-bindings-kind* *fn-pinv-request-spec*
                  (list *fn-pinv-bindings-word*)))

(defun fn-pinv-bindings-request-decode (octets)
  ; t for the reload request, else nil.
  (declare (xargs :guard t))
  (let ((v (fn-nhctrl-open-values octets *fn-pinv-bindings-kind*
                                  *fn-pinv-request-spec*)))
    (and (true-listp v) (equal (len v) 1)
         (equal (car v) *fn-pinv-bindings-word*))))

; =============================================================================
; PRF-124: the confirm step ends with a configured peer, in the SAME
; configuration record that consumes the invitation.
;
; The inviter's operator named the invitee, its groups and its address when
; it issued the invitation (the body lines Invitee, Groups, Host, Port); the
; acceptance names the acceptor's Path identity and principal.  The confirm
; request carries both documents.  The invitation is the one this node
; issued exactly when its ACL2 authored-source identity is the one the
; acceptance names in Invitation-Source-Id, which the consumption already
; requires to be the pending row's (so, A-CRYPTO, the row this node
; recorded at issue from that very source).  The record is
;
;   ((:consume-invitation NONCE ACCEPTOR 0 ((NONCE ACCEPTOR ASID 1)))
;    (:set-peer INVITEE "" 0 <the peer's rows>))
;
; applied left to right under one generation by `fn-cfg-apply', the fold
; `fn-cfg-apply-record' runs when the owner completes the publication
; (host/native/peer-invite.lisp `fnn-pinv-owner-confirm' ->
; `fnn-owner-live-reconfigure-locked' -> `fn-owner-reconfigure-deltas').
; A crash can leave neither or both: there is no state with the invitation
; consumed and no peer.
;
; The peer: name Invitee; Path identity the acceptance's Acceptor-Path;
; transport (:nntp 1 Host Port (:clear)) -- the invitation carries no TLS
; words, and a protected transport is the operator's `peer add' of the same
; name, which replaces the record (specs/peering.md section 10); inbound
; Groups with the record's payload bound and 16 in flight; no outbound half;
; and the role binding (:principal ACCEPTOR), so an inbound connection is a
; reader until an AUTHINFO naming the acceptor promotes it (the
; principal-bound role selection).  A peer of that name already configured
; refuses the confirm (`:peer-name-taken'): the confirm never replaces a
; record the operator wrote.

(defun fn-pinv-digitsp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (integerp (car x)) (<= 48 (car x)) (<= (car x) 57)
           (fn-pinv-digitsp (cdr x)))
    (null x)))

(defun fn-pinv-digits-value (x acc)
  (declare (xargs :guard t))
  (if (consp x)
      (fn-pinv-digits-value (cdr x) (+ (* 10 (nfix acc))
                                       (nfix (- (nfix (car x)) 48))))
    (nfix acc)))

; A TCP port written as at most five decimal digits, 1 to 65535, or nil.
(defun fn-pinv-port (x)
  (declare (xargs :guard t))
  (if (and (fn-pinv-digitsp x) (consp x) (<= (len x) 5))
      (let ((n (fn-pinv-digits-value x 0)))
        (if (and (<= 1 n) (<= n 65535)) n nil))
    nil))

(defconst *fn-pinv-peer-inflight* 16)

(defun fn-pinv-confirmed-peer (invitation acceptance acceptor)
  (declare (xargs :guard t))
  (fn-cfg-peer-make
   (fn-record-octets-string (fn-pinv-field "Invitee" invitation))
   (fn-record-octets-string (fn-pinv-field "Acceptor-Path" acceptance))
   (list :nntp 1 (fn-record-octets-string (fn-pinv-field "Host" invitation))
         (fn-pinv-port (fn-pinv-field "Port" invitation)) '(:clear))
   (list (fn-record-octets-string (fn-pinv-field "Groups" invitation))
         *fn-record-max-payload* *fn-pinv-peer-inflight*)
   nil
   (list :principal (fn-pinv-hex-string acceptor))))

(defthm fn-pinv-confirmed-peer-auth
  (equal (fn-cfg-peer-auth (fn-pinv-confirmed-peer invitation acceptance
                                                   acceptor))
         (list :principal (fn-pinv-hex-string acceptor)))
  :hints (("Goal" :in-theory (e/d (fn-pinv-confirmed-peer)
                                  (fn-pinv-hex-string)))))

; The acceptance names this invitation: its source identity, as the
; Invitation-Source-Id line spells it.
(defun fn-pinv-names-invitation-p (acceptance invitation)
  (declare (xargs :guard t))
  (and (fn-pinv-kindp invitation *fn-pinv-invitation-kind*)
       (equal (fn-pinv-hex (fn-pinv-source-id invitation))
              (fn-pinv-field "Invitation-Source-Id" acceptance))))

; The owner's confirm plan (host/native/peer-invite.lisp
; `fnn-pinv-owner-confirm' calls it through `fn-pinv-host-confirm-record-plan').
; (:configure DELTAS) | (:enrol principal keys) | (:refused why).
(defun fn-pinv-confirm-record-plan (received invitation observed-ml ed ml
                                             invitations snapshots peers)
  (declare (xargs :guard t))
  (let ((plan (fn-pinv-confirm-plan received observed-ml ed ml invitations
                                    snapshots)))
    (if (not (equal (car plan) :consume)) plan
      (let* ((acc (fn-pinv-received-source received))
             (inv (fn-pinv-received-source invitation))
             (peer (fn-pinv-confirmed-peer
                    inv acc (fn-pinv-received-principal received))))
        (cond ((not (fn-pinv-kindp inv *fn-pinv-invitation-kind*))
               (list :refused :invitation-kind))
              ((not (fn-pinv-names-invitation-p acc inv))
               (list :refused :another-invitation))
              ((not (fn-cfg-peerp peer)) (list :refused :peer-record))
              ((fn-cfg-peer-find (fn-cfg-peer-name peer) peers)
               (list :refused :peer-name-taken))
              (t (list :configure
                       (list (fn-pinv-at 1 plan)
                             (fn-cfg-set-peer-delta peer)))))))))

(defthm fn-pinv-acceptance-never-configures
  (not (equal (car (fn-pinv-acceptance received observed-ml ed ml))
              :configure))
  :hints (("Goal" :in-theory (enable fn-pinv-acceptance fn-pinv-document))))

(defthm fn-pinv-confirm-plan-never-configures
  (not (equal (car (fn-pinv-confirm-plan received observed-ml ed ml invitations
                                         snapshots))
              :configure))
  :hints (("Goal" :in-theory (enable fn-pinv-confirm-plan))))

(defthm fn-pinv-confirm-record-plan-passes-the-other-plans
  (implies (not (equal (car (fn-pinv-confirm-plan received observed-ml ed ml
                                                  invitations snapshots))
                       :consume))
           (equal (fn-pinv-confirm-record-plan received invitation observed-ml
                                               ed ml invitations snapshots
                                               peers)
                  (fn-pinv-confirm-plan received observed-ml ed ml invitations
                                        snapshots))))

; KEYSTONE (the record the confirm publishes).  A (:configure DELTAS) plan
; exists only when the consumption plan is (:consume DELTA) (so
; `fn-pinv-confirm-consumes-only-a-pending-named-invitation' holds of it),
; the invitation presented is an invitation whose authored-source identity
; is exactly the pending row's (the invitation this node issued), the peer
; built from the two documents is a well-formed peer record whose name no
; configured peer has, and DELTAS is that consumption followed by that
; peer's (:set-peer) delta.
(defthm fn-pinv-confirm-record-configures-the-issued-invitations-peer
  (let* ((rplan (fn-pinv-confirm-record-plan received invitation observed-ml
                                             ed ml invitations snapshots peers))
         (plan (fn-pinv-confirm-plan received observed-ml ed ml invitations
                                     snapshots))
         (acc (fn-pinv-received-source received))
         (inv (fn-pinv-received-source invitation))
         (nonce (fn-record-octets-string (fn-pinv-field "Nonce" acc)))
         (row (fn-cfg-invitation-row invitations nonce))
         (peer (fn-pinv-confirmed-peer inv acc
                                       (fn-pinv-received-principal received))))
    (implies (equal (car rplan) :configure)
             (and (equal (car plan) :consume)
                  (fn-cfg-invitation-pendingp invitations nonce)
                  (fn-pinv-kindp inv *fn-pinv-invitation-kind*)
                  (equal (fn-pinv-hex-string (fn-pinv-source-id inv))
                         (fn-cfg-row-c row))
                  (fn-cfg-peerp peer)
                  (equal (fn-cfg-peer-auth peer)
                         (list :principal
                               (fn-pinv-hex-string
                                (fn-pinv-received-principal received))))
                  (not (fn-cfg-peer-find (fn-cfg-peer-name peer) peers))
                  (equal (fn-pinv-at 1 rplan)
                         (list (fn-pinv-at 1 plan)
                               (fn-cfg-set-peer-delta peer))))))
  :hints (("Goal" :in-theory (e/d (fn-pinv-names-invitation-p
                                   fn-pinv-hex-string)
                                  (fn-pinv-confirmed-peer fn-cfg-peerp
                                   fn-record-octets-string
                                   fn-cfg-peer-find fn-pinv-body-names-p
                                   fn-pinv-confirm-consumes-only-a-pending-named-invitation))
           :use ((:instance
                  fn-pinv-confirm-consumes-only-a-pending-named-invitation)))))

; The fold, one delta at a time: the consumption writes the invitations
; slot only, the peer delta the peers slot only.
(defthm fn-pinv-peers-of-consume-delta
  (equal (fn-cfg-peers (fn-cfg-apply-delta v gen stamp
                                           (fn-cfg-consume-invitation
                                            nonce acceptor asid)))
         (fn-cfg-peers v))
  :hints (("Goal" :in-theory (enable fn-cfg-apply-delta
                                     fn-cfg-consume-invitation))))

(defthm fn-pinv-invitations-of-set-peer-delta
  (equal (fn-cfg-invitations (fn-cfg-apply-delta v gen stamp
                                                 (fn-cfg-set-peer-delta p)))
         (fn-cfg-invitations v))
  :hints (("Goal" :in-theory (enable fn-cfg-apply-delta fn-cfg-set-peer-delta
                                     fn-cfg-set-peer))))

(defthm fn-pinv-invitation-row-after-consumption
  (equal (fn-cfg-invitation-row
          (fn-cfg-invitations
           (fn-cfg-apply-delta v gen stamp
                               (fn-cfg-consume-invitation nonce acceptor asid)))
          nonce)
         (fn-cfg-row-make nonce acceptor asid 1))
  :hints (("Goal" :in-theory (enable fn-cfg-consume-invitation
                                     fn-cfg-invitation-row
                                     fn-cfg-rows-with-key fn-cfg-ag-car))))

; KEYSTONE (over the fold the host calls).  Applying the confirm's record
; to the live value V (`fn-cfg-apply', under the record's generation and
; stamp) leaves: the invitation row its nonce keys consumed by exactly this
; acceptor and this acceptance's source identity; the peers table holding
; exactly the confirmed peer's rows under its name; and -- the crash point
; after the one record -- the same acceptance's next confirm an enrolment.
(defthm fn-pinv-confirm-record-fold-consumes-and-configures
  (let* ((rplan (fn-pinv-confirm-record-plan
                 received invitation observed-ml ed ml (fn-cfg-invitations v)
                 snapshots (fn-cfg-peers v)))
         (acc (fn-pinv-received-source received))
         (inv (fn-pinv-received-source invitation))
         (nonce (fn-record-octets-string (fn-pinv-field "Nonce" acc)))
         (acceptor (fn-pinv-hex-string (fn-pinv-received-principal received)))
         (peer (fn-pinv-confirmed-peer inv acc
                                       (fn-pinv-received-principal received)))
         (next (fn-cfg-apply v gen stamp (fn-pinv-at 1 rplan))))
    (implies (equal (car rplan) :configure)
             (and (equal (fn-cfg-invitation-row (fn-cfg-invitations next) nonce)
                         (fn-cfg-row-make nonce acceptor
                                          (fn-pinv-hex-string
                                           (fn-pinv-source-id acc))
                                          1))
                  (equal (fn-cfg-rows-with-key (fn-cfg-peers next)
                                               (fn-cfg-peer-name peer))
                         (fn-cfg-peer-rows peer))
                  (implies (not (fn-pinv-enrolled-withp
                                 (fn-pinv-received-principal received)
                                 (fn-pinv-received-keys received) snapshots))
                           (equal (car (fn-pinv-confirm-plan
                                        received observed-ml ed ml
                                        (fn-cfg-invitations next) snapshots))
                                  :enrol)))))
  :hints (("Goal"
           :in-theory (e/d (fn-cfg-apply)
                           (fn-pinv-confirm-record-plan fn-pinv-confirmed-peer
                            fn-record-octets-string fn-cfg-invitation-row
                            fn-cfg-peerp fn-cfg-peer-rows fn-cfg-apply-delta
                            fn-pinv-invitations-of-apply-delta
                            fn-pinv-confirm-record-configures-the-issued-invitations-peer
                            fn-pinv-confirm-consumes-only-a-pending-named-invitation
                            fn-pinv-confirm-after-its-consumption-enrols))
           :use ((:instance
                  fn-pinv-confirm-record-configures-the-issued-invitations-peer
                  (invitations (fn-cfg-invitations v)) (peers (fn-cfg-peers v)))
                 (:instance
                  fn-pinv-confirm-consumes-only-a-pending-named-invitation
                  (invitations (fn-cfg-invitations v)))
                 (:instance fn-pinv-confirm-after-its-consumption-enrols)
                 (:instance fn-pinv-invitations-of-apply-delta
                            (d (fn-pinv-at 1 (fn-pinv-confirm-plan
                                              received observed-ml ed ml
                                              (fn-cfg-invitations v)
                                              snapshots))))
                 (:instance fn-cfg-peer-rows-after-set-peer
                            (p (fn-pinv-confirmed-peer
                                (fn-pinv-received-source invitation)
                                (fn-pinv-received-source received)
                                (fn-pinv-received-principal received)))
                            (v (fn-cfg-apply-delta
                                v gen stamp
                                (fn-pinv-at 1 (fn-pinv-confirm-plan
                                               received observed-ml ed ml
                                               (fn-cfg-invitations v)
                                               snapshots)))))))))

; -----------------------------------------------------------------------------
; PRF-160: the accept configures the inviter (specs/peering.md section 10).
;
; An invitation whose body names `Inviter-Host' and `Inviter-Port' (the
; inviter's own reachable address) lets the invitee configure the inviter as
; a peer in the same step that enrols it.  The peer is the mirror of the one
; the confirm configures at the inviter: named and path-identified by the
; invitation's `Inviter-Path', transport `(:nntp 1 Inviter-Host Inviter-Port
; (:clear))', inbound `Groups' (the inviter may feed them here), no outbound
; half, and the role binding `(:principal INVITER)' of the principal whose
; carrier verified.  A protected transport and an outbound feed stay the
; operator's `peer add' of the same name, which replaces the record.
;
; The configuration record comes first and the kind-3 enrolment second, as
; in the confirm.  A death between the two leaves the peer configured and
; the inviter not enrolled; the next accept of the same invitation finds the
; peers table already holding exactly these rows and enrols without writing
; a second record.

(defun fn-pinv-inviter-peer (invitation inviter)
  (declare (xargs :guard t))
  (let ((path (fn-record-octets-string (fn-pinv-field "Inviter-Path"
                                                      invitation))))
    (fn-cfg-peer-make
     path path
     (list :nntp 1 (fn-record-octets-string (fn-pinv-field "Inviter-Host"
                                                           invitation))
           (fn-pinv-port (fn-pinv-field "Inviter-Port" invitation)) '(:clear))
     (list (fn-record-octets-string (fn-pinv-field "Groups" invitation))
           *fn-record-max-payload* *fn-pinv-peer-inflight*)
     nil
     (list :principal (fn-pinv-hex-string inviter)))))

(defthm fn-pinv-inviter-peer-auth
  (equal (fn-cfg-peer-auth (fn-pinv-inviter-peer invitation inviter))
         (list :principal (fn-pinv-hex-string inviter)))
  :hints (("Goal" :in-theory (e/d (fn-pinv-inviter-peer)
                                  (fn-pinv-hex-string)))))

; The invitation names an address: an Inviter-Port that is a port.  `-' (or
; no line, an invitation written before PRF-160) names none.
(defun fn-pinv-inviter-addressedp (invitation)
  (declare (xargs :guard t))
  (and (fn-pinv-port (fn-pinv-field "Inviter-Port" invitation)) t))

; The owner's accept plan (host/native/peer-invite.lisp
; `fnn-pinv-owner-accept' calls it through `fn-pinv-host-accept-record-plan').
; (:configure DELTAS) | the accept plan (:enrol ...) | (:refused why).
(defun fn-pinv-accept-record-plan (received observed-ml ed ml snapshots peers)
  (declare (xargs :guard t))
  (let ((plan (fn-pinv-accept-plan received observed-ml ed ml)))
    (if (not (equal (car plan) :enrol)) plan
      (let* ((inv (fn-pinv-received-source received))
             (peer (fn-pinv-inviter-peer inv (fn-pinv-received-principal
                                              received)))
             (name (fn-cfg-peer-name peer)))
        (cond ((fn-pinv-enrolled-withp (fn-pinv-received-principal received)
                                       (fn-pinv-received-keys received)
                                       snapshots)
               (list :refused :already-enrolled))
              ((not (fn-pinv-inviter-addressedp inv)) plan)
              ((not (fn-cfg-peerp peer)) (list :refused :peer-record))
              ((equal (fn-cfg-rows-with-key peers name) (fn-cfg-peer-rows peer))
               plan)
              ((consp (fn-cfg-rows-with-key peers name))
               (list :refused :peer-name-taken))
              (t (list :configure (list (fn-cfg-set-peer-delta peer)))))))))

(defthm fn-pinv-accept-plan-never-configures
  (not (equal (car (fn-pinv-accept-plan received observed-ml ed ml))
              :configure))
  :hints (("Goal" :in-theory (enable fn-pinv-accept-plan fn-pinv-document))))

(defthm fn-pinv-accept-plan-enrols-only-a-bound-invitation
  (implies (equal (car (fn-pinv-accept-plan received observed-ml ed ml)) :enrol)
           (fn-pinv-bound-document-p received observed-ml ed ml
                                     *fn-pinv-invitation-kind*))
  :hints (("Goal" :in-theory (enable fn-pinv-accept-plan)
           :use ((:instance fn-pinv-document-ok-is-bound
                            (kind *fn-pinv-invitation-kind*))))))

; KEYSTONE (the record the accept publishes).  A (:configure DELTAS) plan
; exists only when the accept step's own plan enrols (the invitation's
; carrier verifies under the key set its body names and the inviter is its
; genesis principal: `fn-pinv-document-ok-is-bound'), the inviter is not yet
; enrolled here, the invitation names an address, the peer built from it is
; a well-formed peer record bound to exactly the verified inviter, no
; configured peer has its name, and DELTAS is that peer's (:set-peer) delta.
(defthm fn-pinv-accept-record-configures-the-verified-inviter
  (let* ((rplan (fn-pinv-accept-record-plan received observed-ml ed ml
                                            snapshots peers))
         (inv (fn-pinv-received-source received))
         (inviter (fn-pinv-received-principal received))
         (peer (fn-pinv-inviter-peer inv inviter)))
    (implies (equal (car rplan) :configure)
             (and (fn-pinv-bound-document-p received observed-ml ed ml
                                            *fn-pinv-invitation-kind*)
                  (not (fn-pinv-enrolled-withp
                        inviter (fn-pinv-received-keys received) snapshots))
                  (fn-pinv-inviter-addressedp inv)
                  (fn-cfg-peerp peer)
                  (equal (fn-cfg-peer-auth peer)
                         (list :principal (fn-pinv-hex-string inviter)))
                  (not (consp (fn-cfg-rows-with-key peers
                                                    (fn-cfg-peer-name peer))))
                  (equal (fn-pinv-at 1 rplan)
                         (list (fn-cfg-set-peer-delta peer))))))
  :hints (("Goal" :in-theory (disable fn-pinv-inviter-peer fn-cfg-peerp
                                      fn-cfg-peer-rows fn-pinv-inviter-addressedp
                                      fn-record-octets-string
                                      fn-pinv-body-names-p)
           :use ((:instance fn-pinv-accept-plan-enrols-only-a-bound-invitation)))))

; KEYSTONE (over the fold the host calls).  Applying the accept's record to
; the live value V (`fn-cfg-apply', under the record's generation and
; stamp) leaves the peers table holding exactly the inviter peer's rows
; under its name, and -- the crash point after the one record -- the same
; invitation's next accept plan over the folded peers table is the accept
; step's enrolment plan, never a second record.
(defthm fn-pinv-accept-record-fold-configures-the-inviter
  (let* ((rplan (fn-pinv-accept-record-plan received observed-ml ed ml
                                            snapshots (fn-cfg-peers v)))
         (peer (fn-pinv-inviter-peer (fn-pinv-received-source received)
                                     (fn-pinv-received-principal received)))
         (next (fn-cfg-apply v gen stamp (fn-pinv-at 1 rplan))))
    (implies (equal (car rplan) :configure)
             (and (equal (fn-cfg-rows-with-key (fn-cfg-peers next)
                                               (fn-cfg-peer-name peer))
                         (fn-cfg-peer-rows peer))
                  (equal (fn-pinv-accept-record-plan received observed-ml ed ml
                                                     snapshots
                                                     (fn-cfg-peers next))
                         (fn-pinv-accept-plan received observed-ml ed ml))
                  (equal (car (fn-pinv-accept-plan received observed-ml ed ml))
                         :enrol))))
  :hints (("Goal"
           :in-theory (e/d (fn-cfg-apply)
                           (fn-pinv-inviter-peer fn-cfg-peerp fn-cfg-peer-rows
                            fn-cfg-apply-delta fn-pinv-inviter-addressedp
                            fn-record-octets-string
                            fn-pinv-accept-record-configures-the-verified-inviter))
           :use ((:instance fn-pinv-accept-record-configures-the-verified-inviter
                            (peers (fn-cfg-peers v)))
                 (:instance fn-cfg-peer-rows-after-set-peer
                            (p (fn-pinv-inviter-peer
                                (fn-pinv-received-source received)
                                (fn-pinv-received-principal received))))))))
