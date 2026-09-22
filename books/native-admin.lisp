; fn: bounded native administrative configuration plan.
;
; This is deliberately a narrow command boundary.  It selects group, capacity
; and peer deltas that the store already owns, and it never owns a second
; group/peer table, capacity rule, record encoder, or replay algorithm.
; Raw Lisp supplies bounded argv octets and physical observations; the record
; remains `fn-store-cfg-reconfigure' and a proposed history is checked here by
; the same logical replay/open entry used at ordinary recovery.

(in-package "ACL2")
(include-book "node-config")
(include-book "store-observed")
(include-book "byte-store-txn-name")
(include-book "journal-publish")
(include-book "native-config")
(include-book "peer-config")
(include-book "identity")

(defconst *fn-native-admin-max-arguments* 16)
(defconst *fn-native-admin-max-argument-octets* 512)
(defconst *fn-native-admin-config-name-width* 8)
(defconst *fn-native-admin-config-name-limit* 100000000)
(defconst *fn-native-admin-config-name-suffix* '(#\. #\c #\f #\g))

(local (defthm fn-native-admin-natural-digits-characters
  (character-listp (fn-bs-txn-natural-digits n))
  :hints (("Goal" :in-theory (enable fn-bs-txn-natural-digits
                                        fn-bs-txn-natural-digits-rev
                                        fn-bs-txn-reverse)))))

(local (defthm fn-native-admin-zeroes-characters
  (character-listp (fn-bs-txn-zeroes n))
  :hints (("Goal" :induct (fn-bs-txn-zeroes n)))) )

(local (defthm fn-native-admin-config-name-chars
  (character-listp
   (append (fn-bs-txn-zeroes n) (fn-bs-txn-natural-digits generation)
           *fn-native-admin-config-name-suffix*))
  :hints (("Goal" :use ((:instance fn-native-admin-zeroes-characters (n n))
                         (:instance fn-native-admin-natural-digits-characters
                                    (n generation)))))))

(defun fn-native-admin-argvp (argv)
  (declare (xargs :guard t))
  (if (consp argv)
      (and (consp (car argv))
           (<= (len (car argv)) *fn-native-admin-max-argument-octets*)
           (fn-record-ascii-octet-listp (car argv))
           (fn-native-admin-argvp (cdr argv)))
    (null argv)))

(defun fn-native-admin-words (argv)
  (declare (xargs :guard t))
  (if (consp argv)
      (cons (fn-record-octets-string (car argv))
            (fn-native-admin-words (cdr argv)))
    nil))

(defun fn-native-admin-digit-value (char)
  (declare (xargs :guard t))
  (if (characterp char)
      (let ((digit (char-code char)))
        (if (and (<= (char-code #\0) digit) (<= digit (char-code #\9)))
            (- digit (char-code #\0))
          -1))
    -1))

(defun fn-native-admin-decimal-value-aux (chars value)
  (declare (xargs :guard t))
  (if (consp chars)
      (let ((digit (fn-native-admin-digit-value (car chars))))
        (if (<= 0 digit)
            (fn-native-admin-decimal-value-aux
             (cdr chars) (+ (* 10 (nfix value)) digit))
          -1))
    (nfix value)))

(defun fn-native-admin-decimal-value (chars)
  (declare (xargs :guard t))
  (fn-native-admin-decimal-value-aux chars 0))

(defun fn-native-admin-decimalp (text)
  (declare (xargs :guard t))
  (if (not (stringp text)) nil
    (let ((chars (coerce text 'list)))
      (and (consp chars)
           (not (and (consp (cdr chars)) (equal (car chars) #\0)))
           (<= 0 (fn-native-admin-decimal-value chars))
           (fn-record-uint32p (fn-native-admin-decimal-value chars))))))

(defun fn-native-admin-result (status reason kind name capacity peer value)
  ; `value' is the second label of a two-label delta: the policy id of
  ; `policy set SLOT VALUE' (`name' carries the slot).  Every other kind
  ; leaves it nil.
  (declare (xargs :guard t))
  (list status reason kind name capacity peer value))

(defun fn-native-admin-result-status (result)
  (declare (xargs :guard t))
  (mbe :logic (car result) :exec (fn-ag-car result)))
(defun fn-native-admin-result-reason (result)
  (declare (xargs :guard t))
  (mbe :logic (cadr result) :exec (fn-ag-car (fn-ag-cdr result))))
(defun fn-native-admin-result-kind (result)
  (declare (xargs :guard t))
  (mbe :logic (caddr result) :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr result)))))
(defun fn-native-admin-result-name (result)
  (declare (xargs :guard t))
  (mbe :logic (cadddr result)
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr result))))))
(defun fn-native-admin-result-capacity (result) (declare (xargs :guard t))
  (mbe :logic (car (cddddr result))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr result)))))))
(defun fn-native-admin-result-peer (result) (declare (xargs :guard t))
  (mbe :logic (cadr (cddddr result))
       :exec (fn-ag-car
              (fn-ag-cdr
               (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr result))))))))
(defun fn-native-admin-result-value (result) (declare (xargs :guard t))
  (mbe :logic (caddr (cddddr result))
       :exec (fn-ag-car
              (fn-ag-cdr
               (fn-ag-cdr
                (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr result)))))))))

(defun fn-native-admin-peer-plan (words)
  "Build the complete peer record in ACL2; raw Lisp receives no field defaults.

The explicit grammar carries auth-kind/auth-value.  The older grammar is
decoded as source-address for durable command compatibility."
  (declare (xargs :guard t))
  ; The vector is decided before any `nth' of it.  `fn-native-admin-plan' only
  ; ever hands over `fn-native-admin-words' of a recognized argv, which is a
  ; proper list; the raw boundary stays total, and an improper vector is the
  ; same :syntax refusal it has been since e34523a1.  Leading with the test is
  ; what lets `nth' run under a verified guard: the conjunct this replaces sat
  ; below the `nth' calls in the `let*', so the guard conjecture asked for
  ; (implies (equal (len words) 13) (true-listp words)), which is false.
  (if (not (true-listp words))
      (fn-native-admin-result :refused :syntax nil nil 0 nil nil)
  (let* ((count (len words))
         (v2p (and (member-equal count '(13 16))
                   (member-equal (nth 8 words) '("source-address" "principal"))))
         (explicitp (or v2p (member-equal count '(11 14))))
         (auth-kind (if explicitp (nth 8 words) "source-address"))
         (auth-value (if explicitp (nth 9 words) (nth 8 words)))
         (profile (if v2p (nth 10 words) "-"))
         (allow-clear (if v2p (nth 11 words) "false"))
         (streaming (if v2p (nth 12 words)
                      (if explicitp (nth 10 words) (nth 9 words))))
         (security-index (if v2p 13 (if explicitp 11 10))))
    (if (and (member-equal count '(10 11 13 14 16))
             (equal (car words) "peer")
             (equal (cadr words) "add")
             (fn-native-admin-decimalp (nth 5 words))
             (<= 1 (fn-native-admin-decimal-value
                    (coerce (nth 5 words) 'list)))
             (<= (fn-native-admin-decimal-value
                  (coerce (nth 5 words) 'list)) 65535)
             (member-equal auth-kind '("source-address" "principal"))
             (if (equal auth-kind "source-address")
                 (not (equal (fn-native-config-ipv4-address
                              (fn-record-string-octets auth-value)) :bad))
               (and (equal (len (fn-record-string-octets auth-value)) 64)
                    (fn-id-hex-listp (fn-record-string-octets auth-value))))
             (member-equal streaming '("true" "false"))
             (or (not v2p)
                 (and (not (equal profile "-"))
                      (member-equal allow-clear '("true" "false"))))
             (or (equal count 10) (equal count 11)
                 (and v2p (equal count 13))
                 (and (member-equal (nth security-index words)
                                    '("clear" "implicit" "starttls"))
                      (if (equal (nth security-index words) "clear")
                          (and (equal (nth (+ 1 security-index) words) "-")
                               (equal (nth (+ 2 security-index) words) "-"))
                        (and (not (equal (nth (+ 1 security-index) words) "-"))
                             (not (equal (nth (+ 2 security-index) words) "-")))))))
        (let* ((inbound (if (equal (nth 6 words) "-") nil
                          (list (nth 6 words) *fn-record-max-payload* 16)))
               (outbound (if (equal (nth 7 words) "-") nil
                           (append (list (nth 7 words) (equal streaming "true")
                                         1024 1000)
                                   (if v2p
                                       (list (list :authinfo profile
                                                   (equal allow-clear "true")))
                                     nil))))
               (peer (fn-cfg-peer-make
                      (nth 2 words) (nth 3 words)
                      (list :nntp 1 (nth 4 words)
                            (fn-native-admin-decimal-value
                             (coerce (nth 5 words) 'list))
                            (if (or (equal count 10) (equal count 11)
                                    (and v2p (equal count 13))
                                    (equal (nth security-index words) "clear"))
                                '(:clear)
                              (list :tls
                                    (if (equal (nth security-index words) "implicit")
                                        :implicit :starttls)
                                    (nth (+ 1 security-index) words)
                                    (nth (+ 2 security-index) words))))
                      inbound outbound
                      (list (if (equal auth-kind "principal")
                                :principal :source-address)
                            auth-value))))
          (if (fn-cfg-peerp peer)
              (fn-native-admin-result :accepted nil :set-peer nil 0 peer nil)
            (fn-native-admin-result :refused :peer-record nil nil 0 nil nil)))
      (fn-native-admin-result :refused :syntax nil nil 0 nil nil)))))

(defun fn-native-admin-plan (argv)
  "Normalize an administrative request; configuration admission stays in the store core."
  (declare (xargs :guard t))
  (if (or (not (fn-native-admin-argvp argv))
          (< *fn-native-admin-max-arguments* (len argv)))
      (fn-native-admin-result :refused :argv nil nil nil nil nil)
    (let ((words (fn-native-admin-words argv)))
      (cond
       ((and (equal (len words) 3)
             (equal (car words) "group")
             (equal (cadr words) "create")
             (fn-record-group-namep (caddr words)))
        (fn-native-admin-result :accepted nil :create-group (caddr argv) 0 nil nil))
       ((and (equal (len words) 3)
             (equal (car words) "group")
             (equal (cadr words) "retire")
             (fn-record-group-namep (caddr words)))
        (fn-native-admin-result :accepted nil :remove-group (caddr argv) 0 nil nil))
       ((and (equal (len words) 2)
             (equal (car words) "capacity")
             (fn-native-admin-decimalp (cadr words)))
        (fn-native-admin-result :accepted nil :set-capacity nil
                                (fn-native-admin-decimal-value
                                 (coerce (cadr words) 'list)) nil nil))
       ; The node's own RFC 5537 section 3.2 <path-identity>.  It is the one
       ; policy slot peering needs: `fn-peer-local-identity' (books/peer-inbound)
       ; reads it, and while it is unset a node cannot recognise its own name
       ; in a Path, so section 3.5 loop suppression cannot fire (measured on
       ; the native v0 matrix, 2026-09-22: V0-TRANSIT-LOOP accepted 235).  The
       ; value must itself be a <path-identity>; the same recognizer admits a
       ; peer's identity in `fn-native-admin-peer-plan'.  The slot is a durable
       ; `:set-policy' configuration record, not a configuration-file key, for
       ; the reason packaging/fn.toml.example gives for served groups.
       ((and (equal (len words) 4)
             (equal (car words) "policy")
             (equal (cadr words) "set")
             (equal (caddr words) "path-identity")
             (fn-path-identityp (cadddr argv)))
        (fn-native-admin-result :accepted nil :set-policy (caddr argv) 0 nil
                                (cadddr argv)))
       ((and (consp words) (equal (car words) "policy"))
        (fn-native-admin-result :refused :policy nil nil 0 nil nil))
       ((and (consp words) (equal (car words) "peer"))
        (cond
         ; `peer list' is the table's read side.  It carries no name, no
         ; capacity and no record: it is a query over the durable
         ; configuration, and `fn-native-admin-result-queryp' below is what
         ; keeps its executor off the writer lock and off the owner mutex.
         ((and (equal (len words) 2) (equal (cadr words) "list"))
          (fn-native-admin-result :accepted nil :list-peers nil 0 nil nil))
         ((and (equal (len words) 3)
               (equal (cadr words) "remove")
               (stringp (caddr words))
               (not (equal (caddr words) "")))
          (fn-native-admin-result :accepted nil :remove-peer (caddr argv) 0 nil nil))
         (t (fn-native-admin-peer-plan words))))
       (t (fn-native-admin-result :refused :syntax nil nil nil nil nil))))))

; The delta list the LIVE owner stages for an accepted plan.
;
; The live arm (host/native-admin-host.lisp
; `fn-native-admin-host-owner-reconfigure') hands this list to
; `fn-owner-reconfigure-deltas'.  A plan carries its labels as the argv
; OCTETS the operator typed (the offline executor, `fn-store-cfg-reconfigure'
; and its siblings in host/store-node-host.lisp, takes octets and converts
; them itself); a configuration delta's labels are STRINGS (`fn-cfg-labelp',
; books/config.lisp).  The live arm used to pass the octets straight into
; `fn-cfg-create-group', `fn-cfg-remove-group' and `fn-cfg-remove-peer-delta',
; which built deltas `fn-cfg-deltap' refuses, so every live `group create',
; `group retire' and `peer remove' was refused `:malformed-delta' by
; `fn-ocfg-reconfig-refusal' (measured 2026-09-22, the ground witness in
; tests/acl2/native-admin-tests.lisp).  The conversion is the same
; `fn-record-octets-string' the plan's own recognizers were applied to, so
; the label a delta carries is exactly the word the plan admitted.
(defun fn-native-admin-plan-deltas (plan)
  (declare (xargs :guard t))
  (if (not (equal (fn-native-admin-result-status plan) :accepted))
      nil
    (let ((kind (fn-native-admin-result-kind plan))
          (name (fn-record-octets-string (fn-native-admin-result-name plan))))
      (cond ((equal kind :set-peer)
             (list (fn-cfg-set-peer-delta (fn-native-admin-result-peer plan))))
            ((equal kind :remove-peer)
             (list (fn-cfg-remove-peer-delta name)))
            ((equal kind :create-group)
             (list (fn-cfg-create-group name *fn-cfg-default-policy-id*)))
            ((equal kind :remove-group)
             (list (fn-cfg-remove-group name)))
            ((equal kind :set-capacity)
             (list (fn-cfg-set-capacity (fn-native-admin-result-capacity plan))))
            ((equal kind :set-policy)
             (list (fn-cfg-set-policy
                    name
                    (fn-record-octets-string (fn-native-admin-result-value plan)))))
            (t nil)))))

(encapsulate ()
(local (defthm kind-of-result
  (equal (fn-native-admin-result-kind (fn-native-admin-result s r k n c p v)) k)))
(local (defthm status-of-result
  (equal (fn-native-admin-result-status (fn-native-admin-result s r k n c p v)) s)))
(local (defthm name-of-result
  (equal (fn-native-admin-result-name (fn-native-admin-result s r k n c p v)) n)))
(local (in-theory (disable fn-native-admin-result fn-native-admin-result-kind
                           fn-native-admin-result-status fn-native-admin-result-name)))
(defthm fn-native-admin-peer-plan-kind
  (member-equal (fn-native-admin-result-kind (fn-native-admin-peer-plan words))
                '(:set-peer nil))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-native-admin-peer-plan)
                                  (fn-cfg-peerp fn-cfg-peer-make nth len
                                   fn-native-admin-decimalp fn-native-admin-decimal-value
                                   fn-native-config-ipv4-address fn-id-hex-listp)))))
(defthm fn-native-admin-plan-group-name-is-a-group-name
  (implies (and (equal (fn-native-admin-result-status (fn-native-admin-plan argv)) :accepted)
                (member-equal (fn-native-admin-result-kind (fn-native-admin-plan argv))
                              '(:create-group :remove-group)))
           (fn-record-group-namep
            (fn-record-octets-string (fn-native-admin-result-name (fn-native-admin-plan argv)))))
  :hints (("Goal" :in-theory (e/d (fn-native-admin-plan fn-native-admin-words)
                                  (fn-native-admin-peer-plan fn-record-group-namep
                                   fn-path-identityp fn-native-admin-decimalp
                                   fn-native-admin-decimal-value fn-native-admin-argvp))
           :use ((:instance fn-native-admin-peer-plan-kind
                            (words (fn-native-admin-words argv)))))))
)

; KEYSTONE.  Every delta the live arm stages for an accepted `group create'
; or `group retire' is a typed delta: its name label is the admitted group
; name as a STRING, so `fn-ocfg-reconfig-refusal' cannot refuse it
; `:malformed-delta' for the octet/string confusion described above.  The
; teeth, including the old octet delta that `fn-cfg-deltap' refuses, are in
; tests/acl2/native-admin-tests.lisp.  (`peer remove' and `policy set' carry
; labels the plan bounds at 512 octets and the configuration at 256, so a
; long one is a well-typed refusal of the configuration book, not a type
; confusion; they are witnessed on ground values, not in this theorem.)
(encapsulate ()
(local (defthm group-name-is-label
  (implies (fn-record-group-namep s) (fn-cfg-labelp s))
  :hints (("Goal" :in-theory (enable fn-record-group-namep fn-cfg-labelp
                                     fn-record-nonempty-at-mostp)))))
(local (defthm group-deltas-typed
  (implies (fn-record-group-namep s)
           (and (fn-cfg-delta-listp (list (fn-cfg-create-group s *fn-cfg-default-policy-id*)))
                (fn-cfg-delta-listp (list (fn-cfg-remove-group s)))))
  :hints (("Goal" :in-theory (e/d (fn-cfg-deltap fn-cfg-delta-listp
                                   fn-cfg-create-group fn-cfg-remove-group)
                                  (fn-record-group-namep fn-cfg-labelp))))))
(defthm fn-native-admin-live-group-delta-is-a-typed-delta
  (implies (and (equal (fn-native-admin-result-status (fn-native-admin-plan argv)) :accepted)
                (member-equal (fn-native-admin-result-kind (fn-native-admin-plan argv))
                              '(:create-group :remove-group)))
           (and (consp (fn-native-admin-plan-deltas (fn-native-admin-plan argv)))
                (fn-cfg-delta-listp (fn-native-admin-plan-deltas (fn-native-admin-plan argv)))))
  :hints (("Goal" :in-theory (e/d (fn-native-admin-plan-deltas)
                                  (fn-native-admin-plan fn-record-group-namep
                                   fn-cfg-delta-listp fn-cfg-create-group fn-cfg-remove-group
                                   fn-record-octets-string))
           :use (fn-native-admin-plan-group-name-is-a-group-name
                 (:instance group-deltas-typed
                            (s (fn-record-octets-string
                                (fn-native-admin-result-name (fn-native-admin-plan argv)))))))))
)

(defun fn-native-admin-result-queryp (result)
  "Does this accepted plan only read the durable configuration?

A query publishes no configuration record, so its executor opens the store
without the exclusive writer lock and never reaches the live owner's
serialized reconfiguration.  The host asks this question rather than deciding
for itself which kinds are safe to read: the plan kinds are ACL2's."
  (declare (xargs :guard t))
  (and (equal (fn-native-admin-result-status result) :accepted)
       (equal (fn-native-admin-result-kind result) :list-peers)))

; -----------------------------------------------------------------------------
; `peer list': the public projection of the durable peer table.
;
; The fields are the ones `peer add' takes, in that order, so an operator can
; read a record back and see the command that would write it again.  Raw Lisp
; supplies the configuration value's peer rows and writes these octets to a
; descriptor; it renders no field, formats no number, and supplies no name for
; an absent half.  Wildmats and identities are printed as the configuration
; holds them (books/peer-config.lisp is the codec); nothing here re-derives a
; transport, an auth kind or a security mode.

(defconst *fn-native-admin-peer-absent* (list 45)) ; "-"

(defun fn-native-admin-peer-label-octets (text)
  "One configuration label as octets, or `-' when the slot holds no label."
  (declare (xargs :guard t))
  (if (and (stringp text) (consp (fn-record-string-octets text)))
      (fn-record-string-octets text)
    *fn-native-admin-peer-absent*))

(defun fn-native-admin-peer-security-octets (security)
  (declare (xargs :guard t))
  (cond ((equal security '(:clear)) (fn-record-string-octets "clear"))
        ((equal (fn-ag-car (fn-ag-cdr security)) :implicit)
         (fn-record-string-octets "implicit"))
        ((equal (fn-ag-car (fn-ag-cdr security)) :starttls)
         (fn-record-string-octets "starttls"))
        (t *fn-native-admin-peer-absent*)))

(defun fn-native-admin-peer-transport-octets (transport)
  "address, port and security for one peer's transport half.

The three transport shapes `fn-cfg-peer-transportp' admits are the three
arms here: the explicit NNTP endpoint with its security mode, the legacy
durable NNTP endpoint (explicit cleartext), and a BP endpoint, whose EID is
the address and which has no port or TLS mode of its own."
  (declare (xargs :guard t))
  (let ((kind (fn-ag-car transport)))
    (cond
     ((and (equal kind :nntp) (equal (len transport) 5))
      (append (fn-record-string-octets " address=")
              (fn-native-admin-peer-label-octets
               (fn-ag-car (fn-ag-cdr (fn-ag-cdr transport))))
              (fn-record-string-octets " port=")
              (fn-nntp-decimal-field
               (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr transport)))))
              (fn-record-string-octets " security=")
              (fn-native-admin-peer-security-octets
               (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                                                 (fn-ag-cdr transport))))))))
     ((and (equal kind :nntp) (equal (len transport) 3))
      (append (fn-record-string-octets " address=")
              (fn-native-admin-peer-label-octets (fn-ag-car (fn-ag-cdr transport)))
              (fn-record-string-octets " port=")
              (fn-nntp-decimal-field
               (fn-ag-car (fn-ag-cdr (fn-ag-cdr transport))))
              (fn-record-string-octets " security=clear")))
     ((equal kind :bp)
      (append (fn-record-string-octets " address=")
              (fn-native-admin-peer-label-octets (fn-ag-car (fn-ag-cdr transport)))
              (fn-record-string-octets " port=0 security=-")))
     (t (fn-record-string-octets " address=- port=0 security=-")))))

(defun fn-native-admin-peer-auth-octets (auth)
  (declare (xargs :guard t))
  (append (fn-record-string-octets " auth=")
          (if (equal (fn-ag-car auth) :principal)
              (fn-record-string-octets "principal:")
            (fn-record-string-octets "source-address:"))
          (fn-native-admin-peer-label-octets (fn-ag-car (fn-ag-cdr auth)))))

(defun fn-native-admin-peer-row-octets (p)
  (declare (xargs :guard t))
  (append (fn-native-admin-peer-label-octets (fn-cfg-peer-name p))
          (fn-record-string-octets " path-identity=")
          (fn-native-admin-peer-label-octets (fn-cfg-peer-path-identity p))
          (fn-native-admin-peer-transport-octets (fn-cfg-peer-transport p))
          (fn-record-string-octets " inbound=")
          (if (fn-cfg-peer-inbound p)
              (fn-native-admin-peer-label-octets (fn-cfg-peer-inbound-groups p))
            *fn-native-admin-peer-absent*)
          (fn-record-string-octets " outbound=")
          (if (fn-cfg-peer-outbound p)
              (fn-native-admin-peer-label-octets (fn-cfg-peer-outbound-groups p))
            *fn-native-admin-peer-absent*)
          (fn-native-admin-peer-auth-octets (fn-cfg-peer-auth p))
          (list 10)))

(defun fn-native-admin-peer-report-rows (names peers)
  (declare (xargs :guard t))
  (if (consp names)
      (let ((p (fn-cfg-peer-find (car names) peers)))
        (append (if p (fn-native-admin-peer-row-octets p) nil)
                (fn-native-admin-peer-report-rows (cdr names) peers)))
    nil))

(defun fn-native-admin-peer-report (peers)
  "The `peer list' report for a configuration value's peer rows.

The enumeration is `fn-cfg-peer-names' and each record is `fn-cfg-peer-find';
a row group that denotes no well-formed record contributes no line rather
than a partially rendered one."
  (declare (xargs :guard t))
  (fn-native-admin-peer-report-rows (fn-cfg-peer-names peers) peers))

; Config record names are a fixed-width namespace.  The digit renderer is the
; existing ACL2 byte-store renderer; no host formatter derives a durable name.
(defun fn-native-admin-config-name-bounded (generation)
  (declare (xargs :guard (and (natp generation)
                              (< generation *fn-native-admin-config-name-limit*))
                  :verify-guards nil))
  (coerce
   (append (fn-bs-txn-zeroes
            (nfix (- *fn-native-admin-config-name-width*
                     (len (fn-bs-txn-natural-digits generation)))))
           (fn-bs-txn-natural-digits generation)
           *fn-native-admin-config-name-suffix*)
   'string))

(verify-guards fn-native-admin-config-name-bounded
  :hints (("Goal"
           :use ((:instance fn-native-admin-config-name-chars
                            (n (nfix (- *fn-native-admin-config-name-width*
                                        (len (fn-bs-txn-natural-digits generation)))))
                            (generation generation))))))

(defun fn-native-admin-config-name (generation)
  (declare (xargs :guard t))
  (if (and (natp generation)
           (< generation *fn-native-admin-config-name-limit*))
      (fn-native-admin-config-name-bounded generation)
    nil))

; The physical adapter decodes exact framed records at its byte boundary, then
; calls this total logical function over those typed values.  A candidate that
; cannot replay into the same recovering state ordinary startup requires is a
; refusal before a namespace name is published.
(defun fn-native-admin-candidate-open-result (records frontier config-records)
  (declare (xargs :guard t))
  (let ((replayed (fn-cnode-config-replay config-records)))
    (if (not (equal (fn-replay-result-kind replayed) :ok))
        (list :refused :configuration)
      (let* ((cn (fn-replay-result-node replayed))
             (cfg (fn-cnode-config cn))
             (opened (fn-sn-open-observed (fn-cnode-domain cn)
                                          (fn-cfg-capacity (fn-cfg-value cfg))
                                          frontier records)))
        (if (and (fn-sn-open-okp opened)
                 (equal (fn-sf-phase (fn-sn-files (fn-sn-open-state opened)))
                        :recovering))
            (list :accepted cn)
          (list :refused :history))))))

(defun fn-native-admin-candidate-openp (records frontier config-records)
  (declare (xargs :guard t))
  (equal (car (fn-native-admin-candidate-open-result records frontier config-records))
         :accepted))

(defun fn-native-admin-clock-result (status reason stamp)
  (declare (xargs :guard t))
  (list status reason stamp))
(defun fn-native-admin-clock-status (result)
  (declare (xargs :guard t)) (fn-ag-car result))
(defun fn-native-admin-clock-stamp (result)
  (declare (xargs :guard t)) (fn-ag-car (fn-ag-cdr (fn-ag-cdr result))))

(defun fn-native-admin-clock-observation (monotonic wall)
  "The configuration-record codec, not raw Lisp, decides whether the two host
clock observations fit its schema-0 representation."
  (declare (xargs :guard t))
  (let ((stamp (fn-clock-observation monotonic wall 0 t)))
    (if (fn-cfg-stampp stamp)
        (fn-native-admin-clock-result :accepted nil stamp)
      (fn-native-admin-clock-result :refused :clock-unrepresentable nil))))

(defun fn-native-admin-publication-result (status reason generation name publication)
  (declare (xargs :guard t))
  (list status reason generation name publication))
(defun fn-native-admin-publication-status (result)
  (declare (xargs :guard t)) (fn-ag-car result))
(defun fn-native-admin-publication-reason (result)
  (declare (xargs :guard t)) (fn-ag-car (fn-ag-cdr result)))
(defun fn-native-admin-publication-generation (result)
  (declare (xargs :guard t)) (fn-ag-car (fn-ag-cdr (fn-ag-cdr result))))
(defun fn-native-admin-publication-name (result)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr result)))))
(defun fn-native-admin-publication-jpub (result)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr result))))))

(defun fn-native-admin-name-memberp (name names)
  (declare (xargs :guard t))
  (if (consp names)
      (or (equal name (car names)) (fn-native-admin-name-memberp name (cdr names)))
    nil))

(defun fn-native-admin-append-record (records record)
  "Total, one-record extension for the candidate replay.  The byte decoder
supplies proper record lists, but this boundary remains executable for a
malformed logical value and therefore does not make an unproved LISTP claim
to Common Lisp's guarded APPEND."
  (declare (xargs :guard t))
  (if (consp records)
      (cons (car records) (fn-native-admin-append-record (cdr records) record))
    (list record)))

(defun fn-native-admin-publication-authorize
    (records frontier config-records record lock-owned observed-names)
  "Authorize this exact final configuration name once.  LOCK-OWNED and
OBSERVED-NAMES are raw physical observations.  ACL2 binds them to the record's
generation, the candidate replay/open check, the fixed filename, and the
shared immutable publication state before raw Lisp may execute an I/O action."
  (declare (xargs :guard t))
  (if (not lock-owned)
      (fn-native-admin-publication-result :refused :lock nil nil nil)
    (let ((replayed (fn-cnode-config-replay config-records)))
      (if (not (equal (fn-replay-result-kind replayed) :ok))
          (fn-native-admin-publication-result :refused :configuration nil nil nil)
        (let* ((current (fn-cnode-config (fn-replay-result-node replayed)))
               ; Replay success supplies a configuration generation.  NFIX
               ; keeps this public executable boundary total for malformed
               ; logical inputs without changing a valid replay's generation.
               (generation (+ 1 (nfix (fn-cfg-generation current))))
               (name (fn-native-admin-config-name generation))
               (candidate (fn-native-admin-candidate-openp
                           records frontier
                           (fn-native-admin-append-record config-records record))))
          (cond ((not (fn-cfg-recordp record))
                 (fn-native-admin-publication-result :refused :record nil nil nil))
                ((or (not (equal (fn-cfg-record-sequence record)
                                 (fn-cfg-generation current)))
                     (not (equal (fn-cfg-record-generation record) generation)))
                 (fn-native-admin-publication-result :refused :generation nil nil nil))
                ((null name)
                 (fn-native-admin-publication-result :refused :generation-name nil nil nil))
                ((fn-native-admin-name-memberp name observed-names)
                 (fn-native-admin-publication-result :refused :occupied nil nil nil))
                ((not candidate)
                 (fn-native-admin-publication-result :refused :candidate nil nil nil))
                (t (fn-native-admin-publication-result
                    :accepted nil generation name (fn-jpub-initial t)))))))))

(defthm fn-native-admin-config-name-of-one
  (equal (fn-native-admin-config-name 1) "00000001.cfg"))

(defthm fn-native-admin-config-name-refuses-overflow
  (equal (fn-native-admin-config-name *fn-native-admin-config-name-limit*) nil))
