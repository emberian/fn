;; fn: the login binding as part of the configuration (PKT-221, PRF-166).
;
; books/login-binding.lisp decides a served POST against a table of
; (LOGIN . PRINCIPAL) bindings.  Until this book the table was a host global
; the credential file filled once, at start, so `fn principal bind' asked for
; a restart.  Now the table is rows of the configuration's `accounts' slot
; (books/config.lisp `fn-cfg-login-binding', mark 2 beside the account rows'
; marks 0 and 1: ONE credential table, three kinds of row), published through
; the owner's live reconfiguration like every other configuration change:
;
;   * at start the owner publishes the credential file's `signing' fields
;     (`fn-lb-sync-plan': one delta per login whose binding differs, chunked
;     into records of at most *fn-cfg-max-deltas*), and again whenever
;     `fn principal bind|unbind' asks it to after rewriting the file;
;   * a login the configuration holds as a redeemed account (mark 1) and the
;     credential file does not name is bound in the configuration itself
;     (PRF-388, PKT-560): `fn principal bind|unbind' on such a login is the
;     administrative record `account bind|unbind', admitted by
;     `fn-lb-account-bind-plan' only while the login holds that account, and
;     the start publication leaves its binding as it is;
;   * the gate the host calls (`fn-lb-ocfg-gate', as its buffer twin
;     books/article-buffer.lisp fn-ars-lb-ocfg-gate through
;     host/owner-host.lisp fn-owner-login-gate-buffer, called by host/native/owner.lisp
;     fnn-owner-attempt-served) reads the posting policy from the LIVE
;     configuration, as before, and the binding table from the configuration
;     the in-flight submission's CONNECTION pinned when it opened
;     (books/owner-config.lisp fn-ocfg-conn-config).  So a session keeps the
;     binding in force when it opened, however often the table changes, and a
;     connection opened after a publication is decided under the new table.
;
; What is not claimed here: that the owner's live configuration is the replay
; of its durable history across every publication is the owner's maintained
; relation (books/config-owner-publish.lisp fn-ocl-publish-installs-the-
; whole-staged-record hypothesises it; PRF-028's fn-ocl-no-reader-observes-a-
; half-change, which planning/current.md lists as uncertified at the current
; digest, is cited for the pins, not claimed).

(in-package "ACL2")
(include-book "login-binding")
(include-book "owner-config")
(include-book "config-owner-publish")
(local (include-book "identity-invariants"))
(local (include-book "records-canonicality"))

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; The table the configuration holds

(defun fn-lb-hex-text (principal)
  ; The row's spelling of a principal: its lowercase hexadecimal text.
  (declare (xargs :guard t))
  (if (fn-cbor-octet-listp principal)
      (fn-record-octets-string (fn-id-hex-octets principal))
    ""))

(defun fn-lb-text-principal (text)
  (declare (xargs :guard t))
  (let ((hex (fn-record-string-octets text)))
    (if (and (fn-id-hex-listp hex) (evenp (len hex)))
        (fn-id-unhex hex)
      nil)))

(defun fn-lb-row-binding (row)
  (declare (xargs :guard t))
  (cons (fn-record-string-octets (fn-cfg-row-a row))
        (fn-lb-text-principal (fn-cfg-row-b row))))

; The accounts table's walks here execute by loops (lane depth-debt,
; PRF-919): the table is operator data with no fixed cap (D27), and a
; recursion one control-stack frame per row could exhaust the 1,024 KiB
; stack.  Each is (mbe :logic <the recursion, unchanged> :exec <a loop>),
; equal by its <f>-loop-is-rev-onto (books/rev-onto.lisp).
(defun fn-lb-config-bindings-loop (rows acc)
  (declare (xargs :guard t))
  (if (consp rows)
      (fn-lb-config-bindings-loop
       (cdr rows)
       (if (fn-cfg-binding-rowp (car rows))
           (cons (fn-lb-row-binding (car rows)) acc)
         acc))
    (fn-ag-rev-onto acc nil)))

(defun fn-lb-config-bindings (rows)
  ; The binding rows (mark 2) of the accounts slot, as the gate's table.
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp rows)
           (if (fn-cfg-binding-rowp (car rows))
               (cons (fn-lb-row-binding (car rows))
                     (fn-lb-config-bindings (cdr rows)))
             (fn-lb-config-bindings (cdr rows)))
         nil)
       :exec (fn-lb-config-bindings-loop rows nil)))

(defthm fn-lb-config-bindings-loop-is-rev-onto
  (equal (fn-lb-config-bindings-loop rows acc)
         (fn-ag-rev-onto acc (fn-lb-config-bindings rows)))
  :hints (("Goal" :induct (fn-lb-config-bindings-loop rows acc)
                  :in-theory (union-theories
                              '(fn-lb-config-bindings-loop fn-lb-config-bindings
                                fn-ag-rev-onto car-cons cdr-cons)
                              (theory 'minimal-theory)))))

(verify-guards fn-lb-config-bindings
  :hints (("Goal" :in-theory (union-theories
                              '(fn-lb-config-bindings fn-ag-rev-onto fn-lb-config-bindings-loop-is-rev-onto)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))

(defun fn-lb-value-bindings (v)
  (declare (xargs :guard t))
  (fn-lb-config-bindings (fn-cfg-accounts v)))

; The delta binding NAME (octets) to PRINCIPAL (octets), or unbinding it when
; PRINCIPAL is nil.
(defun fn-lb-binding-delta (name principal)
  (declare (xargs :guard t))
  (fn-cfg-login-binding (fn-record-octets-string name)
                        (if principal (fn-lb-hex-text principal) "")))

(defun fn-lb-principalp (principal)
  (declare (xargs :guard t))
  (or (null principal)
      (and (fn-cbor-octet-listp principal) (equal (len principal) 32))))

(defun fn-lb-bindable-namep (name)
  (declare (xargs :guard t))
  (and (fn-cbor-octet-listp name)
       (fn-cfg-account-loginp (fn-record-octets-string name))))

; -----------------------------------------------------------------------------
; The pinned table and the gate the host calls

; The connection of the served submission in flight, or nil (none in flight,
; or a control submission, which has no connection and no login).
(defun fn-lb-inflight-id (o)
  (declare (xargs :guard t))
  (let ((sub (fn-own-inflight o)))
    (if (and sub (not (fn-own-control-submissionp sub)))
        (fn-own-sub-id sub)
      nil)))

; The binding table connection ID pinned when it opened.
(defun fn-lb-conn-bindings (oc id)
  (declare (xargs :guard t))
  (fn-lb-value-bindings (fn-cfg-value (fn-ocfg-conn-config oc id))))

; THE FUNCTION THE HOST CALLS, over the buffer (host/owner-host.lisp
; fn-owner-login-gate-buffer; fn-ars-lb-ocfg-gate-is-reference):
; the policy from the live configuration, the table from the pin.
(defun fn-lb-ocfg-gate (oc received)
  (declare (xargs :guard t))
  (fn-lb-owner-gate (fn-ocfg-owner oc) (fn-ocfg-config oc)
                    (fn-lb-conn-bindings oc (fn-lb-inflight-id (fn-ocfg-owner oc)))
                    received))

; The equation to the function books/login-binding.lisp's keystones are
; about: every one of them applies to the host's verdict with BINDINGS the
; in-flight connection's pinned table.
(defthm fn-lb-ocfg-gate-unfolds
  (equal (fn-lb-ocfg-gate oc received)
         (fn-lb-owner-gate (fn-ocfg-owner oc) (fn-ocfg-config oc)
                           (fn-lb-conn-bindings
                            oc (fn-lb-inflight-id (fn-ocfg-owner oc)))
                           received)))

; -----------------------------------------------------------------------------
; Row algebra

(local (defthm fn-lb-config-bindings-of-append
  (equal (fn-lb-config-bindings (append a b))
         (append (fn-lb-config-bindings a) (fn-lb-config-bindings b)))))

(defun fn-lb-has (login bindings)
  (declare (xargs :guard t))
  (if (consp bindings)
      (or (and (consp (car bindings)) (equal (car (car bindings)) login))
          (fn-lb-has login (cdr bindings)))
    nil))

(local (defthm fn-lb-binding-of-append
  (equal (fn-lb-binding login (append a b))
         (if (and login (fn-lb-has login a))
             (fn-lb-binding login a)
           (fn-lb-binding login b)))
  :hints (("Goal" :in-theory (enable fn-lb-binding)))))

(local (defthm fn-lb-binding-when-not-has
  (implies (not (fn-lb-has login bindings))
           (not (fn-lb-binding login bindings)))
  :hints (("Goal" :in-theory (enable fn-lb-binding)))))

(local (defthm fn-lb-binding-of-no-login
  (equal (fn-lb-binding nil bindings) nil)
  :hints (("Goal" :in-theory (enable fn-lb-binding)))))

(local (defthm fn-lb-string-octets-of-octets-string-when-octets
  (implies (fn-cbor-octet-listp name)
           (equal (fn-record-string-octets (fn-record-octets-string name))
                  name))
  :hints (("Goal" :use ((:instance fn-record-string-octets-of-octets-string
                                   (octets name)))))))

(local (in-theory (disable fn-record-octets-string fn-record-string-octets)))

(local (defthm fn-lb-without-binding-leaves-no-binding
  (implies (equal (fn-record-string-octets l) name)
           (not (fn-lb-has name (fn-lb-config-bindings
                                 (fn-cfg-rows-without-binding rows l)))))
  :hints (("Goal" :induct (fn-cfg-rows-without-binding rows l)
           :in-theory (e/d (fn-cfg-rows-without-binding)
                           (fn-record-string-octets))))))

(local (defthm fn-lb-without-binding-keeps-other-bindings
  (implies (not (equal other (fn-record-string-octets l)))
           (equal (fn-lb-binding other (fn-lb-config-bindings
                                        (fn-cfg-rows-without-binding rows l)))
                  (fn-lb-binding other (fn-lb-config-bindings rows))))
  :hints (("Goal" :induct (fn-cfg-rows-without-binding rows l)
           :in-theory (e/d (fn-cfg-rows-without-binding fn-lb-binding)
                           (fn-record-string-octets))))))

(local (defthm fn-lb-without-binding-keeps-other-has
  (implies (not (equal other (fn-record-string-octets l)))
           (equal (fn-lb-has other (fn-lb-config-bindings
                                    (fn-cfg-rows-without-binding rows l)))
                  (fn-lb-has other (fn-lb-config-bindings rows))))
  :hints (("Goal" :induct (fn-cfg-rows-without-binding rows l)
           :in-theory (e/d (fn-cfg-rows-without-binding)
                           (fn-record-string-octets))))))

(local (defthm fn-lb-hex-listp-is-cfg-hex
  (implies (fn-id-hex-listp x) (fn-cfg-hex-digit-octetsp x))
  :hints (("Goal" :in-theory (enable fn-id-hex-listp fn-id-hex-digitp
                                     fn-cfg-hex-digit-octetsp
                                     fn-cfg-hex-digit-octetp)))))

(local (in-theory (enable (tau-system)))) ; tau-cost: this form needs tau
(local (defthm fn-lb-hex-listp-is-ascii
  (implies (fn-id-hex-listp x) (fn-record-ascii-octet-listp x))
  :hints (("Goal" :in-theory (enable fn-id-hex-listp fn-id-hex-digitp
                                     fn-record-ascii-octet-listp)))))
(local (in-theory (disable (tau-system))))

(local (defthm fn-lb-evenp-len-hex-octets
  (evenp (len (fn-id-hex-octets x)))
  :hints (("Goal" :in-theory (enable fn-id-hex-octets evenp)))))

(local (defthm fn-lb-text-principal-of-hex-text
  (implies (fn-cbor-octet-listp p)
           (equal (fn-lb-text-principal (fn-lb-hex-text p)) p))
  :hints (("Goal" :in-theory (disable fn-id-unhex fn-id-hex-octets
                                      fn-id-hex-listp)))))

(defthm fn-lb-hex-text-is-principal-text
  (implies (and (fn-cbor-octet-listp p) (equal (len p) 32))
           (fn-cfg-hex-textp (fn-lb-hex-text p) 64))
  :hints (("Goal" :in-theory (e/d (fn-cfg-hex-textp fn-cfg-labelp
                                   fn-record-ascii-stringp)
                                  (fn-id-hex-octets fn-id-hex-listp)))))

(defthm fn-lb-hex-text-is-not-empty
  (implies (and (fn-cbor-octet-listp p) p)
           (not (equal (fn-lb-hex-text p) "")))
  :hints (("Goal" :use ((:instance fn-lb-text-principal-of-hex-text))
           :in-theory (disable fn-lb-text-principal-of-hex-text))))

(local (defthm fn-lb-accounts-of-binding-delta
  (equal (fn-cfg-accounts (fn-cfg-apply-delta v gen stamp
                                              (fn-lb-binding-delta name p)))
         (append (fn-cfg-rows-without-binding (fn-cfg-accounts v)
                                              (fn-record-octets-string name))
                 (fn-cfg-binding-rows (fn-record-octets-string name)
                                      (if p (fn-lb-hex-text p) ""))))
  :hints (("Goal" :in-theory (enable fn-cfg-apply-delta fn-cfg-login-binding)))))

; -----------------------------------------------------------------------------
; One delta

; KEYSTONE (the delta).  Applying NAME's binding delta binds NAME to exactly
; PRINCIPAL (unbinds it when PRINCIPAL is nil).
(defthm fn-lb-binding-delta-binds-the-login
  (implies (and (fn-cbor-octet-listp name) (consp name)
                (fn-lb-principalp principal))
           (equal (fn-lb-binding
                   name (fn-lb-value-bindings
                         (fn-cfg-apply-delta v gen stamp
                                             (fn-lb-binding-delta name principal))))
                  principal))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cfg-binding-rows fn-lb-binding)
                           (fn-lb-binding-delta fn-lb-hex-text
                            fn-lb-text-principal)))))

; KEYSTONE (the delta).  It leaves every other login's binding as it was.
(defthm fn-lb-binding-delta-keeps-other-logins
  (implies (and (fn-cbor-octet-listp name)
                (not (equal other name)))
           (equal (fn-lb-binding
                   other (fn-lb-value-bindings
                          (fn-cfg-apply-delta v gen stamp
                                              (fn-lb-binding-delta name principal))))
                  (fn-lb-binding other (fn-lb-value-bindings v))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-cfg-binding-rows fn-lb-binding)
                           (fn-lb-binding-delta fn-lb-hex-text
                            fn-lb-text-principal)))))

; KEYSTONE (admission).  The delta for a bindable login and a principal (or
; nil) is admitted against every configuration: its reason is nil.
(defthm fn-lb-binding-delta-is-admitted
  (implies (and (fn-lb-bindable-namep name)
                (fn-lb-principalp principal))
           (not (fn-cfg-delta-reason v gen stamp reserved ceiling
                                     (fn-lb-binding-delta name principal))))
  :hints (("Goal" :in-theory (e/d (fn-cfg-delta-reason fn-cfg-login-binding
                                   fn-cfg-login-binding-reason
                                   fn-cfg-binding-rows fn-cfg-deltap
                                   fn-cfg-row-listp fn-cfg-rowp
                                   fn-cfg-hex-textp)
                                  (fn-lb-hex-text fn-cfg-labelp
                                   fn-cfg-graphic-octetsp
                                   ; else the :use is rewritten to T by itself
                                   fn-lb-hex-text-is-principal-text))
           :use ((:instance fn-lb-hex-text-is-principal-text (p principal))))))

; -----------------------------------------------------------------------------
; The start publication: the credential file's table into the configuration
;
; FILE is the table books/native-auth-profile.lisp fn-native-auth-load-
; bindings read from the credential file; CURRENT the configuration's
; (fn-lb-value-bindings).  The plan names, as (LOGIN . PRINCIPAL) pairs, the
; file's binding of every login the configuration binds otherwise, and nil
; for every login the configuration binds and the file does not.  The host
; publishes the pairs' deltas in records of at most *fn-cfg-max-deltas*
; (`fn-lb-chunks'); each delta is admitted against any configuration
; (fn-lb-binding-delta-is-admitted) and none reads the record's generation
; or stamp, so the records compose.

(defun fn-lb-sync-binds-loop (entries file current acc)
  (declare (xargs :guard t))
  (if (consp entries)
      (fn-lb-sync-binds-loop
       (cdr entries) file current
       (let ((name (and (consp (car entries)) (car (car entries)))))
         (if (and name
                  (not (equal (fn-lb-binding name current)
                              (fn-lb-binding name file))))
             (cons (cons name (fn-lb-binding name file)) acc)
           acc)))
    (fn-ag-rev-onto acc nil)))

(defun fn-lb-sync-binds (entries file current)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp entries)
           (let ((name (and (consp (car entries)) (car (car entries)))))
             (if (and name
                      (not (equal (fn-lb-binding name current)
                                  (fn-lb-binding name file))))
                 (cons (cons name (fn-lb-binding name file))
                       (fn-lb-sync-binds (cdr entries) file current))
               (fn-lb-sync-binds (cdr entries) file current)))
         nil)
       :exec (fn-lb-sync-binds-loop entries file current nil)))

(defthm fn-lb-sync-binds-loop-is-rev-onto
  (equal (fn-lb-sync-binds-loop entries file current acc)
         (fn-ag-rev-onto acc (fn-lb-sync-binds entries file current)))
  :hints (("Goal" :induct (fn-lb-sync-binds-loop entries file current acc)
                  :in-theory (union-theories
                              '(fn-lb-sync-binds-loop fn-lb-sync-binds
                                fn-ag-rev-onto car-cons cdr-cons)
                              (theory 'minimal-theory)))))

(verify-guards fn-lb-sync-binds
  :hints (("Goal" :in-theory (union-theories
                              '(fn-lb-sync-binds fn-ag-rev-onto fn-lb-sync-binds-loop-is-rev-onto)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))

; PRF-388 (PKT-560): whether ROWS (the accounts slot) hold NAME (octets) as
; a redeemed account (mark 1), the row XREDEEM writes.  A tombstone (mark 7)
; holds no account.
(defun fn-lb-account-heldp (name rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (or (and (equal (fn-cfg-row-n (car rows)) 1)
               (equal (fn-record-string-octets (fn-cfg-row-b (car rows))) name))
          (fn-lb-account-heldp name (cdr rows)))
    nil))

; The configuration, not the credential file, owns NAME's binding: NAME is
; a redeemed account the file does not name.  The start publication leaves
; such a binding as the configuration holds it (`account bind' wrote it).
(defun fn-lb-config-ownsp (name file rows)
  (declare (xargs :guard t))
  (and (fn-lb-account-heldp name rows)
       (not (fn-lb-has name file))))

(defun fn-lb-sync-unbinds-loop (entries file current rows acc)
  (declare (xargs :guard t))
  (if (consp entries)
      (fn-lb-sync-unbinds-loop
       (cdr entries) file current rows
       (let ((name (and (consp (car entries)) (car (car entries)))))
         (if (and name (fn-lb-binding name current)
                  (not (fn-lb-binding name file))
                  (not (fn-lb-config-ownsp name file rows)))
             (cons (cons name nil) acc)
           acc)))
    (fn-ag-rev-onto acc nil)))

(defun fn-lb-sync-unbinds (entries file current rows)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp entries)
           (let ((name (and (consp (car entries)) (car (car entries)))))
             (if (and name (fn-lb-binding name current)
                      (not (fn-lb-binding name file))
                      (not (fn-lb-config-ownsp name file rows)))
                 (cons (cons name nil)
                       (fn-lb-sync-unbinds (cdr entries) file current rows))
               (fn-lb-sync-unbinds (cdr entries) file current rows)))
         nil)
       :exec (fn-lb-sync-unbinds-loop entries file current rows nil)))

(defthm fn-lb-sync-unbinds-loop-is-rev-onto
  (equal (fn-lb-sync-unbinds-loop entries file current rows acc)
         (fn-ag-rev-onto acc (fn-lb-sync-unbinds entries file current rows)))
  :hints (("Goal" :induct (fn-lb-sync-unbinds-loop entries file current rows acc)
                  :in-theory (union-theories
                              '(fn-lb-sync-unbinds-loop fn-lb-sync-unbinds
                                fn-ag-rev-onto car-cons cdr-cons)
                              (theory 'minimal-theory)))))

(verify-guards fn-lb-sync-unbinds
  :hints (("Goal" :in-theory (union-theories
                              '(fn-lb-sync-unbinds fn-ag-rev-onto fn-lb-sync-unbinds-loop-is-rev-onto)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))

(defun fn-lb-sync-pairs (file current rows)
  (declare (xargs :guard t))
  (append (fn-lb-sync-binds file file current)
          (fn-lb-sync-unbinds current file current rows)))

(defun fn-lb-pairs-okp (pairs)
  (declare (xargs :guard t))
  (if (consp pairs)
      (and (consp (car pairs))
           (fn-lb-bindable-namep (car (car pairs)))
           (consp (car (car pairs)))
           (fn-lb-principalp (cdr (car pairs)))
           (fn-lb-pairs-okp (cdr pairs)))
    (null pairs)))

(defun fn-lb-pairs-deltas-loop (pairs acc)
  (declare (xargs :guard t))
  (if (consp pairs)
      (fn-lb-pairs-deltas-loop
       (cdr pairs)
       (cons (fn-lb-binding-delta (and (consp (car pairs)) (car (car pairs)))
                                  (and (consp (car pairs)) (cdr (car pairs))))
             acc))
    (fn-ag-rev-onto acc nil)))

(defun fn-lb-pairs-deltas (pairs)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp pairs)
           (cons (fn-lb-binding-delta (and (consp (car pairs)) (car (car pairs)))
                                      (and (consp (car pairs)) (cdr (car pairs))))
                 (fn-lb-pairs-deltas (cdr pairs)))
         nil)
       :exec (fn-lb-pairs-deltas-loop pairs nil)))

(defthm fn-lb-pairs-deltas-loop-is-rev-onto
  (equal (fn-lb-pairs-deltas-loop pairs acc)
         (fn-ag-rev-onto acc (fn-lb-pairs-deltas pairs)))
  :hints (("Goal" :induct (fn-lb-pairs-deltas-loop pairs acc)
                  :in-theory (union-theories
                              '(fn-lb-pairs-deltas-loop fn-lb-pairs-deltas
                                fn-ag-rev-onto car-cons cdr-cons)
                              (theory 'minimal-theory)))))

(verify-guards fn-lb-pairs-deltas
  :hints (("Goal" :in-theory (union-theories
                              '(fn-lb-pairs-deltas fn-ag-rev-onto fn-lb-pairs-deltas-loop-is-rev-onto)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))

(defun fn-lb-chunks-loop (xs n acc)
  (declare (xargs :guard (and (true-listp xs) (posp n)) :measure (len xs)))
  (if (and (consp xs) (posp n))
      (fn-lb-chunks-loop (nthcdr (min n (len xs)) xs) n
                         (cons (take (min n (len xs)) xs) acc))
    (fn-ag-rev-onto acc nil)))

(defun fn-lb-chunks (xs n)
  ; XS in consecutive pieces of at most N (N >= 1).
  (declare (xargs :guard (and (true-listp xs) (posp n)) :measure (len xs)
                  :verify-guards nil))
  (mbe :logic
       (if (and (consp xs) (posp n))
           (cons (take (min n (len xs)) xs)
                 (fn-lb-chunks (nthcdr (min n (len xs)) xs) n))
         nil)
       :exec (fn-lb-chunks-loop xs n nil)))

(defthm fn-lb-chunks-loop-is-rev-onto
  (equal (fn-lb-chunks-loop xs n acc)
         (fn-ag-rev-onto acc (fn-lb-chunks xs n)))
  :hints (("Goal" :induct (fn-lb-chunks-loop xs n acc)
                  :in-theory (disable take nthcdr min))))

(verify-guards fn-lb-chunks)

(defun fn-lb-flatten (chunks)
  (declare (xargs :guard t))
  (if (consp chunks)
      (append (true-list-fix (car chunks)) (fn-lb-flatten (cdr chunks)))
    nil))

; The host-called plan (host/owner-host.lisp fn-owner-login-bindings-sync):
; (:ok RECORDS) with RECORDS the delta lists to publish in order (nil when
; the configuration already binds every login as the file does), or
; (:refused :binding-login) when a login the plan would write is not one the
; configuration can spell.
(defun fn-lb-sync-plan (file v)
  (declare (xargs :guard t))
  (let ((pairs (fn-lb-sync-pairs file (fn-lb-value-bindings v)
                                 (fn-cfg-accounts v))))
    (if (fn-lb-pairs-okp pairs)
        (list :ok (fn-lb-chunks (fn-lb-pairs-deltas pairs) *fn-cfg-max-deltas*))
      (list :refused :binding-login))))

; --- the fold

(defun fn-lb-pairs-targetp (pairs file)
  (declare (xargs :guard t))
  (if (consp pairs)
      (and (consp (car pairs))
           (equal (cdr (car pairs)) (fn-lb-binding (car (car pairs)) file))
           (fn-lb-pairs-targetp (cdr pairs) file))
    t))

(local (defthm fn-lb-apply-of-cons
  (equal (fn-cfg-apply v gen stamp (cons d ds))
         (fn-cfg-apply (fn-cfg-apply-delta v gen stamp d) gen stamp ds))
  :hints (("Goal" :in-theory (enable fn-cfg-apply)))))

(local (defthm fn-lb-apply-of-nil
  (equal (fn-cfg-apply v gen stamp nil) v)
  :hints (("Goal" :in-theory (enable fn-cfg-apply)))))

(local (defun fn-lb-pairs-ind (v gen stamp pairs)
  (if (consp pairs)
      (fn-lb-pairs-ind (fn-cfg-apply-delta
                        v gen stamp
                        (fn-lb-binding-delta (and (consp (car pairs))
                                                  (car (car pairs)))
                                             (and (consp (car pairs))
                                                  (cdr (car pairs)))))
                       gen stamp (cdr pairs))
    (list v gen stamp))))

(defthm fn-lb-pairs-deltas-set-exactly-their-logins
  (implies (and (fn-lb-pairs-okp pairs)
                (fn-lb-pairs-targetp pairs file))
           (equal (fn-lb-binding name
                                 (fn-lb-value-bindings
                                  (fn-cfg-apply v gen stamp
                                                (fn-lb-pairs-deltas pairs))))
                  (if (and name (fn-lb-has name pairs))
                      (fn-lb-binding name file)
                    (fn-lb-binding name (fn-lb-value-bindings v)))))
  :hints (("Goal" :induct (fn-lb-pairs-ind v gen stamp pairs)
           :in-theory (e/d () (fn-lb-binding-delta fn-lb-value-bindings
                               fn-cfg-account-loginp)))
          ("Subgoal *1/2" :cases ((equal name (car (car pairs)))))))

(local (defthm fn-lb-has-when-binding
  (implies (fn-lb-binding login bindings) (fn-lb-has login bindings))
  :hints (("Goal" :in-theory (enable fn-lb-binding)))))

(local (defthm fn-lb-binding-names-a-login
  (implies (fn-lb-binding login bindings)
           (and login (fn-lb-has login bindings)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-lb-binding)))))

(local (defthm fn-lb-has-of-append
  (equal (fn-lb-has login (append a b))
         (or (fn-lb-has login a) (fn-lb-has login b)))))

(local (defthm fn-lb-sync-binds-names-a-differing-login
  (implies (and login (fn-lb-has login entries)
                (not (equal (fn-lb-binding login current)
                            (fn-lb-binding login file))))
           (fn-lb-has login (fn-lb-sync-binds entries file current)))))

(local (defthm fn-lb-sync-unbinds-names-an-unfiled-login
  (implies (and login (fn-lb-has login entries)
                (fn-lb-binding login current)
                (not (fn-lb-binding login file))
                (not (fn-lb-config-ownsp login file rows)))
           (fn-lb-has login (fn-lb-sync-unbinds entries file current rows)))
  :hints (("Goal" :in-theory (disable fn-lb-config-ownsp)))))

(local (defthm fn-lb-sync-unbinds-skips-an-owned-login
  (implies (fn-lb-config-ownsp login file rows)
           (not (fn-lb-has login (fn-lb-sync-unbinds entries file current rows))))
  :hints (("Goal" :in-theory (disable fn-lb-config-ownsp)))))

(local (defthm fn-lb-config-ownsp-names-no-file-login
  (implies (fn-lb-config-ownsp login file rows)
           (and (not (fn-lb-has login file))
                (not (fn-lb-binding login file))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-lb-binding)))))

(local (defthm fn-lb-sync-binds-names-only-entries
  (implies (not (fn-lb-has login entries))
           (not (fn-lb-has login (fn-lb-sync-binds entries file current))))))

(local (defthm fn-lb-sync-binds-targetp
  (fn-lb-pairs-targetp (fn-lb-sync-binds entries file current) file)))

(local (defthm fn-lb-sync-unbinds-targetp
  (fn-lb-pairs-targetp (fn-lb-sync-unbinds entries file current rows) file)))

(local (defthm fn-lb-pairs-targetp-of-append
  (implies (and (fn-lb-pairs-targetp a file) (fn-lb-pairs-targetp b file))
           (fn-lb-pairs-targetp (append a b) file))))

; KEYSTONE (the start publication; PRF-166, PRF-388).  When the plan is
; :ok, applying its deltas leaves every login bound as the credential file
; binds it (the file's principal, or unbound), except a login the
; configuration owns -- a redeemed account the file does not name -- whose
; binding stays as the configuration held it.
(defthm fn-lb-sync-binds-file-logins-as-the-file-does-and-keeps-account-bindings
  (implies (fn-lb-pairs-okp (fn-lb-sync-pairs file (fn-lb-value-bindings v)
                                              (fn-cfg-accounts v)))
           (equal (fn-lb-binding
                   name
                   (fn-lb-value-bindings
                    (fn-cfg-apply v gen stamp
                                  (fn-lb-pairs-deltas
                                   (fn-lb-sync-pairs
                                    file (fn-lb-value-bindings v)
                                    (fn-cfg-accounts v))))))
                  (if (fn-lb-config-ownsp name file (fn-cfg-accounts v))
                      (fn-lb-binding name (fn-lb-value-bindings v))
                    (fn-lb-binding name file))))
  :hints (("Goal" :in-theory (disable fn-lb-value-bindings fn-lb-pairs-deltas
                                      fn-lb-sync-binds fn-lb-sync-unbinds
                                      fn-lb-pairs-okp fn-lb-pairs-deltas-set-exactly-their-logins
                                      fn-lb-binding-when-not-has fn-lb-config-ownsp
                                      fn-lb-sync-unbinds-names-an-unfiled-login
                                      fn-lb-sync-unbinds-skips-an-owned-login)
           :use ((:instance fn-lb-pairs-deltas-set-exactly-their-logins
                            (pairs (fn-lb-sync-pairs
                                    file (fn-lb-value-bindings v)
                                    (fn-cfg-accounts v))))
                 (:instance fn-lb-binding-when-not-has
                            (login name) (bindings file))
                 (:instance fn-lb-has-when-binding
                            (login name)
                            (bindings (fn-lb-value-bindings v)))
                 (:instance fn-lb-sync-unbinds-names-an-unfiled-login
                            (login name)
                            (entries (fn-lb-value-bindings v))
                            (current (fn-lb-value-bindings v))
                            (rows (fn-cfg-accounts v)))
                 (:instance fn-lb-sync-unbinds-skips-an-owned-login
                            (login name)
                            (entries (fn-lb-value-bindings v))
                            (current (fn-lb-value-bindings v))
                            (rows (fn-cfg-accounts v))))
           :cases ((fn-lb-config-ownsp name file (fn-cfg-accounts v))
                   (and name (fn-lb-has name file))
                   (and name (not (fn-lb-has name file)))
                   (not name)))))

(local (defthm fn-lb-append-take-nthcdr
  (implies (and (natp n) (<= n (len xs)))
           (equal (append (take n xs) (nthcdr n xs)) xs))))

(local (defthm fn-lb-true-list-fix-of-take
  (equal (true-list-fix (take n xs)) (take n xs))))

(local (defthm fn-lb-nthcdr-len
  (implies (true-listp xs) (equal (nthcdr (len xs) xs) nil))))

; The records the plan hands the host are its deltas in order.
(defthm fn-lb-chunks-flatten
  (implies (and (true-listp xs) (posp n))
           (equal (fn-lb-flatten (fn-lb-chunks xs n)) xs)))

; No binding delta reads the record's generation or stamp, so one publication
; per record composes to the flat application above.
(local (defthm fn-lb-binding-delta-ignores-the-record-coordinates
  (implies (and (syntaxp (not (and (equal gen ''0) (equal stamp ''nil))))
                (equal (fn-cfg-delta-kind d) :login-binding))
           (equal (fn-cfg-apply-delta v gen stamp d)
                  (fn-cfg-apply-delta v 0 nil d)))
  :hints (("Goal" :in-theory (enable fn-cfg-apply-delta)))))

(local (defthm fn-lb-binding-delta-kind
  (equal (fn-cfg-delta-kind (fn-lb-binding-delta n p)) :login-binding)
  :hints (("Goal" :in-theory (enable fn-lb-binding-delta
                                     fn-cfg-login-binding)))))

(defthm fn-lb-pairs-deltas-ignore-the-record-coordinates
  (equal (fn-cfg-apply v gen stamp (fn-lb-pairs-deltas pairs))
         (fn-cfg-apply v 0 nil (fn-lb-pairs-deltas pairs)))
  ; Not a rewrite rule: it would rewrite its own right side forever.
  :rule-classes nil
  :hints (("Goal" :induct (fn-lb-pairs-ind v 0 nil pairs)
           :in-theory (disable fn-lb-binding-delta))))

; -----------------------------------------------------------------------------
; The owner: an open connection keeps its table, a new one pins the published
;
; The host's live change is `(:reconfigure other deltas)' through
; fn-ocfg-step (host/owner-host.lisp fn-owner-reconfigure-deltas) and then
; fn-ocl-publish (fn-owner-reconfigure-complete), the one path every live
; configuration change takes (host/native/admin.lisp
; fnn-owner-live-reconfigure-locked).

(local (defthm fn-lb-reconfigure-keeps-pins
  (equal (fn-ocfg-pins (fn-ocfg-step oc (list :reconfigure other deltas) fn-arena))
         (fn-ocfg-pins oc))
  :hints (("Goal" :in-theory (enable fn-ocfg-step fn-ocfg-reconfigure)))))

; KEYSTONE (the pinned view, over the host's live path).  Staging and
; publishing any configuration change, a binding change included, leaves
; every connection's pinned binding table exactly as it was.
(defthm fn-lb-a-publication-keeps-every-open-connections-table
  (equal (fn-lb-conn-bindings
          (mv-nth 1 (fn-ocl-publish
                     (fn-ocfg-step oc (list :reconfigure other deltas) fn-arena)
                     generation max-octets))
          id)
         (fn-lb-conn-bindings oc id))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-conn-config)
                                  (fn-lb-value-bindings fn-ocfg-step))
           :use ((:instance fn-ocl-publish-leaves-connections-and-pins
                            (oc (fn-ocfg-step oc (list :reconfigure other
                                                       deltas) fn-arena)))))))

; KEYSTONE (the pinned view, over any owner trace).  After any sequence of
; owner events that does not re-pin connection ID (fn-ocfg-repins-forp:
; :advance, which no host path calls, or its close), the gate the host calls
; decides a submission of ID under the table ID had pinned before the trace:
; the binding in force when the session opened.
(defthm fn-lb-an-open-session-is-decided-under-its-pinned-table
  (implies (and (fn-ocfg-pin-find id (fn-ocfg-pins oc))
                (not (fn-ocfg-repins-forp id events))
                (equal (fn-lb-inflight-id (fn-ocfg-owner (fn-ocfg-run oc events fn-arena)))
                       id))
           (equal (fn-lb-ocfg-gate (fn-ocfg-run oc events fn-arena) received)
                  (fn-lb-owner-gate (fn-ocfg-owner (fn-ocfg-run oc events fn-arena))
                                    (fn-ocfg-config (fn-ocfg-run oc events fn-arena))
                                    (fn-lb-conn-bindings oc id)
                                    received)))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-conn-config)
                                  (fn-lb-value-bindings fn-lb-owner-gate
                                   fn-lb-inflight-id fn-ocfg-run))
           :use ((:instance fn-ocfg-pin-is-stable-without-advance)))))

(local (defthm fn-lb-staged-record-of-a-fresh-reconfigure
  (implies (and (not (fn-ocfg-staged oc))
                (fn-ocfg-staged (fn-ocfg-step oc (list :reconfigure other deltas) fn-arena)))
           (and (equal (fn-ocfg-staged (fn-ocfg-step oc (list :reconfigure other
                                                                deltas) fn-arena))
                       (fn-ocfg-reconfig-record oc deltas))
                (equal (fn-ocfg-config (fn-ocfg-step oc (list :reconfigure other
                                                                deltas) fn-arena))
                       (fn-ocfg-config oc))))
  :hints (("Goal" :in-theory (enable fn-ocfg-step fn-ocfg-reconfigure)))))

(local (defthm fn-lb-durable-publish-had-a-staged-record
  (implies (equal (mv-nth 0 (fn-ocl-publish oc generation max-octets)) :durable)
           (fn-ocfg-staged oc))
  :hints (("Goal" :in-theory (enable fn-ocl-publish)))))

(local (defthm fn-lb-published-config-of-a-fresh-reconfigure
  (let* ((staged (fn-ocfg-step oc (list :reconfigure other deltas) fn-arena))
         (result (fn-ocl-publish staged generation max-octets)))
    (implies (and (not (fn-ocfg-staged oc))
                  (equal (mv-nth 0 result) :durable)
                  (fn-ocl-config-historyp staged))
             (equal (fn-cfg-value (fn-ocfg-config (mv-nth 1 result)))
                    (fn-cfg-apply (fn-cfg-value (fn-ocfg-config oc))
                                  (+ 1 (fn-cfg-generation (fn-ocfg-config oc)))
                                  (fn-ocfg-config-stamp (fn-own-clock (fn-ocfg-owner oc)))
                                  deltas))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (fn-ocfg-reconfig-record fn-cfg-apply-record)
                           (fn-ocfg-step fn-ocl-publish fn-cfg-apply
                            fn-ocl-config-historyp fn-ocfg-config-stamp
                            fn-ocl-publish-installs-the-whole-staged-record
                            fn-lb-durable-publish-had-a-staged-record
                            fn-lb-staged-record-of-a-fresh-reconfigure))
           :use ((:instance fn-ocl-publish-installs-the-whole-staged-record
                            (oc (fn-ocfg-step oc (list :reconfigure other deltas) fn-arena)))
                 (:instance fn-lb-durable-publish-had-a-staged-record
                            (oc (fn-ocfg-step oc (list :reconfigure other deltas) fn-arena)))
                 (:instance fn-lb-staged-record-of-a-fresh-reconfigure))))))

; A fresh connection pins the live configuration when no pin is left at its
; identifier (what fn-ocfg-statep guarantees in
; fn-ocfg-open-pins-the-live-configuration; stated here as the one fact used).
(local (defthm fn-lb-open-pins-the-live-configuration-at-a-free-identifier
  (implies (and (not (fn-ocfg-pin-find (fn-own-next-id (fn-ocfg-owner oc))
                                       (fn-ocfg-pins oc)))
                (fn-own-find-conn
                 (fn-own-next-id (fn-ocfg-owner oc))
                 (fn-own-conns (fn-ocfg-owner (cdr (fn-ocfg-open oc acfg))))))
           (equal (fn-ocfg-conn-config (cdr (fn-ocfg-open oc acfg))
                                       (fn-own-next-id (fn-ocfg-owner oc)))
                  (fn-ocfg-config oc)))
  :hints (("Goal" :in-theory (enable fn-ocfg-open fn-ocfg-conn-config
                                     fn-ocfg-pin-add fn-ocfg-pin-find)))))

; KEYSTONE (a new connection after the change).  When the owner, with nothing
; staged, stages PAIRS' binding deltas and publishes them durably, a
; connection it opens next pins a table that binds every login PAIRS names as
; FILE does, and every other login as before.  Hypotheses: the published
; configuration is its store history's replay before the publish (the
; owner's maintained relation, fn-ocl-config-historyp), no stale pin at the
; fresh identifier (a consequence of the owner relation fn-ocfg-statep,
; books/owner-config.lisp fn-ocfg-open-pins-the-live-configuration), and that
; the open admitted the connection.  With PAIRS the start plan's
; (fn-lb-sync-binds-file-logins-as-the-file-does-and-keeps-account-bindings)
; that is the credential file's table.
(defthm fn-lb-a-connection-opened-after-a-publication-is-bound-anew
  (let* ((staged (fn-ocfg-step oc (list :reconfigure other
                                        (fn-lb-pairs-deltas pairs)) fn-arena))
         (result (fn-ocl-publish staged generation max-octets))
         (published (mv-nth 1 result))
         (opened (cdr (fn-ocfg-open published acfg)))
         (new (fn-own-next-id (fn-ocfg-owner published))))
    (implies (and (not (fn-ocfg-staged oc))
                  (equal (mv-nth 0 result) :durable)
                  (fn-ocl-config-historyp staged)
                  (not (fn-ocfg-pin-find new (fn-ocfg-pins published)))
                  (fn-own-find-conn new (fn-own-conns (fn-ocfg-owner opened)))
                  (fn-lb-pairs-okp pairs)
                  (fn-lb-pairs-targetp pairs file))
             (equal (fn-lb-binding name (fn-lb-conn-bindings opened new))
                    (if (and name (fn-lb-has name pairs))
                        (fn-lb-binding name file)
                      (fn-lb-binding name (fn-lb-value-bindings
                                           (fn-cfg-value (fn-ocfg-config oc))))))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (union-theories '(fn-lb-conn-bindings)
                                      (theory 'minimal-theory))
           :use ((:instance fn-lb-open-pins-the-live-configuration-at-a-free-identifier
                            (oc (mv-nth 1 (fn-ocl-publish
                                           (fn-ocfg-step oc (list :reconfigure other
                                                                  (fn-lb-pairs-deltas pairs)) fn-arena)
                                           generation max-octets))))
                 (:instance fn-lb-published-config-of-a-fresh-reconfigure
                            (deltas (fn-lb-pairs-deltas pairs)))
                 (:instance fn-lb-pairs-deltas-set-exactly-their-logins
                            (v (fn-cfg-value (fn-ocfg-config oc)))
                            (gen (+ 1 (fn-cfg-generation (fn-ocfg-config oc))))
                            (stamp (fn-ocfg-config-stamp
                                    (fn-own-clock (fn-ocfg-owner oc)))))))))

; -----------------------------------------------------------------------------
; PRF-388 (PKT-560): binding a redeemed account's login
;
; `fn principal bind LOGIN HEX' binds a login of the credential file in the
; file (books/native-auth-admin.lisp fn-native-auth-admin-bind).  A login
; redeemed from an invitation (books/accounts.lisp) is not in the file: its
; credential is a row of the configuration's accounts slot, so its binding
; is too.  The verb's answer for a login the file does not hold is :account,
; and the operator then sends the administrative record `account bind LOGIN
; HEX' (`account unbind LOGIN'), live to the owner or offline into the
; store.  This plan decides it over the configuration it would change: the
; binding delta when LOGIN holds a redeemed account, else a refusal by name
; (`unknown-login': neither the file's login nor an account's).

; The principal of the verb's HEX octets (64 hexadecimal digits), nil for
; the unbind (no HEX), :bad otherwise.
(defun fn-lb-hex-principal (hex)
  (declare (xargs :guard t))
  (cond ((null hex) nil)
        ((and (true-listp hex) (equal (len hex) 64) (fn-id-hex-listp hex))
         (fn-id-unhex hex))
        (t :bad)))

; (:ok DELTAS) or (:refused REASON).  NAME the login's octets.
(defun fn-lb-account-bind-plan (name hex v)
  (declare (xargs :guard t))
  (let ((principal (fn-lb-hex-principal hex)))
    (cond ((not (fn-lb-bindable-namep name)) (list :refused :binding-login))
          ((not (fn-lb-principalp principal)) (list :refused :binding-principal))
          ((not (fn-lb-account-heldp name (fn-cfg-accounts v)))
           (list :refused :unknown-login))
          (t (list :ok (list (fn-lb-binding-delta name principal)))))))

; KEYSTONE (PRF-388, admission).  The subject is `fn-lb-account-bind-plan',
; which host/native-admin-host.lisp fn-native-admin-host-owner-reconfigure
; (the live owner's arm, called by host/native/admin.lisp for a control
; vector) and fn-native-admin-host-apply (the offline arm) compute for an
; `account bind|unbind' plan: the plan stages a record exactly when the
; login is a login the configuration can spell, the principal is 32 octets
; (or absent, the unbind), and the configuration holds the login as a
; redeemed account.
(defthm fn-lb-account-bind-plan-admits-exactly-a-held-account-login
  (iff (equal (car (fn-lb-account-bind-plan name hex v)) :ok)
       (and (fn-lb-bindable-namep name)
            (fn-lb-principalp (fn-lb-hex-principal hex))
            (fn-lb-account-heldp name (fn-cfg-accounts v))))
  :hints (("Goal" :in-theory (disable fn-lb-bindable-namep fn-lb-principalp
                                      fn-lb-hex-principal fn-lb-account-heldp
                                      fn-lb-binding-delta))))

(local (defthm fn-lb-account-heldp-of-append
  (equal (fn-lb-account-heldp name (append a b))
         (or (fn-lb-account-heldp name a) (fn-lb-account-heldp name b)))))

(local (defthm fn-lb-account-heldp-of-rows-without-binding
  (equal (fn-lb-account-heldp name (fn-cfg-rows-without-binding rows l))
         (fn-lb-account-heldp name rows))
  :hints (("Goal" :in-theory (enable fn-cfg-rows-without-binding
                                     fn-cfg-binding-rowp)))))

; A binding delta leaves every account where it was.
(local (defthm fn-lb-binding-delta-keeps-held-accounts
  (implies (fn-lb-account-heldp name (fn-cfg-accounts v))
           (fn-lb-account-heldp name (fn-cfg-accounts
                                      (fn-cfg-apply-delta
                                       v gen stamp
                                       (fn-lb-binding-delta other p)))))
  :hints (("Goal" :in-theory (disable fn-lb-account-heldp fn-lb-hex-text)))))

(local (defthm fn-lb-account-bind-plan-ok-shape
  (implies (equal (car (fn-lb-account-bind-plan name hex v)) :ok)
           (and (equal (cadr (fn-lb-account-bind-plan name hex v))
                       (list (fn-lb-binding-delta name (fn-lb-hex-principal hex))))
                (fn-lb-bindable-namep name)
                (fn-lb-principalp (fn-lb-hex-principal hex))
                (fn-lb-account-heldp name (fn-cfg-accounts v))))
  :hints (("Goal" :in-theory (disable fn-lb-bindable-namep fn-lb-principalp
                                      fn-lb-hex-principal fn-lb-account-heldp
                                      fn-lb-binding-delta)))))

; KEYSTONE (PRF-388, the effect).  An :ok plan's record is admitted against
; the configuration it was planned over, binds the account's login to
; exactly the principal (unbinds it for the unbind), leaves every other
; login's binding, and leaves the login holding its account.
(defthm fn-lb-account-bind-plan-binds-exactly-the-account-login
  (let ((plan (fn-lb-account-bind-plan name hex v)))
    (implies (equal (car plan) :ok)
             (and (not (fn-cfg-delta-reason v gen stamp reserved ceiling
                                            (car (cadr plan))))
                  (equal (fn-lb-binding name (fn-lb-value-bindings
                                              (fn-cfg-apply v gen stamp (cadr plan))))
                         (fn-lb-hex-principal hex))
                  (implies (not (equal other name))
                           (equal (fn-lb-binding other (fn-lb-value-bindings
                                                        (fn-cfg-apply v gen stamp
                                                                      (cadr plan))))
                                  (fn-lb-binding other (fn-lb-value-bindings v))))
                  (fn-lb-account-heldp name (fn-cfg-accounts
                                             (fn-cfg-apply v gen stamp (cadr plan)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lb-bindable-namep)
                           (fn-lb-account-bind-plan fn-lb-principalp
                            fn-lb-hex-principal fn-lb-account-heldp
                            fn-lb-binding-delta fn-lb-value-bindings
                            fn-cfg-account-loginp))
           :use ((:instance fn-lb-account-bind-plan-ok-shape)
                 (:instance fn-lb-binding-delta-is-admitted
                            (principal (fn-lb-hex-principal hex)))
                 (:instance fn-lb-binding-delta-binds-the-login
                            (principal (fn-lb-hex-principal hex)))
                 (:instance fn-lb-binding-delta-keeps-other-logins
                            (principal (fn-lb-hex-principal hex)))
                 (:instance fn-lb-binding-delta-keeps-held-accounts
                            (other name) (p (fn-lb-hex-principal hex)))))))

; KEYSTONE (PRF-388, composed).  An account binding survives the next start:
; after an :ok plan's record, the start publication (the credential file's
; table; a file that does not name the login) leaves the login bound to the
; principal the verb named.  Before PKT-560 the verb refused the login, and
; a binding written any other way was unbound at the next start.
(defthm fn-lb-an-account-binding-survives-the-next-start
  (let* ((plan (fn-lb-account-bind-plan name hex v))
         (v1 (fn-cfg-apply v gen stamp (cadr plan)))
         (pairs (fn-lb-sync-pairs file (fn-lb-value-bindings v1)
                                  (fn-cfg-accounts v1))))
    (implies (and (equal (car plan) :ok)
                  (not (fn-lb-has name file))
                  (fn-lb-pairs-okp pairs))
             (equal (fn-lb-binding name (fn-lb-value-bindings
                                         (fn-cfg-apply v1 gen2 stamp2
                                                       (fn-lb-pairs-deltas pairs))))
                    (fn-lb-hex-principal hex))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lb-config-ownsp)
                           (fn-lb-account-bind-plan fn-lb-account-heldp
                            fn-lb-hex-principal fn-lb-value-bindings
                            fn-lb-sync-pairs fn-lb-pairs-okp fn-lb-pairs-deltas
                            fn-cfg-apply
                            fn-lb-account-bind-plan-binds-exactly-the-account-login
                            fn-lb-sync-binds-file-logins-as-the-file-does-and-keeps-account-bindings))
           :use ((:instance fn-lb-account-bind-plan-binds-exactly-the-account-login
                            (reserved nil) (ceiling nil) (other nil))
                 (:instance
                  fn-lb-sync-binds-file-logins-as-the-file-does-and-keeps-account-bindings
                  (v (fn-cfg-apply v gen stamp
                                   (cadr (fn-lb-account-bind-plan name hex v))))
                  (gen gen2) (stamp stamp2))))))

(in-theory (disable fn-lb-ocfg-gate fn-lb-conn-bindings fn-lb-inflight-id
                    fn-lb-sync-plan fn-lb-value-bindings fn-lb-config-bindings
                    fn-lb-account-bind-plan fn-lb-hex-principal
                    fn-lb-account-heldp fn-lb-config-ownsp))
