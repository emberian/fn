; fn: the TLS key exchange as a policy decision (lane w-serve, 2026-10-04;
; PRF-1327).  Mini's STARTTLS client moves to the hybrid post-quantum group
; X25519MLKEM768 alone; a node that cannot offer it is unreachable by that
; client, and a node that offers only it would lock out every ordinary reader.
;
; THE POLICY, one key of the profile's `[tls]' table (books/native-config.lisp
; admits the table; the owner's configuration record does not carry it, as
; with `[web]'):
;
;   [tls]
;   key_exchange = "hybrid-preferred"   ; the default
;   key_exchange = "hybrid-required"
;
; THE OBSERVATION the host takes before ACL2 decides (host/native/tls.lisp
; fnn-tls-groups-offered-p): whether the loaded TLS library accepts the
; hybrid group list (SSL_CTX_set1_groups_list names every group it must
; know).  OpenSSL 3.5 and later does; 3.0 to 3.4 and LibreSSL do not.
;
; THE DECISION (fn-tlsk-decide POLICY OFFERED):
;   hybrid-required,  library offers the hybrid  -> (:serve HYBRID-LIST :hybrid)
;   hybrid-required,  library does not           -> (:refuse :hybrid-unavailable)
;   hybrid-preferred, library offers the hybrid  -> (:serve HYBRID-LIST :hybrid)
;   hybrid-preferred, library does not           -> (:serve CLASSICAL-LIST :classical)
; The hybrid list puts the hybrid group first and keeps the classical groups
; after it, so a reader that knows only X25519 or P-256 still connects.  A
; refusal stops `run' by name, before anything listens
; (host/native/operator-live.lisp), and only a node that holds a TLS
; certificate has a key exchange to decide.
;
; THE REPORT: each established server session is named in the service log
; with the group its key exchange used (the library's own name for it,
; reduced to a token that cannot carry a line break or a space,
; fn-tlsk-group-token), and `status' and `health' end with the running
; tallies (hybrid, classical, unknown) beside the policy.
;
; Prefix `fn-tlsk-' (docs/prefixes.md).

(in-package "ACL2")
(include-book "native-config")
(include-book "heap-figure")

(defconst *fn-tlsk-hybrid-group* "X25519MLKEM768")
(defconst *fn-tlsk-classical-list* "X25519:secp256r1:secp384r1")
(defconst *fn-tlsk-hybrid-list* "X25519MLKEM768:X25519:secp256r1:secp384r1")

; -----------------------------------------------------------------------------
; The `[tls]' table

(defun fn-tlsk-policy-of (pairs)
  ; The policy the table names, :hybrid-preferred without one, or :bad.
  (declare (xargs :guard t))
  (let ((word (fn-ncfg-string-value (fn-ncfg-value pairs "tls" "key_exchange")
                                    nil *fn-ncfg-max-text* nil)))
    (cond ((null word) :hybrid-preferred)
          ((equal word "hybrid-preferred") :hybrid-preferred)
          ((equal word "hybrid-required") :hybrid-required)
          (t :bad))))

; The plan read from the octets the operator's profile was loaded from:
; (:policy P), or (:refused REASON).
(defun fn-tlsk-config-plan (octets)
  (declare (xargs :guard t))
  (let ((pairs (if (and (fn-ncfg-ascii-octetsp octets)
                        (<= (len octets) *fn-ncfg-max-octets*))
                   (let ((lines (fn-ncfg-lines octets)))
                     (if (< *fn-ncfg-max-lines* (len lines))
                         :bad
                       (fn-ncfg-parse-lines lines nil nil nil)))
                 :bad)))
    (if (equal pairs :bad)
        (list :refused :syntax)
      (let ((policy (fn-tlsk-policy-of pairs)))
        (if (equal policy :bad)
            (list :refused :key-exchange-value)
          (list :policy policy))))))

; -----------------------------------------------------------------------------
; The decision

(defun fn-tlsk-decide (policy offered)
  (declare (xargs :guard t))
  (cond ((equal policy :hybrid-required)
         (if offered
             (list :serve *fn-tlsk-hybrid-list* :hybrid)
           (list :refuse :hybrid-unavailable)))
        ((equal policy :hybrid-preferred)
         (if offered
             (list :serve *fn-tlsk-hybrid-list* :hybrid)
           (list :serve *fn-tlsk-classical-list* :classical)))
        (t (list :refuse :policy))))

(defun fn-tlsk-servep (decision)
  (declare (xargs :guard t))
  (and (consp decision) (equal (car decision) :serve)))

; The groups the host sets on every server context, or nil on a refusal.
(defun fn-tlsk-serve-groups (decision)
  (declare (xargs :guard t))
  (and (fn-tlsk-servep decision)
       (true-listp decision) (equal (len decision) 3)
       (stringp (cadr decision))
       (cadr decision)))

(defun fn-tlsk-serve-mode (decision)
  (declare (xargs :guard t))
  (and (fn-tlsk-servep decision)
       (true-listp decision) (equal (len decision) 3)
       (caddr decision)))

(defun fn-tlsk-policy-word (policy)
  (declare (xargs :guard t))
  (if (equal policy :hybrid-required) "hybrid-required" "hybrid-preferred"))

(defun fn-tlsk-mode-word (mode)
  (declare (xargs :guard t))
  (if (equal mode :hybrid) "hybrid" "classical"))

; The start's refusal, in the node's words: `tls hybrid-required: ...'.
(defun fn-tlsk-refusal-line (decision)
  (declare (xargs :guard t))
  (fn-record-string-octets
   (if (and (consp decision) (equal (cdr decision) '(:hybrid-unavailable)))
       "tls key-exchange hybrid-required: the TLS library cannot offer X25519MLKEM768 (OpenSSL 3.5 or later; FN_OPENSSL_PREFIX names the prefix)"
     "tls key-exchange refused")))

(defthm fn-tlsk-decide-is-total
  (let ((d (fn-tlsk-decide policy offered)))
    (or (and (equal (car d) :serve) (true-listp d) (equal (len d) 3)
             (stringp (cadr d)) (member-equal (caddr d) '(:hybrid :classical)))
        (equal d (list :refuse :hybrid-unavailable))
        (equal d (list :refuse :policy))))
  :rule-classes nil)

; KEYSTONE.  hybrid-required never serves without the hybrid group: with a
; library that cannot offer it the start is refused by name; with one that
; can, the list served is the hybrid list.
(defthm fn-tlsk-required-refuses-by-name-without-the-hybrid
  (equal (fn-tlsk-decide :hybrid-required nil)
         (list :refuse :hybrid-unavailable)))

(defthm fn-tlsk-required-serves-only-the-hybrid-list
  (implies (fn-tlsk-servep (fn-tlsk-decide :hybrid-required offered))
           (and offered
                (equal (fn-tlsk-serve-groups (fn-tlsk-decide :hybrid-required offered))
                       *fn-tlsk-hybrid-list*)))
  :rule-classes nil)

; KEYSTONE.  hybrid-preferred never refuses, and serves the hybrid list
; exactly when the library offers it, the classical list otherwise.
(defthm fn-tlsk-preferred-never-refuses
  (fn-tlsk-servep (fn-tlsk-decide :hybrid-preferred offered)))

(defthm fn-tlsk-preferred-serves-the-hybrid-iff-offered
  (equal (fn-tlsk-serve-groups (fn-tlsk-decide :hybrid-preferred offered))
         (if offered *fn-tlsk-hybrid-list* *fn-tlsk-classical-list*)))

; KEYSTONE.  The hybrid group is served only when the library offers it, and
; the groups an ordinary reader needs stay in every served list: the hybrid
; list is the hybrid group first, then the classical list.
(defthm fn-tlsk-hybrid-is-served-only-when-offered
  (implies (and (fn-tlsk-servep (fn-tlsk-decide policy offered))
                (equal (fn-tlsk-serve-mode (fn-tlsk-decide policy offered)) :hybrid))
           offered)
  :rule-classes nil)

(defthm fn-tlsk-hybrid-list-is-the-hybrid-group-before-the-classical-list
  (equal *fn-tlsk-hybrid-list*
         (concatenate 'string *fn-tlsk-hybrid-group* ":" *fn-tlsk-classical-list*))
  :rule-classes nil)

; An unknown policy decides nothing it can serve.
(defthm fn-tlsk-unknown-policy-refuses
  (implies (and (not (equal policy :hybrid-required))
                (not (equal policy :hybrid-preferred)))
           (equal (fn-tlsk-decide policy offered) (list :refuse :policy))))

; -----------------------------------------------------------------------------
; The per-session group token and the log line

(defun fn-tlsk-token-char-p (c)
  (declare (xargs :guard t))
  (and (characterp c)
       (let ((n (char-code c)))
         (or (and (<= 48 n) (<= n 57))      ; 0-9
             (and (<= 65 n) (<= n 90))      ; A-Z
             (and (<= 97 n) (<= n 122))     ; a-z
             (equal n 45) (equal n 46) (equal n 95)))))

(defun fn-tlsk-token-charsp (chars)
  (declare (xargs :guard t))
  (if (consp chars)
      (and (fn-tlsk-token-char-p (car chars))
           (fn-tlsk-token-charsp (cdr chars)))
    (null chars)))

(defconst *fn-tlsk-max-token* 32)

; The group name the library reported, as a token a log line can carry:
; the name itself when it is 1 to 32 characters of [0-9A-Za-z._-], else
; `unknown' (NIL, an older library, is `unknown' too).
(defun fn-tlsk-group-token (name)
  (declare (xargs :guard t))
  (if (and (stringp name)
           (< 0 (length name))
           (<= (length name) *fn-tlsk-max-token*)
           (fn-tlsk-token-charsp (coerce name 'list)))
      name
    "unknown"))

(defthm fn-tlsk-group-token-is-a-safe-token
  (let ((token (fn-tlsk-group-token name)))
    (and (stringp token)
         (< 0 (length token))
         (<= (length token) *fn-tlsk-max-token*)
         (fn-tlsk-token-charsp (coerce token 'list)))))

(defun fn-tlsk-session-line (name)
  (declare (xargs :guard t))
  (fn-record-string-octets
   (concatenate 'string "tls established group=" (fn-tlsk-group-token name))))

; -----------------------------------------------------------------------------
; The tallies: (HYBRID CLASSICAL UNKNOWN), counts of established sessions.

(defconst *fn-tlsk-zero-tally* '(0 0 0))

(defun fn-tlsk-tally-count (tally i)
  (declare (xargs :guard (natp i)))
  (nfix (nth i (if (true-listp tally) tally nil))))

(defun fn-tlsk-tally-total (tally)
  (declare (xargs :guard t))
  (+ (fn-tlsk-tally-count tally 0) (fn-tlsk-tally-count tally 1)
     (fn-tlsk-tally-count tally 2)))

(defun fn-tlsk-tally-bump (tally name)
  (declare (xargs :guard t))
  (let ((token (fn-tlsk-group-token name))
        (h (fn-tlsk-tally-count tally 0))
        (c (fn-tlsk-tally-count tally 1))
        (u (fn-tlsk-tally-count tally 2)))
    (cond ((equal token *fn-tlsk-hybrid-group*) (list (+ 1 h) c u))
          ((equal token "unknown") (list h c (+ 1 u)))
          (t (list h (+ 1 c) u)))))

; Every established session is counted exactly once, as the hybrid exactly
; when the library said it was the hybrid group.
(defthm fn-tlsk-tally-bump-counts-one-session
  (equal (fn-tlsk-tally-total (fn-tlsk-tally-bump tally name))
         (+ 1 (fn-tlsk-tally-total tally))))

(defthm fn-tlsk-tally-bump-hybrid-only-for-the-hybrid-group
  (implies (not (equal (fn-tlsk-group-token name) *fn-tlsk-hybrid-group*))
           (equal (fn-tlsk-tally-count (fn-tlsk-tally-bump tally name) 0)
                  (fn-tlsk-tally-count tally 0))))

(defthm fn-tlsk-tally-bump-counts-the-hybrid-group
  (implies (equal (fn-tlsk-group-token name) *fn-tlsk-hybrid-group*)
           (equal (fn-tlsk-tally-count (fn-tlsk-tally-bump tally name) 0)
                  (+ 1 (fn-tlsk-tally-count tally 0)))))

; The line `status' and `health' print under the served certificate's:
;   tls key-exchange policy=P serving=M hybrid=H classical=C unknown=U
; (`serving=' is the group list the contexts were given.)
(defun fn-tlsk-kx-line (policy mode tally)
  (declare (xargs :guard t))
  (fn-record-string-octets
   (concatenate 'string
                "tls key-exchange policy=" (fn-tlsk-policy-word policy)
                " serving=" (fn-tlsk-mode-word mode)
                " hybrid=" (fn-heap-decimal (fn-tlsk-tally-count tally 0))
                " classical=" (fn-heap-decimal (fn-tlsk-tally-count tally 1))
                " unknown=" (fn-heap-decimal (fn-tlsk-tally-count tally 2)))))

; The owner's status reply line: the served certificate's line, then the key
; exchange's.  Within the reply's bound it is both; past it, the first alone.
(defun fn-tlsk-status-lines-within (served-line kx-line bound)
  (declare (xargs :guard t))
  (if (and (true-listp served-line) (true-listp kx-line) (natp bound))
      (let ((both (append served-line (list 10) kx-line)))
        (if (<= (len both) bound)
            both
          served-line))
    served-line))

(defun fn-tlsk-status-lines (served-line kx-line)
  (declare (xargs :guard t))
  (fn-tlsk-status-lines-within served-line kx-line *fn-record-max-payload*))

; `health' prints only the key exchange's line (the served certificate is
; `status''s): what follows the first line break of the owner's status reply,
; or nothing when the reply is one line (no TLS served) or not a reply.
(defun fn-tlsk-after-first-lf (octets)
  (declare (xargs :guard t))
  (cond ((atom octets) nil)
        ((equal (car octets) 10) (cdr octets))
        (t (fn-tlsk-after-first-lf (cdr octets)))))

(defun fn-tlsk-health-client-line (read)
  (declare (xargs :guard t))
  (if (and (true-listp read) (equal (len read) 3)
           (equal (car read) :accepted)
           (fn-cbor-octet-listp (caddr read)))
      (let ((rest (fn-tlsk-after-first-lf (caddr read))))
        (and (consp rest) rest))
    nil))
