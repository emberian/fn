; fn: a TLS handshake's source, and the operator's per-source overrides
; (lane tls-handshake-budget-3, 2026-09-29; row W2a; PRF-986).
;
; Split out of books/tls-handshake-decision.lisp so that the administrative
; plan (books/native-admin.lisp, `policy set tls-handshake-source-overrides
; WORD') admits the override list with the parse the owner reads, without
; the decision's closure (connection-budget and what it includes).
;
; It also holds the trusted PROXY peers' row (`tls-proxy-trusted-peers',
; books/tls-proxy.lisp), for the same reason.
;
; THE SOURCE is the peer's address as the listener sees it: an IPv4 address,
; or an IPv6 address's /64; an IPv4-mapped IPv6 address is its IPv4 address.

(in-package "ACL2")
(include-book "native-config")  ; fn-ncfg-*, the address parsers
(include-book "node-config")    ; fn-cfg-policy
(include-book "profile-limits") ; fn-profile-limit
(include-book "records-shape")  ; fn-record-string-octets
(include-book "public-exposure-rows") ; the CIDR list (fn-exp-trusted-of-word)

; An IPv4-mapped IPv6 address (::ffff:a.b.c.d, RFC 4291 section 2.5.5.2:
; what a dual-stack listener reports for an IPv4 peer) is that IPv4 address:
; one source, one budget, whichever way the kernel reports it.
(defconst *fn-hsb-v4-mapped-prefix* '(0 0 0 0 0 0 0 0 0 0 255 255))

(defun fn-hsb-normal-address (address)
  (declare (xargs :guard t))
  (if (and (consp address)
           (equal (car address) :inet6)
           (true-listp (cdr address))
           (equal (len (cdr address)) 16)
           (equal (take 12 (cdr address)) *fn-hsb-v4-mapped-prefix*))
      (cons :inet (nthcdr 12 (cdr address)))
    address))

; The source: an IPv6 address's /64, any other address itself (after the
; mapped form is normalized).
(defun fn-hsb-source-key (address)
  (declare (xargs :guard t))
  (let ((address (fn-hsb-normal-address address)))
    (if (and (consp address)
             (equal (car address) :inet6)
             (true-listp (cdr address))
             (<= 8 (len (cdr address))))
        (cons :inet6 (take 8 (cdr address)))
      address)))

; One source, one budget: the mapped form of an IPv4 address is its key.
(defthm fn-hsb-mapped-address-is-one-source
  (equal (fn-hsb-source-key (cons :inet6 (append *fn-hsb-v4-mapped-prefix* (list a b c d))))
         (fn-hsb-source-key (list :inet a b c d))))

;; THE OVERRIDE LIST, as the operator writes it: the policy row
;; `tls-handshake-source-overrides' holds `none' or a comma-separated list of
;; ADDRESS=N or ADDRESS/64=N (an IPv4 address, an IPv6 address standing for
;; its /64), N a positive handshakes-per-minute.  At most the profile's
;; `tls-handshake-source-overrides' entries (MOST); one more is refused by
;; name, :overrides-full; a word that does not parse, :override-address.
(defconst *fn-hsb-overrides-slot* "tls-handshake-source-overrides")

(defun fn-hsb-override-entry (text)
  ; TEXT is the octets of one entry; (KEY . N), or :bad.
  (declare (xargs :guard t))
  (let* ((sides (fn-ncfg-split-on text 61))
         (n (fn-ncfg-decimal (fn-ncfg-trim (fn-ncfg-first (fn-ncfg-rest sides)))))
         (parts (fn-ncfg-split-on (fn-ncfg-trim (fn-ncfg-first sides)) 47))
         (addr (fn-ncfg-first parts))
         (width (fn-ncfg-rest parts))
         (v4 (fn-native-config-ipv4-address addr))
         (v6 (if (equal v4 :bad) (fn-native-config-ipv6-literal addr) :bad)))
    (cond ((or (not (posp n)) (consp (fn-ncfg-rest (fn-ncfg-rest sides)))) :bad)
          ((and (not (equal v4 :bad)) (not (consp width)))
           (cons (fn-hsb-source-key (cons :inet v4)) n))
          ((and (not (equal v6 :bad)) (true-listp v6) (equal (len v6) 16)
                (or (not (consp width))
                    (and (equal (fn-ncfg-decimal (fn-ncfg-first width)) 64)
                         (not (consp (fn-ncfg-rest width))))))
           (cons (fn-hsb-source-key (cons :inet6 v6)) n))
          (t :bad))))

(defun fn-hsb-override-entries (fields)
  (declare (xargs :guard t))
  (if (consp fields)
      (let ((e (fn-hsb-override-entry (fn-ncfg-trim (car fields))))
            (rest (fn-hsb-override-entries (cdr fields))))
        (if (or (equal e :bad) (equal rest :bad)) :bad (cons e rest)))
    nil))

;; The row's word -> the list, or the refusal's name.
(defun fn-hsb-overrides-of-word (word most)
  (declare (xargs :guard t))
  (cond ((not (stringp word)) :override-address)
        ((equal word "none") nil)
        (t (let ((es (fn-hsb-override-entries
                      (fn-ncfg-split-on (fn-record-string-octets word) 44))))
             (cond ((equal es :bad) :override-address)
                   ((< (nfix most) (len es)) :overrides-full)
                   (t es))))))

;; The live configuration's list (the host's read: fn-owner-handshake-limits).
;; An absent row, `none', or a row that does not parse (no plan writes one:
;; the admission refuses it by name) lists nothing.
(defun fn-hsb-config-overrides (v)
  (declare (xargs :guard t))
  (let* ((word (fn-cfg-policy v *fn-hsb-overrides-slot*))
         (r (if (equal word "") nil
              (fn-hsb-overrides-of-word word (fn-profile-limit :tls-handshake-source-overrides)))))
    (if (symbolp r) nil r)))

(defthm fn-hsb-override-entries-shape
  (implies (not (equal (fn-hsb-override-entries fields) :bad))
           (and (true-listp (fn-hsb-override-entries fields))
                (alistp (fn-hsb-override-entries fields)))))

;; The list is finite by construction: every list the row admits holds at
;; most MOST entries, each a positive rate for a source key.
(defthm fn-hsb-overrides-of-word-is-bounded
  (let ((r (fn-hsb-overrides-of-word word most)))
    (implies (not (member-equal r '(:override-address :overrides-full)))
             (and (true-listp r) (<= (len r) (nfix most)))))
  :hints (("Goal" :in-theory (disable fn-hsb-override-entries))))

;; THE TRUSTED PROXY PEERS (books/tls-proxy.lisp): the policy row
;; `tls-proxy-trusted-peers' holds `none' or a comma-separated CIDR list, the
;; syntax of `exposure-trusted' (fn-exp-trusted-of-word).  Only a transport
;; peer inside one of these ranges is read for a PROXY header; nothing else
;; ever is.  An absent row, `none', or a row that does not parse lists
;; nothing.
(defconst *fn-pxy-peers-slot* "tls-proxy-trusted-peers")

(defun fn-pxy-config-peers (v)
  (declare (xargs :guard t))
  (let* ((word (fn-cfg-policy v *fn-pxy-peers-slot*))
         (r (if (equal word "") nil (fn-exp-trusted-of-word word))))
    (if (equal r :bad) nil r)))

;; The range of PEERS the transport peer ADDRESS is in (why it is trusted),
;; or nil.  An IPv4-mapped IPv6 peer is its IPv4 address.
(defun fn-pxy-trusted-peer (address peers)
  (declare (xargs :guard t))
  (if (consp peers)
      (if (fn-exp-cidr-matchp (car peers) (fn-hsb-normal-address address))
          (car peers)
        (fn-pxy-trusted-peer address (cdr peers)))
    nil))

(defthm fn-pxy-trusted-peer-is-a-listed-match
  (let ((c (fn-pxy-trusted-peer address peers)))
    (implies c
             (and (member-equal c peers)
                  (fn-exp-cidr-matchp c (fn-hsb-normal-address address)))))
  :hints (("Goal" :in-theory (disable fn-exp-cidr-matchp fn-hsb-normal-address))))
