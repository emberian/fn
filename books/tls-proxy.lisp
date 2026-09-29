; fn: the PROXY protocol header, read only on an explicitly trusted path
; (lane tls-handshake-budget-3, 2026-09-29; row W2a item 4; PRF-986).
;
; A TCP proxy in front of the implicit-TLS listener hides every client
; behind the proxy's address: one source, one handshake budget.  The PROXY
; protocol (HAProxy's specification, versions 1 and 2) lets such a proxy
; state the original source in a header before the client's first octet.
; A header is only an assertion by whoever sent it, so fn reads one ONLY
; from a transport peer inside the operator's `tls-proxy-trusted-peers'
; ranges (books/tls-handshake-source.lisp fn-pxy-trusted-peer), and never
; guesses that a public client's octets are a header.  A peer inside the
; ranges MUST send one (the specification: a receiver configured for the
; protocol refuses a connection without it).
;
; What the node then knows, three facts kept apart (THE PATH):
;   the transport peer (the kernel's address: the proxy),
;   the asserted original source (the header's, or the transport peer's for
;     LOCAL / UNKNOWN: a health check from the proxy itself), and
;   why the assertion is believed (the operator's range the peer is in).
;
; THE BOUND: the header is read in pieces this book sizes (fn-pxy-step), so
; the host never reads past it into the client's TLS octets and never reads
; more than *fn-pxy-max* octets for it: a version-1 line at most 107 octets
; (the specification's maximum), a version-2 header 16 octets plus at most
; *fn-pxy-v2-max-body* (a stated bound: the largest address block is 216,
; the rest TLVs, which are skipped).  The read runs under the handshake's
; slot and deadline (`tls-handshake-ms'): the host asks
; fn-owner-handshake-admit for the PROXY peer before it reads anything.
;
; THE CHARGE: the proxy's own source is charged when its connection is
; admitted (the slot, its bucket); once the header names the original
; source, the slot is handed over (fn-pxy-handover: the proxy's handshake
; done, the original source's admitted), so the original source pays its own
; per-source budget too, and the node-wide bounds (at most L in flight, at
; most L started a second) hold over both: fn-pxy-handover is two events of
; books/tls-handshake-budget.lisp's event language, and every bound proved
; there over any event sequence covers it.

(in-package "ACL2")
(include-book "tls-handshake-budget")

(defconst *fn-pxy-v1-max* 107)
(defconst *fn-pxy-v2-max-body* 512)
(defconst *fn-pxy-max* (+ 16 *fn-pxy-v2-max-body*))

; "PROXY " and the version-2 signature (\r\n\r\n\0\r\nQUIT\n).
(defconst *fn-pxy-v1-prefix* '(80 82 79 88 89 32))
(defconst *fn-pxy-v2-signature* '(13 10 13 10 0 13 10 81 85 73 84 10))

(defun fn-pxy-octetp (x)
  (declare (xargs :guard t))
  (and (natp x) (< x 256)))

(defun fn-pxy-at (i xs)
  (declare (xargs :guard (natp i)))
  (let ((x (nth i (true-list-fix xs)))) (if (fn-pxy-octetp x) x 0)))

(defun fn-pxy-octetsp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-pxy-octetp (car xs)) (fn-pxy-octetsp (cdr xs)))
    (null xs)))

(defthm fn-pxy-octetsp-true-listp
  (implies (fn-pxy-octetsp xs) (true-listp xs))
  :rule-classes :forward-chaining)

; A port: decimal, at most 65535.
(defun fn-pxy-portp (xs)
  (declare (xargs :guard t))
  (let ((n (fn-ncfg-decimal xs)))
    (and (natp n) (<= n 65535))))

(defun fn-pxy-field (i fields)
  (declare (xargs :guard (natp i)))
  (if (zp i) (fn-ncfg-first fields) (fn-pxy-field (1- i) (fn-ncfg-rest fields))))

; The version-1 line's fields after "PROXY " and before CRLF: the source,
; or :local (UNKNOWN), or :bad.
(defun fn-pxy-v1-source (fields)
  (declare (xargs :guard t))
  (let ((proto (fn-ncfg-first fields)))
    (cond ((equal proto '(85 78 75 78 79 87 78)) :local) ; UNKNOWN
          ((not (equal (len fields) 5)) :bad)
          ((not (and (fn-pxy-portp (fn-pxy-field 3 fields))
                     (fn-pxy-portp (fn-pxy-field 4 fields)))) :bad)
          ((equal proto '(84 67 80 52)) ; TCP4
           (let ((src (fn-native-config-ipv4-address (fn-pxy-field 1 fields)))
                 (dst (fn-native-config-ipv4-address (fn-pxy-field 2 fields))))
             (if (or (equal src :bad) (equal dst :bad)) :bad (cons :inet src))))
          ((equal proto '(84 67 80 54)) ; TCP6
           (let ((src (fn-ncfg-ipv6-unbracketed (fn-pxy-field 1 fields)))
                 (dst (fn-ncfg-ipv6-unbracketed (fn-pxy-field 2 fields))))
             (if (or (equal src :bad) (equal dst :bad)) :bad (cons :inet6 src))))
          (t :bad))))

; The version-1 line complete (it ends CR LF): its source, or :bad.
(defun fn-pxy-v1-line (octets)
  (declare (xargs :guard t))
  (let* ((body (nthcdr 6 (true-list-fix octets)))
         (n (len body)))
    (if (and (<= 2 n)
             (equal (nth (- n 2) body) 13)
             (equal (nth (- n 1) body) 10))
        (fn-pxy-v1-source (fn-ncfg-split-on (take (- n 2) body) 32))
      :bad)))

(defun fn-pxy-v2-body-length (octets)
  (declare (xargs :guard t))
  (+ (* 256 (fn-pxy-at 14 octets)) (fn-pxy-at 15 octets)))

; The version-2 header complete (16 + its length): its source, :local,
; :unsupported (not TCP over IPv4 or IPv6), or :bad.
(defun fn-pxy-v2-header (octets)
  (declare (xargs :guard t))
  (let* ((vc (fn-pxy-at 12 octets))
         (fam (fn-pxy-at 13 octets))
         (body (fn-pxy-v2-body-length octets))
         (addr (nthcdr 16 (true-list-fix octets))))
    (cond ((not (equal (floor vc 16) 2)) :bad)
          ((equal (mod vc 16) 0) :local)
          ((not (equal (mod vc 16) 1)) :bad)
          ((and (equal fam #x11) (<= 12 body)) (cons :inet (take 4 addr)))
          ((and (equal fam #x21) (<= 36 body)) (cons :inet6 (take 16 addr)))
          ((member fam '(#x11 #x21)) :bad)
          (t :unsupported))))

; THE STEP THE HOST CALLS (host/owner-host.lisp fn-owner-proxy-step) with
; OCTETS, everything read for the header so far.  The answer:
;   (:more K)          read at most K more octets, then ask again;
;   (:header N SOURCE) the header is the N octets read (N = their count),
;                      SOURCE the asserted source or :local;
;   (:refuse REASON)   :proxy-malformed, :proxy-oversize or :proxy-unsupported.
(defun fn-pxy-step (octets)
  (declare (xargs :guard t))
  (let ((n (len octets)))
    (cond ((not (fn-pxy-octetsp octets)) (list :refuse :proxy-malformed))
          ((< n 6) (list :more (- 6 n)))
          ((equal (take 6 octets) *fn-pxy-v1-prefix*)
           (cond ((< *fn-pxy-v1-max* n) (list :refuse :proxy-oversize))
                 ((and (equal (nth (- n 1) octets) 10) (< 6 n))
                  (let ((src (fn-pxy-v1-line octets)))
                    (if (equal src :bad)
                        (list :refuse :proxy-malformed)
                      (list :header n src))))
                 ((member 10 octets) (list :refuse :proxy-malformed))
                 ((equal *fn-pxy-v1-max* n) (list :refuse :proxy-oversize))
                 (t (list :more 1))))
          ((equal (take 6 octets) (take 6 *fn-pxy-v2-signature*))
           (cond ((< n 16) (list :more (- 16 n)))
                 ((not (equal (take 12 octets) *fn-pxy-v2-signature*))
                  (list :refuse :proxy-malformed))
                 ((< *fn-pxy-v2-max-body* (fn-pxy-v2-body-length octets))
                  (list :refuse :proxy-oversize))
                 ((< n (+ 16 (fn-pxy-v2-body-length octets)))
                  (list :more (- (+ 16 (fn-pxy-v2-body-length octets)) n)))
                 ((< (+ 16 (fn-pxy-v2-body-length octets)) n)
                  (list :refuse :proxy-malformed))
                 (t (let ((src (fn-pxy-v2-header octets)))
                      (cond ((equal src :bad) (list :refuse :proxy-malformed))
                            ((equal src :unsupported) (list :refuse :proxy-unsupported))
                            (t (list :header n src)))))))
          (t (list :refuse :proxy-malformed)))))

; THE PATH THE HOST ASKS FIRST (fn-owner-proxy-begin), for the transport peer
; ADDRESS: (:direct) -- not a trusted proxy, nothing is read for a header and
; ADDRESS is the source -- or (:read K WHY): read a header, K octets first,
; WHY the operator's range the peer is in.
(defun fn-pxy-begin (address peers)
  (declare (xargs :guard t))
  (let ((why (fn-pxy-trusted-peer address peers)))
    (if why (list :read 6 why) (list :direct))))

; The asserted source a complete header yields: its SOURCE, or the transport
; peer's for :local.
(defun fn-pxy-asserted (transport source)
  (declare (xargs :guard t))
  (if (equal source :local) transport source))

; THE HANDOVER THE HOST CALLS (fn-owner-proxy-handover) once the header named
; ASSERTED: the proxy's handshake ID is done, and ASSERTED's handshake is
; decided (fn-hsb-admit, not queued): :admit NEW-ID, :wait or :refuse.
(defun fn-pxy-handover (s hl id trustedp asserted now)
  (declare (xargs :guard t))
  (fn-hsb-admit (fn-hsb-done s id) hl trustedp asserted now nil))

(defconst *fn-pxy-reasons*
  '((:proxy-malformed . "proxy-malformed") (:proxy-oversize . "proxy-oversize")
    (:proxy-unsupported . "proxy-unsupported") (:proxy-timeout . "proxy-timeout")))

; The service log's line for a refused header: the transport peer (the
; proxy), and no asserted source (none was believed).
(defun fn-pxy-refusal-line (reason transport)
  (declare (xargs :guard t))
  (let ((word (cdr (assoc-equal reason *fn-pxy-reasons*))))
    (concatenate 'string "tls refused reason=" (if (stringp word) word "other")
                 " proxy=" (fn-hsb-source-text (fn-hsb-normal-address transport)))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-pxy-direct-unless-trusted: a transport peer in none of the
; operator's ranges is never read for a header: the path is (:direct),
; whatever it sends.  A peer that is in one is read, and WHY is a listed
; range that matches it.
(defthm fn-pxy-direct-unless-trusted
  (let ((p (fn-pxy-begin address peers)))
    (and (iff (equal p (list :direct)) (not (fn-pxy-trusted-peer address peers)))
         (implies (equal (car p) :read)
                  (and (member-equal (caddr p) peers)
                       (fn-exp-cidr-matchp (caddr p) (fn-hsb-normal-address address))))))
  :hints (("Goal" :in-theory (disable fn-exp-cidr-matchp)
                  :use fn-pxy-trusted-peer-is-a-listed-match)))

; KEYSTONE fn-pxy-step-reads-within-the-bound: whatever has been read, a
; request for more asks for at least one octet and never past *fn-pxy-max*
; (528) in all; a header is exactly the octets read, at most *fn-pxy-max*.
(defthm fn-pxy-step-reads-within-the-bound
  (let ((r (fn-pxy-step octets)))
    (and (implies (equal (car r) :more)
                  (and (posp (cadr r))
                       (<= (+ (len octets) (cadr r)) *fn-pxy-max*)))
         (implies (equal (car r) :header)
                  (and (equal (cadr r) (len octets))
                       (<= (len octets) *fn-pxy-max*)))
         (member-equal (car r) '(:more :header :refuse))))
  :hints (("Goal" :in-theory (disable fn-pxy-v1-line fn-pxy-v2-header fn-pxy-octetsp
                                      take member-equal))))

; KEYSTONE fn-pxy-handover-keeps-the-bound: the handover keeps
; books/tls-handshake-decision.lisp's bound (at most L in flight, at most L
; started in the tick, at most 32 L waiting), because it is two events of
; the event language: the proxy's handshake done, the asserted source's
; admitted -- so every bound over any event sequence covers a proxied
; connection, both charges included.
(defthm fn-pxy-handover-is-two-events-by-definition
  (equal (fn-hsb-state (fn-pxy-handover s hl id trustedp asserted now))
         (fn-hsb-run s (list (list :done id)
                             (list :admit hl trustedp asserted now nil))))
  :hints (("Goal" :in-theory (enable fn-hsb-event fn-hsb-run))))

(defthm fn-pxy-handover-keeps-the-bound
  (implies (fn-hsb-okp s hl)
           (fn-hsb-okp (fn-hsb-state (fn-pxy-handover s hl id trustedp asserted now)) hl))
  :hints (("Goal" :in-theory (disable fn-hsb-okp fn-hsb-admit fn-hsb-done)
                  :use ((:instance fn-hsb-done-keeps-the-bound)
                        (:instance fn-hsb-admit-keeps-the-bound
                                   (s (fn-hsb-done s id)) (address asserted)
                                   (queuedp nil))))))
