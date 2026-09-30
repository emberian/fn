; fn: the configuration rows of a public reader port (PRF-161).
;
; The slot names books/public-exposure.lisp reads and the words
; books/native-admin.lisp admits for `policy set SLOT VALUE', in one small
; book so that the operator's plan does not include the owner.  Each limit
; slot is a `:set-limit' row keyed (SLOT, ""); `anonymous' is a
; `:set-policy' row.  What each means is books/public-exposure.lisp's header.
;
; This book owns the prefix `fn-exp-' with books/public-exposure.lisp
; (docs/prefixes.md).

(in-package "ACL2")
(include-book "config")
; PRF-211: the trusted range's address grammar is the listener's
; (fn-native-config-ipv4-address, fn-native-config-ipv6-literal).
(include-book "native-config")

(defconst *fn-exp-slot-connections* "exposure-connections")
(defconst *fn-exp-slot-per-address* "exposure-per-address")
(defconst *fn-exp-slot-steps* "exposure-steps-per-second")
(defconst *fn-exp-slot-idle* "exposure-idle-seconds")
(defconst *fn-exp-slot-first* "exposure-first-seconds")
(defconst *fn-exp-slot-auth-failures* "exposure-auth-failures")
(defconst *fn-exp-slot-posts* "exposure-posts-per-minute")
(defconst *fn-exp-policy-slot* "anonymous")
; PRF-211: the addresses exempt from exposure-per-address, a `:set-policy'
; row whose value is the operator's word (`policy set exposure-trusted
; CIDR[,CIDR...]', or `none').
(defconst *fn-exp-trusted-slot* "exposure-trusted")
(defconst *fn-exp-trusted-none* "none")

(defconst *fn-exp-limit-slots*
  (list *fn-exp-slot-connections* *fn-exp-slot-per-address* *fn-exp-slot-steps*
        *fn-exp-slot-idle* *fn-exp-slot-first* *fn-exp-slot-auth-failures*
        *fn-exp-slot-posts*))

; -----------------------------------------------------------------------------
; The operator's words: `policy set SLOT VALUE' (books/native-admin.lisp).

(defun fn-exp-limit-slotp (slot)
  (declare (xargs :guard t))
  (and (member-equal slot *fn-exp-limit-slots*) t))

(defun fn-exp-anonymous-wordp (word)
  (declare (xargs :guard t))
  (and (member-equal word '("none" "open")) t))


; -----------------------------------------------------------------------------
; PRF-211 (NNT-043): the connection capacity and the trusted range.
;
; THE CAPACITY IS THE ROW.  `exposure-connections' is how many connections
; the owner holds at once; a row is a `:set-limit' natural, so its width is
; the limit rows' (`fn-cfg-limit-ceiling': the CBOR uint32 maximum).  The
; owner a run installs is given one more than that width
; (`*fn-exp-owner-connection-bound*', books/native-operator.lisp
; fn-native-operator-result-run-max-connections), so fn-own-open's own
; bound never refuses a connection the row admits, and the one private
; connection the operator's live reconfiguration stages through always
; finds room (books/public-exposure.lisp fn-exp-socket-cap).  With no row,
; the capacity is 31, the figure every node ran with before (the run's
; fixed 32 less the operator's one).  A default, not a ceiling: `policy set
; exposure-connections N' takes any N the row holds, live.  The memory N
; connections cost is the operator's profile's to size (PKT-605).

(defconst *fn-exp-default-connections* 31)
(defconst *fn-exp-owner-connection-bound* (+ 1 *fn-cbor-max-uint*))

(include-book "public-exposure-selectors")

; THE TRUSTED RANGE.  A list of (FAMILY OCTETS BITS): FAMILY :inet or
; :inet6, OCTETS the network address as the listener grammar reads it, BITS
; the prefix length (at most 32 or 128; absent means the whole address).
; The host hands fn-exp-open the kernel's (FAMILY . OCTETS) for the source;
; an address is trusted when some range has its family and agrees with it
; on the first BITS bits.  The point is a node behind a home router whose
; NAT loopback makes every reader on the LAN one address (the router's):
; the operator names the LAN, and its readers stop sharing one
; per-address allowance.  The exemption is from exposure-per-address only:
; the total, the step budget and the failed-login limit still apply.

(defun fn-exp-cidr-of (text)
  ; TEXT is the octets of one range; the range, or :bad.
  (declare (xargs :guard t))
  (let* ((fields (fn-ncfg-split-on text 47))
         (addr (fn-ncfg-first fields))
         (more (fn-ncfg-rest fields))
         (v4 (fn-native-config-ipv4-address addr))
         (v6 (if (equal v4 :bad) (fn-native-config-ipv6-literal addr) :bad))
         (family (cond ((not (equal v4 :bad)) :inet)
                       ((not (equal v6 :bad)) :inet6)
                       (t nil)))
         (width (if (equal family :inet) 32 128))
         (bits (if (consp more) (fn-ncfg-decimal (fn-ncfg-first more)) width)))
    (if (and family
             (not (consp (fn-ncfg-rest more)))
             (natp bits) (<= bits width))
        (list family (if (equal family :inet) v4 v6) bits)
      :bad)))

; Executes by a loop (lane depth-debt, PRF-919): its depth was the length of
; operator data (D27: no fixed cap), one control-stack frame per element.
(defun fn-exp-cidrs-of-step (x rest)
  (declare (xargs :guard t))
  (let ((c (fn-exp-cidr-of (fn-ncfg-trim x))))
    (if (or (equal c :bad) (equal rest :bad)) :bad (cons c rest))))

(defun fn-exp-cidrs-of-loop (rev acc)
  (declare (xargs :guard t))
  (if (consp rev)
      (fn-exp-cidrs-of-loop (cdr rev) (fn-exp-cidrs-of-step (car rev) acc))
    acc))

(defun fn-exp-cidrs-of (fields)
  (declare (xargs :verify-guards nil :guard t))
  (mbe :logic
       (if (consp fields)
           (let ((c (fn-exp-cidr-of (fn-ncfg-trim (car fields))))
                 (rest (fn-exp-cidrs-of (cdr fields))))
             (if (or (equal c :bad) (equal rest :bad)) :bad (cons c rest)))
         nil)
       :exec (fn-exp-cidrs-of-loop (fn-ag-rev-onto fields nil) nil)))

(defthm fn-exp-cidrs-of-loop-of-rev-onto
  (equal (fn-exp-cidrs-of-loop (fn-ag-rev-onto fields zs) nil)
         (fn-exp-cidrs-of-loop zs (fn-exp-cidrs-of fields)))
  :hints (("Goal" :induct (fn-ag-rev-onto fields zs)
                  :in-theory (union-theories
                              '(fn-exp-cidrs-of-loop fn-exp-cidrs-of fn-exp-cidrs-of-step fn-ag-rev-onto
                                car-cons cdr-cons)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))

(verify-guards fn-exp-cidrs-of
  :hints (("Goal" :use ((:instance fn-exp-cidrs-of-loop-of-rev-onto (zs nil)))
                  :in-theory (union-theories
                              '(fn-exp-cidrs-of-loop fn-exp-cidrs-of)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))

; The operator's word, as the row holds it: `none' is no range; otherwise a
; comma-separated list of one or more ranges, every one well formed.
(defun fn-exp-trusted-of-word (word)
  (declare (xargs :guard t))
  (cond ((not (stringp word)) :bad)
        ((equal word *fn-exp-trusted-none*) nil)
        (t (fn-exp-cidrs-of (fn-ncfg-split-on (fn-record-string-octets word) 44)))))

(defun fn-exp-trusted-wordp (word)
  (declare (xargs :guard t))
  (and (fn-cfg-labelp word)
       (not (equal (fn-exp-trusted-of-word word) :bad))))

; Whether A and B agree on their first BITS bits (octet lists).
(defun fn-exp-octets-prefixp (a b bits)
  (declare (xargs :guard t :measure (acl2-count a)))
  (cond ((not (posp bits)) t)
        ((or (not (consp a)) (not (consp b))) nil)
        ((<= 8 bits)
         (and (equal (car a) (car b))
              (fn-exp-octets-prefixp (cdr a) (cdr b) (- bits 8))))
        (t (equal (floor (nfix (car a)) (expt 2 (- 8 bits)))
                  (floor (nfix (car b)) (expt 2 (- 8 bits)))))))

(defun fn-exp-cidr-matchp (cidr address)
  (declare (xargs :guard t))
  (and (consp address)
       (equal (car address) (fn-exp-at 0 cidr))
       (fn-exp-octets-prefixp (cdr address) (fn-exp-at 1 cidr)
                              (nfix (fn-exp-at 2 cidr)))))

(defun fn-exp-trusted-addressp (address trusted)
  (declare (xargs :guard t))
  (if (consp trusted)
      (or (fn-exp-cidr-matchp (car trusted) address)
          (fn-exp-trusted-addressp address (cdr trusted)))
    nil))
