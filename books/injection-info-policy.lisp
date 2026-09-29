; fn: the operator-facing half of the Injection-Info parameters (PKT-597;
; prefix `fn-ipp-', shared with books/injection-info-params.lisp).
;
; Two things an operator touches, kept in a small book so the admin planner
; (books/native-admin.lisp) and the operator host (host/native-operator-
; host.lisp) include it without the injection walk:
;   * the complaints address: `fn operator CONFIG policy set complaints-to
;     ADDR' is admitted exactly when ADDR is an <addr-spec> of two
;     dot-atoms (`fn-ipp-addr-specp'), a durable `:set-policy' row like
;     path-identity (no delta code of its own);
;   * the posting-account value of an account (`fn-ipp-account-hash'; `fn
;     operator CONFIG account hash LOGIN' resolves LOGIN to its account,
;     books/native-operator.lisp fn-nop-account-hash): the value an article
;     posted under that account carries, for the operator who answers a
;     complaint.

(in-package "ACL2")
(include-book "posting-account")
(include-book "article-fields")

; The octets of a text, a string's character codes or an octet list as is.
; Executes by a loop (lane depth-debt, PRF-919): its depth was the length of
; operator data (D27: no fixed cap), one control-stack frame per element.
(defun fn-ipp-codes-loop (chars acc)
  (declare (xargs :guard (character-listp chars)))
  (if (consp chars)
      (fn-ipp-codes-loop (cdr chars) (cons (char-code (car chars)) acc))
    (fn-ag-rev-onto acc nil)))

(defun fn-ipp-codes (chars)
  (declare (xargs :guard (character-listp chars) :verify-guards nil))
  (mbe :logic (if (consp chars)
                  (cons (char-code (car chars)) (fn-ipp-codes (cdr chars)))
                nil)
       :exec (fn-ipp-codes-loop chars nil)))

(defthm fn-ipp-codes-loop-is-rev-onto
  (equal (fn-ipp-codes-loop chars acc)
         (fn-ag-rev-onto acc (fn-ipp-codes chars)))
  :hints (("Goal" :induct (fn-ipp-codes-loop chars acc)
                  :in-theory (union-theories
                              '(fn-ipp-codes-loop fn-ipp-codes fn-ag-rev-onto
                                car-cons cdr-cons)
                              (theory 'minimal-theory)))))

(verify-guards fn-ipp-codes
  :hints (("Goal" :in-theory (union-theories
                              '(fn-ipp-codes fn-ag-rev-onto fn-ipp-codes-loop-is-rev-onto
                                character-listp)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))

(defun fn-ipp-octets (text)
  (declare (xargs :guard t))
  (if (stringp text) (fn-ipp-codes (coerce text 'list)) text))

; An <addr-spec> of two dot-atoms, local "@" domain: what the operator may
; set as the complaints address.  atext has no DQUOTE, backslash, ";", SP,
; CR or LF, so the address stands in a <quoted-string> as it is.
; Executes by a loop (lane depth-debt, PRF-919): its depth was the length of
; operator data (D27: no fixed cap), one control-stack frame per element.
; The loop carries the octets before the "@" reversed.
(defun fn-ipp-split-at-loop (x acc)
  (declare (xargs :guard t))
  (if (consp x)
      (if (equal (car x) 64)
          (cons (fn-ag-rev-onto acc nil) (cdr x))
        (fn-ipp-split-at-loop (cdr x) (cons (car x) acc)))
    nil))

(defun fn-ipp-split-at (x)
  ; (local . domain) at the first "@", or nil.
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (if (consp x)
                  (if (equal (car x) 64)
                      (cons nil (cdr x))
                    (let ((r (fn-ipp-split-at (cdr x))))
                      (if r (cons (cons (car x) (car r)) (cdr r)) nil)))
                nil)
       :exec (fn-ipp-split-at-loop x nil)))

(defthm fn-ipp-split-at-loop-is-rev-onto
  (equal (fn-ipp-split-at-loop x acc)
         (let ((r (fn-ipp-split-at x)))
           (if r (cons (fn-ag-rev-onto acc (car r)) (cdr r)) nil)))
  :hints (("Goal" :induct (fn-ipp-split-at-loop x acc)
                  :in-theory (union-theories
                              '(fn-ipp-split-at-loop fn-ipp-split-at fn-ag-rev-onto
                                car-cons cdr-cons)
                              (theory 'minimal-theory)))))

(verify-guards fn-ipp-split-at
  :hints (("Goal" :in-theory (union-theories
                              '(fn-ipp-split-at fn-ag-rev-onto fn-ipp-split-at-loop-is-rev-onto
                                car-cons cdr-cons)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))

(defun fn-ipp-addr-specp (x)
  (declare (xargs :guard t))
  (let ((r (fn-ipp-split-at x)))
    (and r
         (fn-af-dot-atom-textp (car r))
         (fn-af-dot-atom-textp (cdr r)))))

; The policy slot of the complaints address (`fn operator CONFIG policy set
; complaints-to ADDR', books/native-admin.lisp: a `:set-policy' row like
; path-identity; no delta code of its own).
(defconst *fn-ipp-complaints-slot* "complaints-to")

(local
 (defthm fn-ipp-split-member
   (implies (fn-ipp-split-at x)
            (iff (member-equal a x)
                 (or (equal a 64)
                     (member-equal a (car (fn-ipp-split-at x)))
                     (member-equal a (cdr (fn-ipp-split-at x))))))
   :hints (("Goal" :induct (fn-ipp-split-at x)))))

(local
 (defthm fn-ipp-dot-atom-excludes
   (implies (fn-af-dot-atom-text-aux b w)
            (and (not (member-equal 34 b)) (not (member-equal 92 b))
                 (not (member-equal 13 b)) (not (member-equal 10 b))
                 (not (member-equal 59 b))))
   :hints (("Goal" :induct (fn-af-dot-atom-text-aux b w)
            :in-theory (enable fn-af-dot-atom-text-aux fn-af-atextp)))))

; The address stands in the header's quoted-string as it is, and on one
; line: no DQUOTE, backslash, ";", CR or LF.
(defthm fn-ipp-addr-spec-has-no-quote-or-line-break
  (implies (fn-ipp-addr-specp x)
           (and (not (member-equal 34 x)) (not (member-equal 92 x))
                (not (member-equal 13 x)) (not (member-equal 10 x))
                (not (member-equal 59 x))))
  :hints (("Goal" :in-theory (e/d (fn-af-dot-atom-textp) (fn-ipp-split-at))
           :use ((:instance fn-ipp-dot-atom-excludes
                            (b (car (fn-ipp-split-at x))) (w t))
                 (:instance fn-ipp-dot-atom-excludes
                            (b (cdr (fn-ipp-split-at x))) (w t))))))

; A login as the operator types it: printable ASCII, no space (an
; AUTHINFO USER argument is one such token, RFC 4643 section 2.3.2), so its
; octets are its character codes.
(defun fn-ipp-login-octetsp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (integerp (car x)) (<= 33 (car x)) (<= (car x) 126)
           (fn-ipp-login-octetsp (cdr x)))
    (null x)))

(defun fn-ipp-login-wordp (w)
  (declare (xargs :guard t))
  (and (stringp w) (consp (fn-ipp-octets w))
       (fn-ipp-login-octetsp (fn-ipp-octets w))))

; The posting-account value of an ACCOUNT (the principal a session
; authenticated as, books/served.lisp fn-served-account; PKT-786): the value
; an article posted under that account carries, under the same secret
; (books/injection-info-params.lisp fn-ipp-injected-octets).  The operator's
; `fn operator CONFIG account hash LOGIN' resolves LOGIN to its account
; first (books/native-operator.lisp fn-nop-account-hash).
(defun fn-ipp-account-hash (secret account)
  (declare (xargs :guard t))
  (fn-pa-account-value secret (fn-ipp-octets account)))

;; Withdrawn from includers (lane rule-hygiene, tools/rule_cost.py).
;; Each is tried in includers' proofs and pays for its frames in
;; almost none (planning/evidence/rule-cost-*.json has the counts;
;; docs/proof-style.md section 8).  An includer that needs one
;; enables it where it is used.
(in-theory (disable (:definition fn-ipp-addr-specp)
                    (:definition fn-ipp-split-at)
                    (:rewrite fn-ipp-addr-spec-has-no-quote-or-line-break)))
