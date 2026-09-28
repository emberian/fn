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
;   * the posting-account value of a login (`fn operator CONFIG account
;     hash LOGIN', `fn-ipp-account-hash'): the value an article posted under
;     LOGIN carries, for the operator who answers a complaint.

(in-package "ACL2")
(include-book "posting-account")
(include-book "article-fields")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-af-atextp)
                          (:definition fn-af-dot-atom-text-aux))))

; The octets of a text, a string's character codes or an octet list as is.
(defun fn-ipp-codes (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (consp chars)
      (cons (char-code (car chars)) (fn-ipp-codes (cdr chars)))
    nil))

(defun fn-ipp-octets (text)
  (declare (xargs :guard t))
  (if (stringp text) (fn-ipp-codes (coerce text 'list)) text))

; An <addr-spec> of two dot-atoms, local "@" domain: what the operator may
; set as the complaints address.  atext has no DQUOTE, backslash, ";", SP,
; CR or LF, so the address stands in a <quoted-string> as it is.
(defun fn-ipp-split-at (x)
  ; (local . domain) at the first "@", or nil.
  (declare (xargs :guard t))
  (if (consp x)
      (if (equal (car x) 64)
          (cons nil (cdr x))
        (let ((r (fn-ipp-split-at (cdr x))))
          (if r (cons (cons (car x) (car r)) (cdr r)) nil)))
    nil))

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

; The operator's answer for a login (`fn operator CONFIG account hash
; LOGIN', books/native-operator.lisp fn-nop-parse-account; the host reads
; the node secret and prints this value): the value an article posted under
; LOGIN carries, under the same secret.
(defun fn-ipp-account-hash (secret login)
  (declare (xargs :guard t))
  (fn-pa-account-value secret (fn-ipp-octets login)))

;; Withdrawn from includers (lane rule-hygiene, tools/rule_cost.py).
;; Each is tried in includers' proofs and pays for its frames in
;; almost none (planning/evidence/rule-cost-*.json has the counts;
;; docs/proof-style.md section 8).  An includer that needs one
;; enables it where it is used.
(in-theory (disable (:definition fn-ipp-addr-specp)
                    (:definition fn-ipp-split-at)
                    (:rewrite fn-ipp-addr-spec-has-no-quote-or-line-break)))
