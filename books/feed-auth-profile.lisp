; Bounded physical outbound AUTHINFO profile codec.  The host reads bytes;
; ACL2 alone recognizes `FNAUTH1\n<user>\n<password>\n'.
(in-package "ACL2")
(include-book "nntp-syntax")

(defconst *fn-fap-max-octets* 1024)
(defconst *fn-fap-magic* '(70 78 65 85 84 72 49 10))
; AUTHINFO USER/PASS share the 14-octet prefix and CRLF.  The command passed
; to fn-wire-outbound-command-line must fit its 510-octet bound including both.
(defconst *fn-fap-max-token-octets* 494)

(defun fn-fap-prefixp (prefix xs)
  (declare (xargs :guard t))
  (if (consp prefix)
      (and (consp xs) (equal (car prefix) (car xs))
           (fn-fap-prefixp (cdr prefix) (cdr xs))) t))
(defun fn-fap-drop (n xs)
  (declare (xargs :guard t))
  (if (and (posp n) (consp xs)) (fn-fap-drop (1- n) (cdr xs)) xs))
(defun fn-fap-reverse-aux (xs out)
  (declare (xargs :guard t))
  (if (consp xs) (fn-fap-reverse-aux (cdr xs) (cons (car xs) out)) out))
(defun fn-fap-reverse (xs)
  (declare (xargs :guard t))
  (fn-fap-reverse-aux xs nil))
(defun fn-fap-line-aux (xs rev)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (equal (car xs) 10) (list :ok (fn-fap-reverse rev) (cdr xs))
        (fn-fap-line-aux (cdr xs) (cons (car xs) rev)))
    (list :bad nil nil)))
(defun fn-fap-line (xs) (declare (xargs :guard t)) (fn-fap-line-aux xs nil))
(defun fn-fap-tokenp (xs)
  (declare (xargs :guard t))
  (and (consp xs) (<= (len xs) *fn-fap-max-token-octets*)
       (fn-nntp-printable-tokenp xs)))
(defun fn-fap-decode (octets)
  (declare (xargs :guard t))
  (if (and (fn-wire-octet-listp octets)
           (<= (len octets) *fn-fap-max-octets*)
           (fn-fap-prefixp *fn-fap-magic* octets))
      (let* ((u (fn-fap-line (fn-fap-drop (len *fn-fap-magic*) octets)))
             (p (fn-fap-line (caddr u))))
        (if (and (equal (car u) :ok) (equal (car p) :ok)
                 (null (caddr p)) (fn-fap-tokenp (cadr u))
                 (fn-fap-tokenp (cadr p)))
            (list :ok (cadr u) (cadr p))
          (list :bad nil nil)))
    (list :bad nil nil)))

;
; What an accepted profile hands the connection machine.  `fn-fap-decode'
; itself checks `fn-fap-tokenp' of both fields; what it does not say on its
; face is that both are true lists, which `fn-fc-auth-command' requires
; before it renders anything (books/feed-connection).  Together they are
; the hypotheses of `fn-fc-decoded-profile-renders-verbatim-in-every-state'
; in books/feed-connection-invariants.  The subject is the function the host
; calls: host/owner-host.lisp `fn-owner-feed-profile-decode' is
; `fn-fap-decode', and host/native/feed-service.lisp `fnn-feed-auth-profile'
; calls it on the bytes of the owner-only profile file.
(local
 (defthm fn-fap-reverse-aux-is-true-list
   (implies (true-listp out) (true-listp (fn-fap-reverse-aux xs out)))))

(local
 (defthm fn-fap-line-aux-yields-a-true-list
   (implies (true-listp rev)
            (true-listp (cadr (fn-fap-line-aux xs rev))))
   :hints (("Goal" :in-theory (enable fn-fap-line-aux fn-fap-reverse)))))

(defthm fn-fap-decode-yields-two-renderable-tokens
  (implies (equal (car (fn-fap-decode octets)) :ok)
           (and (fn-fap-tokenp (cadr (fn-fap-decode octets)))
                (true-listp (cadr (fn-fap-decode octets)))
                (fn-fap-tokenp (caddr (fn-fap-decode octets)))
                (true-listp (caddr (fn-fap-decode octets)))))
  :hints (("Goal" :in-theory (e/d (fn-fap-decode fn-fap-line)
                                  (fn-fap-tokenp fn-fap-line-aux)))))

; And a profile it refuses yields no name and no secret at all.
(defthm fn-fap-decode-refusal-yields-no-credential
  (implies (not (equal (car (fn-fap-decode octets)) :ok))
           (and (equal (cadr (fn-fap-decode octets)) nil)
                (equal (caddr (fn-fap-decode octets)) nil)))
  :hints (("Goal" :in-theory (e/d (fn-fap-decode) (fn-fap-tokenp fn-fap-line)))))

(verify-guards fn-fap-prefixp)
(verify-guards fn-fap-drop)
(verify-guards fn-fap-reverse-aux)
(verify-guards fn-fap-reverse)
(verify-guards fn-fap-line-aux)
(verify-guards fn-fap-line)
(verify-guards fn-fap-tokenp)
(verify-guards fn-fap-decode)
