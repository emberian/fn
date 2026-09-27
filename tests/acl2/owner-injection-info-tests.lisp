; Teeth for books/owner-injection-info.lisp (PKT-597 with SEC-006): the D25
; subject of the octets the owner stores is the poster's source, with the
; node's Cancel-Lock in front and the Injection-Info parameters in the block.
(in-package "ACL2")
(include-book "../../books/owner-injection-info")
(include-book "must-fail-checked")

(defun oiit-codes (cs)
  (declare (xargs :guard (character-listp cs)))
  (if (consp cs) (cons (char-code (car cs)) (oiit-codes (cdr cs))) nil))
(defmacro oiit-o (s) `(oiit-codes (coerce ,s 'list)))
(defun oiit-crlf (x)
  (declare (xargs :guard t))
  (if (consp x)
      (if (equal (car x) 10) (list* 13 10 (oiit-crlf (cdr x))) (cons (car x) (oiit-crlf (cdr x))))
    nil))

(defconst *oiit-source* (oiit-crlf (oiit-o "From: poster@example.invalid
Subject: hello
Newsgroups: fn.letters
Message-ID: <a.b@example.invalid>

Hello, news.
")))
(defconst *oiit-agent* (oiit-o "fn.example.invalid"))
(defconst *oiit-inj* (fn-inj-make-config t *oiit-agent* (list (oiit-o "fn.letters")) 32768))
(defconst *oiit-obs* (fn-clock-observation 1000000 843004800000 500 t))
(defconst *oiit-d* (fn-inj-decide *oiit-source* *oiit-inj* *oiit-obs*))
(defconst *oiit-ring* (list (fn-ns-make-entry 1 (oiit-o "local")
                                              (make-list 32 :initial-element 7))))
(defconst *oiit-account* (make-list 32 :initial-element 5))
(defconst *oiit-sub* (fn-own-sub-make-author 3 0 nil *oiit-d* (oiit-o "alice") *oiit-account*))
(defconst *oiit-cfg* (fn-cfg-initial))
(defconst *oiit-stored* (fn-own-sub-stored-octets *oiit-cfg* *oiit-sub* *oiit-ring*))

; Positive witness: an injected decision; the stored octets open with the
; node's Cancel-Lock ("C") and carry the posting-account parameter, and the
; D25 subject is the poster's source.
(assert-event
 (and (fn-inj-injectedp *oiit-d*)
      (equal (car *oiit-stored*) 67)
      (not (equal *oiit-stored* (fn-inj-decision-octets *oiit-d*)))
      (equal (fn-pb-subject *oiit-stored* *oiit-agent* (fn-inj-decision-msgid *oiit-d*))
             (cons :source *oiit-source*))))
; Omitted hypothesis (an injection): a submission whose decision is not the
; injection named gives no source.
(assert-event
 (let ((sub (fn-own-sub-make-author 3 0 nil nil (oiit-o "alice") *oiit-account*)))
   (not (equal (fn-pb-subject (fn-own-sub-stored-octets *oiit-cfg* sub *oiit-ring*)
                              *oiit-agent* (fn-inj-decision-msgid *oiit-d*))
               (cons :source *oiit-source*)))))
(must-fail-checked
 (defthm oiit-any-stored-octets-have-the-source
   (equal (fn-pb-subject (fn-own-sub-stored-octets cfg sub ring)
                         (fn-inj-config-agent config)
                         (fn-inj-decision-msgid (fn-own-sub-decision sub)))
          (cons :source source))))
