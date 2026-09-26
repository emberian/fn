; fn: the grammar of `control log' and `control evidence MESSAGE-ID'
; (PKT-209, PRF-185).
;
; The two verbs read what the owner decided about withdrawing articles
; (books/control-evidence.lisp renders it).  They are status reports, not
; administrative plans: they publish no configuration record, and the
; running owner answers them over its control socket like `status' (the
; FNLS exchange, books/native-live-status.lisp).  This book is only the
; words, kept apart from books/native-admin.lisp (its certification time is
; at the ten-second line) and from the renderer (which the operator's parse
; need not load).
;
; A report kind is :control-log, or (:control-evidence . MSGID) with MSGID
; a Message-ID as the operator typed it: `<', at least one printable
; non-space US-ASCII octet, `>', at most 250 octets in all (RFC 5536
; section 3.1.3: a msg-id is at most 250 octets).
;
; Prefix `fn-cevg-' (docs/prefixes.md).
(in-package "ACL2")

(defconst *fn-cevg-max-msgid-octets* 250)

(defun fn-cevg-printable-charsp (cs)
  (declare (xargs :guard t))
  (if (consp cs)
      (and (characterp (car cs))
           (< 32 (char-code (car cs)))
           (< (char-code (car cs)) 127)
           (fn-cevg-printable-charsp (cdr cs)))
    (null cs)))

(defun fn-cevg-msgidp (x)
  (declare (xargs :guard t))
  (and (stringp x)
       (let ((cs (coerce x 'list)))
         (and (< 2 (len cs))
              (<= (len cs) *fn-cevg-max-msgid-octets*)
              (equal (car cs) #\<)
              (equal (car (last cs)) #\>)
              (fn-cevg-printable-charsp cs)))))

(defun fn-cevg-kindp (kind)
  (declare (xargs :guard t))
  (or (equal kind :control-log)
      (and (consp kind)
           (equal (car kind) :control-evidence)
           (fn-cevg-msgidp (cdr kind)))))

; The words after `control': (:kind KIND), (:usage REASON) for a word
; `evidence' whose argument is not a Message-ID, or nil for every other
; verb (the administrative grammar decides those).
(defun fn-cevg-parse (words)
  (declare (xargs :guard t))
  (cond ((and (consp words) (equal (car words) "log"))
         (if (atom (cdr words))
             (list :kind :control-log)
           (list :usage :unexpected-arguments)))
        ((and (consp words) (equal (car words) "evidence"))
         (if (and (consp (cdr words)) (atom (cddr words))
                  (fn-cevg-msgidp (cadr words)))
             (list :kind (cons :control-evidence (cadr words)))
           (list :usage :message-id)))
        (t nil)))

; What `fn-cevg-parse' accepts is a report kind the renderer takes.
(defthm fn-cevg-parse-kind-is-a-kind
  (implies (equal (car (fn-cevg-parse words)) :kind)
           (fn-cevg-kindp (cadr (fn-cevg-parse words)))))
(in-theory (disable fn-cevg-parse fn-cevg-kindp fn-cevg-msgidp))
