; The real moderated POST route creates an envelope BODY from the whole source.
; This is a design boundary, not an invalid recipe or an octet-domain failure.
(in-package "ACL2")
(include-book "../../books/nntp-post")
(include-book "../../books/article-art")
(include-book "must-fail-checked")
(include-book "arena-lift")

(defun pamb-o (s)
 (declare (xargs :guard (stringp s)))
 (fn-nntp-string-octets s))
(defconst *pamb-agent* (pamb-o "fn.example.invalid"))
(defconst *pamb-groups* (list (pamb-o "fn.mod") (pamb-o "fn.queue")))
(defconst *pamb-cfg*
 (fn-inj-make-config-closed t *pamb-agent* *pamb-groups* 32768
  (list (list :moderated (pamb-o "fn.mod") (pamb-o "fn.queue")
              (list (pamb-o "alice"))))))
(defconst *pamb-open-cfg*
 (fn-inj-make-config-closed t *pamb-agent* *pamb-groups* 32768 nil))
(defconst *pamb-clock* (fn-clock-observation 1000000 843004800000 500 t))
(defconst *pamb-lines*
 (list (pamb-o "From: poster@example.invalid")
       (pamb-o "Subject: hello")
       (pamb-o "Newsgroups: fn.mod")
       (pamb-o "Message-ID: <m1@example.invalid>")
       nil (pamb-o "Hello.")))
(defconst *pamb-source* (fn-post-body-octets *pamb-lines*))
(defconst *pamb-input-art* (fn-art-of *pamb-source*))
(defconst *pamb-envelope*
 (fn-post-gated-decision *pamb-source* *pamb-cfg* *pamb-clock*))
(defconst *pamb-output-art* (fn-art-of (fn-inj-decision-octets *pamb-envelope*)))
(defconst *pamb-control*
 (fn-post-gated-decision *pamb-source* *pamb-open-cfg* *pamb-clock*))
(defconst *pamb-forwarded*
 (fn-mod-forwarded-source *pamb-source* (fn-mod-facts *pamb-source* *pamb-cfg*)
  (pamb-o "<m1@example.invalid>")
  (fn-inj-date-octets (fn-inj-instant-of (fn-clock-wall *pamb-clock*)))))

; Traverse the actual POST command and article step with an empty arena.
(defconst *pamb-archive* (fn-initial-state '("fn.mod" "fn.queue")))
(bpr-lift fn-nntp-post-step 6)
(defconst *pamb-awaiting*
 (fn-post-result-session
  (in-arena-fn-nntp-post-step nil (fn-post-open-session *pamb-archive*)
   *pamb-archive* *pamb-cfg* *pamb-clock* *pamb-clock*
   (list :command (pamb-o "POST")))))
(defconst *pamb-post-result*
 (in-arena-fn-nntp-post-step nil *pamb-awaiting* *pamb-archive*
  *pamb-cfg* *pamb-clock* *pamb-clock* (list :article *pamb-lines*)))

(assert-event
 (and (fn-inj-configp *pamb-cfg*)
      (fn-clock-observationp *pamb-clock*)
      (fn-wire-octet-linesp *pamb-lines*)
      (fn-bch-octetsp *pamb-source*)
      (fn-post-sessionp *pamb-awaiting*)
      (fn-post-session-awaiting *pamb-awaiting*)
      (fn-art-headp *pamb-input-art*)
      (fn-art-headp *pamb-output-art*)
      (fn-inj-injectedp *pamb-envelope*)
      (equal (fn-post-result-submission *pamb-post-result*) *pamb-envelope*)
      (equal (fn-inj-decision-groups *pamb-envelope*) (list (pamb-o "fn.queue")))
      (equal (fn-bch-unpack (fn-art-body *pamb-input-art*))
             (append (pamb-o "Hello.") '(13 10)))
      (equal (fn-bch-unpack (fn-art-body *pamb-output-art*)) *pamb-forwarded*)
      (not (equal (fn-art-body *pamb-output-art*) (fn-art-body *pamb-input-art*)))
      (fn-inj-injectedp *pamb-control*)
      (equal (fn-art-body (fn-art-of (fn-inj-decision-octets *pamb-control*)))
             (fn-art-body *pamb-input-art*))))

(must-fail-checked
 (assert-event
  (implies (and (fn-bch-octetsp *pamb-source*) (fn-art-headp *pamb-input-art*)
                (fn-inj-injectedp *pamb-envelope*))
   (equal (fn-art-body *pamb-output-art*) (fn-art-body *pamb-input-art*)))))
