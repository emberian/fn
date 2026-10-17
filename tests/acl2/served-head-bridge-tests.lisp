; PKT-772 literal HEAD bridge teeth; no qualification claim before all removals.
(in-package "ACL2")
(include-book "must-fail-checked")
(include-book "arena-lift")

(defconst *hdt-payload*
 (append (fn-nntp-string-octets "Message-ID: <head@fn.test>") '(13 10)
         (fn-nntp-string-octets "Subject: retained header") '(13 10 13 10)
         (fn-nntp-string-octets "body excluded from HEAD") '(13 10)))
(defconst *hdt-article*
 (fn-make-article "<head@fn.test>" 0 '("fn.test") '(("fn.test" . 1)) t 1))
(defconst *hdt-archive*
 (fn-make-state '("fn.test") '(("fn.test" . 2)) (list *hdt-article*) 1 nil nil))
(defconst *hdt-config*
 (fn-inj-make-config-listed t "news.fn.test" '("fn.test") 65536
  (list nil nil (fn-nntp-string-octets "news.fn.test") nil nil nil)))
(defconst *hdt-open*
 (fn-served-result-conn
  (fn-served-open-group-indexed *hdt-archive*
   (fn-gidx-build (list *hdt-article*))
   nil 510 65536 *hdt-config* nil nil (fn-auth-open-config))))
(defconst *sr-arena* (list *hdt-payload*))
(bpr-lift fn-served-step 2)
(defconst *hdt-selected*
 (fn-served-result-conn
  (in-arena-fn-served-step *sr-arena* *hdt-open*
   (append (fn-nntp-string-octets "GROUP fn.test") '(13 10)))))
(defconst *hdt-token* (fn-nntp-string-octets "<head@fn.test>"))
(assert-event (and (fn-statep *hdt-archive*) (fn-served-conn-shapep *hdt-selected*)))

(defconst *hdt-as* (fn-served-conn-session *hdt-selected*))
(defconst *hdt-peer* (fn-auth-session-base *hdt-as*))
(defconst *hdt-post* (fn-peer-session-base *hdt-peer*))
(defconst *hdt-reader* (fn-post-session-base *hdt-post*))

