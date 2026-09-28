; Witnesses and teeth for books/web-config.lisp (lane web-native, PRF-340).
(in-package "ACL2")
(include-book "../../books/web-config")
(include-book "must-fail-checked")

(defun wcft-octs (s) (declare (xargs :guard (stringp s))) (fn-wrq-chars-octets (coerce s 'list)))

(defconst *wcft-profile*
  (wcft-octs "[store]
path = \"/tmp/s\"

[listener]
port = 119

[web]
port = 8119
site = \"Friends news\"
domain = \"news.example\"
proxied = true
"))

(defconst *wcft-plan* (fn-web-config-plan *wcft-profile* 119 nil nil))
(assert-event (equal *wcft-plan*
                     (list :web 8119 :inet '(127 0 0 1) (wcft-octs "Friends news")
                           (wcft-octs "news.example") t nil 43200 64)))
(assert-event (equal (fn-web-plan-config *wcft-plan*)
                     (fn-web-config (wcft-octs "Friends news") (wcft-octs "news.example") t 43200 64)))
; No [web] port: no face.  The profile's own port: refused.  TLS without a
; certificate: refused.  An unknown key: the profile itself is refused.
(assert-event (equal (fn-web-config-plan (wcft-octs "[store]
path = \"/tmp/s\"
") 119 nil nil) '(:none)))
(assert-event (equal (fn-web-config-plan (wcft-octs "[web]
port = 119
") 119 nil nil) '(:refused :port-taken)))
(assert-event (equal (fn-web-config-plan (wcft-octs "[web]
port = 8119
tls = true
") 119 nil nil) '(:refused :tls-needs-certificate)))
(assert-event (equal (fn-web-config-plan (wcft-octs "[web]
port = 8119
colour = 3
") 119 nil nil) '(:refused :syntax)))

; KEYSTONE fn-web-config-plan-answers: reached witness (the plan above);
; tooth: without "the plan is :web" the refused plan's second element is
; a keyword, not a port.
(assert-event (let ((plan *wcft-plan*))
                (and (equal (car plan) :web)
                     (natp (fn-web-plan-port plan)) (not (equal (fn-web-plan-port plan) 119))
                     (member (fn-web-plan-family plan) '(:inet :inet6)))))
(assert-event (not (natp (fn-web-plan-port (fn-web-config-plan (wcft-octs "[web]
port = 119
") 119 nil nil)))))
(must-fail-checked
 (defthm wcft-tooth-plan-needs-web
   (natp (fn-web-plan-port (fn-web-config-plan octets listener-port tls-port certp)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-web-config-plan)))))
