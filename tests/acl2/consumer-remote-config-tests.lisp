; Witnesses and teeth for books/consumer-remote-config.lisp (D48 / PKT-673):
; the [remote_consumer] listener's plan and the client's argv grammar.
(in-package "ACL2")
(include-book "../../books/consumer-remote-config")

(defun crct-octs (s) (declare (xargs :guard (stringp s))) (fn-record-string-octets s))

(defconst *crct-profile*
  (crct-octs "[store]
path = \"/tmp/s\"

[listener]
port = 119

[remote_consumer]
port = 1563
max_sessions = 2
"))

; Satisfiable: a port, a certificate, the default loopback host.
(assert-event (equal (fn-crc-config-plan *crct-profile* 119 563 t)
                     (list :remote 1563 :inet '(127 0 0 1) 2)))
; Teeth: no certificate, no listener (FNCR carries an account password).
(assert-event (equal (fn-crc-config-plan *crct-profile* 119 563 nil)
                     '(:refused :tls-needs-certificate)))
; No table: no listener.  A taken port, zero sessions, too many sessions.
(assert-event (equal (fn-crc-config-plan (crct-octs "[store]
path = \"/tmp/s\"
") 119 563 t) '(:none)))
(assert-event (equal (fn-crc-config-plan (crct-octs "[remote_consumer]
port = 563
") 119 563 t) '(:refused :port-taken)))
(assert-event (equal (fn-crc-config-plan (crct-octs "[remote_consumer]
port = 1563
max_sessions = 0
") 119 563 t) '(:refused :bounds)))
(assert-event (equal (fn-crc-config-plan (crct-octs "[remote_consumer]
port = 1563
max_sessions = 65
") 119 563 t) '(:refused :bounds)))
; An unknown key refuses the profile itself.
(assert-event (equal (fn-crc-config-plan (crct-octs "[remote_consumer]
port = 1563
mode = \"open\"
") 119 563 t) '(:refused :syntax)))

; The client's argv grammar.
(defun crct-argv (words) (if (consp words) (cons (crct-octs (car words)) (crct-argv (cdr words))) nil))
(assert-event
 (equal (fn-crc-cli-plan (crct-argv '("wait" "127.0.0.1" "1563" "ca.pem" "bob" "pw" "inbox"
                                      "cursor" "report" "30")))
        (list :run :wait (crct-octs "127.0.0.1") 1563 (crct-octs "ca.pem") (crct-octs "bob")
              (crct-octs "pw") (crct-octs "inbox") (crct-octs "cursor") (crct-octs "report") 30)))
(assert-event
 (equal (fn-crc-cli-plan (crct-argv '("ack" "127.0.0.1" "1563" "ca.pem" "bob" "pw" "cursor")))
        (list :run :ack (crct-octs "127.0.0.1") 1563 (crct-octs "ca.pem") (crct-octs "bob")
              (crct-octs "pw") (crct-octs "cursor") nil nil 0)))
(assert-event
 (equal (fn-crc-cli-plan (crct-argv '("register" "127.0.0.1" "1563" "ca.pem" "bob" "pw" "x")))
        '(:usage)))
(assert-event
 (equal (fn-crc-cli-plan (crct-argv '("wait" "127.0.0.1" "1563" "ca.pem" "bob" "pw" "inbox"
                                      "cursor" "report" "3601")))
        '(:usage)))
(assert-event
 (equal (fn-crc-cli-plan (crct-argv '("poll" "127.0.0.1" "0" "ca.pem" "bob" "pw" "inbox"
                                      "cursor" "report")))
        '(:usage)))
