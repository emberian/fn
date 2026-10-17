; Witnesses and teeth for books/filed-stored (O1 P3-5): three POSTs at
; profile limits equal to the source's own census, each injected, stored
; parsing, within the widened limits and NOT within the unwidened ones (the
; widening is needed): all generated (W1), a cancel adding seven fields (W2),
; a supplied Path, the splice arm (W3).  Removal of the parse hypothesis: a
; 990-octet supplied Path is injected and its stored bytes do not parse, so
; the conclusion fails.  Mutation: six added fields refuse W2.
; P4-1 and P4-3 (the transit arm) witnesses are at the end.
(in-package "ACL2")
(include-book "peer-inbound-tests")   ; the configured peer innA and its transferred article

(defun p3-codes (cs) (declare (xargs :mode :program)) (if (consp cs) (cons (char-code (car cs)) (p3-codes (cdr cs))) nil))
(defun p3-octets (s) (declare (xargs :mode :program)) (p3-codes (coerce s 'list)))
(defun p3-lines (lines) (declare (xargs :mode :program)) (if (consp lines) (append (p3-octets (car lines)) '(13 10) (p3-lines (cdr lines))) nil))
(defun p3-rep (n s) (declare (xargs :mode :program)) (if (zp n) "" (concatenate 'string s (p3-rep (1- n) s))))
(defconst *p3-long-path*
  (p3-lines (list "From: ember <ember@example.org>" "Subject: dated" "Newsgroups: fn.letters"
                  (concatenate 'string "Path: " (p3-rep 490 "a!") "hbox")
                  "Date: Tue, 22 Sep 2026 21:26:21 +0000" "Message-ID: <tin.1@example.org>" "" "body")))
(defun p3-crlf (x)
  (declare (xargs :mode :program))
  (if (consp x) (if (equal (car x) 10) (list* 13 10 (p3-crlf (cdr x))) (cons (car x) (p3-crlf (cdr x)))) nil))
(defconst *p3-agent* (p3-octets "fn.example.invalid"))
(defconst *p3-obs* (fn-clock-observation 1000000 843004800000 500 t))
(defconst *p3-ring* (list (fn-ns-make-entry 1 (p3-octets "local") (make-list 32 :initial-element 7))))
(defconst *p3-account* (p3-octets "alice"))
(defconst *p3-cfg1*
  (fn-cfg-make 1 (fn-cfg-apply-delta (fn-cfg-empty-value) 1 (fn-clock-observation 5 1700000000 2 t)
                                     (fn-cfg-set-policy "complaints-to" (p3-octets "abuse@example.org")))))
; config whose profile limits are exactly SOURCE's census
(defun p3-inj-at (source) (declare (xargs :mode :program))
  (fn-inj-make-config t *p3-agent* (list (p3-octets "fn.letters"))
                      (cons 32768 (fn-article-header-census source))))
; W1: everything generated (Path, Injection-Date, Message-ID, Date,
; Injection-Info with posting-account and mail-complaints-to, Cancel-Lock).
(defconst *p3-src-gen* (p3-crlf (p3-octets "From: poster@example.invalid
Subject: hello
Newsgroups: fn.letters

Hello, news.
")))
; W2: a cancel (adds Cancel-Key).
(defconst *p3-src-cancel* (p3-crlf (p3-octets "From: poster@example.invalid
Subject: cmsg cancel <a.b@example.invalid>
Newsgroups: fn.letters
Control: cancel <a.b@example.invalid>

cancel
")))
; W3: a supplied Path (the splice arm), Date and Message-ID supplied.
(defconst *p3-src-path* (p3-crlf (p3-octets "Path: example.org!hbox
From: poster@example.invalid
Subject: dated
Newsgroups: fn.letters
Date: Tue, 22 Sep 2026 21:26:21 +0000
Message-ID: <tin.1@example.org>

body
")))

(defun p4-tl (path ngs extra)
  (declare (xargs :mode :program))
  (fn-post-body-octets
   (pt-lines (append (list path "From: poster@example.invalid" (concatenate 'string "Newsgroups: " ngs))
                     extra
                     (list "Subject: s" "Date: Sat, 19 Sep 2026 12:00:00 +0000"
                           "Message-ID: <a1@example.invalid>" "" "body")))))

