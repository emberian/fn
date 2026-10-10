; Witnesses and teeth for books/filed-stored (O1 P3-5): three POSTs at
; profile limits equal to the source's own census, each injected, stored
; parsing, within the widened limits and NOT within the unwidened ones (the
; widening is needed): all generated (W1), a cancel adding seven fields (W2),
; a supplied Path, the splice arm (W3).  Removal of the parse hypothesis: a
; 990-octet supplied Path is injected and its stored bytes do not parse, so
; the conclusion fails.  Mutation: six added fields refuse W2.
(in-package "ACL2")
(include-book "../../books/filed-stored")

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
(defun p3-check (source) (declare (xargs :mode :program))
  (let* ((config (p3-inj-at source))
         (stored (fn-o1-post-stored-octets source config *p3-obs* *p3-ring* *p3-account* *p3-cfg1*))
         (limits (fn-inj-config-header-limits config)))
    (list :injected (fn-inj-injectedp (fn-inj-decide source config *p3-obs*))
          :stored-parses (fn-article-result-okp (fn-article-parse stored))
          :widened (fn-article-result-okp
                    (fn-article-parse-under stored (fn-o1-stored-header-limits limits *p3-agent*)))
          :profile (fn-article-result-okp (fn-article-parse-under stored limits))
          :source-census (fn-article-header-census source)
          :stored-census (fn-article-header-census stored)
          :block-bound (fn-o1-injected-block-octets *p3-agent*))))
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
; Mutations: the block's seven fields are attained (the cancel adds Cancel-
; Lock, Cancel-Key, Path, Injection-Date, Message-ID, Date, Injection-Info);
; six refuses it.  The octet widening is needed (W1 :profile nil).
(defun p3-fields-6 (source) (declare (xargs :mode :program))
  (let* ((config (p3-inj-at source)) (l (fn-inj-config-header-limits config))
         (stored (fn-o1-post-stored-octets source config *p3-obs* *p3-ring* *p3-account* *p3-cfg1*)))
    (fn-article-result-okp
     (fn-article-parse-under stored (fn-article-limits (+ 6 (fn-article-limit-fields l)) (+ 7 (fn-article-limit-lines l))
                                                       (+ (fn-article-limit-octets l) (fn-o1-injected-block-octets *p3-agent*)))))))
(assert-event (and (equal (car (p3-check *p3-src-cancel*)) :injected)
                   (not (p3-fields-6 *p3-src-cancel*))))

(defun p3-holds (source) (declare (xargs :mode :program))
  (let ((r (p3-check source)))
    (and (equal (nth 1 r) t) (equal (nth 3 r) t) (equal (nth 5 r) t) (equal (nth 7 r) nil))))
(assert-event (p3-holds *p3-src-gen*))
(assert-event (p3-holds *p3-src-cancel*))
(assert-event (p3-holds *p3-src-path*))
(assert-event (equal (nth 11 (p3-check *p3-src-cancel*)) '(11 11 634)))
(assert-event (let ((r (p3-check *p3-long-path*)))
                (and (equal (nth 1 r) t) (equal (nth 3 r) nil) (equal (nth 5 r) nil))))
