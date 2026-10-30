; D4 2/n evidence: POST's article input through the served core
; (fn2/docs/d-machines-nntp.md section 14.2-14.3). The connection takes an
; upload (A-S7's taken kind), feeds the block into its window, the upload
; hashes and scans it and posts its verdict word back, and the connection
; renders it. The expected wires are written here from the catalogue's
; texts (fn1's, nntp-grammar.lisp) and RFC 3977 section 6.3.1; each
; transcript also arrives byte by byte and in 7-octet chunks (the wire must
; not change). Posting is served only under :posting-interim (section
; 14.5): the same POST under the plain wire profile is the 440 interim.
; Run: sh fn2/tools/certify.sh tests/upload-unit.lisp
(in-package "ACL2")
(include-book "../books/owed-conn")
(include-book "../sim/check-wire")

(defconst *fn2-uu-profile*
  (put-assoc-equal :posting-interim t
    (put-assoc-equal :format-slots 5
      (put-assoc-equal :pool-classes '((8 . 1024) (4 . 4096)) *fn2-conn-wire-profile*))))

(defun fn2-uu-text (lines)
  (declare (xargs :verify-guards nil))
  (fn2-cw-crlf-octets lines))
(defun fn2-uu-sizes (n k) (declare (xargs :verify-guards nil)) (make-list (+ 1 (floor n k)) :initial-element k))

; The wire one client gets for LINES (CRLF added), arriving in chunks of K.
(defun fn2-uu-wire (profile lines k)
  (declare (xargs :verify-guards nil))
  (let* ((octets (fn2-cw-crlf-octets lines))
         (r (fn2-conn-wire-run-in profile (list (list octets (fn2-uu-sizes (len octets) k))))))
    (list (car r) (nth 2 r) (car (car (nth 1 r))) (cadr (car (nth 1 r))))))
(defun fn2-uu-check (lines expect closed)
  (declare (xargs :verify-guards nil))
  (let ((want (list :quiet 0 (fn2-uu-text expect) closed)))
    (and ;; the expected wire is one WIRE admits (POST's two phases)
         (or (fn2-wire-pass-p (fn2-uu-text lines) (fn2-uu-text expect) closed)
             (cw "WIRE ~x0~%" (fn2-wire-check (fn2-uu-text lines) (fn2-uu-text expect) closed)))
         (or (equal (fn2-uu-wire *fn2-uu-profile* lines 4096) want) (cw "whole ~x0~%" (fn2-uu-wire *fn2-uu-profile* lines 4096)))
         (or (equal (fn2-uu-wire *fn2-uu-profile* lines 7) want) (cw "by 7 ~x0~%" (fn2-uu-wire *fn2-uu-profile* lines 7)))
         (or (equal (fn2-uu-wire *fn2-uu-profile* lines 1) want) (cw "by 1 ~x0~%" (fn2-uu-wire *fn2-uu-profile* lines 1))))))

(defconst *fn2-uu-greeting* "200 fn-nntp experimental server ready")
(defconst *fn2-uu-good* '("From: a@example.invalid" "Subject: hello" "Newsgroups: local.test"
                          "Message-ID: <one@example.invalid>" "" "body" "..stuffed"))

(defun fn2-uu-fixtures ()
  (declare (xargs :verify-guards nil))
  (and
   ;; a valid article: 340, then the interim refusal (no transaction until D5),
   ;; and the connection goes on to its next command
   (fn2-uu-check (append '("POST") *fn2-uu-good* '("." "QUIT"))
                 (list *fn2-uu-greeting* "340 send article to be posted" "441 posting failed"
                       "205 closing connection") t)
   ;; definite refusals, each by its catalogue row
   (fn2-uu-check '("POST" "From: a" "Newsgroups: g" "" "x" "." "QUIT")
                 (list *fn2-uu-greeting* "340 send article to be posted" "441 posting failed; Subject is required"
                       "205 closing connection") t)
   (fn2-uu-check '("POST" "From: a" "From: b" "Subject: s" "Newsgroups: g" "" "x" "." "QUIT")
                 (list *fn2-uu-greeting* "340 send article to be posted" "441 posting failed; From appears more than once"
                       "205 closing connection") t)
   (fn2-uu-check '("POST" "From: a" "Subject: s" "Newsgroups: g" "Xref: h g:1" "" "x" "." "QUIT")
                 (list *fn2-uu-greeting* "340 send article to be posted" "441 posting failed; Xref must not be supplied"
                       "205 closing connection") t)
   (fn2-uu-check '("POST" "From: a" "Subject: s" "Newsgroups: g" "Message-ID: <bad>" "" "x" "." "QUIT")
                 (list *fn2-uu-greeting* "340 send article to be posted"
                       "441 posting failed; Message-ID is not a valid identifier" "205 closing connection") t)
   ;; an unescaped leading dot: drained to the terminator, refused, closed
   (fn2-uu-check '("POST" "From: a" "Subject: s" "Newsgroups: g" "" ".bad" "." "QUIT")
                 (list *fn2-uu-greeting* "340 send article to be posted"
                       "441 posting failed; the article is not valid syntax") t)
   ;; two posts on one connection, pipelined
   (fn2-uu-check (append '("POST") *fn2-uu-good* '(".") '("POST" "From: a" "Newsgroups: g" "" "x" "." "QUIT"))
                 (list *fn2-uu-greeting* "340 send article to be posted" "441 posting failed"
                       "340 send article to be posted" "441 posting failed; Subject is required"
                       "205 closing connection") t)))
(assert-event (fn2-uu-fixtures))

; Over the bound (8 KiB with 4 KiB chunks): refused as oversize, the block
; drained, nothing buffered past the bound.
(defun fn2-uu-big (n) (declare (xargs :verify-guards nil))
  (if (zp n) nil (cons (coerce (make-list 100 :initial-element #\z) 'string) (fn2-uu-big (- n 1)))))
(assert-event
 (fn2-uu-check (append '("POST" "From: a" "Subject: s" "Newsgroups: g" "") (fn2-uu-big 100) '("." "QUIT"))
               (list *fn2-uu-greeting* "340 send article to be posted"
                     "441 posting failed; the article exceeds the configured size" "205 closing connection") t))

; Posting not served (the plain wire profile): the greeting says 201 and
; POST is the interim 440.
(assert-event
 (equal (fn2-uu-wire *fn2-conn-wire-profile* '("POST" "QUIT") 4096)
        (list :quiet 0 (fn2-uu-text (list "201 fn-nntp experimental reader ready" "440 posting not permitted"
                                          "205 closing connection")) t)))

; Three clients POST at once over two upload rows (the profile's two
; windows): the third connection's take parks it on the upload kind's FIFO
; (A-S7) and the grant, once a row and its chunks are free again, re-runs
; its POST line. Every client gets the same wire.
(defun fn2-uu-many (lines n k)
  (declare (xargs :verify-guards nil))
  (let* ((octets (fn2-cw-crlf-octets lines))
         (one (list octets (fn2-uu-sizes (len octets) k))))
    (fn2-conn-wire-run-in *fn2-uu-profile* (make-list n :initial-element one))))
(defun fn2-uu-all-wires (results want)
  (declare (xargs :verify-guards nil))
  (or (atom results)
      (and (equal (car results) want) (fn2-uu-all-wires (cdr results) want))))
(assert-event
 (let* ((r (fn2-uu-many (append '("POST") *fn2-uu-good* '("." "QUIT")) 3 7))
        (want (list (fn2-uu-text (list *fn2-uu-greeting* "340 send article to be posted" "441 posting failed"
                                       "205 closing connection")) t)))
   (or (and (equal (car r) :quiet) (equal (nth 2 r) 0) (equal (len (nth 1 r)) 3)
            (fn2-uu-all-wires (nth 1 r) want))
       (cw "many ~x0~%" (list (car r) (nth 2 r) (nth 1 r))))))

; WIRE's two POST phases have teeth: the block's reply in place of 340, and
; a 340 whose block is answered 340 again, are refused.
(assert-event
 (let ((client (fn2-uu-text (append '("POST") *fn2-uu-good* '("." "QUIT")))))
   (and (not (fn2-wire-pass-p client (fn2-uu-text (list *fn2-uu-greeting* "441 posting failed"
                                                        "205 closing connection")) t))
        (not (fn2-wire-pass-p client (fn2-uu-text (list *fn2-uu-greeting* "340 send article to be posted"
                                                        "340 send article to be posted" "205 closing connection")) t)))))
