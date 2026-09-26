; Witnesses and teeth for books/relay-source.lisp and
; books/relay-source-routes.lisp (PRF-127): relaying cannot change the
; authored source.
;
; The article is the corpus's client-path element (tests/fixtures/
; source-corpus/client-path.article: a client-supplied Path tail, D32), in
; the BP peer's group and with a folded unknown header, injected at A by the
; real fn-inj-decide, so it carries A's injection-added Path prefix,
; Injection-Date and Injection-Info.  B is the bp-transit-join-tests node
; and configuration: peer dtnB, whose record expects A's identity
; dtnb.example, and B's own identity fnA.hbox.test.  Every subject is the
; function the host calls: fn-peer-relayed-octets (host/owner-host.lisp
; fn-owner-take), fn-peer-decide-transfer and fn-peer-injection-arguments
; (fn-peer-transfer), and fn-bpaj-transit-plan (host/bp-native-app-host.lisp
; fn-owner-app-plan-install).
(in-package "ACL2")
(include-book "../../books/relay-source-routes")
(include-book "bp-transit-join-tests")
(include-book "std/testing/must-fail" :dir :system)

(defconst *rst-crlf* '(13 10))
(defun rst-lines (strings)
  (if (consp strings)
      (append (pt-o (car strings)) *rst-crlf* (rst-lines (cdr strings)))
    nil))
(defun rst-authored (x)
  (fn-hc-authored-source (fn-article-result-article (fn-article-parse x))))
(defun rst-parsesp (x) (fn-article-result-okp (fn-article-parse x)))
(defun rst-sublistp (p x)
  (cond ((fn-pu-prefixp p x) t)
        ((atom x) nil)
        (t (rst-sublistp p (cdr x)))))

(defconst *rst-msgid* "<sc2-client-path@example.invalid>")
(defconst *rst-source*
  (rst-lines (list "Path: poster.example.invalid!not-for-mail"
                   "From: poster@example.invalid"
                   "Newsgroups: fn.letters"
                   "Subject: corpus client path"
                   "Date: Fri, 25 Sep 2026 12:00:00 +0000"
                   (concatenate 'string "Message-ID: " *rst-msgid*)
                   "X-Corpus-Unknown: kept,"
                   "	folded"
                   ""
                   "a supplied Path tail (D32)")))
; A's injecting agent is the identity B's peer record expects.
(defconst *rst-inj*
  (fn-inj-make-config t (pt-o "dtnb.example") (list (pt-o "fn.letters")) 32768))
(make-event
 `(defconst *rst-a-decision* ',(fn-inj-decide *rst-source* *rst-inj* *pt-obs*)))
(defconst *rst-a* (fn-inj-decision-octets *rst-a-decision*))
(assert-event (fn-inj-injectedp *rst-a-decision*))
; A's stored octets carry the injection prefix and keep the poster's tail.
(assert-event (rst-sublistp (pt-o "Path: dtnb.example!poster.example.invalid!not-for-mail")
                            *rst-a*))
(assert-event (rst-sublistp (pt-o "Injection-Info: ") *rst-a*))

; What B stores.
(make-event
 `(defconst *rst-b* ',(fn-peer-relayed-octets *btj-cfg* "dtnB" *rst-a*)))
(assert-event (rst-sublistp
               (pt-o "Path: fnA.hbox.test!!dtnb.example!poster.example.invalid!not-for-mail")
               *rst-b*))

; -----------------------------------------------------------------------------
; fn-rs-authored-source-is-the-walk

(assert-event (and (rst-parsesp *rst-a*)
                   (equal (rst-authored *rst-a*)
                          (fn-rs-source-walk (fn-pu-strip *rst-a* nil) nil))
                   ; the projection is not constant: it keeps the authored
                   ; fields, and drops the node-added ones
                   (rst-sublistp (pt-o "X-Corpus-Unknown: kept,") (rst-authored *rst-a*))
                   (rst-sublistp (pt-o "Subject: corpus client path") (rst-authored *rst-a*))
                   (not (rst-sublistp (pt-o "Injection-Info") (rst-authored *rst-a*)))
                   (not (rst-sublistp (pt-o "Path:") (rst-authored *rst-a*)))))
; Without the parse: octets with no blank line are refused by the parser,
; whose "article" projects to nil, while the walk returns the line.
(defconst *rst-unframed* (rst-lines (list "From: poster@example.invalid")))
(assert-event (and (not (rst-parsesp *rst-unframed*))
                   (not (equal (rst-authored *rst-unframed*)
                               (fn-rs-source-walk (fn-pu-strip *rst-unframed* nil) nil)))))
(must-fail
 (defthm rst-walk-without-the-parse
   (equal (fn-hc-authored-source (fn-article-result-article (fn-article-parse y)))
          (fn-rs-source-walk (fn-pu-strip y nil) nil))))

; -----------------------------------------------------------------------------
; fn-rs-relaying-keeps-the-authored-source over fn-peer-relayed-octets

(assert-event (and (rst-parsesp *rst-a*)
                   (rst-parsesp *rst-b*)
                   (not (equal *rst-a* *rst-b*))
                   (consp (rst-authored *rst-a*))
                   (equal (rst-authored *rst-b*) (rst-authored *rst-a*))))
; With a sender's Xref (a non-fn sending node): B drops it, and the
; authored source is still A's.
(defconst *rst-xref* (append (rst-lines (list "Xref: dtnb.example fn.letters:3")) *rst-a*))
(make-event
 `(defconst *rst-xref-b* ',(fn-peer-relayed-octets *btj-cfg* "dtnB" *rst-xref*)))
(assert-event (and (rst-parsesp *rst-xref*) (rst-parsesp *rst-xref-b*)
                   (not (fn-pu-xref-freep *rst-xref*))
                   (fn-pu-xref-freep *rst-xref-b*)
                   (equal (rst-authored *rst-xref-b*) (rst-authored *rst-a*))
                   (equal (rst-authored *rst-xref*) (rst-authored *rst-a*))))
; The authored source does see an authored byte: another Subject is another
; source, through the same relay.
(defconst *rst-other*
  (fn-inj-decision-octets
   (fn-inj-decide (rst-lines (list "Path: poster.example.invalid!not-for-mail"
                                   "From: poster@example.invalid"
                                   "Newsgroups: fn.letters"
                                   "Subject: corpus client path!"
                                   "Date: Fri, 25 Sep 2026 12:00:00 +0000"
                                   (concatenate 'string "Message-ID: " *rst-msgid*)
                                   "X-Corpus-Unknown: kept,"
                                   "	folded"
                                   ""
                                   "a supplied Path tail (D32)"))
                  *rst-inj* *pt-obs*)))
(assert-event (not (equal (rst-authored *rst-other*) (rst-authored *rst-a*))))

; Hypothesis removal, the parse of what arrived: an Xref line longer than
; RFC 5322's 998 octets makes the received octets unparseable; B's relay
; drops it, and the stored octets parse.  Retained hypothesis true, omitted
; one false, conclusion false.
(defun rst-repeat (n c) (if (zp n) nil (cons c (rst-repeat (1- n) c))))
(defconst *rst-long-xref*
  (append (pt-o "Xref: dtnb.example fn.letters:") (rst-repeat 980 49) *rst-crlf* *rst-a*))
(make-event
 `(defconst *rst-long-xref-b* ',(fn-peer-relayed-octets *btj-cfg* "dtnB" *rst-long-xref*)))
(assert-event (and (not (rst-parsesp *rst-long-xref*))
                   (rst-parsesp *rst-long-xref-b*)
                   (not (equal (rst-authored *rst-long-xref-b*)
                               (rst-authored *rst-long-xref*)))))
(must-fail
 (defthm rst-relay-without-the-received-parse
   (implies (fn-article-result-okp
             (fn-article-parse (fn-peer-relayed-octets cfg peer octets)))
            (equal (fn-hc-authored-source
                    (fn-article-result-article
                     (fn-article-parse (fn-peer-relayed-octets cfg peer octets))))
                   (fn-hc-authored-source
                    (fn-article-result-article (fn-article-parse octets)))))))

; Hypothesis removal, the parse of what is stored: a received Path line of
; 995 octets parses, and B's splice pushes it past 998.
(defconst *rst-long-path*
  (append (pt-o "Path: ") (rst-repeat 988 97) (pt-o "!x") *rst-crlf*
          (rst-lines (list "From: poster@example.invalid" "Newsgroups: fn.letters"
                           "Subject: long path" "Date: Fri, 25 Sep 2026 12:00:00 +0000"
                           "Message-ID: <sc2-long-path@example.invalid>" "" "body"))))
(make-event
 `(defconst *rst-long-path-b* ',(fn-peer-relayed-octets *btj-cfg* "dtnB" *rst-long-path*)))
(assert-event (and (rst-parsesp *rst-long-path*)
                   (not (rst-parsesp *rst-long-path-b*))
                   (not (equal (rst-authored *rst-long-path-b*)
                               (rst-authored *rst-long-path*)))))
(must-fail
 (defthm rst-relay-without-the-stored-parse
   (implies (fn-article-result-okp (fn-article-parse octets))
            (equal (fn-hc-authored-source
                    (fn-article-result-article
                     (fn-article-parse (fn-peer-relayed-octets cfg peer octets))))
                   (fn-hc-authored-source
                    (fn-article-result-article (fn-article-parse octets)))))))

; -----------------------------------------------------------------------------
; fn-rs-a-wanted-transfer-keeps-the-authored-source (NNTP transit)

(defconst *rst-mo* (pt-o *rst-msgid*))
(make-event
 `(defconst *rst-want*
    ',(fn-peer-decide-transfer *pt-node0* *btj-cfg* "dtnB" *rst-mo* *rst-a* *pt-obs*
                               "rst-id" "rst-subject")))
(make-event
 `(defconst *rst-args*
    ',(fn-peer-injection-arguments *pt-node0* *btj-cfg* "dtnB" *rst-mo* *rst-a* 1
                                   "rst-id" "rst-subject" *pt-obs*)))
(assert-event (and (equal (fn-peer-decision-kind *rst-want*) :want)
                   (rst-parsesp *rst-a*)
                   (rst-parsesp (nth 2 *rst-args*))
                   (equal (nth 2 *rst-args*) *rst-b*)
                   (equal (rst-authored (nth 2 *rst-args*)) (rst-authored *rst-a*))))
; Without :want: the Path the splice would push past the line bound is
; refused as :oversize, and its stored projection has no authored source.
(make-event
 `(defconst *rst-refused*
    ',(fn-peer-decide-transfer *pt-node0* *btj-cfg* "dtnB"
                               (pt-o "<sc2-long-path@example.invalid>")
                               *rst-long-path* *pt-obs* "rst-id" "rst-subject")))
(make-event
 `(defconst *rst-refused-args*
    ',(fn-peer-injection-arguments *pt-node0* *btj-cfg* "dtnB"
                                   (pt-o "<sc2-long-path@example.invalid>")
                                   *rst-long-path* 1 "rst-id" "rst-subject" *pt-obs*)))
(assert-event (and (equal *rst-refused* (fn-peer-decision :refuse :oversize))
                   (not (rst-parsesp (nth 2 *rst-refused-args*)))
                   (not (equal (rst-authored (nth 2 *rst-refused-args*))
                               (rst-authored *rst-long-path*)))))
(must-fail
 (defthm rst-transfer-without-the-want
   (let ((stored (nth 2 (fn-peer-injection-arguments node cfg peer msgid octets
                                                     generation id subject clock))))
     (and (fn-article-result-okp (fn-article-parse octets))
          (fn-article-result-okp (fn-article-parse stored))
          (equal (fn-hc-authored-source
                  (fn-article-result-article (fn-article-parse stored)))
                 (fn-hc-authored-source
                  (fn-article-result-article (fn-article-parse octets))))))))

; -----------------------------------------------------------------------------
; fn-rs-a-bp-transit-keeps-the-authored-source (the BP route)

(make-event
 `(defconst *rst-subject*
    ',(fn-record-octets-string (fn-id-text (fn-id-subject-of-payload *rst-a*)))))
(defconst *rst-request-octets*
  (fn-bpa-encode (fn-bpa-make-request "work-rst" *rst-subject* "dtn://b/" "dtn://local/"
                                      "policy" "incarnation" "auth" "terms" *rst-a*)))
(make-event
 `(defconst *rst-plan*
    ',(fn-bpaj-transit-plan *pt-node0* *btj-cfg* *btj-ingress* "dtn://b/"
                            *rst-request-octets* *pt-obs*)))
(assert-event (and (equal (car *rst-plan*) :submit)
                   (equal (fn-bpa-request-article (fn-bpaj-request *rst-request-octets*)) *rst-a*)
                   (rst-parsesp *rst-a*)
                   (rst-parsesp (fn-bpaj-transit-stored-octets *rst-plan*))
                   (equal (fn-bpaj-transit-stored-octets *rst-plan*) *rst-b*)
                   (not (equal (fn-bpaj-transit-stored-octets *rst-plan*) *rst-a*))
                   (equal (rst-authored (fn-bpaj-transit-stored-octets *rst-plan*))
                          (rst-authored *rst-a*))))
; Without :submit: a request whose article the parser refuses is not
; submitted, and the conclusion's first conjunct fails.
(make-event
 `(defconst *rst-bad-subject*
    ',(fn-record-octets-string (fn-id-text (fn-id-subject-of-payload *rst-long-xref*)))))
(defconst *rst-bad-request-octets*
  (fn-bpa-encode (fn-bpa-make-request "work-rst-bad" *rst-bad-subject* "dtn://b/" "dtn://local/"
                                      "policy" "incarnation" "auth" "terms" *rst-long-xref*)))
(make-event
 `(defconst *rst-bad-plan*
    ',(fn-bpaj-transit-plan *pt-node0* *btj-cfg* *btj-ingress* "dtn://b/"
                            *rst-bad-request-octets* *pt-obs*)))
(assert-event (and (not (equal (car *rst-bad-plan*) :submit))
                   (equal (fn-bpa-request-article (fn-bpaj-request *rst-bad-request-octets*))
                          *rst-long-xref*)
                   (not (rst-parsesp *rst-long-xref*))))
(must-fail
 (defthm rst-bp-transit-without-the-submit
   (let ((plan (fn-bpaj-transit-plan node cfg ingress source-eid request-octets clock))
         (article (fn-bpa-request-article (fn-bpaj-request request-octets))))
     (and (fn-article-result-okp (fn-article-parse article))
          (fn-article-result-okp
           (fn-article-parse (fn-bpaj-transit-stored-octets plan)))
          (equal (fn-hc-authored-source
                  (fn-article-result-article
                   (fn-article-parse (fn-bpaj-transit-stored-octets plan))))
                 (fn-hc-authored-source
                  (fn-article-result-article (fn-article-parse article))))))))
