; The native authority regression: a 3309-octet detached signature must
; survive field folding and NNTP's CRLF-terminated body. Crypto here is
; the explicit toy realiser, not evidence about native ML-DSA verification.
(in-package "ACL2")
(include-book "crypto-seam-tests")
(include-book "../../books/native-statement-material")
(include-book "../../books/codec-attach")
(include-book "../../books/statement-attach")
(include-book "../../books/defkeystone")

(defteeth fn-stx-framed-body-round-trip
 :claim (((octets (fn-cbor-octet-listp payload)))
         (equal (fn-stx-body-payload (fn-wg-lines 76 (fn-stx-b64-encode payload)))
                (fn-stx-ok (list payload))))
 :subject fn-stx-body-payload
 :witness ((payload (make-list 100 :initial-element 85)))
 :breaks ((octets ((payload '(256)))))
 :mutations ((drop-last-octet (:conclusion
               (equal (fn-stx-body-payload (fn-wg-lines 76 (fn-stx-b64-encode payload)))
                      (fn-stx-ok (list (cdr payload)))))
              ((payload '(1 2 3))) :fault "line framing must preserve every payload octet")))

; Incorrect CRLF and noncanonical padding are still refused. The earlier
; unframed spelling keeps exactly its old interpretation.
(assert-event (not (fn-stx-okp (fn-stx-body-payload '(90 103 61 61 10)))))
(assert-event (not (fn-stx-okp (fn-stx-body-payload '(90 103 13 10 61 61 13 10)))))
(assert-event (not (fn-stx-okp (fn-stx-body-payload '(90 104 61 61 13 10)))))
(assert-event (equal (fn-stx-body-payload '(90 103 61 61)) (fn-stx-ok (list '(102)))))

(defconst *fn-nsmt-source*
 (append (fn-record-string-octets "Path: upstream!not-for-mail") '(13 10)
         (fn-record-string-octets "From: a@example.invalid") '(13 10)
         (fn-record-string-octets "Date: Wed, 30 Sep 2026 12:00:00 +0000") '(13 10)
         (fn-record-string-octets "Newsgroups: fn.test") '(13 10)
         (fn-record-string-octets "Subject: authority") '(13 10)
         (fn-record-string-octets "Message-ID: <p@authority.invalid>") '(13 10 13 10)
         (make-list 160 :initial-element 120) '(13 10)))
(make-event
 (list 'defconst '*fn-nsmt-plan*
       (list 'quote (fn-nsm-plan (make-list 32 :initial-element 85) "0" "0"
                                "policy" "fn.test" *fn-nsmt-source*))))
(assert-event (consp *fn-nsmt-plan*))
; A production-sized detached signature: all field, header, payload and
; signature bytes must be recovered, including across multiple body lines.
(assert-event
 (let* ((p *fn-nsmt-plan*) (sig (make-list 3309 :initial-element 0))
        (wire (fn-nsm-render p sig)) (article (fn-stx-parse wire)))
  (and (> (len (fn-stx-header-value-parts (car p) sig)) 998)
       article
       (equal (nthcdr (- (len wire) 2) wire) '(13 10))
       (equal (fn-stx-statement-of article) (fn-stmt-make (car p) (cadr p) sig))
       ; The previous flat renderer fails before any authority observation.
       (not (fn-stx-parse
             (append (fn-record-string-octets "FN-Statement: ")
                     (fn-stx-header-value-parts (car p) sig) '(13 10) (caddr p)))))))

; Whole signing/checking composition under the named toy realiser: the
; correct supplied key succeeds and another key is refused after folding.
(assert-event
 (let* ((p *fn-nsmt-plan*) (sk (make-list 32 :initial-element 11)) (key (fn-sig-public-key sk))
        (sig (fn-sig-sign sk (cadddr p))) (principal (make-list 32 :initial-element 85)))
   (and (fn-nsm-check-rendered principal key p sig)
        (not (fn-nsm-check-rendered principal (fn-sig-public-key (make-list 32 :initial-element 23)) p sig)))))
(defteeth-check (fn-stx-framed-body-round-trip))
