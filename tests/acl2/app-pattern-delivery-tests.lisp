; fn: teeth for books/app-pattern-delivery.lisp.
;
; fn-pat-reader-delivers-what-the-writer-encoded: inhabited by a real Store
; event (the hybrid-store fixture's constructor, books/hybrid-store) around
; the source the pubsub posting role encodes; the reader delivers exactly
; the payload.  Each hypothesis is needed: the fixture's own event (a source
; that is not the writer's encoding, outside the kind) is delivered as
; :foreign, not as a payload; a cursor of another position fails the
; projection (:binding); a source of the grammar outside the kind (a From
; that is no mailbox-list) is refused :from.  The report kinds that are not
; articles (empty, withdrawn) pass through.  The spool check accepts the
; request it wrote and refuses another payload, another generation, and a
; non-request.

(in-package "ACL2")
(include-book "../../books/app-pattern-delivery")
(include-book "hybrid-store-tests")

(defconst *apd-name* (fn-ak-text "pubsub"))
(defconst *apd-from* (fn-ak-text "author@example.invalid"))
(defconst *apd-group* (fn-ak-text "example"))
(defconst *apd-msgid-text* "<pattern1@example.invalid>")
(defconst *apd-msgid* (fn-ak-text *apd-msgid-text*))
(defconst *apd-payload* (fn-ak-iota 115))
(defconst *apd-seconds* 1791115200)

(make-event
 `(defconst *apd-source*
    ',(fn-pat-encode *apd-name* *apd-from* *apd-seconds* *apd-group* *apd-msgid* *apd-payload*)))
(assert-event (consp *apd-source*))
(assert-event (null (fn-pat-values-check *apd-name* *apd-from* *apd-seconds* *apd-group* *apd-msgid*)))

(make-event `(defconst *apd-received*
               ',(fn-hsig-injected-carrier-octets
                  *apd-source* *hst-principal* *hst-keys*
                  *hst-signatures* *hst-injection-config*
                  *hst-injection-observation*)))
(assert-event (consp *apd-received*))
(make-event `(defconst *apd-subject-id*
               ',(fn-id-subject-of-payload *apd-received*)))
(defconst *apd-subject* (fn-record-octets-string (fn-id-text *apd-subject-id*)))
(make-event `(defconst *apd-obligation*
               ',(fn-record-octets-string
                  (fn-id-text
                   (fn-id-obligation-of (fn-record-string-octets *apd-msgid-text*)
                                        *apd-subject-id*)))))
(make-event `(defconst *apd-event*
               ',(fn-hsig-authorized-injected-carried-submission-event
                  2 3 4 4 *hst-snapshot* *apd-msgid-text*
                  *apd-source* *apd-received* '("example")
                  *apd-obligation* *apd-subject* "release"
                  (fn-charge-for-payload (len *apd-received*))
                  *hst-principal* *hst-keys* *hst-signatures* *hst-ml-key*
                  :verified :verified *hst-injection-config*
                  *hst-injection-observation*)))
(assert-event (fn-stxa-p *apd-event*))

(defconst *apd-cursor* (fn-cp-cursor-encode (fn-cp-cursor '(1) '(2) '(3) '(4) '(5) 1 1 1 3)))
(defconst *apd-event-bytes* (fn-stxa-encode *apd-event*))

; Inhabited: every hypothesis holds and the reader delivers the payload.
(make-event `(defconst *apd-projection* ',(fn-cpj-project *apd-cursor* *apd-event-bytes*)))
(assert-event (equal (car *apd-projection*) :ok))
(assert-event (equal (nth 6 *apd-projection*) *apd-source*))
(assert-event
 (equal (fn-pat-decode :opaque-1 (fn-pat-project *apd-cursor* *apd-event-bytes*))
        (list :deliver 2 *apd-msgid* *apd-payload*)))
(assert-event (equal (fn-pat-delivery-name 2) (fn-ak-text "00000000000000000002.payload")))

; The source hypothesis is needed: the fixture's event projects, but its
; source is not the writer's encoding (and not of the kind).
(defconst *apd-other-bytes* (fn-stxa-encode *hst-injected-event*))
(assert-event (equal (car (fn-cpj-project *apd-cursor* *apd-other-bytes*)) :ok))
(assert-event
 (equal (fn-pat-decode :opaque-1 (fn-pat-project *apd-cursor* *apd-other-bytes*))
        (list :foreign :malformed (fn-ak-text "<hybrid@example.invalid>"))))

; The projection hypothesis is needed: a cursor of another position.
(defconst *apd-cursor-2* (fn-cp-cursor-encode (fn-cp-cursor '(1) '(2) '(3) '(4) '(5) 1 1 1 2)))
(assert-event (equal (car (fn-pat-decode :opaque-1 (fn-pat-project *apd-cursor-2* *apd-event-bytes*)))
                     :foreign))
(assert-event (equal (cadr (fn-pat-decode :opaque-1 (fn-pat-project *apd-cursor-2* *apd-event-bytes*)))
                     :binding))

; The values hypothesis is needed: a grammar source outside the kind.
(defconst *apd-bad-values*
  (fn-ak-values (fn-ak-text "nomailbox") (fn-ak-text "x") *apd-group*
                (fn-ak-text "s") *apd-msgid* (fn-ak-text "t")))
(assert-event (fn-pat-values-check *apd-name* (fn-ak-text "nomailbox") 0 *apd-group* *apd-msgid*))
(assert-event
 (equal (fn-pat-decode :opaque-1
                       (list :article 7 *apd-msgid*
                             (fn-wg-encode *fn-ak-grammar*
                                           (fn-ak-grammar-value *apd-bad-values* *apd-payload*))))
        (list :foreign :from *apd-msgid*)))

; Reports that are not articles.
(assert-event (equal (fn-pat-decode :opaque-1 (fn-pat-project *apd-cursor* nil)) '(:empty)))
(assert-event
 (equal (fn-pat-decode :opaque-1 (fn-pat-project *apd-cursor*
                                                 (append *fn-ncr-withdrawal-magic* *apd-msgid*)))
        (list :withdrawn *apd-msgid*)))

; The spool.
(defconst *apd-request*
  (fn-native-hybrid-control-author-encode
   1 *apd-source* (make-list 64 :initial-element 17) (make-list 3309 :initial-element 19)
   (fn-ak-text "/k/ml-public.pem")))
(assert-event (null (fn-pat-spool-check *apd-request* 1 *apd-name* *apd-from* *apd-group*
                                        *apd-msgid* *apd-payload*)))
(assert-event (equal (fn-pat-spool-check *apd-request* 1 *apd-name* *apd-from* *apd-group*
                                         *apd-msgid* (fn-ak-text "other"))
                     :spool-conflict))
(assert-event (equal (fn-pat-spool-check *apd-request* 2 *apd-name* *apd-from* *apd-group*
                                         *apd-msgid* *apd-payload*)
                     :spool-request))
(assert-event (equal (fn-pat-spool-check '(1 2 3) 1 *apd-name* *apd-from* *apd-group*
                                         *apd-msgid* *apd-payload*)
                     :spool-request))
