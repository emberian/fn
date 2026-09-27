; The receiver's durable-acceptance predicate over a flipped Store is the
; pre-flip predicate over ALPHA of that Store (records-flip, flip-L4).
;
; books/bp-receipt.lisp fn-bpr-store-record-acceptedp is what the receiver
; asks of the Store before it binds a request context (fn-bpr-accept-request,
; through fn-bpr-request-acceptablep; host: host/bp-receipt-host.lisp and
; host/bp-receive-host.lisp through fn-bpaj-bpr-accept-request-fast).  The
; receiver holds the WIRE record; the history retains held rows and the node's
; articles hold handles.  This book states the refinement: over rows whose
; composites are what the intern made of them (fn-rows-composites-okp, which
; fn-intern-event-composite-okp establishes at every intern), the predicate
; is membership in the article records of ALPHA of the history and the node's
; comparison over ALPHA of its articles.
(in-package "ACL2")
(include-book "bp-receipt")
(include-book "history-fold-refinement")

(local (defthm fn-bpra-record-msgid-is-a-string
  (implies (fn-record-p r) (stringp (fn-record-msgid r)))
  :hints (("Goal" :in-theory (enable fn-record-p fn-record-msgidp fn-record-shapep)))))

; A Store history holds retained events only (fn-sn-statep): of its article
; records, the held rows are the only ones whose wire form is a WIRE record
; -- a composite row's article is its held row, and no other retained event
; is an article record.
(local (defthm fn-bpra-hstxa-held-is-held
  (implies (fn-hstxa-p x) (fn-held-p (fn-hstxa-held x)))
  :hints (("Goal" :in-theory (enable fn-hstxa-p fn-hstxa-held)))))
(local (defthm fn-bpra-store-event-other-is-no-record
  (implies (and (fn-store-event-p x) (not (fn-held-p x)) (not (fn-hstxa-p x)))
           (not (fn-record-p x)))
  :hints (("Goal" :in-theory (enable fn-store-event-p)))))
(local (defthm fn-bpra-store-event-is-no-stxa
  (implies (fn-store-event-p x) (not (fn-stxa-p x)))
  :hints (("Goal" :in-theory (e/d (fn-store-event-p) (fn-stxa-p fn-held-p fn-hstxa-p))
           :use ((:instance fn-stxa-is-no-other-wire-event)
                 (:instance fn-held-is-no-wire-event)
                 (:instance fn-hstxa-is-no-wire-event))))))
(local (defthm fn-bpra-member-of-alpha-stands
  (implies (and (fn-sf-record-valuesp rows)
                (fn-record-p record)
                (member-equal record (fn-rows-wire-of (fn-bpr-article-records rows) fn-arena)))
           (fn-bpr-rows-stand-for record (fn-bpr-article-records rows) fn-arena))
  :hints (("Goal" :induct (len rows)
           :in-theory (e/d (fn-bpr-article-records fn-bpr-event-article fn-rows-wire-of
                            fn-sf-record-valuesp fn-bpr-rows-stand-for fn-bpr-row-stands-for)
                           (fn-stxa-p fn-held-p fn-hstxa-p fn-record-p fn-store-event-p
                            fn-row-wire-of fn-hstxa-held fn-replay-composite-record))
           :expand ((:free (x) (fn-row-wire-of x fn-arena)))))))
(local (defthm fn-bpra-record-listp-values
  (implies (fn-sf-record-listp records sequence lower frontier)
           (fn-sf-record-valuesp records))
  :hints (("Goal" :in-theory (e/d (fn-sf-record-listp fn-sf-record-valuesp) (fn-store-event-p))))))
(local (defthm fn-bpra-statep-history-values
  (implies (fn-sn-statep s) (fn-sf-record-valuesp (fn-sf-records (fn-sn-files s))))
  :hints (("Goal" :in-theory (enable fn-sn-statep fn-sf-statep)))))

; KEYSTONE (the receipt's Store gate over the arena).
(defthm fn-bpr-store-record-acceptedp-is-acceptance-over-alpha
  (implies (fn-rows-composites-okp (fn-sf-records (fn-sn-files store)) fn-arena)
           (iff (fn-bpr-store-record-acceptedp store record fn-arena)
                (and (fn-sn-statep store) (fn-record-p record)
                     (equal (fn-sf-phase (fn-sn-files store)) :ready)
                     (member-equal
                      record
                      (fn-bpr-article-records
                       (fn-rows-wire-of (fn-sf-records (fn-sn-files store)) fn-arena)))
                     (let* ((node (fn-sn-node store))
                            (article (fn-find-article
                                      (fn-record-msgid record)
                                      (fn-articles-wire-of
                                       (fn-state-articles (fn-node-acceptance node))
                                       fn-arena)))
                            (binding (fn-node-find-binding
                                      (fn-record-msgid record) (fn-node-bindings node))))
                       (and (fn-node-statep node) (consp article) (consp binding)
                            (equal (fn-article-payload article) (fn-record-payload record))
                            (equal (fn-article-groups article) (fn-record-groups record))
                            (equal (fn-node-binding-subject binding)
                                   (fn-record-content-subject record))
                            (equal (fn-node-binding-id binding)
                                   (fn-record-obligation-id record)))))))
  :hints (("Goal" :in-theory (e/d (fn-bpr-store-record-acceptedp)
                                  (fn-bpi-node-wire-committedp fn-bpr-rows-stand-for
                                   fn-rows-wire-of fn-bpr-article-records
                                   fn-articles-wire-of fn-find-article fn-record-p
                                   fn-bpi-node-wire-committedp-is-committed-over-alpha
                                   fn-bpra-member-of-alpha-stands fn-sn-statep))
           :use ((:instance fn-bpra-record-msgid-is-a-string (r record))
                 (:instance fn-bpr-rows-stand-for-is-member-of-alpha
                  (rows (fn-bpr-article-records (fn-sf-records (fn-sn-files store)))))
                 (:instance fn-bpra-member-of-alpha-stands
                  (rows (fn-sf-records (fn-sn-files store))))
                 (:instance fn-bpra-statep-history-values (s store))
                 (:instance fn-bpr-article-records-over-alpha
                  (rows (fn-sf-records (fn-sn-files store))))
                 (:instance fn-bpi-node-wire-committedp-is-committed-over-alpha
                  (node (fn-sn-node store)))))))
