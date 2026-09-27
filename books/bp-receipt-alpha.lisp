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
                                   fn-articles-wire-of fn-find-article))
           :use ((:instance fn-bpr-rows-stand-for-is-member-of-alpha
                  (rows (fn-bpr-article-records (fn-sf-records (fn-sn-files store)))))
                 (:instance fn-bpr-article-records-over-alpha
                  (rows (fn-sf-records (fn-sn-files store))))
                 (:instance fn-bpi-node-wire-committedp-is-committed-over-alpha
                  (node (fn-sn-node store)))))))
