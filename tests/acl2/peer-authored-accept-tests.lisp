(in-package "ACL2")
(include-book "../../books/peer-authored-accept")
(include-book "topic-history-authorship-tests")
(include-book "std/testing/must-fail" :dir :system)

(defconst *pat-snapshots* (list *tha-snapshot*))
(defconst *pat-relayed*
  (append (tha-line "Path: gateway.example!fn") *tha-received*))
(assert-event (equal (fn-pa-carrier-kind *tha-root-source*) :absent))
(assert-event (equal (fn-pa-current-plan *tha-root-source* *pat-snapshots*)
                     :absent))
(assert-event (equal (fn-pa-carrier-kind *pat-relayed*) :present))
(assert-event
 (equal (fn-pa-current-plan *pat-relayed* *pat-snapshots*)
        (list :ok *tha-root-source* *tha-principal* *tha-keys*
              *tha-signatures* *tha-snapshot* 4)))

; No B-local enrollment, wrong ordered keys, and a later B-local revocation
; are three different reasons that valid portable bytes cannot be admitted.
(assert-event (equal (fn-pa-current-plan *pat-relayed* nil)
                     (list :refused :local-enrollment)))
(assert-event
 (equal (fn-pa-current-plan
         *pat-relayed*
         (list (fn-hsig-keyring-event 1 2 3 4 *tha-principal*
                                      *tha-other-keys*)))
        (list :refused :local-enrollment)))
(make-event `(defconst *pat-revoked*
               ',(fn-hl-revoke-event 2 3 4 5 *tha-principal*
                                     *pat-snapshots*)))
(assert-event (fn-stxk-p *pat-revoked*))
(assert-event
 (equal (fn-pa-current-plan *pat-relayed*
                            (cons *pat-revoked* *pat-snapshots*))
        (list :refused :local-enrollment)))

; A present but malformed FN-Authorship cannot downgrade to the legacy path.
(defconst *pat-malformed*
  (append (tha-line "FN-Authorship: !!!") *tha-root-source*))
(assert-event (equal (fn-pa-carrier-kind *pat-malformed*) :present))
(assert-event (equal (fn-pa-current-plan *pat-malformed* *pat-snapshots*)
                     (list :refused :carrier)))
(must-fail
 (assert-event
  (equal (fn-pa-current-plan *pat-malformed* *pat-snapshots*) :absent)))

(make-event `(defconst *pat-subject-id*
               ',(fn-id-subject-of-payload *pat-relayed*)))
(defconst *pat-subject*
  (fn-record-octets-string (fn-id-text *pat-subject-id*)))
(make-event `(defconst *pat-obligation*
               ',(fn-record-octets-string
                  (fn-id-text
                   (fn-id-obligation-of
                    (fn-record-string-octets
                     "<topic-binding@example.invalid>")
                    *pat-subject-id*)))))
(make-event `(defconst *pat-event*
               ',(fn-pa-authorized-event
                  2 3 4 "<topic-binding@example.invalid>" *pat-relayed*
                  '("fn.test") *pat-obligation* *pat-subject*
                  "gateway-peer-evidence"
                  (fn-charge-for-payload (len *pat-relayed*))
                  *pat-snapshots* *tha-ml-key* :verified :verified
                  (fn-clock-observation 1 841000000000 0 t))))
(assert-event (fn-stxa-p *pat-event*))
(assert-event (fn-stxa-bindsp *pat-event*))
(assert-event (equal (fn-stxa-authored-source *pat-event*)
                     *tha-root-source*))
(assert-event (equal (fn-stxa-keyring-generation *pat-event*) 4))
(assert-event (fn-hsig-article-event-snapshot-bindsp-v1
               *pat-event* *tha-snapshot*))
(assert-event
 (equal (fn-record-payload
         (fn-record-result-record
          (fn-record-decode-exact (fn-stxa-article-record *pat-event*))))
        *pat-relayed*))
(assert-event
 (null (fn-pa-authorized-event
        2 3 4 "<topic-binding@example.invalid>" *pat-relayed*
        '("fn.test") *pat-obligation* *pat-subject*
        "gateway-peer-evidence"
        (fn-charge-for-payload (len *pat-relayed*))
        (cons *pat-revoked* *pat-snapshots*) *tha-ml-key*
        :verified :verified (fn-clock-observation 1 841000000000 0 t))))
