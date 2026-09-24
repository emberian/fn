(in-package "ACL2")
(include-book "../../books/peer-authored-accept")
(include-book "topic-history-authorship-tests")
(include-book "std/testing/must-fail" :dir :system)

(defconst *pat-snapshots* (list *tha-snapshot*))
; D23: a boundary allowlisting the fixture's author (32 octets of 7), as the
; rows of one peer's configuration group spell it.
(defconst *pat-hex-principal*
  "0707070707070707070707070707070707070707070707070707070707070707")
(defconst *pat-peer-rows*
  (list (list "relay" "path-identity" "relay.example" 0)
        (list "relay" "carries-principal" *pat-hex-principal* 0)
        (list "relay" "auth-principal" "ab" 0)))
(defconst *pat-carries* (fn-pa-peer-carried-sources "relay" *pat-peer-rows*))
(assert-event (equal *pat-carries*
                     (list (fn-record-string-octets *pat-hex-principal*))))
(assert-event (fn-pa-carriesp *tha-principal* *pat-carries*))
(assert-event (null (fn-pa-peer-carried-sources "other" *pat-peer-rows*)))
(defconst *pat-relayed*
  (append (tha-line "Path: gateway.example!fn") *tha-received*))
(assert-event (equal (fn-pa-carrier-kind *tha-root-source*) :absent))
(assert-event (equal (fn-pa-current-plan *tha-root-source* *pat-snapshots* nil)
                     :absent))
(assert-event (equal (fn-pa-carrier-kind *pat-relayed*) :present))
(assert-event
 (equal (fn-pa-current-plan *pat-relayed* *pat-snapshots* nil)
        (list :ok *tha-root-source* *tha-principal* *tha-keys*
              *tha-signatures* *tha-snapshot* 4)))

; No B-local enrollment, wrong ordered keys, and a later B-local revocation
; are three different reasons that valid portable bytes cannot be admitted.
(assert-event (equal (fn-pa-current-plan *pat-relayed* nil nil)
                     (list :refused :local-enrollment)))
(assert-event
 (equal (fn-pa-current-plan
         *pat-relayed*
         (list (fn-hsig-keyring-event 1 2 3 4 *tha-principal*
                                      *tha-other-keys*))
         *pat-carries*)
        (list :refused :local-enrollment)))
(make-event `(defconst *pat-revoked*
               ',(fn-hl-revoke-event 2 3 4 5 *tha-principal*
                                     *pat-snapshots*)))
(assert-event (fn-stxk-p *pat-revoked*))
(assert-event
 (equal (fn-pa-current-plan *pat-relayed*
                            (cons *pat-revoked* *pat-snapshots*)
                            *pat-carries*)
        (list :refused :local-enrollment)))

; A present but malformed FN-Authorship cannot downgrade to the legacy path.
(defconst *pat-malformed*
  (append (tha-line "FN-Authorship: !!!") *tha-root-source*))
(assert-event (equal (fn-pa-carrier-kind *pat-malformed*) :present))
(assert-event (equal (fn-pa-current-plan *pat-malformed* *pat-snapshots* nil)
                     (list :refused :carrier)))
(must-fail
 (assert-event
  (equal (fn-pa-current-plan *pat-malformed* *pat-snapshots* nil) :absent)))

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

; ---------------------------------------------------------------------------
; D23, the carried arm.  Witness: a node with no snapshot of the author whose
; delivering boundary lists it carries the article.
(assert-event
 (equal (fn-pa-current-plan *pat-relayed* nil *pat-carries*)
        (list :carried *tha-root-source* *tha-principal* *tha-keys*
              *tha-signatures*)))
; Tooth (the list): the same node without the list refuses, as D02 did.
(must-fail
 (assert-event
  (equal (car (fn-pa-current-plan *pat-relayed* nil nil)) :carried)))
; Tooth (the list names this principal): a list naming another principal.
(defconst *pat-other-carries*
  (list (fn-record-string-octets
         "0808080808080808080808080808080808080808080808080808080808080808")))
(assert-event (equal (fn-pa-current-plan *pat-relayed* nil *pat-other-carries*)
                     (list :refused :local-enrollment)))
(must-fail
 (assert-event
  (equal (car (fn-pa-current-plan *pat-relayed* nil *pat-other-carries*))
         :carried)))
; Tooth (no local snapshot): an enrolled receiver verifies as today even
; when the boundary lists the author, and a revoked or re-keyed principal is
; refused (the two refusals above pass *pat-carries*).
(assert-event
 (equal (fn-pa-current-plan *pat-relayed* *pat-snapshots* *pat-carries*)
        (fn-pa-current-plan *pat-relayed* *pat-snapshots* nil)))
(must-fail
 (assert-event
  (equal (car (fn-pa-current-plan *pat-relayed* *pat-snapshots* *pat-carries*))
         :carried)))
; A malformed carrier is refused whatever the list.
(assert-event (equal (fn-pa-current-plan *pat-malformed* nil *pat-carries*)
                     (list :refused :carrier)))

(make-event `(defconst *pat-carried-event*
               ',(fn-pa-carried-event
                  2 3 4 "<topic-binding@example.invalid>" *pat-relayed*
                  '("fn.test") *pat-obligation* *pat-subject*
                  "gateway-peer-evidence"
                  (fn-charge-for-payload (len *pat-relayed*))
                  nil *pat-carries*
                  (fn-clock-observation 1 841000000000 0 t))))
(assert-event (fn-stxa-p *pat-carried-event*))
(assert-event (fn-hsig-article-event-carried-bindsp *pat-carried-event*))
(assert-event (equal (fn-stxa-keyring-generation *pat-carried-event*) 0))
(assert-event
 (equal (fn-stmt-value (fn-stxe-decode-exact
                        (fn-stxa-verdict-event *pat-carried-event*)))
        (fn-stxe-make 2 3 4 "<topic-binding@example.invalid>" :carried
                      *tha-principal* 0 *fn-hsig-profile-tag*)))
(assert-event
 (equal (fn-record-payload
         (fn-record-result-record
          (fn-record-decode-exact (fn-stxa-article-record *pat-carried-event*))))
        *pat-relayed*))
(assert-event (equal (fn-stxa-authored-source *pat-carried-event*)
                     *tha-root-source*))
; The carried composite never binds as an enrolled one.
(assert-event (not (fn-hsig-article-event-snapshot-bindsp
                    *pat-carried-event* *tha-snapshot*)))
; Tooth (the carried arm): an enrolled receiver builds no carried event.
(assert-event
 (null (fn-pa-carried-event
        2 3 4 "<topic-binding@example.invalid>" *pat-relayed*
        '("fn.test") *pat-obligation* *pat-subject* "gateway-peer-evidence"
        (fn-charge-for-payload (len *pat-relayed*))
        *pat-snapshots* *pat-carries*
        (fn-clock-observation 1 841000000000 0 t))))
(must-fail
 (assert-event
  (fn-pa-carried-event
   2 3 4 "<topic-binding@example.invalid>" *pat-relayed*
   '("fn.test") *pat-obligation* *pat-subject* "gateway-peer-evidence"
   (fn-charge-for-payload (len *pat-relayed*))
   nil nil (fn-clock-observation 1 841000000000 0 t))))
; A composite that claims :verified at generation 0 is no carried record.
(make-event
 `(defconst *pat-forged-verified*
    ',(fn-stxa-make-carried
       2 3 4 0 *fn-hsig-profile-tag*
       (fn-record-string-octets *pat-subject*)
       (fn-stxa-article-record *pat-carried-event*)
       (fn-stxe-encode (fn-stxe-make 2 3 4 "<topic-binding@example.invalid>"
                                     :verified *tha-principal* 0
                                     *fn-hsig-profile-tag*))
       (fn-stxa-authored-source *pat-carried-event*)
       (fn-stxa-authored-id *pat-carried-event*))))
(assert-event (fn-stxa-bindsp *pat-forged-verified*))
(assert-event (not (fn-hsig-article-event-carried-bindsp *pat-forged-verified*)))
(assert-event (not (fn-hsig-article-event-snapshot-bindsp
                    *pat-forged-verified* *tha-snapshot*)))
