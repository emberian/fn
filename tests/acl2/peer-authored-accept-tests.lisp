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

;; ---------------------------------------------------------------------------
;; SPIKE (spike/peering): the revoked arm.  After this node revokes the
;; author, the same enrolled keys give the revoked plan at the tombstone's
;; generation (5), and its event binds as a :revoked composite that replay
;; records only over that tombstone.
(defconst *pat-revoked-snapshots* (cons *pat-revoked* *pat-snapshots*))
(assert-event
 (equal (fn-pa-revoked-plan *pat-relayed* *pat-revoked-snapshots*)
        (list :revoked *tha-root-source* *tha-principal* *tha-keys*
              *tha-signatures* 5)))
; Teeth: no tombstone (enrolled, still active), no snapshot at all, and a
; tombstone over a principal enrolled under other keys give no revoked plan.
(assert-event (null (fn-pa-revoked-plan *pat-relayed* *pat-snapshots*)))
(assert-event (null (fn-pa-revoked-plan *pat-relayed* nil)))
(make-event
 `(defconst *pat-other-enrolled*
    ',(list (fn-hsig-keyring-event 1 2 3 4 *tha-principal* *tha-other-keys*))))
(make-event
 `(defconst *pat-other-revoked*
    ',(fn-hl-revoke-event 2 3 4 5 *tha-principal* *pat-other-enrolled*)))
(assert-event (fn-stxk-p *pat-other-revoked*))
(assert-event (null (fn-pa-revoked-plan
                     *pat-relayed*
                     (cons *pat-other-revoked* *pat-other-enrolled*))))
(must-fail
 (assert-event (fn-pa-revoked-plan *pat-relayed* *pat-snapshots*)))
(make-event `(defconst *pat-revoked-event*
               ',(fn-pa-revoked-event
                  2 3 4 "<topic-binding@example.invalid>" *pat-relayed*
                  '("fn.test") *pat-obligation* *pat-subject*
                  "gateway-peer-evidence"
                  (fn-charge-for-payload (len *pat-relayed*))
                  *pat-revoked-snapshots*
                  (fn-clock-observation 1 841000000000 0 t))))
(assert-event (fn-stxa-p *pat-revoked-event*))
(assert-event (fn-hsig-article-event-revoked-bindsp *pat-revoked-event*))
(assert-event (not (fn-hsig-article-event-carried-bindsp *pat-revoked-event*)))
(assert-event (not (fn-hsig-article-event-revoked-bindsp *pat-carried-event*)))
(assert-event (equal (fn-stxa-keyring-generation *pat-revoked-event*) 5))
(assert-event
 (equal (fn-stmt-value (fn-stxe-decode-exact
                        (fn-stxa-verdict-event *pat-revoked-event*)))
        (fn-stxe-make 2 3 4 "<topic-binding@example.invalid>" :revoked
                      *tha-principal* 5 *fn-hsig-profile-tag*)))
(assert-event
 (equal (fn-stx-verified-item
         (fn-stx-make-verdict :revoked *tha-principal* 5))
        (append *fn-stx-token-revoked*
                (append '(32) (append (fn-stx-hex-octets *tha-principal*)
                                      (fn-stx-keyring-suffix 5))))))
(must-fail
 (assert-event
  (fn-pa-revoked-event
   2 3 4 "<topic-binding@example.invalid>" *pat-relayed*
   '("fn.test") *pat-obligation* *pat-subject* "gateway-peer-evidence"
   (fn-charge-for-payload (len *pat-relayed*))
   *pat-snapshots* (fn-clock-observation 1 841000000000 0 t))))

;; SPIKE (spike/peering): the opaque-carriage budget and the refusal class.
(defconst *pat-budget-rows*
  (append *pat-peer-rows*
          (list (list "relay" "carried-budget-octets" "1000" 0)
                (list "relay" "carried-budget-count" "2" 0))))
(assert-event (equal (fn-pa-peer-carried-budget "relay" *pat-budget-rows*)
                     (list 1000 2)))
(assert-event (equal (fn-pa-peer-carried-budget "relay" *pat-peer-rows*)
                     (list nil nil)))
(assert-event (equal (fn-pa-carried-budget-decision (list 1000 2) (list 0 0) 400)
                     :within))
(assert-event (equal (fn-pa-carried-budget-decision (list 1000 2) (list 400 1) 600)
                     :within))
; Teeth: each bound refuses by its own name, and no budget carries nothing.
(assert-event (equal (fn-pa-carried-budget-decision (list 1000 2) (list 400 1) 601)
                     (list :refused :carried-octets-exhausted)))
(assert-event (equal (fn-pa-carried-budget-decision (list 1000 2) (list 400 2) 1)
                     (list :refused :carried-count-exhausted)))
(assert-event (equal (fn-pa-carried-budget-decision (list nil nil) (list 0 0) 1)
                     (list :refused :carried-budget-unset)))
(must-fail
 (assert-event (equal (fn-pa-carried-budget-decision (list 1000 2) (list 400 1) 601)
                      :within)))
; The three unverified outcomes stay distinct in the decision.
(assert-event (equal (fn-pa-signed-refusal-class *pat-relayed* nil nil nil)
                     :no-local-binding))
(assert-event (equal (fn-pa-signed-refusal-class *pat-relayed* *pat-snapshots* nil
                                                 :failed)
                     :signature-failed))
(assert-event (equal (fn-pa-signed-refusal-class *pat-malformed* nil nil nil)
                     :malformed))
(assert-event (null (fn-pa-signed-refusal-class *tha-root-source* nil nil :failed)))
(assert-event (null (fn-pa-signed-refusal-class *pat-relayed* *pat-snapshots* nil nil)))
