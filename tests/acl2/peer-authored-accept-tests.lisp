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
(assert-event (equal (fn-pa-current-plan *tha-root-source* *pat-snapshots* nil nil)
                     :absent))
(assert-event (equal (fn-pa-carrier-kind *pat-relayed*) :present))
(assert-event
 (equal (fn-pa-current-plan *pat-relayed* *pat-snapshots* nil nil)
        (list :ok *tha-root-source* *tha-principal* *tha-keys*
              *tha-signatures* *tha-snapshot* 4)))

; No B-local enrollment, wrong ordered keys, and a later B-local revocation
; are three different reasons that valid portable bytes cannot be admitted.
(assert-event (equal (fn-pa-current-plan *pat-relayed* nil nil nil)
                     (list :refused :local-enrollment)))
(assert-event
 (equal (fn-pa-current-plan
         *pat-relayed*
         (list (fn-hsig-keyring-event 1 2 3 4 *tha-principal*
                                      *tha-other-keys*))
         *pat-carries* nil)
        (list :refused :local-enrollment)))
(make-event `(defconst *pat-revoked*
               ',(fn-hl-revoke-event 2 3 4 5 *tha-principal*
                                     *pat-snapshots*)))
(assert-event (fn-stxk-p *pat-revoked*))
(assert-event
 (equal (fn-pa-current-plan *pat-relayed*
                            (cons *pat-revoked* *pat-snapshots*)
                            *pat-carries* nil)
        (list :refused :local-enrollment)))

; A present but malformed FN-Authorship cannot downgrade to the legacy path.
(defconst *pat-malformed*
  (append (tha-line "FN-Authorship: !!!") *tha-root-source*))
(assert-event (equal (fn-pa-carrier-kind *pat-malformed*) :present))
(assert-event (equal (fn-pa-current-plan *pat-malformed* *pat-snapshots* nil nil)
                     (list :refused :carrier)))
(must-fail
 (assert-event
  (equal (fn-pa-current-plan *pat-malformed* *pat-snapshots* nil nil) :absent)))

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
 (equal (fn-pa-current-plan *pat-relayed* nil *pat-carries* nil)
        (list :carried *tha-root-source* *tha-principal* *tha-keys*
              *tha-signatures*)))
; Tooth (the list): the same node without the list refuses, as D02 did.
(must-fail
 (assert-event
  (equal (car (fn-pa-current-plan *pat-relayed* nil nil nil)) :carried)))
; Tooth (the list names this principal): a list naming another principal.
(defconst *pat-other-carries*
  (list (fn-record-string-octets
         "0808080808080808080808080808080808080808080808080808080808080808")))
(assert-event (equal (fn-pa-current-plan *pat-relayed* nil *pat-other-carries* nil)
                     (list :refused :local-enrollment)))
(must-fail
 (assert-event
  (equal (car (fn-pa-current-plan *pat-relayed* nil *pat-other-carries* nil))
         :carried)))
; Tooth (no local snapshot): an enrolled receiver verifies as today even
; when the boundary lists the author, and a revoked or re-keyed principal is
; refused (the two refusals above pass *pat-carries*).
(assert-event
 (equal (fn-pa-current-plan *pat-relayed* *pat-snapshots* *pat-carries* nil)
        (fn-pa-current-plan *pat-relayed* *pat-snapshots* nil nil)))
(must-fail
 (assert-event
  (equal (car (fn-pa-current-plan *pat-relayed* *pat-snapshots* *pat-carries* nil))
         :carried)))
; A malformed carrier is refused whatever the list.
(assert-event (equal (fn-pa-current-plan *pat-malformed* nil *pat-carries* nil)
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

; ---------------------------------------------------------------------------
; PRF-098, the revoked arm.  *pat-revoked* is the principal's tombstone at
; generation 5 over its enrollment at 4 (*pat-snapshots*).
(defconst *pat-after-revocation* (cons *pat-revoked* *pat-snapshots*))
; Witness: on NNTP transit the once-enrolled keys give :revoked at 5.
(assert-event
 (equal (fn-pa-current-plan *pat-relayed* *pat-after-revocation* nil t)
        (list :revoked *tha-root-source* *tha-principal* *tha-keys*
              *tha-signatures* *pat-revoked* 5)))
; Tooth (transit): every other path refuses :local-enrollment.
(must-fail
 (assert-event
  (equal (car (fn-pa-current-plan *pat-relayed* *pat-after-revocation* nil nil))
         :revoked)))
; Tooth (the tombstone): before the revocation the same carrier is :ok.
(must-fail
 (assert-event
  (equal (car (fn-pa-current-plan *pat-relayed* *pat-snapshots* nil t))
         :revoked)))
; Tooth (keys once enrolled): the principal enrolled under OTHER keys and
; then revoked; the carrier's keys were never enrolled here, so it is refused.
(make-event `(defconst *pat-other-enrolled*
               ',(fn-hsig-keyring-event 1 2 3 4 *tha-principal* *tha-other-keys*)))
(make-event `(defconst *pat-other-revoked*
               ',(fn-hl-revoke-event 2 3 4 5 *tha-principal*
                                     (list *pat-other-enrolled*))))
(assert-event (fn-stxk-p *pat-other-revoked*))
(assert-event
 (equal (fn-pa-current-plan *pat-relayed*
                            (list *pat-other-revoked* *pat-other-enrolled*) nil t)
        (list :refused :local-enrollment)))
(must-fail
 (assert-event
  (equal (car (fn-pa-current-plan *pat-relayed*
                                  (list *pat-other-revoked* *pat-other-enrolled*)
                                  nil t))
         :revoked)))

; fn-pa-no-ok-plan-for-a-revoked-principal.  Tooth (the principal is the
; carrier's): another principal (8s) enrolled and revoked leaves this
; carrier's plan :ok.
(make-event `(defconst *pat-q-enrolled*
               ',(fn-hl-enroll-event 3 4 5 5 *tha-other-principal* *tha-other-keys*
                                     *pat-snapshots*)))
(make-event `(defconst *pat-q-revoked*
               ',(fn-hl-revoke-event 4 5 6 6 *tha-other-principal*
                                     (cons *pat-q-enrolled* *pat-snapshots*))))
(defconst *pat-q-history* (list* *pat-q-revoked* *pat-q-enrolled* *pat-snapshots*))
(assert-event (fn-stxk-p *pat-q-revoked*))
(assert-event
 (equal (fn-stxk-profile (fn-hl-current-for-principal *tha-other-principal*
                                                      *pat-q-history*))
        *fn-hl-revoked-profile*))
(must-fail
 (assert-event
  (not (equal (car (fn-pa-current-plan *pat-relayed* *pat-q-history* nil t))
              :ok))))

; The revoked event: both observations verified give the composite replay's
; revoked branch admits; either refused gives nothing.
(make-event `(defconst *pat-revoked-event*
               ',(fn-pa-revoked-event
                  2 3 4 "<topic-binding@example.invalid>" *pat-relayed*
                  '("fn.test") *pat-obligation* *pat-subject*
                  "gateway-peer-evidence"
                  (fn-charge-for-payload (len *pat-relayed*))
                  *pat-after-revocation* *tha-ml-key* :verified :verified
                  (fn-clock-observation 1 841000000000 0 t))))
(assert-event (fn-stxa-p *pat-revoked-event*))
(assert-event (fn-hsig-article-event-revoked-bindsp *pat-revoked-event*))
(assert-event (equal (fn-stxa-keyring-generation *pat-revoked-event*) 5))
(assert-event
 (equal (fn-stxe-token (fn-stmt-value (fn-stxe-decode-exact
                                        (fn-stxa-verdict-event *pat-revoked-event*))))
        :revoked))
(assert-event
 (fn-hsig-revoked-tombstone-bindsp
  (fn-stmt-value (fn-stxe-decode-exact (fn-stxa-verdict-event *pat-revoked-event*)))
  (fn-hsig-article-event-carrier-keys *pat-revoked-event*)
  *pat-after-revocation*))
; Replay's revoked binding needs a tombstone of exactly this principal at
; that generation: at the snapshots without the tombstone it fails.
(must-fail
 (assert-event
  (fn-hsig-revoked-tombstone-bindsp
   (fn-stmt-value (fn-stxe-decode-exact (fn-stxa-verdict-event *pat-revoked-event*)))
   (fn-hsig-article-event-carrier-keys *pat-revoked-event*)
   *pat-snapshots*)))
; ...and at another principal's tombstone at 5 it fails too.
(make-event `(defconst *pat-q-at-5*
               ',(fn-hl-revoke-event 2 3 4 5 *tha-other-principal*
                                     (list (fn-hsig-keyring-event
                                            1 2 3 4 *tha-other-principal*
                                            *tha-keys*)))))
(must-fail
 (assert-event
  (fn-hsig-revoked-tombstone-bindsp
   (fn-stmt-value (fn-stxe-decode-exact (fn-stxa-verdict-event *pat-revoked-event*)))
   (fn-hsig-article-event-carrier-keys *pat-revoked-event*)
   (list *pat-q-at-5* (fn-hsig-keyring-event 1 2 3 4 *tha-other-principal*
                                             *tha-keys*)))))
; Tooth (both observations): either refused gives no composite.
(must-fail
 (assert-event
  (fn-pa-revoked-event
   2 3 4 "<topic-binding@example.invalid>" *pat-relayed*
   '("fn.test") *pat-obligation* *pat-subject* "gateway-peer-evidence"
   (fn-charge-for-payload (len *pat-relayed*))
   *pat-after-revocation* *tha-ml-key* :refused :verified
   (fn-clock-observation 1 841000000000 0 t))))
(must-fail
 (assert-event
  (fn-pa-revoked-event
   2 3 4 "<topic-binding@example.invalid>" *pat-relayed*
   '("fn.test") *pat-obligation* *pat-subject* "gateway-peer-evidence"
   (fn-charge-for-payload (len *pat-relayed*))
   *pat-after-revocation* *tha-ml-key* :verified :refused
   (fn-clock-observation 1 841000000000 0 t))))
; The reader never sees `verified' for it: the item begins `revoked'.
(assert-event
 (equal (take 7 (fn-stx-verified-item
                 (fn-stx-make-verdict :revoked *tha-principal* 5)))
        (fn-record-string-octets "revoked")))
(must-fail
 (assert-event
  (equal (car (fn-stx-verified-item
               (fn-stx-make-verdict :revoked *tha-principal* 5)))
         118)))

;; PKT-473 (PRF-184): fn-pa-served-post-word.  The durable word with the
;; executor's detail names the refused key change; every other pair is the
;; served word.
(assert-event (equal (fn-pa-served-post-word :durable :key-change-refused)
                     :durable-key-change-refused))
(assert-event (equal (fn-pa-served-post-word :durable nil) :durable))
(assert-event (equal (fn-pa-served-post-word :durable :carried) :durable))
(assert-event (equal (fn-pa-served-post-word :refused :key-change-refused) :refused))
(assert-event (equal (fn-pa-served-post-word :refused :signature) :signature))
;; The hypothesis (WORD is not the new word itself): with it dropped the
;; word is :durable-key-change-refused while WORD is not :durable.
(must-fail
 (assert-event
  (iff (equal (fn-pa-served-post-word :durable-key-change-refused nil)
              :durable-key-change-refused)
       (and (equal :durable-key-change-refused :durable)
            (equal nil :key-change-refused)))))
