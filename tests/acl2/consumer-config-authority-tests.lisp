(in-package "ACL2")
(include-book "../../books/owner-authority-proposal-state")
(include-book "consumer-account-adoption-tests")

(defconst *ccat-record*
  (fn-cfg-record-make 0 6 1 (list (fn-cfg-set-capacity 20)) *fn-cfg-default-stamp*))
(defconst *ccat-approved* (fn-cca-preflight *caat-first* nil))
(defconst *ccat-proposal* (fn-cca-proposal 7 *caat-first* *ccat-record* *ccat-approved*))
;@positive fn-cca-consume-keeps-approved-result
(assert-event
 (and (fn-cfg-recordp *ccat-record*) (fn-cp-statep *caat-first*)
      (natp 7) *ccat-record* (eq (fn-cp-nth 0 *ccat-approved*) :ok)
      (equal (fn-cca-consume *ccat-proposal* 7 *caat-first* *ccat-record*)
             (list :ok (fn-cp-nth 1 *ccat-approved*) (fn-cp-nth 2 *ccat-approved*)))
      (equal (fn-cp-nth 1 (fn-cp-nth 6 (fn-cp-nth 1 *ccat-approved*))) 2)
      (equal (fn-cp-nth 4 (fn-cp-nth 6 (fn-cp-nth 1 *ccat-approved*)))
             (fn-cp-nth 4 (fn-cp-nth 6 *caat-first*)))))

;@hypothesis-removal fn-cca-consume-keeps-approved-result epoch-natural
(assert-event
 (and (not (natp -1)) *ccat-record* (eq (fn-cp-nth 0 *ccat-approved*) :ok)
      (not (equal (fn-cca-consume (fn-cca-proposal -1 *caat-first* *ccat-record* *ccat-approved*)
                                  -1 *caat-first* *ccat-record*)
                   (list :ok (fn-cp-nth 1 *ccat-approved*) (fn-cp-nth 2 *ccat-approved*))))))
;@hypothesis-removal fn-cca-consume-keeps-approved-result actual-record
(assert-event
 (and (natp 7) (not nil) (eq (fn-cp-nth 0 *ccat-approved*) :ok)
      (not (equal (fn-cca-consume (fn-cca-proposal 7 *caat-first* nil *ccat-approved*)
                                  7 *caat-first* nil)
                   (list :ok (fn-cp-nth 1 *ccat-approved*) (fn-cp-nth 2 *ccat-approved*))))))
;@hypothesis-removal fn-cca-consume-keeps-approved-result approved
(assert-event
 (let ((approved '(:refused :authority-revision-exhausted)))
   (and (natp 7) *ccat-record* (not (eq (fn-cp-nth 0 approved) :ok))
        (not (equal (fn-cca-consume (fn-cca-proposal 7 *caat-first* *ccat-record* approved)
                                    7 *caat-first* *ccat-record*)
                     (list :ok (fn-cp-nth 1 approved) (fn-cp-nth 2 approved)))))))

;@positive fn-cca-consume-epoch-mismatch-requires-recovery
(assert-event
 (and (natp 7) *ccat-record* (eq (fn-cp-nth 0 *ccat-approved*) :ok)
      (not (equal 8 7))
      (equal (fn-cca-consume *ccat-proposal* 8 *caat-first* *ccat-record*)
             '(:recovery-required :authority-proposal))))
;@hypothesis-removal fn-cca-consume-epoch-mismatch-requires-recovery mismatch
(assert-event
 (and (natp 7) *ccat-record* (eq (fn-cp-nth 0 *ccat-approved*) :ok)
      (equal 7 7)
      (not (equal (fn-cca-consume *ccat-proposal* 7 *caat-first* *ccat-record*)
                   '(:recovery-required :authority-proposal)))))

; Other carried scalar lineage mismatches require recovery after persistence.
(assert-event
 (and (equal (fn-cca-consume *ccat-proposal* 7 *caat-first*
                (fn-cfg-record-make 1 6 1 (list (fn-cfg-set-capacity 20)) *fn-cfg-default-stamp*))
             '(:recovery-required :authority-proposal))
      (equal (fn-cca-consume *ccat-proposal* 7 (fn-cp-nth 1 *ccat-approved*) *ccat-record*)
             '(:recovery-required :authority-proposal))))

; Typed active exhaustion is refused during the prewrite call, and cannot
; construct a consumable saved proposal.
(defconst *ccat-exhausted*
  (fn-carv-revision-state *caat-first* *fn-cbor-max-uint*))
(assert-event
 (and (fn-cp-statep *ccat-exhausted*)
      (equal (fn-cca-preflight *ccat-exhausted* nil)
             '(:refused :authority-revision-exhausted))
      (null (fn-cca-proposal 7 *ccat-exhausted* *ccat-record*
                             (fn-cca-preflight *ccat-exhausted* nil)))))

; Corrupted-producer witness: scalar coordinates do NOT prove exact record
; payload identity. The actual immutable staged-object relation is owed.
(defconst *ccat-same-coords-different-payload*
  (fn-cfg-record-make 0 6 1 (list (fn-cfg-set-capacity 21)) *fn-cfg-default-stamp*))
(assert-event
 (and (not (equal *ccat-record* *ccat-same-coords-different-payload*))
      (equal (fn-cca-coordinates *ccat-record*)
             (fn-cca-coordinates *ccat-same-coords-different-payload*))
      (fn-cca-matchesp *ccat-proposal* 7 *caat-first* *ccat-same-coords-different-payload*)))

; Actual STATE capture/consume/clear: a repeated completion cannot use the
; same proposal, and neither successful nor mismatched consume leaves it live.
(make-event
 (let ((state (fn-owner-authority-proposal-capture
               7 *caat-first* *ccat-record* *ccat-approved* state)))
   (mv-let (one state)
     (fn-owner-authority-proposal-consume 7 *caat-first* *ccat-record* state)
     (if (or (not (equal one *ccat-approved*))
             (fn-owner-authority-proposal state))
         (er soft 'config-authority-tests "saved proposal did not consume and clear")
       (mv-let (again state)
         (fn-owner-authority-proposal-consume 7 *caat-first* *ccat-record* state)
         (if (not (equal again '(:recovery-required :authority-proposal)))
             (er soft 'config-authority-tests "proposal reused after completion")
           (value '(assert-event t))))))))
