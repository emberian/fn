; Teeth for books/owner-intent-carried.lisp.
(in-package "ACL2")
(include-book "../../books/owner-intent-carried")
(include-book "std/testing/must-fail" :dir :system)
(include-book "owner-tests")

; Every function the host calls is guard-verified.
(assert-event
 (equal (list (symbol-class 'fn-icar-carry-of (w state))
              (symbol-class 'fn-icar-intent-id (w state))
              (symbol-class 'fn-icar-submission-intent (w state))
              (symbol-class 'fn-icar-submission-resolution-records (w state)))
        '(:common-lisp-compliant :common-lisp-compliant
          :common-lisp-compliant :common-lisp-compliant)))

; The digests run through their attachments (books/crypto-attach), which a
; defconst may not call, so the values that contain one are thunks.

; Reachable witness: owner-tests' *own-control-fed-taken* is a control
; submission taken by fn-own-take-submission into an owner whose feed table
; has one outbound peer; its intent is :ready with one record.
(defconst *icar-t-sub* (fn-own-inflight *own-control-fed-taken*))
(defun icar-t-carry () (fn-icar-carry-of *icar-t-sub*))
(assert-event (fn-icar-carryp (icar-t-carry)))
(assert-event (fn-feed-namep (cadr (icar-t-carry))))
(assert-event (equal (cadr (icar-t-carry))
                     (fn-own-feed-intent-id *own-control-msgid*
                                            *own-control-source*)))

(defun icar-t-intent ()
  (fn-icar-submission-intent *own-control-fed-taken* (icar-t-carry)
                             *own-control-evidence* 1 3))
(assert-event (equal (car (icar-t-intent)) :ready))
(assert-event (equal (len (cdr (icar-t-intent))) 1))
(assert-event (equal (icar-t-intent)
                     (cons (fn-own-submission-intent-result
                            *own-control-fed-taken* *own-control-evidence* 1 3)
                           (own-control-intents))))

; The resolution over the same carry: commit after the consumed completion,
; abort on a known duplicate, nothing on an uncertain outcome.  The in-flight
; submission of *own-control-fed-done* is the one the take built.
(assert-event (equal (fn-own-inflight *own-control-fed-done*) *icar-t-sub*))
(assert-event (equal (fn-icar-submission-resolution-records
                      *own-control-fed-done* (icar-t-carry) :durable
                      *own-control-evidence* 1 3)
                     (own-control-commits)))
(assert-event (equal (fn-icar-submission-resolution-records
                      *own-control-fed-taken* (icar-t-carry) :duplicate
                      *own-control-evidence* 1 3)
                     (own-control-aborts)))
(assert-event (null (fn-icar-submission-resolution-records
                     *own-control-fed-taken* (icar-t-carry) :uncertain
                     *own-control-evidence* 1 3)))

; A stale carry (a valid carry of another submission, owner-tests' served
; POST taken in *own-taken*) and the empty carry the host starts with fall
; back to the digest and still give the reference.
(defun icar-t-stale () (fn-icar-carry-of (fn-own-inflight *own-taken*)))
(assert-event (fn-icar-carryp (icar-t-stale)))
(assert-event (not (equal (car (icar-t-stale)) *icar-t-sub*)))
(assert-event (equal (fn-icar-submission-intent *own-control-fed-taken*
                                                (icar-t-stale)
                                                *own-control-evidence* 1 3)
                     (icar-t-intent)))
(assert-event (equal (fn-icar-submission-intent *own-control-fed-taken* nil
                                                *own-control-evidence* 1 3)
                     (icar-t-intent)))

; Teeth.  The one hypothesis of every theorem is fn-icar-carryp.  A carry
; that names the in-flight submission itself (so the atom clause and the
; submission match do not separate it) but holds another submission's
; identity violates it, and then every reader differs from its reference.
(defun icar-t-forged () (list* *icar-t-sub* (cadr (icar-t-stale))
                               (cddr (icar-t-carry))))
(assert-event (not (fn-icar-carryp (icar-t-forged))))
(assert-event (fn-feed-namep (cadr (icar-t-forged))))
(assert-event (not (equal (fn-icar-intent-id *icar-t-sub* (icar-t-forged))
                          (fn-own-feed-intent-id
                           (fn-own-sub-msgid *icar-t-sub*)
                           (fn-own-sub-octets *icar-t-sub*)))))
(assert-event (not (equal (fn-icar-submission-intent *own-control-fed-taken*
                                                     (icar-t-forged)
                                                     *own-control-evidence* 1 3)
                          (icar-t-intent))))
(assert-event (not (equal (fn-icar-submission-resolution-records
                           *own-control-fed-done* (icar-t-forged) :durable
                           *own-control-evidence* 1 3)
                          (own-control-commits))))
; A carry whose identity is not a feed name at all refuses the intent.
(assert-event (equal (car (fn-icar-submission-intent
                           *own-control-fed-taken*
                           (list* *icar-t-sub* nil (cddr (icar-t-carry)))
                           *own-control-evidence* 1 3))
                     :refused))

; The Path (PKT-113).  The carry holds the Path the take parsed; the source
; has no Path header, so it is nil.  A carry whose identity is right but
; whose Path names the outbound peer's path identity violates
; fn-icar-carryp, and the feed targets then drop the peer: the intent has
; no records where the reference has one.
(assert-event (equal (cddr (icar-t-carry))
                     (fn-own-feed-path-of *own-control-source*)))
(assert-event (equal (fn-icar-submission-targets *own-control-fed-taken* (icar-t-carry))
                     (fn-own-submission-targets *own-control-fed-taken*)))
(assert-event (consp (fn-own-submission-targets *own-control-fed-taken*)))
(defun icar-t-forged-path ()
  (list* *icar-t-sub* (cadr (icar-t-carry))
         (fn-nntp-string-octets "out.example!not-for-mail")))
(assert-event (not (fn-icar-carryp (icar-t-forged-path))))
(assert-event (not (equal (fn-icar-submission-targets *own-control-fed-taken*
                                                      (icar-t-forged-path))
                          (fn-own-submission-targets *own-control-fed-taken*))))
(assert-event (not (equal (fn-icar-submission-intent *own-control-fed-taken*
                                                     (icar-t-forged-path)
                                                     *own-control-evidence* 1 3)
                          (icar-t-intent))))
; The same refutations over constants the prover evaluates (the identity
; slot is 0: the Path readers never read it).
(defconst *icar-t-forged-path-carry*
  (list* *icar-t-sub* 0 (fn-nntp-string-octets "out.example!not-for-mail")))
(must-fail
 (defthm icar-t-path-without-carryp
   (equal (fn-icar-path *icar-t-sub* *icar-t-forged-path-carry*)
          (fn-own-feed-path-of (fn-own-sub-octets *icar-t-sub*)))))
(must-fail
 (defthm icar-t-targets-without-carryp
   (equal (fn-icar-submission-targets *own-control-fed-taken*
                                      *icar-t-forged-path-carry*)
          (fn-own-submission-targets *own-control-fed-taken*))))
(must-fail
 (defthm icar-t-intent-id-without-carryp
   (equal (fn-icar-intent-id sub carry)
          (fn-own-feed-intent-id (fn-own-sub-msgid sub)
                                 (fn-own-sub-octets sub)))))
(must-fail
 (defthm icar-t-intent-without-carryp
   (equal (fn-icar-submission-intent o carry evidence generation txid)
          (cons (fn-own-submission-intent-result o evidence generation txid)
                (fn-own-submission-intent-records o evidence generation txid)))))
(must-fail
 (defthm icar-t-resolution-without-carryp
   (equal (fn-icar-submission-resolution-records
           o carry word evidence generation txid)
          (fn-own-submission-resolution-records
           o word evidence generation txid))))

; PKT-400 (PRF-163): the host's carried intent (fn-icar-submission-targets,
; what fn-owner-submission-intent calls) names the target a cancel's
; Newsgroups selects: "out" (fn.*) for a cancel filed in control.cancel whose
; Newsgroups is fn.letters (tests/acl2/owner-tests.lisp *own-cancel-a*).
(assert-event (equal (fn-icar-submission-targets
                      *own-cancel-a* (fn-icar-carry-of (fn-own-inflight *own-cancel-a*)))
                     '("out")))
