; Teeth for books/owner-prepare-served.lisp and
; books/owner-prepare-served-ocl.lisp (lane prepare-served, PKT-827 (d)): the
; served decision inside the prepare the host calls, the carried owner
; invariant across the retention prepare, the deferred record's order, the
; known abort and the configuration un-stage.  The witnesses are
; owner-log-ocl-tests' configured owner, its retired-group owner and its
; stale staged request, run through the host's own entries.
(in-package "ACL2")
(include-book "../../books/owner-prepare-served-ocl")
(include-book "owner-log-ocl-tests")
(include-book "std/testing/must-fail" :dir :system)

(defun pst-carry (oc)
  ; The carry fn-owner-prepare-buffer passes: fn-prc-refresh of the global
  ; (NIL before the first POST) at the owner Store's retention ledger.
  (fn-prc-refresh nil (fn-node-retention (fn-sn-node (lgt-store oc)))))

; -----------------------------------------------------------------------------
; fn-psrv-prepare-preserves-invariant.  Reachable positive witness: at
; :reserved the article's group fn.letters is served; the host's prepare
; stages it (it is fn-prc-sbud-prepare there) and carries the invariant.
(defconst *pst-prepared* (fn-psrv-prepare *lgt-reserved* *acar-t-record* 1000000
                                          (pst-carry *lgt-reserved*)))
(assert-event (fn-lgoc-invariantp *lgt-reserved*))
(assert-event (fn-prc-carryp (pst-carry *lgt-reserved*)))
(assert-event (fn-scar-view-indexedp (fn-ocfg-owner *lgt-reserved*)))
(assert-event (fn-ceis-indexedp (fn-sbud-oc-store *lgt-reserved*)))
(assert-event (fn-psrv-event-servedp (fn-ocfg-config *lgt-reserved*) *acar-t-record*))
(assert-event (equal *pst-prepared* *lgt-prepared*))
(assert-event (equal (lgt-phase *pst-prepared*) :record-staged))
(assert-event (fn-lgoc-invariantp *pst-prepared*))

; THE RETIRED-GROUP WITNESS, refused by name.  control-quanta-2's
; *lgt-r-prepared*: fn.letters retired by a live completion (still in the
; Store's allocation domain), the owner carrying the invariant; the old
; prepare (fn-sbud-prepare / fn-prc-sbud-prepare, no served test) staged the
; article and broke fn-ocl-relation.  The host's prepare now leaves the
; owner unchanged, the invariant holds, and the word is :refused.
(defconst *pst-r-prepared* (fn-psrv-prepare *lgt-r-reserved* *acar-t-record* 1000000
                                            (pst-carry *lgt-r-reserved*)))
(assert-event (fn-lgoc-invariantp *lgt-r-reserved*))
(assert-event (fn-prc-carryp (pst-carry *lgt-r-reserved*)))
(assert-event (fn-scar-view-indexedp (fn-ocfg-owner *lgt-r-reserved*)))
(assert-event (fn-ceis-indexedp (fn-sbud-oc-store *lgt-r-reserved*)))
(assert-event (not (fn-psrv-event-servedp (fn-ocfg-config *lgt-r-reserved*) *acar-t-record*)))
(assert-event (equal *pst-r-prepared* *lgt-r-reserved*))
(assert-event (fn-lgoc-invariantp *pst-r-prepared*))
(assert-event (equal (fn-psrv-refusal-kind *lgt-r-reserved* *acar-t-record* 1000000) :refused))
; The prepare without the served test still breaks it (the finding).
(assert-event (not (fn-lgoc-invariantp
                    (fn-prc-sbud-prepare *lgt-r-reserved* *acar-t-record* 1000000
                                         (pst-carry *lgt-r-reserved*)))))
; Hypothesis fn-lgoc-invariantp (corrupted-state witness): the topic counter
; off at :reserved; every other hypothesis holds; the staged article's topic
; step faults and the conclusion fails.
(assert-event (fn-prc-carryp (pst-carry *lgt-bad-reserved*)))
(assert-event (fn-scar-view-indexedp (fn-ocfg-owner *lgt-bad-reserved*)))
(assert-event (fn-ceis-indexedp (fn-sbud-oc-store *lgt-bad-reserved*)))
(assert-event (not (fn-lgoc-invariantp *lgt-bad-reserved*)))
(assert-event (not (fn-lgoc-invariantp
                    (fn-psrv-prepare *lgt-bad-reserved* *acar-t-record* 1000000
                                     (pst-carry *lgt-bad-reserved*)))))
; -----------------------------------------------------------------------------
; fn-psrv-prepare-retention-preserves-invariant and the deferred order.
; Reachable positive witness: the retention event the host's
; fn-owner-prepare-retention builds at :reserved (an undertaking of one
; obligation) is staged by (:store (:prepare-retention E)) and the owner
; carries the invariant; the log route's order step publishes it (a
; deferred record: control-quanta-2's order theorem named the article only)
; and the owner reaches :completing carrying the invariant; the finish
; carries it back to :ready.
(defun pst-retention-event (oc)
  (let* ((s (lgt-store oc))
         (txid (fn-state-next-txid (fn-node-acceptance (fn-sn-node s)))))
    (fn-store-retention-event-make :undertake (fn-sn-identity-next s) txid txid
                                   "<obligation-1@fn.test>" "<subject-1@fn.test>"
                                   "evidence" 1)))
(defconst *pst-ret-event* (pst-retention-event *lgt-reserved*))
(defconst *pst-ret-staged*
  (in-arena-acar-t-ocfg-run *sr-arena* *lgt-reserved* (list (list :store (list :prepare-retention *pst-ret-event*)))))
(assert-event (fn-store-retention-event-p *pst-ret-event*))
(assert-event (equal (lgt-phase *pst-ret-staged*) :record-staged))
(assert-event (equal (fn-sf-record-candidate (fn-sn-files (lgt-store *pst-ret-staged*)))
                     *pst-ret-event*))
(assert-event (fn-lgoc-invariantp *pst-ret-staged*))
(defconst *pst-ret-ordered* (fn-olr-ocfg-order *pst-ret-staged*))
(assert-event (not (fn-lgoc-article-stagedp (lgt-store *pst-ret-staged*))))
(assert-event (equal (lgt-phase *pst-ret-ordered*) :completing))
(assert-event (equal (len (fn-sf-records (fn-sn-files (lgt-store *pst-ret-ordered*)))) 3))
(assert-event (fn-lgoc-invariantp *pst-ret-ordered*))
; Hypothesis fn-lgoc-invariantp (corrupted-state witness): the topic counter
; off at :reserved; the retention prepare (which does not read the topic
; prefix) stages the event, and the companion fails.
(defconst *pst-bad-ret-staged*
  (in-arena-acar-t-ocfg-run *sr-arena* *lgt-bad-reserved* (list (list :store (list :prepare-retention *pst-ret-event*)))))
(assert-event (not (fn-lgoc-invariantp *lgt-bad-reserved*)))
(assert-event (equal (lgt-phase *pst-bad-ret-staged*) :record-staged))
(assert-event (not (fn-lgoc-invariantp *pst-bad-ret-staged*)))
; fn-psrv-log-order-preserves-invariant without the invariant: the corrupted
; staged retention, ordered, is not fn-ocl-relation.
(assert-event (not (fn-ocl-relation (fn-olr-ocfg-order *pst-bad-ret-staged*))))

; -----------------------------------------------------------------------------
; fn-psrv-known-abort-preserves-invariant.  Reachable positive witnesses: the
; staged article and the staged retention event, each known-aborted (the
; host's fn-owner-known-abort after a pre-publication Store refusal), reach
; :ready one transaction on and carry the invariant.
(defconst *pst-art-aborted*
  (in-arena-acar-t-ocfg-run *sr-arena* *pst-prepared* (list (list :store (list :known-abort)))))
(defconst *pst-ret-aborted*
  (in-arena-acar-t-ocfg-run *sr-arena* *pst-ret-staged* (list (list :store (list :known-abort)))))
(assert-event (equal (lgt-phase *pst-art-aborted*) :ready))
(assert-event (fn-lgoc-invariantp *pst-art-aborted*))
(assert-event (equal (lgt-phase *pst-ret-aborted*) :ready))
(assert-event (fn-lgoc-invariantp *pst-ret-aborted*))
(assert-event (equal (fn-sf-records (fn-sn-files (lgt-store *pst-ret-aborted*)))
                     (fn-sf-records (fn-sn-files (lgt-store *lgt-reserved*)))))
; Hypothesis fn-lgoc-invariantp (corrupted-state witness): the corrupted
; staged retention, known-aborted, does not carry the invariant.
(assert-event (not (fn-lgoc-invariantp
                    (in-arena-acar-t-ocfg-run *sr-arena* *pst-bad-ret-staged* (list (list :store (list :known-abort)))))))

; -----------------------------------------------------------------------------
; fn-psrv-unstage-preserves-invariant.  Reachable witness: control-quanta-2's
; *lgt-stale* (a retirement staged against a Store whose frontier the
; refused reservation moved): the invariant holds and the authorization
; refuses.  Before the un-stage the staged record is the configuration lock:
; the owner refuses :begin.  The un-stage keeps the invariant and the owner,
; drops the record, and :begin is admitted again.
(assert-event (fn-lgoc-invariantp *lgt-stale*))
(assert-event (not (fn-oclc-live-authorizep *lgt-stale*)))
(assert-event (fn-ocfg-staged *lgt-stale*))
(defconst *pst-unstaged* (fn-psrv-unstage *lgt-stale*))
(assert-event (fn-lgoc-invariantp *pst-unstaged*))
(assert-event (not (fn-ocfg-staged *pst-unstaged*)))
(assert-event (equal (fn-ocfg-owner *pst-unstaged*) (fn-ocfg-owner *lgt-stale*)))
(assert-event (equal (fn-ocfg-config *pst-unstaged*) (fn-ocfg-config *lgt-stale*)))
(assert-event (equal (in-arena-acar-t-ocfg-run *sr-arena* *lgt-stale* (list '(:begin 0))) *lgt-stale*))
(assert-event (not (equal (in-arena-acar-t-ocfg-run *sr-arena* *pst-unstaged* (list '(:begin 0))) *pst-unstaged*)))
; Hypothesis fn-lgoc-invariantp: the corrupted-companion owner with the
; retirement staged; the un-stage keeps it corrupted.
(defconst *pst-bad-stale*
  (fn-ocfg-make (fn-ocfg-owner *lgt-bad-oc0*) (fn-ocfg-config *lgt-bad-oc0*)
                (fn-ocfg-pins *lgt-bad-oc0*) *lgt-retire*))
(assert-event (not (fn-lgoc-invariantp *pst-bad-stale*)))
(assert-event (not (fn-lgoc-invariantp (fn-psrv-unstage *pst-bad-stale*))))
