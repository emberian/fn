; Teeth for books/owner-open-carried.lisp (PRF-188): the greeting the host
; opens with the owner's invariant carried.
(in-package "ACL2")
(include-book "../../books/owner-open-carried")
(include-book "std/testing/must-fail" :dir :system)
(include-book "owner-advance-carried-tests")
(include-book "public-exposure-tests")

; -----------------------------------------------------------------------------
; Reachable witness: owner-advance-carried-tests' *acar-t-committed*, the
; configured owner the host's open installs (config-owner-live-tests'
; *ocl-t-new-open*, one connection open) after one POST ran through
; fn-ocfg-step to :completing and the host's commit.  Its view archive holds
; the committed article; fn-ocl-relation holds.  A reader opens connection 2
; under the operator's AUTHINFO policy *aut-required*.

(defconst *ocar-t-oc* *acar-t-committed*)
(defconst *ocar-t-id* (fn-own-next-id (fn-ocfg-owner *ocar-t-oc*)))
(defconst *ocar-t-opened* (fn-ocar-ocfg-open *ocar-t-oc* *aut-required*))
(assert-event (fn-ocl-relation *ocar-t-oc*))
(assert-event (consp (fn-state-articles
                      (fn-own-view-archive (fn-own-view (fn-ocfg-owner *ocar-t-oc*))))))
(assert-event (equal *ocar-t-opened* (fn-ocfg-open *ocar-t-oc* *aut-required*)))
; Non-degenerate: the greeting is written, a connection is installed at the
; old next id and pinned, and its reader session records the projection and
; pins the store's node and the live configuration.
(assert-event (consp (car *ocar-t-opened*)))
(assert-event (equal (fn-served-reply-octets (car *ocar-t-opened*))
                     (fn-served-reply-octets
                      (list (fn-nntp-reply-effect *fn-served-greeting*)))))
(defconst *ocar-t-conn*
  (fn-own-find-conn *ocar-t-id* (fn-own-conns (fn-ocfg-owner (cdr *ocar-t-opened*)))))
(assert-event (equal (fn-own-conn-id *ocar-t-conn*) *ocar-t-id*))
(assert-event (fn-ocfg-pin-find *ocar-t-id* (fn-ocfg-pins (cdr *ocar-t-opened*))))
(defconst *ocar-t-base* (fn-auth-session-base (fn-own-conn-session *ocar-t-conn*)))
(assert-event (equal (fn-nntp-session-projected
                      (fn-auth-reader-session (fn-own-conn-session *ocar-t-conn*)))
                     t))
(assert-event (equal (fn-peer-session-node *ocar-t-base*)
                     (fn-sn-node (fn-own-store (fn-ocfg-owner *ocar-t-oc*)))))
(assert-event (equal (fn-peer-session-cfg *ocar-t-base*)
                     (fn-ocfg-config *ocar-t-oc*)))
(assert-event (fn-ocl-relation (cdr *ocar-t-opened*)))

; The exposure open (host/owner-host.lisp fn-owner-exposure-open): a reader
; admitted under public-exposure-tests' limits, the same witness owner.
(defconst *ocar-t-xr*
  (fn-ocar-exp-open *ocar-t-oc* (fn-exp-initial) *pxt-lim* *aut-required*
                    nil *pxt-a* 5000))
(assert-event (equal *ocar-t-xr*
                     (fn-exp-open *ocar-t-oc* (fn-exp-initial) *pxt-lim*
                                  *aut-required* nil *pxt-a* 5000)))
(assert-event (equal (fn-exp-open-id *ocar-t-xr*) *ocar-t-id*))
(assert-event (consp (fn-exp-open-effects *ocar-t-xr*)))

; The host's call runs compiled code: every carried function is guard-verified.
(assert-event
 (and (eq (symbol-class 'fn-ocar-auth-open-reader (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ocar-peer-open-reader (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ocar-served-open-group-indexed (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ocar-own-open (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ocar-own-reader-context (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ocar-ocfg-open (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-ocar-exp-open (w state)) :common-lisp-compliant)))

; -----------------------------------------------------------------------------
; The relation hypothesis of both keystones.  owner-advance-carried-tests'
; *acar-t-bad-view-oc*: the witness with a non-article added to the view
; archive (test-only surgery, no transition makes it).  The group list, next
; numbers and article bound still hold, so the carried open records a
; projection the reference denies; the relation fails on it.

(defconst *ocar-t-bad-oc* *acar-t-bad-view-oc*)
(assert-event (not (fn-ocl-relation *ocar-t-bad-oc*)))
(assert-event (not (equal (fn-ocar-ocfg-open *ocar-t-bad-oc* *aut-required*)
                          (fn-ocfg-open *ocar-t-bad-oc* *aut-required*))))
(assert-event
 (let ((id (fn-own-next-id (fn-ocfg-owner *ocar-t-bad-oc*))))
   (and (equal (fn-nntp-session-projected
                (fn-auth-reader-session
                 (fn-own-conn-session
                  (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner
                                                      (cdr (fn-ocar-ocfg-open
                                                            *ocar-t-bad-oc*
                                                            *aut-required*))))))))
               t)
        (equal (fn-nntp-session-projected
                (fn-auth-reader-session
                 (fn-own-conn-session
                  (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner
                                                      (cdr (fn-ocfg-open
                                                            *ocar-t-bad-oc*
                                                            *aut-required*))))))))
               nil))))
(assert-event (not (equal (fn-ocar-ocfg-open *ocar-t-bad-oc* *aut-required*)
          (fn-ocfg-open *ocar-t-bad-oc* *aut-required*))))
(must-fail
 (defthm fn-ocar-t-ocfg-open-without-relation
   (equal (fn-ocar-ocfg-open *ocar-t-bad-oc* *aut-required*)
          (fn-ocfg-open *ocar-t-bad-oc* *aut-required*))))
(assert-event (not (equal (fn-ocar-exp-open *ocar-t-bad-oc* (fn-exp-initial) *pxt-lim*
                            *aut-required* nil *pxt-a* 5000)
          (fn-exp-open *ocar-t-bad-oc* (fn-exp-initial) *pxt-lim*
                       *aut-required* nil *pxt-a* 5000))))
(must-fail
 (defthm fn-ocar-t-exp-open-without-relation
   (equal (fn-ocar-exp-open *ocar-t-bad-oc* (fn-exp-initial) *pxt-lim*
                            *aut-required* nil *pxt-a* 5000)
          (fn-exp-open *ocar-t-bad-oc* (fn-exp-initial) *pxt-lim*
                       *aut-required* nil *pxt-a* 5000))))

; -----------------------------------------------------------------------------
; The steps' hypotheses, each alone (the others hold on the witness values).

(defconst *ocar-t-archive*
  (fn-own-view-archive (fn-own-view (fn-ocfg-owner *ocar-t-oc*))))
(defconst *ocar-t-cfg* (fn-ocfg-config *ocar-t-oc*))
(defconst *ocar-t-node* (fn-sn-node (fn-own-store (fn-ocfg-owner *ocar-t-oc*))))
(assert-event (fn-statep *ocar-t-archive*))
(assert-event (not (fn-statep *acar-t-bad-archive*)))
(assert-event (fn-node-statep *ocar-t-node*))
(assert-event (not (fn-node-statep *scar-t-bad-node*)))
(assert-event (fn-cfgp *ocar-t-cfg*))

; fn-ocar-auth-open-reader-is-auth-open-session: witness and (fn-statep archive).
(assert-event (equal (fn-ocar-auth-open-reader *ocar-t-archive* *aut-required*)
                     (fn-auth-open-session *ocar-t-archive* nil nil nil
                                           *aut-required* nil)))
(assert-event (not (equal (fn-ocar-auth-open-reader *acar-t-bad-archive* *aut-required*)
          (fn-auth-open-session *acar-t-bad-archive* nil nil nil
                                *aut-required* nil))))
(must-fail
 (defthm fn-ocar-t-auth-reader-without-statep
   (equal (fn-ocar-auth-open-reader *acar-t-bad-archive* *aut-required*)
          (fn-auth-open-session *acar-t-bad-archive* nil nil nil
                                *aut-required* nil))))

; fn-ocar-peer-open-reader-is-peer-open-session: witness, then each of its
; three hypotheses.
(assert-event (equal (fn-ocar-peer-open-reader *ocar-t-archive* *ocar-t-node* *ocar-t-cfg*)
                     (fn-peer-open-session *ocar-t-archive* nil *ocar-t-node* *ocar-t-cfg*)))
(assert-event (not (equal (fn-ocar-peer-open-reader *acar-t-bad-archive* *ocar-t-node* *ocar-t-cfg*)
          (fn-peer-open-session *acar-t-bad-archive* nil *ocar-t-node* *ocar-t-cfg*))))
(must-fail
 (defthm fn-ocar-t-peer-reader-without-statep
   (equal (fn-ocar-peer-open-reader *acar-t-bad-archive* *ocar-t-node* *ocar-t-cfg*)
          (fn-peer-open-session *acar-t-bad-archive* nil *ocar-t-node* *ocar-t-cfg*))))
(assert-event (not (equal (fn-ocar-peer-open-reader *ocar-t-archive* *scar-t-bad-node* *ocar-t-cfg*)
          (fn-peer-open-session *ocar-t-archive* nil *scar-t-bad-node* *ocar-t-cfg*))))
(must-fail
 (defthm fn-ocar-t-peer-reader-without-node-statep
   (equal (fn-ocar-peer-open-reader *ocar-t-archive* *scar-t-bad-node* *ocar-t-cfg*)
          (fn-peer-open-session *ocar-t-archive* nil *scar-t-bad-node* *ocar-t-cfg*))))
(assert-event (not (fn-cfgp nil)))
(assert-event (not (equal (fn-ocar-peer-open-reader *ocar-t-archive* *ocar-t-node* nil)
          (fn-peer-open-session *ocar-t-archive* nil *ocar-t-node* nil))))
(must-fail
 (defthm fn-ocar-t-peer-reader-without-cfgp
   (equal (fn-ocar-peer-open-reader *ocar-t-archive* *ocar-t-node* nil)
          (fn-peer-open-session *ocar-t-archive* nil *ocar-t-node* nil))))

; fn-ocar-own-open-is-own-open: witness and fn-acar-view-statep.
(assert-event (fn-acar-view-statep (fn-ocfg-owner *ocar-t-oc*)))
(assert-event (equal (fn-ocar-own-open (fn-ocfg-owner *ocar-t-oc*) *aut-required*)
                     (fn-own-open (fn-ocfg-owner *ocar-t-oc*) *aut-required*)))
(assert-event (not (fn-acar-view-statep *acar-t-bad-view-o*)))
(assert-event (not (equal (fn-ocar-own-open *acar-t-bad-view-o* *aut-required*)
          (fn-own-open *acar-t-bad-view-o* *aut-required*))))
(must-fail
 (defthm fn-ocar-t-own-open-without-view-statep
   (equal (fn-ocar-own-open *acar-t-bad-view-o* *aut-required*)
          (fn-own-open *acar-t-bad-view-o* *aut-required*))))

; fn-ocar-own-reader-context-is-reference: the owner just opened (the new
; connection at *ocar-t-id*), then each hypothesis alone.
(defconst *ocar-t-raw* (cdr (fn-own-open (fn-ocfg-owner *ocar-t-oc*) *aut-required*)))
(assert-event (fn-statep (fn-own-conn-archive
                          (fn-own-find-conn *ocar-t-id* (fn-own-conns *ocar-t-raw*)))))
(assert-event (equal (fn-ocar-own-reader-context *ocar-t-raw* *ocar-t-id* *ocar-t-cfg*)
                     (fn-own-reader-context *ocar-t-raw* *ocar-t-id* *ocar-t-cfg*)))
(assert-event (not (equal (fn-own-reader-context *ocar-t-raw* *ocar-t-id* *ocar-t-cfg*)
                          *ocar-t-raw*)))
(defconst *ocar-t-bad-raw* (cdr (fn-own-open *acar-t-bad-view-o* *aut-required*)))
(assert-event (not (equal (fn-ocar-own-reader-context *ocar-t-bad-raw* *ocar-t-id* *ocar-t-cfg*)
          (fn-own-reader-context *ocar-t-bad-raw* *ocar-t-id* *ocar-t-cfg*))))
(must-fail
 (defthm fn-ocar-t-reader-context-without-statep
   (equal (fn-ocar-own-reader-context *ocar-t-bad-raw* *ocar-t-id* *ocar-t-cfg*)
          (fn-own-reader-context *ocar-t-bad-raw* *ocar-t-id* *ocar-t-cfg*))))
(defconst *ocar-t-bad-node-raw*
  (fn-own-make (update-nth 3 *scar-t-bad-node* (fn-own-store *ocar-t-raw*))
               (fn-own-view *ocar-t-raw*) (fn-own-conns *ocar-t-raw*)
               (fn-own-next-id *ocar-t-raw*) (fn-own-max-conns *ocar-t-raw*)
               (fn-own-pending *ocar-t-raw*) (fn-own-ledger *ocar-t-raw*)
               (fn-own-clock *ocar-t-raw*) (fn-own-facts *ocar-t-raw*)
               (fn-own-config *ocar-t-raw*) (fn-own-queue *ocar-t-raw*)
               (fn-own-inflight *ocar-t-raw*) (fn-own-feeds *ocar-t-raw*)))
(assert-event (equal (fn-sn-node (fn-own-store *ocar-t-bad-node-raw*)) *scar-t-bad-node*))
(assert-event (not (equal (fn-ocar-own-reader-context *ocar-t-bad-node-raw* *ocar-t-id* *ocar-t-cfg*)
          (fn-own-reader-context *ocar-t-bad-node-raw* *ocar-t-id* *ocar-t-cfg*))))
(must-fail
 (defthm fn-ocar-t-reader-context-without-node-statep
   (equal (fn-ocar-own-reader-context *ocar-t-bad-node-raw* *ocar-t-id* *ocar-t-cfg*)
          (fn-own-reader-context *ocar-t-bad-node-raw* *ocar-t-id* *ocar-t-cfg*))))
(assert-event (not (equal (fn-ocar-own-reader-context *ocar-t-raw* *ocar-t-id* nil)
          (fn-own-reader-context *ocar-t-raw* *ocar-t-id* nil))))
(must-fail
 (defthm fn-ocar-t-reader-context-without-cfgp
   (equal (fn-ocar-own-reader-context *ocar-t-raw* *ocar-t-id* nil)
          (fn-own-reader-context *ocar-t-raw* *ocar-t-id* nil))))
