; Teeth for books/owner-advance-carried.lisp and books/owner-commit-ocl.lisp.
(in-package "ACL2")
(include-book "../../books/owner-advance-carried")
(include-book "../../books/owner-commit-ocl")
(include-book "std/testing/must-fail" :dir :system)
(include-book "owner-served-invariants-tests")
(include-book "owner-served-carried-tests")

; -----------------------------------------------------------------------------
; The re-pin after a durable POST (books/owner-advance-carried.lisp).

; Reachable witness (owner relation): owner-served-invariants-tests'
; *osi-completing*, connection 4's article at :completing, committed through
; the carried commit; the outcome for :durable is the 240 and re-pins
; connection 4.
(defconst *acar-t-o4* (cdr (fn-ccar-own-finish *osi-completing* *osi-cfg*)))
(assert-event (fn-own-relation *osi-completing*))
(assert-event (fn-acar-conn-sessionp *acar-t-o4* 4))
(assert-event (equal (fn-acar-own-outcome *acar-t-o4* 4 :durable)
                     (fn-own-outcome *acar-t-o4* 4 :durable)))
(assert-event (equal (fn-served-reply-octets (car (fn-acar-own-outcome *acar-t-o4* 4 :durable)))
                     (append (fn-nntp-string-octets "240 article received OK") '(13 10))))
(assert-event (not (equal (cdr (fn-acar-own-outcome *acar-t-o4* 4 :durable)) *acar-t-o4*)))

; Reachable witness (configured owner relation): config-owner-live-tests'
; *ocl-t-new-open* (as *scar-t-oc*), then connection-free store events of
; one POST run through fn-ocfg-step to :completing, then the host's commit.
; Connection 1's session carries a node, the store's node when it was
; opened; after the commit the store's node is a new one, so the served
; lane's comparison with the live node would miss, and the carried advance
; compares with the node the session already carries.
(defun acar-t-ocfg-run (oc events)
  (declare (xargs :mode :program))
  (if (consp events)
      (acar-t-ocfg-run (fn-ocfg-step oc (car events)) (cdr events))
    oc))
(defconst *acar-t-record* (own-record 2 8 "<ocmt@example>"))
(defconst *acar-t-completing*
  (acar-t-ocfg-run *scar-t-oc* (osi-drop-last (own-post-events *acar-t-record*))))
(defconst *acar-t-committed*
  (fn-ocfg-with-owner *acar-t-completing*
                      (cdr (fn-ccar-own-finish (fn-ocfg-owner *acar-t-completing*)
                                               (fn-ocfg-config *acar-t-completing*)))))
(defconst *acar-t-o* (fn-ocfg-owner *acar-t-committed*))
(defconst *acar-t-conn* (fn-own-find-conn 1 (fn-own-conns *acar-t-o*)))
(assert-event (fn-ocl-relation *acar-t-completing*))
(assert-event (fn-ocl-relation *acar-t-committed*))
(assert-event (fn-acar-session-node *acar-t-conn*))
(assert-event (equal (fn-acar-session-node *acar-t-conn*)
                     (fn-sn-node (fn-own-store (fn-ocfg-owner *scar-t-oc*)))))
(assert-event (not (equal (fn-acar-session-node *acar-t-conn*)
                          (fn-sn-node (fn-own-store *acar-t-o*)))))
(assert-event (equal (fn-acar-own-advance-result *acar-t-o* 1)
                     (fn-own-advance-result *acar-t-o* 1)))
(assert-event (equal (car (fn-acar-own-advance-result *acar-t-o* 1)) :advanced))
(assert-event (equal (fn-own-view-version
                      (fn-own-view *acar-t-o*)) 3))

; The host's call runs compiled code: the carried functions are guard-verified.
(assert-event
 (and (eq (symbol-class 'fn-acar-own-outcome (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-acar-own-advance-result (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-acar-session-node (w state)) :common-lisp-compliant)))

; The hypothesis.  The committed owner with connection 1's session carrying
; a value that is not a node state (test-only surgery).  The connection no
; longer holds a session and the relation fails; the carried advance trusts
; the held node and re-pins, the reference refuses.
(defconst *acar-t-bad-session*
  (let ((as (fn-own-conn-session *acar-t-conn*)))
    (fn-auth-with-base as (fn-peer-with-node (fn-auth-session-base as)
                                             *scar-t-bad-node*))))
(defconst *acar-t-bad-o*
  (fn-own-set-conns *acar-t-o*
                    (fn-own-replace-conn (update-nth 4 *acar-t-bad-session* *acar-t-conn*)
                                         (fn-own-conns *acar-t-o*))))
(defconst *acar-t-bad-oc*
  (fn-ocfg-make *acar-t-bad-o* (fn-ocfg-config *acar-t-committed*)
                (fn-ocfg-pins *acar-t-committed*) (fn-ocfg-staged *acar-t-committed*)))
(assert-event (equal (fn-own-conn-session (fn-own-find-conn 1 (fn-own-conns *acar-t-bad-o*)))
                     *acar-t-bad-session*))
(assert-event (not (fn-acar-conn-sessionp *acar-t-bad-o* 1)))
(assert-event (not (fn-ocl-relation *acar-t-bad-oc*)))
(assert-event (equal (car (fn-acar-own-advance-result *acar-t-bad-o* 1)) :advanced))
(assert-event (equal (car (fn-own-advance-result *acar-t-bad-o* 1)) :refused))
; fn-acar-own-advance-result-is-own-advance-result without its hypothesis.
(must-fail
 (defthm fn-acar-t-advance-without-session
   (equal (fn-acar-own-advance-result *acar-t-bad-o* 1)
          (fn-own-advance-result *acar-t-bad-o* 1))))
; fn-acar-scar-auth-sessionp-of-rebuilt-session without (fn-auth-sessionp as).
(must-fail
 (defthm fn-acar-t-rebuilt-session-without-session
   (equal (fn-scar-auth-sessionp
           (fn-auth-with-base
            *acar-t-bad-session*
            (fn-peer-with-base (fn-auth-session-base *acar-t-bad-session*)
                               (fn-peer-session-base
                                (fn-auth-session-base *acar-t-bad-session*))))
           (fn-peer-session-node (fn-auth-session-base *acar-t-bad-session*)))
          (fn-auth-sessionp
           (fn-auth-with-base
            *acar-t-bad-session*
            (fn-peer-with-base (fn-auth-session-base *acar-t-bad-session*)
                               (fn-peer-session-base
                                (fn-auth-session-base *acar-t-bad-session*))))))))
; fn-acar-ocl-relation-carries-conn-sessionp without the relation.
(must-fail
 (defthm fn-acar-t-conn-sessionp-without-relation
   (fn-acar-conn-sessionp (fn-ocfg-owner *acar-t-bad-oc*) 1)))
; The outcome keystones without the relation.  A submission of connection 1
; in flight with a completion consumed makes the outcome re-pin it.
(defconst *acar-t-bad-inflight-o*
  (let ((o *acar-t-bad-o*))
    (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                 (fn-own-next-id o) (fn-own-max-conns o) (fn-own-pending o)
                 (fn-own-ledger o) (fn-own-clock o) (fn-own-facts o)
                 (fn-own-config o) (fn-own-queue o)
                 (fn-own-sub-make 1 (fn-own-conn-version *acar-t-conn*) 0 nil)
                 (fn-own-feeds o))))
(defconst *acar-t-bad-inflight-oc*
  (fn-ocfg-make *acar-t-bad-inflight-o* (fn-ocfg-config *acar-t-committed*)
                (fn-ocfg-pins *acar-t-committed*) (fn-ocfg-staged *acar-t-committed*)))
(assert-event (not (fn-ocl-relation *acar-t-bad-inflight-oc*)))
(must-fail
 (defthm fn-acar-t-outcome-without-relation
   (equal (fn-acar-own-outcome (fn-ocfg-owner *acar-t-bad-inflight-oc*) 1 :durable)
          (fn-own-outcome (fn-ocfg-owner *acar-t-bad-inflight-oc*) 1 :durable))))

; -----------------------------------------------------------------------------
; fn-ocl-relation across the commit (books/owner-commit-ocl.lisp).

; The witness is an article completion: the record found is the article
; record, the store returns to :ready with the history kept, the node moves.
(defconst *acar-t-st* (fn-own-store (fn-ocfg-owner *acar-t-completing*)))
(assert-event (fn-sn-completion-enabledp *acar-t-st*))
(assert-event (fn-record-p (fn-sn-completion-record *acar-t-st*)))
(assert-event (fn-cst-relation *acar-t-st*))
(assert-event (fn-cst-relation (fn-sn-finish *acar-t-st*)))
(assert-event (equal (fn-sf-phase (fn-sn-files (fn-sn-finish *acar-t-st*))) :ready))
(assert-event (equal (len (fn-sf-records (fn-sn-files (fn-sn-finish *acar-t-st*)))) 3))
(assert-event (not (equal (fn-sn-node (fn-sn-finish *acar-t-st*)) (fn-sn-node *acar-t-st*))))
(assert-event (equal (fn-own-store *acar-t-o*) (fn-sn-finish *acar-t-st*)))

; fn-ocmt-sn-finish-preserves-cst-relation without fn-cst-relation: the same
; store with its node replaced; the completion gate refuses (fn-sn-statep
; fails) and the store stays unrelated.
(defconst *acar-t-bad-st* (update-nth 3 *scar-t-bad-node* *acar-t-st*))
(assert-event (not (fn-cst-relation *acar-t-bad-st*)))
(must-fail
 (defthm fn-acar-t-finish-cst-without-relation
   (fn-cst-relation (fn-sn-finish *acar-t-bad-st*))))
; fn-ocmt-post-commit-preserves-ocl-relation without fn-ocl-relation.
(defconst *acar-t-bad-completing*
  (let ((o (fn-ocfg-owner *acar-t-completing*)))
    (fn-ocfg-make
     (fn-own-make *acar-t-bad-st* (fn-own-view o) (fn-own-conns o)
                  (fn-own-next-id o) (fn-own-max-conns o) (fn-own-pending o)
                  (fn-own-ledger o) (fn-own-clock o) (fn-own-facts o)
                  (fn-own-config o) (fn-own-queue o) (fn-own-inflight o)
                  (fn-own-feeds o))
     (fn-ocfg-config *acar-t-completing*) (fn-ocfg-pins *acar-t-completing*)
     (fn-ocfg-staged *acar-t-completing*))))
(assert-event (not (fn-ocl-relation *acar-t-bad-completing*)))
(must-fail
 (defthm fn-acar-t-commit-ocl-without-relation
   (fn-ocl-relation
    (fn-ocfg-with-owner *acar-t-bad-completing*
                        (cdr (fn-ccar-own-finish (fn-ocfg-owner *acar-t-bad-completing*)
                                                 (fn-ocfg-config *acar-t-bad-completing*)))))))
