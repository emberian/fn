; Teeth for books/served-carried.lisp and books/owner-served-carried.lisp.
(in-package "ACL2")
(include-book "../../books/owner-served-carried")
(include-book "std/testing/must-fail" :dir :system)
(include-book "config-owner-live-tests")

; Reachable witness: the configured owner after a live group creation opens
; two connections (config-owner-live-tests, *ocl-t-new-open*); connection 1
; reads "GROUP fn.live".
(defconst *scar-t-oc* *ocl-t-new-open*)
(defconst *scar-t-o* (fn-ocfg-owner *scar-t-oc*))
(defconst *scar-t-conn* (fn-own-find-conn 1 (fn-own-conns *scar-t-o*)))
(defconst *scar-t-carried*
  (fn-scar-ocfg-read-tls-prefix *scar-t-oc* 1 *ocl-t-live-group-command*))
(defconst *scar-t-reference*
  (fn-ocfg-read-tls-prefix *scar-t-oc* 1 *ocl-t-live-group-command*))

(assert-event (fn-ocl-relation *scar-t-oc*))
; The shortcut is exercised: the served session pins a node, and it is the
; store's own node, so the carried recognizer compares one pointer.
(assert-event
 (let ((node (fn-peer-session-node
              (fn-auth-session-base (fn-own-conn-live-session *scar-t-o* *scar-t-conn*)))))
   (and node (equal node (fn-sn-node (fn-own-store *scar-t-o*))))))
; The keystone on the witness, and it is not vacuous: the read answers and
; keeps the connection.
(assert-event (equal *scar-t-carried* *scar-t-reference*))
(assert-event (consp (fn-own-tls-result-effects *scar-t-carried*)))
(assert-event
 (fn-own-find-conn 1 (fn-own-conns (fn-ocfg-owner
                                    (fn-own-tls-result-owner *scar-t-carried*)))))
(assert-event
 (equal (fn-own-store (fn-ocfg-owner (fn-own-tls-result-owner *scar-t-carried*)))
        (fn-own-store *scar-t-o*)))

; The host's call runs compiled code: every carried function is guard-verified.
(assert-event
 (and (eq (symbol-class 'fn-scar-ocfg-read-tls-prefix (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-scar-own-read-tls-prefix (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-scar-auth-step-pinned (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-scar-finish-read (w state)) :common-lisp-compliant)))

; The hypothesis.  The same owner with the store's node replaced by a value
; that is not a node state (test-only surgery; fn-sn-with-configuration
; writes the node at position 3).  The relation fails; the carried read
; trusts the pointer and serves the command, the reference refuses the
; session, answers nothing and drops the connection.
(defconst *scar-t-bad-node* '(:not-a-node-state))
(defconst *scar-t-bad-o*
  (let ((o *scar-t-o*))
    (fn-own-make (update-nth 3 *scar-t-bad-node* (fn-own-store o))
                 (fn-own-view o) (fn-own-conns o) (fn-own-next-id o)
                 (fn-own-max-conns o) (fn-own-pending o) (fn-own-ledger o)
                 (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
                 (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o))))
(defconst *scar-t-bad-oc*
  (fn-ocfg-make *scar-t-bad-o* (fn-ocfg-config *scar-t-oc*)
                (fn-ocfg-pins *scar-t-oc*) (fn-ocfg-staged *scar-t-oc*)))
(assert-event (not (fn-ocl-relation *scar-t-bad-oc*)))
(assert-event (not (fn-node-statep (fn-sn-node (fn-own-store *scar-t-bad-o*)))))
(assert-event
 (not (equal (fn-scar-ocfg-read-tls-prefix *scar-t-bad-oc* 1 *ocl-t-live-group-command*)
             (fn-ocfg-read-tls-prefix *scar-t-bad-oc* 1 *ocl-t-live-group-command*))))
(assert-event
 (consp (fn-own-tls-result-effects
         (fn-scar-ocfg-read-tls-prefix *scar-t-bad-oc* 1 *ocl-t-live-group-command*))))
(assert-event
 (not (fn-own-find-conn
       1 (fn-own-conns
          (fn-ocfg-owner
           (fn-own-tls-result-owner
            (fn-ocfg-read-tls-prefix *scar-t-bad-oc* 1 *ocl-t-live-group-command*)))))))
(must-fail
 (defthm fn-scar-t-read-is-reference-without-relation
   (equal (fn-scar-ocfg-read-tls-prefix *scar-t-bad-oc* 1 *ocl-t-live-group-command*)
          (fn-ocfg-read-tls-prefix *scar-t-bad-oc* 1 *ocl-t-live-group-command*))))

; The served-level hypothesis, on the session alone: the bad node as `live'.
(defconst *scar-t-bad-session*
  (let ((as (fn-own-conn-live-session *scar-t-o* *scar-t-conn*)))
    (fn-auth-with-base as (fn-peer-with-node (fn-auth-session-base as)
                                             *scar-t-bad-node*))))
(assert-event (fn-scar-auth-sessionp *scar-t-bad-session* *scar-t-bad-node*))
(assert-event (not (fn-auth-sessionp *scar-t-bad-session*)))
(must-fail
 (defthm fn-scar-t-auth-sessionp-without-node-premise
   (equal (fn-scar-auth-sessionp *scar-t-bad-session* *scar-t-bad-node*)
          (fn-auth-sessionp *scar-t-bad-session*))))

; The store-keeping theorem is not the trivial one: a read changes the owner.
(assert-event
 (not (equal (fn-ocfg-owner (fn-own-tls-result-owner *scar-t-carried*))
             *scar-t-o*)))
