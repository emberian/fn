; Teeth for books/served-carried.lisp and books/owner-served-carried.lisp.
(in-package "ACL2")
(include-book "../../books/owner-served-carried")
(include-book "../../books/defkeystone")
(include-book "must-fail-checked")
(include-book "config-owner-live-tests")

; Reachable witness: the configured owner after a live group creation opens
; two connections (config-owner-live-tests, *ocl-t-new-open*); connection 1
; reads "GROUP fn.live".
(defconst *scar-t-oc* *ocl-t-new-open*)
(defconst *scar-t-o* (fn-ocfg-owner *scar-t-oc*))
(defconst *scar-t-conn* (fn-own-find-conn 1 (fn-own-conns *scar-t-o*)))
(include-book "arena-lift")
;; The payloads the arena holds at handles 0, 1, ...: none (no byte is read here).
(defconst *sr-arena* nil)
(bpr-lift fn-ocfg-read-tls-prefix 3)
(bpr-lift fn-scar-ocfg-read-tls-prefix 3)
(bpr-lift fn-ocfg-read-step 3)
(bpr-lift fn-scar-ocfg-read-step 3)
(defconst *scar-t-carried*
  (in-arena-fn-scar-ocfg-read-tls-prefix *sr-arena* *scar-t-oc* 1 *ocl-t-live-group-command*))
(defconst *scar-t-reference*
  (in-arena-fn-ocfg-read-tls-prefix *sr-arena* *scar-t-oc* 1 *ocl-t-live-group-command*))

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
                 (fn-own-max-conns o) (fn-own-pending o) (fn-own-ledger-field o)
                 (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
                 (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o))))
(defconst *scar-t-bad-oc*
  (fn-ocfg-make *scar-t-bad-o* (fn-ocfg-config *scar-t-oc*)
                (fn-ocfg-pins *scar-t-oc*) (fn-ocfg-staged *scar-t-oc*)))
(assert-event (not (fn-ocl-relation *scar-t-bad-oc*)))
(assert-event (not (fn-node-statep (fn-sn-node (fn-own-store *scar-t-bad-o*)))))
(assert-event
 (not (equal (in-arena-fn-scar-ocfg-read-tls-prefix *sr-arena* *scar-t-bad-oc* 1 *ocl-t-live-group-command*)
             (in-arena-fn-ocfg-read-tls-prefix *sr-arena* *scar-t-bad-oc* 1 *ocl-t-live-group-command*))))
(assert-event
 (consp (fn-own-tls-result-effects
         (in-arena-fn-scar-ocfg-read-tls-prefix *sr-arena* *scar-t-bad-oc* 1 *ocl-t-live-group-command*))))
(assert-event
 (not (fn-own-find-conn
       1 (fn-own-conns
          (fn-ocfg-owner
           (fn-own-tls-result-owner
            (in-arena-fn-ocfg-read-tls-prefix *sr-arena* *scar-t-bad-oc* 1 *ocl-t-live-group-command*)))))))
(must-fail-checked
 (defthm fn-scar-t-read-is-reference-without-relation
   (equal (fn-scar-ocfg-read-tls-prefix *scar-t-bad-oc* 1 *ocl-t-live-group-command* fn-arena)
          (fn-ocfg-read-tls-prefix *scar-t-bad-oc* 1 *ocl-t-live-group-command* fn-arena))))

; The served-level hypothesis, on the session alone: the bad node as `live'.
(defconst *scar-t-bad-session*
  (let ((as (fn-own-conn-live-session *scar-t-o* *scar-t-conn*)))
    (fn-auth-with-base as (fn-peer-with-node (fn-auth-session-base as)
                                             *scar-t-bad-node*))))
(assert-event (fn-scar-auth-sessionp *scar-t-bad-session* *scar-t-bad-node*))
(assert-event (not (fn-auth-sessionp *scar-t-bad-session*)))
(must-fail-checked
 (defthm fn-scar-t-auth-sessionp-without-node-premise
   (equal (fn-scar-auth-sessionp *scar-t-bad-session* *scar-t-bad-node*)
          (fn-auth-sessionp *scar-t-bad-session*))))

; The store-keeping theorem is not the trivial one: a read changes the owner.
(assert-event
 (not (equal (fn-ocfg-owner (fn-own-tls-result-owner *scar-t-carried*))
             *scar-t-o*)))

; -----------------------------------------------------------------------------
; The host's wire events (PRF-1357): the SASL context event every accept
; sends, carried.  Connection 1 of the same witness takes the context.

(defconst *scar-t-seed* (make-list 32 :initial-element 7))
(defconst *scar-t-event* (list :sasl-context *scar-t-seed* nil))
(defconst *scar-t-ev-carried*
  (in-arena-fn-scar-ocfg-read-step *sr-arena* *scar-t-oc* 1 *scar-t-event*))
(defconst *scar-t-ev-reference*
  (in-arena-fn-ocfg-read-step *sr-arena* *scar-t-oc* 1 *scar-t-event*))
(defconst *scar-t-ev-conn*
  (fn-own-find-conn 1 (fn-own-conns (fn-ocfg-owner (cdr *scar-t-ev-carried*)))))

; Positive witness: the whole antecedent (the relation, the view trie's
; correspondence) and the conclusion, and the event did its work: no reply,
; the connection kept, the context installed in its session, the store kept.
(assert-event (and (fn-ocl-relation *scar-t-oc*)
                   (fn-scar-view-indexedp *scar-t-o*)))
(assert-event (equal *scar-t-ev-carried* *scar-t-ev-reference*))
(assert-event (null (car *scar-t-ev-carried*)))
(assert-event (and *scar-t-ev-conn*
                   (equal (fn-auth-session-ctx (fn-own-conn-session *scar-t-ev-conn*))
                          (list :sasl-context *scar-t-seed* nil))))
(assert-event (equal (fn-own-store (fn-ocfg-owner (cdr *scar-t-ev-carried*)))
                     (fn-own-store *scar-t-o*)))
(assert-event (not (equal (fn-ocfg-owner (cdr *scar-t-ev-carried*)) *scar-t-o*)))

(assert-event
 (and (eq (symbol-class 'fn-scar-ocfg-read-step (w state)) :common-lisp-compliant)
      (eq (symbol-class 'fn-scar-own-read-step-full (w state)) :common-lisp-compliant)))

; Hypothesis removal.  An event step reads the connection's stored session,
; which pins the node the connection opened over; the byte read re-pins the
; store's node first.  So the witness is the bad-node owner whose connection 1
; pins that same bad node: the relation fails, the carried step trusts the
; pointer, keeps the connection and installs the context, and the reference
; refuses the session, installs nothing and drops the connection.
(defconst *scar-t-bad-conn1*
  (let ((c *scar-t-conn*))
    (fn-own-conn-make-group-indexed
     (fn-own-conn-id c) (fn-own-conn-version c) (fn-own-conn-frontier c)
     (fn-own-conn-wire c)
     (fn-auth-with-base (fn-own-conn-session c)
                        (fn-peer-with-node
                         (fn-auth-session-base (fn-own-conn-session c))
                         *scar-t-bad-node*))
     (fn-own-conn-archive c) (fn-own-conn-config c) (fn-own-conn-observation c)
     (fn-own-conn-verdicts c) (fn-own-conn-index c) (fn-own-conn-group-index c)
     (fn-own-conn-control c))))
(defconst *scar-t-bad-ev-oc*
  (let ((o *scar-t-bad-o*))
    (fn-ocfg-make
     (fn-own-set-conns o (fn-own-replace-conn *scar-t-bad-conn1* (fn-own-conns o)))
     (fn-ocfg-config *scar-t-bad-oc*) (fn-ocfg-pins *scar-t-bad-oc*)
     (fn-ocfg-staged *scar-t-bad-oc*))))
(assert-event (not (fn-ocl-relation *scar-t-bad-ev-oc*)))
(assert-event
 (not (equal (in-arena-fn-scar-ocfg-read-step *sr-arena* *scar-t-bad-ev-oc* 1 *scar-t-event*)
             (in-arena-fn-ocfg-read-step *sr-arena* *scar-t-bad-ev-oc* 1 *scar-t-event*))))
(assert-event
 (fn-own-find-conn
  1 (fn-own-conns
     (fn-ocfg-owner
      (cdr (in-arena-fn-scar-ocfg-read-step *sr-arena* *scar-t-bad-ev-oc* 1 *scar-t-event*))))))
(assert-event
 (not (fn-own-find-conn
       1 (fn-own-conns
          (fn-ocfg-owner
           (cdr (in-arena-fn-ocfg-read-step *sr-arena* *scar-t-bad-ev-oc* 1 *scar-t-event*)))))))

;; The three theorems of PRF-1357 as registered keystones.  Each carries its
;; premises as one labelled hypothesis: the node and view-trie premises are
;; the carried invariant (books/owner-offer-indexed.lisp, fn-ocl-relation),
;; and a state with the relation true and the trie uncorresponding is not
;; reachable by an event the SASL context witness can exercise, so the
;; removal witness drops the whole premise at the bad-node owner.
(defteeth fn-scar-ocfg-read-step-is-reference-under-ocl-relation
  :claim (((carried-premises (and (fn-ocl-relation oc)
                                  (fn-scar-view-indexedp (fn-ocfg-owner oc)))))
          (equal (fn-scar-ocfg-read-step oc id event fn-arena)
                 (fn-ocfg-read-step oc id event fn-arena)))
  :subject fn-scar-ocfg-read-step
  :witness ((oc *scar-t-oc*) (id 1) (event *scar-t-event*))
  :breaks ((carried-premises ((oc *scar-t-bad-ev-oc*))))
  :mutations ((reply-for-a-context-event
               (:conclusion
                (equal (car (fn-scar-ocfg-read-step oc id event fn-arena))
                       '(:a-reply-for-a-context-event)))
               ()
               :fault "The carried step answers a reply to a host event that emits none")))

(defteeth fn-scar-ocfg-read-step-is-ocfg-read-step
  :claim (((carried-premises (and (fn-node-statep (fn-sn-node (fn-own-store (fn-ocfg-owner oc))))
                                  (fn-scar-view-indexedp (fn-ocfg-owner oc)))))
          (equal (fn-scar-ocfg-read-step oc id event fn-arena)
                 (fn-ocfg-read-step oc id event fn-arena)))
  :subject fn-scar-ocfg-read-step
  :witness ((oc *scar-t-oc*) (id 1) (event *scar-t-event*))
  :breaks ((carried-premises ((oc *scar-t-bad-ev-oc*))))
  :mutations ((dropped-pin-update
               (:conclusion
                (equal (fn-ocfg-pins (cdr (fn-scar-ocfg-read-step oc id event fn-arena)))
                       nil))
               ()
               :fault "The carried step loses the configuration pin table")))

(defteeth fn-scar-own-read-step-full-is-own-read-step-full
  :claim (((carried-premises (and (fn-node-statep (fn-sn-node (fn-own-store o)))
                                  (fn-scar-view-indexedp o))))
          (equal (fn-scar-own-read-step-full o id event fn-arena)
                 (fn-own-read-step-full o id event fn-arena)))
  :subject fn-scar-own-read-step-full
  :witness ((o *scar-t-o*) (id 1) (event *scar-t-event*))
  :breaks ((carried-premises ((o (fn-ocfg-owner *scar-t-bad-ev-oc*)))))
  :mutations ((reply-for-a-context-event
               (:conclusion
                (equal (car (fn-scar-own-read-step-full o id event fn-arena))
                       '(:a-reply-for-a-context-event)))
               ()
               :fault "The carried step answers a reply to a host event that emits none")))

(defteeth-check (fn-scar-ocfg-read-step-is-reference-under-ocl-relation
                 fn-scar-ocfg-read-step-is-ocfg-read-step
                 fn-scar-own-read-step-full-is-own-read-step-full))
