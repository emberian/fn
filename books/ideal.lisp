; F_node, the ideal node functionality -- SKELETON ONLY (packet P0).
;
; specs/node-functionality.md section 1 describes one object: a state machine
; whose state is the relay state plus configuration, connections and the clock,
; and whose step dispatches each port's event to the machine that already
; exists.  This book is the dispatcher's shape, not its content.  It is here so
; that the served path (books/served.lisp, packet P1) has a named port to be
; the reader port of, and so that the theorem the whole design is for has a
; written statement before it has a proof.
;
; WHAT IS REAL HERE: the reader port.  (:octets id chunk) is one socket read
; and is fn-served-step, whose keystones are proved in books/served.lisp.
;
; WHAT IS A STUB: every other port returns the state unchanged with a single
; (:todo <port>) effect.  A stub is not a refusal and not a no-op semantics
; claim; it is an unwritten transition.  No theorem in the tree may cite a
; stub branch, and fn-ideal-statep below is NOT the recognizer of section 1.1:
; the clauses that need books/relay and books/store-node-traces in the include
; closure (fn-relay-invp, fn-snt-relation, the configuration recognizer, the
; generation bound on each connection's version pin, max-conns, the clock
; observation and the outbox typing) are OPEN and listed at fn-ideal-statep.

(in-package "ACL2")
(include-book "served")

; -----------------------------------------------------------------------------
; The state record
;
; Field order and meaning follow specs/node-functionality.md section 1.1
; exactly, so that filling the stubs in never renumbers a field.

(defun fn-ideal-state-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 5)))

(defun fn-ideal-config (x)
  (declare (xargs :guard t))
  (mbe :logic (car x) :exec (fn-ag-car x)))

(defun fn-ideal-relay (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))

(defun fn-ideal-conns (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr x)))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr x)))))

(defun fn-ideal-clock (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr x))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x))))))

(defun fn-ideal-outbox (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr (cdr (cdr (cdr x)))))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))))

(defun fn-ideal-make-state (config relay conns clock outbox)
  (declare (xargs :guard t))
  (list config relay conns clock outbox))

(defthm fn-ideal-state-shapep-of-fn-ideal-make-state
  (fn-ideal-state-shapep (fn-ideal-make-state config relay conns clock outbox)))

(defthm fn-ideal-config-of-fn-ideal-make-state
  (equal (fn-ideal-config (fn-ideal-make-state config relay conns clock outbox))
         config))

(defthm fn-ideal-relay-of-fn-ideal-make-state
  (equal (fn-ideal-relay (fn-ideal-make-state config relay conns clock outbox))
         relay))

(defthm fn-ideal-conns-of-fn-ideal-make-state
  (equal (fn-ideal-conns (fn-ideal-make-state config relay conns clock outbox))
         conns))

(defthm fn-ideal-clock-of-fn-ideal-make-state
  (equal (fn-ideal-clock (fn-ideal-make-state config relay conns clock outbox))
         clock))

(defthm fn-ideal-outbox-of-fn-ideal-make-state
  (equal (fn-ideal-outbox (fn-ideal-make-state config relay conns clock outbox))
         outbox))

(defthm fn-ideal-state-shapep-forward-shape
  (implies (fn-ideal-state-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining)

(in-theory (disable (:d fn-ideal-state-shapep) (:d fn-ideal-config)
                    (:d fn-ideal-relay) (:d fn-ideal-conns)
                    (:d fn-ideal-clock) (:d fn-ideal-outbox)
                    (:d fn-ideal-make-state)))

; The result of one step: the state after it and the effects the host owes.

(defun fn-ideal-result-state (x)
  (declare (xargs :guard t))
  (mbe :logic (car x) :exec (fn-ag-car x)))

(defun fn-ideal-result-effects (x)
  (declare (xargs :guard t))
  (mbe :logic (car (cdr x)) :exec (fn-ag-car (fn-ag-cdr x))))

; The formal is `node', not `state': ACL2 reserves `state'.
(defun fn-ideal-make-result (node effects)
  (declare (xargs :guard t))
  (list node effects))

(defthm fn-ideal-result-state-of-fn-ideal-make-result
  (equal (fn-ideal-result-state (fn-ideal-make-result node effects)) node))

(defthm fn-ideal-result-effects-of-fn-ideal-make-result
  (equal (fn-ideal-result-effects (fn-ideal-make-result node effects)) effects))

(in-theory (disable (:d fn-ideal-result-state) (:d fn-ideal-result-effects)
                    (:d fn-ideal-make-result)))

; -----------------------------------------------------------------------------
; Connections, keyed by the host's connection identifier

(defun fn-ideal-conn-find (id conns)
  (declare (xargs :guard t))
  (if (consp conns)
      (if (and (consp (car conns)) (equal (car (car conns)) id))
          (cdr (car conns))
        (fn-ideal-conn-find id (cdr conns)))
    nil))

(defun fn-ideal-conn-put (id conn conns)
  (declare (xargs :guard t))
  (if (consp conns)
      (if (and (consp (car conns)) (equal (car (car conns)) id))
          (cons (cons id conn) (cdr conns))
        (cons (car conns) (fn-ideal-conn-put id conn (cdr conns))))
    (list (cons id conn))))

(defun fn-ideal-conn-alistp (conns)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp conns)
      (and (consp (car conns))
           (fn-served-connp (cdr (car conns)))
           (fn-ideal-conn-alistp (cdr conns)))
    (null conns)))

; OPEN.  This is NOT the recognizer of specs/node-functionality.md section 1.1.
; What it carries: the shape, and that every connection satisfies the served
; path's carried invariant.  What it is missing, each needing a book this
; skeleton does not include:
;   (fn-ideal-configp (fn-ideal-config s))                books/store-config, bp
;   (fn-relay-invp (fn-ideal-relay s))                    books/relay
;   (fn-snt-relation (fn-ideal-store s))                  books/store-node-traces
;   groups and capacity agree with the configuration      books/store-node
;   (<= (fn-ideal-conn-version c) (fn-ideal-generation s)) version pins, w2 owner
;   (<= (len conns) max-conns), duplicate-free ids
;   the clock observation and the outbox effect typing
; Until those clauses exist, no theorem may quote this predicate as "the F_node
; invariant"; it is the shape plus the reader port's share of it.
(defun fn-ideal-statep (s)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-ideal-state-shapep s)
       (fn-ideal-conn-alistp (fn-ideal-conns s))))

; -----------------------------------------------------------------------------
; The dispatcher
;
; One event, one port.  The event is (<port> . arguments); the reader port
; carries (:octets id chunk).

(defun fn-ideal-todo (s port)
  (declare (xargs :guard t))
  (fn-ideal-make-result s (list (list :todo port))))

(defun fn-ideal-step (s e)
  (declare (xargs :guard t))
  (let ((port (fn-ag-car e)))
    (cond
     ((equal port :octets)
      ;; The served path.  books/served.lisp proves this branch: the carried
      ;; invariant is preserved, the effects are the typed enumeration, and
      ;; the reply stream does not depend on how the network cut the input.
      (let* ((id (fn-ag-car (fn-ag-cdr e)))
             (chunk (fn-ag-car (fn-ag-cdr (fn-ag-cdr e))))
             ;; The reader environment (clock observation, creation facts)
             ;; rides on the port event: (:octets id chunk env).  The
             ;; environment supplies the observation; the machine never
             ;; reads a clock of its own.
             (env (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr e)))))
             (result (fn-served-step (fn-ideal-conn-find id (fn-ideal-conns s))
                                     env chunk)))
        (fn-ideal-make-result
         (fn-ideal-make-state (fn-ideal-config s)
                              (fn-ideal-relay s)
                              (fn-ideal-conn-put id (fn-served-result-conn result)
                                                 (fn-ideal-conns s))
                              (fn-ideal-clock s)
                              (fn-ideal-outbox s))
         (fn-served-result-effects result))))
     ;; STUBS.  Each names the machine that will own it; none is a semantics
     ;; claim, and none may be cited by any theorem.
     ((equal port :open)    (fn-ideal-todo s :open))     ; fn-served-open + pin
     ((equal port :close)   (fn-ideal-todo s :close))
     ((equal port :store)   (fn-ideal-todo s :store))    ; fn-snrt-step
     ((equal port :reopen)  (fn-ideal-todo s :reopen))   ; fn-sn-open-observed
     ((equal port :sender)  (fn-ideal-todo s :sender))   ; fn-bp-step
     ((equal port :bundle)  (fn-ideal-todo s :bundle))   ; fn-relay-accept
     ((equal port :clock)   (fn-ideal-todo s :clock))    ; fn-clock-observe
     ((equal port :io)      (fn-ideal-todo s :io))       ; A-HOST report
     (t                     (fn-ideal-todo s :unknown)))))

; -----------------------------------------------------------------------------
; The theorem this design exists for -- OPEN, statement only
;
; specs/node-functionality.md section 3: "clients cannot crash us regardless of
; what they send" is five theorems about the served entry point, each
; quantified over every state satisfying the carried invariant and over every
; event with no hypothesis on the event.  Written out here so that the claim
; is on the record before anything can be said to have proved it.  None of the
; five is proved.  Two of the five hold TODAY for the reader port only, in
; books/served.lisp (fn-served-step-effects-are-typed and
; fn-served-step-nntp-steps-is-bounded); the rest of each statement, and the
; lifting through fn-ideal-step, is unwritten.
;
; 3.1 Totality and typing.  The executable half is the guard theorem: guard t
; verified for fn-ideal-step and for every function reachable from it.  That
; closure check is packet P2 and does not hold yet (fn-ideal-statep and
; fn-ideal-conn-alistp above are deliberately not guard verified).
;
;   (defthm fn-ideal-step-is-total-and-typed                       ; OPEN
;     (and (implies (fn-ideal-statep s)
;                   (fn-ideal-statep (fn-ideal-result-state (fn-ideal-step s e))))
;          (fn-ideal-effect-listp (fn-ideal-result-effects (fn-ideal-step s e)))))
;
; 3.2 Work per step is bounded by configuration and input length.  Needs the
; instrumented twin of packet P3; books/served.lisp bounds the number of
; dispatcher steps per read by the read length and records the rest open.
;
;   (defthm fn-ideal-step-cost-is-bounded                          ; OPEN
;     (implies (fn-ideal-statep s)
;              (<= (fn-ideal-step-cost s e)
;                  (fn-ideal-cost-bound (fn-ideal-config s) (fn-ideal-event-len e)))))
;
; 3.3 Retained memory is bounded by configuration.  Needs posp charges (P3).
;
;   (defthm fn-ideal-reachable-size-is-bounded                     ; OPEN
;     (implies (fn-ideal-statep s)
;              (<= (fn-ideal-size s) (fn-ideal-size-bound (fn-ideal-config s)))))
;
; 3.4 The only failures are the typed refusals (P4), and uncertain, refused and
; accepted stay distinct at every boundary.
;
;   (defthm fn-ideal-step-effects-are-enumerated                   ; OPEN
;     (implies (fn-ideal-statep s)
;              (subsetp-equal (fn-ideal-refusals-of (fn-ideal-step s e))
;                             *fn-ideal-refusals*)))
;
; 3.5 Connection isolation: a read on one connection changes no other
; connection's state and produces no effect naming another connection.  Needs
; the w2 owner keystones (packet M7).
;
;   (defthm fn-ideal-connection-isolation                          ; OPEN
;     (implies (and (fn-ideal-statep s) (not (equal id other)))
;              (equal (fn-ideal-conn-find other
;                       (fn-ideal-conns (fn-ideal-result-state
;                                        (fn-ideal-step s (list :octets id chunk)))))
;                     (fn-ideal-conn-find other (fn-ideal-conns s)))))

; -----------------------------------------------------------------------------
; Export theory
;
; A skeleton exports its record lemmas and nothing else: no includer should be
; able to open a stub branch and conclude anything from it.

(deftheory fn-ideal-vocabulary
  '(fn-ideal-statep fn-ideal-conn-alistp fn-ideal-todo fn-ideal-step))

(in-theory (disable fn-ideal-vocabulary))
