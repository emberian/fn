; Teeth for books/owner-retain-frame.lisp: the owner profile proves REAL owner
; writers.  The callback-level writers of books/owner-connection-callbacks.lisp
; are the bodies of the host entries fn-owner-close, fn-owner-fault and
; fn-owner-open-peer (host/owner-host.lisp, each a one-line wrapper), so the
; declarations here are the stage-5 tier-A hand proofs
; (host/owner-retain-host.lisp on lane/stage-5b) minus the wrapper: the same
; keystones (:via), the same callees opened, the generated statement.
;
;   1. Three accepted writers; their generated statements pinned; the row
;      records the keystones and the written globals.
;   2. The legacy carrier's refusals: a function that puts 'fn-owner
;      directly; one that installs a value no keystone covers; the
;      profile's installers and carried globals as declared.
;   3. The row over the pilot: the transitions are the pilot's three
;      prepares then the three callbacks; def-carried-check re-checks it
;      (completeness is vacuous here: no fn-interfaces entry); the generated
;      ROW-FN-carries equals the writer's theorem by formula.

(in-package "ACL2")
(include-book "../../books/owner-retain-frame")
(include-book "../../books/owner-host-relation") ; the fn-ohr-* keystones
(include-book "../../books/payload-kinds")       ; the kinds (fn-cbor-octet-listp)
(include-book "must-fail-checked")

; ---------------------------------------------------------------------------
; 1. The writers.

(def-owner-writer fn-owner-callback-close
  :via (fn-ohr-step-close-preserves-carried-relation
        fn-owner-callback-close-branch-unfolds))

(assert-event
 (equal (getpropc 'fn-owner-callback-close-preserves-retain-state 'theorem nil (w state))
        '(implies (fn-owner-retain-statep state)
                  (fn-owner-retain-statep (mv-nth '2 (fn-owner-callback-close id fn-arena state))))))
(assert-event
 (equal (cdr (assoc-eq 'fn-owner-callback-close (table-alist 'fn-carried-writers (w state))))
        '(:profile fn-owner-retain :theorem fn-owner-callback-close-preserves-retain-state
          :via (fn-ohr-step-close-preserves-carried-relation
                fn-owner-callback-close-branch-unfolds)
          :opens nil :lemmas nil :step nil :bridges nil :hyps nil
          :put-keys nil :uncovered nil :hand-hints nil)))

(def-owner-writer fn-owner-callback-fault
  :via (fn-ohr-fault-preserves-carried-relation))

(assert-event
 (equal (getpropc 'fn-owner-callback-fault-preserves-retain-state 'theorem nil (w state))
        '(implies (fn-owner-retain-statep state)
                  (fn-owner-retain-statep (mv-nth '2 (fn-owner-callback-fault id state))))))

(def-owner-writer fn-owner-callback-open-peer
  :via ((fn-ohr-open-peer-preserves-carried-relation
         (peer (fn-store-octets->string peer-octets))
         (acfg (fn-owner-auth state)))))

(assert-event
 (equal (fn-cd-get :put-keys (cdr (assoc-eq 'fn-owner-callback-open-peer
                                          (table-alist 'fn-carried-writers (w state)))))
        '(fn-owner-log-line)))

; ---------------------------------------------------------------------------
; 2. The legacy carrier's refusals.

(defmacro ort-refused (fn kvs expected)
  `(make-event
    (mv-let (problem uncovered)
      (fn-cw-problem ',fn ',kvs (w state))
      (declare (ignore uncovered))
      (let ((text (if (and (consp problem) (stringp (car problem))) (car problem) "")))
        (if (search ,expected text)
            (value '(value-triple :refused))
          (er soft 'ort-refused "~x0 refused by ~@1, expected ~x2"
              ',fn (or problem "nothing") ,expected))))))

; a direct put of the carried global, outside the installers
(defun ort-direct-put (oc state)
  (declare (xargs :stobjs state :guard (boundp-global 'fn-owner state)))
  (f-put-global 'fn-owner oc state))
(ort-refused ort-direct-put (:profile fn-owner-retain)
             "writes the carried global")

; the installer fed the caller's own argument: no keystone covers it
(defun ort-install-arg (oc state)
  (declare (xargs :stobjs state :guard (boundp-global 'fn-owner state)))
  (fn-owner-install-ocfg oc state))
(ort-refused ort-install-arg (:profile fn-owner-retain)
             "and no :via, :lemmas, :frame or step")

; a guard conjunct over the state the host passes: (fn-sn-statep ...) is
; concluded by the pilot row's bridge, so a writer carrying it is accepted
; (the three prepares of the pilot do); one applying another predicate to
; the state alone names the bridge it needs
(defun ort-other-pred (state)
  (declare (xargs :stobjs state :guard (and (boundp-global 'fn-owner state)
                                            (fn-owner-history-bootstrap-mutationp state))))
  (f-put-global 'fn-owner-log-line nil state))
(ort-refused ort-other-pred (:profile fn-owner-retain) "no bridge concludes it")

(assert-event
 (equal (fn-cd-get :installers
                   (cdr (assoc-eq 'fn-owner-retain (table-alist 'fn-carried-profiles (w state)))))
        '(fn-owner-install-ocfg fn-owner-retain-carry-put)))
(assert-event
 (equal (fn-cd-get :carried-globals
                   (cdr (assoc-eq 'fn-owner-retain (table-alist 'fn-carried-profiles (w state)))))
        '(fn-owner fn-owner-retain-carry)))

(must-fail-checked (def-owner-writer ort-direct-put)
                   :unchecked "a refusal at expansion: the direct put of 'fn-owner")

; ---------------------------------------------------------------------------
; 3. The row.

(def-carried-writers-row ort-row :profile fn-owner-retain :from fn-owner-retain-carried)
(assert-event
 (equal (strip-cars (fn-cd-get :transitions
                               (cdr (assoc-eq 'ort-row (table-alist 'fn-carried (w state))))))
        '(fn-owner-prepare-identity fn-owner-prepare-consumer fn-owner-prepare-topic
          fn-owner-callback-close fn-owner-callback-fault fn-owner-callback-open-peer)))
(def-carried-check ort-row)
; the row's statement carries the guard; it is proved from the writer's by :use
(assert-event
 (equal (getpropc 'ort-row-fn-owner-callback-close-carries 'theorem nil (w state))
        '(implies (if (fn-owner-retain-statep state) (boundp-global 'fn-owner state) 'nil)
                  (fn-owner-retain-statep (mv-nth '2 (fn-owner-callback-close id fn-arena state))))))
(assert-event (null (fn-cw-owed 'fn-owner-retain 'fn-owner-retain-carried (w state))))
