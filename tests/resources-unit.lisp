; Negative fixtures for every certification-time check of resources.lisp:
; each predicate accepts the real table and rejects one named defect.
; Run: sh tools/certify.sh tests/resources-unit.lisp
(in-package "ACL2")
(include-book "../books/resources")
(include-book "../books/sched")
(include-book "../books/arm-children")
(include-book "../books/core")
(include-book "std/util/bstar" :dir :system)

(defmacro fn2-resource-rejects (name form)
  `(assert-event (not ,form) :msg (msg "~x0: a defective table was accepted" ',name)))

; (a) one total order (a rank is a kind's place, so no tie or gap can be
; written): no duplicate kind, no prose-free row; ranks follow the order.
(assert-event (fn2-resource-order-p *fn2-resource-order*))
(assert-event (and (equal (fn2-resource-rank :service-work *fn2-resource-order*) 1)
                   (equal (fn2-resource-rank :cursor-row *fn2-resource-order*) 14)
                   ;; a consumer request takes its append's upload (e-surface.md 3.3)
                   (< (fn2-resource-rank :wait-row *fn2-resource-order*) (fn2-resource-rank :upload-row *fn2-resource-order*))
                   (equal (fn2-resource-rank :bogus *fn2-resource-order*) 0)))
(fn2-resource-rejects :order-duplicate
  (fn2-resource-order-p
   (append *fn2-resource-order*
           (list (cons :operation '(:unit :op :bound (:profile :o) :why "again"))))))
(fn2-resource-rejects :order-no-why
  (fn2-resource-order-p
   (append *fn2-resource-order* (list '(:extra :unit :op :bound (:profile :o))))))

(defun fn2-resource-test-bundle (acquires holds reserve transition)
  (declare (xargs :guard t))
  (list (list 'fn2-test transition) :acquires acquires :holds holds :reserve reserve
        :status :exists :owed-by nil :why "fixture"))
(defmacro fn2-resource-bundle-ok (acquires holds reserve transition)
  `(fn2-resource-bundle-p (fn2-resource-test-bundle ',acquires ',holds ',reserve ',transition)
                          *fn2-resource-order* *fn2-resource-reserves*))

; (b)/(c) bundles: the control is accepted, each defect refused.
(assert-event (fn2-resource-bundle-ok (:rx-range :operation) (:connection-row) nil :receive))
(fn2-resource-rejects :bundle-descends (fn2-resource-bundle-ok (:operation :rx-range) nil nil :receive))
(fn2-resource-rejects :bundle-tie (fn2-resource-bundle-ok (:rx-range :rx-range) nil nil :receive))
(fn2-resource-rejects :holds-above-first
  (fn2-resource-bundle-ok (:rx-range :operation) (:tls-slot) nil :receive))
(fn2-resource-rejects :holds-equal-first
  (fn2-resource-bundle-ok (:rx-range :operation) (:rx-range) nil :receive))
(fn2-resource-rejects :unknown-kind (fn2-resource-bundle-ok (:bogus) nil nil :receive))
(fn2-resource-rejects :unknown-held (fn2-resource-bundle-ok (:operation) (:bogus) nil :receive))
; (e) protected transitions draw a reserve covering the whole bundle.
(assert-event (fn2-resource-bundle-ok (:operation) (:connection-row) :close :close))
(fn2-resource-rejects :close-unreserved (fn2-resource-bundle-ok (:operation) nil nil :close))
(fn2-resource-rejects :fence-reserve-short (fn2-resource-bundle-ok (:fence-slot :operation) nil :close :fence))
(fn2-resource-rejects :wrong-reserve (fn2-resource-bundle-ok (:operation) nil :system :arm-wake))
; No unit an issue reserve covers is held while waiting.
(fn2-resource-rejects :reserve-held-while-waiting
  (fn2-resource-bundle-ok (:operation) (:fence-slot) :close :close))
(fn2-resource-rejects :duplicate-bundle
  (fn2-resource-bundles-p (append *fn2-resource-bundles* (list (car *fn2-resource-bundles*)))
                          *fn2-resource-order* *fn2-resource-reserves*))
(fn2-resource-rejects :bad-owed-by
  (fn2-resource-bundles-p
   (list (list '(fn2-test :receive) :acquires '(:operation) :holds nil :reserve nil
               :status :exists :owed-by :someone :why "fixture"))
   *fn2-resource-order* *fn2-resource-reserves*))

; (d) release lists descend; a refusal releases nothing.
(fn2-resource-rejects :release-ascends
  (fn2-resource-releases-p '(((fn2-test :close) :releases (:connection-row :operation)))
                           *fn2-resource-order*))
(fn2-resource-rejects :refusal-releases
  (fn2-resource-releases-p '(((fn2-test :refusal) :releases (:operation))) *fn2-resource-order*))

; (e) reserves name known kinds once.
(fn2-resource-rejects :reserve-unknown-kind
  (fn2-resource-reserves-p '((:close :covers (:bogus) :issue t :why "x")) *fn2-resource-order*))
(fn2-resource-rejects :reserve-duplicate
  (fn2-resource-reserves-p (cons (car *fn2-resource-reserves*) *fn2-resource-reserves*)
                           *fn2-resource-order*))

; (f) no per-recipient debt in a batch; no membership after publish.
(fn2-resource-rejects :batch-holds-recipient
  (fn2-resource-batch-phases-p '((:collect :holds (:batch-membership :wait-row) :after-publish nil))
                               *fn2-resource-order* *fn2-resource-per-recipient*))
(fn2-resource-rejects :membership-after-publish
  (fn2-resource-batch-phases-p '((:notify :holds (:batch-membership) :after-publish t))
                               *fn2-resource-order* *fn2-resource-per-recipient*))

; Effects: transfer and release only what is held; acquisitions ascend.
(assert-event (fn2-resource-effects-p
               '(((fn2-listener :admit) :holds-before (:accept-credit :connection-row)
                  :effects ((:transfer (:connection-row) :to fn2-echo) (:acquire (:rx-range) :for fn2-echo))))
               *fn2-resource-order*))
(fn2-resource-rejects :transfer-unheld
  (fn2-resource-effects-p '(((fn2-test :admit) :holds-before (:accept-credit)
                             :effects ((:transfer (:connection-row) :to fn2-echo))))
                          *fn2-resource-order*))
(fn2-resource-rejects :acquire-below-held
  (fn2-resource-effects-p '(((fn2-test :admit) :holds-before (:rx-range)
                             :effects ((:acquire (:connection-row)))))
                          *fn2-resource-order*))
(fn2-resource-rejects :release-unheld-after-transfer
  (fn2-resource-effects-p '(((fn2-test :admit) :holds-before (:accept-credit :connection-row)
                             :effects ((:transfer (:connection-row) :to fn2-echo)
                                       (:release (:connection-row)))))
                          *fn2-resource-order*))
(fn2-resource-rejects :unknown-effect
  (fn2-resource-effects-p '(((fn2-test :admit) :holds-before (:accept-credit)
                             :effects ((:borrow (:connection-row)))))
                          *fn2-resource-order*))

; Interim A holds and wait reasons.
(fn2-resource-rejects :holds-unknown
  (fn2-resource-machine-holds-p '((fn2-test (:free :bogus))) *fn2-resource-order*))
(fn2-resource-rejects :wait-reason-unknown
  (fn2-resource-wait-reasons-p '((:op-credit . :bogus)) *fn2-resource-order*))

; (g) The proved lemma has a subject: an unranked pair of waiters, each
; holding what the other awaits, is a cycle, and the ranked check refuses it.
(defconst *fn2-resource-test-cycle*
  '(((:rx-range) . :connection-row) ((:connection-row) . :rx-range)))
(assert-event (fn2-resource-cyclep *fn2-resource-test-cycle*))
(fn2-resource-rejects :cycle-ranked
  (fn2-resource-waiters-ranked-p *fn2-resource-test-cycle* *fn2-resource-order*))
(assert-event (fn2-resource-waiters-ranked-p
               '(((:connection-row :rx-range) . :operation) ((:accept-credit) . :connection-row))
               *fn2-resource-order*))

; Extensible declarations: defresource, defservice, defaction, fn2-assemble.
(assert-event
 (let ((ord (fn2-resource-assembled-order (w state))))
   (and (fn2-resource-order-p ord)
        (posp (fn2-resource-rank :successor-workspace ord))
        (< (fn2-resource-rank :identity-reservation ord)
           (fn2-resource-rank :successor-workspace ord))
        (< (fn2-resource-rank :successor-workspace ord)
           (fn2-resource-rank :cursor-row ord))
        (assoc-eq :timer (table-alist 'fn2-services (w state)))
        (assoc-eq :connect (table-alist 'fn2-actions (w state)))
        (assoc-eq :timer (table-alist 'fn2-actions (w state)))
        (assoc-eq 'fn2-probe-app (table-alist 'fn2-app-manifests (w state))))))

; Every service (:ready, :step) and action (:issue) registered in resources.lisp
; names a defined, guard-verified :common-lisp-compliant function (no dangling stubs).
(defun fn2-resource-plist-get (k xs)
  (declare (xargs :guard t))
  (if (or (atom xs) (atom (cdr xs)))
      nil
    (if (equal (car xs) k)
        (cadr xs)
      (fn2-resource-plist-get k (cddr xs)))))

(defun fn2-resource-service-fns (rows)
  (declare (xargs :guard t))
  (if (atom rows) nil
    (let ((plist (and (consp (car rows)) (cdar rows))))
      (list* (fn2-resource-plist-get :ready plist)
             (fn2-resource-plist-get :step plist)
             (fn2-resource-service-fns (cdr rows))))))

(defun fn2-resource-action-fns (rows)
  (declare (xargs :guard t))
  (if (atom rows) nil
    (let ((plist (and (consp (car rows)) (cdar rows))))
      (cons (fn2-resource-plist-get :issue plist)
            (fn2-resource-action-fns (cdr rows))))))

(assert-event
 (fn2-assert-compliant-p
  (append (fn2-resource-service-fns (table-alist 'fn2-services (w state)))
          (fn2-resource-action-fns (table-alist 'fn2-actions (w state))))
  (w state)))

; Outbound :connect end-to-end check: refusal frames on invalid peer records,
; reservation + outbox submission, ConnectResult completion, and latched peer observation.
(defun fn2-resource-test-connect-run (fn2-pool fn2-ops fn2-control)
  (declare (xargs :stobjs (fn2-pool fn2-ops fn2-control) :verify-guards nil))
  (b* ((fn2-pool (fn2-pool-init *fn2-profile-tiny* fn2-pool))
       (fn2-ops (fn2-ops-init *fn2-profile-tiny* fn2-ops))
       (fn2-control (fn2-control-init *fn2-profile-tiny* fn2-control))
       (free0 (fn2-ops-free-count fn2-ops))
       ((mv bad1 & & fn2-pool fn2-ops fn2-control)
        (fn2-issue-connect *fn2-peer-family-none* 0 0 0 0 0 1 2 3 0 fn2-pool fn2-ops fn2-control))
       ((mv bad2 & & fn2-pool fn2-ops fn2-control)
        (fn2-issue-connect *fn2-peer-family-inet* 119 #x7f000001 99 0 0 1 2 3 0 fn2-pool fn2-ops fn2-control))
       (unchanged (and (= (fn2-ops-free-count fn2-ops) free0)
                       (= (fn2-ops-queued fn2-ops) 0)
                       (= (fn2-control-stop fn2-control) 0)))
       ((mv ok opslot opgen fn2-pool fn2-ops fn2-control)
        (fn2-issue-connect *fn2-peer-family-inet* 119 #x7f000001 0 0 0 1 2 3 0 fn2-pool fn2-ops fn2-control))
       ((mv ack fn2-ops) (fn2-outbox-ack 1 fn2-ops))
       (fn2-ops (fn2-post-result 0 opslot opgen *fn2-event-connect-result*
                                 *fn2-outcome-done* *fn2-reason-none* 0 4 7 fn2-ops))
       ((mv found hslot hgen hcell fn2-ops) (fn2-harvest-next fn2-ops))
       ((mv pf pp pw0 pw1 pw2 pw3) (fn2-ops-observed-peer fn2-ops)))
    (mv (and (eq bad1 :bounds) (eq bad2 :bounds) unchanged
             (eq ok :ok) (eq ack :ok) (eq found t)
             (= hslot opslot) (= hgen opgen) (= hcell 0)
             (= pf *fn2-peer-family-inet*) (= pp 119)
             (= pw0 #x7f000001) (= pw1 0) (= pw2 0) (= pw3 0)
             (= (fn2-control-stop fn2-control) 0))
        fn2-pool fn2-ops fn2-control)))

(defun fn2-resource-test-connect ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-pool
    (mv-let (ok fn2-pool)
      (with-local-stobj fn2-ops
        (mv-let (ok fn2-pool fn2-ops)
          (with-local-stobj fn2-control
            (mv-let (ok fn2-pool fn2-ops fn2-control)
              (fn2-resource-test-connect-run fn2-pool fn2-ops fn2-control)
              (mv ok fn2-pool fn2-ops)))
          (mv ok fn2-pool)))
      ok)))
(assert-event (fn2-resource-test-connect))
