; fn: the host lease's premises (Builder A): every predicate a runtime-contract keystone assumes at a host
; entry, established of what the host lease's drivers (books/runtime-contract-host-lease.lisp fn-hld-*)
; return, so the contract's keystones speak of the running node's states (tools/premise_audit.py).
(in-package "ACL2")
(include-book "runtime-contract-host-lease")
(include-book "runtime-contract-host-lease-run")
(include-book "runtime-contract-isolation")
(include-book "runtime-contract-keystones")
; --- Local proof steps (none is a statement; none is cited downstream).
(local (defthm fn-hlp-shapep-pool-shapep
  (implies (fn-rtc-shapep s) (fn-rtc-pool-shapep 0 (fn-rtc-pool s) (fn-rtc-config s)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-shapep) (theory 'minimal-theory))))))
(local (defthm fn-hlp-invp-pieces
  (implies (fn-rtc-invp s)
           (and (fn-rtc-invp s) (fn-rtc-core-invp s) (fn-rtc-st-p s) (fn-rtc-shapep s)
                (fn-rtc-mstates-okp (fn-rtc-mstates s))
                (fn-rtc-slots-okp 0 (fn-rtc-slots s))
                (fn-rtc-statics-okp 1 (fn-rtc-nstatic (fn-rtc-config s)) (fn-rtc-slots s))
                (fn-rtc-pool-okp 0 (fn-rtc-pool s) s)
                (fn-rtc-pool-shapep 0 (fn-rtc-pool s) (fn-rtc-config s))
                (fn-rtc-draining-okp 0 (fn-rtc-slots s) (fn-rtc-uses s))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-core-invp)
                                             (theory 'minimal-theory))
           :use (fn-rtc-invp-implies-core-invp fn-rtc-invp-implies-st-p (:instance fn-rtc-st-p-is-shapep (x s))
                 fn-hlp-shapep-pool-shapep)))))
(local (defthm fn-hlp-hll-invp-pieces
  (implies (fn-hll-invp s)
           (and (fn-rtc-invp s) (fn-rtc-core-invp s) (fn-rtc-st-p s) (fn-rtc-shapep s)
                (fn-rtc-mstates-okp (fn-rtc-mstates s))
                (fn-rtc-slots-okp 0 (fn-rtc-slots s))
                (fn-rtc-statics-okp 1 (fn-rtc-nstatic (fn-rtc-config s)) (fn-rtc-slots s))
                (fn-rtc-pool-okp 0 (fn-rtc-pool s) s)
                (fn-rtc-pool-shapep 0 (fn-rtc-pool s) (fn-rtc-config s))
                (fn-rtc-draining-okp 0 (fn-rtc-slots s) (fn-rtc-uses s))))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use (fn-hlp-invp-pieces fn-hld-hll-invp-is-generic-invp)))))
(local (defthm fn-hlp-workspace-facts
  (implies (fn-hld-workspace h id inc st)
           (and (natp (fn-hld-workspace h id inc st))
                (< (fn-hld-workspace h id inc st) (fn-rtc-nbufs (fn-rtc-config st)))
                (equal (fn-rtc-b-owner (fn-rtc-buffer (fn-hld-workspace h id inc st) st)) (list :workspace id inc))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-hld-workspace h id inc st)
           :in-theory (union-theories '(fn-hld-workspace fn-hld-readers natp nfix (:type-prescription fn-rtc-nbufs))
                                      (theory 'minimal-theory))))))
(local (defthm fn-hlp-use-handle-owner
  (implies (and (fn-rtc-use-okp u s) (member-eq (fn-rtc-get 0 u) '(:recv :pread :hand :pool)))
           (member-eq (fn-rtc-get 0 (fn-rtc-b-owner (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s))) '(:leased :handed)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-use-okp fn-rtc-usep (:e fn-rtc-handlep) (:e member-equal) member-equal (:e member-eq) member-eq (:e fn-rtc-h-buf) (:e fn-rtc-h-gen) (:e fn-rtc-get) iff
                                               (:e fn-rtc-u-hd) fn-rtc-u-hd (:e fn-rtc-b-owner) (:e fn-rtc-buffer))
                                             (theory 'minimal-theory))))))
(local (defun fn-hlp-ind (u) (declare (xargs :guard t)) (if (consp u) (fn-hlp-ind (cdr u)) u)))
(local (defthm fn-hlp-workspace-has-no-handle-holder
  (implies (and (fn-rtc-uses-okp uses s) (natp h)
                (equal (fn-rtc-get 0 (fn-rtc-b-owner (fn-rtc-buffer h s))) :workspace))
           (fn-rtc-compatible-usesp (list :send id inc op (list h g 0 n)) uses))
  :rule-classes nil
  :hints (("Goal" :induct (fn-hlp-ind uses)
           :in-theory (union-theories '((:induction fn-hlp-ind) fn-rtc-compatible-usesp fn-rtc-compatible-use-p fn-rtc-uses-okp
                                        fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e binary-+) (:e unary--)
                                        fn-rtc-u-hd fn-rtc-h-buf (:e member-eq) member-eq natp nfix
                                        (:e consp) (:e equal) (:e fn-rtc-u-hd) (:e fn-rtc-h-buf))
                                      (theory 'minimal-theory)))
          ("Subgoal *1/1" :use ((:instance fn-hlp-use-handle-owner (u (car uses))))))))
(local (defthm fn-hlp-invp-uses-okp
  (implies (fn-rtc-invp s) (fn-rtc-uses-okp (fn-rtc-uses s) s))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-core-invp) (theory 'minimal-theory))
           :use fn-rtc-invp-implies-core-invp))))
(local (defthm fn-hlp-send-prep
  (implies (and (fn-rtc-invp st) (fn-dss-out-p out) (fn-hl-render-ready-p h id inc st)
                (<= (len out) (fn-rtc-buf-cap h (fn-rtc-config st))))
           (let ((p (fn-rtc-st$a-puts h 0 out st))
                 (hd (list h (fn-rtc-b-gen (fn-rtc-buffer h st)) 0 (len out))))
             (and (fn-rtc-submit-okp :send hd id inc p)
                  (equal (fn-rtc-uses p) (fn-rtc-uses st))
                  (fn-rtc-compatible-usesp (list :send id inc (fn-rtc-next-op st) hd) (fn-rtc-uses st)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hl-render-ready-p fn-hlr-puts-frame fn-hlr-puts-len2 fn-hlr-submit-okp-send fn-hlr-buffer-facts
                                               fn-hlr-pool-len-facts fn-hlr-len-nonneg fn-hlr-natp-len fn-dss-out-p-is-octet-listp natp (:e natp)
                                               fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) zp nfix)
                                             (theory 'minimal-theory))
           :use ((:instance fn-hlr-submit-okp-send (p (fn-rtc-st$a-puts h 0 out st)) (g (fn-rtc-b-gen (fn-rtc-buffer h st))) (n (len out)))
                 (:instance fn-hlr-puts-len2 (off 0) (w out) (s st))
                 fn-hlr-pool-len-facts fn-hlr-buffer-facts
                 (:instance fn-hlp-invp-uses-okp (s st))
                 (:instance fn-hlp-workspace-has-no-handle-holder (uses (fn-rtc-uses st)) (s st) (op (fn-rtc-next-op st))
                            (g (fn-rtc-b-gen (fn-rtc-buffer h st))) (n (len out))))))))
(local (defun fn-hlp-nth-ind (k l) (declare (xargs :verify-guards nil)) (if (or (zp k) (atom l)) (list k l) (fn-hlp-nth-ind (- k 1) (cdr l)))))
(local (defthm fn-hlp-compat-nth
  (implies (fn-rtc-compatible-usesp new uses) (fn-rtc-compatible-use-p new (nth k uses)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-hlp-nth-ind k uses)
           :in-theory (union-theories '((:induction fn-hlp-nth-ind) fn-rtc-compatible-usesp nth fn-rtc-compatible-use-p fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e member-eq) (:e zp) zp)
                                      (theory 'minimal-theory))))))
(local (defthm fn-hlp-quantum-ok-consp
  (implies (and (fn-hll-invp st) (fn-dss-out-p out) (mv-nth 1 (fn-hld-quantum h id inc out st)))
           (consp out))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use (fn-hlr-quantum-empty (:instance fn-hld-hll-invp-st-p (s st)))))))
(local (defthm fn-hlp-quantum-ok-conditions
  (implies (and (fn-hll-invp st) (fn-dss-out-p out) (mv-nth 1 (fn-hld-quantum h id inc out st)))
           (and (fn-rtc-invp st) (fn-rtc-st-p st) (consp out)
                (equal (mv-nth 1 (fn-hld-quantum h id inc out st)) (fn-rtc-next-op st))
                (fn-hl-render-ready-p h id inc st)
                (fn-rtc-live-p id inc st)
                (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses st)))
                (<= (len out) (fn-rtc-buf-cap h (fn-rtc-config st)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use (fn-hlp-quantum-ok-consp fn-hld-quantum-is-the-quantum-state
                 (:instance fn-hld-hll-invp-st-p (s st))
                 (:instance fn-hld-hll-invp-is-generic-invp (s st))
                 (:instance fn-dss-out-p-is-octet-listp (x out)))))))
(local (defthm fn-hlp-quantum-facts
  (implies (and (fn-hll-invp st) (fn-dss-out-p out) (mv-nth 1 (fn-hld-quantum h id inc out st)))
           (let ((q (mv-nth 0 (fn-hld-quantum h id inc out st)))
                 (op (mv-nth 1 (fn-hld-quantum h id inc out st))))
             (and (natp id) (natp inc) (natp op)
                  (fn-rtc-live-p id inc q)
                  (equal (fn-rtc-uses q)
                         (cons (list :send id inc op (list h (fn-rtc-b-gen (fn-rtc-buffer h st)) 0 (len out)))
                               (fn-rtc-uses st))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hl-render-ready-p) (theory 'minimal-theory))
           :use (fn-hlp-quantum-ok-conditions
                 (:instance fn-hlr-quantum-succeeds)
                 (:instance fn-hlr-ws-posp-id (s st)) (:instance fn-hlr-live-natp-inc (s st))
                 (:instance fn-hlr-posp-natp (x id))
                 (:instance fn-hlr-next-op-natp (s st))
                 (:instance fn-hlr-slot-of-slots (a (mv-nth 0 (fn-hld-quantum h id inc out st))) (b st))
                 (:instance fn-hlr-live-via-slot (s st) (s2 (mv-nth 0 (fn-hld-quantum h id inc out st)))))))))
(local (defthm fn-hlp-sent-event-completion-aux
  (implies (and (natp id) (natp inc) (natp op) (fn-rtc-outcomep outcome))
           (fn-rtc-completionp (fn-hld-sent-event id inc op outcome)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hld-sent-event fn-rtc-completionp fn-rtc-outcomep fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e binary-+) (:e unary--) (:e member-eq) (:e fn-rtc-get) (:e len) (:e equal) true-listp len) (theory 'minimal-theory))))))
(local (defthm fn-hlp-sent-event-acts-on-send
  (implies (and (equal (fn-rtc-uses q) (cons (list :send id inc op x) uses0))
                (natp id) (natp inc) (natp op) (fn-rtc-outcomep o) (fn-rtc-live-p id inc q))
           (and (fn-rtc-acts-on-p q (fn-hld-sent-event id inc op o))
                (fn-rtc-ends-use-p (fn-hld-sent-event id inc op o)
                                   (fn-rtc-find-use (fn-rtc-key (fn-hld-sent-event id inc op o)) (fn-rtc-uses q)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hld-sent-event fn-rtc-acts-on-p fn-rtc-ends-use-p fn-hlr-key-of-send fn-hlr-find-use-send fn-rtc-live-p
                                               fn-rtc-e-id fn-rtc-e-inc fn-rtc-e-kind fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) zp nfix natp
                                               (:e equal))
                                             (theory 'minimal-theory))
           :use ((:instance fn-hlp-sent-event-completion-aux (outcome o))
                 (:instance fn-hlr-find-use-send (uses0 uses0)))))))
(local (defthm fn-hlp-kind-op-finds-use
  (implies (and (fn-rtc-kind-out-p kind id inc uses) (fn-rtc-uses-ops-natp uses))
           (fn-rtc-find-use (list kind id inc (fn-rtc-kind-op kind id inc uses)) uses))
  :rule-classes nil
  :hints (("Goal" :induct (fn-rtc-kind-op kind id inc uses)
           :in-theory (union-theories '(fn-rtc-kind-op fn-rtc-kind-out-p fn-rtc-find-use fn-rtc-key fn-rtc-uses-ops-natp
                                        fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e binary-+) (:e unary--) natp nfix)
                                      (theory 'minimal-theory))))))
(local (defthm fn-hlp-kind-op-natp
  (natp (fn-rtc-kind-op kind id inc uses))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn-rtc-kind-op)))))
(local (defthm fn-hlp-accept-acts-on
  (implies (and (fn-rtc-invp s) (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s)) (natp r))
           (fn-rtc-acts-on-p s (list :accept 0 0 (fn-rtc-kind-op :accept 0 0 (fn-rtc-uses s)) (list :done r))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-acts-on-p fn-rtc-completionp fn-rtc-outcomep fn-rtc-e-id fn-rtc-e-inc fn-rtc-e-kind
                                               fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e binary-+) (:e unary--)
                                               (:e member-eq) member-eq (:e len) len (:e true-listp) true-listp (:e equal) natp
                                               (:type-prescription nfix) (:e consp) fn-rtc-s-inc fn-rtc-s-status fn-hlp-kind-op-natp fn-rtc-key)
                                             (theory 'minimal-theory))
           :use (fn-rtc-invp-listener fn-rtc-invp-ops-natp
                 (:instance fn-hlp-kind-op-finds-use (kind :accept) (id 0) (inc 0) (uses (fn-rtc-uses s))))))))
(local (defthm fn-hlp-find-use-kind
  (implies (fn-rtc-find-use key uses)
           (equal (fn-rtc-get 0 (fn-rtc-find-use key uses)) (fn-rtc-get 0 key)))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-key fn-rtc-get-of-cons car-cons cdr-cons (:e zp) (:e nfix))
                                             (theory 'minimal-theory))
           :use ((:instance fn-rtc-key-of-find-use (k key)))))))
(local (defthm fn-hlp-accept-use-hd-nil
  (implies (and (fn-rtc-invp s) (fn-rtc-find-use key (fn-rtc-uses s)) (equal (fn-rtc-get 0 key) :accept))
           (equal (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s))) nil))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-use-okp fn-rtc-usep (:e member-eq) member-eq (:e fn-rtc-get) fn-rtc-u-hd fn-hlp-find-use-kind)
                                             (theory 'minimal-theory))
           :use (fn-rtc-invp-uses-okp
                 (:instance fn-rtc-uses-okp-member (uses (fn-rtc-uses s)) (s s) (u (fn-rtc-find-use key (fn-rtc-uses s))))
                 (:instance fn-rtc-find-use-is-member (k key) (uses (fn-rtc-uses s)))
                 (:instance fn-rtc-key-of-find-use (k key) (uses (fn-rtc-uses s))))))))
(local (defthm fn-hlp-end-lease-no-hd
  (implies (not (fn-rtc-handlep (fn-rtc-u-hd u))) (equal (fn-rtc-end-lease u e s) s))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-end-lease) (theory 'minimal-theory))))))
(local (defthm fn-hlp-retire-live
  (implies (not (equal (fn-rtc-s-status (fn-rtc-slot id s)) :draining)) (equal (fn-rtc-retire-drained id s) s))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-retire-drained) (theory 'minimal-theory))))))
(local (defthm fn-hlp-accept-event-facts
  (implies (and (fn-rtc-invp s) (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s)) (natp r))
           (let ((e (list :accept 0 0 (fn-rtc-kind-op :accept 0 0 (fn-rtc-uses s)) (list :done r))))
             (and (fn-rtc-completionp e)
                  (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-completionp fn-rtc-outcomep fn-rtc-key
                                               fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e binary-+) (:e unary--)
                                               (:e member-eq) member-eq (:e len) len (:e true-listp) true-listp (:e equal) natp
                                               (:type-prescription nfix) (:e consp) fn-hlp-kind-op-natp)
                                             (theory 'minimal-theory))
           :use (fn-rtc-invp-ops-natp
                 (:instance fn-hlp-kind-op-finds-use (kind :accept) (id 0) (inc 0) (uses (fn-rtc-uses s))))))))
(local (defthm fn-hlp-accept-end-use
  (implies (and (fn-rtc-invp s) (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s)) (natp r))
           (let* ((e (list :accept 0 0 (fn-rtc-kind-op :accept 0 0 (fn-rtc-uses s)) (list :done r)))
                  (s1 (fn-rtc-end-use s e)))
             (and (equal (fn-rtc-slots s1) (fn-rtc-slots s))
                  (equal (fn-rtc-pool s1) (fn-rtc-pool s))
                  (equal (fn-rtc-config s1) (fn-rtc-config s))
                  (equal (fn-rtc-mstates s1) (fn-rtc-mstates s))
                  (equal (fn-rtc-next-op s1) (fn-rtc-next-op s))
                  (equal (fn-rtc-uses s1) (fn-rtc-remove-use (fn-rtc-key e) (fn-rtc-uses s))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-with-accessors fn-hlp-end-lease-no-hd fn-hlp-retire-live fn-rtc-e-id fn-rtc-s-status fn-rtc-key (:e fn-rtc-handlep) fn-rtc-slot-of-with fn-rtc-next-op-of-with
                                               fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e binary-+) (:e unary--)
                                               (:e member-eq))
                                             (theory 'minimal-theory))
           :use ((:instance fn-hlp-accept-event-facts)
                 (:instance fn-hlp-accept-use-hd-nil (key (fn-rtc-key (list :accept 0 0 (fn-rtc-kind-op :accept 0 0 (fn-rtc-uses s)) (list :done r)))))
                 (:instance fn-rtc-end-use-structure (e (list :accept 0 0 (fn-rtc-kind-op :accept 0 0 (fn-rtc-uses s)) (list :done r))))
                 fn-rtc-invp-listener)))))
(local (defthm fn-hlp-step-accept-parts
  (implies (and (fn-rtc-acts-on-p s e) (equal (fn-rtc-get 0 e) :accept))
           (and (equal (mv-nth 0 (fn-hll-step* s e q))
                       (mv-nth 0 (fn-hll-accept-branch (fn-rtc-end-use s e)
                                                       (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e) q)))
                (equal (mv-nth 1 (fn-hll-step* s e q))
                       (mv-nth 1 (fn-hll-accept-branch (fn-rtc-end-use s e)
                                                       (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e) q)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hll-step* fn-rtc-hand-delivers-p fn-rtc-e-kind mv-nth (:e mv-nth) (:e eq) eq)
                                             (theory 'minimal-theory))))))
(local (defun fn-hlp-acc-j (s1) (declare (xargs :guard t :verify-guards nil)) (fn-rtc-free-slot 0 (fn-rtc-slots s1))))
(local (defun fn-hlp-acc-jinc (s1) (declare (xargs :guard t :verify-guards nil)) (+ 1 (fn-rtc-s-inc (fn-rtc-slot (fn-hlp-acc-j s1) s1)))))
(local (defun fn-hlp-acc-prep (s1 r)
  (declare (xargs :guard t :verify-guards nil))
  (fn-rtc-with-mstate (fn-hlp-acc-j s1) (fn-hlm-init)
                      (fn-rtc-with-slot (fn-hlp-acc-j s1) (list (fn-hlp-acc-jinc s1) :live r) s1))))
(local (defun fn-hlp-acc-deliver (s1 r q)
  (declare (xargs :guard t :verify-guards nil))
  (fn-hll-deliver (fn-hlp-acc-prep s1 r) (fn-hlp-acc-j s1) (fn-hlp-acc-jinc s1)
                  (fn-rtc-ev :accept (list :done r) (fn-hlp-acc-j s1) (fn-hlp-acc-jinc s1) nil) q)))
(local (defthm fn-hlp-accept-branch-go-parts
  (implies (and (fn-hlp-acc-j s1) (natp r) (< r (expt 2 64)))
           (and (equal (mv-nth 1 (fn-hll-accept-branch s1 (list :done r) q))
                       (append (mv-nth 1 (fn-hlp-acc-deliver s1 r q))
                               (mv-nth 1 (fn-rtc-rearm (mv-nth 0 (fn-hlp-acc-deliver s1 r q))))))
                (equal (mv-nth 0 (fn-hll-accept-branch s1 (list :done r) q))
                       (mv-nth 0 (fn-rtc-rearm (mv-nth 0 (fn-hlp-acc-deliver s1 r q)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-rtc-free-slot-has-incarnation-room (i 0) (slots (fn-rtc-slots s1)))
                 (:instance fn-rtc-free-slot-index-type (i 0) (slots (fn-rtc-slots s1))))
           :in-theory (union-theories '(fn-hll-accept-branch fn-hlp-acc-deliver fn-hlp-acc-prep fn-hlp-acc-jinc fn-hlp-acc-j fn-hlm-init
                                        fn-rtc-slot unicity-of-0 commutativity-of-+ fix posp
                                        fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e binary-+) (:e unary--) natp mv-nth (:e mv-nth))
                                      (theory 'minimal-theory))))))
(local (defthm fn-hlp-deliver-accept
  (implies (equal (fn-rtc-get 0 ev) :accept)
           (and (equal (mv-nth 0 (fn-hll-deliver s id inc ev q))
                       (mv-nth 0 (fn-rtc-requests '((:submit :pool nil nil)) id inc (fn-rtc-with-mstate id nil s))))
                (equal (mv-nth 1 (fn-hll-deliver s id inc ev q))
                       (mv-nth 1 (fn-rtc-requests '((:submit :pool nil nil)) id inc (fn-rtc-with-mstate id nil s))))
                (equal (mv-nth 2 (fn-hll-deliver s id inc ev q))
                       (mv-nth 2 (fn-rtc-requests '((:submit :pool nil nil)) id inc (fn-rtc-with-mstate id nil s))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hll-deliver fn-hll-m-step fn-hlm-step mv-nth (:e mv-nth) (:e fn-rtc-get) fn-rtc-requests)
                                             (theory 'minimal-theory))))))
(local (defthm fn-hlp-request-pool
  (implies (and (fn-rtc-live-p id inc s) (not (fn-rtc-kind-out-p :wait id inc (fn-rtc-uses s))))
           (and (equal (mv-nth 0 (fn-rtc-requests '((:submit :pool nil nil)) id inc s))
                       (fn-rtc-issue (list :wait id inc (fn-rtc-next-op s) nil) s))
                (equal (mv-nth 1 (fn-rtc-requests '((:submit :pool nil nil)) id inc s)) nil)
                (equal (mv-nth 2 (fn-rtc-requests '((:submit :pool nil nil)) id inc s)) nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-requests fn-rtc-request fn-rtc-req-submit fn-rtc-kind-extrap fn-rtc-extrap
                                               mv-nth (:e mv-nth) (:e fn-rtc-get) fn-rtc-get-of-cons car-cons cdr-cons (:e member-eq) member-eq
                                               (:e zp) (:e nfix) (:e binary-+) (:e unary--) (:e equal) (:e eq) eq append (:e append) (:e len) len (:e <))
                                             (theory 'minimal-theory))))))
(local (defthm fn-hlp-use-slot-not-free
  (implies (and (fn-rtc-use-okp u s) (equal (fn-rtc-get 1 u) j) (natp j))
           (not (equal (fn-rtc-s-status (fn-rtc-slot j s)) :free)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-use-okp fn-rtc-current-p natp nfix) (theory 'minimal-theory))))))
(local (defthm fn-hlp-free-slot-no-use
  (implies (and (fn-rtc-uses-okp uses s) (natp j) (equal (fn-rtc-s-status (fn-rtc-slot j s)) :free))
           (not (fn-rtc-kind-out-p kind j inc uses)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-hlr-ind uses)
           :in-theory (union-theories '((:induction fn-hlr-ind) fn-rtc-uses-okp fn-rtc-kind-out-p) (theory 'minimal-theory)))
          ("Subgoal *1/1" :use ((:instance fn-hlp-use-slot-not-free (u (car uses))))))))
(local (defthm fn-hlp-landed-accept
  (implies (equal (fn-rtc-get 0 e) :accept)
           (equal (fn-rtc-landed e s) e))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-landed fn-hlp-find-use-kind fn-rtc-key fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix)
                                               (:e member-eq) member-eq)
                                             (theory 'minimal-theory))))))
(local (defun fn-hlp-bev (st r)
  (declare (xargs :guard t :verify-guards nil))
  (list :accept 0 0 (fn-rtc-kind-op :accept 0 0 (fn-rtc-uses st)) (list :done r))))
(local (defthm fn-hlp-begin-parts
  (implies (and (natp r) (< r (expt 2 64)) (fn-rtc-free-slot 0 (fn-rtc-slots st))
                (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses st)))
           (let ((sa (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st)))
                 (acts (mv-nth 1 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))))
             (and (equal (mv-nth 0 (fn-hld-begin r st))
                         (mv-nth 0 (fn-hld-settle (true-list-fix acts) (fn-hld-fuel sa) sa)))
                  (equal (mv-nth 1 (fn-hld-begin r st)) (fn-rtc-free-slot 0 (fn-rtc-slots st)))
                  (equal (mv-nth 2 (fn-hld-begin r st))
                         (+ 1 (fn-rtc-s-inc (fn-rtc-slot (fn-rtc-free-slot 0 (fn-rtc-slots st)) st)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hld-begin fn-hlp-bev fn-rtc-st-free-slot fn-rtc-st$a-free-slot fn-hld-readers fn-rtc-st-slot fn-rtc-st$a-slot
                                               fn-rtc-slot unicity-of-0 commutativity-of-+ fix posp (:e binary-+) (:e unary--)
                                               natp mv-nth (:e mv-nth) (:type-prescription fn-rtc-free-slot))
                                             (theory 'minimal-theory))
           :use ((:instance fn-rtc-free-slot-has-incarnation-room (i 0) (slots (fn-rtc-slots st)))
                 (:instance fn-rtc-free-slot-index-type (i 0) (slots (fn-rtc-slots st))))))))
(local (defun fn-hlp-accept-onlyp (acts)
  (declare (xargs :guard t))
  (if (consp acts)
      (and (equal (fn-rtc-get 0 (car acts)) :accept) (fn-hlp-accept-onlyp (cdr acts)))
    (null acts))))
(local (defthm fn-hlp-settle-accept-only
  (implies (fn-hlp-accept-onlyp work)
           (equal (mv-nth 0 (fn-hld-settle work fuel st)) st))
  :hints (("Goal" :induct (fn-hld-settle work fuel st)
           :in-theory (union-theories '((:induction fn-hld-settle) fn-hld-settle fn-hlp-accept-onlyp mv-nth (:e mv-nth) (:e member-eq) member-eq (:e equal))
                                      (theory 'minimal-theory))))))
(local (defthm fn-hlp-rearm-pool
  (equal (fn-rtc-pool (mv-nth 0 (fn-rtc-rearm s))) (fn-rtc-pool s))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-rearm fn-rtc-arm-accept fn-rtc-arm-grant fn-rtc-issue-frame mv-nth (:e mv-nth))
                                             (theory 'minimal-theory))))))
(local (defthm fn-hlp-rearm-wait
  (equal (fn-rtc-oldest-wait (fn-rtc-uses (mv-nth 0 (fn-rtc-rearm s)))) (fn-rtc-oldest-wait (fn-rtc-uses s)))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-rearm fn-rtc-arm-accept fn-rtc-arm-grant fn-rtc-issue-frame mv-nth (:e mv-nth)
                                               fn-rtc-oldest-wait-cons-other fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e binary-+) (:e unary--))
                                             (theory 'minimal-theory))))))
(local (defthm fn-hlp-rearm-accept-only
  (implies (not (and (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s))
                     (fn-rtc-oldest-wait (fn-rtc-uses s))
                     (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses s)))))
           (fn-hlp-accept-onlyp (mv-nth 1 (fn-rtc-rearm s))))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-rearm fn-rtc-arm-accept fn-rtc-arm-grant fn-rtc-issue-frame mv-nth (:e mv-nth)
                                               fn-rtc-oldest-wait-cons-other fn-rtc-kind-out-cons fn-hlp-accept-onlyp append (:e append)
                                               fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e binary-+) (:e unary--) (:e equal))
                                             (theory 'minimal-theory))))))
(local (defthm fn-hlp-remove-use-keeps-other-kind
  (implies (and (fn-rtc-kind-out-p k id inc uses) (not (equal k (fn-rtc-get 0 key))))
           (fn-rtc-kind-out-p k id inc (fn-rtc-remove-use key uses)))
  :hints (("Goal" :induct (fn-rtc-remove-use key uses)
           :in-theory (union-theories '((:induction fn-rtc-remove-use) fn-rtc-remove-use fn-rtc-kind-out-p fn-rtc-key
                                        fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix))
                                      (theory 'minimal-theory))))))
(local (defthm fn-hlp-accept-j-free
  (implies (and (fn-rtc-invp st) (equal j (fn-rtc-free-slot 0 (fn-rtc-slots st))) j)
           (and (posp j) (< j (len (fn-rtc-slots st)))
                (equal (fn-rtc-s-status (fn-rtc-slot j st)) :free)
                (not (fn-rtc-kind-out-p kind j inc (fn-rtc-uses st)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-slot fn-rtc-slots natp posp unicity-of-0 commutativity-of-+ fix (:e unary--) (:e binary-+))
                                             (theory 'minimal-theory))
           :use ((:instance fn-rtc-free-slot-result (i 0) (slots (fn-rtc-slots st)))
                 (:instance fn-hlp-free-slot-no-use (uses (fn-rtc-uses st)) (s st))
                 (:instance fn-rtc-invp-uses-okp (s st)))))))
(local (defthm fn-hlp-acc-prep-live
  (implies (and (fn-hlp-acc-j s1) (< (fn-hlp-acc-j s1) (len (fn-rtc-slots s1))))
           (fn-rtc-live-p (fn-hlp-acc-j s1) (fn-hlp-acc-jinc s1)
                          (fn-rtc-with-mstate (fn-hlp-acc-j s1) nil (fn-hlp-acc-prep s1 r))))
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-acc-prep fn-rtc-live-p fn-rtc-slot-of-with fn-rtc-s-inc fn-rtc-s-status
                                               fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e binary-+) (:e unary--)
                                               fn-hlp-acc-jinc natp posp (:type-prescription fn-hlp-acc-j) (:type-prescription fn-hlp-acc-jinc) (:type-prescription nfix) nfix fn-rtc-with-accessors fn-rtc-slots)
                                             (theory 'minimal-theory))))))
(local (defthm fn-hlp-accept-deliver-gen
  (implies (and (fn-hlp-acc-j s1) (< (fn-hlp-acc-j s1) (len (fn-rtc-slots s1)))
                (not (fn-rtc-kind-out-p :wait (fn-hlp-acc-j s1) (fn-hlp-acc-jinc s1) (fn-rtc-uses s1))))
           (and (equal (mv-nth 0 (fn-hlp-acc-deliver s1 r q))
                       (fn-rtc-issue (list :wait (fn-hlp-acc-j s1) (fn-hlp-acc-jinc s1) (fn-rtc-next-op s1) nil)
                                     (fn-rtc-with-mstate (fn-hlp-acc-j s1) nil (fn-hlp-acc-prep s1 r))))
                (equal (mv-nth 1 (fn-hlp-acc-deliver s1 r q)) nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-acc-deliver fn-rtc-ev fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e binary-+) (:e unary--)
                                               fn-rtc-with-accessors fn-hlp-acc-prep fn-rtc-next-op-of-with)
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance fn-hlp-deliver-accept (s (fn-hlp-acc-prep s1 r)) (id (fn-hlp-acc-j s1)) (inc (fn-hlp-acc-jinc s1))
                            (ev (fn-rtc-ev :accept (list :done r) (fn-hlp-acc-j s1) (fn-hlp-acc-jinc s1) nil)) (q q))
                 (:instance fn-hlp-request-pool (id (fn-hlp-acc-j s1)) (inc (fn-hlp-acc-jinc s1))
                            (s (fn-rtc-with-mstate (fn-hlp-acc-j s1) nil (fn-hlp-acc-prep s1 r))))
                 (:instance fn-hlp-acc-prep-live))))))
(local (defthm fn-hlp-accept-outcome
  (implies (and (equal (fn-rtc-get 0 u) :accept) (equal (fn-rtc-get 4 e) (list :done r)))
           (equal (fn-rtc-delivered-outcome u e) (list :done r)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-delivered-outcome fn-rtc-e-outcome fn-rtc-u-hd fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix)
                                               (:e member-eq) member-eq (:e equal))
                                             (theory 'minimal-theory))))))
(local (defun fn-hlp-dd (st r)
  (declare (xargs :guard t :verify-guards nil))
  (let ((s1 (fn-rtc-end-use st (fn-hlp-bev st r))))
    (fn-rtc-issue (list :wait (fn-hlp-acc-j s1) (fn-hlp-acc-jinc s1) (fn-rtc-next-op s1) nil)
                  (fn-rtc-with-mstate (fn-hlp-acc-j s1) nil (fn-hlp-acc-prep s1 r))))))
(local (defthm fn-hlp-accept-s1-facts
  (implies (and (fn-rtc-invp st) (natp r) (fn-rtc-free-slot 0 (fn-rtc-slots st)) (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses st)))
           (let ((s1 (fn-rtc-end-use st (fn-hlp-bev st r))))
             (and (fn-hlp-acc-j s1) (< (fn-hlp-acc-j s1) (len (fn-rtc-slots s1)))
                  (not (fn-rtc-kind-out-p :wait (fn-hlp-acc-j s1) (fn-hlp-acc-jinc s1) (fn-rtc-uses s1))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-acc-j fn-hlp-acc-jinc fn-hlp-bev natp fn-rtc-slot)
                                             (theory 'minimal-theory))
           :use ((:instance fn-hlp-accept-end-use (s st))
                 (:instance fn-hlp-accept-j-free (j (fn-rtc-free-slot 0 (fn-rtc-slots st))) (kind :wait)
                            (inc (+ 1 (fn-rtc-s-inc (fn-rtc-slot (fn-rtc-free-slot 0 (fn-rtc-slots st)) st)))))
                 (:instance fn-hlr-remove-nosend (k :wait) (id (fn-rtc-free-slot 0 (fn-rtc-slots st)))
                            (inc (+ 1 (fn-rtc-s-inc (fn-rtc-slot (fn-rtc-free-slot 0 (fn-rtc-slots st)) st))))
                            (key (fn-rtc-key (fn-hlp-bev st r))) (uses (fn-rtc-uses st))))))))
(local (defthm fn-hlp-accept-step-a
  (implies (and (fn-rtc-invp st) (natp r) (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses st)))
           (and (equal (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))
                       (mv-nth 0 (fn-hll-accept-branch (fn-rtc-end-use st (fn-hlp-bev st r)) (list :done r) 1)))
                (equal (mv-nth 1 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))
                       (mv-nth 1 (fn-hll-accept-branch (fn-rtc-end-use st (fn-hlp-bev st r)) (list :done r) 1)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hll-x-step*-is fn-rtc-invp-implies-st-p fn-hlp-bev fn-hlp-find-use-kind fn-rtc-key fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix))
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance fn-hlp-landed-accept (e (fn-hlp-bev st r)) (s st))
                 (:instance fn-hlp-step-accept-parts (s st) (e (fn-hlp-bev st r)) (q 1))
                 (:instance fn-hlp-accept-acts-on (s st))
                 (:instance fn-hlp-accept-outcome (u (fn-rtc-find-use (fn-rtc-key (fn-hlp-bev st r)) (fn-rtc-uses st))) (e (fn-hlp-bev st r)))
                 (:instance fn-hlp-accept-use-hd-nil (s st) (key (fn-rtc-key (fn-hlp-bev st r))))
                 (:instance fn-hlp-accept-event-facts (s st)))))))
(local (defthm fn-hlp-accept-step
  (implies (and (fn-rtc-invp st) (natp r) (< r (expt 2 64)) (fn-rtc-free-slot 0 (fn-rtc-slots st))
                (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses st)))
           (and (equal (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))
                       (mv-nth 0 (fn-rtc-rearm (fn-hlp-dd st r))))
                (equal (mv-nth 1 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))
                       (mv-nth 1 (fn-rtc-rearm (fn-hlp-dd st r))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-dd binary-append) (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance fn-hlp-accept-step-a)
                 (:instance fn-hlp-accept-branch-go-parts (s1 (fn-rtc-end-use st (fn-hlp-bev st r))) (q 1))
                 (:instance fn-hlp-accept-deliver-gen (s1 (fn-rtc-end-use st (fn-hlp-bev st r))) (q 1))
                 (:instance fn-hlp-accept-s1-facts))))))
(local (defthm fn-hlp-acc-j-of-s1
  (implies (and (fn-rtc-invp st) (natp r) (fn-rtc-free-slot 0 (fn-rtc-slots st)) (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses st)))
           (let ((s1 (fn-rtc-end-use st (fn-hlp-bev st r))))
             (and (equal (fn-hlp-acc-j s1) (fn-rtc-free-slot 0 (fn-rtc-slots st)))
                  (equal (fn-hlp-acc-jinc s1) (+ 1 (fn-rtc-s-inc (fn-rtc-slot (fn-rtc-free-slot 0 (fn-rtc-slots st)) st))))
                  (equal (fn-rtc-next-op s1) (fn-rtc-next-op st)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-acc-j fn-hlp-acc-jinc fn-rtc-slot fn-hlp-bev) (theory 'minimal-theory))
           :use ((:instance fn-hlp-accept-end-use (s st)))))))
(local (defthm fn-hlp-dd-facts
  (implies (and (fn-rtc-invp st) (natp r) (fn-rtc-free-slot 0 (fn-rtc-slots st)) (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses st)))
           (let ((j (fn-rtc-free-slot 0 (fn-rtc-slots st)))
                 (jinc (+ 1 (fn-rtc-s-inc (fn-rtc-slot (fn-rtc-free-slot 0 (fn-rtc-slots st)) st)))))
             (and (equal (fn-rtc-uses (fn-hlp-dd st r))
                         (cons (list :wait j jinc (fn-rtc-next-op st) nil)
                               (fn-rtc-remove-use (fn-rtc-key (fn-hlp-bev st r)) (fn-rtc-uses st))))
                  (equal (fn-rtc-pool (fn-hlp-dd st r)) (fn-rtc-pool st))
                  (equal (fn-rtc-config (fn-hlp-dd st r)) (fn-rtc-config st))
                  (equal (fn-rtc-slots (fn-hlp-dd st r)) (fn-rtc-set j (list jinc :live r) (fn-rtc-slots st))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-dd fn-hlp-acc-prep fn-rtc-with-accessors fn-rtc-issue-frame fn-hlp-bev)
                                             (theory 'minimal-theory))
           :use ((:instance fn-hlp-accept-end-use (s st))
                 (:instance fn-hlp-acc-j-of-s1))))))
(local (defthm fn-hlp-accept-end-use-bev
  (implies (and (fn-rtc-invp s) (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s)) (natp r))
           (let ((s1 (fn-rtc-end-use s (fn-hlp-bev s r))))
             (and (equal (fn-rtc-slots s1) (fn-rtc-slots s))
                  (equal (fn-rtc-pool s1) (fn-rtc-pool s))
                  (equal (fn-rtc-config s1) (fn-rtc-config s))
                  (equal (fn-rtc-mstates s1) (fn-rtc-mstates s))
                  (equal (fn-rtc-next-op s1) (fn-rtc-next-op s))
                  (equal (fn-rtc-uses s1) (fn-rtc-remove-use (fn-rtc-key (fn-hlp-bev s r)) (fn-rtc-uses s))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-bev) (theory 'minimal-theory))
           :use ((:instance fn-hlp-accept-end-use))))))
(local (defthm fn-hlp-dd-slot
  (implies (and (fn-rtc-invp st) (natp r) (fn-rtc-free-slot 0 (fn-rtc-slots st)) (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses st)))
           (let ((j (fn-rtc-free-slot 0 (fn-rtc-slots st)))
                 (jinc (+ 1 (fn-rtc-s-inc (fn-rtc-slot (fn-rtc-free-slot 0 (fn-rtc-slots st)) st)))))
             (equal (fn-rtc-slot j (fn-hlp-dd st r)) (list jinc :live r))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-dd fn-hlp-acc-prep fn-rtc-issue-frame fn-rtc-slot-of-with fn-rtc-with-accessors fn-hlp-acc-j fn-hlp-acc-jinc posp nfix natp)
                                             (theory 'minimal-theory))
           :use ((:instance fn-hlp-accept-end-use-bev (s st))
                 (:instance fn-hlp-acc-j-of-s1)
                 (:instance fn-hlp-accept-j-free (j (fn-rtc-free-slot 0 (fn-rtc-slots st))) (kind :wait) (inc 0)))))))
(local (defthm fn-hlp-nfix-1+ (equal (nfix (+ 1 (nfix x))) (+ 1 (nfix x)))))
(local (defthm fn-hlp-begin-ids
  (implies (mv-nth 1 (fn-hld-begin r st))
           (and (posp (mv-nth 1 (fn-hld-begin r st))) (natp (mv-nth 2 (fn-hld-begin r st)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hld-begin fn-rtc-st-free-slot fn-rtc-st$a-free-slot fn-hld-readers natp posp mv-nth (:e mv-nth) nfix
                                               (:type-prescription fn-rtc-free-slot) (:type-prescription fn-rtc-s-inc) (:type-prescription nfix))
                                             (theory 'minimal-theory))))))
(local (defthm fn-hlp-begin-success
  (implies (mv-nth 1 (fn-hld-begin r st))
           (and (natp r) (< r (expt 2 64)) (fn-rtc-free-slot 0 (fn-rtc-slots st))
                (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses st))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hld-begin fn-rtc-st-free-slot fn-rtc-st$a-free-slot fn-hld-readers natp mv-nth (:e mv-nth))
                                             (theory 'minimal-theory))))))
(local (defthm fn-hlp-begin-slot
  (implies (and (fn-hll-invp st) (mv-nth 1 (fn-hld-begin r st)))
           (equal (fn-rtc-slot (mv-nth 1 (fn-hld-begin r st)) (mv-nth 0 (fn-hld-begin r st)))
                  (list (mv-nth 2 (fn-hld-begin r st)) :live r)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hlr-benign-tlf fn-hld-hll-invp-is-generic-invp fn-rtc-s-status
                                               fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) natp posp (:type-prescription fn-rtc-free-slot))
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use (fn-hlp-begin-success fn-hlp-begin-ids
                 (:instance fn-hlp-begin-parts)
                 (:instance fn-hlp-accept-step)
                 (:instance fn-hlp-dd-slot)
                 (:instance fn-hld-x-step*-keeps-invp (e (fn-hlp-bev st r)) (q 1))
                 (:instance fn-hlr-rearm (s (fn-hlp-dd st r)) (id 0) (inc 0))
                 (:instance fn-rtc-slot-of-rearm (j (fn-rtc-free-slot 0 (fn-rtc-slots st))) (s (fn-hlp-dd st r)))
                 (:instance fn-hlr-settle-frames (work (true-list-fix (mv-nth 1 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))))
                            (fuel (fn-hld-fuel (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))))
                            (st (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st)))
                            (id 0) (inc 0) (k 0) (j (fn-rtc-free-slot 0 (fn-rtc-slots st))))
                 (:instance fn-hld-hll-invp-is-generic-invp (s st)))))))
(local (defthm fn-hlp-accept-only-tlf
  (implies (fn-hlp-accept-onlyp acts) (equal (true-list-fix acts) acts))
  :hints (("Goal" :in-theory (enable fn-hlp-accept-onlyp)))))
(local (defthm fn-hlp-workspace-holder-live
  (implies (and (fn-rtc-core-invp s) (fn-hld-workspace h j inc s))
           (member-eq (fn-rtc-s-status (fn-rtc-slot j s)) '(:live :closing)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-buffer-okp fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e member-eq) member-eq nfix natp)
                                             (theory 'minimal-theory))
           :use ((:instance fn-hlp-workspace-facts (id j) (st s))
                 (:instance fn-rtc-core-invp-buffer (h (fn-hld-workspace h j inc s))))))))
(local (defthm fn-hlp-no-workspace-for-free-slot
  (implies (and (fn-rtc-core-invp st) (equal (fn-rtc-pool s2) (fn-rtc-pool st)) (equal (fn-rtc-config s2) (fn-rtc-config st))
                (equal (fn-rtc-s-status (fn-rtc-slot j st)) :free))
           (not (fn-hld-workspace h j inc s2)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-buffer fn-rtc-config fn-rtc-pool fn-rtc-buffer-okp fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix)
                                               (:e member-eq) member-eq natp nfix)
                                             (theory 'minimal-theory))
           :use ((:instance fn-rtc-core-invp-buffer (s st) (h (fn-hld-workspace h j inc s2)))
                 (:instance fn-hlp-workspace-facts (id j) (st s2)))))))
(local (defthm fn-hlp-no-free-buffer-no-workspace
  (implies (and (fn-hll-invp st) (mv-nth 1 (fn-hld-begin r st))
                (not (fn-rtc-free-pool-buf 0 (fn-rtc-pool st) (fn-rtc-config st))))
           (not (fn-hld-workspace 0 (mv-nth 1 (fn-hld-begin r st)) (mv-nth 2 (fn-hld-begin r st)) (mv-nth 0 (fn-hld-begin r st)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hld-hll-invp-is-generic-invp fn-hlp-accept-only-tlf)
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use (fn-hlp-begin-success
                 (:instance fn-hlp-begin-parts)
                 (:instance fn-hlp-accept-step)
                 (:instance fn-hlp-dd-facts)
                 (:instance fn-hlp-rearm-accept-only (s (fn-hlp-dd st r)))
                 (:instance fn-hlp-settle-accept-only (work (true-list-fix (mv-nth 1 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))))
                            (fuel (fn-hld-fuel (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))))
                            (st (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))))
                 (:instance fn-hlp-rearm-pool (s (fn-hlp-dd st r)))
                 (:instance fn-rtc-rearm-frame (s (fn-hlp-dd st r)) (h 0) (j 0) (u nil))
                 (:instance fn-hlp-accept-j-free (j (fn-rtc-free-slot 0 (fn-rtc-slots st))) (kind :wait) (inc 0))
                 (:instance fn-rtc-invp-implies-core-invp (s st))
                 (:instance fn-hlp-no-workspace-for-free-slot
                            (s2 (mv-nth 0 (fn-hld-begin r st))) (j (fn-rtc-free-slot 0 (fn-rtc-slots st)))
                            (h 0) (inc (mv-nth 2 (fn-hld-begin r st)))))))))
(local (defthm fn-hlp-landed-not-in
  (implies (not (member-eq (fn-rtc-get 0 e) '(:recv :pread)))
           (equal (fn-rtc-landed e s) e))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-landed fn-hlp-find-use-kind fn-rtc-key fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix)
                                               (:e member-eq) member-eq)
                                             (theory 'minimal-theory))))))
(local (defthm fn-hlp-owp-replace
  (implies (not (equal (fn-rtc-get 0 u2) :wait))
           (equal (fn-rtc-oldest-wait (fn-rtc-replace-use key u2 uses))
                  (fn-rtc-oldest-wait (fn-rtc-remove-use key uses))))
  :hints (("Goal" :induct (fn-rtc-replace-use key u2 uses)
           :in-theory (union-theories '((:induction fn-rtc-replace-use) fn-rtc-replace-use fn-rtc-remove-use fn-rtc-oldest-wait-cons-other car-cons cdr-cons)
                                      (theory 'minimal-theory)))
          ("Subgoal *1/2" :expand ((fn-rtc-oldest-wait (cons (car uses) (fn-rtc-replace-use key u2 (cdr uses))))
                                   (fn-rtc-oldest-wait (cons (car uses) (fn-rtc-remove-use key (cdr uses)))))))))
(local (defun fn-hlp-front-p (s opg)
  (declare (xargs :guard t))
  (and (consp (fn-rtc-uses s)) (equal (car (fn-rtc-uses s)) (list :grant 0 0 opg nil)))))
(local (defthm fn-hlp-grant-key-of
  (implies (equal x (list :grant 0 0 opg nil)) (equal (fn-rtc-key x) (list :grant 0 0 opg)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-key fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix)) (theory 'minimal-theory))))))
(local (defthm fn-hlp-front-find
  (implies (fn-hlp-front-p s opg)
           (equal (fn-rtc-find-use (list :grant 0 0 opg) (fn-rtc-uses s)) (list :grant 0 0 opg nil)))
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-front-p) (theory 'minimal-theory))
           :expand ((fn-rtc-find-use (list :grant 0 0 opg) (fn-rtc-uses s)))
           :use ((:instance fn-hlp-grant-key-of (x (car (fn-rtc-uses s)))))))))
(local (defthm fn-hlp-front-remove
  (implies (fn-hlp-front-p s opg)
           (equal (fn-rtc-remove-use (list :grant 0 0 opg) (fn-rtc-uses s)) (cdr (fn-rtc-uses s))))
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-front-p) (theory 'minimal-theory))
           :expand ((fn-rtc-remove-use (list :grant 0 0 opg) (fn-rtc-uses s)))
           :use ((:instance fn-hlp-grant-key-of (x (car (fn-rtc-uses s)))))))))
(local (defthm fn-hlp-front-opg
  (implies (and (fn-rtc-invp s) (fn-hlp-front-p s opg)) (natp opg))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-front-p fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix))
                                             (theory 'minimal-theory))
           :expand ((fn-rtc-uses-ops-natp (fn-rtc-uses s)))
           :use (fn-rtc-invp-ops-natp)))))
(local (defthm fn-hlp-grant-event-facts
  (implies (and (fn-rtc-invp s) (fn-hlp-front-p s opg))
           (let ((e (list :grant 0 0 opg (list :done 0))))
             (and (fn-rtc-completionp e) (fn-rtc-acts-on-p s e)
                  (equal (fn-rtc-end-use s e) (fn-rtc-with-uses (cdr (fn-rtc-uses s)) s)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-acts-on-p fn-rtc-completionp fn-rtc-outcomep fn-rtc-e-id fn-rtc-e-inc fn-rtc-e-kind fn-rtc-key
                                               fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e binary-+) (:e unary--) (:e member-eq) member-eq
                                               (:e len) len (:e true-listp) true-listp (:e equal) natp (:type-prescription nfix) (:e consp) fn-rtc-s-inc fn-rtc-s-status
                                               fn-rtc-end-use fn-rtc-u-hd fn-hlp-end-lease-no-hd fn-hlp-retire-live (:e fn-rtc-handlep)
                                               fn-hlp-front-find fn-hlp-front-remove fn-rtc-slot-of-with)
                                             (theory 'minimal-theory))
           :use (fn-rtc-invp-listener fn-hlp-front-opg)))))
(local (defthm fn-hlp-grant-step
  (implies (and (fn-rtc-invp s) (fn-hlp-front-p s opg))
           (let* ((e (list :grant 0 0 opg (list :done 0)))
                  (s1 (fn-rtc-with-uses (cdr (fn-rtc-uses s)) s))
                  (g (fn-rtc-grant (fn-rtc-npool (fn-rtc-config s)) s1)))
             (and (equal (mv-nth 0 (fn-hll-x-step* e 1 s)) (mv-nth 0 (fn-rtc-rearm (mv-nth 0 g))))
                  (equal (mv-nth 1 (fn-hll-x-step* e 1 s))
                         (append (mv-nth 1 g) (mv-nth 1 (fn-rtc-rearm (mv-nth 0 g))))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hll-x-step*-is fn-rtc-invp-implies-st-p fn-hlp-landed-not-in fn-hll-step* fn-rtc-hand-delivers-p fn-rtc-e-kind
                                               fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e member-eq) member-eq (:e eq) eq
                                               fn-rtc-with-accessors)
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance fn-hlp-grant-event-facts))))))
(local (defthm fn-hlp-grant-without-wait
  (implies (not (fn-rtc-oldest-wait (fn-rtc-uses s)))
           (and (equal (mv-nth 0 (fn-rtc-grant n s)) s) (equal (mv-nth 1 (fn-rtc-grant n s)) nil)))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-grant fn-rtc-grant-one mv-nth (:e mv-nth) (:e consp)) (theory 'minimal-theory))))))
(local (defthm fn-hlp-grant-one-acts
  (implies (and (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s)) (fn-rtc-oldest-wait (fn-rtc-uses s)))
           (and (consp (mv-nth 1 (fn-rtc-grant-one s))) (true-listp (mv-nth 1 (fn-rtc-grant-one s)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-grant-one mv-nth (:e mv-nth) (:e consp) (:e true-listp) true-listp) (theory 'minimal-theory))))))
(local (defthm fn-hlp-grant-one-pair
  (equal (fn-rtc-grant-one s) (list (mv-nth 0 (fn-rtc-grant-one s)) (mv-nth 1 (fn-rtc-grant-one s))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-grant-one mv-nth (:e mv-nth)) (theory 'minimal-theory))))))
(local (defthm fn-hlp-append-nil (implies (true-listp x) (equal (append x nil) x))))
(local (defthm fn-hlp-grant-twice
  (implies (and (natp n) (< 0 n)
                (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s))
                (fn-rtc-oldest-wait (fn-rtc-uses s))
                (not (fn-rtc-oldest-wait (fn-rtc-uses (mv-nth 0 (fn-rtc-grant-one s))))))
           (and (equal (mv-nth 0 (fn-rtc-grant n s)) (mv-nth 0 (fn-rtc-grant-one s)))
                (equal (mv-nth 1 (fn-rtc-grant n s)) (mv-nth 1 (fn-rtc-grant-one s)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(natp zp fn-hld-mv-nth-0-cons fn-hlr-mv-nth-1-cons (:e consp) binary-append fn-hlp-append-nil)
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :expand ((fn-rtc-grant n s))
           :use (fn-hlp-grant-one-acts fn-hlp-grant-one-pair
                 (:instance fn-hlp-grant-without-wait (n (+ -1 n)) (s (mv-nth 0 (fn-rtc-grant-one s)))))))))
(local (defthm fn-hlp-grant-step-main
  (implies (and (fn-rtc-invp s) (fn-hlp-front-p s opg)
                (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s))
                (fn-rtc-oldest-wait (cdr (fn-rtc-uses s)))
                (not (fn-rtc-oldest-wait (fn-rtc-remove-use (fn-rtc-key (fn-rtc-oldest-wait (cdr (fn-rtc-uses s)))) (cdr (fn-rtc-uses s)))))
                (< 0 (fn-rtc-npool (fn-rtc-config s))))
           (let* ((e (list :grant 0 0 opg (list :done 0)))
                  (s1 (fn-rtc-with-uses (cdr (fn-rtc-uses s)) s))
                  (g (fn-rtc-grant-one s1)))
             (and (equal (mv-nth 0 (fn-hll-x-step* e 1 s)) (mv-nth 0 (fn-rtc-rearm (mv-nth 0 g))))
                  (equal (mv-nth 1 (fn-hll-x-step* e 1 s))
                         (append (mv-nth 1 g) (mv-nth 1 (fn-rtc-rearm (mv-nth 0 g)))))
                  (consp (mv-nth 1 g)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-with-accessors natp (:type-prescription fn-rtc-npool))
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance fn-hlp-grant-step)
                 (:instance fn-hlp-grant-twice (n (fn-rtc-npool (fn-rtc-config s))) (s (fn-rtc-with-uses (cdr (fn-rtc-uses s)) s)))
                 (:instance fn-hlp-grant-one-acts (s (fn-rtc-with-uses (cdr (fn-rtc-uses s)) s)))
                 (:instance fn-rtc-grant-one-is-pool-grant-state (s (fn-rtc-with-uses (cdr (fn-rtc-uses s)) s)))
                 (:instance fn-rtc-pool-grant-state-frame (j 0)
                            (w (fn-rtc-oldest-wait (cdr (fn-rtc-uses s))))
                            (h (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s)))
                            (s (fn-rtc-with-uses (cdr (fn-rtc-uses s)) s)))
                 (:instance fn-hlp-owp-replace (key (fn-rtc-key (fn-rtc-oldest-wait (cdr (fn-rtc-uses s)))))
                            (u2 (fn-rtc-pool-grant-use (fn-rtc-oldest-wait (cdr (fn-rtc-uses s))) (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s))
                                                       (fn-rtc-with-uses (cdr (fn-rtc-uses s)) s)))
                            (uses (cdr (fn-rtc-uses s))))
                 (:instance fn-rtc-pool-grant-use-fields (w (fn-rtc-oldest-wait (cdr (fn-rtc-uses s))))
                            (h (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s)))
                            (s (fn-rtc-with-uses (cdr (fn-rtc-uses s)) s))))))))
(local (defthm fn-hlp-pool-use-facts
  (implies (and (fn-rtc-invp s) (fn-rtc-find-use key (fn-rtc-uses s)) (equal (fn-rtc-get 0 key) :pool))
           (let* ((u (fn-rtc-find-use key (fn-rtc-uses s)))
                  (hd (fn-rtc-u-hd u)) (h (fn-rtc-h-buf hd)) (o (fn-rtc-b-owner (fn-rtc-buffer h s))))
             (and (equal (fn-rtc-get 0 u) :pool) (fn-rtc-handlep hd)
                  (< h (fn-rtc-nbufs (fn-rtc-config s)))
                  (equal (fn-rtc-b-gen (fn-rtc-buffer h s)) (fn-rtc-h-gen hd))
                  (equal (fn-rtc-get 0 o) :leased) (equal (fn-rtc-get 3 o) :in)
                  (equal (fn-rtc-get 1 o) (nfix (fn-rtc-get 1 u))) (equal (fn-rtc-get 2 o) (fn-rtc-get 2 u))
                  (equal (fn-rtc-holders h (fn-rtc-h-gen hd) (fn-rtc-uses s)) 1))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-use-okp fn-rtc-usep fn-hlp-find-use-kind (:e member-eq) member-eq (:e member-equal) member-equal (:e fn-rtc-get) iff fn-rtc-u-hd fn-rtc-h-buf fn-rtc-b-owner (:type-prescription nfix) natp
                                               fn-rtc-pool-buf-p)
                                             (theory 'minimal-theory))
           :use (fn-rtc-invp-uses-okp
                 (:instance fn-rtc-uses-okp-member (uses (fn-rtc-uses s)) (s s) (u (fn-rtc-find-use key (fn-rtc-uses s))))
                 (:instance fn-rtc-find-use-is-member (k key) (uses (fn-rtc-uses s))))))))
(local (defthm fn-hlp-holders-of-remove-found
  (implies (and (equal u (fn-rtc-find-use key uses)) u)
           (equal (fn-rtc-holders h g (fn-rtc-remove-use key uses))
                  (- (fn-rtc-holders h g uses)
                     (if (and (fn-rtc-handlep (fn-rtc-u-hd u))
                              (equal (fn-rtc-h-buf (fn-rtc-u-hd u)) h)
                              (equal (fn-rtc-h-gen (fn-rtc-u-hd u)) g))
                         1 0))))
  :hints (("Goal" :induct (fn-rtc-remove-use key uses)
           :in-theory (disable fn-rtc-key fn-rtc-handlep fn-rtc-h-buf fn-rtc-h-gen)))))
(local (defthm fn-hlp-pool-lease-ends
  (implies (and (fn-rtc-invp s) (fn-rtc-find-use key (fn-rtc-uses s)) (equal (fn-rtc-get 0 key) :pool))
           (let* ((u (fn-rtc-find-use key (fn-rtc-uses s))) (hd (fn-rtc-u-hd u)))
             (not (fn-rtc-holds-p (fn-rtc-h-buf hd) (fn-rtc-h-gen hd) (fn-rtc-remove-use key (fn-rtc-uses s))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-holds-iff-positive-holders fn-hlp-holders-of-remove-found) (theory 'minimal-theory))
           :use (fn-hlp-pool-use-facts)))))
(local (defthm fn-hlp-find-use-field1
  (implies (fn-rtc-find-use key uses)
           (equal (fn-rtc-get 1 (fn-rtc-find-use key uses)) (fn-rtc-get 1 key)))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-key fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix)) (theory 'minimal-theory))
           :use ((:instance fn-rtc-key-of-find-use (k key)))))))
(local (defthm fn-hlp-find-use-field2
  (implies (fn-rtc-find-use key uses)
           (equal (fn-rtc-get 2 (fn-rtc-find-use key uses)) (fn-rtc-get 2 key)))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-key fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix)) (theory 'minimal-theory))
           :use ((:instance fn-rtc-key-of-find-use (k key)))))))
(local (defthm fn-hlp-lease-return-workspace
  (implies (and (equal (fn-rtc-b-owner b) o) (equal (fn-rtc-get 0 o) :leased) (equal (nfix (fn-rtc-get 1 o)) id)
                (natp id) (equal (fn-rtc-get 2 o) inc) (fn-rtc-live-p id inc s))
           (equal (fn-rtc-b-owner (fn-rtc-lease-return u e b s)) (list :workspace id inc)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-lease-return fn-rtc-handed-to-live-p fn-rtc-live-p fn-rtc-current-p fn-rtc-s-inc fn-rtc-s-status fn-rtc-b-owner
                                               fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e member-eq) member-eq natp)
                                             (theory 'minimal-theory))))))
(local (defthm fn-hlp-end-lease-buffer
  (implies (and (fn-rtc-handlep (fn-rtc-u-hd u)) (natp (fn-rtc-h-buf (fn-rtc-u-hd u)))
                (< (fn-rtc-h-buf (fn-rtc-u-hd u)) (len (fn-rtc-pool s)))
                (not (fn-rtc-holds-p (fn-rtc-h-buf (fn-rtc-u-hd u)) (fn-rtc-h-gen (fn-rtc-u-hd u)) (fn-rtc-uses s))))
           (equal (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) (fn-rtc-end-lease u e s))
                  (fn-rtc-lease-return u e (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s) s)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-end-lease fn-rtc-buffer-of-with natp nfix) (theory 'minimal-theory))))))
(local (defthm fn-hlp-pool-end-use-buffer
  (implies (and (fn-rtc-invp s) (natp id) (natp inc) (natp op)
                (fn-rtc-find-use (list :pool id inc op) (fn-rtc-uses s))
                (fn-rtc-live-p id inc s))
           (let* ((e (list :pool id inc op (list :done 0)))
                  (u (fn-rtc-find-use (list :pool id inc op) (fn-rtc-uses s)))
                  (h (fn-rtc-h-buf (fn-rtc-u-hd u))))
             (and (< h (fn-rtc-nbufs (fn-rtc-config s)))
                  (equal (fn-rtc-b-owner (fn-rtc-buffer h (fn-rtc-end-use s e))) (list :workspace id inc)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-find-use-field1 fn-hlp-find-use-field2 fn-rtc-key fn-hlr-live-of-with-uses fn-hlr-retire-keeps fn-rtc-with-accessors fn-rtc-buffer-of-with
                                               fn-hlr-pool-len-facts fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:type-prescription nfix) natp nfix
                                               (:type-prescription fn-rtc-h-buf) fn-rtc-e-id fn-rtc-completionp fn-rtc-outcomep (:e member-eq) member-eq (:e len) len
                                               (:e true-listp) true-listp (:e consp) (:e equal))
                                             (theory 'minimal-theory))
           :use ((:instance fn-rtc-end-use-structure (s s) (e (list :pool id inc op (list :done 0))))
                 (:instance fn-hlp-pool-use-facts (key (list :pool id inc op)))
                 (:instance fn-hlp-pool-lease-ends (key (list :pool id inc op)))
                 (:instance fn-hlp-end-lease-buffer (u (fn-rtc-find-use (list :pool id inc op) (fn-rtc-uses s)))
                            (e (list :pool id inc op (list :done 0)))
                            (s (fn-rtc-with-uses (fn-rtc-remove-use (list :pool id inc op) (fn-rtc-uses s)) s)))
                 (:instance fn-hlp-lease-return-workspace
                            (b (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (list :pool id inc op) (fn-rtc-uses s)))) s))
                            (o (fn-rtc-b-owner (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (list :pool id inc op) (fn-rtc-uses s)))) s)))
                            (u (fn-rtc-find-use (list :pool id inc op) (fn-rtc-uses s)))
                            (e (list :pool id inc op (list :done 0)))
                            (s (fn-rtc-with-uses (fn-rtc-remove-use (list :pool id inc op) (fn-rtc-uses s)) s)))
                 (:instance fn-hlr-pool-len-facts))))))
(local (defthm fn-hlp-pool-acts-on
  (implies (and (natp id) (natp inc) (natp op) (fn-rtc-find-use (list :pool id inc op) (fn-rtc-uses s)) (fn-rtc-live-p id inc s))
           (fn-rtc-acts-on-p s (list :pool id inc op (list :done 0))))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-acts-on-p fn-rtc-completionp fn-rtc-outcomep fn-rtc-live-p fn-rtc-e-id fn-rtc-e-inc fn-rtc-e-kind fn-rtc-key
                                               fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e binary-+) (:e unary--) (:e member-eq) member-eq
                                               (:e len) len (:e true-listp) true-listp (:e equal) natp (:type-prescription nfix) (:e consp) fn-rtc-s-inc fn-rtc-s-status nfix)
                                             (theory 'minimal-theory))))))
(local (defthm fn-hlp-pool-step-ws
  (implies (and (fn-hll-invp s) (natp id) (natp inc) (natp op)
                (fn-rtc-find-use (list :pool id inc op) (fn-rtc-uses s))
                (fn-rtc-live-p id inc s))
           (let* ((e (list :pool id inc op (list :done 0)))
                  (s2 (mv-nth 0 (fn-hll-x-step* e 1 s)))
                  (h (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (list :pool id inc op) (fn-rtc-uses s))))))
             (and (< h (fn-rtc-nbufs (fn-rtc-config s)))
                  (equal (fn-rtc-b-owner (fn-rtc-buffer h s2)) (list :workspace id inc))
                  (fn-hlr-benign-actsp (mv-nth 1 (fn-hll-x-step* e 1 s))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hll-x-step*-is fn-hld-hll-invp-st-p fn-hld-hll-invp-is-generic-invp fn-hlp-landed-not-in fn-hll-step* fn-rtc-hand-delivers-p fn-rtc-e-kind
                                               fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e member-eq) member-eq (:e eq) eq
                                               fn-hlr-deliver-is-mstate fn-rtc-ev fn-rtc-rearm-frame fn-rtc-buffer-of-with fn-rtc-with-accessors
                                               fn-hlr-pool-len-facts natp nfix (:type-prescription nfix) fn-rtc-e-id)
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance fn-hlp-pool-end-use-buffer (s s))
                 (:instance fn-hlr-xstep-frames (st s) (e (list :pool id inc op (list :done 0))) (q 1) (id 0) (inc 0) (k 0) (j 0))
                 (:instance fn-hlp-pool-acts-on))))))
(local (defthm fn-hlp-owp-remove-nil
  (implies (not (fn-rtc-oldest-wait uses)) (not (fn-rtc-oldest-wait (fn-rtc-remove-use key uses))))
  :hints (("Goal" :induct (fn-rtc-remove-use key uses)
           :in-theory (union-theories '((:induction fn-rtc-remove-use) fn-rtc-remove-use fn-rtc-oldest-wait fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get))
                                      (theory 'minimal-theory))))))
(local (defthm fn-hlp-owp-cons-wait
  (implies (and (equal (fn-rtc-get 0 u) :wait) (not (fn-rtc-oldest-wait rest)))
           (equal (fn-rtc-oldest-wait (cons u rest)) u))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-oldest-wait car-cons cdr-cons) (theory 'minimal-theory))))))
(local (defthm fn-hlp-replace-use-member
  (implies (member-equal w uses) (member-equal u2 (fn-rtc-replace-use (fn-rtc-key w) u2 uses)))
  :hints (("Goal" :induct (fn-rtc-replace-use (fn-rtc-key w) u2 uses)
           :in-theory (union-theories '((:induction fn-rtc-replace-use) fn-rtc-replace-use member-equal car-cons cdr-cons) (theory 'minimal-theory))))))
(local (defthm fn-hlp-invp-configp
  (implies (fn-rtc-invp s) (fn-rtc-configp (fn-rtc-config s)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-core-invp) (theory 'minimal-theory))
           :use fn-rtc-invp-implies-core-invp))))
(local (defthm fn-hlp-npool-pos
  (implies (and (fn-rtc-invp s) (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s)))
           (< 0 (fn-rtc-npool (fn-rtc-config s))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-pool-buf-p fn-rtc-nhome fn-rtc-npool fn-rtc-nbufs fn-rtc-nslots fn-rtc-qfixed fn-rtc-configp nfix natp) (theory 'minimal-theory))
           :use ((:instance fn-rtc-free-pool-buf-pool-index (i 0) (pool (fn-rtc-pool s)) (cfg (fn-rtc-config s)))
                 fn-hlp-invp-configp)))))
(local (defthm fn-hlp-workspace-exists
  (implies (and (natp h) (natp k) (<= h k) (< k (fn-rtc-nbufs (fn-rtc-config st)))
                (equal (fn-rtc-b-owner (fn-rtc-buffer k st)) (list :workspace id inc)))
           (fn-hld-workspace h id inc st))
  :hints (("Goal" :induct (fn-hld-workspace h id inc st)
           :in-theory (union-theories '(fn-hld-workspace fn-hld-readers natp nfix (:type-prescription fn-rtc-nbufs)) (theory 'minimal-theory))))))
(local (defthm fn-hlp-rearm-grant-shape
  (implies (and (fn-rtc-free-pool-buf 0 (fn-rtc-pool d) (fn-rtc-config d))
                (fn-rtc-oldest-wait (fn-rtc-uses d))
                (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses d))))
           (let* ((a (and (fn-rtc-free-slot 0 (fn-rtc-slots d)) (not (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses d)))))
                  (opg (if a (+ 1 (fn-rtc-next-op d)) (fn-rtc-next-op d))))
             (and (equal (mv-nth 1 (fn-rtc-rearm d))
                         (if a
                             (list (list :accept 0 0 (fn-rtc-next-op d) (list nil)) (list :grant 0 0 opg (list nil)))
                           (list (list :grant 0 0 opg (list nil)))))
                  (fn-hlp-front-p (mv-nth 0 (fn-rtc-rearm d)) opg)
                  (equal (cdr (fn-rtc-uses (mv-nth 0 (fn-rtc-rearm d))))
                         (if a (cons (list :accept 0 0 (fn-rtc-next-op d) nil) (fn-rtc-uses d)) (fn-rtc-uses d))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-rearm fn-rtc-arm-accept fn-rtc-arm-grant fn-rtc-issue-frame fn-hlp-front-p mv-nth (:e mv-nth)
                                               fn-rtc-oldest-wait-cons-other fn-rtc-kind-out-cons car-cons cdr-cons fn-rtc-get-of-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e binary-+) (:e unary--)
                                               (:e equal) append (:e append) binary-append)
                                             (theory 'minimal-theory))))))
(local (defthm fn-hlp-invp-no-wait
  (implies (and (fn-rtc-invp s) (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s))
                (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses s))))
           (not (fn-rtc-oldest-wait (fn-rtc-uses s))))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use (fn-rtc-invp-is-core-and-admission)))))
(local (defthm fn-hlp-dd-G
  (implies (and (fn-rtc-invp st) (natp r) (fn-rtc-free-slot 0 (fn-rtc-slots st)) (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses st))
                (fn-rtc-free-pool-buf 0 (fn-rtc-pool st) (fn-rtc-config st))
                (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses st))))
           (let ((d (fn-hlp-dd st r))
                 (w (list :wait (fn-rtc-free-slot 0 (fn-rtc-slots st))
                          (+ 1 (fn-rtc-s-inc (fn-rtc-slot (fn-rtc-free-slot 0 (fn-rtc-slots st)) st)))
                          (fn-rtc-next-op st) nil)))
             (and (fn-rtc-free-pool-buf 0 (fn-rtc-pool d) (fn-rtc-config d))
                  (equal (fn-rtc-oldest-wait (fn-rtc-uses d)) w)
                  (not (fn-rtc-oldest-wait (cdr (fn-rtc-uses d))))
                  (equal (car (fn-rtc-uses d)) w)
                  (not (fn-rtc-oldest-wait (fn-rtc-remove-use (fn-rtc-key w) (fn-rtc-uses d))))
                  (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses d))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-kind-out-cons fn-hlp-owp-cons-wait fn-hlp-owp-remove-nil fn-rtc-remove-use fn-rtc-key car-cons cdr-cons fn-rtc-get-of-cons (:e fn-rtc-get) (:e zp) (:e nfix)
                                               (:e equal))
                                             (theory 'minimal-theory))
           :use ((:instance fn-hlp-dd-facts)
                 (:instance fn-hlp-invp-no-wait (s st))
                 (:instance fn-hlp-remove-use-keeps-other-kind (k :grant) (id 0) (inc 0) (key (fn-rtc-key (fn-hlp-bev st r))) (uses (fn-rtc-uses st)))
                 (:instance fn-hlr-remove-nosend (k :grant) (id 0) (inc 0) (key (fn-rtc-key (fn-hlp-bev st r))) (uses (fn-rtc-uses st))))))))
(local (defthm fn-hlp-remove-use-cons
  (equal (fn-rtc-remove-use k (cons a u)) (if (equal (fn-rtc-key a) k) u (cons a (fn-rtc-remove-use k u))))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-remove-use car-cons cdr-cons) (theory 'minimal-theory))))))
(local (defthm fn-hlp-sa1
  (implies (and (equal (fn-rtc-get 0 w) :wait)
                (not (fn-rtc-oldest-wait (fn-rtc-uses p)))
                (fn-rtc-free-pool-buf 0 (fn-rtc-pool p) (fn-rtc-config p))
                (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses p))))
           (let* ((sa (mv-nth 0 (fn-rtc-rearm (fn-rtc-issue w p))))
                  (a (and (fn-rtc-free-slot 0 (fn-rtc-slots p)) (not (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses p)))))
                  (opg (if a (+ 1 1 (fn-rtc-next-op p)) (+ 1 (fn-rtc-next-op p)))))
             (and (fn-hlp-front-p sa opg)
                  (equal (fn-rtc-oldest-wait (cdr (fn-rtc-uses sa))) w)
                  (not (fn-rtc-oldest-wait (fn-rtc-remove-use (fn-rtc-key w) (cdr (fn-rtc-uses sa)))))
                  (equal (fn-rtc-pool sa) (fn-rtc-pool p))
                  (equal (fn-rtc-config sa) (fn-rtc-config p))
                  (equal (mv-nth 1 (fn-rtc-rearm (fn-rtc-issue w p)))
                         (if a
                             (list (list :accept 0 0 (+ 1 (fn-rtc-next-op p)) (list nil)) (list :grant 0 0 opg (list nil)))
                           (list (list :grant 0 0 opg (list nil))))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-rearm-pool fn-rtc-rearm-frame fn-hlp-remove-use-cons fn-rtc-kind-out-cons fn-rtc-oldest-wait-cons-other fn-hlp-owp-cons-wait
                                               fn-rtc-key fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e equal) fn-rtc-issue-frame fn-rtc-with-accessors)
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance fn-hlp-rearm-grant-shape (d (fn-rtc-issue w p))))))))
(local (defun fn-hlp-p (st r)
  (declare (xargs :guard t :verify-guards nil))
  (let ((s1 (fn-rtc-end-use st (fn-hlp-bev st r))))
    (fn-rtc-with-mstate (fn-hlp-acc-j s1) nil (fn-hlp-acc-prep s1 r)))))
(local (defun fn-hlp-w2 (st r)
  (declare (xargs :guard t :verify-guards nil))
  (let ((s1 (fn-rtc-end-use st (fn-hlp-bev st r))))
    (list :wait (fn-hlp-acc-j s1) (fn-hlp-acc-jinc s1) (fn-rtc-next-op s1) nil))))
(local (defthm fn-hlp-dd-is-issue
  (equal (fn-hlp-dd st r) (fn-rtc-issue (fn-hlp-w2 st r) (fn-hlp-p st r)))
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-dd fn-hlp-p fn-hlp-w2) (theory 'minimal-theory))))))
(local (defthm fn-hlp-p-facts
  (implies (and (fn-rtc-invp st) (natp r) (fn-rtc-free-slot 0 (fn-rtc-slots st)) (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses st))
                (fn-rtc-free-pool-buf 0 (fn-rtc-pool st) (fn-rtc-config st))
                (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses st))))
           (and (equal (fn-rtc-get 0 (fn-hlp-w2 st r)) :wait)
                (not (fn-rtc-oldest-wait (fn-rtc-uses (fn-hlp-p st r))))
                (fn-rtc-free-pool-buf 0 (fn-rtc-pool (fn-hlp-p st r)) (fn-rtc-config (fn-hlp-p st r)))
                (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (fn-hlp-p st r))))
                (equal (fn-rtc-next-op (fn-hlp-p st r)) (fn-rtc-next-op st))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-p fn-hlp-w2 fn-rtc-next-op-of-with fn-rtc-with-accessors fn-hlp-acc-prep fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix))
                                             (theory 'minimal-theory))
           :use ((:instance fn-hlp-accept-end-use-bev (s st))
                 (:instance fn-hlp-invp-no-wait (s st))
                 (:instance fn-hlp-owp-remove-nil (key (fn-rtc-key (fn-hlp-bev st r))) (uses (fn-rtc-uses st)))
                 (:instance fn-hlr-remove-nosend (k :grant) (id 0) (inc 0) (key (fn-rtc-key (fn-hlp-bev st r))) (uses (fn-rtc-uses st))))))))
(local (defthm fn-hlp-settle-skip
  (implies (and (not (zp fuel)) (consp work) (not (member-eq (fn-rtc-get 0 (car work)) '(:grant :pool :close :opened))))
           (equal (fn-hld-settle work fuel st) (fn-hld-settle (cdr work) (- fuel 1) st)))
  :hints (("Goal" :in-theory (union-theories '(fn-hld-settle) (theory 'minimal-theory))))))
(local (defthm fn-hlp-settle-step
  (implies (and (not (zp fuel)) (consp work) (member-eq (fn-rtc-get 0 (car work)) '(:grant :pool :close :opened)))
           (equal (fn-hld-settle work fuel st)
                  (fn-hld-settle (append (cdr work)
                                         (true-list-fix (mv-nth 1 (fn-hll-x-step* (list (fn-rtc-get 0 (car work)) (fn-rtc-get 1 (car work)) (fn-rtc-get 2 (car work))
                                                                                        (fn-rtc-get 3 (car work)) '(:done 0)) 1 st))))
                                 (- fuel 1)
                                 (mv-nth 0 (fn-hll-x-step* (list (fn-rtc-get 0 (car work)) (fn-rtc-get 1 (car work)) (fn-rtc-get 2 (car work))
                                                                 (fn-rtc-get 3 (car work)) '(:done 0)) 1 st)))))
  :hints (("Goal" :in-theory (union-theories '(fn-hld-settle mv-nth (:e mv-nth)) (theory 'minimal-theory))))))
(local (defthm fn-hlp-grant-act-fields
  (implies (and (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s)) (fn-rtc-oldest-wait (fn-rtc-uses s)))
           (let ((a (car (mv-nth 1 (fn-rtc-grant-one s)))) (w (fn-rtc-oldest-wait (fn-rtc-uses s))))
             (and (equal (fn-rtc-get 0 a) :pool) (equal (fn-rtc-get 1 a) (nfix (fn-rtc-get 1 w)))
                  (equal (fn-rtc-get 2 a) (fn-rtc-get 2 w)) (equal (fn-rtc-get 3 a) (fn-rtc-get 3 w)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-grant-one mv-nth (:e mv-nth) fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix))
                                             (theory 'minimal-theory))))))
(local (defthm fn-hlp-grant-state-find
  (implies (and (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s)) (fn-rtc-oldest-wait (fn-rtc-uses s)))
           (let ((w (fn-rtc-oldest-wait (fn-rtc-uses s))))
             (fn-rtc-find-use (list :pool (nfix (fn-rtc-get 1 w)) (fn-rtc-get 2 w) (fn-rtc-get 3 w))
                              (fn-rtc-uses (mv-nth 0 (fn-rtc-grant-one s))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-pool-grant-state-frame fn-rtc-grant-one-is-pool-grant-state fn-rtc-pool-grant-use fn-rtc-oldest-wait-member fn-hlp-replace-use-member
                                               fn-rtc-find-use-of-member-key fn-rtc-key fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix))
                                             (theory 'minimal-theory))
           :use ((:instance fn-rtc-grant-one-is-pool-grant-state)
                 (:instance fn-rtc-pool-grant-state-frame (w (fn-rtc-oldest-wait (fn-rtc-uses s))) (h (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s))) (j 0))
                 (:instance fn-rtc-oldest-wait-member (uses (fn-rtc-uses s)))
                 (:instance fn-hlp-replace-use-member (w (fn-rtc-oldest-wait (fn-rtc-uses s)))
                            (u2 (fn-rtc-pool-grant-use (fn-rtc-oldest-wait (fn-rtc-uses s)) (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s)) s))
                            (uses (fn-rtc-uses s)))
                 (:instance fn-rtc-pool-grant-use-fields (w (fn-rtc-oldest-wait (fn-rtc-uses s))) (h (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s))))
                 (:instance fn-rtc-find-use-of-member-key
                            (x (fn-rtc-pool-grant-use (fn-rtc-oldest-wait (fn-rtc-uses s)) (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s)) s))
                            (k (list :pool (nfix (fn-rtc-get 1 (fn-rtc-oldest-wait (fn-rtc-uses s)))) (fn-rtc-get 2 (fn-rtc-oldest-wait (fn-rtc-uses s))) (fn-rtc-get 3 (fn-rtc-oldest-wait (fn-rtc-uses s)))))
                            (uses (fn-rtc-uses (mv-nth 0 (fn-rtc-grant-one s))))))))))
(local (defthm fn-hlp-grant-act-singleton
  (implies (and (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s)) (fn-rtc-oldest-wait (fn-rtc-uses s)))
           (and (consp (mv-nth 1 (fn-rtc-grant-one s))) (equal (cdr (mv-nth 1 (fn-rtc-grant-one s))) nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-grant-one fn-hld-mv-nth-0-cons fn-hlr-mv-nth-1-cons car-cons cdr-cons)
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth)))))))
(local (defthm fn-hlp-find-use-cons
  (implies (and (fn-rtc-find-use k uses) (consp u)) (fn-rtc-find-use k (cons u uses)))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-find-use car-cons cdr-cons) (theory 'minimal-theory))))))
(local (defthm fn-hlp-rearm-find-use
  (implies (fn-rtc-find-use k (fn-rtc-uses s)) (fn-rtc-find-use k (fn-rtc-uses (mv-nth 0 (fn-rtc-rearm s)))))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-rearm fn-rtc-arm-accept fn-rtc-arm-grant fn-rtc-issue-frame fn-hlp-find-use-cons mv-nth (:e mv-nth))
                                             (theory 'minimal-theory))))))
(local (defthm fn-hlp-rearm-slot
  (equal (fn-rtc-slot j (mv-nth 0 (fn-rtc-rearm s))) (fn-rtc-slot j s))
  :hints (("Goal" :use fn-rtc-slot-of-rearm :in-theory (theory 'minimal-theory)))))
(local (defthm fn-hlp-car-append (implies (consp x) (equal (car (append x y)) (car x)))))
(local (defthm fn-hlp-cdr-append (implies (consp x) (equal (cdr (append x y)) (append (cdr x) y)))))
(local (defthm fn-hlp-grant-stage
  (implies (and (fn-hll-invp s) (fn-hlp-front-p s opg)
                (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s))
                (fn-rtc-oldest-wait (cdr (fn-rtc-uses s)))
                (not (fn-rtc-oldest-wait (fn-rtc-remove-use (fn-rtc-key (fn-rtc-oldest-wait (cdr (fn-rtc-uses s)))) (cdr (fn-rtc-uses s)))))
                (< 0 (fn-rtc-npool (fn-rtc-config s)))
                (fn-rtc-live-p (nfix (fn-rtc-get 1 (fn-rtc-oldest-wait (cdr (fn-rtc-uses s)))))
                               (fn-rtc-get 2 (fn-rtc-oldest-wait (cdr (fn-rtc-uses s)))) s))
           (let* ((e (list :grant 0 0 opg (list :done 0)))
                  (w (fn-rtc-oldest-wait (cdr (fn-rtc-uses s))))
                  (acts (mv-nth 1 (fn-hll-x-step* e 1 s)))
                  (s2 (mv-nth 0 (fn-hll-x-step* e 1 s))))
             (and (consp acts)
                  (equal (fn-rtc-get 0 (car acts)) :pool)
                  (equal (fn-rtc-get 1 (car acts)) (nfix (fn-rtc-get 1 w)))
                  (equal (fn-rtc-get 2 (car acts)) (fn-rtc-get 2 w))
                  (equal (fn-rtc-get 3 (car acts)) (fn-rtc-get 3 w))
                  (fn-hlr-benign-actsp (cdr acts))
                  (fn-hll-invp s2)
                  (fn-rtc-find-use (list :pool (nfix (fn-rtc-get 1 w)) (fn-rtc-get 2 w) (fn-rtc-get 3 w)) (fn-rtc-uses s2))
                  (fn-rtc-live-p (nfix (fn-rtc-get 1 w)) (fn-rtc-get 2 w) s2))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hld-hll-invp-is-generic-invp fn-hlp-rearm-find-use fn-hlp-rearm-slot fn-rtc-with-accessors fn-rtc-slot-of-with fn-rtc-live-p
                                               fn-hlr-rearm car-cons cdr-cons fn-hlp-car-append fn-hlp-cdr-append binary-append)
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance fn-hlp-grant-step-main (s s))
                 (:instance fn-hlp-grant-act-fields (s (fn-rtc-with-uses (cdr (fn-rtc-uses s)) s)))
                 (:instance fn-hlp-grant-act-singleton (s (fn-rtc-with-uses (cdr (fn-rtc-uses s)) s)))
                 (:instance fn-hlp-grant-state-find (s (fn-rtc-with-uses (cdr (fn-rtc-uses s)) s)))
                 (:instance fn-hld-x-step*-keeps-invp (e (list :grant 0 0 opg (list :done 0))) (q 1) (st s))
                 (:instance fn-rtc-pool-grant-state-frame (j (nfix (fn-rtc-get 1 (fn-rtc-oldest-wait (cdr (fn-rtc-uses s))))))
                            (w (fn-rtc-oldest-wait (cdr (fn-rtc-uses s))))
                            (h (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s)))
                            (s (fn-rtc-with-uses (cdr (fn-rtc-uses s)) s)))
                 (:instance fn-rtc-grant-one-is-pool-grant-state (s (fn-rtc-with-uses (cdr (fn-rtc-uses s)) s)))
                 (:instance fn-hlr-rearm (s (mv-nth 0 (fn-rtc-grant-one (fn-rtc-with-uses (cdr (fn-rtc-uses s)) s)))) (id 0) (inc 0)))))))
(local (defthm fn-hlp-benign-cons
  (implies (and (consp x) (member-eq (fn-rtc-get 0 (car x)) '(:grant :pool :accept)) (fn-hlr-benign-actsp (cdr x)))
           (fn-hlr-benign-actsp x))
  :hints (("Goal" :in-theory (enable fn-hlr-benign-actsp)))))
(local (defthm fn-hlp-settle-pool
  (implies (and (fn-hll-invp s) (natp id) (natp inc) (natp op)
                (fn-rtc-find-use (list :pool id inc op) (fn-rtc-uses s))
                (fn-rtc-live-p id inc s)
                (equal (fn-rtc-get 0 pa) :pool) (equal (fn-rtc-get 1 pa) id) (equal (fn-rtc-get 2 pa) inc) (equal (fn-rtc-get 3 pa) op)
                (fn-hlr-benign-actsp rest) (natp fuel) (< 0 fuel))
           (fn-hld-workspace 0 id inc (mv-nth 0 (fn-hld-settle (cons pa rest) fuel s))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-settle-step fn-hlr-benign-tlf fn-hlr-benign-actsp-append fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e member-eq) member-eq natp zp (:type-prescription fn-rtc-h-buf))
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance fn-hlp-pool-step-ws)
                 (:instance fn-hlr-xstep-frames (st s) (e (list :pool id inc op (list :done 0))) (q 1) (id 0) (inc 0) (k 0) (j 0))
                 (:instance fn-hld-x-step*-keeps-invp (st s) (e (list :pool id inc op (list :done 0))) (q 1))
                 (:instance fn-hlr-settle-frames (work (append rest (true-list-fix (mv-nth 1 (fn-hll-x-step* (list :pool id inc op (list :done 0)) 1 s))))) (fuel (+ -1 fuel)) (st (mv-nth 0 (fn-hll-x-step* (list :pool id inc op (list :done 0)) 1 s))) (id 0) (inc 0) (k (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (list :pool id inc op) (fn-rtc-uses s))))) (j 0))
                 (:instance fn-hlp-workspace-exists (h 0) (k (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (list :pool id inc op) (fn-rtc-uses s))))) (st (mv-nth 0 (fn-hld-settle (append rest (true-list-fix (mv-nth 1 (fn-hll-x-step* (list :pool id inc op (list :done 0)) 1 s)))) (+ -1 fuel) (mv-nth 0 (fn-hll-x-step* (list :pool id inc op (list :done 0)) 1 s)))))))))))
(local (defthm fn-hlp-settle-grant
  (implies (and (fn-hll-invp s) (fn-hlp-front-p s opg)
                (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s))
                (fn-rtc-oldest-wait (cdr (fn-rtc-uses s)))
                (not (fn-rtc-oldest-wait (fn-rtc-remove-use (fn-rtc-key (fn-rtc-oldest-wait (cdr (fn-rtc-uses s)))) (cdr (fn-rtc-uses s)))))
                (< 0 (fn-rtc-npool (fn-rtc-config s)))
                (fn-rtc-live-p (nfix (fn-rtc-get 1 (fn-rtc-oldest-wait (cdr (fn-rtc-uses s)))))
                               (fn-rtc-get 2 (fn-rtc-oldest-wait (cdr (fn-rtc-uses s)))) s)
                (natp (fn-rtc-get 2 (fn-rtc-oldest-wait (cdr (fn-rtc-uses s)))))
                (natp (fn-rtc-get 3 (fn-rtc-oldest-wait (cdr (fn-rtc-uses s)))))
                (natp fuel) (< 2 fuel))
           (let ((w (fn-rtc-oldest-wait (cdr (fn-rtc-uses s)))))
             (fn-hld-workspace 0 (nfix (fn-rtc-get 1 w)) (fn-rtc-get 2 w)
                               (mv-nth 0 (fn-hld-settle (list (list :grant 0 0 opg (list nil))) fuel s)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-settle-step fn-hlr-benign-tlf fn-hlp-benign-cons fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e member-eq) member-eq natp zp binary-append (:type-prescription nfix))
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance fn-hlp-grant-stage)
                 (:instance fn-hlp-settle-pool
                            (s (mv-nth 0 (fn-hll-x-step* (list :grant 0 0 opg (list :done 0)) 1 s)))
                            (id (nfix (fn-rtc-get 1 (fn-rtc-oldest-wait (cdr (fn-rtc-uses s))))))
                            (inc (fn-rtc-get 2 (fn-rtc-oldest-wait (cdr (fn-rtc-uses s)))))
                            (op (fn-rtc-get 3 (fn-rtc-oldest-wait (cdr (fn-rtc-uses s)))))
                            (pa (car (mv-nth 1 (fn-hll-x-step* (list :grant 0 0 opg (list :done 0)) 1 s))))
                            (rest (cdr (mv-nth 1 (fn-hll-x-step* (list :grant 0 0 opg (list :done 0)) 1 s))))
                            (fuel (+ -1 fuel))))))))
(local (defthm fn-hlp-fuel-big
  (implies (fn-rtc-invp s) (and (natp (fn-hld-fuel s)) (< 3 (fn-hld-fuel s))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hld-fuel fn-hld-readers fn-rtc-nbufs fn-rtc-nslots fn-rtc-configp nfix natp) (theory 'minimal-theory))
           :use (fn-hlp-invp-configp)))))
(local (defthm fn-hlp-bsa-inv
  (implies (and (fn-hll-invp st) (natp r) (< r (expt 2 64)) (fn-rtc-free-slot 0 (fn-rtc-slots st)) (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses st))
                (fn-rtc-free-pool-buf 0 (fn-rtc-pool st) (fn-rtc-config st))
                (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses st))))
           (fn-hll-invp (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-dd-is-issue fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e equal) fn-hlp-w2 natp nfix fn-rtc-live-p fn-rtc-s-inc fn-rtc-s-status (:type-prescription fn-rtc-s-inc))
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance fn-hlp-accept-step (st st))
                 (:instance fn-hld-hll-invp-is-generic-invp (s st))
                 (:instance fn-hld-x-step*-keeps-invp (e (fn-hlp-bev st r)) (q 1))
                 (:instance fn-hlp-p-facts)
                 (:instance fn-hlp-sa1 (w (fn-hlp-w2 st r)) (p (fn-hlp-p st r)))
                 (:instance fn-hlp-acc-j-of-s1)
                 (:instance fn-hlp-dd-slot)
                 )))))
(local (defthm fn-hlp-bsa-front
  (implies (and (fn-hll-invp st) (natp r) (< r (expt 2 64)) (fn-rtc-free-slot 0 (fn-rtc-slots st)) (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses st))
                (fn-rtc-free-pool-buf 0 (fn-rtc-pool st) (fn-rtc-config st))
                (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses st))))
           (fn-hlp-front-p (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st)) (if (and (fn-rtc-free-slot 0 (fn-rtc-slots (fn-hlp-p st r))) (not (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses (fn-hlp-p st r))))) (+ 1 1 (fn-rtc-next-op (fn-hlp-p st r))) (+ 1 (fn-rtc-next-op (fn-hlp-p st r))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-dd-is-issue fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e equal) fn-hlp-w2 natp nfix fn-rtc-live-p fn-rtc-s-inc fn-rtc-s-status (:type-prescription fn-rtc-s-inc))
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance fn-hlp-accept-step (st st))
                 (:instance fn-hld-hll-invp-is-generic-invp (s st))
                 (:instance fn-hld-x-step*-keeps-invp (e (fn-hlp-bev st r)) (q 1))
                 (:instance fn-hlp-p-facts)
                 (:instance fn-hlp-sa1 (w (fn-hlp-w2 st r)) (p (fn-hlp-p st r)))
                 (:instance fn-hlp-acc-j-of-s1)
                 (:instance fn-hlp-dd-slot)
                 )))))
(local (defthm fn-hlp-bsa-free
  (implies (and (fn-hll-invp st) (natp r) (< r (expt 2 64)) (fn-rtc-free-slot 0 (fn-rtc-slots st)) (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses st))
                (fn-rtc-free-pool-buf 0 (fn-rtc-pool st) (fn-rtc-config st))
                (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses st))))
           (fn-rtc-free-pool-buf 0 (fn-rtc-pool (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))) (fn-rtc-config (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-dd-is-issue fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e equal) fn-hlp-w2 natp nfix fn-rtc-live-p fn-rtc-s-inc fn-rtc-s-status (:type-prescription fn-rtc-s-inc))
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance fn-hlp-accept-step (st st))
                 (:instance fn-hld-hll-invp-is-generic-invp (s st))
                 (:instance fn-hld-x-step*-keeps-invp (e (fn-hlp-bev st r)) (q 1))
                 (:instance fn-hlp-p-facts)
                 (:instance fn-hlp-sa1 (w (fn-hlp-w2 st r)) (p (fn-hlp-p st r)))
                 (:instance fn-hlp-acc-j-of-s1)
                 (:instance fn-hlp-dd-slot)
                 )))))
(local (defthm fn-hlp-bsa-wait
  (implies (and (fn-hll-invp st) (natp r) (< r (expt 2 64)) (fn-rtc-free-slot 0 (fn-rtc-slots st)) (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses st))
                (fn-rtc-free-pool-buf 0 (fn-rtc-pool st) (fn-rtc-config st))
                (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses st))))
           (fn-rtc-oldest-wait (cdr (fn-rtc-uses (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-dd-is-issue fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e equal) fn-hlp-w2 natp nfix fn-rtc-live-p fn-rtc-s-inc fn-rtc-s-status (:type-prescription fn-rtc-s-inc))
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance fn-hlp-accept-step (st st))
                 (:instance fn-hld-hll-invp-is-generic-invp (s st))
                 (:instance fn-hld-x-step*-keeps-invp (e (fn-hlp-bev st r)) (q 1))
                 (:instance fn-hlp-p-facts)
                 (:instance fn-hlp-sa1 (w (fn-hlp-w2 st r)) (p (fn-hlp-p st r)))
                 (:instance fn-hlp-acc-j-of-s1)
                 (:instance fn-hlp-dd-slot)
                 )))))
(local (defthm fn-hlp-bsa-uniq
  (implies (and (fn-hll-invp st) (natp r) (< r (expt 2 64)) (fn-rtc-free-slot 0 (fn-rtc-slots st)) (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses st))
                (fn-rtc-free-pool-buf 0 (fn-rtc-pool st) (fn-rtc-config st))
                (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses st))))
           (not (fn-rtc-oldest-wait (fn-rtc-remove-use (fn-rtc-key (fn-rtc-oldest-wait (cdr (fn-rtc-uses (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st)))))) (cdr (fn-rtc-uses (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-dd-is-issue fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e equal) fn-hlp-w2 natp nfix fn-rtc-live-p fn-rtc-s-inc fn-rtc-s-status (:type-prescription fn-rtc-s-inc))
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance fn-hlp-accept-step (st st))
                 (:instance fn-hld-hll-invp-is-generic-invp (s st))
                 (:instance fn-hld-x-step*-keeps-invp (e (fn-hlp-bev st r)) (q 1))
                 (:instance fn-hlp-p-facts)
                 (:instance fn-hlp-sa1 (w (fn-hlp-w2 st r)) (p (fn-hlp-p st r)))
                 (:instance fn-hlp-acc-j-of-s1)
                 (:instance fn-hlp-dd-slot)
                 )))))
(local (defthm fn-hlp-bsa-npool
  (implies (and (fn-hll-invp st) (natp r) (< r (expt 2 64)) (fn-rtc-free-slot 0 (fn-rtc-slots st)) (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses st))
                (fn-rtc-free-pool-buf 0 (fn-rtc-pool st) (fn-rtc-config st))
                (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses st))))
           (< 0 (fn-rtc-npool (fn-rtc-config (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-dd-is-issue fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e equal) fn-hlp-w2 natp nfix fn-rtc-live-p fn-rtc-s-inc fn-rtc-s-status (:type-prescription fn-rtc-s-inc))
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance fn-hlp-accept-step (st st))
                 (:instance fn-hld-hll-invp-is-generic-invp (s st))
                 (:instance fn-hld-x-step*-keeps-invp (e (fn-hlp-bev st r)) (q 1))
                 (:instance fn-hlp-p-facts)
                 (:instance fn-hlp-sa1 (w (fn-hlp-w2 st r)) (p (fn-hlp-p st r)))
                 (:instance fn-hlp-acc-j-of-s1)
                 (:instance fn-hlp-dd-slot)
                 (:instance fn-hlp-npool-pos (s (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))))
                 (:instance fn-hld-hll-invp-is-generic-invp (s (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))))
                 (:instance fn-hlp-bsa-inv) (:instance fn-hlp-bsa-free))))))
(local (defthm fn-hlp-w2-fields
  (implies (and (fn-rtc-invp st) (natp r) (fn-rtc-free-slot 0 (fn-rtc-slots st)) (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses st)))
           (and (equal (fn-rtc-get 1 (fn-hlp-w2 st r)) (fn-rtc-free-slot 0 (fn-rtc-slots st)))
                (equal (fn-rtc-get 2 (fn-hlp-w2 st r)) (+ 1 (fn-rtc-s-inc (fn-rtc-slot (fn-rtc-free-slot 0 (fn-rtc-slots st)) st))))
                (equal (fn-rtc-get 3 (fn-hlp-w2 st r)) (fn-rtc-next-op st))))
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-w2 fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e binary-+) (:e unary--))
                                             (theory 'minimal-theory))
           :use ((:instance fn-hlp-acc-j-of-s1))))))
(local (defthm fn-hlp-bsa-w
  (implies (and (fn-hll-invp st) (natp r) (< r (expt 2 64)) (fn-rtc-free-slot 0 (fn-rtc-slots st)) (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses st))
                (fn-rtc-free-pool-buf 0 (fn-rtc-pool st) (fn-rtc-config st))
                (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses st))))
           (equal (fn-rtc-oldest-wait (cdr (fn-rtc-uses (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st)))))
                  (fn-hlp-w2 st r)))
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-dd-is-issue) (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance fn-hlp-accept-step (st st))
                 (:instance fn-hld-hll-invp-is-generic-invp (s st))
                 (:instance fn-hlp-p-facts)
                 (:instance fn-hlp-sa1 (w (fn-hlp-w2 st r)) (p (fn-hlp-p st r))))))))
(local (defthm fn-hlp-bsa-j
  (implies (and (fn-hll-invp st) (natp r) (< r (expt 2 64)) (fn-rtc-free-slot 0 (fn-rtc-slots st)) (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses st))
                (fn-rtc-free-pool-buf 0 (fn-rtc-pool st) (fn-rtc-config st))
                (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses st))))
           (equal (nfix (fn-rtc-get 1 (fn-rtc-oldest-wait (cdr (fn-rtc-uses (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))))))) (fn-rtc-free-slot 0 (fn-rtc-slots st))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-bsa-w fn-hlp-w2-fields posp natp nfix (:type-prescription fn-rtc-free-slot) (:type-prescription nfix) (:type-prescription fn-rtc-s-inc) fn-rtc-get-of-cons car-cons cdr-cons) (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance fn-hld-hll-invp-is-generic-invp (s st)) (:instance fn-hlp-bsa-w) (:instance fn-hlp-accept-j-free (j (fn-rtc-free-slot 0 (fn-rtc-slots st))) (kind :wait) (inc 0)) (:instance fn-hlp-w2-fields))))))
(local (defthm fn-hlp-bsa-jinc
  (implies (and (fn-hll-invp st) (natp r) (< r (expt 2 64)) (fn-rtc-free-slot 0 (fn-rtc-slots st)) (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses st))
                (fn-rtc-free-pool-buf 0 (fn-rtc-pool st) (fn-rtc-config st))
                (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses st))))
           (equal (fn-rtc-get 2 (fn-rtc-oldest-wait (cdr (fn-rtc-uses (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st)))))) (+ 1 (fn-rtc-s-inc (fn-rtc-slot (fn-rtc-free-slot 0 (fn-rtc-slots st)) st)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-bsa-w fn-hlp-w2-fields posp natp nfix (:type-prescription fn-rtc-free-slot) (:type-prescription nfix) (:type-prescription fn-rtc-s-inc) fn-rtc-get-of-cons car-cons cdr-cons) (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance fn-hld-hll-invp-is-generic-invp (s st)) (:instance fn-hlp-bsa-w) (:instance fn-hlp-accept-j-free (j (fn-rtc-free-slot 0 (fn-rtc-slots st))) (kind :wait) (inc 0)) (:instance fn-hlp-w2-fields))))))
(local (defthm fn-hlp-bsa-op
  (implies (and (fn-hll-invp st) (natp r) (< r (expt 2 64)) (fn-rtc-free-slot 0 (fn-rtc-slots st)) (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses st))
                (fn-rtc-free-pool-buf 0 (fn-rtc-pool st) (fn-rtc-config st))
                (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses st))))
           (natp (fn-rtc-get 3 (fn-rtc-oldest-wait (cdr (fn-rtc-uses (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-bsa-w fn-hlp-w2-fields posp natp nfix (:type-prescription fn-rtc-free-slot) (:type-prescription nfix) (:type-prescription fn-rtc-s-inc) fn-rtc-get-of-cons car-cons cdr-cons) (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance fn-hld-hll-invp-is-generic-invp (s st)) (:instance fn-hlp-bsa-w) (:instance fn-hlp-accept-j-free (j (fn-rtc-free-slot 0 (fn-rtc-slots st))) (kind :wait) (inc 0)) (:instance fn-hlp-w2-fields) (:instance fn-hlr-next-op-natp (s st)))))))
(local (defthm fn-hlp-dd-slot-rw
  (implies (and (fn-rtc-invp st) (natp r) (fn-rtc-free-slot 0 (fn-rtc-slots st)) (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses st)))
           (equal (fn-rtc-slot (fn-rtc-free-slot 0 (fn-rtc-slots st)) (fn-hlp-dd st r)) (list (+ 1 (fn-rtc-s-inc (fn-rtc-slot (fn-rtc-free-slot 0 (fn-rtc-slots st)) st))) :live r)))
  :hints (("Goal" :use (fn-hlp-dd-slot) :in-theory (theory 'minimal-theory)))))
(local (defthm fn-hlp-bsa-live
  (implies (and (fn-hll-invp st) (natp r) (< r (expt 2 64)) (fn-rtc-free-slot 0 (fn-rtc-slots st)) (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses st))
                (fn-rtc-free-pool-buf 0 (fn-rtc-pool st) (fn-rtc-config st))
                (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses st))))
           (fn-rtc-live-p (fn-rtc-free-slot 0 (fn-rtc-slots st)) (+ 1 (fn-rtc-s-inc (fn-rtc-slot (fn-rtc-free-slot 0 (fn-rtc-slots st)) st))) (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-live-p fn-rtc-s-inc fn-rtc-s-status natp nfix (:type-prescription fn-rtc-s-inc) fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix)
                                               fn-hlp-dd-slot-rw fn-hlp-rearm-slot)
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance fn-hlp-accept-step (st st)) (:instance fn-hld-hll-invp-is-generic-invp (s st)))))))
(local (defthm fn-hlp-begin-case-g
  (implies (and (fn-hll-invp st) (mv-nth 1 (fn-hld-begin r st))
                (fn-rtc-free-pool-buf 0 (fn-rtc-pool st) (fn-rtc-config st))
                (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses st))))
           (fn-hld-workspace 0 (mv-nth 1 (fn-hld-begin r st)) (mv-nth 2 (fn-hld-begin r st)) (mv-nth 0 (fn-hld-begin r st))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hlr-benign-tlf true-list-fix fn-hlp-settle-skip fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e member-eq) member-eq natp zp
                                               (:type-prescription nfix) (:type-prescription fn-rtc-free-slot))
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :cases ((and (fn-rtc-free-slot 0 (fn-rtc-slots (fn-hlp-p st r))) (not (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses (fn-hlp-p st r))))))
           :use (fn-hlp-begin-success fn-hlp-begin-ids (:instance fn-hlp-begin-parts)
                 (:instance fn-hlp-accept-step) (:instance fn-hlp-dd-is-issue)
                 (:instance fn-hlp-p-facts) (:instance fn-hlp-fuel-big (s (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))))
                 (:instance fn-hlp-sa1 (w (fn-hlp-w2 st r)) (p (fn-hlp-p st r)))
                 (:instance fn-hlp-settle-grant (s (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))) (opg (if (and (fn-rtc-free-slot 0 (fn-rtc-slots (fn-hlp-p st r))) (not (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses (fn-hlp-p st r))))) (+ 1 1 (fn-rtc-next-op (fn-hlp-p st r))) (+ 1 (fn-rtc-next-op (fn-hlp-p st r)))))
                            (fuel (fn-hld-fuel (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st)))))
                 (:instance fn-hlp-settle-grant (s (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))) (opg (if (and (fn-rtc-free-slot 0 (fn-rtc-slots (fn-hlp-p st r))) (not (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses (fn-hlp-p st r))))) (+ 1 1 (fn-rtc-next-op (fn-hlp-p st r))) (+ 1 (fn-rtc-next-op (fn-hlp-p st r)))))
                            (fuel (+ -1 (fn-hld-fuel (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))))))
                 (:instance fn-hld-hll-invp-is-generic-invp (s (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))))
                 (:instance fn-hld-hll-invp-is-generic-invp (s st))
                 (:instance fn-hlp-bsa-inv) (:instance fn-hlp-bsa-front) (:instance fn-hlp-bsa-free) (:instance fn-hlp-bsa-wait) (:instance fn-hlp-bsa-uniq) (:instance fn-hlp-bsa-npool) (:instance fn-hlp-bsa-j) (:instance fn-hlp-bsa-jinc) (:instance fn-hlp-bsa-op) (:instance fn-hlp-bsa-live))))))
(local (defthm fn-hlp-owp-cons-wait-nonnil
  (implies (equal (fn-rtc-get 0 u) :wait) (fn-rtc-oldest-wait (cons u rest)))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-oldest-wait car-cons cdr-cons fn-rtc-get (:e zp) (:e nfix)) (theory 'minimal-theory))
           :cases ((consp u))))))
(local (defthm fn-hlp-dd-accept-only
  (implies (and (fn-rtc-invp st) (natp r) (fn-rtc-free-slot 0 (fn-rtc-slots st)) (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses st))
                (or (not (fn-rtc-free-pool-buf 0 (fn-rtc-pool st) (fn-rtc-config st)))
                    (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses st))))
           (fn-hlp-accept-onlyp (mv-nth 1 (fn-rtc-rearm (fn-hlp-dd st r)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-kind-out-cons fn-hlp-bev fn-rtc-key car-cons cdr-cons fn-rtc-get-of-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e equal))
                                             (theory 'minimal-theory))
           :use ((:instance fn-hlp-dd-facts)
                 (:instance fn-hlp-rearm-accept-only (s (fn-hlp-dd st r)))
                 (:instance fn-hlp-remove-use-keeps-other-kind (k :grant) (id 0) (inc 0) (key (fn-rtc-key (fn-hlp-bev st r))) (uses (fn-rtc-uses st))))))))
(local (defthm fn-hlp-begin-case-n
  (implies (and (fn-hll-invp st) (mv-nth 1 (fn-hld-begin r st))
                (or (not (fn-rtc-free-pool-buf 0 (fn-rtc-pool st) (fn-rtc-config st)))
                    (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses st))))
           (fn-rtc-oldest-wait (fn-rtc-uses (mv-nth 0 (fn-hld-begin r st)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hld-hll-invp-is-generic-invp fn-hlp-accept-only-tlf fn-hlp-rearm-wait fn-hlp-owp-cons-wait-nonnil
                                               fn-rtc-issue-frame fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix))
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use (fn-hlp-begin-success (:instance fn-hlp-begin-parts)
                 (:instance fn-hlp-accept-step)
                 (:instance fn-hlp-dd-accept-only)
                 (:instance fn-hlp-dd-facts)
                 (:instance fn-hlp-settle-accept-only (work (true-list-fix (mv-nth 1 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))))
                            (fuel (fn-hld-fuel (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))))
                            (st (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))))
                 (:instance fn-hlp-rearm-wait (s (fn-hlp-dd st r))))))))
(local (defthm fn-hlp-step-parts
  (and (equal (mv-nth 0 (fn-hll-step* s e q)) (mv-nth 0 (fn-hll-step s e q)))
       (equal (mv-nth 1 (fn-hll-step* s e q)) (mv-nth 1 (fn-hll-step s e q))))
  :hints (("Goal" :in-theory (union-theories '(fn-hll-step mv-nth) (theory 'minimal-theory))))))
(local (defthm fn-hlp-actions-okp-of-subset
  (implies (and (fn-hll-invp s) (subsetp-equal acts (mv-nth 1 (fn-hll-step s e q))))
           (fn-rtc-actions-okp acts (mv-nth 0 (fn-hll-step s e q))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-hlr-ind acts)
           :in-theory (union-theories '((:induction fn-hlr-ind) subsetp-equal fn-rtc-actions-okp fn-rtc-recorded-key)
                                      (theory 'minimal-theory)))
          ("Subgoal *1/1" :use ((:instance fn-hll-every-action-is-outstanding (a (car acts))))))))
(local (defthm fn-hlp-invp-pool-len
  (implies (fn-rtc-invp s) (equal (len (fn-rtc-pool s)) (fn-rtc-nbufs (fn-rtc-config s))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-core-invp) (theory 'minimal-theory))
           :use fn-rtc-invp-implies-core-invp))))
(local (defthm fn-hlp-grant-one-leases-in
  (implies (and (fn-rtc-invp s)
                (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s))
                (fn-rtc-oldest-wait (fn-rtc-uses s)))
           (fn-rtc-in-leased-p (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s))
                               (mv-nth 0 (fn-rtc-grant-one s))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-grant-one fn-rtc-in-leased-p fn-rtc-buffer-of-with fn-rtc-b-owner
                                               fn-rtc-with-accessors
                                               fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e binary-+) (:e unary--)
                                               (:e mv-nth) mv-nth natp nfix fn-rtc-pool-buf-p)
                                             (theory 'minimal-theory))
           :use (fn-hlp-invp-pool-len
                 (:instance fn-rtc-free-pool-buf-pool-index (i 0) (pool (fn-rtc-pool s)) (cfg (fn-rtc-config s))))))))
(local (defthm fn-hlp-replace-use-pool-op
  (implies (member-equal w uses)
           (fn-rtc-pool-op-p (fn-rtc-get 3 w)
                             (fn-rtc-replace-use (fn-rtc-key w) (list :pool id inc (fn-rtc-get 3 w) hd) uses)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-rtc-replace-use (fn-rtc-key w) (list :pool id inc (fn-rtc-get 3 w) hd) uses)
           :in-theory (e/d (fn-rtc-replace-use fn-rtc-pool-op-p fn-rtc-key) (fn-rtc-get)))
          ("Subgoal *1/2" :in-theory (e/d (fn-rtc-replace-use fn-rtc-pool-op-p fn-rtc-key fn-rtc-get-of-cons) (fn-rtc-get))))))

; -----------------------------------------------------------------------------
; The establishments.  fn-hll-invp is the leased layer's invariant: fn-hld-init establishes it and every
; other driver keeps it (fn-hld-*-keeps-invp), so it holds of every state the host has.

; --- Local proof steps for G (no :grant outstanding in any state the host keeps; the host path's instance is natural).
(local (defun fn-hlp-gin (w op)
  (declare (xargs :guard t))
  (if (consp w)
      (or (and (equal (fn-rtc-get 0 (car w)) :grant) (equal (fn-rtc-get 1 (car w)) 0)
               (equal (fn-rtc-get 2 (car w)) 0) (equal (fn-rtc-get 3 (car w)) op))
          (fn-hlp-gin (cdr w) op))
    nil)))
(local (defthm fn-hlp-gin-append
  (equal (fn-hlp-gin (append a b) op) (or (fn-hlp-gin a op) (fn-hlp-gin b op)))))
(local (defthm fn-hlp-gin-tlf
  (equal (fn-hlp-gin (true-list-fix x) op) (fn-hlp-gin x op))
  :hints (("Goal" :in-theory (enable true-list-fix)))))
(local (defthm fn-hlp-rm
  (let* ((r (fn-rtc-rearm d)) (s2 (mv-nth 0 r)) (acts (mv-nth 1 r)))
    (implies (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses s2))
             (or (and (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses d))
                      (equal (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses s2)) (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses d))))
                 (fn-hlp-gin acts (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses s2))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-rearm fn-rtc-arm-accept fn-rtc-arm-grant fn-rtc-issue-frame fn-rtc-kind-out-cons fn-rtc-kind-op fn-hlp-gin
                                               mv-nth (:e mv-nth) fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e binary-+) (:e unary--) (:e equal)
                                               append (:e append) nfix binary-append (:type-prescription fn-rtc-next-op))
                                             (theory 'minimal-theory))))))
(local (defthm fn-hlp-replace-grant
  (implies (and (not (equal (fn-rtc-get 0 key) :grant)) (not (equal (fn-rtc-get 0 u2) :grant)))
           (and (equal (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-replace-use key u2 uses)) (fn-rtc-kind-out-p :grant 0 0 uses))
                (equal (fn-rtc-kind-op :grant 0 0 (fn-rtc-replace-use key u2 uses)) (fn-rtc-kind-op :grant 0 0 uses))))
  :hints (("Goal" :induct (fn-rtc-replace-use key u2 uses)
           :in-theory (union-theories '((:induction fn-rtc-replace-use) fn-rtc-replace-use fn-rtc-kind-out-p fn-rtc-kind-op fn-rtc-key
                                        fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix))
                                      (theory 'minimal-theory))))))
(local (defthm fn-hlp-key0
  (equal (fn-rtc-get 0 (fn-rtc-key x)) (fn-rtc-get 0 x))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-key fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix)) (theory 'minimal-theory))))))
(local (defthm fn-hlp-grant-one-grant
  (and (equal (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-rtc-grant-one s)))) (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses s)))
       (equal (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-rtc-grant-one s)))) (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses s))))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-grant-one-is-pool-grant-state fn-rtc-pool-grant-state-frame fn-hlp-replace-grant fn-rtc-pool-grant-use-fields
                                               fn-rtc-oldest-wait-kind fn-hlp-key0 mv-nth (:e mv-nth))
                                             (theory 'minimal-theory))
           :use ((:instance fn-rtc-grant-one-is-pool-grant-state)
                 (:instance fn-rtc-pool-grant-state-frame (w (fn-rtc-oldest-wait (fn-rtc-uses s))) (h (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s))) (j 0))
                 (:instance fn-rtc-pool-grant-use-fields (w (fn-rtc-oldest-wait (fn-rtc-uses s))) (h (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s)))))))))
(local (defthm fn-hlp-mv0 (equal (mv-nth 0 x) (car x)) :hints (("Goal" :in-theory (enable mv-nth)))))
(local (defthm fn-hlp-g1-consp (consp (fn-rtc-grant-one s))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-grant-one) (theory 'minimal-theory))))))
(local (defthm fn-hlp-grant-one-grant-car
  (and (equal (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (car (fn-rtc-grant-one s)))) (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses s)))
       (equal (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses (car (fn-rtc-grant-one s)))) (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses s))))
  :hints (("Goal" :use fn-hlp-grant-one-grant :in-theory (union-theories '(fn-hlp-mv0) (theory 'minimal-theory))))))
(local (defthm fn-hlp-grant-n-grant
  (and (equal (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-rtc-grant n s)))) (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses s)))
       (equal (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-rtc-grant n s)))) (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses s))))
  :hints (("Goal" :induct (fn-rtc-grant n s)
           :in-theory (union-theories '((:induction fn-rtc-grant) fn-rtc-grant fn-hlp-grant-one-grant fn-hlp-grant-one-grant-car fn-hlp-g1-consp fn-hld-mv-nth-0-cons fn-hlr-mv-nth-1-cons zp mv-nth (:e mv-nth))
                                      (theory 'minimal-theory))
           :expand ((fn-rtc-grant n s))))))
(local (defun fn-hlp-guniq (uses)
  (declare (xargs :guard t))
  (if (consp uses)
      (and (natp (fn-rtc-get 3 (car uses)))
           (implies (and (equal (fn-rtc-get 0 (car uses)) :grant) (equal (fn-rtc-get 1 (car uses)) 0) (equal (fn-rtc-get 2 (car uses)) 0))
                    (not (fn-rtc-kind-out-p :grant 0 0 (cdr uses))))
           (fn-hlp-guniq (cdr uses)))
    t)))
(local (defthm fn-hlp-guniq-from-okp
  (implies (and (fn-rtc-uses-okp uses s) (fn-rtc-uses-ops-natp uses)) (fn-hlp-guniq uses))
  :hints (("Goal" :induct (fn-rtc-uses-okp uses s)
           :in-theory (union-theories '(fn-rtc-uses-okp fn-rtc-uses-ops-natp fn-hlp-guniq (:e member-equal) member-equal) (theory 'minimal-theory))))))
(local (defthm fn-hlp-ru
  (implies (and (fn-hlp-guniq uses) (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-remove-use key uses)))
           (and (fn-rtc-kind-out-p :grant 0 0 uses)
                (equal (fn-rtc-kind-op :grant 0 0 (fn-rtc-remove-use key uses)) (fn-rtc-kind-op :grant 0 0 uses))
                (not (equal key (list :grant 0 0 (fn-rtc-kind-op :grant 0 0 uses))))))
  :hints (("Goal" :induct (fn-rtc-remove-use key uses)
           :in-theory (union-theories '((:induction fn-rtc-remove-use) fn-rtc-remove-use fn-hlp-guniq fn-rtc-kind-out-p fn-rtc-kind-op fn-rtc-key natp nfix
                                        fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e equal))
                                      (theory 'minimal-theory))))))
(local (defthm fn-hlp-end-lease-uses
  (equal (fn-rtc-uses (fn-rtc-end-lease u e s)) (fn-rtc-uses s))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-end-lease fn-rtc-with-accessors) (theory 'minimal-theory))))))
(local (defthm fn-hlp-eu-uses
  (implies (and (fn-rtc-completionp e) (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))
           (equal (fn-rtc-uses (fn-rtc-end-use s e)) (fn-rtc-remove-use (fn-rtc-key e) (fn-rtc-uses s))))
  :hints (("Goal" :in-theory (union-theories '(fn-hlr-retire-keeps fn-hlp-end-lease-uses fn-rtc-with-accessors) (theory 'minimal-theory))
           :use (fn-rtc-end-use-structure)))))
(local (defthm fn-hlp-eu-else
  (implies (not (and (fn-rtc-completionp e) (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))
           (equal (fn-rtc-end-use s e) s))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-end-use) (theory 'minimal-theory))))))
(local (defthm fn-hlp-e1k
  (implies (and (fn-rtc-uses-okp (fn-rtc-uses s) s) (fn-rtc-uses-ops-natp (fn-rtc-uses s))
                (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (fn-rtc-end-use s e))))
           (and (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses s))
                (equal (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses (fn-rtc-end-use s e))) (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses s)))
                (or (not (equal (fn-rtc-key e) (list :grant 0 0 (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses s)))))
                    (not (fn-rtc-completionp e)))))
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-eu-uses fn-hlp-eu-else) (theory 'minimal-theory))
           :cases ((and (fn-rtc-completionp e) (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))
           :use ((:instance fn-hlp-guniq-from-okp (uses (fn-rtc-uses s)) (s s))
                 (:instance fn-hlp-ru (uses (fn-rtc-uses s)) (key (fn-rtc-key e)))
                 (:instance fn-hlp-kind-op-finds-use (kind :grant) (id 0) (inc 0) (uses (fn-rtc-uses s))))))))
(local (defthm fn-hlp-rm1
  (implies (and (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-rtc-rearm d))))
                (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses d))))
           (fn-hlp-gin (mv-nth 1 (fn-rtc-rearm d)) (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-rtc-rearm d))))))
  :hints (("Goal" :use fn-hlp-rm :in-theory (theory 'minimal-theory)))))
(local (defthm fn-hlp-rm2
  (implies (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses d))
           (and (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-rtc-rearm d))))
                (equal (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-rtc-rearm d)))) (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses d)))))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-rearm fn-rtc-arm-accept fn-rtc-arm-grant fn-rtc-issue-frame fn-rtc-kind-out-cons fn-rtc-kind-op
                                               mv-nth (:e mv-nth) fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e equal))
                                             (theory 'minimal-theory))))))
(local (defthm fn-hlp-ru2
  (implies (and (fn-hlp-guniq uses) (fn-rtc-kind-out-p :grant 0 0 uses)
                (not (equal key (list :grant 0 0 (fn-rtc-kind-op :grant 0 0 uses)))))
           (and (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-remove-use key uses))
                (equal (fn-rtc-kind-op :grant 0 0 (fn-rtc-remove-use key uses)) (fn-rtc-kind-op :grant 0 0 uses))))
  :hints (("Goal" :induct (fn-rtc-remove-use key uses)
           :in-theory (union-theories '((:induction fn-rtc-remove-use) fn-rtc-remove-use fn-hlp-guniq fn-rtc-kind-out-p fn-rtc-kind-op fn-rtc-key natp nfix
                                        fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e equal))
                                      (theory 'minimal-theory))))))
(local (defthm fn-hlp-ea2
  (implies (and (fn-rtc-invp s) (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses s))))
           (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (fn-rtc-end-use s e)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory) :use (fn-hlp-e1k fn-rtc-invp-ops-natp fn-rtc-invp-uses-okp)))))
(local (defthm fn-hlp-eb2
  (implies (and (fn-rtc-invp s) (fn-rtc-completionp e) (equal (fn-rtc-key e) (list :grant 0 0 (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses s)))))
           (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (fn-rtc-end-use s e)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory) :use (fn-hlp-e1k fn-rtc-invp-ops-natp fn-rtc-invp-uses-okp)))))
(local (defthm fn-hlp-ec2
  (implies (and (fn-rtc-invp s) (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses s))
                (not (equal (fn-rtc-key e) (list :grant 0 0 (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses s))))))
           (and (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (fn-rtc-end-use s e)))
                (equal (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses (fn-rtc-end-use s e))) (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses s)))))
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-eu-uses fn-hlp-eu-else) (theory 'minimal-theory))
           :cases ((and (fn-rtc-completionp e) (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))
           :use ((:instance fn-hlp-guniq-from-okp (uses (fn-rtc-uses s)) (s s)) fn-rtc-invp-ops-natp fn-rtc-invp-uses-okp
                 (:instance fn-hlp-ru2 (uses (fn-rtc-uses s)) (key (fn-rtc-key e))))))))
(local (defthm fn-hlp-pmain
  (implies (and (fn-rtc-invp s) (not (member-eq (fn-rtc-get 0 e) '(:accept :hand)))
                (or (not (equal (fn-rtc-key e) (list :grant 0 0 (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses s))))) (fn-rtc-completionp e))
                (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-hll-step* s e q)))))
           (or (and (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses s))
                    (equal (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-hll-step* s e q)))) (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses s)))
                    (not (equal (fn-rtc-key e) (list :grant 0 0 (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses s))))))
               (fn-hlp-gin (mv-nth 1 (fn-hll-step* s e q)) (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-hll-step* s e q)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hlp-ea2) (:instance fn-hlp-eb2) (:instance fn-hlp-ec2))
           :cases ((fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses s)) (equal (fn-rtc-key e) (list :grant 0 0 (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses s)))))
           :in-theory (union-theories '(fn-hll-step* fn-rtc-hand-delivers-p fn-rtc-e-kind fn-hlr-deliver-is-mstate fn-hll-close-branch fn-hlp-grant-n-grant
                                        fn-rtc-ev fn-rtc-with-accessors fn-rtc-make-accessors fn-hlp-gin-append fn-hlp-rm1 fn-hlp-rm2 fn-hlp-ea2 fn-hlp-eb2 fn-hlp-ec2
                                        fn-hld-mv-nth-0-cons fn-hlr-mv-nth-1-cons fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix)
                                        (:e member-eq) member-eq (:e eq) eq (:e equal) binary-append (:e consp) nfix)
                                      (set-difference-theories (theory 'minimal-theory) '(mv-nth)))))))
(local (defthm fn-hlp-gcomp0
  (fn-rtc-completionp (list :grant 0 0 (fn-rtc-kind-op :grant 0 0 uses) (list :done 0)))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-completionp fn-rtc-outcomep fn-hlp-kind-op-natp natp
                                               fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e member-eq) member-eq (:e len) len (:e true-listp) true-listp (:e equal))
                                             (theory 'minimal-theory))))))
(local (defthm fn-hlp-pmain-x
  (implies (and (fn-rtc-invp s) (member-eq (fn-rtc-get 0 e) '(:grant :pool :close :opened))
                (or (not (equal (fn-rtc-key e) (list :grant 0 0 (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses s))))) (fn-rtc-completionp e))
                (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-hll-x-step* e q s)))))
           (or (and (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses s))
                    (equal (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-hll-x-step* e q s)))) (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses s)))
                    (not (equal (fn-rtc-key e) (list :grant 0 0 (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses s))))))
               (fn-hlp-gin (mv-nth 1 (fn-hll-x-step* e q s)) (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-hll-x-step* e q s)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hll-x-step*-is fn-rtc-invp-implies-st-p fn-hlp-landed-not-in (:e member-eq) member-eq)
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use (fn-hlp-pmain (:instance fn-hlp-landed-not-in (s s)))))))
(local (defthm fn-hlp-pmain-y
  (implies (and (fn-rtc-invp s) (not (member-eq (fn-rtc-get 0 e) '(:accept :hand :recv :pread)))
                (or (not (equal (fn-rtc-key e) (list :grant 0 0 (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses s))))) (fn-rtc-completionp e))
                (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-hll-x-step* e q s)))))
           (or (and (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses s))
                    (equal (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-hll-x-step* e q s)))) (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses s)))
                    (not (equal (fn-rtc-key e) (list :grant 0 0 (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses s))))))
               (fn-hlp-gin (mv-nth 1 (fn-hll-x-step* e q s)) (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-hll-x-step* e q s)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hll-x-step*-is fn-rtc-invp-implies-st-p fn-hlp-landed-not-in (:e member-eq) member-eq)
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use (fn-hlp-pmain (:instance fn-hlp-landed-not-in (s s)))))))
(local (defthm fn-hlp-sent-leaves-no-grant-pre
  (implies (and (fn-hll-invp st) (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses st))))
           (implies (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-hll-x-step* (fn-hld-sent-event id inc op outcome) 1 st))))
                    (fn-hlp-gin (mv-nth 1 (fn-hll-x-step* (fn-hld-sent-event id inc op outcome) 1 st))
                                (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-hll-x-step* (fn-hld-sent-event id inc op outcome) 1 st)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hld-sent-event fn-hld-hll-invp-is-generic-invp fn-rtc-key fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix)
                                               (:e equal) cons-equal (:e member-eq) member-eq)
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance fn-hlp-pmain-y (s st) (e (fn-hld-sent-event id inc op outcome)) (q 1)))))))
(local (defun fn-hlp-ev (a) (declare (xargs :guard t)) (list (fn-rtc-get 0 a) (fn-rtc-get 1 a) (fn-rtc-get 2 a) (fn-rtc-get 3 a) (list :done 0))))
(local (defthm fn-hlp-cov-step
  (implies (and (fn-rtc-invp st) (consp work) (member-eq (fn-rtc-get 0 (car work)) '(:grant :pool :close :opened))
                (implies (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses st)) (fn-hlp-gin work (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses st))))
                (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-hll-x-step* (fn-hlp-ev (car work)) 1 st)))))
           (fn-hlp-gin (append (cdr work) (true-list-fix (mv-nth 1 (fn-hll-x-step* (fn-hlp-ev (car work)) 1 st))))
                       (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-hll-x-step* (fn-hlp-ev (car work)) 1 st))))))
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-gin-append fn-hlp-gin-tlf fn-hlp-ev fn-rtc-key fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix)
                                               (:e equal) cons-equal fn-hlp-gcomp0 (:e member-eq) member-eq)
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :do-not-induct t
           :expand ((fn-hlp-gin work (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses st))))
           :use ((:instance fn-hlp-pmain-x (s st) (e (fn-hlp-ev (car work))) (q 1))
                 (:instance fn-hlp-gcomp0 (uses (fn-rtc-uses st))))))))
(local (defthm fn-hlp-settle-no-grant
  (implies (and (fn-hll-invp st)
                (implies (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses st))
                         (fn-hlp-gin work (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses st))))
                (null (mv-nth 1 (fn-hld-settle work fuel st))))
           (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-hld-settle work fuel st))))))
  :hints (("Goal" :induct (fn-hld-settle work fuel st)
           :in-theory (union-theories '((:induction fn-hld-settle) fn-hld-settle fn-hlp-gin)
                                      (set-difference-theories (theory 'minimal-theory) '(mv-nth))))
          ("Subgoal *1/2" :in-theory (union-theories '(fn-hlp-settle-step fn-hlr-benign-tlf fn-hlp-ev fn-rtc-get-of-cons (:e fn-rtc-get) (:e member-eq) member-eq fn-hld-hll-invp-is-generic-invp)
                                                     (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance fn-hlp-cov-step (work work))
                 (:instance fn-hld-x-step*-keeps-invp (e (fn-hlp-ev (car work))) (q 1))))
          ("Subgoal *1/3" :in-theory (union-theories '(fn-hlp-settle-skip fn-hlp-gin (:e member-eq) member-eq fn-rtc-get-of-cons (:e fn-rtc-get))
                                                     (set-difference-theories (theory 'minimal-theory) '(mv-nth)))))))
(local (defthm fn-hlp-ru-subset
  (implies (and (fn-hlp-guniq uses) (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-remove-use key uses)))
           (fn-rtc-kind-out-p :grant 0 0 uses))
  :rule-classes nil
  :hints (("Goal" :use fn-hlp-ru :in-theory (theory 'minimal-theory)))))
(local (defthm fn-hlp-begin-sa-cov
  (implies (and (fn-hll-invp st) (natp r) (< r (expt 2 64)) (fn-rtc-free-slot 0 (fn-rtc-slots st))
                (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses st))
                (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses st))))
           (implies (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))))
                    (fn-hlp-gin (mv-nth 1 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))
                                (fn-rtc-kind-op :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st)))))))
  :hints (("Goal" :in-theory (union-theories '(fn-hld-hll-invp-is-generic-invp fn-hlp-rm1 fn-rtc-kind-out-cons fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e equal))
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :do-not-induct t
           :use ((:instance fn-hlp-accept-step (st st))
                 (:instance fn-hlp-dd-facts)
                 (:instance fn-hlp-ru-subset (uses (fn-rtc-uses st)) (key (fn-rtc-key (fn-hlp-bev st r))))
                 (:instance fn-hlp-guniq-from-okp (uses (fn-rtc-uses st)) (s st))
                 (:instance fn-hlp-rm1 (d (fn-hlp-dd st r)))
                 (:instance fn-rtc-invp-ops-natp (s st)) (:instance fn-rtc-invp-uses-okp (s st))
                 (:instance fn-hld-hll-invp-is-generic-invp (s st)))))))
(local (defthm fn-hlp-begin-left
  (implies (and (natp r) (< r (expt 2 64)) (fn-rtc-free-slot 0 (fn-rtc-slots st))
                (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses st)))
           (equal (mv-nth 3 (fn-hld-begin r st))
                  (mv-nth 1 (fn-hld-settle (true-list-fix (mv-nth 1 (fn-hll-x-step* (fn-hlp-bev st r) 1 st)))
                                           (fn-hld-fuel (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st)))
                                           (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hld-begin fn-hlp-bev fn-rtc-st-free-slot fn-rtc-st$a-free-slot fn-hld-readers fn-rtc-st-slot fn-rtc-st$a-slot
                                               fn-rtc-slot unicity-of-0 commutativity-of-+ fix posp (:e binary-+) (:e unary--)
                                               natp mv-nth (:e mv-nth) (:type-prescription fn-rtc-free-slot))
                                             (theory 'minimal-theory))
           :use ((:instance fn-rtc-free-slot-has-incarnation-room (i 0) (slots (fn-rtc-slots st)))
                 (:instance fn-rtc-free-slot-index-type (i 0) (slots (fn-rtc-slots st))))))))
(local (defthm fn-hlp-begin-fail
  (implies (not (and (natp r) (< r (expt 2 64)) (fn-rtc-free-slot 0 (fn-rtc-slots st))
                     (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses st))))
           (and (equal (mv-nth 0 (fn-hld-begin r st)) st) (equal (mv-nth 3 (fn-hld-begin r st)) nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-hld-begin fn-rtc-st-free-slot fn-rtc-st$a-free-slot fn-hld-readers fn-rtc-st-slot fn-rtc-st$a-slot
                                               natp mv-nth (:e mv-nth) (:type-prescription fn-rtc-free-slot))
                                             (theory 'minimal-theory))))))
(local (defthm fn-hlp-close-no-grant
  (implies (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses s)))
           (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-rtc-request '(:close) id inc s))))))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-request fn-rtc-req-close fn-rtc-issue-frame fn-rtc-with-accessors fn-rtc-kind-out-cons
                                               fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e equal) mv-nth (:e mv-nth))
                                             (theory 'minimal-theory))))))
(local (defthm fn-hlp-send-req-no-grant
  (equal (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-rtc-request (list :submit :send hd nil) id inc s))))
         (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses s)))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-request fn-rtc-req-submit fn-rtc-issue-frame fn-rtc-with-accessors fn-rtc-kind-out-cons fn-rtc-buffered-kind-p
                                               fn-rtc-kind-extrap fn-rtc-extrap fn-rtc-with-buffer fn-rtc-make-accessors (:e len) len
                                               fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e equal) (:e member-eq) member-eq mv-nth (:e mv-nth))
                                             (theory 'minimal-theory))))))
(local (defthm fn-hlp-send-req-no-grant-car
  (equal (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (car (fn-rtc-request (list :submit :send hd nil) id inc s))))
         (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses s)))
  :hints (("Goal" :use fn-hlp-send-req-no-grant :in-theory (union-theories '(fn-hlp-mv0) (theory 'minimal-theory))))))
(local (defthm fn-hlp-request-consp (consp (fn-rtc-request r id inc s))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release fn-rtc-req-close fn-rtc-req-submit fn-rtc-req-cancel)
                                             (theory 'minimal-theory))))))
(local (defthm fn-hlp-quantum-grant
  (implies (and (fn-rtc-st-p st) (fn-dss-out-p out))
           (equal (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-hld-quantum h id inc out st))))
                  (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses st))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-hld-quantum fn-dss-out-len-is-len fn-hld-readers fn-hlp-send-req-no-grant fn-hlp-send-req-no-grant-car fn-hlp-request-consp fn-hlr-puts-frame fn-dss-out-p-is-octet-listp
                                        fn-hld-puts-keeps-st-p fn-rtc-x-request-is fn-rtc-st-p-is-shapep natp nfix (:type-prescription fn-rtc-nbufs) (:e zp) fn-hld-nthcdr-0
                                        fn-hld-copy-is-puts mv-nth (:e mv-nth) car-cons cdr-cons (:type-prescription len))
                                      (theory 'minimal-theory))
           :use ((:instance fn-hlp-send-req-no-grant-car (hd (list h (fn-rtc-b-gen (fn-rtc-buffer h st)) 0 (len out))) (s (fn-rtc-st$a-puts h 0 out st)) (id id) (inc inc))
                 (:instance fn-hld-copy-is-puts (i 0))
                 (:instance fn-hld-puts-keeps-st-p (off 0) (w out))
                 (:instance fn-hlr-puts-frame (off 0) (w out) (s st) (k 0))
                 (:instance fn-rtc-x-request-is (r (list :submit :send (list h (fn-rtc-st-gen h st) 0 (len out)) nil))
                            (fn-rtc-st (fn-rtc-st$a-puts h 0 out st))))))))
(local (defthm fn-hlp-allopened-nogrant
  (implies (fn-rtc-all-opened-p uses) (not (fn-rtc-kind-out-p :grant 0 0 uses)))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-all-opened-p fn-rtc-kind-out-p fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix)) (theory 'minimal-theory))))))
(local (defthm fn-hlp-arm-opened-all
  (implies (fn-rtc-all-opened-p (fn-rtc-uses s))
           (fn-rtc-all-opened-p (fn-rtc-uses (mv-nth 0 (fn-hll-arm-opened j n s)))))
  :hints (("Goal" :induct (fn-hll-arm-opened j n s)
           :in-theory (union-theories '((:induction fn-hll-arm-opened) fn-hll-arm-opened fn-rtc-issue-frame fn-rtc-all-opened-p fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) zp
                                        fn-hld-mv-nth-0-cons)
                                      (set-difference-theories (theory 'minimal-theory) '(mv-nth)))))))
(local (defthm fn-hlp-rearm-fresh
  (implies (and (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses d))) (not (fn-rtc-oldest-wait (fn-rtc-uses d))))
           (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-rtc-rearm d))))))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-rearm fn-rtc-arm-accept fn-rtc-arm-grant fn-rtc-issue-frame fn-rtc-kind-out-cons fn-rtc-oldest-wait-cons-other
                                               mv-nth (:e mv-nth) fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e equal))
                                             (theory 'minimal-theory))))))
(local (defthm fn-hlp-init-fresh
  (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-hll-init cfg)))))
  :hints (("Goal" :in-theory (union-theories '(fn-hll-init fn-rtc-with-accessors fn-rtc-make-accessors fn-hlp-allopened-nogrant fn-hlp-arm-opened-all fn-rtc-all-opened-p
                                               fn-rtc-all-opened-no-oldest-wait fn-hlp-rearm-fresh fn-hld-mv-nth-0-cons mv-nth (:e mv-nth))
                                             (theory 'minimal-theory))))))
(local (in-theory (disable fn-hlp-mv0)))

; --- A. Every state a driver leaves satisfies the contract invariant and each of its pieces.
(defthm fn-hlp-init-state
  (implies (mv-nth 1 (fn-hld-init profile cfg q st))
           (let ((s (mv-nth 0 (fn-hld-init profile cfg q st))))
             (and (fn-rtc-invp s) (fn-rtc-core-invp s) (fn-rtc-st-p s) (fn-rtc-shapep s)
                  (fn-rtc-mstates-okp (fn-rtc-mstates s))
                  (fn-rtc-slots-okp 0 (fn-rtc-slots s))
                  (fn-rtc-statics-okp 1 (fn-rtc-nstatic (fn-rtc-config s)) (fn-rtc-slots s))
                  (fn-rtc-pool-okp 0 (fn-rtc-pool s) s)
                  (fn-rtc-pool-shapep 0 (fn-rtc-pool s) (fn-rtc-config s))
                  (fn-rtc-draining-okp 0 (fn-rtc-slots s) (fn-rtc-uses s)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory) :use ((:instance fn-hlp-hll-invp-pieces (s (mv-nth 0 (fn-hld-init profile cfg q st)))) fn-hld-init-establishes-invp))))

(defthm fn-hlp-begin-state
  (implies (fn-hll-invp st)
           (let ((s (mv-nth 0 (fn-hld-begin r st))))
             (and (fn-rtc-invp s) (fn-rtc-core-invp s) (fn-rtc-st-p s) (fn-rtc-shapep s)
                  (fn-rtc-mstates-okp (fn-rtc-mstates s))
                  (fn-rtc-slots-okp 0 (fn-rtc-slots s))
                  (fn-rtc-statics-okp 1 (fn-rtc-nstatic (fn-rtc-config s)) (fn-rtc-slots s))
                  (fn-rtc-pool-okp 0 (fn-rtc-pool s) s)
                  (fn-rtc-pool-shapep 0 (fn-rtc-pool s) (fn-rtc-config s))
                  (fn-rtc-draining-okp 0 (fn-rtc-slots s) (fn-rtc-uses s)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory) :use ((:instance fn-hlp-hll-invp-pieces (s (mv-nth 0 (fn-hld-begin r st)))) fn-hld-begin-keeps-invp))))

(defthm fn-hlp-quantum-state
  (implies (and (fn-hll-invp st) (fn-dss-out-p out))
           (let ((s (mv-nth 0 (fn-hld-quantum h id inc out st))))
             (and (fn-rtc-invp s) (fn-rtc-core-invp s) (fn-rtc-st-p s) (fn-rtc-shapep s)
                  (fn-rtc-mstates-okp (fn-rtc-mstates s))
                  (fn-rtc-slots-okp 0 (fn-rtc-slots s))
                  (fn-rtc-statics-okp 1 (fn-rtc-nstatic (fn-rtc-config s)) (fn-rtc-slots s))
                  (fn-rtc-pool-okp 0 (fn-rtc-pool s) s)
                  (fn-rtc-pool-shapep 0 (fn-rtc-pool s) (fn-rtc-config s))
                  (fn-rtc-draining-okp 0 (fn-rtc-slots s) (fn-rtc-uses s)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory) :use ((:instance fn-hlp-hll-invp-pieces (s (mv-nth 0 (fn-hld-quantum h id inc out st)))) fn-hld-quantum-keeps-invp))))

(defthm fn-hlp-sent-state
  (implies (fn-hll-invp st)
           (let ((s (mv-nth 0 (fn-hld-sent id inc op outcome st))))
             (and (fn-rtc-invp s) (fn-rtc-core-invp s) (fn-rtc-st-p s) (fn-rtc-shapep s)
                  (fn-rtc-mstates-okp (fn-rtc-mstates s))
                  (fn-rtc-slots-okp 0 (fn-rtc-slots s))
                  (fn-rtc-statics-okp 1 (fn-rtc-nstatic (fn-rtc-config s)) (fn-rtc-slots s))
                  (fn-rtc-pool-okp 0 (fn-rtc-pool s) s)
                  (fn-rtc-pool-shapep 0 (fn-rtc-pool s) (fn-rtc-config s))
                  (fn-rtc-draining-okp 0 (fn-rtc-slots s) (fn-rtc-uses s)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory) :use ((:instance fn-hlp-hll-invp-pieces (s (mv-nth 0 (fn-hld-sent id inc op outcome st)))) fn-hld-sent-keeps-invp))))

(defthm fn-hlp-end-state
  (implies (fn-hll-invp st)
           (let ((s (mv-nth 0 (fn-hld-end id inc st))))
             (and (fn-rtc-invp s) (fn-rtc-core-invp s) (fn-rtc-st-p s) (fn-rtc-shapep s)
                  (fn-rtc-mstates-okp (fn-rtc-mstates s))
                  (fn-rtc-slots-okp 0 (fn-rtc-slots s))
                  (fn-rtc-statics-okp 1 (fn-rtc-nstatic (fn-rtc-config s)) (fn-rtc-slots s))
                  (fn-rtc-pool-okp 0 (fn-rtc-pool s) s)
                  (fn-rtc-pool-shapep 0 (fn-rtc-pool s) (fn-rtc-config s))
                  (fn-rtc-draining-okp 0 (fn-rtc-slots s) (fn-rtc-uses s)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory) :use ((:instance fn-hlp-hll-invp-pieces (s (mv-nth 0 (fn-hld-end id inc st)))) fn-hld-end-keeps-invp))))


; --- B. The concrete stobj the image creates is well formed (defabsstobj's {correspondence}
; theorems carry it across every export from there).
(defthm fn-hlp-created-concrete-state
  (and (fn-rtc-c-wfp (create-fn-rtc-st$c))
       (fn-rtc-c-metas-okp 0 (nth *fn-rtc-c-metai* (create-fn-rtc-st$c)) (nth *fn-rtc-c-cfg* (create-fn-rtc-st$c))))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-st$corr fn-rtc-c-wfp) (theory 'minimal-theory))
           :use (create-fn-rtc-st{correspondence}))))


; --- C. What the host passes the contract is what its keystones assume.
; C1: the buffer the host renders into (fn-hld-workspace's answer) is render-ready for its instance.
(defthm fn-hlp-workspace-is-render-ready
  (implies (fn-hld-workspace h id inc st)
           (fn-hl-render-ready-p (fn-hld-workspace h id inc st) id inc st))
  :hints (("Goal" :in-theory (union-theories '(fn-hl-render-ready-p) (theory 'minimal-theory))
           :use fn-hlp-workspace-facts)))

; C2: that workspace is foreign to every other instance (the isolation keystones' scene).
(defthm fn-hlp-workspace-is-foreign-to-others
  (implies (and (fn-hld-workspace h id inc st) (not (equal id2 id)))
           (fn-rtc-foreign-ws-p (fn-hld-workspace h id inc st) id2 st))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-foreign-ws-p fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e binary-+) (:e unary--)) (theory 'minimal-theory))
           :use fn-hlp-workspace-facts)))

; C3: the instance begin returns is live in the state begin leaves.
(defthm fn-hlp-begun-instance-is-live
  (implies (and (fn-hll-invp st) (mv-nth 1 (fn-hld-begin r st)))
           (fn-rtc-live-p (mv-nth 1 (fn-hld-begin r st)) (mv-nth 2 (fn-hld-begin r st))
                          (mv-nth 0 (fn-hld-begin r st))))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-live-p fn-rtc-s-inc fn-rtc-s-status fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) natp nfix)
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use (fn-hlp-begin-ids fn-hlp-begin-slot))))

; C4: begin succeeds only on a free slot, the one the contract's accept takes.
(defthm fn-hlp-begin-takes-the-free-slot
  (implies (mv-nth 1 (fn-hld-begin r st))
           (and (fn-rtc-free-slot 0 (fn-rtc-slots st))
                (equal (mv-nth 1 (fn-hld-begin r st)) (fn-rtc-free-slot 0 (fn-rtc-slots st)))))
  :hints (("Goal" :in-theory (union-theories '(fn-hld-begin fn-rtc-st-free-slot fn-rtc-st$a-free-slot natp mv-nth) (theory 'minimal-theory)))))

; C5: a begun instance holds a workspace only if the pool had a free buffer; else its pool request waits.
(defthm fn-hlp-begin-grants-from-a-free-buffer
  (implies (and (fn-hll-invp st) (mv-nth 1 (fn-hld-begin r st))
                (fn-hld-workspace 0 (mv-nth 1 (fn-hld-begin r st)) (mv-nth 2 (fn-hld-begin r st))
                                  (mv-nth 0 (fn-hld-begin r st))))
           (fn-rtc-free-pool-buf 0 (fn-rtc-pool st) (fn-rtc-config st)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use (fn-hlp-no-free-buffer-no-workspace))))

(defthm fn-hlp-begin-waits-for-a-buffer
  (implies (and (fn-hll-invp st) (mv-nth 1 (fn-hld-begin r st))
                (not (fn-hld-workspace 0 (mv-nth 1 (fn-hld-begin r st)) (mv-nth 2 (fn-hld-begin r st))
                                       (mv-nth 0 (fn-hld-begin r st)))))
           (fn-rtc-oldest-wait (fn-rtc-uses (mv-nth 0 (fn-hld-begin r st)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :cases ((and (fn-rtc-free-pool-buf 0 (fn-rtc-pool st) (fn-rtc-config st)) (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses st)))))
           :use (fn-hlp-begin-case-g fn-hlp-begin-case-n))))

; C5c: and conversely, a begin on a pool with a free buffer leaves the instance holding a workspace
; (settle completes the grant and its :pool action at once): what C1 and C2 assume of fn-hld-workspace.
;; Restated (A17) after the counterexample sonnet-premises/cex-fn-hlp-begin-on-a-free-buffer-holds-a-workspace.lsp:
;; with an earlier waiter and the listener's :grant still outstanding, the new request queues behind it.
;; Settle completes every :grant at once and the host faults when settle leaves work (owner.lisp
;; fnn-owner-lease-*), so the states the host passes have no :grant outstanding (the search: 0 of 3409
;; settled states violate the original; all 944 violations had a :grant pending).
(defthm fn-hlp-begin-on-a-free-buffer-holds-a-workspace
  (implies (and (fn-hll-invp st) (mv-nth 1 (fn-hld-begin r st))
                (fn-rtc-free-pool-buf 0 (fn-rtc-pool st) (fn-rtc-config st))
                (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses st))))
           (fn-hld-workspace 0 (mv-nth 1 (fn-hld-begin r st)) (mv-nth 2 (fn-hld-begin r st))
                             (mv-nth 0 (fn-hld-begin r st))))
  :hints (("Goal" :use fn-hlp-begin-case-g :in-theory (theory 'minimal-theory))))

; C6: the completion the host delivers for its send is a contract completion with a kind.  (Its
; hypotheses are fn-hld-sent-event's guard, checked at the host's fn-hld-sent call.)
(defthm fn-hlp-sent-event-is-a-completion
  (implies (and (natp id) (natp inc) (natp op) (fn-rtc-outcomep outcome))
           (and (fn-rtc-completionp (fn-hld-sent-event id inc op outcome))
                (fn-rtc-get 0 (fn-hld-sent-event id inc op outcome))))
  :hints (("Goal" :in-theory (union-theories '(fn-hld-sent-event fn-rtc-completionp fn-rtc-outcomep fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e binary-+) (:e unary--) (:e member-eq) (:e fn-rtc-get) (:e len) (:e equal) true-listp len) (theory 'minimal-theory)))))

; C7: the send the quantum submits passes the contract's submit check, and its use is compatible with
; every use outstanding at submission (the quantum's own terms: G = H's generation, N = the window).
(defthm fn-hlp-quantum-send-is-admissible
  (implies (and (fn-hll-invp st) (fn-dss-out-p out) (fn-hl-render-ready-p h id inc st)
                (fn-rtc-live-p id inc st) (consp out)
                (<= (len out) (fn-rtc-buf-cap h (fn-rtc-config st))))
           (let ((s1 (fn-hld-copy 0 (len out) h out st))
                 (hd (list h (fn-rtc-st-gen h st) 0 (len out))))
             (and (fn-rtc-submit-okp :send hd id inc s1)
                  (fn-rtc-compatible-usesp (list :send id inc (fn-rtc-st-next-op st) hd) (fn-rtc-uses s1)))))
  :hints (("Goal" :in-theory (union-theories '(fn-hld-readers fn-hld-nthcdr-0 fn-hld-hll-invp-is-generic-invp fn-hl-render-ready-p
                                               fn-dss-out-p-is-octet-listp fn-hlr-natp-len fn-hlr-len-nonneg natp (:e natp))
                                             (theory 'minimal-theory))
           :use ((:instance fn-hld-copy-is-puts (i 0))
                 fn-hlp-send-prep (:instance fn-hld-readers)
                 (:instance fn-hlr-puts-frame (off 0) (w out) (s st) (k 0))))))

(defthm fn-hlp-quantum-send-is-compatible-with-each-use
  (implies (and (fn-hll-invp st) (fn-dss-out-p out) (fn-hl-render-ready-p h id inc st)
                (fn-rtc-live-p id inc st) (consp out)
                (<= (len out) (fn-rtc-buf-cap h (fn-rtc-config st)))
                (natp k))
           (let ((s1 (fn-hld-copy 0 (len out) h out st))
                 (hd (list h (fn-rtc-st-gen h st) 0 (len out))))
             (fn-rtc-compatible-use-p (list :send id inc (fn-rtc-st-next-op st) hd)
                                      (nth k (fn-rtc-uses s1)))))
  :hints (("Goal" :in-theory (union-theories '(fn-hld-readers fn-hld-nthcdr-0 fn-hld-hll-invp-is-generic-invp fn-hl-render-ready-p
                                               fn-dss-out-p-is-octet-listp fn-hlr-natp-len fn-hlr-len-nonneg natp (:e natp))
                                             (theory 'minimal-theory))
           :use ((:instance fn-hld-copy-is-puts (i 0))
                 fn-hlp-send-prep (:instance fn-hld-readers)
                 (:instance fn-hlr-puts-frame (off 0) (w out) (s st) (k 0))
                 (:instance fn-hlp-compat-nth (new (list :send id inc (fn-rtc-next-op st) (list h (fn-rtc-b-gen (fn-rtc-buffer h st)) 0 (len out))))
                            (uses (fn-rtc-uses st)))))))

; C8: the host's completion of the send the quantum submitted acts on the quantum's state and ends that
; send's use (the completion keystones' scene: T4, fn-rtc-completion-ends-its-use).
(defthm fn-hlp-sent-acts-on-the-quantum
  (implies (and (fn-hll-invp st) (fn-dss-out-p out) (mv-nth 1 (fn-hld-quantum h id inc out st))
                (fn-rtc-outcomep outcome))
           (let ((q (mv-nth 0 (fn-hld-quantum h id inc out st)))
                 (e (fn-hld-sent-event id inc (mv-nth 1 (fn-hld-quantum h id inc out st)) outcome)))
             (and (fn-rtc-acts-on-p q e)
                  (fn-rtc-ends-use-p e (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses q))))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use (fn-hlp-quantum-facts
                 (:instance fn-hlp-sent-event-acts-on-send (q (mv-nth 0 (fn-hld-quantum h id inc out st)))
                            (op (mv-nth 1 (fn-hld-quantum h id inc out st)))
                            (x (list h (fn-rtc-b-gen (fn-rtc-buffer h st)) 0 (len out)))
                            (uses0 (fn-rtc-uses st)) (o outcome))))))

; C9: the actions the contract emits for the host's requests (quantum's send, end's close) are
; well-formed and each names an outstanding use; so are those of the leased step settle completes.
;; Restated (A17) after the counterexamples sonnet-premises/cex-fn-hlp-request-actions-ok.lsp and
;; cex-fn-hlp-request-action-is-an-action.lsp: at a non-natural id the contract reads slot (nfix id) = the
;; listener and emits an action naming id nil.  The host's requests name a begun instance (natural id and
;; incarnation: fn-hlp-begun-instance-is-live's slot), so the statements carry (natp id) (natp inc).
(defthm fn-hlp-request-actions-ok
  (implies (and (fn-rtc-invp s) (natp id) (natp inc))
           (fn-rtc-actions-okp (mv-nth 1 (fn-rtc-x-request r id inc s)) (mv-nth 0 (fn-rtc-x-request r id inc s))))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-x-request-is fn-rtc-invp-implies-st-p fn-rtc-req-pre) (theory 'minimal-theory))
           :use (fn-rtc-request-actions-ok fn-rtc-invp-slot-res fn-rtc-invp-ops-natp))))
(local (defthm fn-hlp-nth-member
  (implies (and (natp k) (< k (len l))) (member-equal (nth k l) l))
  :hints (("Goal" :in-theory (enable nth len)))))
(defthm fn-hlp-request-action-is-an-action
  (implies (and (fn-rtc-invp s) (natp id) (natp inc) (natp k) (< k (len (mv-nth 1 (fn-rtc-x-request r id inc s)))))
           (fn-rtc-actionp (nth k (mv-nth 1 (fn-rtc-x-request r id inc s)))))
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-nth-member) (theory 'minimal-theory))
           :use (fn-hlp-request-actions-ok
                 (:instance fn-rtc-actions-okp-member (acts (mv-nth 1 (fn-rtc-x-request r id inc s)))
                            (s (mv-nth 0 (fn-rtc-x-request r id inc s)))
                            (a (nth k (mv-nth 1 (fn-rtc-x-request r id inc s)))))
                 (:instance fn-hlp-nth-member (l (mv-nth 1 (fn-rtc-x-request r id inc s))))))))

(defthm fn-hlp-step-actions-ok
  (implies (fn-hll-invp st)
           (fn-rtc-actions-okp (mv-nth 1 (fn-hll-x-step* e q st)) (mv-nth 0 (fn-hll-x-step* e q st))))
  :hints (("Goal" :in-theory (union-theories '(fn-hll-x-step*-is fn-hld-hll-invp-st-p fn-hlp-step-parts) (theory 'minimal-theory))
           :use ((:instance fn-hlp-actions-okp-of-subset (s st) (e (fn-rtc-landed e st))
                            (acts (mv-nth 1 (fn-hll-step st (fn-rtc-landed e st) q)))) 
                 (:instance fn-hlr-subsetp-refl (x (mv-nth 1 (fn-hll-step st (fn-rtc-landed e st) q))))))))


; --- G. Two hypotheses the restatements of C5c, C9a and C9b added hold on the host path (A17; STATEMENT-G.lisp).
; G1: no :grant is outstanding in any state the host keeps: init establishes it, and each driver keeps it
; (LEFT is the work settle could not finish; the host faults unless it is nil).
(defthm fn-hlp-init-leaves-no-grant
  (implies (and (mv-nth 1 (fn-hld-init profile cfg q st)) (null (mv-nth 2 (fn-hld-init profile cfg q st))))
           (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-hld-init profile cfg q st))))))
  :hints (("Goal" :in-theory (union-theories '(fn-hld-init fn-hll-x-init-is fn-rtc-st-cfg-okp fn-hld-mv-nth-0-cons fn-hlp-gin-tlf) (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance fn-hlp-init-fresh (cfg (fn-hl-rtc-config profile cfg q 1 0 0)))
                 (:instance fn-hll-init-establishes-invp (cfg (fn-hl-rtc-config profile cfg q 1 0 0)))
                 (:instance fn-hlp-settle-no-grant (st (mv-nth 0 (fn-hll-init (fn-hl-rtc-config profile cfg q 1 0 0)))) (work (true-list-fix (mv-nth 1 (fn-hll-init (fn-hl-rtc-config profile cfg q 1 0 0))))) (fuel (fn-hld-fuel (mv-nth 0 (fn-hll-init (fn-hl-rtc-config profile cfg q 1 0 0))))))))))
(defthm fn-hlp-begin-leaves-no-grant
  (implies (and (fn-hll-invp st) (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses st)))
                (null (mv-nth 3 (fn-hld-begin r st))))
           (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-hld-begin r st))))))
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-gin-tlf) (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :cases ((and (natp r) (< r (expt 2 64)) (fn-rtc-free-slot 0 (fn-rtc-slots st)) (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses st))))
           :use (fn-hlp-begin-fail fn-hlp-begin-parts fn-hlp-begin-left fn-hlp-begin-sa-cov
                 (:instance fn-hld-x-step*-keeps-invp (st st) (e (fn-hlp-bev st r)) (q 1))
                 (:instance fn-hlp-settle-no-grant (st (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st))) (work (true-list-fix (mv-nth 1 (fn-hll-x-step* (fn-hlp-bev st r) 1 st)))) (fuel (fn-hld-fuel (mv-nth 0 (fn-hll-x-step* (fn-hlp-bev st r) 1 st)))))))))
(defthm fn-hlp-quantum-leaves-no-grant
  (implies (and (fn-hll-invp st) (fn-dss-out-p out) (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses st))))
           (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-hld-quantum h id inc out st))))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use (fn-hlp-quantum-grant (:instance fn-hld-hll-invp-st-p (s st))))))
(defthm fn-hlp-sent-leaves-no-grant
  (implies (and (fn-hll-invp st) (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses st)))
                (null (mv-nth 1 (fn-hld-sent id inc op outcome st))))
           (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-hld-sent id inc op outcome st))))))
  :hints (("Goal" :in-theory (union-theories '(fn-hld-sent fn-hlp-gin-tlf) (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance fn-hlp-sent-leaves-no-grant-pre)
                 (:instance fn-hld-x-step*-keeps-invp (st st) (e (fn-hld-sent-event id inc op outcome)) (q 1))
                 (:instance fn-hlp-settle-no-grant (st (mv-nth 0 (fn-hll-x-step* (fn-hld-sent-event id inc op outcome) 1 st))) (work (true-list-fix (mv-nth 1 (fn-hll-x-step* (fn-hld-sent-event id inc op outcome) 1 st)))) (fuel (fn-hld-fuel (mv-nth 0 (fn-hll-x-step* (fn-hld-sent-event id inc op outcome) 1 st)))))))))
(defthm fn-hlp-end-leaves-no-grant
  (implies (and (fn-hll-invp st) (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses st)))
                (null (mv-nth 1 (fn-hld-end id inc st))))
           (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-hld-end id inc st))))))
  :hints (("Goal" :in-theory (union-theories '(fn-hld-end fn-hlp-gin-tlf fn-rtc-x-request-is fn-hld-hll-invp-st-p) (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance fn-hlp-close-no-grant (s st))
                 (:instance fn-hld-close-keeps-hll-invp (st st))
                 (:instance fn-rtc-x-request-is (r '(:close)) (fn-rtc-st st))
                 (:instance fn-hld-hll-invp-st-p (s st))
                 (:instance fn-hlp-settle-no-grant (st (mv-nth 0 (fn-rtc-x-request '(:close) id inc st))) (work (true-list-fix (mv-nth 1 (fn-rtc-x-request '(:close) id inc st)))) (fuel (fn-hld-fuel (mv-nth 0 (fn-rtc-x-request '(:close) id inc st)))))))))
; G2: the instance begin returns, which the host passes to every later quantum, sent and end, has a natural id and incarnation.
(defthm fn-hlp-begun-instance-is-natural
  (implies (and (fn-hll-invp st) (mv-nth 1 (fn-hld-begin r st)))
           (and (natp (mv-nth 1 (fn-hld-begin r st)))
                (natp (mv-nth 2 (fn-hld-begin r st)))))
  :hints (("Goal" :in-theory (union-theories '(posp natp) (theory 'minimal-theory)) :use fn-hlp-begin-ids)))

; --- D. The pool grant's :in lease, and the :hand transfer the lease host never makes.
; D1: the grant the leased step runs (books/runtime-contract.lisp fn-rtc-grant-one; the executable
; fn-rtc-x-grant-one, copied into the leased layer as its grant) leases the first free pool buffer :in to the
; oldest waiter until the host completes its :pool action (settle does so at once): the landing keystones'
; scene (fn-rtc-landing-is-hidden: the :pool completion lands on an :in-leased buffer).
(defthm fn-hlp-grant-leases-the-buffer-in
  (implies (and (fn-rtc-invp s)
                (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s))
                (fn-rtc-oldest-wait (fn-rtc-uses s)))
           (fn-rtc-in-leased-p (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s))
                               (mv-nth 0 (fn-rtc-x-grant-one s))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance fn-rtc-x-grant-one-is (fn-rtc-st s)) fn-rtc-invp-implies-st-p fn-hlp-grant-one-leases-in))))

; D1b: and the waiter's operation number becomes a :pool use's (the oldest-first keystone's scene,
; fn-rtc-pool-grants-oldest-first: B becomes a pool op in the step).
(defthm fn-hlp-grant-makes-the-oldest-wait-a-pool-op
  (implies (and (fn-rtc-invp s)
                (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s))
                (fn-rtc-oldest-wait (fn-rtc-uses s)))
           (fn-rtc-pool-op-p (fn-rtc-get 3 (fn-rtc-oldest-wait (fn-rtc-uses s)))
                             (fn-rtc-uses (mv-nth 0 (fn-rtc-x-grant-one s)))))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-grant-one fn-rtc-with-accessors mv-nth (:e mv-nth) fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e binary-+) (:e unary--))
                                             (theory 'minimal-theory))
           :use ((:instance fn-rtc-x-grant-one-is (fn-rtc-st s)) fn-rtc-invp-implies-st-p
                 (:instance fn-hlp-replace-use-pool-op (w (fn-rtc-oldest-wait (fn-rtc-uses s))) (uses (fn-rtc-uses s))
                            (id (nfix (fn-rtc-get 1 (fn-rtc-oldest-wait (fn-rtc-uses s)))))
                            (inc (fn-rtc-get 2 (fn-rtc-oldest-wait (fn-rtc-uses s))))
                            (hd (list (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s))
                                      (+ 1 (fn-rtc-b-gen (fn-rtc-buffer (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s)) s)))
                                      0 0)))
                 (:instance fn-rtc-oldest-wait-member (uses (fn-rtc-uses s)))))))

; D2: no completion the lease host delivers is a :hand delivery: its send completion (fn-hld-sent-event)
; and settle's completions (kinds :grant :pool :close :opened only, fn-hld-settle) are not :hand.  So
; fn-rtc-hand-delivers-p stays unestablished on purpose: the theorems assuming it have no instance on this
; host path.  The READY names it (no hosted :hand transfer exists).
; The work fn-hld-sent settles (the leased step's actions on the host's completion) is benign: grants,
; pool completions and accepts only, the hypothesis fn-hlr-settle-frames assumes of its work list.
(local (defthm fn-hlp-sent-event-kind
  (equal (fn-rtc-get 0 (fn-hld-sent-event id inc op outcome)) :send)
  :hints (("Goal" :in-theory (enable fn-hld-sent-event fn-rtc-get)))))
(defthm fn-hlp-sent-work-is-benign
  (implies (fn-hll-invp st)
           (fn-hlr-benign-actsp (mv-nth 1 (fn-hll-x-step* (fn-hld-sent-event id inc op outcome) q st))))
  :hints (("Goal" :in-theory (union-theories '(fn-hlp-sent-event-kind (:e member-eq)) (theory 'minimal-theory))
           :use ((:instance fn-hlr-xstep-frames (e (fn-hld-sent-event id inc op outcome)) (id 0) (inc 0) (k 0) (j 0))))))

(defthm fn-hlp-sent-event-is-not-a-hand-delivery
  (not (fn-rtc-hand-delivers-p s (fn-hld-sent-event id inc op outcome)))
  :hints (("Goal" :in-theory (union-theories '(fn-hld-sent-event fn-rtc-hand-delivers-p fn-rtc-e-kind fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e binary-+) (:e unary--)) (theory 'minimal-theory)))))


; --- E. Book-internal proof steps made local (premise_audit local_theorems; no other book cites them by
; name; the transitive certify is the check that none is used as a rule downstream):
;   books/runtime-contract-invariant.lisp    fn-rtc-all-opened-no-kind-out, fn-rtc-opened-clear-first
;   books/runtime-contract-invariant-ops.lisp fn-rtc-octets-n-properties
; (wrap each defthm in (local ...); statements unchanged).  If a later event in its own book or any
; other book needs one non-locally, do NOT make it local: report which.
