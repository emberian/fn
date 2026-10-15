; Owner observations of the generated product layer (section R, definitions).
(in-package "ACL2")
(include-book "post-transaction-host-layer")
(include-book "post-transaction-sim")
(local (in-theory (current-theory 'fn-ptx-p5)))
(set-verify-guards-eagerness 0)
(set-ignore-ok t)

; R9: the request validator's state-independent checks and its complement.
; These are factored by the equalities below, not a second admissibility check.
(defun fn-pth-req-data-okp (r)
 (case (fn-rtc-get 0 r)
  ((:acquire :release) (natp (fn-rtc-get 1 r)))
  (:write (and (natp (fn-rtc-get 1 r)) (natp (fn-rtc-get 3 r))
               (fn-cbor-octet-listp (fn-rtc-get 4 r))))
  (:close t)
  (:cancel (and (member-eq (fn-rtc-get 1 r) *fn-rtc-machine-kinds*)
                (not (member-eq (fn-rtc-get 1 r) '(:hand :pool)))))
  (:submit
   (let ((kind (fn-rtc-get 1 r)) (hd (fn-rtc-get 2 r)) (extra (fn-rtc-get 3 r)))
    (and (member-eq kind *fn-rtc-machine-kinds*)
         (fn-rtc-kind-extrap kind extra)
         (implies (eq kind :hand)
                  (and (natp (fn-rtc-get 0 extra)) (natp (fn-rtc-get 1 extra))
                       (<= 1 (fn-rtc-get 0 extra))))
         (cond ((eq kind :pool) (and (null hd) (null extra)))
               ((not (fn-rtc-buffered-kind-p kind)) (null hd))
               (t (and (fn-rtc-handlep hd)
                       (implies (eq kind :hand) (equal (fn-rtc-h-off hd) 0))))))))
  (otherwise nil)))
(defun fn-pth-reqs-data-okp (rs)
 (if (consp rs) (and (fn-pth-req-data-okp (car rs)) (fn-pth-reqs-data-okp (cdr rs))) t))
(defun fn-pth-req-state-okp (r id inc s)
 (let* ((h (fn-rtc-get 1 r)) (g (fn-rtc-get 2 r)) (off (fn-rtc-get 3 r))
        (b (fn-rtc-buffer h s)))
  (case (fn-rtc-get 0 r)
   (:acquire (and (posp id) (fn-rtc-live-p id inc s)
                  (< h (fn-rtc-nbufs (fn-rtc-config s)))
                  (equal (fn-rtc-home h (fn-rtc-config s)) (nfix id))
                  (equal (fn-rtc-b-owner b) '(:free))))
   (:write (and (< h (fn-rtc-nbufs (fn-rtc-config s)))
                (equal (fn-rtc-b-owner b) (list :workspace id inc))
                (equal (fn-rtc-b-gen b) g)
                (<= off (len (fn-rtc-b-bytes b)))
                (<= (+ off (len (fn-rtc-get 4 r))) (fn-rtc-buf-cap h (fn-rtc-config s)))))
   (:release (and (< h (fn-rtc-nbufs (fn-rtc-config s)))
                  (equal (fn-rtc-b-owner b) (list :workspace id inc))
                  (equal (fn-rtc-b-gen b) g)))
   (:close (and (fn-rtc-live-p id inc s) (< (fn-rtc-nstatic (fn-rtc-config s)) (nfix id))))
   (:cancel (and (fn-rtc-current-p id inc s)
                 (fn-rtc-kind-out-p (fn-rtc-get 1 r) id inc (fn-rtc-uses s))))
   (:submit
    (let* ((kind (fn-rtc-get 1 r)) (hd (fn-rtc-get 2 r)) (extra (fn-rtc-get 3 r))
           (h (fn-rtc-h-buf hd)) (b (fn-rtc-buffer h s)) (o (fn-rtc-b-owner b))
           (own (equal o (list :workspace id inc))))
     (and (fn-rtc-live-p id inc s)
          (implies (eq kind :hand)
                   (and (<= 1 (nfix id))
                        (< (fn-rtc-get 0 extra) (fn-rtc-nslots (fn-rtc-config s)))
                        (not (equal (fn-rtc-get 0 extra) (nfix id)))
                        (implies (< (fn-rtc-nstatic (fn-rtc-config s)) (nfix id))
                                 (<= (fn-rtc-get 0 extra) (fn-rtc-nstatic (fn-rtc-config s))))))
          (or (eq kind :hand)
              (not (fn-rtc-kind-out-p (if (eq kind :pool) :wait kind) id inc (fn-rtc-uses s))))
          (if (or (eq kind :pool) (not (fn-rtc-buffered-kind-p kind))) t
            (and (< h (fn-rtc-nbufs (fn-rtc-config s)))
                 (equal (fn-rtc-b-gen b) (fn-rtc-h-gen hd))
                 (cond ((member-eq kind *fn-rtc-in-kinds*)
                        (and own (<= (fn-rtc-h-off hd) (len (fn-rtc-b-bytes b)))
                             (<= (+ (fn-rtc-h-off hd) (fn-rtc-h-len hd))
                                 (fn-rtc-buf-cap h (fn-rtc-config s)))))
                       ((eq kind :hand) (and own (equal (fn-rtc-h-len hd) (len (fn-rtc-b-bytes b)))))
                       (t (and (or own (equal o (list :leased id inc :out)))
                               (<= (+ (fn-rtc-h-off hd) (fn-rtc-h-len hd)) (len (fn-rtc-b-bytes b)))
                               (<= (+ (fn-rtc-h-off hd) (fn-rtc-h-len hd))
                                   (fn-rtc-buf-cap h (fn-rtc-config s)))))))))))
   (otherwise nil))))

(defthm fn-pth-req-acquire-factors
 (implies (equal (fn-rtc-get 0 r) :acquire)
  (iff (not (mv-nth 2 (fn-rtc-req-acquire r id inc s)))
       (and (fn-pth-req-data-okp r) (fn-pth-req-state-okp r id inc s))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-req-data-okp fn-pth-req-state-okp fn-rtc-req-acquire
    fn-rtc-req-write fn-rtc-req-release fn-rtc-req-close fn-rtc-req-submit
    fn-rtc-req-cancel fn-rtc-request fn-rtc-submit-okp fn-rtc-hand-target-okp
    car-cons cdr-cons mv-nth (:executable-counterpart fn-rtc-get)
    (:executable-counterpart equal) (:executable-counterpart member-equal)
    (:executable-counterpart fn-rtc-buffered-kind-p)
    (:executable-counterpart zp) (:executable-counterpart nfix))))))
(defthm fn-pth-req-write-factors
 (implies (equal (fn-rtc-get 0 r) :write)
  (iff (not (mv-nth 2 (fn-rtc-req-write r id inc s)))
       (and (fn-pth-req-data-okp r) (fn-pth-req-state-okp r id inc s))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-req-data-okp fn-pth-req-state-okp fn-rtc-req-acquire
    fn-rtc-req-write fn-rtc-req-release fn-rtc-req-close fn-rtc-req-submit
    fn-rtc-req-cancel fn-rtc-request fn-rtc-submit-okp fn-rtc-hand-target-okp
    car-cons cdr-cons mv-nth (:executable-counterpart fn-rtc-get)
    (:executable-counterpart equal) (:executable-counterpart member-equal)
    (:executable-counterpart fn-rtc-buffered-kind-p)
    (:executable-counterpart zp) (:executable-counterpart nfix))))))
(defthm fn-pth-req-release-factors
 (implies (equal (fn-rtc-get 0 r) :release)
  (iff (not (mv-nth 2 (fn-rtc-req-release r id inc s)))
       (and (fn-pth-req-data-okp r) (fn-pth-req-state-okp r id inc s))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-req-data-okp fn-pth-req-state-okp fn-rtc-req-acquire
    fn-rtc-req-write fn-rtc-req-release fn-rtc-req-close fn-rtc-req-submit
    fn-rtc-req-cancel fn-rtc-request fn-rtc-submit-okp fn-rtc-hand-target-okp
    car-cons cdr-cons mv-nth (:executable-counterpart fn-rtc-get)
    (:executable-counterpart equal) (:executable-counterpart member-equal)
    (:executable-counterpart fn-rtc-buffered-kind-p)
    (:executable-counterpart zp) (:executable-counterpart nfix))))))
(defthm fn-pth-req-close-factors
 (implies (equal (fn-rtc-get 0 r) :close)
  (iff (not (mv-nth 2 (fn-rtc-req-close r id inc s)))
       (and (fn-pth-req-data-okp r) (fn-pth-req-state-okp r id inc s))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-req-data-okp fn-pth-req-state-okp fn-rtc-req-acquire
    fn-rtc-req-write fn-rtc-req-release fn-rtc-req-close fn-rtc-req-submit
    fn-rtc-req-cancel fn-rtc-request fn-rtc-submit-okp fn-rtc-hand-target-okp
    car-cons cdr-cons mv-nth (:executable-counterpart fn-rtc-get)
    (:executable-counterpart equal) (:executable-counterpart member-equal)
    (:executable-counterpart fn-rtc-buffered-kind-p)
    (:executable-counterpart zp) (:executable-counterpart nfix))))))
(defthm fn-pth-req-submit-factors
 (implies (equal (fn-rtc-get 0 r) :submit)
  (iff (not (mv-nth 2 (fn-rtc-req-submit r id inc s)))
       (and (fn-pth-req-data-okp r) (fn-pth-req-state-okp r id inc s))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-req-data-okp fn-pth-req-state-okp fn-rtc-req-acquire
    fn-rtc-req-write fn-rtc-req-release fn-rtc-req-close fn-rtc-req-submit
    fn-rtc-req-cancel fn-rtc-request fn-rtc-submit-okp fn-rtc-hand-target-okp
    car-cons cdr-cons mv-nth (:executable-counterpart fn-rtc-get)
    (:executable-counterpart equal) (:executable-counterpart member-equal)
    (:executable-counterpart fn-rtc-buffered-kind-p)
    (:executable-counterpart zp) (:executable-counterpart nfix))))))
(defthm fn-pth-req-cancel-factors
 (implies (equal (fn-rtc-get 0 r) :cancel)
  (iff (not (mv-nth 2 (fn-rtc-req-cancel r id inc s)))
       (and (fn-pth-req-data-okp r) (fn-pth-req-state-okp r id inc s))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-req-data-okp fn-pth-req-state-okp fn-rtc-req-acquire
    fn-rtc-req-write fn-rtc-req-release fn-rtc-req-close fn-rtc-req-submit
    fn-rtc-req-cancel fn-rtc-request fn-rtc-submit-okp fn-rtc-hand-target-okp
    car-cons cdr-cons mv-nth (:executable-counterpart fn-rtc-get)
    (:executable-counterpart equal) (:executable-counterpart member-equal)
    (:executable-counterpart fn-rtc-buffered-kind-p)
    (:executable-counterpart zp) (:executable-counterpart nfix))))))
(defthm fn-pth-request-factors
 (iff (not (mv-nth 2 (fn-rtc-request r id inc s)))
      (and (fn-pth-req-data-okp r) (fn-pth-req-state-okp r id inc s)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-req-data-okp fn-pth-req-state-okp fn-rtc-req-acquire
    fn-rtc-req-write fn-rtc-req-release fn-rtc-req-close fn-rtc-req-submit
    fn-rtc-req-cancel fn-rtc-request fn-rtc-submit-okp fn-rtc-hand-target-okp
    car-cons cdr-cons mv-nth (:executable-counterpart fn-rtc-get)
    (:executable-counterpart equal) (:executable-counterpart member-equal)
    (:executable-counterpart fn-rtc-buffered-kind-p)
    (:executable-counterpart zp) (:executable-counterpart nfix))))))

; Project the actual dispatch tree, retaining its branch tests, bindings and
; event arguments.  No second encoding of the delivery event lives here.
; Slot 1's incarnation is 1 on section R's reachable states; the projection
; also records deliveries to slot 1 on arbitrary invariant states.
(make-event
 (let* ((body (car (last (get-event 'fn-pth-step* (w state)))))
        (dispatch (cadddr (caddr body)))
        (bindings (cadr dispatch))
        (clauses (cdr (caddr dispatch)))
        (accept-body (car (last (get-event 'fn-pth-accept-branch (w state)))))
        (accept-if (caddr accept-body))
        (accept-let (caddr accept-if))
        (accept-call (caddr (caddr accept-let))))
   `(defun fn-pth-owner-delivery (s e q)
      (declare (xargs :guard t) (ignore q))
      (if (not (fn-rtc-acts-on-p s e)) (mv nil nil)
        (let* ,(remove-assoc-eq 'base bindings)
          (cond
           ,@(loop$ for clause in clauses collect
               (let* ((arm (cadr clause))
                      (wrapped (eq (car arm) 'let*))
                      (delivery (if wrapped (caddr arm) arm))
                      (call (caddr delivery)))
                 (list (car clause)
                       (if (eq (car call) 'fn-pth-deliver)
                           (let ((answer `(if (equal ,(caddr call) 1)
                                             (mv t ,(car (cddddr call)))
                                           (mv nil nil))))
                             (if wrapped `(let* ,(cadr arm) ,answer) answer))
                         (if (eq (car call) 'fn-pth-accept-branch)
                             `(let ,(cadr accept-body)
                                (if ,(cadr accept-if)
                                    (let* ,(cadr accept-let)
                                      (if (equal ,(caddr accept-call) 1)
                                          (mv t ,(car (cddddr accept-call)))
                                        (mv nil nil)))
                                  (mv nil nil)))
                           '(mv nil nil))))))))))))

; The actual request list, projected from the same delivery calls as above.
(make-event
 (let* ((body (car (last (get-event 'fn-pth-step* (w state)))))
        (dispatch (cadddr (caddr body)))
        (bindings (cadr dispatch))
        (clauses (cdr (caddr dispatch)))
        (accept-body (car (last (get-event 'fn-pth-accept-branch (w state)))))
        (accept-if (caddr accept-body))
        (accept-let (caddr accept-if))
        (accept-call (caddr (caddr accept-let))))
   `(defun fn-pth-owner-requests (s e q)
      (declare (xargs :guard t))
      (if (not (fn-rtc-acts-on-p s e)) nil
        (let* ,(remove-assoc-eq 'base bindings)
          (cond
           ,@(loop$ for clause in clauses collect
               (let* ((arm (cadr clause))
                      (wrapped (eq (car arm) 'let*))
                      (delivery (if wrapped (caddr arm) arm))
                      (call (caddr delivery)))
                 (list (car clause)
                       (if (eq (car call) 'fn-pth-deliver)
                           (let ((answer `(if (equal ,(caddr call) 1)
                                   (mv-nth 1
                                    (fn-pth-m-step (fn-rtc-mstate ,(caddr call) ,(cadr call))
                                     ,(car (cddddr call))
                                     (fn-rtc-view-state ,(caddr call) ,(cadddr call) ,(cadr call))
                                     (nfix ,(cadr (cddddr call))))) nil)))
                             (if wrapped `(let* ,(cadr arm) ,answer) answer))
                         (if (eq (car call) 'fn-pth-accept-branch)
                             `(let ,(cadr accept-body)
                                (if ,(cadr accept-if)
                                    (let* ,(cadr accept-let)
                                      (if (equal ,(caddr accept-call) 1)
                                          (mv-nth 1
                                   (fn-pth-m-step (fn-rtc-mstate ,(caddr accept-call) ,(cadr accept-call))
                                    ,(car (cddddr accept-call))
                                    (fn-rtc-view-state ,(caddr accept-call) ,(cadddr accept-call) ,(cadr accept-call))
                                    (nfix ,(cadr (cddddr accept-call)))))
                                        nil))
                                  nil))
                           'nil)))))))))))

; The projected list is the list actually processed by the delivery, at its
; own post-end-use state. This unfolding equality gives the projection teeth.
(defthm fn-pth-deliver-processes-its-machine-requests-by-definition
 (equal (mv-nth 2 (fn-pth-deliver s id inc ev q))
        (mv-nth 2
         (fn-rtc-requests
          (mv-nth 1 (fn-pth-m-step (fn-rtc-mstate id s) ev
                                  (fn-rtc-view-state id inc s) (nfix q))) id inc
          (fn-rtc-with-mstate id
           (mv-nth 0 (fn-pth-m-step (fn-rtc-mstate id s) ev
                                   (fn-rtc-view-state id inc s) (nfix q))) s))))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                          '(fn-pth-deliver fn-rtc-view-state mv-nth car-cons cdr-cons
                            (:executable-counterpart zp) (:executable-counterpart nfix))))))

(defun fn-pth-fo (e)
  (declare (xargs :guard t))
  (let ((out (fn-rtc-e-outcome e)))
    (if (equal (fn-rtc-get 0 out) :done) :ok out)))

(defun fn-pth-host-run (s ops q)
  (if (consp ops)
      (let ((op (car ops)))
        (case (fn-rtc-get 0 op)
          (:complete
           (mv-let (s2 acts) (fn-pth-step s (fn-rtc-get 1 op) q)
             (declare (ignore acts))
             (fn-pth-host-run s2 (cdr ops) q)))
          (:request
           (if (equal (fn-rtc-get 1 op) 1)
               (fn-pth-host-run s (cdr ops) q)
             (mv-let (s2 acts refused cost)
               (fn-rtc-requests (fn-rtc-get 3 op) (fn-rtc-get 1 op) (fn-rtc-get 2 op) s)
               (declare (ignore acts refused cost))
               (fn-pth-host-run s2 (cdr ops) q))))
          (otherwise (fn-pth-host-run s (cdr ops) q))))
    s))

; POST-ST is after the WHOLE delivery: fn-rtc-deliver stores m2 and runs
; requests (runtime-contract.lisp:1432-1440), as does the executor
; (runtime-contract-exec.lisp:501-508).  The two equalities below justify
; the field, including the A-HOST-LANDS input-landing boundary.
(defthm fn-pth-step-post-view-is-executor-post-view
  (implies (fn-rtc-st-p fn-rtc-st)
           (equal
            (fn-rtc-view-state 1 1
              (mv-nth 0 (fn-pth-step fn-rtc-st (fn-rtc-landed e fn-rtc-st) q)))
            (fn-rtc-view-state 1 1
              (mv-nth 0 (fn-pth-x-step* e q fn-rtc-st)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-pth-x-step*-is))
           :in-theory (union-theories (theory 'minimal-theory)
                                     '(fn-pth-step mv-nth car-cons cdr-cons
                                       (:executable-counterpart zp)
                                       (:executable-counterpart not))))))

; A-HOST-LANDS: host has spliced the operation's octets before delivery.
(defthm fn-pth-host-post-view-is-the-contract-post-view
  (implies (and (fn-pth-invp st)
                (fn-rtc-completionp e)
                (equal u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses st)))
                u
                (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*)
                (member-eq (fn-rtc-get 0 (fn-rtc-e-outcome e)) '(:done :short))
                (<= (fn-rtc-get 1 (fn-rtc-e-outcome e)) (fn-rtc-h-len (fn-rtc-u-hd u))))
           (let ((data (fn-assume-host-input (fn-rtc-e-op e)
                                            (fn-rtc-get 1 (fn-rtc-e-outcome e)))))
             (equal
              (fn-rtc-view-state 1 1
                (mv-nth 0 (fn-pth-step st (fn-rtc-with-data e data) q)))
              (fn-rtc-view-state 1 1
                (mv-nth 0
                  (fn-pth-x-step* e q
                    (fn-rtc-st-splice (fn-rtc-h-buf (fn-rtc-u-hd u))
                                     (fn-rtc-h-off (fn-rtc-u-hd u)) data st)))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-pth-host-landing-is-the-contract-step))
           :in-theory (union-theories (theory 'minimal-theory)
                                     '(fn-pth-step mv-nth car-cons cdr-cons
                                       (:executable-counterpart zp)
                                       (:executable-counterpart not))))))

(defun-nx fn-pth-owner-trace (s ops q)
  (if (consp ops)
      (let ((op (car ops)))
        (case (fn-rtc-get 0 op)
          (:complete
           (let ((e (fn-rtc-get 1 op)))
             (mv-let (deliveredp ev) (fn-pth-owner-delivery s e q)
               (let* ((s2 (mv-nth 0 (fn-pth-step s e q)))
                      (tail (fn-pth-owner-trace s2 (cdr ops) q)))
                 (if deliveredp
                     (cons (list ev (fn-rtc-view-state 1 1 s) q (fn-pth-fo e)
                                 (fn-rtc-view-state 1 1 s2)) tail)
                   tail)))))
          (:request
           (fn-pth-owner-trace
             (if (equal (fn-rtc-get 1 op) 1) s
               (mv-nth 0 (fn-rtc-requests
                           (fn-rtc-get 3 op) (fn-rtc-get 1 op) (fn-rtc-get 2 op) s)))
             (cdr ops) q))
          (otherwise (fn-pth-owner-trace s (cdr ops) q))))
    nil))

(defun-sk fn-pth-reachablep (s)
  (exists (profile mcfg ops0 q0)
    (let ((cfg (fn-hl-rtc-config profile mcfg q0 *fn-pth-nstatic* 0 0
                                *fn-pth-qs* *fn-pth-cs*)))
      (and (fn-rtc-configp cfg) (natp q0)
           (fn-rtc-st-cfg-okp cfg)
           (<= 1 (fn-rtc-nstatic cfg))
           (equal s (fn-pth-host-run (mv-nth 0 (fn-pth-init cfg)) ops0 q0))))))

; Local frames and normal forms for the definition ties.
(local
 (defthm fn-pth-owner-mstate-as-nth
  (equal (fn-rtc-mstate 1 s) (nth 1 (fn-rtc-mstates s)))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-rtc-get 1 (fn-rtc-mstates s))
                           (fn-rtc-get 0 (cdr (fn-rtc-mstates s)))
                           (nth 1 (fn-rtc-mstates s))
                           (nth 0 (cdr (fn-rtc-mstates s))))
           :in-theory (union-theories (theory 'minimal-theory)
                      '(fn-rtc-mstate nfix zp car-cons cdr-cons car-cdr-elim
                        (:executable-counterpart nfix) (:executable-counterpart zp)))))))

(local
 (defthm fn-pth-static-owner-facts
  (implies (and (fn-pth-invp s) (<= 1 (fn-rtc-nstatic (fn-rtc-config s))))
           (and (equal (fn-rtc-slot 1 s) '(1 :live 0))
                (true-listp (fn-rtc-mstates s)) (< 1 (len (fn-rtc-mstates s)))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                          '(fn-pth-invp fn-rtc-slot fn-rtc-nslots fn-rtc-nstatic
                            fn-rtc-configp nfix natp))
           :use ((:instance fn-rtc-statics-okp-get
                   (j 1) (k 1) (n (fn-rtc-nstatic (fn-rtc-config s)))
                   (slots (fn-rtc-slots s))))))))

(local
 (defthm fn-pth-mstate-of-deliver
  (equal (fn-rtc-mstate j (mv-nth 0 (fn-pth-deliver s id inc ev q)))
         (if (and (equal (nfix j) (nfix id)) (< (nfix id) (len (fn-rtc-mstates s))))
             (mv-nth 0 (fn-pth-m-step (fn-rtc-mstate id s) ev
                          (fn-rtc-view-state id inc s) (nfix q)))
           (fn-rtc-mstate j s)))
  :hints (("Goal" :in-theory (e/d (fn-pth-deliver fn-rtc-view-state)
                                  (fn-rtc-requests mv-nth))))))

(local
 (defthm fn-pth-ptx-mstate-off-timer
  (implies (not (equal (fn-rtc-get 0 ev) :timer))
           (equal (mv-nth 0 (fn-ptx-step m ev st q))
                  (mv-nth 0 (fn-ptx-step m ev st2 q))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                         '(fn-ptx-step fn-ptx-step1-0 fn-ptx-end-0 car-cons cdr-cons
                           mv-nth (:executable-counterpart zp) (:executable-counterpart nfix)
                           (:executable-counterpart equal) (:executable-counterpart member-equal)))))))

(local
 (defthm fn-pth-static-owner-not-free
  (implies (and (fn-pth-invp s) (<= 1 (fn-rtc-nstatic (fn-rtc-config s))))
           (not (equal (fn-rtc-free-slot 0 (fn-rtc-slots s)) 1)))
  :hints (("Goal" :use (fn-pth-static-owner-facts (:instance fn-rtc-free-slot-result (i 0) (slots (fn-rtc-slots s))))
           :in-theory (union-theories (theory 'minimal-theory)
                         '(fn-pth-static-owner-facts fn-rtc-slot fn-rtc-s-status
                           (:executable-counterpart fn-rtc-get) (:executable-counterpart binary-+) (:executable-counterpart natp)))))))

(local
 (defthm fn-pth-acting-use-is-ok
  (implies (and (fn-pth-invp s) (fn-rtc-acts-on-p s e))
           (and (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))
                (fn-rtc-use-okp (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) s)))
  :hints (("Goal" :in-theory (e/d (fn-pth-invp fn-rtc-acts-on-p fn-rtc-hand-delivers-p)
                                  (fn-rtc-use-okp fn-rtc-uses-okp fn-rtc-find-use fn-rtc-key
                                   fn-rtc-pool-okp fn-pth-mstates-okp fn-rtc-completionp
                                   fn-rtc-slots-okp fn-rtc-statics-okp fn-rtc-draining-okp))
           :use ((:instance fn-rtc-find-use-is-member (k (fn-rtc-key e)) (uses (fn-rtc-uses s)))
                 (:instance fn-rtc-uses-okp-member (uses (fn-rtc-uses s))
                             (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))))))))

(local
 (defthm fn-pth-timer-has-no-handle
  (implies (and (fn-pth-invp s) (fn-rtc-acts-on-p s e) (equal (fn-rtc-e-kind e) :timer))
           (not (fn-rtc-handlep (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))))
  :hints (("Goal" :use (fn-pth-acting-use-is-ok
                         (:instance fn-rtc-key-of-find-use (k (fn-rtc-key e)) (uses (fn-rtc-uses s)))
                         (:instance fn-rtc-key-equal-parts
                           (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))))
           :in-theory (union-theories (theory 'minimal-theory)
                     '(fn-rtc-use-okp fn-rtc-usep fn-rtc-u-hd fn-rtc-e-kind
                       (:executable-counterpart member-equal) (:executable-counterpart fn-rtc-handlep)))))))

(local
 (defthm fn-pth-pool-of-end-use-without-handle
  (implies (not (fn-rtc-handlep (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))))
           (equal (fn-rtc-pool (fn-rtc-end-use s e)) (fn-rtc-pool s)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                      '(fn-rtc-end-use fn-rtc-end-lease fn-rtc-retire-drained
                        fn-rtc-with-accessors car-cons cdr-cons))))))

(local
 (defthm fn-pth-timer-view-of-end-use
  (implies (and (fn-pth-invp s) (fn-rtc-acts-on-p s e) (equal (fn-rtc-e-kind e) :timer))
           (equal (fn-rtc-view-state id inc (fn-rtc-end-use s e)) (fn-rtc-view-state id inc s)))
  :hints (("Goal" :use (fn-pth-timer-has-no-handle)
           :in-theory (union-theories (theory 'minimal-theory)
                     '(fn-rtc-view-state fn-rtc-view fn-pth-pool-of-end-use-without-handle
                       fn-rtc-end-use-config))))))

(local
 (defthm fn-pth-owner-nth-as-mstate
  (equal (nth 1 (fn-rtc-mstates s)) (fn-rtc-mstate 1 s))
  :hints (("Goal" :use (fn-pth-owner-mstate-as-nth)
           :in-theory (theory 'minimal-theory)))))

(local
 (defthm fn-pth-static-slot-of-end-use
  (implies (and (fn-pth-invp s) (<= 1 (fn-rtc-nstatic (fn-rtc-config s))))
           (equal (fn-rtc-slot 1 (fn-rtc-end-use s e)) '(1 :live 0)))
  :hints (("Goal" :use (fn-pth-static-owner-facts)
           :in-theory (union-theories (theory 'minimal-theory)
                      '(fn-rtc-end-use fn-rtc-end-lease fn-rtc-retire-drained fn-rtc-slot-of-with
                        fn-rtc-s-status fn-rtc-s-inc nfix natp (:executable-counterpart fn-rtc-get)
                        (:executable-counterpart nfix) (:executable-counterpart zp) car-cons cdr-cons))))))

(local
 (defthm fn-pth-static-owner-not-free-after-end-use
  (implies (and (fn-pth-invp s) (<= 1 (fn-rtc-nstatic (fn-rtc-config s))))
           (not (equal (fn-rtc-free-slot 0 (fn-rtc-slots (fn-rtc-end-use s e))) 1)))
  :hints (("Goal" :use (fn-pth-static-slot-of-end-use
                         (:instance fn-rtc-free-slot-result (i 0) (slots (fn-rtc-slots (fn-rtc-end-use s e)))))
           :in-theory (union-theories (theory 'minimal-theory)
                         '(fn-rtc-slot fn-rtc-s-status (:executable-counterpart fn-rtc-get)
                           (:executable-counterpart binary-+) (:executable-counterpart natp)))))))

(local
 (defthm fn-pth-end-use-mstates
  (equal (fn-rtc-mstates (fn-rtc-end-use s e)) (fn-rtc-mstates s))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                     '(fn-rtc-end-use fn-rtc-end-lease fn-rtc-retire-drained fn-rtc-with-accessors))))))

(local
 (defthm fn-pth-owner-direct-facts
  (implies (and (fn-pth-invp s) (<= 1 (fn-rtc-nstatic (fn-rtc-config s)))
                (fn-rtc-acts-on-p s e) (not (fn-rtc-hand-delivers-p s e))
                (equal (fn-rtc-e-id e) 1))
           (and (equal (fn-rtc-e-inc e) 1) (not (equal (fn-rtc-e-kind e) :close))))
  :hints (("Goal" :use (fn-pth-static-owner-facts)
           :in-theory (union-theories (theory 'minimal-theory)
                     '(fn-rtc-acts-on-p fn-rtc-s-inc fn-rtc-s-status
                       (:executable-counterpart fn-rtc-get) (:executable-counterpart nfix)))))))

(local
 (defthm fn-pth-owner-hand-inc
  (implies (and (fn-pth-invp s) (<= 1 (fn-rtc-nstatic (fn-rtc-config s)))
                (fn-rtc-hand-delivers-p s e) (equal (fn-rtc-hand-to s e) 1))
           (equal (fn-rtc-get 4 (fn-rtc-b-owner (fn-rtc-buffer
                        (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) s))) 1))
  :hints (("Goal" :use (fn-pth-static-owner-facts)
           :in-theory (union-theories (theory 'minimal-theory)
                     '(fn-rtc-hand-delivers-p fn-rtc-handed-to-live-p fn-rtc-live-p fn-rtc-hand-to
                       fn-rtc-s-inc fn-rtc-s-status (:executable-counterpart fn-rtc-get)
                       (:executable-counterpart nfix)))))))

(local
 (defthm fn-pth-listener-completion-id
  (implies (and (fn-pth-invp s) (fn-rtc-acts-on-p s e)
                (member-eq (fn-rtc-e-kind e) '(:accept :grant)))
           (equal (fn-rtc-e-id e) 0))
  :hints (("Goal" :use (fn-pth-acting-use-is-ok
                         (:instance fn-rtc-key-of-find-use (k (fn-rtc-key e)) (uses (fn-rtc-uses s)))
                         (:instance fn-rtc-key-equal-parts
                           (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))))
           :in-theory (union-theories (theory 'minimal-theory)
                     '(fn-rtc-use-okp fn-rtc-e-kind fn-rtc-e-id member-equal iff
                       (:executable-counterpart member-equal) (:executable-counterpart nfix)))))))

(local
 (defthm fn-pth-ev-kind
  (equal (fn-rtc-get 0 (fn-rtc-ev kind out id inc more)) kind)
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                     '(fn-rtc-ev fn-rtc-get-of-cons (:executable-counterpart zp)
                       (:executable-counterpart nfix)))))))

(local
 (defthm fn-pth-ptx-step-nonnatural-q
  (implies (not (natp q))
           (equal (fn-ptx-step m ev st q) (fn-ptx-step m ev st 0)))
  :hints (("Goal" :use (fn-ptx-step-nfix-q)
           :in-theory (union-theories (theory 'minimal-theory)
                         '(nfix natp (:executable-counterpart nfix)))))))

(local
 (defthm fn-pth-ptx-mstate-off-timer-normalize
  (implies (and (syntaxp (not (equal st ''nil))) (not (equal (fn-rtc-get 0 ev) :timer)))
           (equal (mv-nth 0 (fn-ptx-step m ev st q))
                  (mv-nth 0 (fn-ptx-step m ev nil q))))
  :hints (("Goal" :use ((:instance fn-pth-ptx-mstate-off-timer (st2 nil)))
           :in-theory (theory 'minimal-theory)))))

; The two section-R ties: static slot 1, incarnation 1.
(defthm fn-pth-owner-delivered-mstate
  (implies (and (fn-pth-invp s) (<= 1 (fn-rtc-nstatic (fn-rtc-config s)))
                (mv-nth 0 (fn-pth-owner-delivery s e q)))
           (equal (nth 1 (fn-rtc-mstates (mv-nth 0 (fn-pth-step s e q))))
                  (mv-nth 0 (fn-pthm-step (nth 1 (fn-rtc-mstates s))
                             (mv-nth 1 (fn-pth-owner-delivery s e q))
                             (fn-rtc-view-state 1 1 s) q))))
  :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
                     '(fn-pth-owner-delivery fn-pth-step fn-pth-step* fn-pth-mstate-of-deliver
                       fn-pth-owner-nth-as-mstate fn-pth-end-use-mstates fn-pth-owner-direct-facts
                       fn-pth-owner-hand-inc fn-pth-listener-completion-id fn-rtc-hand-to
                       fn-pth-static-owner-facts fn-pth-static-owner-not-free-after-end-use
                       fn-rtc-rearm-frame fn-rtc-mstate-of-end-use fn-pth-m-step fn-pthm-step
                       fn-rtc-ev-names-its-instance fn-rtc-hand-delivers-kind fn-pth-ev-kind fn-pth-ptx-mstate-off-timer-normalize fn-pth-timer-view-of-end-use
                       fn-pth-ptx-step-nonnatural-q nfix natp member-equal car-cons cdr-cons (:executable-counterpart member-equal) (:executable-counterpart fn-rtc-get)
                       (:executable-counterpart nfix) (:executable-counterpart zp)))
           :cases ((equal (fn-rtc-e-kind e) :timer)) :do-not-induct t)))

(defthm fn-pth-owner-not-delivered-mstate
  (implies (and (fn-pth-invp s) (<= 1 (fn-rtc-nstatic (fn-rtc-config s)))
                (not (mv-nth 0 (fn-pth-owner-delivery s e q))))
           (equal (nth 1 (fn-rtc-mstates (mv-nth 0 (fn-pth-step s e q))))
                  (nth 1 (fn-rtc-mstates s))))
  :hints (("Goal" :use ((:instance fn-pth-machine-changes-only-when-delivered-to (j 1)))
           :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
                    '(fn-pth-owner-delivery fn-pth-owner-nth-as-mstate fn-rtc-target fn-rtc-hand-to
                      fn-pth-owner-direct-facts fn-pth-listener-completion-id
                      fn-pth-static-owner-not-free fn-pth-static-owner-not-free-after-end-use
                      fn-rtc-hand-delivers-kind fn-rtc-acts-on-id-natp nfix natp member-equal car-cons cdr-cons
                      (:executable-counterpart member-equal) (:executable-counterpart fn-rtc-get) (:executable-counterpart nfix)
                      (:executable-counterpart zp) (:executable-counterpart natp))))))


(defthm fn-pth-host-config-holds-the-workspace
  (let ((c (fn-hl-rtc-config profile mcfg q
                           *fn-pth-nstatic* 0 0 *fn-pth-qs* *fn-pth-cs*)))
    (and (fn-rtc-configp c)
         (equal (fn-rtc-nstatic-home c) *fn-pth-qs*)
         (iff (and (natp h) (< h (fn-rtc-nbufs c))
                   (equal (fn-rtc-home h c) 1))
              (and (natp h) (< h *fn-pth-qs*)))
         (implies (and (natp h) (< h *fn-pth-qs*))
                  (equal (fn-rtc-buf-cap h c) (fn-rtc-capf-static c)))
         (equal (fn-rtc-capf-static c) *fn-pth-cs*)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-hl-rtc-config-is-a-config
                               (cfg mcfg) (nstatic *fn-pth-nstatic*)
                               (qfixed 0) (capf 0) (qs *fn-pth-qs*) (cs *fn-pth-cs*)))
           :in-theory (enable fn-hl-rtc-config fn-rtc-nstatic-home fn-rtc-nbufs
                              fn-rtc-nstatic fn-rtc-qfixed-static fn-rtc-nconnections
                              fn-rtc-qfixed fn-rtc-nconnection-home fn-rtc-nhome
                              fn-rtc-home fn-rtc-buf-cap fn-rtc-capf-static fn-rtc-get))))

; A small nonempty reachable-state witness; the :opened use has op 0.
(defconst *fn-pth-rely-mcfg* '(1 nil 0 0 nil 0 0 0 nil 0 1))
(defconst *fn-pth-rely-cfg*
  (fn-hl-rtc-config *fn-bs-profile-development* *fn-pth-rely-mcfg* 100000
                    *fn-pth-nstatic* 0 0 *fn-pth-qs* *fn-pth-cs*))
(defconst *fn-pth-rely-events0*
  (list (list :opened 1 1 0 '(:done 0)
              (list (list 0 (make-list 32 :initial-element 0) 0 1 0)
                    0 '(1 256 256)))))
(defconst *fn-pth-rely-ops0*
  (list (list :complete (car *fn-pth-rely-events0*))))
(defconst *fn-pth-rely-state*
  (fn-rtc-make *fn-pth-rely-cfg*
               '((0 :live nil) (1 :live 0) (0 :free nil))
               (fn-rtc-free-pool 4) '((:accept 0 0 1 nil))
               (list nil (fn-ptx-opened (car (fn-rtc-e-data (car *fn-pth-rely-events0*)))
                                        0 '(1 256 256)) nil) 2))

(defthm fn-pth-reachablep-small-witness
  (fn-pth-reachablep *fn-pth-rely-state*)
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
             (union-theories
               '(fn-pth-host-run fn-pth-step fn-pth-step* fn-pth-deliver fn-pth-m-step
                 fn-pthm-step fn-ptx-step fn-ptx-step1 fn-ptx-wfp fn-ptx-size-rem
                 fn-ptx-wf-cost car-cons cdr-cons fn-rtc-requests fn-rtc-with-mstate fn-rtc-make
                 fn-rtc-set fn-rtc-mstates fn-rtc-rearm)
               (set-difference-theories (executable-counterpart-theory :here)
                 '((:executable-counterpart fn-pth-reachablep)
                   (:executable-counterpart fn-pth-host-run) (:executable-counterpart fn-pth-step)
                   (:executable-counterpart fn-pth-step*) (:executable-counterpart fn-pth-deliver)
                   (:executable-counterpart fn-pth-m-step) (:executable-counterpart fn-pthm-step)
                   (:executable-counterpart fn-ptx-step) (:executable-counterpart fn-ptx-step1)
                   (:executable-counterpart fn-ptx-wfp) (:executable-counterpart fn-ptx-wf-cost)))))
           :use ((:instance fn-pth-reachablep-suff
                                  (s *fn-pth-rely-state*)
                                  (profile *fn-bs-profile-development*) (mcfg *fn-pth-rely-mcfg*)
                                  (ops0 *fn-pth-rely-ops0*) (q0 100000))
                 (:instance fn-ptx-size-pos (x (fn-ptx-acc-begin 0)))
                 (:instance fn-ptx-acc-begin-bounded (txid 0))))))

(defthm fn-pth-reachablep-small-witness-is-idle
  (equal (fn-ptx-ph (nth 1 (fn-rtc-mstates *fn-pth-rely-state*))) :idle)
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here)))))


; A24: a build-time refusal checks the actual request binding. The theorem
; formula below is the fixed hand-written seat/A24 text, not generated.
(make-event
 (let* ((body (car (last (get-event 'fn-pth-deliver (w state)))))
        (binding (cadr body)))
  (if (and (equal (car body) 'mv-let) (equal (cadr binding) 'reqs)
           (equal (car (caddr (cadddr body))) 'fn-rtc-requests)
           (equal (cadr (caddr (cadddr body))) 'reqs))
      (value '(value-triple :delivery-request-site-unchanged))
    (er soft 'fn-pth-owner-requests-are-the-step-request-list "Delivery request site changed."))))

(local (defthm mh2-accept-owner-requests-nil
 (implies (and (equal (fn-rtc-get 0 ev) :accept) (equal (fn-rtc-ev-id ev) 1))
          (equal (mv-nth 1 (fn-pth-m-step m ev st q)) nil))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
    '(fn-pth-m-step fn-pthm-step fn-ptx-step fn-ptx-step1
      mv-nth car-cons cdr-cons (:executable-counterpart equal)
      (:executable-counterpart member-equal) (:executable-counterpart nfix)
      (:executable-counterpart zp)))))))

(defthm fn-pth-owner-requests-are-the-step-request-list
(implies (mv-nth 0 (fn-pth-owner-delivery s e q))
 (let* ((ev (mv-nth 1 (fn-pth-owner-delivery s e q))) (inc (fn-rtc-ev-inc ev)) (s1 (fn-rtc-end-use s e))
        (d (if (eq (fn-rtc-e-kind e) :accept)
               (fn-rtc-with-mstate 1 (fn-rtc-m-init) (fn-rtc-with-slot 1 (list inc :live (fn-rtc-get 1 (fn-rtc-get 1 ev))) s1))
             s1)))
  (equal (fn-pth-owner-requests s e q) (mv-nth 1 (fn-pth-m-step (fn-rtc-mstate 1 d) ev (fn-rtc-view-state 1 inc d) (nfix q))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
    '(fn-pth-owner-delivery fn-pth-owner-requests fn-rtc-view-state
      fn-rtc-e-kind fn-rtc-hand-delivers-p fn-rtc-get nth
      fn-rtc-ev-inc fn-rtc-ev-id fn-rtc-ev mh2-accept-owner-requests-nil
      fn-pthm-init fn-hlm-init car-cons cdr-cons mv-nth
      (:executable-counterpart fn-rtc-get) (:executable-counterpart nfix)
      (:executable-counterpart zp) (:executable-counterpart equal)
      (:executable-counterpart not))))))

; P13: RTC-U64 facts transported by the existing product-layer generator.
; Use the layer generator's own functional-instance substitutions and events.
(make-event
 (let* ((copied (fn-rtc-layer-alist 'fn-pth (append *fn-rtc-layer-spec-fns* *fn-rtc-layer-exec-fns*)))
        (alist (append '((fn-rtc-m-init . fn-pthm-init)
                         (fn-rtc-m-static-init . fn-pthm-static-init)
                         (fn-rtc-m-step . fn-pth-m-step)
                         (fn-rtc-m-committedp . fn-pthm-committedp)
                         (fn-rtc-m-c . fn-pthm-c)
                         (fn-rtc-m-max-reqs . fn-pthm-max-reqs)
                         (fn-rtc-m-max-state . fn-pthm-max-state)
                         (fn-rtc-mx-step . fn-pthm-step)) copied))
        (fi (fn-rtc-layer-fi-alist alist))
        (obligations (append (list 'natp)
          (fn-rtc-layer-names 'fn-pth
            '(fn-rtc-m-constants fn-rtc-mx-step-is-m-step fn-rtc-m-step-is-charged
              fn-rtc-m-step-requests-are-bounded fn-rtc-m-init-is-bounded
              fn-rtc-m-step-state-is-bounded fn-rtc-m-init-is-uncommitted
              fn-rtc-m-static-init-is-bounded fn-rtc-m-static-init-is-uncommitted
              fn-rtc-m-commits-only-on-fsync-done)))))
  (value (cons 'progn
    (fn-rtc-layer-keystone-events
      '(fn-rtc-slot-id-and-incarnation-are-u64 fn-rtc-step*-keeps-fixed-width-admission)
      'fn-pth alist fi (strip-cdrs copied) obligations (w state))))))

; Fixed-width slot projection over arbitrary host requests and completions.
; Listener request anomalies do not enter this scalar preservation argument.
; This predicate carries only fixed-width slot scalars, independently of
; listener-use validity or the machine/pool joint invariant.
(defun fn-pth-inc-tablep (slots)
 (declare (xargs :guard t :measure (len slots)
  :hints (("Goal" :in-theory
   (union-theories (theory 'minimal-theory)
    '(len o< o-finp o-p natp (:type-prescription len)))))))
 (if (consp slots)
  (and (fn-rtc-u64p (fn-rtc-s-inc (car slots))) (fn-pth-inc-tablep (cdr slots))) t))
(verify-guards fn-pth-inc-tablep)
(defthm fn-pth-inc-tablep-get
 (implies (fn-pth-inc-tablep slots)
  (fn-rtc-u64p (fn-rtc-s-inc (fn-rtc-get j slots))))
 :hints (("Goal" :induct (fn-rtc-get j slots)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '((:executable-counterpart zp) (:executable-counterpart nfix) fn-pth-inc-tablep fn-rtc-get fn-rtc-u64p fn-rtc-s-inc nfix natp zp
     car-cons cdr-cons (:executable-counterpart expt)
     (:executable-counterpart fn-rtc-s-inc) (:executable-counterpart fn-rtc-u64p))))))
(defthm fn-pth-slot-inc-is-u64-from-inc-table
 (implies (fn-pth-inc-tablep (fn-rtc-slots s))
  (fn-rtc-u64p (fn-rtc-s-inc (fn-rtc-slot j s))))
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '((:executable-counterpart zp) (:executable-counterpart nfix) fn-rtc-slot fn-pth-inc-tablep-get)))))
(defthm fn-pth-inc-tablep-set
 (implies (and (fn-pth-inc-tablep slots) (fn-rtc-u64p (fn-rtc-s-inc slot)))
  (fn-pth-inc-tablep (fn-rtc-set id slot slots)))
 :hints (("Goal" :induct (fn-rtc-set id slot slots)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '((:executable-counterpart zp) (:executable-counterpart nfix) fn-pth-inc-tablep fn-rtc-set car-cons cdr-cons)))))

(defthm fn-pth-inc-tablep-with-slot
 (implies (and (fn-pth-inc-tablep (fn-rtc-slots s))
               (fn-rtc-u64p (fn-rtc-s-inc slot)))
  (fn-pth-inc-tablep (fn-rtc-slots (fn-rtc-with-slot id slot s))))
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '((:executable-counterpart zp) (:executable-counterpart nfix) fn-rtc-with-accessors fn-pth-inc-tablep-set)))))
(defthm fn-pth-req-close-keeps-inc-table
 (implies (fn-pth-inc-tablep (fn-rtc-slots s))
  (fn-pth-inc-tablep (fn-rtc-slots (mv-nth 0 (fn-rtc-req-close r id inc s)))))
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '((:executable-counterpart zp) (:executable-counterpart nfix) fn-rtc-req-close fn-rtc-live-p
    fn-pth-inc-tablep-with-slot fn-pth-inc-tablep-set fn-rtc-with-accessors fn-rtc-issue-frame fn-pth-slot-inc-is-u64-from-inc-table
    fn-rtc-slot-accessors (:type-prescription fn-rtc-s-inc) nfix natp zp car-cons cdr-cons fn-hld-mv-nth-0-cons)))))
(defthm fn-pth-request-keeps-inc-table
 (implies (fn-pth-inc-tablep (fn-rtc-slots s))
  (fn-pth-inc-tablep (fn-rtc-slots (mv-nth 0 (fn-rtc-request r id inc s)))))
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '((:executable-counterpart zp) (:executable-counterpart nfix) fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release
    fn-rtc-req-submit fn-rtc-req-cancel fn-pth-req-close-keeps-inc-table
    fn-rtc-with-accessors fn-rtc-issue-frame fn-rtc-issue-frame
    fn-hld-mv-nth-0-cons car-cons cdr-cons)))))
(defthm fn-pth-requests-keep-inc-table
 (implies (fn-pth-inc-tablep (fn-rtc-slots s))
  (fn-pth-inc-tablep (fn-rtc-slots (mv-nth 0 (fn-rtc-requests rs id inc s)))))
 :hints (("Goal" :induct (fn-rtc-requests rs id inc s)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '((:executable-counterpart zp) (:executable-counterpart nfix) fn-rtc-requests fn-pth-request-keeps-inc-table fn-hld-mv-nth-0-cons car-cons cdr-cons)))))
(defthm fn-pth-retire-keeps-inc-table
 (implies (fn-pth-inc-tablep (fn-rtc-slots s))
  (fn-pth-inc-tablep (fn-rtc-slots (fn-rtc-retire-drained id s))))
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '((:executable-counterpart zp) (:executable-counterpart nfix) fn-rtc-retire-drained fn-pth-inc-tablep-with-slot fn-pth-inc-tablep-set fn-pth-slot-inc-is-u64-from-inc-table
    fn-rtc-slot-accessors (:type-prescription fn-rtc-s-inc) nfix natp zp car-cons cdr-cons)))))
(defthm fn-pth-end-use-keeps-inc-table
 (implies (fn-pth-inc-tablep (fn-rtc-slots s))
  (fn-pth-inc-tablep (fn-rtc-slots (fn-rtc-end-use s e))))
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '((:executable-counterpart zp) (:executable-counterpart nfix) fn-rtc-end-use fn-rtc-end-lease-keeps-slot-table
    fn-pth-retire-keeps-inc-table fn-rtc-with-accessors fn-rtc-issue-frame)))))
(defthm fn-pth-deliver-keeps-inc-table
 (implies (fn-pth-inc-tablep (fn-rtc-slots s))
  (fn-pth-inc-tablep (fn-rtc-slots (mv-nth 0 (fn-pth-deliver s id inc ev q)))))
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '((:executable-counterpart zp) (:executable-counterpart nfix) fn-pth-deliver fn-pth-requests-keep-inc-table fn-rtc-with-accessors fn-rtc-issue-frame
    fn-hld-mv-nth-0-cons car-cons cdr-cons)))))
(defthm fn-pth-rearm-keeps-inc-table
 (implies (fn-pth-inc-tablep (fn-rtc-slots s))
  (fn-pth-inc-tablep (fn-rtc-slots (mv-nth 0 (fn-rtc-rearm s)))))
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '((:executable-counterpart zp) (:executable-counterpart nfix) fn-rtc-rearm-frame)))))
(defthm fn-pth-accept-keeps-inc-table
 (implies (fn-pth-inc-tablep (fn-rtc-slots s1))
  (fn-pth-inc-tablep (fn-rtc-slots (mv-nth 0 (fn-pth-accept-branch s1 out q)))))
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '((:executable-counterpart zp) (:executable-counterpart nfix) fn-pth-accept-branch fn-pth-deliver-keeps-inc-table fn-pth-rearm-keeps-inc-table
    fn-pth-inc-tablep-with-slot fn-pth-inc-tablep-set fn-rtc-with-accessors fn-rtc-issue-frame
    fn-rtc-inc-roomp fn-rtc-s-inc fn-rtc-get fn-rtc-u64p
    natp nfix zp car-cons cdr-cons fn-hld-mv-nth-0-cons
    default-+-1 default-+-2 (:type-prescription fn-rtc-s-inc)
    (:executable-counterpart expt))))))
(defthm fn-pth-close-keeps-inc-table
 (implies (and (fn-pth-inc-tablep (fn-rtc-slots s1)) (fn-rtc-u64p inc))
  (fn-pth-inc-tablep (fn-rtc-slots (mv-nth 0 (fn-pth-close-branch s1 id inc)))))
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '((:executable-counterpart zp) (:executable-counterpart nfix) fn-pth-close-branch fn-pth-inc-tablep-with-slot fn-pth-inc-tablep-set fn-rtc-with-accessors fn-rtc-issue-frame
    fn-pth-rearm-keeps-inc-table fn-rtc-make-accessors
    fn-rtc-slot-accessors fn-rtc-u64p nfix natp zp car-cons cdr-cons fn-hld-mv-nth-0-cons)))))
(defthm fn-pth-grant-keeps-inc-table
 (implies (fn-pth-inc-tablep (fn-rtc-slots s))
  (fn-pth-inc-tablep (fn-rtc-slots (mv-nth 0 (fn-rtc-grant n s)))))
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '((:executable-counterpart zp) (:executable-counterpart nfix) fn-rtc-grant-frame)))))
(defthm fn-pth-acting-close-inc-is-u64
 (implies (and (fn-pth-inc-tablep (fn-rtc-slots s))
               (fn-rtc-acts-on-p s e) (not (fn-rtc-hand-delivers-p s e)))
  (fn-rtc-u64p (fn-rtc-e-inc e)))
 :hints (("Goal" :use fn-rtc-acting-close-incarnation
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '((:executable-counterpart zp) (:executable-counterpart nfix) fn-pth-inc-tablep-get fn-rtc-slot)))))
(defthm fn-pth-step-keeps-inc-table
 (implies (fn-pth-inc-tablep (fn-rtc-slots s))
  (fn-pth-inc-tablep (fn-rtc-slots (mv-nth 0 (fn-pth-step* s e q)))))
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '((:executable-counterpart zp) (:executable-counterpart nfix) fn-pth-step* fn-pth-deliver-keeps-inc-table fn-pth-rearm-keeps-inc-table
    fn-pth-accept-keeps-inc-table fn-pth-close-keeps-inc-table
    fn-pth-grant-keeps-inc-table fn-pth-end-use-keeps-inc-table
    fn-pth-acting-close-inc-is-u64 fn-hld-mv-nth-0-cons car-cons cdr-cons))
  :use fn-pth-acting-close-inc-is-u64)))
(defthm fn-pth-step-config-frame-without-global-invariant
 (equal (fn-rtc-config (mv-nth 0 (fn-pth-step* s e q))) (fn-rtc-config s))
 :hints (("Goal" :in-theory
  (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '((:executable-counterpart zp) (:executable-counterpart nfix) fn-pth-step* fn-pth-deliver fn-pth-accept-branch fn-pth-close-branch
     fn-rtc-grant-frame fn-rtc-end-use-config fn-rtc-rearm-frame
     fn-rtc-make-accessors fn-rtc-with-accessors fn-rtc-requests-config-frame
     fn-hld-mv-nth-0-cons car-cons cdr-cons)))))
(defthm fn-pth-host-run-keeps-inc-table
 (implies (fn-pth-inc-tablep (fn-rtc-slots s))
  (fn-pth-inc-tablep (fn-rtc-slots (fn-pth-host-run s ops q))))
 :hints (("Goal" :induct (fn-pth-host-run s ops q)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '((:executable-counterpart zp) (:executable-counterpart nfix) fn-pth-host-run fn-pth-step fn-pth-step-keeps-inc-table
     fn-pth-requests-keep-inc-table fn-hld-mv-nth-0-cons car-cons cdr-cons)))))
(defthm fn-pth-host-run-config-frame
 (equal (fn-rtc-config (fn-pth-host-run s ops q)) (fn-rtc-config s))
 :hints (("Goal" :induct (fn-pth-host-run s ops q)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '((:executable-counterpart zp) (:executable-counterpart nfix) fn-pth-host-run fn-pth-step fn-pth-step-config-frame-without-global-invariant
     fn-rtc-requests-config-frame fn-hld-mv-nth-0-cons car-cons cdr-cons)))))
(defthm fn-pth-slots-okp-implies-inc-table
 (implies (fn-rtc-slots-okp i slots) (fn-pth-inc-tablep slots))
 :hints (("Goal" :induct (fn-rtc-slots-okp i slots)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '((:executable-counterpart zp) (:executable-counterpart nfix) fn-rtc-slots-okp fn-pth-inc-tablep fn-rtc-slotp-incarnation-u64
     car-cons cdr-cons)))))
(defthm fn-pth-init-inc-table
 (implies (fn-rtc-configp cfg)
  (fn-pth-inc-tablep (fn-rtc-slots (mv-nth 0 (fn-pth-init cfg)))))
 :hints (("Goal" :use fn-pth-init-establishes-invp
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '((:executable-counterpart zp) (:executable-counterpart nfix) fn-pth-invp fn-pth-slots-okp-implies-inc-table)))))
(defthm fn-pth-arm-opened-config-frame
 (equal (fn-rtc-config (mv-nth 0 (fn-pth-arm-opened j n s))) (fn-rtc-config s))
 :hints (("Goal" :induct (fn-pth-arm-opened j n s)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '((:executable-counterpart zp) (:executable-counterpart nfix) fn-pth-arm-opened fn-rtc-issue-frame fn-hld-mv-nth-0-cons car-cons cdr-cons)))))
(defthm fn-pth-init-config-frame
 (equal (fn-rtc-config (mv-nth 0 (fn-pth-init cfg))) cfg)
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '((:executable-counterpart zp) (:executable-counterpart nfix) fn-pth-init fn-pth-arm-opened-config-frame fn-rtc-rearm-frame
    fn-rtc-make-accessors fn-hld-mv-nth-0-cons car-cons cdr-cons)))))
(defthm fn-pth-reachable-slot-scalars-and-admission
 (implies (fn-pth-reachablep s)
  (and (fn-pth-inc-tablep (fn-rtc-slots s))
       (fn-rtc-st-cfg-okp (fn-rtc-config s))))
 :hints (("Goal" :expand ((fn-pth-reachablep s))
  :use ((:instance fn-pth-host-run-keeps-inc-table
    (s (mv-nth 0
      (fn-pth-init
        (fn-hl-rtc-config
          (mv-nth 0 (fn-pth-reachablep-witness s))
          (mv-nth 1 (fn-pth-reachablep-witness s))
          (mv-nth 3 (fn-pth-reachablep-witness s))
          *fn-pth-nstatic* 0 0 *fn-pth-qs* *fn-pth-cs*))))
    (ops (mv-nth 2 (fn-pth-reachablep-witness s)))
    (q (mv-nth 3 (fn-pth-reachablep-witness s)))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '((:executable-counterpart zp) (:executable-counterpart nfix) fn-pth-host-run-keeps-inc-table fn-pth-init-inc-table
     fn-pth-host-run-config-frame fn-pth-init-config-frame
     fn-rtc-rearm-frame fn-rtc-make-accessors fn-hld-mv-nth-0-cons car-cons cdr-cons)))))
; Approved final lemma follows only after the above have PROVED. The source
; text in c6s/PENDING.lisp is the authority, not this candidate wrapper.
(defthm fn-pth-live-slot-inc-below-2^64
 (implies (and (fn-pth-reachablep s) (natp id)
               (< id (fn-rtc-nslots (fn-rtc-config s)))
               (equal (fn-rtc-s-status (fn-rtc-slot id s)) :live))
          (and (< id (expt 2 64))
               (< (fn-rtc-s-inc (fn-rtc-slot id s)) (expt 2 64))))
 :hints (("Goal" :use (fn-pth-reachable-slot-scalars-and-admission
         (:instance fn-pth-slot-inc-is-u64-from-inc-table (j id)))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '((:executable-counterpart zp) (:executable-counterpart nfix) fn-rtc-st-cfg-okp fn-rtc-u64p
     natp (:executable-counterpart expt))))))

; Joint I carries present slot/configuration scalars, buffer/use compatibility,
; and POST phase, queue, workspace, byte and pending-operation facts. Listener
; requests and aliases are covered separately from the legacy uses-okp rule.
; I contains no reachability or future step/request/rely conclusion. Its base
; and the owner part under foreign requests are proved below. Global/completion
; preservation and the OD/R0-R2 consequences remain owed. The proposed form and
; pre-proof rationale are recorded in build/post-runs/l2/c6a/I-FORM.lisp.
; Joint I: BASE and foreign-request OWNER part only; completion/global preservation and OD/R0-R2 are not claimed.


; From c6a/I-FORM.lisp
(defun fn-pth-i-buffer-ownerp (o)
 (and (true-listp o)
  (case (fn-rtc-get 0 o)
   (:free (equal o '(:free)))
   (:workspace (and (equal (len o) 3) (natp (fn-rtc-get 1 o))
                    (fn-rtc-u64p (fn-rtc-get 2 o))))
   (:leased (and (equal (len o) 4) (natp (fn-rtc-get 1 o))
                 (fn-rtc-u64p (fn-rtc-get 2 o))
                 (member-eq (fn-rtc-get 3 o) '(:in :out))))
   (:handed (and (equal (len o) 5) (posp (fn-rtc-get 1 o))
                 (fn-rtc-u64p (fn-rtc-get 2 o))
                 (posp (fn-rtc-get 3 o)) (natp (fn-rtc-get 4 o))))
   (otherwise nil))))
(defun fn-pth-i-pool (h pool s)
 (declare (xargs :measure (len pool) :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(len o< o-finp o-p natp (:type-prescription len)))))))
 (if (consp pool)
  (let* ((b (car pool)) (o (fn-rtc-b-owner b)) (id (fn-rtc-get 1 o)))
   (and (fn-pth-i-buffer-ownerp o)
    (case (fn-rtc-get 0 o)
     (:workspace (and (< id (fn-rtc-nslots (fn-rtc-config s)))
       (equal (fn-rtc-get 2 o) (fn-rtc-s-inc (fn-rtc-slot id s)))
       (member-eq (fn-rtc-s-status (fn-rtc-slot id s)) '(:live :closing))))
     (:leased (and (< id (fn-rtc-nslots (fn-rtc-config s)))
       (fn-rtc-holds-p h (fn-rtc-b-gen b) (fn-rtc-uses s))))
     (:handed (and (< id (fn-rtc-nslots (fn-rtc-config s)))
       (< (fn-rtc-get 3 o) (fn-rtc-nslots (fn-rtc-config s)))
       (not (equal id (fn-rtc-get 3 o)))
       (implies (< (fn-rtc-nstatic (fn-rtc-config s)) id)
                (<= (fn-rtc-get 3 o) (fn-rtc-nstatic (fn-rtc-config s))))
       (fn-rtc-holds-p h (fn-rtc-b-gen b) (fn-rtc-uses s))))
     (otherwise t))
    (fn-pth-i-pool (+ 1 (nfix h)) (cdr pool) s)))
  (null pool)))
(defun fn-pth-i-listener-use (u s)
 (let* ((kind (fn-rtc-get 0 u)) (raw-id (fn-rtc-get 1 u))
        (hd (fn-rtc-u-hd u)) (h (fn-rtc-h-buf hd))
        (b (fn-rtc-buffer h s)) (o (fn-rtc-b-owner b)))
  (and (equal (nfix raw-id) 0) (equal (fn-rtc-get 2 u) 0)
   (true-listp u) (equal (len u) 5) (natp (fn-rtc-get 3 u))
   (< (fn-rtc-get 3 u) (fn-rtc-next-op s))
   (member-eq kind (cons :wait *fn-rtc-machine-kinds*))
   (not (equal kind :hand))
   (if (or (fn-rtc-buffered-kind-p kind) (equal kind :pool))
    (and (equal raw-id 0) (fn-rtc-handlep hd)
     (< h (fn-rtc-nbufs (fn-rtc-config s)))
     (equal (fn-rtc-h-gen hd) (fn-rtc-b-gen b))
     (equal o (list :leased 0 0
        (if (member-eq kind (cons :pool *fn-rtc-in-kinds*)) :in :out)))
     (cond
      ((equal kind :pool)
       (and (fn-rtc-pool-buf-p h (fn-rtc-config s))
        (equal (fn-rtc-h-off hd) 0) (equal (fn-rtc-h-len hd) 0)
        (null (fn-rtc-b-bytes b))
        (equal (fn-rtc-holders h (fn-rtc-h-gen hd) (fn-rtc-uses s)) 1)))
      ((member-eq kind *fn-rtc-in-kinds*)
       (and (<= (fn-rtc-h-off hd) (len (fn-rtc-b-bytes b)))
        (<= (+ (fn-rtc-h-off hd) (fn-rtc-h-len hd))
            (fn-rtc-buf-cap h (fn-rtc-config s)))
        (equal (fn-rtc-holders h (fn-rtc-h-gen hd) (fn-rtc-uses s)) 1)))
      (t (<= (+ (fn-rtc-h-off hd) (fn-rtc-h-len hd))
             (len (fn-rtc-b-bytes b))))))
    (null hd)))))
(defun fn-pth-i-uses (uses s)
 (declare (xargs :measure (len uses) :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(len o< o-finp o-p natp (:type-prescription len)))))))
 (if (consp uses)
  (let ((u (car uses)))
   (and (or (fn-rtc-use-okp u s) (fn-pth-i-listener-use u s))
    (or (member-eq (fn-rtc-get 0 u) '(:hand :pool))
        (not (fn-rtc-kind-out-p (fn-rtc-get 0 u) (fn-rtc-get 1 u)
                              (fn-rtc-get 2 u) (cdr uses))))
    (not (fn-rtc-op-used-p (fn-rtc-get 3 u) (cdr uses)))
    (fn-pth-i-uses (cdr uses) s)))
  (null uses)))
(defun fn-pth-i-visible-buffer (h s leasedp)
 (and (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
  (or (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:workspace 1 1))
      (and leasedp
       (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:leased 1 1 :out))))))
(defun fn-pth-i-post (p s leasedp)
 (let ((fid (fn-ptx-cur-fid p)) (finc (fn-ptx-cur-finc p))
       (h (fn-ptx-cur-bp p)))
  (and (natp fid) (< 1 fid) (< fid (fn-rtc-nslots (fn-rtc-config s)))
   (fn-rtc-u64p finc) (fn-pth-i-visible-buffer h s leasedp))))
(defun fn-pth-i-queue (ps s used)
 (declare (xargs :measure (len ps) :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(len o< o-finp o-p natp (:type-prescription len)))))))
 (if (consp ps)
  (let* ((p (car ps)) (h (fn-ptx-cur-bp p)))
   (and (fn-pth-i-post p s nil) (not (member-equal h used))
    (equal (len (fn-rtc-b-bytes (fn-rtc-buffer h s))) (fn-ptx-cur-len p))
    (fn-pth-i-queue (cdr ps) s (cons h used))))
  (null ps)))
(defun fn-pth-i-owner-uses (uses m)
 (declare (xargs :measure (len uses) :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(len o< o-finp o-p natp (:type-prescription len)))))))
 (if (consp uses)
  (let ((u (car uses)))
   (and (implies (equal (fn-rtc-get 1 u) 1)
     (and (equal (fn-rtc-get 2 u) 1)
      (or (equal (fn-rtc-get 0 u) :hand)
          (and (equal (fn-ptx-ph m) :closed) (equal (fn-rtc-get 0 u) :opened))
          (and (fn-ptx-expected m) (equal (fn-rtc-get 0 u) (fn-ptx-expected m))))))
    (fn-pth-i-owner-uses (cdr uses) m))) t))
(defun fn-pth-i-post-state (m s)
 (let* ((ph (fn-ptx-ph m)) (cur (fn-ptx-cur m))
        (active (member-eq ph '(:reading :hashing :extending :extsyncing
                               :payload-writing :log-writing :committing)))
        (flight (fn-ptx-in-flight-p ph))
        (bp (fn-ptx-cur-bp cur)) (b1 (fn-ptx-b1 m)) (b3 (fn-ptx-b3 m))
        (h1 (fn-ptx-buf-h b1)) (h3 (fn-ptx-buf-h b3))
        (used (append (if active (list bp) nil)
                      (if (consp b1) (list h1 h3) nil))))
  (and (fn-ptx-okp m)
   (fn-cbor-octet-listp (fn-ptx-kd-last (fn-ptx-kd m)))
   (implies flight (fn-cbor-octet-listp (fn-rtc-get 1 (fn-ptx-hs m))))
   (< (fn-ptx-ext m) (expt 2 64)) (< (fn-ptx-nxt m) (expt 2 64))
   (fn-pth-i-owner-uses (fn-rtc-uses s) m)
   (implies (fn-ptx-expected m)
            (fn-rtc-kind-out-p (fn-ptx-expected m) 1 1 (fn-rtc-uses s)))
   (fn-pth-i-queue (fn-ptx-q m) s used)
   (implies (not active) (and (null cur) (null b1) (null b3)))
   (implies active
    (and (fn-pth-i-post cur s flight)
     (equal (len (fn-rtc-b-bytes (fn-rtc-buffer bp s)))
      (if (equal ph :reading) (fn-ptx-cur-len cur)
       (+ (fn-ptx-cur-base cur) (fn-ptx-cur-len cur) (fn-ptx-cur-glen cur))))))
   (implies (equal ph :reading) (and (null b1) (null b3)))
   (implies (or (equal ph :hashing) flight)
    (and (consp b1) (consp b3) (natp h1) (natp h3)
     (< h1 *fn-pth-qs*) (< h3 *fn-pth-qs*)
     (not (equal h1 h3)) (not (equal h1 bp)) (not (equal h3 bp))
     (fn-pth-i-visible-buffer h1 s flight) (fn-pth-i-visible-buffer h3 s flight)
     (equal (len (fn-rtc-b-bytes (fn-rtc-buffer h1 s)))
            (+ (fn-ptx-buf-len b1) (fn-ptx-buf-x b1)))
     (equal (len (fn-rtc-b-bytes (fn-rtc-buffer h3 s))) (fn-ptx-buf-len b3))
     (<= (fn-ptx-buf-x b3) (fn-ptx-buf-cut b3))
     (equal (fn-ptx-buf-cut b3) *fn-ptx-sufhead-max*)
     (<= (fn-ptx-buf-cut b3) (fn-ptx-buf-len b3))))
   (implies (equal ph :hashing)
    (and (equal (fn-ptx-buf-g b1) (fn-rtc-b-gen (fn-rtc-buffer h1 s)))
     (equal (fn-ptx-buf-g b3) (fn-rtc-b-gen (fn-rtc-buffer h3 s)))
     (<= (+ (fn-ptx-buf-len b3) 32) (fn-rtc-buf-cap h3 (fn-rtc-config s)))
     (equal (take (fn-ptx-head-len) (fn-rtc-b-bytes (fn-rtc-buffer h1 s)))
      (append (fn-ptx-frame-header (- (fn-ptx-nmsg m) (fn-ptx-head-len)))
              (fn-ptx-kd-last (fn-ptx-kd m))))))
   (implies flight
    (<= (+ (fn-ptx-kd-frontier (fn-ptx-kd m)) (fn-ptx-elen m)) (fn-ptx-nxt m))))))
(defun fn-pth-i (s)
 (let ((c (fn-rtc-config s)))
  (and (fn-rtc-shapep s) (fn-rtc-st-cfg-okp c)
   (equal (fn-rtc-nstatic c) *fn-pth-nstatic*)
   (equal (fn-rtc-qfixed c) 0)
   (equal (fn-rtc-nstatic-home c) *fn-pth-qs*)
   (equal (fn-rtc-capf-static c) *fn-pth-cs*) (posp (fn-rtc-capl c))
   (fn-rtc-slots-okp 0 (fn-rtc-slots s))
   (equal (fn-rtc-slot 0 s) *fn-rtc-listener*)
   (equal (fn-rtc-slot 1 s) '(1 :live 0))
   (fn-pth-inc-tablep (fn-rtc-slots s))
   (fn-pth-i-pool 0 (fn-rtc-pool s) s) (fn-pth-i-uses (fn-rtc-uses s) s)
   (fn-pth-i-post-state (fn-rtc-mstate 1 s) s))))


; From c6a/p15b-I-foreign-requests.lisp
(defthm fn-pth-request-foreign-workspace-frame
 (implies (and (not (equal id 1))
               (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:workspace 1 1)))
          (equal (fn-rtc-buffer h (mv-nth 0 (fn-rtc-request r id inc s)))
                 (fn-rtc-buffer h s)))
 :hints (("Goal" :cases ((natp h))
  :in-theory (union-theories
   (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release
     fn-rtc-req-close fn-rtc-req-cancel fn-rtc-req-submit fn-rtc-submit-okp
     fn-rtc-buffer-of-with fn-rtc-buffer-accessors fn-rtc-issue-frame
     fn-rtc-buffer-of-non-natp fn-rtc-get-of-cons
     fn-hld-mv-nth-0-cons car-cons cdr-cons nfix natp
     (:type-prescription fn-rtc-h-buf)
     (:executable-counterpart nfix) (:executable-counterpart zp)
     (:executable-counterpart natp) (:executable-counterpart equal)
     (:executable-counterpart fn-rtc-get) (:executable-counterpart member-equal))))))
(defthm fn-pth-request-visible-buffer-frame
 (implies (and (not (equal id 1))
               (fn-rtc-view-own-p (fn-rtc-b-owner (fn-rtc-buffer h s)) 1 1))
          (equal (fn-rtc-buffer h (mv-nth 0 (fn-rtc-request r id inc s)))
                 (fn-rtc-buffer h s)))
 :hints (("Goal" :use (fn-pth-request-foreign-workspace-frame fn-rtc-request-keeps-leased)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-view-own-p fn-rtc-leasedp (:executable-counterpart fn-rtc-get)
     (:executable-counterpart equal) (:executable-counterpart member-equal))))))
(defthm fn-pth-requests-visible-buffer-frame
 (implies (and (not (equal id 1))
               (fn-rtc-view-own-p (fn-rtc-b-owner (fn-rtc-buffer h s)) 1 1))
          (equal (fn-rtc-buffer h (mv-nth 0 (fn-rtc-requests rs id inc s)))
                 (fn-rtc-buffer h s)))
 :hints (("Goal" :induct (fn-rtc-requests rs id inc s)
  :in-theory (union-theories
   (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-requests fn-pth-request-visible-buffer-frame fn-hld-mv-nth-0-cons
     car-cons cdr-cons (:executable-counterpart zp) (:executable-counterpart nfix))))))


; From c6a/p15b-I-foundation.lisp
(defthm fn-pth-i-uses-from-uses-okp
 (implies (fn-rtc-uses-okp uses s) (fn-pth-i-uses uses s))
 :hints (("Goal" :induct (fn-rtc-uses-okp uses s)
  :in-theory (union-theories (theory 'minimal-theory)
    '(fn-rtc-uses-okp fn-pth-i-uses)))))


; From c6a/p15b-I-init-pool.lisp
(defun fn-pth-i-free-pool-induct (h n)
 (declare (xargs :measure (nfix n)
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(nfix zp natp o-p o-finp o<))))))
 (if (zp n) (list h n)
  (fn-pth-i-free-pool-induct (+ 1 (nfix h)) (- n 1))))
(defthm fn-pth-i-pool-free
 (fn-pth-i-pool h (fn-rtc-free-pool n) s)
 :hints (("Goal" :induct (fn-pth-i-free-pool-induct h n)
  :in-theory (union-theories (theory 'minimal-theory)
   '((:induction fn-pth-i-free-pool-induct) fn-pth-i-pool fn-pth-i-buffer-ownerp fn-rtc-free-pool
     fn-rtc-b-owner fn-rtc-get-of-cons
     car-cons cdr-cons (:executable-counterpart equal)
     (:executable-counterpart len) (:executable-counterpart true-listp)
     (:executable-counterpart fn-rtc-get) (:executable-counterpart zp)
     (:executable-counterpart nfix))))))


; From c6a/p15b-I-closed.lisp
(defthm fn-pth-i-closed-post-state
 (implies (fn-pth-i-owner-uses (fn-rtc-uses s) (fn-ptx-closed))
          (fn-pth-i-post-state (fn-ptx-closed) s))
 :hints (("Goal" :use (fn-ptx-closed-is-ok)
  :in-theory (union-theories (theory 'minimal-theory)
   (append '(fn-pth-i-post-state fn-pth-i-queue fn-ptx-in-flight-p)
    (remove-equal nil
     (loop$ for rune in (current-theory :here) collect
       (if (equal (car rune) :executable-counterpart) rune nil))))))))


; From c6a/p15b-I-shape.lisp
(defthm fn-pth-rearm-pool-and-mstates-frame
 (and (equal (fn-rtc-pool (mv-nth 0 (fn-rtc-rearm s))) (fn-rtc-pool s))
      (equal (fn-rtc-mstates (mv-nth 0 (fn-rtc-rearm s))) (fn-rtc-mstates s)))
 :hints (("Goal" :in-theory (union-theories
  (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-rearm fn-rtc-arm-accept fn-rtc-arm-grant fn-rtc-issue-frame
     fn-hld-mv-nth-0-cons car-cons cdr-cons)))))
(defthm fn-pth-pool-okp-implies-pool-shapep
 (implies (and (natp i) (fn-rtc-pool-okp i pool s))
          (fn-rtc-pool-shapep i pool (fn-rtc-config s)))
 :hints (("Goal" :induct (fn-rtc-pool-okp i pool s)
  :expand ((fn-rtc-pool-okp i pool s) (fn-rtc-pool-shapep i pool (fn-rtc-config s)))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-buffer-okp fn-rtc-bufferp fn-rtc-pool-okp fn-rtc-pool-shapep
     fn-rtc-b-gen fn-rtc-b-owner fn-rtc-b-bytes fn-rtc-get nfix natp zp
     car-cons cdr-cons fn-cbor-octet-listp-implies-true-listp)))))
(defthm fn-pth-slots-okp-true-listp
 (implies (fn-rtc-slots-okp i slots) (true-listp slots))
 :hints (("Goal" :induct (fn-rtc-slots-okp i slots)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-slots-okp true-listp car-cons cdr-cons)))))
(defthm fn-pth-invp-implies-shapep
 (implies (fn-pth-invp s) (fn-rtc-shapep s))
 :hints (("Goal" :use ((:instance fn-pth-pool-okp-implies-pool-shapep
     (i 0) (pool (fn-rtc-pool s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-invp fn-rtc-shapep fn-pth-slots-okp-true-listp (:executable-counterpart natp))))))


; From c6a/p15b-I-init-frames.lisp
(defthm fn-pth-arm-opened-pool-and-mstates-frame
 (and (equal (fn-rtc-pool (mv-nth 0 (fn-pth-arm-opened j n s))) (fn-rtc-pool s))
      (equal (fn-rtc-mstates (mv-nth 0 (fn-pth-arm-opened j n s))) (fn-rtc-mstates s)))
 :hints (("Goal" :induct (fn-pth-arm-opened j n s)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-arm-opened fn-rtc-issue-frame fn-hld-mv-nth-0-cons
     car-cons cdr-cons (:executable-counterpart zp) (:executable-counterpart nfix))))))
(defthm fn-pth-i-owner-uses-rearm
 (equal (fn-pth-i-owner-uses (fn-rtc-uses (mv-nth 0 (fn-rtc-rearm s))) m)
        (fn-pth-i-owner-uses (fn-rtc-uses s) m))
 :hints (("Goal" :in-theory (union-theories
  (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-rearm fn-rtc-arm-accept fn-rtc-arm-grant fn-pth-i-owner-uses
     fn-rtc-issue-frame fn-hld-mv-nth-0-cons fn-rtc-get-of-cons
     car-cons cdr-cons (:executable-counterpart zp) (:executable-counterpart nfix)
     (:executable-counterpart equal))))))
(defthm fn-pth-i-owner-uses-arm-opened-one
 (equal (fn-pth-i-owner-uses (fn-rtc-uses (mv-nth 0 (fn-pth-arm-opened 1 1 s))) (fn-ptx-closed))
        (fn-pth-i-owner-uses (fn-rtc-uses s) (fn-ptx-closed)))
 :hints (("Goal" :expand ((fn-pth-arm-opened 1 1 s)
    (:free (j s) (fn-pth-arm-opened j 0 s)))
  :in-theory (union-theories
  (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-arm-opened fn-pth-i-owner-uses fn-rtc-issue-frame
     fn-hld-mv-nth-0-cons fn-rtc-get-of-cons car-cons cdr-cons
     (:executable-counterpart zp) (:executable-counterpart nfix)
     (:executable-counterpart equal) (:executable-counterpart fn-ptx-closed)
     (:executable-counterpart fn-ptx-ph) (:executable-counterpart binary-+)
     (:executable-counterpart fn-ptx-expected))))))
(defthm fn-pth-i-init-local-facts
 (implies (equal (fn-rtc-nstatic cfg) 1)
  (and (equal (fn-rtc-pool (mv-nth 0 (fn-pth-init cfg))) (fn-rtc-free-pool (fn-rtc-nbufs cfg)))
       (equal (fn-rtc-mstate 1 (mv-nth 0 (fn-pth-init cfg))) (fn-ptx-closed))
       (fn-pth-i-owner-uses (fn-rtc-uses (mv-nth 0 (fn-pth-init cfg))) (fn-ptx-closed))))
 :hints (("Goal" :expand ((fn-pth-static-mstates 1 1)
    (:free (j) (fn-pth-static-mstates j 0)))
  :in-theory (union-theories
  (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-init fn-pth-static-mstates fn-pthm-static-init
     fn-pth-arm-opened-pool-and-mstates-frame fn-rtc-rearm-frame fn-pth-rearm-pool-and-mstates-frame
     fn-pth-i-owner-uses-rearm fn-pth-i-owner-uses-arm-opened-one
     fn-rtc-make-accessors fn-rtc-mstate fn-rtc-get-of-cons fn-pth-i-owner-uses
     binary-append fn-hld-mv-nth-0-cons car-cons cdr-cons
     (:executable-counterpart zp) (:executable-counterpart nfix)
     (:executable-counterpart equal) (:executable-counterpart binary-+))))))


; From c6a/p15b-I-initial.lisp
(defthm fn-pth-invp-listener-for-initialization
 (implies (fn-pth-invp s) (equal (fn-rtc-slot 0 s) *fn-rtc-listener*))
 :hints (("Goal" :cases ((consp (fn-rtc-slots s)))
  :expand ((fn-rtc-slots-okp 0 (fn-rtc-slots s)) (len (fn-rtc-slots s))
           (fn-rtc-get 0 (fn-rtc-slots s)))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-invp fn-rtc-slot fn-rtc-configp fn-rtc-nslots nfix natp
     (:executable-counterpart zp) (:executable-counterpart nfix)
     (:executable-counterpart natp) (:executable-counterpart len)
     (:executable-counterpart equal))))))
(defthm fn-pth-invp-owner-for-initialization
 (implies (and (fn-pth-invp s) (equal (fn-rtc-nstatic (fn-rtc-config s)) 1))
          (equal (fn-rtc-slot 1 s) '(1 :live 0)))
 :hints (("Goal" :use ((:instance fn-rtc-statics-okp-get
   (j 1) (k 1) (n 1) (slots (fn-rtc-slots s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-invp fn-rtc-slot (:executable-counterpart nfix)
     (:executable-counterpart natp) (:executable-counterpart binary-+)
     (:executable-counterpart <) (:executable-counterpart equal))))))
(defthm fn-pth-i-initial-invariant
 (let ((cfg (fn-hl-rtc-config profile mcfg q *fn-pth-nstatic* 0 0 *fn-pth-qs* *fn-pth-cs*)))
  (implies (fn-rtc-st-cfg-okp cfg) (fn-pth-i (mv-nth 0 (fn-pth-init cfg)))))
 :hints (("Goal"
  :use ((:instance fn-pth-init-establishes-invp
          (cfg (fn-hl-rtc-config profile mcfg q *fn-pth-nstatic* 0 0 *fn-pth-qs* *fn-pth-cs*)))
        (:instance fn-pth-host-config-holds-the-workspace (h 0))
        fn-hl-article-capl-is-a-lease)
  :in-theory (union-theories
   (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i fn-pth-invp fn-pth-init-establishes-invp
     fn-pth-invp-implies-shapep fn-pth-init-config-frame
     fn-pth-i-init-local-facts fn-pth-i-closed-post-state fn-pth-i-pool-free
     fn-pth-i-uses-from-uses-okp fn-pth-init-inc-table
     fn-pth-invp-listener-for-initialization fn-pth-invp-owner-for-initialization
     fn-hl-rtc-config fn-rtc-qfixed fn-rtc-nstatic fn-rtc-nstatic-home
     fn-rtc-capf-static fn-rtc-capl fn-rtc-get-of-cons nfix natp posp
     default-+-1 default-+-2 default-*-1 default-*-2
     car-cons cdr-cons (:executable-counterpart nfix)
     (:executable-counterpart zp) (:executable-counterpart natp)
     (:executable-counterpart posp) (:executable-counterpart equal))))))


; From c6a/p15b-I-owner-request-fields.lisp
(defthm fn-pth-i-owner-uses-request-frame
 (implies (not (equal id 1))
  (equal (fn-pth-i-owner-uses (fn-rtc-uses (mv-nth 0 (fn-rtc-request r id inc s))) m)
         (fn-pth-i-owner-uses (fn-rtc-uses s) m)))
 :hints (("Goal" :in-theory (union-theories
  (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release
     fn-rtc-req-close fn-rtc-req-cancel fn-rtc-req-submit
     fn-rtc-with-accessors fn-rtc-issue-frame fn-pth-i-owner-uses
     fn-rtc-get-of-cons fn-hld-mv-nth-0-cons car-cons cdr-cons
     (:executable-counterpart zp) (:executable-counterpart nfix)
     (:executable-counterpart equal))))))
(defthm fn-pth-i-owner-kind-out-request-frame
 (implies (not (equal id 1))
  (equal (fn-rtc-kind-out-p kind 1 1 (fn-rtc-uses (mv-nth 0 (fn-rtc-request r id inc s))))
         (fn-rtc-kind-out-p kind 1 1 (fn-rtc-uses s))))
 :hints (("Goal" :in-theory (union-theories
  (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release
     fn-rtc-req-close fn-rtc-req-cancel fn-rtc-req-submit
     fn-rtc-with-accessors fn-rtc-issue-frame fn-rtc-kind-out-p
     fn-rtc-get-of-cons fn-hld-mv-nth-0-cons car-cons cdr-cons
     (:executable-counterpart zp) (:executable-counterpart nfix)
     (:executable-counterpart equal))))))
(defthm fn-pth-i-visible-buffer-request
 (implies (and (not (equal id 1)) (fn-pth-i-visible-buffer h s leasedp))
          (fn-pth-i-visible-buffer h (mv-nth 0 (fn-rtc-request r id inc s)) leasedp))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-visible-buffer fn-pth-request-visible-buffer-frame
     fn-rtc-view-own-p fn-rtc-request-config-frame)))))
(defthm fn-pth-i-post-request
 (implies (and (not (equal id 1)) (fn-pth-i-post p s leasedp))
          (fn-pth-i-post p (mv-nth 0 (fn-rtc-request r id inc s)) leasedp))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-post fn-pth-i-visible-buffer-request fn-rtc-request-config-frame)))))
(defthm fn-pth-i-queue-request
 (implies (and (not (equal id 1)) (fn-pth-i-queue ps s used))
          (fn-pth-i-queue ps (mv-nth 0 (fn-rtc-request r id inc s)) used))
 :hints (("Goal" :induct (fn-pth-i-queue ps s used)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-queue fn-pth-i-post-request fn-pth-i-post fn-pth-i-visible-buffer
     fn-rtc-request-config-frame fn-pth-request-visible-buffer-frame fn-rtc-view-own-p)))))


; From c6a/p15b-I-post-state-request.lisp
(defthm fn-pth-i-post-state-request
 (implies (and (not (equal id 1)) (fn-pth-i-post-state m s))
          (fn-pth-i-post-state m (mv-nth 0 (fn-rtc-request r id inc s))))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-post-state fn-pth-i-owner-uses-request-frame
     fn-pth-i-owner-kind-out-request-frame fn-pth-i-queue-request
     fn-pth-i-post-request fn-pth-i-visible-buffer-request
     fn-pth-i-post fn-pth-i-visible-buffer fn-rtc-view-own-p
     fn-pth-request-visible-buffer-frame fn-rtc-request-config-frame)))))


; From c6a/p15b-I-owner-requests.lisp
(defthm fn-pth-i-post-state-requests
 (implies (and (not (equal id 1)) (fn-pth-i-post-state m s))
          (fn-pth-i-post-state m (mv-nth 0 (fn-rtc-requests rs id inc s))))
 :hints (("Goal" :induct (fn-rtc-requests rs id inc s)
  :in-theory (union-theories
   (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-requests fn-pth-i-post-state-request fn-hld-mv-nth-0-cons
     car-cons cdr-cons (:executable-counterpart zp) (:executable-counterpart nfix))))))
(defthm fn-pth-i-foreign-requests-preserve-owner-post-state
 (implies (and (not (equal id 1)) (fn-pth-i-post-state (fn-rtc-mstate 1 s) s))
          (let ((s2 (mv-nth 0 (fn-rtc-requests rs id inc s))))
           (fn-pth-i-post-state (fn-rtc-mstate 1 s2) s2)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-post-state-requests fn-rtc-requests-keeps-mstates)))))


; From c6a/p15b-OD-constructors.lisp
(defthm fn-pth-data-okp-append
 (equal (fn-pth-reqs-data-okp (append x y))
        (and (fn-pth-reqs-data-okp x) (fn-pth-reqs-data-okp y)))
 :hints (("Goal" :induct (append x y)
  :in-theory (union-theories (theory 'minimal-theory)
   '(binary-append fn-pth-reqs-data-okp car-cons cdr-cons)))))
(defthm fn-pth-post-view-gen-is-natural
 (natp (fn-ptx-gen h id inc st))
 :rule-classes (:rewrite :type-prescription)
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-ptx-gen fn-rtc-st-v-gen fn-rtc-st$a-v-gen fn-rtc-b-gen nfix natp)))))
(defthm fn-pth-data-okp-write
 (implies (and (natp h) (natp off) (fn-cbor-octet-listp data))
  (fn-pth-req-data-okp (list :write h g off data)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-req-data-okp fn-rtc-get-of-cons car-cons cdr-cons
    (:executable-counterpart zp) (:executable-counterpart nfix)
    (:executable-counterpart equal))))))


; From c6a/p15b-OD-code.lisp
(defthm fn-pth-answer-code-is-octet
 (fn-cbor-octetp (fn-ptx-code o))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-ptx-code fn-cbor-octetp assoc-equal nfix natp car-cons cdr-cons
    (:executable-counterpart equal) (:executable-counterpart nfix)
    (:executable-counterpart <))))))


; From c6a/p15b-OD-constructors.lisp
(defthm fn-pth-data-okp-answer
 (implies (and (fn-rtc-u64p (fn-ptx-cur-fid p)) (posp (fn-ptx-cur-fid p))
               (fn-rtc-u64p (fn-ptx-cur-finc p)))
  (fn-pth-reqs-data-okp (fn-ptx-answer p o id inc st)))
 :hints (("Goal" :use (fn-pth-answer-code-is-octet)
  :in-theory (union-theories (theory 'minimal-theory)
  '(fn-ptx-answer fn-ptx-cur-bp fn-pth-reqs-data-okp fn-pth-req-data-okp
    fn-rtc-get-of-cons fn-rtc-kind-extrap fn-rtc-extrap fn-rtc-handlep
    fn-rtc-h-off fn-rtc-u64p fn-rtc-buffered-kind-p fn-pth-post-view-gen-is-natural
    max nfix natp posp car-cons cdr-cons len true-listp (:type-prescription len)
    (:executable-counterpart member-equal) (:executable-counterpart assoc-equal)
    (:executable-counterpart nfix)
    (:executable-counterpart zp) (:executable-counterpart equal)
    fn-cbor-octet-listp fn-cbor-octetp
    (:executable-counterpart <) (:executable-counterpart expt)
    (:executable-counterpart len) (:executable-counterpart binary-+))))))

; Supporting validator/projection bridge only: full OD still needs reachability -> no refusal.
; The accept-event local control is unreachable-in-composition for static owner 1;
; it accounts only for the generic dispatch projection on malformed states.
(encapsulate ()
(local
 (defthm fn-pth-mv-nth-1-cons
 (equal (mv-nth 1 (cons a (cons b tail))) b)
 :hints (("Goal" :expand ((mv-nth 1 (cons a (cons b tail))) (mv-nth 0 (cons b tail)))
  :in-theory (union-theories (theory 'minimal-theory)
   '(mv-nth car-cons cdr-cons (:executable-counterpart nfix) (:executable-counterpart zp)))))))
(local
 (defthm fn-pth-mv-nth-2-cons
 (equal (mv-nth 2 (cons a (cons b (cons c tail)))) c)
 :hints (("Goal" :expand ((mv-nth 2 (cons a (cons b (cons c tail)))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(mv-nth fn-pth-mv-nth-1-cons car-cons cdr-cons
     (:executable-counterpart nfix) (:executable-counterpart zp)))))))
(local
 (defthm fn-pth-append-nil-with-list-head
 (implies (true-listp x)
  (equal (not (append x y)) (and (not x) (not y))))
 :hints (("Goal" :induct (append x y)
  :in-theory (union-theories (theory 'minimal-theory)
   '(binary-append true-listp car-cons cdr-cons))))))
(local
 (defthm fn-pth-refusal-free-request-data
 (implies (not (mv-nth 2 (fn-rtc-request r id inc s))) (fn-pth-req-data-okp r))
 :rule-classes nil
 :hints (("Goal" :use (fn-pth-request-factors) :in-theory (theory 'minimal-theory)))))
(local
 (defthm fn-pth-append-nonempty-with-list-head
 (implies (true-listp x) (iff (append x y) (or x y)))
 :hints (("Goal" :use (fn-pth-append-nil-with-list-head)
  :in-theory (theory 'minimal-theory)))))
(local
 (defthm fn-pth-request-refusal-factors
 (iff (mv-nth 2 (fn-rtc-request r id inc s))
      (not (and (fn-pth-req-data-okp r) (fn-pth-req-state-okp r id inc s))))
 :hints (("Goal" :use (fn-pth-request-factors) :in-theory (theory 'minimal-theory)))))
(local
 (defthm fn-pth-refusal-free-requests-data
 (implies (not (mv-nth 2 (fn-rtc-requests rs id inc s))) (fn-pth-reqs-data-okp rs))
 :rule-classes nil
 :hints (("Goal" :induct (fn-rtc-requests rs id inc s)
  :in-theory (union-theories
   (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-requests fn-pth-reqs-data-okp fn-pth-mv-nth-2-cons fn-hld-mv-nth-0-cons
     fn-pth-append-nonempty-with-list-head fn-rtc-request-lists fn-pth-request-refusal-factors
     car-cons cdr-cons (:executable-counterpart zp) (:executable-counterpart nfix)))))))
(local
 (defthm fn-pth-accept-event-emits-no-requests
 (implies (and (equal (fn-rtc-get 0 ev) :accept) (equal (fn-rtc-ev-id ev) 1))
          (equal (mv-nth 1 (fn-pth-m-step m ev st q)) nil))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-m-step fn-pthm-step fn-ptx-step fn-ptx-step1
     mv-nth car-cons cdr-cons (:executable-counterpart equal)
     (:executable-counterpart member-equal) (:executable-counterpart nfix)
     (:executable-counterpart zp)))))))
(local
 (defthm fn-pth-unrefused-delivery-requests-data
 (implies (not (mv-nth 2 (fn-pth-deliver s id inc ev q)))
  (fn-pth-reqs-data-okp
   (mv-nth 1 (fn-pth-m-step (fn-rtc-mstate id s) ev
                            (fn-rtc-view-state id inc s) (nfix q)))))
 :hints (("Goal"
  :use (fn-pth-deliver-processes-its-machine-requests-by-definition
        (:instance fn-pth-refusal-free-requests-data
         (rs (mv-nth 1 (fn-pth-m-step (fn-rtc-mstate id s) ev
                                     (fn-rtc-view-state id inc s) (nfix q))))
         (s (fn-rtc-with-mstate id
              (mv-nth 0 (fn-pth-m-step (fn-rtc-mstate id s) ev
                                      (fn-rtc-view-state id inc s) (nfix q))) s))))
  :in-theory (theory 'minimal-theory)))))
(defthm fn-pth-unrefused-owner-requests-data
 (implies (and (mv-nth 0 (fn-pth-owner-delivery s e q))
               (not (mv-nth 2 (fn-pth-step* s e q))))
          (fn-pth-reqs-data-okp (fn-pth-owner-requests s e q)))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories
   (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-step* fn-pth-owner-delivery fn-pth-owner-requests fn-pth-accept-branch
     fn-pth-unrefused-delivery-requests-data fn-pth-mv-nth-1-cons fn-pth-mv-nth-2-cons
     fn-pth-accept-event-emits-no-requests fn-rtc-ev fn-rtc-ev-id fn-rtc-get-of-cons
     (:executable-counterpart fn-pth-reqs-data-okp)
     fn-hld-mv-nth-0-cons car-cons cdr-cons
     (:executable-counterpart zp) (:executable-counterpart nfix)
     (:executable-counterpart equal))))))
)

; Runtime-I buffer and inert request arms only; close/submit and completion preservation still owed.


; From p15b-I-use-compatibility-modular2.lisp
(defthm fn-pth-i-listener-use-handle-is-leased
 (implies (and (fn-pth-i-listener-use u s) (fn-rtc-handlep (fn-rtc-u-hd u)))
          (fn-rtc-leasedp (fn-rtc-h-buf (fn-rtc-u-hd u)) s))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-listener-use fn-rtc-leasedp fn-rtc-get-of-cons
     (:executable-counterpart fn-rtc-get) (:executable-counterpart fn-rtc-handlep)
     (:executable-counterpart equal) (:executable-counterpart member-equal)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))
(defthm fn-pth-i-holders-of-unleased-buffer
 (implies (and (fn-pth-i-uses uses s) (not (fn-rtc-leasedp h s)))
          (equal (fn-rtc-holders h g uses) 0))
 :hints (("Goal" :induct (fn-pth-i-uses uses s)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-uses fn-rtc-holders
     default-+-1 default-+-2 car-cons cdr-cons (:executable-counterpart binary-+)
     (:type-prescription fn-rtc-holders))))
  ("Subgoal *1/1" :use ((:instance fn-rtc-use-okp-lease (u (car uses)))
                         (:instance fn-pth-i-listener-use-handle-is-leased (u (car uses)))))))

; From p15b-I-unleased-update.lisp
(defthm fn-pth-i-listener-use-of-unleased-update
 (implies (and (natp h) (fn-pth-i-listener-use u s) (not (fn-rtc-leasedp h s)))
          (fn-pth-i-listener-use u (fn-rtc-with-buffer h b s)))
 :hints (("Goal" :use (fn-pth-i-listener-use-handle-is-leased)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-listener-use fn-rtc-with-accessors fn-rtc-slot-of-with
     fn-rtc-buffer-of-with fn-rtc-next-op-of-with
     (:type-prescription fn-rtc-h-buf) nfix natp
     (:executable-counterpart equal) (:executable-counterpart member-equal)
     (:executable-counterpart fn-rtc-handlep))))))
(defthm fn-pth-i-uses-of-unleased-update
 (implies (and (natp h) (fn-pth-i-uses uses s) (not (fn-rtc-leasedp h s)))
          (fn-pth-i-uses uses (fn-rtc-with-buffer h b s)))
 :hints (("Goal" :induct (fn-pth-i-uses uses s)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-uses fn-pth-i-listener-use-of-unleased-update
     fn-rtc-use-okp-of-unleased-update)))))
(defthm fn-pth-i-pool-control-frame-of-buffer-update
 (equal (fn-pth-i-pool i pool (fn-rtc-with-buffer h b s))
        (fn-pth-i-pool i pool s))
 :hints (("Goal" :induct (fn-pth-i-pool i pool s)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-pool fn-rtc-with-accessors fn-rtc-slot-of-with)))))

; From p15b-I-physical-shape.lisp
(defthm fn-pth-request-keeps-shapep
 (implies (fn-rtc-shapep s) (fn-rtc-shapep (mv-nth 0 (fn-rtc-request r id inc s))))
 :hints (("Goal" :use ((:instance fn-rtc-request-keeps-st-p (fn-rtc-st s)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-st-p-is-shapep)))))
(defthm fn-pth-with-slot-keeps-shapep
 (implies (fn-rtc-shapep s) (fn-rtc-shapep (fn-rtc-with-slot id slot s)))
 :hints (("Goal" :use ((:instance fn-rtc-st-p-of-with-slot (fn-rtc-st s)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-st-p-is-shapep)))))
(defthm fn-pth-with-mstate-keeps-shapep
 (implies (fn-rtc-shapep s) (fn-rtc-shapep (fn-rtc-with-mstate id m s)))
 :hints (("Goal" :use ((:instance fn-rtc-st-p-of-with-mstate (fn-rtc-st s)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-st-p-is-shapep)))))
(defthm fn-pth-issue-keeps-shapep
 (implies (fn-rtc-shapep s) (fn-rtc-shapep (fn-rtc-issue use s)))
 :hints (("Goal" :use ((:instance fn-rtc-st-p-of-spec-issue (fn-rtc-st s)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-st-p-is-shapep)))))
(defthm fn-pth-grant-one-keeps-shapep
 (implies (fn-rtc-shapep s) (fn-rtc-shapep (mv-nth 0 (fn-rtc-grant-one s))))
 :hints (("Goal" :use ((:instance fn-rtc-x-grant-one-is (fn-rtc-st s)) (:instance fn-rtc-x-grant-one-keeps-st-p (fn-rtc-st s)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-st-p-is-shapep)))))
(defthm fn-pth-requests-keep-shapep
 (implies (fn-rtc-shapep s) (fn-rtc-shapep (mv-nth 0 (fn-rtc-requests rs id inc s))))
 :hints (("Goal" :induct (fn-rtc-requests rs id inc s)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-requests fn-pth-request-keeps-shapep fn-hld-mv-nth-0-cons car-cons cdr-cons)))))

; From p15b-I-factoring.lisp
(make-event
 (let* ((ev (get-event 'fn-pth-i-pool (w state)))
        (body (car (last ev))) (branch (caddr body))
        (bindings (cadr branch)) (conjuncts (caddr branch)))
  (if (and (eq (car body) 'if) (eq (car branch) 'let*)
           (equal (car bindings) '(b (car pool)))
           (eq (car conjuncts) 'and)
           (equal (car (last conjuncts))
                  '(fn-pth-i-pool (+ 1 (nfix h)) (cdr pool) s)))
   (value `(defun fn-pth-i-buffer-state-okp (h b s)
     (declare (xargs :guard t :verify-guards nil))
     (let* ,(cdr bindings) ,(butlast conjuncts 1))))
   (er soft 'fn-pth-i-buffer-state-okp "I pool loop shape changed."))))
(defthm fn-pth-i-pool-unfolds
 (equal (fn-pth-i-pool h pool s)
  (if (consp pool)
   (and (fn-pth-i-buffer-state-okp h (car pool) s)
        (fn-pth-i-pool (+ 1 (nfix h)) (cdr pool) s))
   (null pool)))
 :rule-classes :definition
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-pool fn-pth-i-buffer-state-okp)))))
(in-theory (disable fn-pth-i-pool-unfolds))
(make-event
 (let* ((ev (get-event 'fn-pth-i (w state))) (body (car (last ev)))
        (clauses (caddr body)))
  (if (and (member-eq (car body) '(let let*)) (eq (car clauses) 'and)
           (equal (car (last clauses)) '(fn-pth-i-post-state (fn-rtc-mstate 1 s) s)))
   (value `(defun fn-pth-i-runtime (s)
     (declare (xargs :guard t :verify-guards nil))
     (,(car body) ,(cadr body) ,(butlast clauses 1))))
   (er soft 'fn-pth-i-runtime "I conjunction shape changed."))))
(defthm fn-pth-i-runtime-and-post-state-by-definition
 (equal (fn-pth-i s)
        (and (fn-pth-i-runtime s) (fn-pth-i-post-state (fn-rtc-mstate 1 s) s)))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i fn-pth-i-runtime)))))

; From p15b-I-pool-index.lisp
(defthm fn-pth-i-pool-get
 (implies (and (natp i) (natp k) (< k (len pool)) (fn-pth-i-pool i pool s))
          (fn-pth-i-buffer-state-okp (+ i k) (fn-rtc-get k pool) s))
 :hints (("Goal" :induct (fn-rtc-index-induct k i pool)
  :in-theory (union-theories (theory 'minimal-theory)
   '((:induction fn-rtc-index-induct) fn-pth-i-pool-unfolds fn-rtc-get
     nfix natp zp len (:type-prescription len) car-cons cdr-cons
     default-+-1 default-+-2 associativity-of-+ commutativity-of-+ commutativity-2-of-+ fold-consts-in-+ unicity-of-0 fix
     (:executable-counterpart zp) (:executable-counterpart nfix))))))
(defthm fn-pth-i-pool-set
 (implies (and (natp i) (natp k) (fn-pth-i-pool i pool s)
               (fn-pth-i-buffer-state-okp (+ i k) b s))
          (fn-pth-i-pool i (fn-rtc-set k b pool) s))
 :hints (("Goal" :induct (fn-rtc-index-induct k i pool)
  :expand ((:with fn-pth-i-pool-unfolds (fn-pth-i-pool i pool s))
           (:with fn-pth-i-pool-unfolds (fn-pth-i-pool i (cons b (cdr pool)) s)))
  :in-theory (union-theories (theory 'minimal-theory)
   '((:induction fn-rtc-index-induct) fn-pth-i-pool-unfolds fn-rtc-set
     nfix natp zp car-cons cdr-cons
     default-+-1 default-+-2 associativity-of-+ commutativity-of-+ commutativity-2-of-+ fold-consts-in-+ unicity-of-0 fix
     (:executable-counterpart zp) (:executable-counterpart nfix))))))
(defthm fn-pth-i-pool-with-buffer
 (implies (and (natp h) (fn-pth-i-pool 0 (fn-rtc-pool s) s)
               (fn-pth-i-buffer-state-okp h b s))
          (fn-pth-i-pool 0 (fn-rtc-pool (fn-rtc-with-buffer h b s))
                         (fn-rtc-with-buffer h b s)))
 :hints (("Goal" :use ((:instance fn-pth-i-pool-set (i 0) (k h) (pool (fn-rtc-pool s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-pool-control-frame-of-buffer-update fn-rtc-with-accessors
     nfix natp default-+-1 default-+-2 unicity-of-0 fix (:executable-counterpart binary-+))))))

; From p15b-I-runtime-buffer-update.lisp
(defthm fn-pth-i-runtime-of-unleased-buffer-update
 (implies (and (fn-pth-i-runtime s) (natp h) (not (fn-rtc-leasedp h s))
               (fn-pth-i-buffer-state-okp h b s)
               (fn-rtc-shapep (fn-rtc-with-buffer h b s)))
          (fn-pth-i-runtime (fn-rtc-with-buffer h b s)))
 :hints (("Goal" :use (fn-pth-i-pool-with-buffer)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-rtc-with-accessors fn-rtc-slot-of-with
     fn-pth-i-pool-with-buffer fn-pth-i-uses-of-unleased-update)))))
(defthm fn-pth-i-runtime-buffer-metadata
 (implies (and (fn-pth-i-runtime s) (natp h)
               (< h (fn-rtc-nbufs (fn-rtc-config s))))
          (fn-pth-i-buffer-state-okp h (fn-rtc-buffer h s) s))
 :hints (("Goal" :use ((:instance fn-pth-i-pool-get
    (i 0) (k h) (pool (fn-rtc-pool s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-rtc-shapep fn-rtc-buffer nfix natp
     default-+-1 default-+-2 unicity-of-0 fix (:executable-counterpart binary-+))))))
(defthm fn-pth-i-shaped-live-slot-in-range
 (implies (and (fn-rtc-shapep s) (natp id)
               (member-eq (fn-rtc-s-status (fn-rtc-slot id s)) '(:live :closing)))
          (< id (fn-rtc-nslots (fn-rtc-config s))))
 :hints (("Goal" :use ((:instance fn-rtc-get-out-of-range (i id) (l (fn-rtc-slots s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-shapep fn-rtc-slot fn-rtc-s-status nfix natp
     (:executable-counterpart fn-rtc-get) (:executable-counterpart member-equal))))))

; From p15b-I-workspace-metadata.lisp
(defthm fn-pth-i-runtime-live-caller-is-u64
 (implies (and (fn-pth-i-runtime s) (posp id) (fn-rtc-live-p id inc s))
          (and (fn-rtc-u64p id) (fn-rtc-u64p inc)))
 :hints (("Goal" :use ((:instance fn-pth-i-shaped-live-slot-in-range)
                         (:instance fn-pth-slot-inc-is-u64-from-inc-table (j id)))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-rtc-live-p fn-rtc-u64p fn-rtc-st-cfg-okp natp posp
     (:executable-counterpart expt) (:executable-counterpart member-equal))))))
(defthm fn-pth-i-free-buffer-metadata
 (fn-pth-i-buffer-state-okp h (list g '(:free) bytes) s)
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-buffer-state-okp fn-pth-i-buffer-ownerp fn-rtc-buffer-accessors
     fn-rtc-get-of-cons car-cons cdr-cons (:executable-counterpart fn-rtc-get)
     (:executable-counterpart equal) (:executable-counterpart len)
     (:executable-counterpart true-listp) (:executable-counterpart nfix)
     (:executable-counterpart zp))))))
(defthm fn-pth-i-workspace-buffer-metadata-frame
 (implies (equal (fn-rtc-b-owner b0) (list :workspace id inc))
  (equal (fn-pth-i-buffer-state-okp h (list g (list :workspace id inc) bytes) s)
         (fn-pth-i-buffer-state-okp h b0 s)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-buffer-state-okp fn-rtc-buffer-accessors fn-rtc-get-of-cons
     car-cons cdr-cons (:executable-counterpart fn-rtc-get)
     (:executable-counterpart equal) (:executable-counterpart nfix)
     (:executable-counterpart zp))))))
(defthm fn-pth-i-live-workspace-buffer-metadata
 (implies (and (fn-pth-i-runtime s) (posp id) (fn-rtc-live-p id inc s))
          (fn-pth-i-buffer-state-okp h (list g (list :workspace id inc) bytes) s))
 :hints (("Goal" :use (fn-pth-i-runtime-live-caller-is-u64
                         fn-pth-i-shaped-live-slot-in-range)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-pth-i-buffer-state-okp fn-pth-i-buffer-ownerp
     fn-rtc-live-p fn-rtc-u64p posp natp len true-listp fn-rtc-buffer-accessors fn-rtc-get-of-cons
     car-cons cdr-cons (:executable-counterpart fn-rtc-get)
     (:executable-counterpart equal) (:executable-counterpart member-equal)
     (:executable-counterpart len) (:executable-counterpart true-listp)
     (:executable-counterpart nfix) (:executable-counterpart zp)
     (:executable-counterpart binary-+))))))

; From p15b-I-acquire.lisp
(defthm fn-pth-i-runtime-shape-by-definition
 (implies (fn-pth-i-runtime s) (fn-rtc-shapep s))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime)))))
(defthm fn-pth-i-runtime-request-acquire
 (implies (and (fn-pth-i-runtime s) (equal (fn-rtc-get 0 r) :acquire))
          (fn-pth-i-runtime (mv-nth 0 (fn-rtc-request r id inc s))))
 :hints (("Goal" :use (fn-pth-request-keeps-shapep)
  :in-theory (union-theories
   (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-request fn-rtc-req-acquire fn-pth-i-runtime-shape-by-definition
     fn-pth-i-runtime-of-unleased-buffer-update fn-pth-i-live-workspace-buffer-metadata
     fn-rtc-leasedp fn-rtc-get-of-cons fn-hld-mv-nth-0-cons car-cons cdr-cons
     (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
     (:executable-counterpart member-equal) (:executable-counterpart nfix)
     (:executable-counterpart zp))))))

; From p15b-I-owner-fields.lisp
(defthm fn-pth-owner-equality-fields-by-definition
 (implies (equal o (list* tag id inc tail))
  (and (equal (fn-rtc-get 0 o) tag) (equal (fn-rtc-get 1 o) id)
       (equal (fn-rtc-get 2 o) inc)))
 :rule-classes :forward-chaining
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-rtc-get-of-cons car-cons cdr-cons (:executable-counterpart nfix)
    (:executable-counterpart zp))))))

; From p15b-I-write-release.lisp
(defthm fn-pth-i-runtime-request-write
 (implies (and (fn-pth-i-runtime s) (equal (fn-rtc-get 0 r) :write))
          (fn-pth-i-runtime (mv-nth 0 (fn-rtc-request r id inc s))))
 :hints (("Goal"
  :use (fn-pth-request-keeps-shapep
        (:instance fn-pth-i-runtime-buffer-metadata (h (fn-rtc-get 1 r)))
        (:instance fn-pth-i-workspace-buffer-metadata-frame
         (h (fn-rtc-get 1 r)) (g (fn-rtc-get 2 r))
         (b0 (fn-rtc-buffer (fn-rtc-get 1 r) s))
         (bytes (fn-rtc-splice (fn-rtc-b-bytes (fn-rtc-buffer (fn-rtc-get 1 r) s))
                              (fn-rtc-get 3 r) (fn-rtc-get 4 r)))))
  :in-theory (union-theories
   (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-request fn-rtc-req-write fn-pth-i-runtime-shape-by-definition
     fn-pth-i-runtime-of-unleased-buffer-update fn-rtc-leasedp fn-rtc-get-of-cons fn-pth-owner-equality-fields-by-definition
     fn-hld-mv-nth-0-cons car-cons cdr-cons
     (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
     (:executable-counterpart member-equal) (:executable-counterpart nfix)
     (:executable-counterpart zp))))))
(defthm fn-pth-i-runtime-request-release
 (implies (and (fn-pth-i-runtime s) (equal (fn-rtc-get 0 r) :release))
          (fn-pth-i-runtime (mv-nth 0 (fn-rtc-request r id inc s))))
 :hints (("Goal" :use (fn-pth-request-keeps-shapep)
  :in-theory (union-theories
   (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-request fn-rtc-req-release fn-pth-i-runtime-shape-by-definition
     fn-pth-i-runtime-of-unleased-buffer-update fn-pth-i-free-buffer-metadata
     fn-rtc-leasedp fn-rtc-get-of-cons fn-pth-owner-equality-fields-by-definition fn-hld-mv-nth-0-cons car-cons cdr-cons
     (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
     (:executable-counterpart member-equal) (:executable-counterpart nfix)
     (:executable-counterpart zp))))))

; From p15b-I-inert-requests.lisp
(defthm fn-pth-i-runtime-request-cancel
 (implies (and (fn-pth-i-runtime s) (equal (fn-rtc-get 0 r) :cancel))
          (fn-pth-i-runtime (mv-nth 0 (fn-rtc-request r id inc s))))
 :hints (("Goal" :in-theory (union-theories
   (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-request fn-rtc-req-cancel-keeps-state fn-hld-mv-nth-0-cons
     car-cons cdr-cons (:executable-counterpart equal))))))
(defthm fn-pth-i-runtime-request-unknown
 (implies (and (fn-pth-i-runtime s)
               (not (member-eq (fn-rtc-get 0 r) '(:acquire :write :release :close :submit :cancel))))
          (fn-pth-i-runtime (mv-nth 0 (fn-rtc-request r id inc s))))
 :hints (("Goal" :in-theory (union-theories
   (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-request member-equal fn-hld-mv-nth-0-cons car-cons cdr-cons
     (:executable-counterpart equal))))))

; Runtime I close arm and shared unbuffered-issue laws. Submit/completion preservation still owed.

; From p15b-I-pool-structural-induction.lisp
(defun fn-pth-i-pool-index-induct (i pool)
 (declare (xargs :measure (len pool)
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(len o< o-finp o-p natp (:type-prescription len)))))))
 (if (consp pool) (fn-pth-i-pool-index-induct (+ 1 (nfix i)) (cdr pool)) i))

; From p15b-I-closing-slot.lisp
(defthm fn-pth-i-listener-use-slot-frame
 (equal (fn-pth-i-listener-use u (fn-rtc-with-slot id slot s))
        (fn-pth-i-listener-use u s))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-listener-use fn-rtc-with-accessors fn-rtc-buffer-of-with
     fn-rtc-next-op-of-with)))))
(defthm fn-pth-i-uses-of-closing-slot
 (implies (and (natp id) (fn-rtc-live-p id inc s) (fn-pth-i-uses uses s))
          (fn-pth-i-uses uses (fn-rtc-with-slot id (list inc :closing res) s)))
 :hints (("Goal" :induct (fn-pth-i-uses uses s)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-uses fn-pth-i-listener-use-slot-frame fn-rtc-use-okp-of-closing-slot)))))
(defthm fn-pth-i-buffer-state-of-closing-slot
 (implies (and (natp id) (fn-rtc-live-p id inc s) (fn-pth-i-buffer-state-okp h b s))
          (fn-pth-i-buffer-state-okp h b (fn-rtc-with-slot id (list inc :closing res) s)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-buffer-state-okp fn-pth-i-buffer-ownerp fn-rtc-live-p
     fn-rtc-with-accessors fn-rtc-slot-of-with fn-rtc-slot-accessors
     fn-rtc-u64p-implies-natp nfix natp (:type-prescription fn-rtc-s-inc)
     (:executable-counterpart member-equal) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart equal) (:executable-counterpart nfix)
     (:executable-counterpart zp))))))
(defthm fn-pth-i-pool-of-closing-slot
 (implies (and (natp id) (fn-rtc-live-p id inc s) (fn-pth-i-pool i pool s))
          (fn-pth-i-pool i pool (fn-rtc-with-slot id (list inc :closing res) s)))
 :hints (("Goal" :induct (fn-pth-i-pool-index-induct i pool)
  :in-theory (union-theories (theory 'minimal-theory)
   '((:induction fn-pth-i-pool-index-induct) fn-pth-i-pool-unfolds
     fn-pth-i-buffer-state-of-closing-slot)))))

; From p15b-I-unbuffered-issue.lisp
(defthm fn-pth-i-listener-use-of-unbuffered-issue
 (implies (and (fn-pth-i-listener-use u s) (not (fn-rtc-handlep (fn-rtc-u-hd new))))
          (fn-pth-i-listener-use u (fn-rtc-issue new s)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-listener-use fn-rtc-issue-frame fn-rtc-holders-cons-unbuffered
     (:type-prescription fn-rtc-next-op))))))
(defthm fn-pth-i-uses-of-unbuffered-issue
 (implies (and (fn-pth-i-uses uses s) (not (fn-rtc-handlep (fn-rtc-u-hd new))))
          (fn-pth-i-uses uses (fn-rtc-issue new s)))
 :hints (("Goal" :induct (fn-pth-i-uses uses s)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-uses fn-pth-i-listener-use-of-unbuffered-issue
     fn-rtc-use-okp-of-unbuffered-issue)))))
(defthm fn-pth-i-buffer-state-of-issue
 (implies (fn-pth-i-buffer-state-okp h b s)
          (fn-pth-i-buffer-state-okp h b (fn-rtc-issue new s)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-buffer-state-okp fn-rtc-issue-frame fn-rtc-holds-p-cons)))))
(defthm fn-pth-i-pool-of-issue
 (implies (fn-pth-i-pool i pool s) (fn-pth-i-pool i pool (fn-rtc-issue new s)))
 :hints (("Goal" :induct (fn-pth-i-pool-index-induct i pool)
  :in-theory (union-theories (theory 'minimal-theory)
   '((:induction fn-pth-i-pool-index-induct) fn-pth-i-pool-unfolds
     fn-pth-i-buffer-state-of-issue)))))
(defthm fn-pth-i-runtime-of-unbuffered-issue
 (implies (and (fn-pth-i-runtime s) (not (fn-rtc-handlep (fn-rtc-u-hd new)))
               (or (fn-rtc-use-okp new (fn-rtc-issue new s))
                   (fn-pth-i-listener-use new (fn-rtc-issue new s)))
               (or (member-eq (fn-rtc-get 0 new) '(:hand :pool))
                   (not (fn-rtc-kind-out-p (fn-rtc-get 0 new) (fn-rtc-get 1 new)
                                           (fn-rtc-get 2 new) (fn-rtc-uses s))))
               (not (fn-rtc-op-used-p (fn-rtc-get 3 new) (fn-rtc-uses s))))
          (fn-pth-i-runtime (fn-rtc-issue new s)))
 :hints (("Goal" :expand ((fn-pth-i-uses (cons new (fn-rtc-uses s)) (fn-rtc-issue new s)))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-rtc-issue-frame fn-pth-issue-keeps-shapep
     fn-pth-i-uses-of-unbuffered-issue fn-pth-i-pool-of-issue
     car-cons cdr-cons)))))

; From p15b-I-use-control.lisp
(defthm fn-pth-i-use-issued-op
 (implies (or (fn-rtc-use-okp u s) (fn-pth-i-listener-use u s))
          (and (natp (fn-rtc-get 3 u)) (< (fn-rtc-get 3 u) (fn-rtc-next-op s))))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-use-okp fn-rtc-usep fn-pth-i-listener-use nfix natp
     (:executable-counterpart member-equal) (:executable-counterpart fn-rtc-handlep))))))
(defthm fn-pth-i-op-not-used-above-next
 (implies (and (fn-pth-i-uses uses s) (natp op) (<= (fn-rtc-next-op s) op))
          (not (fn-rtc-op-used-p op uses)))
 :hints (("Goal" :induct (fn-pth-i-uses uses s)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-uses fn-rtc-op-used-p natp nfix)))
  ("Subgoal *1/1" :use ((:instance fn-pth-i-use-issued-op (u (car uses)))))))
(defthm fn-pth-i-close-use-status
 (implies (and (or (fn-rtc-use-okp u s) (fn-pth-i-listener-use u s))
               (equal (fn-rtc-get 0 u) :close))
          (equal (fn-rtc-s-status (fn-rtc-slot (nfix (fn-rtc-get 1 u)) s)) :closing))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-use-okp fn-pth-i-listener-use (:executable-counterpart member-equal)
     (:executable-counterpart equal))))))
(defthm fn-pth-i-live-slot-has-no-close
 (implies (and (natp id) (fn-rtc-live-p id inc s) (fn-pth-i-uses uses s))
          (not (fn-rtc-kind-out-p :close id inc uses)))
 :hints (("Goal" :induct (fn-pth-i-uses uses s)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-uses fn-rtc-kind-out-p fn-rtc-live-p nfix natp)))
  ("Subgoal *1/1" :use ((:instance fn-pth-i-close-use-status (u (car uses)))))))

; From p15b-I-close-runtime.lisp
(defthm fn-pth-i-runtime-slot-facts
 (implies (and (fn-pth-i-runtime s) (natp id) (< id (fn-rtc-nslots (fn-rtc-config s))))
  (and (fn-rtc-slotp (fn-rtc-slot id s))
       (if (equal id 0) (equal (fn-rtc-slot id s) *fn-rtc-listener*)
        (iff (null (fn-rtc-s-res (fn-rtc-slot id s)))
             (equal (fn-rtc-s-status (fn-rtc-slot id s)) :free)))))
 :hints (("Goal" :use ((:instance fn-rtc-slots-okp-get (i 0) (k id) (slots (fn-rtc-slots s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-rtc-shapep fn-rtc-slot nfix natp unicity-of-0 fix
     (:executable-counterpart natp) (:executable-counterpart binary-+))))))
(defthm fn-pth-i-closing-slot-record
 (implies (and (fn-pth-i-runtime s) (posp id) (fn-rtc-live-p id inc s))
  (and (fn-rtc-slotp (list inc :closing (fn-rtc-s-res (fn-rtc-slot id s))))
       (not (null (fn-rtc-s-res (fn-rtc-slot id s))))))
 :hints (("Goal" :use (fn-pth-i-runtime-slot-facts fn-pth-i-runtime-live-caller-is-u64
                       fn-pth-i-shaped-live-slot-in-range)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-rtc-live-p fn-rtc-slotp fn-rtc-s-res fn-rtc-get-of-cons
     fn-rtc-u64p natp posp len true-listp car-cons cdr-cons
     (:executable-counterpart member-equal) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart equal) (:executable-counterpart nfix)
     (:executable-counterpart zp) (:executable-counterpart binary-+))))))
(defthm fn-pth-i-runtime-of-closing-dynamic-slot
 (implies (and (fn-pth-i-runtime s) (natp id) (fn-rtc-live-p id inc s)
               (< (fn-rtc-nstatic (fn-rtc-config s)) id))
          (fn-pth-i-runtime
           (fn-rtc-with-slot id (list inc :closing (fn-rtc-s-res (fn-rtc-slot id s))) s)))
 :hints (("Goal"
  :use (fn-pth-i-closing-slot-record fn-pth-i-runtime-live-caller-is-u64
        (:instance fn-rtc-slots-okp-set (i 0) (k id) (slots (fn-rtc-slots s))
         (slot (list inc :closing (fn-rtc-s-res (fn-rtc-slot id s))))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-pth-with-slot-keeps-shapep fn-rtc-with-accessors
     fn-rtc-slot-of-with fn-rtc-slot-accessors fn-pth-i-pool-of-closing-slot
     fn-pth-i-uses-of-closing-slot fn-pth-inc-tablep-set fn-pth-inc-tablep-with-slot
     fn-pth-slots-okp-implies-inc-table
     fn-rtc-u64p-implies-natp nfix natp posp unicity-of-0 fix
     (:executable-counterpart natp) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart equal) (:executable-counterpart nfix)
     (:executable-counterpart zp) (:executable-counterpart binary-+))))))

; From p15b-I-fresh-close.lisp
(defthm fn-pth-i-fresh-close-use-okp
 (implies (and (fn-pth-i-runtime s) (posp id) (fn-rtc-live-p id inc s))
  (fn-rtc-use-okp (list :close id inc (fn-rtc-next-op s) nil)
   (fn-rtc-issue (list :close id inc (fn-rtc-next-op s) nil)
    (fn-rtc-with-slot id (list inc :closing (fn-rtc-s-res (fn-rtc-slot id s))) s))))
 :hints (("Goal"
  :use (fn-pth-i-runtime-live-caller-is-u64 fn-pth-i-shaped-live-slot-in-range
        (:instance fn-rtc-fresh-unbuffered-use-okp (kind :close)
         (s (fn-rtc-with-slot id (list inc :closing (fn-rtc-s-res (fn-rtc-slot id s))) s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-rtc-shapep fn-rtc-live-p fn-rtc-current-p
     fn-rtc-slot-of-with fn-rtc-slot-accessors fn-rtc-with-accessors fn-rtc-next-op-of-with
     fn-rtc-u64p natp posp nfix
     (:executable-counterpart member-equal) (:executable-counterpart equal)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))

; From p15b-I-close-request.lisp
(defthm fn-pth-i-runtime-control-by-definition
 (implies (fn-pth-i-runtime s)
          (and (equal (fn-rtc-nstatic (fn-rtc-config s)) *fn-pth-nstatic*)
               (fn-pth-i-uses (fn-rtc-uses s) s)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pth-i-runtime)))))
(defthm fn-pth-i-runtime-request-close
 (implies (and (fn-pth-i-runtime s) (equal (fn-rtc-get 0 r) :close))
          (fn-pth-i-runtime (mv-nth 0 (fn-rtc-request r id inc s))))
 :hints (("Goal"
  :use ((:instance fn-pth-i-live-slot-has-no-close (uses (fn-rtc-uses s)))
        (:instance fn-pth-i-op-not-used-above-next (uses (fn-rtc-uses s))
         (op (fn-rtc-next-op s))))
  :in-theory (union-theories
   (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-request fn-rtc-req-close fn-pth-i-runtime-control-by-definition
     fn-pth-i-runtime-of-closing-dynamic-slot fn-pth-i-runtime-of-unbuffered-issue
     fn-pth-i-fresh-close-use-okp fn-rtc-with-accessors fn-rtc-next-op-of-with
     fn-rtc-u-hd fn-rtc-get-of-cons fn-hld-mv-nth-0-cons
     (:type-prescription fn-rtc-next-op) nfix natp posp car-cons cdr-cons
     (:executable-counterpart fn-rtc-get) (:executable-counterpart fn-rtc-handlep)
     (:executable-counterpart member-equal) (:executable-counterpart equal)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))

(in-package "ACL2")

; Runtime I: all raw requests, including listener/alias and buffered submit cases.

; From p15b-I-listener-unbuffered.lisp

(defthm fn-pth-i-runtime-listener-by-definition
 (implies (fn-pth-i-runtime s) (equal (fn-rtc-slot 0 s) *fn-rtc-listener*))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pth-i-runtime)))))

(defthm fn-pth-i-runtime-listener-live-inc
 (implies (and (fn-pth-i-runtime s) (equal (nfix id) 0) (fn-rtc-live-p id inc s))
          (equal inc 0))
 :rule-classes nil
 :hints (("Goal" :cases ((natp id))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime-listener-by-definition fn-rtc-live-p fn-rtc-slot-of-non-natp
     fn-rtc-slot-accessors nfix natp (:executable-counterpart fn-rtc-s-inc)
     (:executable-counterpart nfix) (:executable-counterpart equal))))))

(defthm fn-pth-i-fresh-listener-unbuffered-use
 (implies (and (equal (nfix id) 0) (member-eq kind '(:wait :fsync :timer :extend)))
  (fn-pth-i-listener-use (list kind id 0 (fn-rtc-next-op s) nil)
                       (fn-rtc-issue (list kind id 0 (fn-rtc-next-op s) nil) s)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-listener-use fn-rtc-issue-frame fn-rtc-u-hd fn-rtc-get-of-cons
     len true-listp natp member-equal fn-rtc-buffered-kind-p
     (:type-prescription fn-rtc-next-op) car-cons cdr-cons
     (:executable-counterpart equal) (:executable-counterpart len)
     (:executable-counterpart member-equal) (:executable-counterpart binary-+)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))

; From p15b-I-positive-unbuffered.lisp

(defthm fn-pth-i-fresh-wait-use-okp
 (implies (and (fn-pth-i-runtime s) (posp id) (fn-rtc-live-p id inc s))
  (fn-rtc-use-okp (list :wait id inc (fn-rtc-next-op s) nil)
                 (fn-rtc-issue (list :wait id inc (fn-rtc-next-op s) nil) s)))
 :hints (("Goal" :use (fn-pth-i-runtime-live-caller-is-u64 fn-pth-i-shaped-live-slot-in-range)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-rtc-use-okp fn-rtc-usep fn-rtc-live-p fn-rtc-current-p
     fn-rtc-issue-frame fn-rtc-get-of-cons fn-rtc-u-hd fn-rtc-u64p natp posp nfix
     len true-listp car-cons cdr-cons (:type-prescription fn-rtc-next-op)
     (:executable-counterpart fn-rtc-handlep) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart member-equal) (:executable-counterpart equal)
     (:executable-counterpart nfix) (:executable-counterpart zp)
     (:executable-counterpart binary-+))))))

(defthm fn-pth-i-fresh-positive-unbuffered-use-okp
 (implies (and (fn-pth-i-runtime s) (posp id) (fn-rtc-live-p id inc s)
               (member-eq kind '(:wait :fsync :timer :extend)))
  (fn-rtc-use-okp (list kind id inc (fn-rtc-next-op s) nil)
                 (fn-rtc-issue (list kind id inc (fn-rtc-next-op s) nil) s)))
 :hints (("Goal" :cases ((equal kind :wait))
  :use (fn-pth-i-fresh-wait-use-okp fn-pth-i-runtime-live-caller-is-u64
        fn-pth-i-shaped-live-slot-in-range fn-rtc-fresh-unbuffered-use-okp)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-rtc-current-p fn-rtc-live-p fn-rtc-u64p member-equal
     natp posp nfix (:executable-counterpart member-equal) (:executable-counterpart equal))))))

; From p15b-I-unbuffered-submit.lisp

(defthm fn-pth-i-fresh-unbuffered-use
 (implies (and (fn-pth-i-runtime s) (fn-rtc-live-p id inc s)
               (member-eq kind '(:wait :fsync :timer :extend)))
  (or (fn-rtc-use-okp (list kind id inc (fn-rtc-next-op s) nil)
                      (fn-rtc-issue (list kind id inc (fn-rtc-next-op s) nil) s))
      (fn-pth-i-listener-use (list kind id inc (fn-rtc-next-op s) nil)
                      (fn-rtc-issue (list kind id inc (fn-rtc-next-op s) nil) s))))
 :rule-classes nil
 :hints (("Goal" :cases ((posp id)) :use (fn-pth-i-runtime-listener-live-inc)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-fresh-positive-unbuffered-use-okp fn-pth-i-fresh-listener-unbuffered-use
     nfix natp posp (:executable-counterpart equal) (:executable-counterpart nfix))))))

(defthm fn-pth-i-unbuffered-machine-kind-properties
 (implies (and (member-eq kind *fn-rtc-machine-kinds*) (not (fn-rtc-buffered-kind-p kind)))
  (and (member-eq kind '(:wait :fsync :timer :extend))
       (not (equal kind :hand)) (not (equal kind :pool))))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-buffered-kind-p member-equal (:executable-counterpart equal))))))

(defthm fn-pth-i-runtime-request-submit-unbuffered
 (implies (and (fn-pth-i-runtime s) (equal (fn-rtc-get 0 r) :submit)
               (or (equal (fn-rtc-get 1 r) :pool)
                   (not (fn-rtc-buffered-kind-p (fn-rtc-get 1 r)))))
          (fn-pth-i-runtime (mv-nth 0 (fn-rtc-request r id inc s))))
 :hints (("Goal"
  :use ((:instance fn-pth-i-fresh-unbuffered-use (kind :wait))
        (:instance fn-pth-i-fresh-unbuffered-use (kind (fn-rtc-get 1 r)))
        (:instance fn-pth-i-unbuffered-machine-kind-properties (kind (fn-rtc-get 1 r)))
        (:instance fn-pth-i-op-not-used-above-next (uses (fn-rtc-uses s))
         (op (fn-rtc-next-op s))))
  :in-theory (union-theories
   (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-request fn-rtc-req-submit fn-pth-i-runtime-control-by-definition
     fn-pth-i-runtime-of-unbuffered-issue fn-rtc-u-hd fn-rtc-get-of-cons
     fn-hld-mv-nth-0-cons car-cons cdr-cons (:type-prescription fn-rtc-next-op)
     natp nfix (:executable-counterpart fn-rtc-get) (:executable-counterpart fn-rtc-handlep)
     (:executable-counterpart fn-rtc-buffered-kind-p) (:executable-counterpart member-equal)
     (:executable-counterpart equal) (:executable-counterpart nfix)
     (:executable-counterpart zp))))))

; From p15b-I-compatible-issue.lisp

(defthm fn-pth-i-listener-use-of-compatible-issue
 (implies (and (fn-pth-i-listener-use u s) (fn-rtc-compatible-use-p new u))
          (fn-pth-i-listener-use u (fn-rtc-issue new s)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-listener-use fn-rtc-issue-frame fn-rtc-compatible-use-p fn-rtc-holders-cons
     (:type-prescription fn-rtc-next-op) (:type-prescription fn-rtc-holders)
     (:executable-counterpart member-equal) unicity-of-0 fix)))))

(defthm fn-pth-i-uses-of-compatible-issue
 (implies (and (fn-pth-i-uses uses s) (fn-rtc-compatible-usesp new uses))
          (fn-pth-i-uses uses (fn-rtc-issue new s)))
 :hints (("Goal" :induct (fn-pth-i-uses uses s)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-uses fn-rtc-compatible-usesp fn-rtc-use-okp-of-compatible-issue
     fn-pth-i-listener-use-of-compatible-issue)))))

(defthm fn-pth-i-runtime-of-compatible-issue
 (implies (and (fn-pth-i-runtime s) (fn-rtc-compatible-usesp new (fn-rtc-uses s))
               (or (fn-rtc-use-okp new (fn-rtc-issue new s))
                   (fn-pth-i-listener-use new (fn-rtc-issue new s)))
               (or (member-eq (fn-rtc-get 0 new) '(:hand :pool))
                   (not (fn-rtc-kind-out-p (fn-rtc-get 0 new) (fn-rtc-get 1 new)
                                           (fn-rtc-get 2 new) (fn-rtc-uses s))))
               (not (fn-rtc-op-used-p (fn-rtc-get 3 new) (fn-rtc-uses s))))
          (fn-pth-i-runtime (fn-rtc-issue new s)))
 :hints (("Goal" :expand ((fn-pth-i-uses (cons new (fn-rtc-uses s)) (fn-rtc-issue new s)))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-rtc-issue-frame fn-pth-issue-keeps-shapep
     fn-pth-i-uses-of-compatible-issue fn-pth-i-pool-of-issue
     car-cons cdr-cons)))))

; From p15b-I-buffer-and-issue.lisp

(defthm fn-pth-i-pool-old-table-after-buffer-and-issue
 (implies (fn-pth-i-pool i pool s)
          (fn-pth-i-pool i pool (fn-rtc-issue new (fn-rtc-with-buffer h b s))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-pool-of-issue fn-pth-i-pool-control-frame-of-buffer-update)))))

(defthm fn-pth-i-pool-after-buffer-and-issue
 (let ((s2 (fn-rtc-issue new (fn-rtc-with-buffer h b s))))
  (implies (and (natp h) (fn-pth-i-pool 0 (fn-rtc-pool s) s)
                (fn-pth-i-buffer-state-okp h b s2))
           (fn-pth-i-pool 0 (fn-rtc-pool s2) s2)))
 :hints (("Goal"
  :use ((:instance fn-pth-i-pool-set (i 0) (k h) (pool (fn-rtc-pool s))
         (s (fn-rtc-issue new (fn-rtc-with-buffer h b s)))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-pool-old-table-after-buffer-and-issue fn-rtc-issue-frame fn-rtc-with-accessors
     nfix natp unicity-of-0 fix default-+-1 default-+-2)))))

(defthm fn-pth-i-runtime-of-buffer-and-compatible-issue
 (let ((s2 (fn-rtc-issue new (fn-rtc-with-buffer h b s))))
  (implies (and (fn-pth-i-runtime s) (natp h) (not (fn-rtc-leasedp h s))
                (fn-rtc-compatible-usesp new (fn-rtc-uses s))
                (fn-pth-i-buffer-state-okp h b s2)
                (or (fn-rtc-use-okp new s2) (fn-pth-i-listener-use new s2))
                (or (member-eq (fn-rtc-get 0 new) '(:hand :pool))
                    (not (fn-rtc-kind-out-p (fn-rtc-get 0 new) (fn-rtc-get 1 new)
                                            (fn-rtc-get 2 new) (fn-rtc-uses s))))
                (not (fn-rtc-op-used-p (fn-rtc-get 3 new) (fn-rtc-uses s)))
                (fn-rtc-shapep s2))
           (fn-pth-i-runtime s2)))
 :hints (("Goal" :use (fn-pth-i-pool-after-buffer-and-issue)
  :expand ((fn-pth-i-uses (cons new (fn-rtc-uses s))
             (fn-rtc-issue new (fn-rtc-with-buffer h b s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-rtc-issue-frame fn-rtc-with-accessors fn-rtc-slot-of-with
     fn-pth-i-uses-of-compatible-issue fn-pth-i-uses-of-unleased-update
     car-cons cdr-cons)))))

; From p15b-I-shareable-pool.lisp

(defthm fn-pth-i-listener-compatible-use-from-shareable-pool
 (implies (and (fn-pth-i-listener-use u s)
  (or (not (fn-rtc-handlep (fn-rtc-u-hd new)))
      (not (fn-rtc-leasedp (fn-rtc-h-buf (fn-rtc-u-hd new)) s))
      (and (equal (fn-rtc-get 0 (fn-rtc-b-owner
                    (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd new)) s))) :leased)
           (equal (fn-rtc-get 3 (fn-rtc-b-owner
                    (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd new)) s))) :out))))
  (fn-rtc-compatible-use-p new u))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-listener-use fn-rtc-compatible-use-p fn-rtc-leasedp fn-rtc-buffered-kind-p member-equal
     fn-rtc-get-of-cons (:executable-counterpart fn-rtc-get)
     (:executable-counterpart fn-rtc-handlep) (:executable-counterpart equal)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))

(defthm fn-pth-i-compatible-uses-from-shareable-pool
 (implies (and (fn-pth-i-uses uses s)
  (or (not (fn-rtc-handlep (fn-rtc-u-hd new)))
      (not (fn-rtc-leasedp (fn-rtc-h-buf (fn-rtc-u-hd new)) s))
      (and (equal (fn-rtc-get 0 (fn-rtc-b-owner
                    (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd new)) s))) :leased)
           (equal (fn-rtc-get 3 (fn-rtc-b-owner
                    (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd new)) s))) :out))))
  (fn-rtc-compatible-usesp new uses))
 :hints (("Goal" :induct (fn-pth-i-uses uses s)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-uses fn-rtc-compatible-usesp fn-rtc-compatible-use-from-shareable-pool
     fn-pth-i-listener-compatible-use-from-shareable-pool)))))

; From p15b-I-buffered-submitter.lisp

(defthm fn-pth-i-submitter-has-natural-id
 (implies (and (fn-pth-i-runtime s) (fn-rtc-submit-okp kind hd id inc s))
          (natp id))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-pth-i-runtime-buffer-metadata (h (fn-rtc-h-buf hd))))
  :in-theory (union-theories (theory 'minimal-theory)
   '((:type-prescription fn-rtc-h-buf) fn-rtc-submit-okp fn-pth-i-buffer-state-okp fn-pth-i-buffer-ownerp
     fn-rtc-handlep fn-rtc-get-of-cons fn-pth-owner-equality-fields-by-definition
     car-cons cdr-cons member-equal len true-listp natp
     (:executable-counterpart fn-rtc-get) (:executable-counterpart equal))))))

(defthm fn-pth-i-buffered-submit-positive-new-use-okp
 (implies (and (fn-pth-i-runtime s) (posp id)
                (fn-rtc-live-p id inc s)
                (member-eq kind '(:recv :send :pread :pwrite :bp-send))
                (fn-rtc-submit-okp kind hd id inc s))
           (fn-rtc-use-okp (list kind id inc (fn-rtc-next-op s) hd)
                          (fn-rtc-buffered-submit-state kind hd id inc s)))
 :hints (("Goal" :use (fn-pth-i-runtime-live-caller-is-u64
    fn-pth-i-shaped-live-slot-in-range
    (:instance fn-pth-i-holders-of-unleased-buffer
     (h (fn-rtc-h-buf hd)) (g (fn-rtc-h-gen hd)) (uses (fn-rtc-uses s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-rtc-shapep fn-rtc-buffered-submit-state fn-rtc-submit-okp fn-rtc-use-okp fn-rtc-usep
     fn-rtc-current-p fn-rtc-live-p fn-rtc-issue-frame fn-rtc-with-accessors
     fn-rtc-buffer-of-with fn-rtc-next-op-of-with fn-rtc-slot-of-with fn-rtc-get-of-cons fn-rtc-buffer-accessors
     fn-rtc-u-hd fn-rtc-holders-cons fn-rtc-leasedp fn-pth-i-runtime-control-by-definition
     fn-pth-owner-equality-fields-by-definition
     member-equal natp posp nfix len true-listp car-cons cdr-cons
     default-+-1 default-+-2 unicity-of-0 fix (:type-prescription fn-rtc-next-op)
     (:type-prescription fn-rtc-h-buf) (:type-prescription fn-rtc-h-gen)
     (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
     (:executable-counterpart member-equal) (:executable-counterpart nfix)
     (:executable-counterpart binary-+) (:executable-counterpart zp))))))

(defthm fn-pth-i-buffered-submit-listener-new-use
 (implies (and (fn-pth-i-runtime s) (fn-rtc-live-p 0 inc s)
                (member-eq kind '(:recv :send :pread :pwrite :bp-send))
                (fn-rtc-submit-okp kind hd 0 inc s))
           (fn-pth-i-listener-use (list kind 0 inc (fn-rtc-next-op s) hd)
                          (fn-rtc-buffered-submit-state kind hd 0 inc s)))
 :hints (("Goal" :use ((:instance fn-pth-i-runtime-listener-live-inc (id 0))
    (:instance fn-pth-i-holders-of-unleased-buffer
     (h (fn-rtc-h-buf hd)) (g (fn-rtc-h-gen hd)) (uses (fn-rtc-uses s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-rtc-shapep fn-rtc-buffered-submit-state fn-rtc-submit-okp fn-pth-i-listener-use fn-rtc-buffered-kind-p
     fn-rtc-current-p fn-rtc-live-p fn-rtc-issue-frame fn-rtc-with-accessors
     fn-rtc-buffer-of-with fn-rtc-next-op-of-with fn-rtc-slot-of-with fn-rtc-get-of-cons fn-rtc-buffer-accessors
     fn-rtc-u-hd fn-rtc-holders-cons fn-rtc-leasedp fn-pth-i-runtime-control-by-definition
     fn-pth-owner-equality-fields-by-definition
     member-equal natp posp nfix len true-listp car-cons cdr-cons
     default-+-1 default-+-2 unicity-of-0 fix (:type-prescription fn-rtc-next-op)
     (:type-prescription fn-rtc-h-buf) (:type-prescription fn-rtc-h-gen)
     (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
     (:executable-counterpart member-equal) (:executable-counterpart nfix)
     (:executable-counterpart binary-+) (:executable-counterpart zp))))))

; From p15b-I-buffered-bridge.lisp

(defthm fn-pth-i-live-natural-caller-scalars
 (implies (and (fn-pth-i-runtime s) (natp id) (fn-rtc-live-p id inc s))
          (and (fn-rtc-u64p inc) (< id (fn-rtc-nslots (fn-rtc-config s)))))
 :rule-classes nil
 :hints (("Goal" :cases ((posp id))
  :use (fn-pth-i-runtime-live-caller-is-u64 fn-pth-i-runtime-listener-live-inc
        fn-pth-i-shaped-live-slot-in-range)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-rtc-live-p posp natp nfix (:executable-counterpart fn-rtc-u64p) (:executable-counterpart member-equal)
     (:executable-counterpart fn-rtc-s-inc) (:executable-counterpart fn-rtc-s-status))))))

(defthm fn-pth-i-issued-lease-buffer-metadata
 (implies (and (natp id) (fn-rtc-u64p inc) (< id (fn-rtc-nslots (fn-rtc-config s)))
               (member-eq dir '(:in :out)) (fn-rtc-handlep hd) (equal g (fn-rtc-h-gen hd)))
  (fn-pth-i-buffer-state-okp (fn-rtc-h-buf hd) (list g (list :leased id inc dir) bytes)
   (fn-rtc-issue (list kind id inc op hd) s)))
 :hints (("Goal"
  :expand ((fn-rtc-holds-p (fn-rtc-h-buf hd) (fn-rtc-h-gen hd)
            (cons (list kind id inc op hd) (fn-rtc-uses s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-buffer-state-okp fn-pth-i-buffer-ownerp fn-rtc-issue-frame
     fn-rtc-buffer-accessors fn-rtc-u-hd fn-rtc-get-of-cons car-cons cdr-cons
     len true-listp member-equal nfix natp (:type-prescription fn-rtc-h-gen)
     (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
     (:executable-counterpart binary-+) (:executable-counterpart nfix)
     (:executable-counterpart zp))))))

; From p15b-I-buffered-state.lisp

(defthm fn-pth-i-buffered-submit-new-use
 (implies (and (fn-pth-i-runtime s) (fn-rtc-live-p id inc s)
                (member-eq kind '(:recv :send :pread :pwrite :bp-send))
                (fn-rtc-submit-okp kind hd id inc s))
  (or (fn-rtc-use-okp (list kind id inc (fn-rtc-next-op s) hd)
                     (fn-rtc-buffered-submit-state kind hd id inc s))
      (fn-pth-i-listener-use (list kind id inc (fn-rtc-next-op s) hd)
                     (fn-rtc-buffered-submit-state kind hd id inc s))))
 :rule-classes nil
 :hints (("Goal" :cases ((posp id)) :use (fn-pth-i-submitter-has-natural-id)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-buffered-submit-positive-new-use-okp fn-pth-i-buffered-submit-listener-new-use
     natp posp (:executable-counterpart equal))))))

(defthm fn-pth-i-buffered-submit-new-buffer-metadata
 (let* ((h (fn-rtc-h-buf hd)) (b (fn-rtc-buffer h s))
        (dir (if (member-eq kind *fn-rtc-in-kinds*) :in :out)))
  (implies (and (fn-pth-i-runtime s) (fn-rtc-live-p id inc s)
                (member-eq kind '(:recv :send :pread :pwrite :bp-send))
                (fn-rtc-submit-okp kind hd id inc s))
   (fn-pth-i-buffer-state-okp h
    (list (fn-rtc-b-gen b) (list :leased id inc dir) (fn-rtc-b-bytes b))
    (fn-rtc-buffered-submit-state kind hd id inc s))))
 :hints (("Goal" :use (fn-pth-i-submitter-has-natural-id fn-pth-i-live-natural-caller-scalars)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-buffered-submit-state fn-rtc-submit-okp fn-pth-i-issued-lease-buffer-metadata
     fn-pth-owner-equality-fields-by-definition fn-rtc-get-of-cons
     (:executable-counterpart fn-rtc-get) (:executable-counterpart nfix) (:executable-counterpart zp)
     fn-rtc-with-accessors fn-rtc-next-op-of-with member-equal
     (:executable-counterpart member-equal) (:executable-counterpart equal))))))

; From p15b-I-buffered-runtime.lisp

(defthm fn-pth-i-buffered-submit-compatible
 (implies (and (fn-pth-i-runtime s)
               (member-eq kind '(:recv :send :pread :pwrite :bp-send))
               (fn-rtc-submit-okp kind hd id inc s))
  (fn-rtc-compatible-usesp (list kind id inc (fn-rtc-next-op s) hd) (fn-rtc-uses s)))
 :hints (("Goal" :use ((:instance fn-pth-i-compatible-uses-from-shareable-pool
   (uses (fn-rtc-uses s)) (new (list kind id inc (fn-rtc-next-op s) hd))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime-control-by-definition fn-rtc-submit-okp fn-rtc-leasedp
     fn-rtc-u-hd fn-rtc-get-of-cons fn-pth-owner-equality-fields-by-definition
     member-equal car-cons cdr-cons (:executable-counterpart fn-rtc-get)
     (:executable-counterpart equal) (:executable-counterpart nfix)
     (:executable-counterpart zp))))))

(defthm fn-pth-i-runtime-buffered-submit
 (implies (and (fn-pth-i-runtime s) (fn-rtc-live-p id inc s)
               (member-eq kind '(:recv :send :pread :pwrite :bp-send))
               (fn-rtc-submit-okp kind hd id inc s)
               (not (fn-rtc-kind-out-p kind id inc (fn-rtc-uses s)))
               (fn-rtc-shapep (fn-rtc-buffered-submit-state kind hd id inc s)))
  (fn-pth-i-runtime (fn-rtc-buffered-submit-state kind hd id inc s)))
 :hints (("Goal"
  :use (fn-pth-i-buffered-submit-new-use fn-pth-i-buffered-submit-new-buffer-metadata
        fn-pth-i-buffered-submit-compatible
        (:instance fn-pth-i-op-not-used-above-next (uses (fn-rtc-uses s))
          (op (fn-rtc-next-op s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-buffered-submit-state fn-rtc-submit-okp
     fn-pth-i-runtime-of-buffer-and-compatible-issue fn-pth-i-runtime-of-compatible-issue
     fn-pth-i-runtime-control-by-definition fn-rtc-leasedp
     fn-rtc-next-op-of-with fn-rtc-with-accessors fn-rtc-get-of-cons
     fn-pth-owner-equality-fields-by-definition natp
     (:type-prescription fn-rtc-h-buf) (:type-prescription fn-rtc-next-op)
     (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
     (:executable-counterpart member-equal) (:executable-counterpart nfix)
     (:executable-counterpart zp))))))

; From p15b-I-hand-new-use.lisp

(defthm fn-pth-i-hand-submit-new-use-okp
 (implies (and (fn-pth-i-runtime s) (posp id)
                (fn-rtc-live-p id inc s)
                (fn-rtc-submit-okp :hand hd id inc s))
           (fn-rtc-use-okp (list :hand id inc (fn-rtc-next-op s) hd)
                          (fn-rtc-hand-submit-state hd extra id inc s)))
 :hints (("Goal" :use (fn-pth-i-runtime-live-caller-is-u64
    fn-pth-i-shaped-live-slot-in-range
    (:instance fn-pth-i-holders-of-unleased-buffer
     (h (fn-rtc-h-buf hd)) (g (fn-rtc-h-gen hd)) (uses (fn-rtc-uses s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-rtc-shapep fn-rtc-hand-submit-state fn-rtc-submit-okp fn-rtc-use-okp fn-rtc-usep
     fn-rtc-current-p fn-rtc-live-p fn-rtc-issue-frame fn-rtc-with-accessors
     fn-rtc-buffer-of-with fn-rtc-next-op-of-with fn-rtc-slot-of-with fn-rtc-get-of-cons fn-rtc-buffer-accessors
     fn-rtc-u-hd fn-rtc-holders-cons fn-rtc-leasedp fn-pth-i-runtime-control-by-definition
     fn-pth-owner-equality-fields-by-definition
     member-equal natp posp nfix len true-listp car-cons cdr-cons
     default-+-1 default-+-2 unicity-of-0 fix (:type-prescription fn-rtc-next-op)
     (:type-prescription fn-rtc-h-buf) (:type-prescription fn-rtc-h-gen)
     (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
     (:executable-counterpart member-equal) (:executable-counterpart nfix)
     (:executable-counterpart binary-+) (:executable-counterpart zp))))))

; From p15b-I-hand-runtime.lisp

(defthm fn-pth-i-issued-hand-buffer-metadata
 (implies (and (posp id) (fn-rtc-u64p inc) (< id (fn-rtc-nslots (fn-rtc-config s)))
               (fn-rtc-hand-target-okp extra id s)
               (fn-rtc-handlep hd) (equal g (fn-rtc-h-gen hd)))
  (fn-pth-i-buffer-state-okp (fn-rtc-h-buf hd)
   (list g (list :handed id inc (fn-rtc-get 0 extra) (fn-rtc-get 1 extra)) bytes)
   (fn-rtc-issue (list :hand id inc op hd) (fn-rtc-with-buffer h b s))))
 :hints (("Goal"
  :expand ((fn-rtc-holds-p (fn-rtc-h-buf hd) (fn-rtc-h-gen hd)
            (cons (list :hand id inc op hd) (fn-rtc-uses s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-buffer-state-okp fn-pth-i-buffer-ownerp fn-rtc-hand-target-okp
     fn-rtc-issue-frame fn-rtc-with-accessors fn-rtc-buffer-accessors fn-rtc-u-hd
     fn-rtc-get-of-cons car-cons cdr-cons len true-listp member-equal nfix natp posp
     (:type-prescription fn-rtc-h-gen) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart equal) (:executable-counterpart binary-+)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))

(defthm fn-pth-i-hand-submit-new-buffer-metadata
 (let* ((h (fn-rtc-h-buf hd)) (b (fn-rtc-buffer h s)))
  (implies (and (fn-pth-i-runtime s) (fn-rtc-live-p id inc s)
               (fn-rtc-hand-target-okp extra id s) (fn-rtc-submit-okp :hand hd id inc s))
   (fn-pth-i-buffer-state-okp h
    (list (fn-rtc-b-gen b) (list :handed id inc (fn-rtc-get 0 extra) (fn-rtc-get 1 extra))
          (fn-rtc-b-bytes b)) (fn-rtc-hand-submit-state hd extra id inc s))))
 :hints (("Goal" :use ((:instance fn-pth-i-submitter-has-natural-id (kind :hand))
                       fn-pth-i-live-natural-caller-scalars)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-hand-submit-state fn-rtc-submit-okp fn-rtc-hand-target-okp
     fn-pth-i-issued-hand-buffer-metadata
     fn-rtc-with-accessors fn-rtc-next-op-of-with member-equal natp posp nfix
     (:executable-counterpart member-equal) (:executable-counterpart equal))))))

(defthm fn-pth-i-hand-submit-compatible
 (implies (and (fn-pth-i-runtime s) (fn-rtc-submit-okp :hand hd id inc s))
  (fn-rtc-compatible-usesp (list :hand id inc (fn-rtc-next-op s) hd) (fn-rtc-uses s)))
 :hints (("Goal" :use ((:instance fn-pth-i-compatible-uses-from-shareable-pool
   (uses (fn-rtc-uses s)) (new (list :hand id inc (fn-rtc-next-op s) hd))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime-control-by-definition fn-rtc-submit-okp fn-rtc-leasedp
     fn-rtc-u-hd fn-rtc-get-of-cons fn-pth-owner-equality-fields-by-definition
     car-cons cdr-cons (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
     (:executable-counterpart member-equal) (:executable-counterpart nfix)
     (:executable-counterpart zp))))))

(defthm fn-pth-i-runtime-hand-submit
 (implies (and (fn-pth-i-runtime s) (fn-rtc-live-p id inc s)
               (fn-rtc-submit-okp :hand hd id inc s) (fn-rtc-hand-target-okp extra id s)
               (fn-rtc-shapep (fn-rtc-hand-submit-state hd extra id inc s)))
  (fn-pth-i-runtime (fn-rtc-hand-submit-state hd extra id inc s)))
 :hints (("Goal"
  :use ((:instance fn-pth-i-submitter-has-natural-id (kind :hand))
        fn-pth-i-hand-submit-new-use-okp fn-pth-i-hand-submit-new-buffer-metadata
        fn-pth-i-hand-submit-compatible
        (:instance fn-pth-i-op-not-used-above-next (uses (fn-rtc-uses s))
          (op (fn-rtc-next-op s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-hand-submit-state fn-rtc-submit-okp fn-rtc-hand-target-okp
     fn-pth-i-runtime-of-buffer-and-compatible-issue fn-pth-i-runtime-control-by-definition
     fn-rtc-leasedp fn-rtc-next-op-of-with fn-rtc-get-of-cons
     fn-pth-owner-equality-fields-by-definition natp posp nfix
     (:type-prescription fn-rtc-h-buf) (:type-prescription fn-rtc-next-op)
     (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
     (:executable-counterpart member-equal) (:executable-counterpart nfix)
     (:executable-counterpart zp))))))

; From p15b-I-submit-request.lisp

(defthm fn-pth-i-buffered-machine-kind-properties
 (implies (and (member-eq kind *fn-rtc-machine-kinds*) (fn-rtc-buffered-kind-p kind)
               (not (equal kind :hand)) (not (equal kind :pool)))
          (member-eq kind '(:recv :send :pread :pwrite :bp-send)))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-buffered-kind-p member-equal (:executable-counterpart equal))))))

(defthm fn-pth-i-runtime-request-submit
 (implies (and (fn-pth-i-runtime s) (equal (fn-rtc-get 0 r) :submit))
          (fn-pth-i-runtime (mv-nth 0 (fn-rtc-request r id inc s))))
 :hints (("Goal"
  :cases ((or (equal (fn-rtc-get 1 r) :pool)
              (not (fn-rtc-buffered-kind-p (fn-rtc-get 1 r)))))
  :use (fn-pth-request-keeps-shapep fn-pth-i-runtime-request-submit-unbuffered
        (:instance fn-pth-i-runtime-buffered-submit (kind (fn-rtc-get 1 r)) (hd (fn-rtc-get 2 r)))
        (:instance fn-pth-i-runtime-hand-submit (hd (fn-rtc-get 2 r)) (extra (fn-rtc-get 3 r)))
        (:instance fn-rtc-hand-submit-okp-owner (hd (fn-rtc-get 2 r)))
        (:instance fn-pth-i-buffered-machine-kind-properties (kind (fn-rtc-get 1 r))))
  :in-theory (union-theories
   (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-runtime-shape-by-definition fn-rtc-request fn-rtc-req-submit
     fn-rtc-buffered-submit-state fn-rtc-hand-submit-state fn-rtc-next-op-of-with
     fn-rtc-get-of-cons fn-hld-mv-nth-0-cons car-cons cdr-cons
     (:executable-counterpart fn-rtc-get) (:executable-counterpart fn-rtc-handlep)
     (:executable-counterpart fn-rtc-buffered-kind-p) (:executable-counterpart member-equal)
     (:executable-counterpart equal) (:executable-counterpart nfix)
     (:executable-counterpart zp))))))

; From p15b-I-all-requests.lisp

(defthm fn-pth-i-runtime-request
 (implies (fn-pth-i-runtime s)
          (fn-pth-i-runtime (mv-nth 0 (fn-rtc-request r id inc s))))
 :hints (("Goal" :cases ((equal (fn-rtc-get 0 r) :acquire)
   (equal (fn-rtc-get 0 r) :write) (equal (fn-rtc-get 0 r) :release)
   (equal (fn-rtc-get 0 r) :close) (equal (fn-rtc-get 0 r) :submit)
   (equal (fn-rtc-get 0 r) :cancel))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime-request-acquire fn-pth-i-runtime-request-write
     fn-pth-i-runtime-request-release fn-pth-i-runtime-request-close
     fn-pth-i-runtime-request-submit fn-pth-i-runtime-request-cancel
     fn-pth-i-runtime-request-unknown member-equal (:executable-counterpart equal))))))

(defthm fn-pth-i-runtime-requests
 (implies (fn-pth-i-runtime s)
          (fn-pth-i-runtime (mv-nth 0 (fn-rtc-requests reqs id inc s))))
 :hints (("Goal" :induct (fn-rtc-requests reqs id inc s)
  :in-theory (union-theories
   (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-requests fn-pth-i-runtime-request fn-hld-mv-nth-0-cons car-cons cdr-cons)))))

; Runtime I: completion end-use and listener rearm.

; From p15c-I-removal.lisp
(defthm fn-pth-i-uses-member
 (implies (and (fn-pth-i-uses uses s) (member-equal u uses))
          (or (fn-rtc-use-okp u s) (fn-pth-i-listener-use u s)))
 :hints (("Goal" :induct (member-equal u uses)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-uses member-equal car-cons cdr-cons)))))
(defthm fn-pth-i-uses-remove
 (implies (fn-pth-i-uses uses s)
          (fn-pth-i-uses (fn-rtc-remove-use key uses) s))
 :hints (("Goal" :induct (fn-rtc-remove-use key uses)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-uses fn-rtc-remove-use fn-rtc-remove-use-kind-subset
     fn-rtc-remove-use-op-subset car-cons cdr-cons)))))
(defthm fn-pth-i-listener-use-after-removal
 (implies (and (fn-pth-i-listener-use u s)
               (member-equal u (fn-rtc-remove-use key (fn-rtc-uses s))))
          (fn-pth-i-listener-use u
           (fn-rtc-with-uses (fn-rtc-remove-use key (fn-rtc-uses s)) s)))
 :hints (("Goal"
  :use ((:instance fn-rtc-holders-remove-bound
          (h (fn-rtc-h-buf (fn-rtc-u-hd u))) (g (fn-rtc-h-gen (fn-rtc-u-hd u)))
          (uses (fn-rtc-uses s)))
        (:instance fn-rtc-member-holder-positive
          (uses (fn-rtc-remove-use key (fn-rtc-uses s)))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-listener-use fn-rtc-with-accessors fn-rtc-slot-of-with
     fn-rtc-buffer-of-with fn-rtc-next-op-of-with
     (:type-prescription fn-rtc-holders)
     (:executable-counterpart equal) (:executable-counterpart member-equal))))))
(defthm fn-pth-i-uses-after-removal-subset
 (implies (and (fn-pth-i-uses uses s)
               (subsetp-equal uses (fn-rtc-remove-use key (fn-rtc-uses s))))
          (fn-pth-i-uses uses
           (fn-rtc-with-uses (fn-rtc-remove-use key (fn-rtc-uses s)) s)))
 :hints (("Goal" :induct (fn-pth-i-uses uses s)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-uses subsetp-equal fn-pth-i-listener-use-after-removal
     fn-rtc-use-okp-after-removal car-cons cdr-cons)))))
(defthm fn-pth-i-uses-after-removal
 (implies (fn-pth-i-uses (fn-rtc-uses s) s)
          (fn-pth-i-uses (fn-rtc-remove-use key (fn-rtc-uses s))
           (fn-rtc-with-uses (fn-rtc-remove-use key (fn-rtc-uses s)) s)))
 :hints (("Goal"
  :use ((:instance fn-pth-i-uses-after-removal-subset
          (uses (fn-rtc-remove-use key (fn-rtc-uses s)))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-uses-remove fn-rtc-subset-reflexive)))))

; From p15c-I-pool-removal.lisp
(defthm fn-pth-i-buffer-state-okp-after-removal-other
  (implies (and (fn-pth-i-buffer-state-okp h b s)
                (or (not (fn-rtc-handlep (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s)))))
                    (not (equal h (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s))))))
                    (fn-rtc-holds-p (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s))))
                                    (fn-rtc-h-gen (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s))))
                                    (fn-rtc-remove-use key (fn-rtc-uses s)))))
           (fn-pth-i-buffer-state-okp h b (fn-rtc-with-uses (fn-rtc-remove-use key (fn-rtc-uses s)) s)))
  :hints (("Goal" :cases ((equal (fn-rtc-b-gen b) (fn-rtc-h-gen (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s))))))
 :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-buffer-state-okp fn-rtc-with-accessors fn-rtc-slot-of-with fn-rtc-holds-remove-other
    (:executable-counterpart equal) (:executable-counterpart member-equal))))))


(defthm fn-pth-i-pool-after-covered-removal
  (implies (and (fn-pth-i-pool i pool s)
                (or (not (fn-rtc-handlep (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s)))))
                    (fn-rtc-holds-p (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s))))
                                    (fn-rtc-h-gen (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s))))
                                    (fn-rtc-remove-use key (fn-rtc-uses s)))))
           (fn-pth-i-pool i pool (fn-rtc-with-uses (fn-rtc-remove-use key (fn-rtc-uses s)) s)))
  :hints (("Goal" :induct (fn-pth-i-pool-index-induct i pool)
 :in-theory (union-theories (theory 'minimal-theory)
  '((:induction fn-pth-i-pool-index-induct) fn-pth-i-pool-unfolds
    fn-pth-i-buffer-state-okp-after-removal-other)))))


(defthm fn-pth-i-pool-after-removal-later
  (implies (and (natp i) (fn-pth-i-pool i pool s)
                (< (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s)))) i))
           (fn-pth-i-pool i pool (fn-rtc-with-uses (fn-rtc-remove-use key (fn-rtc-uses s)) s)))
  :hints (("Goal" :induct (fn-pth-i-pool-index-induct i pool)
 :in-theory (union-theories (theory 'minimal-theory)
  '((:induction fn-pth-i-pool-index-induct) fn-pth-i-pool-unfolds
    fn-pth-i-buffer-state-okp-after-removal-other nfix natp
    default-+-1 default-+-2 (:executable-counterpart binary-+))))))


(defthm fn-pth-i-pool-replace-after-removal
  (implies (and (natp i) (natp k) (fn-pth-i-pool i pool s)
                (equal (+ i k) (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s)))))
                (fn-pth-i-buffer-state-okp (+ i k) b
                  (fn-rtc-with-uses (fn-rtc-remove-use key (fn-rtc-uses s)) s)))
           (fn-pth-i-pool i (fn-rtc-set k b pool)
             (fn-rtc-with-uses (fn-rtc-remove-use key (fn-rtc-uses s)) s)))
  :hints (("Goal" :induct (fn-rtc-index-induct k i pool)
 :in-theory (union-theories (theory 'minimal-theory)
  '((:induction fn-rtc-index-induct) fn-pth-i-pool-unfolds fn-rtc-set
    fn-pth-i-pool-after-removal-later fn-pth-i-buffer-state-okp-after-removal-other
    nfix natp zp car-cons cdr-cons
    default-+-1 default-+-2 associativity-of-+ commutativity-of-+ commutativity-2-of-+ fold-consts-in-+ unicity-of-0 fix
    (:executable-counterpart nfix) (:executable-counterpart zp)))
 :expand ((:with fn-pth-i-pool-unfolds (fn-pth-i-pool i pool s))
          (:with fn-pth-i-pool-unfolds (fn-pth-i-pool i (cons b (cdr pool))
           (fn-rtc-with-uses (fn-rtc-remove-use key (fn-rtc-uses s)) s)))))))


; From p15c-I-end-lease-uses.lisp
(defthm fn-pth-i-listener-use-of-unheld-update
 (implies (and (natp h) (fn-pth-i-listener-use u s) (member-equal u (fn-rtc-uses s))
               (equal (fn-rtc-holders h (fn-rtc-b-gen (fn-rtc-buffer h s)) (fn-rtc-uses s)) 0))
          (fn-pth-i-listener-use u (fn-rtc-with-buffer h b s)))
 :hints (("Goal" :use ((:instance fn-rtc-member-holder-positive (uses (fn-rtc-uses s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-listener-use fn-rtc-with-accessors fn-rtc-buffer-of-with
     fn-rtc-next-op-of-with (:type-prescription fn-rtc-h-buf) nfix natp)))))
(defthm fn-pth-i-uses-of-unheld-update-subset
 (implies (and (natp h) (fn-pth-i-uses uses s) (subsetp-equal uses (fn-rtc-uses s))
               (equal (fn-rtc-holders h (fn-rtc-b-gen (fn-rtc-buffer h s)) (fn-rtc-uses s)) 0))
          (fn-pth-i-uses uses (fn-rtc-with-buffer h b s)))
 :hints (("Goal" :induct (fn-pth-i-uses uses s)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-uses subsetp-equal fn-pth-i-listener-use-of-unheld-update
     fn-rtc-use-okp-of-unheld-update car-cons cdr-cons)))))
(defthm fn-pth-i-uses-of-unheld-update
 (implies (and (natp h) (fn-pth-i-uses (fn-rtc-uses s) s)
               (equal (fn-rtc-holders h (fn-rtc-b-gen (fn-rtc-buffer h s)) (fn-rtc-uses s)) 0))
          (fn-pth-i-uses (fn-rtc-uses s) (fn-rtc-with-buffer h b s)))
 :hints (("Goal"
  :use ((:instance fn-pth-i-uses-of-unheld-update-subset (uses (fn-rtc-uses s))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-subset-reflexive)))))
(defthm fn-pth-i-listener-use-lease-generation
 (implies (and (fn-pth-i-listener-use u s) (fn-rtc-handlep (fn-rtc-u-hd u)))
          (equal (fn-rtc-b-gen (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s))
                 (fn-rtc-h-gen (fn-rtc-u-hd u))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-listener-use (:executable-counterpart fn-rtc-handlep))))))
(defthm fn-pth-i-uses-end-lease-after-removal
 (implies (and (fn-pth-i-uses (fn-rtc-uses s) s) (fn-rtc-find-use key (fn-rtc-uses s)))
  (let* ((u (fn-rtc-find-use key (fn-rtc-uses s)))
         (s1 (fn-rtc-with-uses (fn-rtc-remove-use key (fn-rtc-uses s)) s))
         (s2 (fn-rtc-end-lease u e s1)))
   (fn-pth-i-uses (fn-rtc-uses s2) s2)))
 :hints (("Goal"
  :use ((:instance fn-pth-i-uses-after-removal)
        (:instance fn-pth-i-uses-of-unheld-update
         (h (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s)))))
         (b (fn-rtc-lease-return (fn-rtc-find-use key (fn-rtc-uses s)) e
             (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s)))) s)
             (fn-rtc-with-uses (fn-rtc-remove-use key (fn-rtc-uses s)) s)))
         (s (fn-rtc-with-uses (fn-rtc-remove-use key (fn-rtc-uses s)) s)))
        (:instance fn-pth-i-uses-member (uses (fn-rtc-uses s))
          (u (fn-rtc-find-use key (fn-rtc-uses s))))
        (:instance fn-rtc-find-use-is-member (k key) (uses (fn-rtc-uses s)))
        (:instance fn-rtc-use-okp-lease (u (fn-rtc-find-use key (fn-rtc-uses s))))
        (:instance fn-pth-i-listener-use-lease-generation (u (fn-rtc-find-use key (fn-rtc-uses s)))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-end-lease fn-rtc-with-accessors fn-rtc-buffer-of-with
     fn-pth-i-uses-after-removal fn-pth-i-uses-of-unheld-update
     fn-rtc-holds-iff-positive-holders (:type-prescription fn-rtc-holders)
     (:type-prescription fn-rtc-h-buf) natp)))))

; From p15c-I-return-metadata.lisp
(defthm fn-pth-i-current-active-caller-scalars
 (implies (and (fn-pth-i-runtime s) (natp id) (fn-rtc-current-p id inc s)
               (member-eq (fn-rtc-s-status (fn-rtc-slot id s)) '(:live :closing)))
          (and (fn-rtc-u64p inc) (< id (fn-rtc-nslots (fn-rtc-config s)))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-pth-i-shaped-live-slot-in-range)
                         (:instance fn-pth-slot-inc-is-u64-from-inc-table (j id)))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-rtc-current-p)))))
(defthm fn-pth-i-lease-return-buffer-metadata
 (implies (and (fn-pth-i-runtime s) (fn-pth-i-buffer-state-okp h b s))
          (fn-pth-i-buffer-state-okp h (fn-rtc-lease-return u e b s) s))
 :hints (("Goal"
  :use ((:instance fn-pth-i-current-active-caller-scalars (id (nfix (fn-rtc-get 1 (fn-rtc-b-owner b))))
          (inc (fn-rtc-get 2 (fn-rtc-b-owner b))))
        (:instance fn-pth-i-live-natural-caller-scalars (id (nfix (fn-rtc-get 3 (fn-rtc-b-owner b))))
          (inc (fn-rtc-get 4 (fn-rtc-b-owner b)))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-lease-return fn-rtc-handed-to-live-p fn-pth-i-buffer-state-okp
     fn-pth-i-buffer-ownerp fn-rtc-buffer-accessors fn-rtc-get-of-cons
     fn-rtc-live-p fn-rtc-current-p fn-rtc-u64p-implies-natp
     nfix natp posp len true-listp car-cons cdr-cons
     (:type-prescription nfix) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart equal) (:executable-counterpart len)
     (:executable-counterpart true-listp) (:executable-counterpart member-equal)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))

; From p15c-I-return-shape.lisp
(defthm fn-pth-with-uses-keeps-shapep
 (implies (fn-rtc-shapep s) (fn-rtc-shapep (fn-rtc-with-uses uses s)))
 :hints (("Goal" :use ((:instance fn-rtc-st-p-of-with-uses (fn-rtc-st s)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-st-p-is-shapep)))))
(defthm fn-pth-with-buffer-physical-shape
 (implies (and (fn-rtc-shapep s) (natp h)
               (true-listp b) (equal (len b) 3) (natp (fn-rtc-get 0 b))
               (fn-cbor-octet-listp (fn-rtc-get 2 b))
               (<= (len (fn-rtc-get 2 b)) (fn-rtc-buf-cap h (fn-rtc-config s))))
          (fn-rtc-shapep (fn-rtc-with-buffer h b s)))
 :hints (("Goal"
  :use ((:instance fn-rtc-c-pool-shapep-of-set (k 0) (i h)
          (pool (fn-rtc-pool s)) (cfg (fn-rtc-config s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-shapep fn-rtc-with-buffer fn-rtc-make-accessors
     fn-rtc-c-make-shape fn-rtc-len-of-set fn-rtc-get-of-cons
     fn-rtc-next-op nfix natp len true-listp car-cons cdr-cons
     default-+-1 default-+-2 unicity-of-0 fix
     (:executable-counterpart binary-+) (:executable-counterpart nfix)
     (:executable-counterpart zp) (:executable-counterpart equal))))))
(defthm fn-pth-i-input-use-local-range
 (implies (and (or (fn-rtc-use-okp u s) (fn-pth-i-listener-use u s))
               (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*))
          (and (natp (fn-rtc-h-off (fn-rtc-u-hd u)))
               (<= (fn-rtc-h-off (fn-rtc-u-hd u))
                   (len (fn-rtc-b-bytes (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s))))
               (<= (+ (fn-rtc-h-off (fn-rtc-u-hd u)) (fn-rtc-h-len (fn-rtc-u-hd u)))
                   (fn-rtc-buf-cap (fn-rtc-h-buf (fn-rtc-u-hd u)) (fn-rtc-config s)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-rtc-use-okp fn-rtc-usep fn-rtc-u-hd fn-pth-i-listener-use fn-rtc-buffered-kind-p member-equal
    (:type-prescription fn-rtc-h-off) natp (:executable-counterpart member-equal))))))
(defthm fn-pth-i-lease-return-physical-bytes
 (implies (and (fn-rtc-shapep s)
               (or (fn-rtc-use-okp u s) (fn-pth-i-listener-use u s)))
  (let ((bytes (fn-rtc-b-bytes
                (fn-rtc-lease-return u e (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s) s))))
   (and (fn-cbor-octet-listp bytes)
        (<= (len bytes) (fn-rtc-buf-cap (fn-rtc-h-buf (fn-rtc-u-hd u)) (fn-rtc-config s))))))
 :rule-classes nil
 :hints (("Goal"
  :use (fn-pth-i-input-use-local-range fn-rtc-delivered-in-data
        (:instance fn-rtc-c-shapep-buffer (h (fn-rtc-h-buf (fn-rtc-u-hd u)))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-lease-return fn-rtc-b-bytes fn-rtc-buffer-accessors fn-rtc-get-of-cons
     fn-rtc-splice-octets fn-rtc-splice-length fn-cbor-octet-listp-implies-true-listp
     max car-cons cdr-cons
     (:executable-counterpart nfix) (:executable-counterpart zp)
     (:executable-counterpart equal) (:executable-counterpart member-equal))))))

; From p15c-I-pool-end-lease.lisp
(defthm fn-pth-i-unleased-buffer-state-uses-frame
 (implies (member-eq (fn-rtc-get 0 (fn-rtc-b-owner b)) '(:free :workspace))
  (equal (fn-pth-i-buffer-state-okp h b (fn-rtc-with-uses uses s))
         (fn-pth-i-buffer-state-okp h b s)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-buffer-state-okp fn-rtc-with-accessors fn-rtc-slot-of-with
    member-equal (:executable-counterpart equal))))))
(defthm fn-pth-i-lease-return-is-unleased
 (member-eq (fn-rtc-get 0 (fn-rtc-b-owner (fn-rtc-lease-return u e b s))) '(:free :workspace))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-rtc-lease-return fn-rtc-buffer-accessors fn-rtc-get-of-cons
    car-cons cdr-cons (:executable-counterpart fn-rtc-get)
    (:executable-counterpart member-equal) (:executable-counterpart equal)
    (:executable-counterpart nfix) (:executable-counterpart zp))))))
(defthm fn-pth-i-pool-end-lease-after-removal
 (implies (and (fn-pth-i-runtime s) (fn-rtc-find-use key (fn-rtc-uses s)))
  (let* ((u (fn-rtc-find-use key (fn-rtc-uses s)))
         (s1 (fn-rtc-with-uses (fn-rtc-remove-use key (fn-rtc-uses s)) s))
         (s2 (fn-rtc-end-lease u e s1)))
   (fn-pth-i-pool 0 (fn-rtc-pool s2) s2)))
 :hints (("Goal"
  :use ((:instance fn-pth-i-uses-member (uses (fn-rtc-uses s))
          (u (fn-rtc-find-use key (fn-rtc-uses s))))
        (:instance fn-rtc-find-use-is-member (k key) (uses (fn-rtc-uses s)))
        (:instance fn-rtc-use-okp-buffer-index (u (fn-rtc-find-use key (fn-rtc-uses s))))
        (:instance fn-pth-i-runtime-buffer-metadata
          (h (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s))))))
        (:instance fn-pth-i-pool-replace-after-removal (i 0)
          (k (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s)))))
          (pool (fn-rtc-pool s))
          (b (fn-rtc-lease-return (fn-rtc-find-use key (fn-rtc-uses s)) e
              (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s)))) s) s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-rtc-end-lease fn-rtc-with-accessors fn-rtc-buffer-of-with
     fn-rtc-lease-return-of-with-uses fn-pth-i-lease-return-is-unleased
     fn-pth-i-unleased-buffer-state-uses-frame fn-pth-i-lease-return-buffer-metadata
     fn-pth-i-pool-control-frame-of-buffer-update fn-pth-i-pool-after-covered-removal
     fn-pth-i-listener-use (:type-prescription fn-rtc-h-buf)
     nfix natp unicity-of-0 fix default-+-1 default-+-2
     (:executable-counterpart binary-+) (:executable-counterpart fn-rtc-handlep))))))

; From p15c-I-end-lease-runtime.lisp
(defthm fn-pth-i-lease-return-physical-shape
 (implies (and (fn-rtc-shapep s)
               (or (fn-rtc-use-okp u s) (fn-pth-i-listener-use u s)))
          (fn-rtc-shapep
           (fn-rtc-with-buffer (fn-rtc-h-buf (fn-rtc-u-hd u))
            (fn-rtc-lease-return u e (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s) s)
            (fn-rtc-with-uses uses s))))
 :hints (("Goal" :use (fn-pth-i-lease-return-physical-bytes)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-with-buffer-physical-shape fn-pth-with-uses-keeps-shapep
     fn-rtc-lease-return fn-rtc-buffer-accessors fn-rtc-get-of-cons
     fn-rtc-with-accessors true-listp len car-cons cdr-cons natp
     (:type-prescription fn-rtc-h-buf) (:type-prescription fn-rtc-b-gen)
     default-+-1 default-+-2 (:executable-counterpart fn-rtc-get)
     (:executable-counterpart nfix) (:executable-counterpart zp)
     (:executable-counterpart equal) (:executable-counterpart member-equal))))))
(defthm fn-pth-i-end-lease-after-removal-shapep
 (implies (and (fn-pth-i-runtime s) (fn-rtc-find-use key (fn-rtc-uses s)))
          (fn-rtc-shapep
           (fn-rtc-end-lease (fn-rtc-find-use key (fn-rtc-uses s)) e
            (fn-rtc-with-uses (fn-rtc-remove-use key (fn-rtc-uses s)) s))))
 :hints (("Goal"
  :use ((:instance fn-pth-i-uses-member (uses (fn-rtc-uses s))
          (u (fn-rtc-find-use key (fn-rtc-uses s))))
        (:instance fn-rtc-find-use-is-member (k key) (uses (fn-rtc-uses s)))
        (:instance fn-pth-i-lease-return-physical-shape
          (u (fn-rtc-find-use key (fn-rtc-uses s)))
          (uses (fn-rtc-remove-use key (fn-rtc-uses s)))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime-shape-by-definition fn-rtc-end-lease fn-rtc-with-accessors
     fn-rtc-buffer-of-with fn-rtc-lease-return-of-with-uses
     fn-pth-with-uses-keeps-shapep fn-pth-i-runtime-control-by-definition)))))
(defthm fn-pth-i-runtime-end-lease-after-removal
 (implies (and (fn-pth-i-runtime s) (fn-rtc-find-use key (fn-rtc-uses s)))
          (fn-pth-i-runtime
           (fn-rtc-end-lease (fn-rtc-find-use key (fn-rtc-uses s)) e
            (fn-rtc-with-uses (fn-rtc-remove-use key (fn-rtc-uses s)) s))))
 :hints (("Goal"
  :use (fn-pth-i-end-lease-after-removal-shapep fn-pth-i-pool-end-lease-after-removal
        fn-pth-i-uses-end-lease-after-removal)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-rtc-end-lease fn-rtc-with-accessors fn-rtc-slot-of-with
     fn-rtc-next-op-of-with fn-pth-with-uses-keeps-shapep)))))

; From p15c-I-retire.lisp
(defthm fn-pth-i-uses-of-unused-slot-update-subset
 (implies (and (natp id) (fn-pth-i-uses uses s) (subsetp-equal uses (fn-rtc-uses s))
               (not (fn-rtc-uses-of-slot-p id (fn-rtc-s-inc (fn-rtc-slot id s)) (fn-rtc-uses s))))
          (fn-pth-i-uses uses (fn-rtc-with-slot id slot s)))
 :hints (("Goal" :induct (fn-pth-i-uses uses s)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-uses subsetp-equal fn-pth-i-listener-use-slot-frame
     fn-rtc-use-okp-of-unused-slot-update car-cons cdr-cons)))))
(defthm fn-pth-i-uses-of-unused-slot-update
 (implies (and (natp id) (fn-pth-i-uses (fn-rtc-uses s) s)
               (not (fn-rtc-uses-of-slot-p id (fn-rtc-s-inc (fn-rtc-slot id s)) (fn-rtc-uses s))))
          (fn-pth-i-uses (fn-rtc-uses s) (fn-rtc-with-slot id slot s)))
 :hints (("Goal" :use ((:instance fn-pth-i-uses-of-unused-slot-update-subset
                                (uses (fn-rtc-uses s))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-subset-reflexive)))))
(defthm fn-pth-i-buffer-state-of-retired-slot
 (implies (and (natp id) (equal (fn-rtc-s-status (fn-rtc-slot id s)) :draining)
               (fn-pth-i-buffer-state-okp h b s))
          (fn-pth-i-buffer-state-okp h b (fn-rtc-with-slot id (list inc :free nil) s)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-buffer-state-okp fn-pth-i-buffer-ownerp
    fn-rtc-with-accessors fn-rtc-slot-of-with fn-rtc-slot-accessors
    nfix natp (:executable-counterpart fn-rtc-get)
    (:executable-counterpart equal) (:executable-counterpart member-equal)
    (:executable-counterpart nfix) (:executable-counterpart zp))))))
(defthm fn-pth-i-pool-of-retired-slot
 (implies (and (natp id) (equal (fn-rtc-s-status (fn-rtc-slot id s)) :draining)
               (fn-pth-i-pool i pool s))
          (fn-pth-i-pool i pool (fn-rtc-with-slot id (list inc :free nil) s)))
 :hints (("Goal" :induct (fn-pth-i-pool-index-induct i pool)
  :in-theory (union-theories (theory 'minimal-theory)
   '((:induction fn-pth-i-pool-index-induct) fn-pth-i-pool-unfolds
     fn-pth-i-buffer-state-of-retired-slot)))))
(defthm fn-pth-i-runtime-retire-drained
 (implies (and (fn-pth-i-runtime s) (natp id))
          (fn-pth-i-runtime (fn-rtc-retire-drained id s)))
 :hints (("Goal" :cases ((equal id 0) (equal id 1))
  :use ((:instance fn-pth-slot-inc-is-u64-from-inc-table (j id)))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-rtc-retire-drained fn-pth-with-slot-keeps-shapep
     fn-rtc-slots-okp-set fn-rtc-slot fn-rtc-free-slotp
     fn-pth-inc-tablep-with-slot fn-pth-inc-tablep-set fn-rtc-u64p-implies-natp fn-pth-i-pool-of-retired-slot fn-pth-i-uses-of-unused-slot-update
     fn-rtc-slot-of-with fn-rtc-with-accessors fn-rtc-slot-accessors
     fn-rtc-get-of-cons fn-rtc-get-of-set fn-rtc-len-of-set fn-rtc-next-op-of-with (:type-prescription fn-rtc-s-inc) nfix natp
     (:executable-counterpart fn-rtc-get) (:executable-counterpart fn-rtc-s-status)
     (:executable-counterpart fn-rtc-s-inc) (:executable-counterpart equal)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))

; From p15c-I-end-use-rearm.lisp
(defthm fn-pth-i-runtime-end-use
 (implies (fn-pth-i-runtime s) (fn-pth-i-runtime (fn-rtc-end-use s e)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-rtc-end-use fn-pth-i-runtime-end-lease-after-removal fn-pth-i-runtime-retire-drained
    (:type-prescription fn-rtc-e-id) natp)))))
(defthm fn-pth-i-fresh-listener-admission-use
 (implies (and (fn-pth-i-runtime s) (member-eq kind '(:accept :grant)))
          (fn-rtc-use-okp (list kind 0 0 (fn-rtc-next-op s) nil)
                         (fn-rtc-issue (list kind 0 0 (fn-rtc-next-op s) nil) s)))
 :hints (("Goal"
  :use ((:instance fn-pth-i-shaped-live-slot-in-range (id 0)))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime-listener-by-definition fn-pth-i-runtime-shape-by-definition
     fn-rtc-use-okp fn-rtc-usep fn-rtc-current-p fn-rtc-issue-frame
     fn-rtc-u-hd fn-rtc-get-of-cons fn-rtc-buffered-kind-p
     member-equal len true-listp nfix natp car-cons cdr-cons
     (:type-prescription fn-rtc-next-op) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart fn-rtc-u64p) (:executable-counterpart fn-rtc-s-inc)
     (:executable-counterpart fn-rtc-s-status) (:executable-counterpart fn-rtc-handlep)
     (:executable-counterpart equal) (:executable-counterpart nfix) (:executable-counterpart zp)
     (:executable-counterpart binary-+))))))
(defthm fn-pth-i-runtime-arm-accept
 (implies (fn-pth-i-runtime s) (fn-pth-i-runtime (mv-nth 0 (fn-rtc-arm-accept s))))
 :hints (("Goal"
  :use ((:instance fn-pth-i-op-not-used-above-next (uses (fn-rtc-uses s)) (op (fn-rtc-next-op s))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '((:type-prescription fn-rtc-next-op) natp fn-rtc-arm-accept fn-pth-i-runtime-of-unbuffered-issue fn-pth-i-fresh-listener-admission-use
     fn-pth-i-runtime-control-by-definition fn-rtc-u-hd fn-rtc-get-of-cons
     fn-hld-mv-nth-0-cons car-cons cdr-cons
     (:executable-counterpart fn-rtc-get) (:executable-counterpart fn-rtc-handlep)
     (:executable-counterpart member-equal) (:executable-counterpart equal)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))
(defthm fn-pth-i-runtime-arm-grant
 (implies (fn-pth-i-runtime s) (fn-pth-i-runtime (mv-nth 0 (fn-rtc-arm-grant s))))
 :hints (("Goal"
  :use ((:instance fn-pth-i-op-not-used-above-next (uses (fn-rtc-uses s)) (op (fn-rtc-next-op s))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '((:type-prescription fn-rtc-next-op) natp fn-rtc-arm-grant fn-pth-i-runtime-of-unbuffered-issue fn-pth-i-fresh-listener-admission-use
     fn-pth-i-runtime-control-by-definition fn-rtc-u-hd fn-rtc-get-of-cons
     fn-hld-mv-nth-0-cons car-cons cdr-cons
     (:executable-counterpart fn-rtc-get) (:executable-counterpart fn-rtc-handlep)
     (:executable-counterpart member-equal) (:executable-counterpart equal)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))
(defthm fn-pth-i-runtime-rearm
 (implies (fn-pth-i-runtime s) (fn-pth-i-runtime (mv-nth 0 (fn-rtc-rearm s))))
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '(fn-rtc-rearm fn-pth-i-runtime-arm-accept fn-pth-i-runtime-arm-grant fn-hld-mv-nth-0-cons car-cons cdr-cons)))))

; Runtime I: pool grants including listener/alias waits.

; From p15c-I-grant-structural.lisp
(defthm fn-pth-i-wait-has-no-handle
 (implies (and (or (fn-rtc-use-okp u s) (fn-pth-i-listener-use u s))
               (equal (fn-rtc-get 0 u) :wait))
          (and (not (fn-rtc-handlep (fn-rtc-u-hd u))) (consp u)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-rtc-use-okp fn-rtc-usep fn-pth-i-listener-use fn-rtc-u-hd
    fn-rtc-buffered-kind-p true-listp len
    (:executable-counterpart member-equal) (:executable-counterpart fn-rtc-handlep)
    (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
    (:executable-counterpart len))))))
(defthm fn-pth-i-replace-use-kind-subset
 (implies (and (not (equal kind (fn-rtc-get 0 v))) (not (fn-rtc-kind-out-p kind id inc uses)))
          (not (fn-rtc-kind-out-p kind id inc (fn-rtc-replace-use key v uses))))
 :hints (("Goal" :induct (fn-rtc-replace-use key v uses)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-kind-out-p fn-rtc-replace-use car-cons cdr-cons)))))
(defthm fn-pth-i-replace-wait-op-unused
 (implies (and (equal (fn-rtc-get 3 key) (fn-rtc-get 3 v))
               (not (fn-rtc-op-used-p op uses)))
          (not (fn-rtc-op-used-p op (fn-rtc-replace-use key v uses))))
 :hints (("Goal" :induct (fn-rtc-replace-use key v uses)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-op-used-p fn-rtc-replace-use fn-rtc-key fn-rtc-get-of-cons
     car-cons cdr-cons (:executable-counterpart nfix) (:executable-counterpart zp))))))
(defthm fn-pth-i-uses-replace-wait
 (implies (and (fn-pth-i-uses uses s) (equal (fn-rtc-get 0 v) :pool)
               (equal (fn-rtc-get 3 v) (fn-rtc-get 3 key))
               (or (fn-rtc-use-okp v s) (fn-pth-i-listener-use v s)))
          (fn-pth-i-uses (fn-rtc-replace-use key v uses) s))
 :hints (("Goal" :induct (fn-rtc-replace-use key v uses)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-uses fn-rtc-replace-use fn-pth-i-replace-use-kind-subset
     fn-pth-i-replace-wait-op-unused fn-rtc-key fn-rtc-get-of-cons car-cons cdr-cons
     (:executable-counterpart nfix) (:executable-counterpart zp)
     member-equal (:executable-counterpart equal))))))
(defthm fn-pth-i-holders-replace-wait
 (implies (and (fn-pth-i-uses uses s) (equal (fn-rtc-get 0 key) :wait))
  (equal (fn-rtc-holders h g (fn-rtc-replace-use key v uses))
   (+ (fn-rtc-holders h g uses)
      (if (and (fn-rtc-find-use key uses) (fn-rtc-handlep (fn-rtc-u-hd v))
               (equal h (fn-rtc-h-buf (fn-rtc-u-hd v)))
               (equal g (fn-rtc-h-gen (fn-rtc-u-hd v)))) 1 0))))
 :hints (("Goal" :induct (fn-rtc-replace-use key v uses)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-uses fn-rtc-replace-use fn-rtc-find-use fn-rtc-holders
     default-+-1 default-+-2 associativity-of-+ commutativity-of-+ commutativity-2-of-+ fold-consts-in-+ unicity-of-0 fix
     (:type-prescription fn-rtc-holders) (:executable-counterpart binary-+)
     (:executable-counterpart fn-rtc-key) (:executable-counterpart fn-rtc-get)
     car-cons cdr-cons)))
  ("Subgoal *1/1"
   :use ((:instance fn-pth-i-wait-has-no-handle (u (car uses))))
   :in-theory (union-theories (theory 'minimal-theory)
    '(fn-pth-i-uses fn-rtc-replace-use fn-rtc-find-use fn-rtc-holders
      fn-rtc-key fn-rtc-get-of-cons car-cons cdr-cons
      (:executable-counterpart nfix) (:executable-counterpart zp)
      default-+-1 default-+-2 (:executable-counterpart binary-+))))))

; From p15c-I-grant-holder-frame.lisp
(defthm fn-pth-i-holders-through-pool-grant-other
 (implies (and (fn-pth-i-uses (fn-rtc-uses s) s) (equal (fn-rtc-get 0 w) :wait)
               (natp h) (not (equal k h)))
          (equal (fn-rtc-holders k g (fn-rtc-uses (fn-rtc-pool-grant-state w h s)))
                 (fn-rtc-holders k g (fn-rtc-uses s))))
 :hints (("Goal"
  :use ((:instance fn-pth-i-holders-replace-wait (key (fn-rtc-key w))
          (uses (fn-rtc-uses s)) (h k) (v (fn-rtc-pool-grant-use w h s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-pool-grant-state-frame fn-rtc-pool-grant-use-fields
     fn-rtc-key fn-rtc-get-of-cons nfix natp car-cons cdr-cons
     default-+-1 default-+-2 (:type-prescription fn-rtc-holders)
     (:executable-counterpart binary-+) (:executable-counterpart nfix) (:executable-counterpart zp))))))

; From p15c-I-use-state-congruence.lisp
(defthm fn-pth-i-ordinary-use-state-congruence
 (implies (and (equal (fn-rtc-config s2) (fn-rtc-config s))
               (equal (fn-rtc-next-op s2) (fn-rtc-next-op s))
               (equal (fn-rtc-slot (nfix (fn-rtc-get 1 u)) s2)
                      (fn-rtc-slot (nfix (fn-rtc-get 1 u)) s))
               (implies (fn-rtc-handlep (fn-rtc-u-hd u))
                (and (equal (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s2)
                            (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s))
                     (equal (fn-rtc-holders (fn-rtc-h-buf (fn-rtc-u-hd u))
                                           (fn-rtc-h-gen (fn-rtc-u-hd u)) (fn-rtc-uses s2))
                            (fn-rtc-holders (fn-rtc-h-buf (fn-rtc-u-hd u))
                                           (fn-rtc-h-gen (fn-rtc-u-hd u)) (fn-rtc-uses s))))))
          (equal (fn-rtc-use-okp u s2) (fn-rtc-use-okp u s)))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-rtc-use-okp fn-rtc-current-p)))))
(defthm fn-pth-i-listener-use-state-congruence
 (implies (and (equal (fn-rtc-config s2) (fn-rtc-config s))
               (equal (fn-rtc-next-op s2) (fn-rtc-next-op s))
               (equal (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s2)
                      (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s))
               (equal (fn-rtc-holders (fn-rtc-h-buf (fn-rtc-u-hd u))
                                     (fn-rtc-h-gen (fn-rtc-u-hd u)) (fn-rtc-uses s2))
                      (fn-rtc-holders (fn-rtc-h-buf (fn-rtc-u-hd u))
                                     (fn-rtc-h-gen (fn-rtc-u-hd u)) (fn-rtc-uses s))))
          (equal (fn-pth-i-listener-use u s2) (fn-pth-i-listener-use u s)))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pth-i-listener-use)))))

; From p15c-I-grant-compatibility.lisp
(defthm fn-pth-i-pool-grant-other-buffer
 (implies (not (equal (nfix k) (nfix h)))
          (equal (fn-rtc-buffer k (fn-rtc-pool-grant-state w h s)) (fn-rtc-buffer k s)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-rtc-pool-grant-state fn-rtc-buffer-of-with)))))
(defthm fn-pth-i-holds-through-pool-grant
 (implies (and (fn-pth-i-uses (fn-rtc-uses s) s)
               (equal (fn-rtc-get 0 w) :wait) (fn-rtc-holds-p k g (fn-rtc-uses s)))
          (fn-rtc-holds-p k g (fn-rtc-uses (fn-rtc-pool-grant-state w h s))))
 :hints (("Goal"
  :use ((:instance fn-pth-i-holders-replace-wait (key (fn-rtc-key w))
          (uses (fn-rtc-uses s)) (h k) (v (fn-rtc-pool-grant-use w h s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-pool-grant-state-frame fn-rtc-holds-iff-positive-holders
     fn-rtc-key fn-rtc-get-of-cons (:executable-counterpart nfix) (:executable-counterpart zp)
     (:type-prescription fn-rtc-holders) car-cons cdr-cons
     default-+-1 default-+-2 (:executable-counterpart binary-+))))))
(defthm fn-pth-i-buffer-state-through-pool-grant
 (implies (and (fn-pth-i-uses (fn-rtc-uses s) s) (equal (fn-rtc-get 0 w) :wait)
               (fn-pth-i-buffer-state-okp k b s))
          (fn-pth-i-buffer-state-okp k b (fn-rtc-pool-grant-state w h s)))
 :hints (("Goal" :use ((:instance fn-pth-i-holds-through-pool-grant (g (fn-rtc-b-gen b))))
  :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-buffer-state-okp fn-rtc-pool-grant-state-frame
    fn-pth-i-holds-through-pool-grant (:executable-counterpart equal)
    (:executable-counterpart member-equal))))))
(defthm fn-pth-i-old-pool-through-grant
 (implies (and (fn-pth-i-uses (fn-rtc-uses s) s) (equal (fn-rtc-get 0 w) :wait)
               (fn-pth-i-pool k pool s))
          (fn-pth-i-pool k pool (fn-rtc-pool-grant-state w h s)))
 :hints (("Goal" :induct (fn-pth-i-pool-index-induct k pool)
  :in-theory (union-theories (theory 'minimal-theory)
   '((:induction fn-pth-i-pool-index-induct) fn-pth-i-pool-unfolds
     fn-pth-i-buffer-state-through-pool-grant)))))
(defthm fn-pth-i-compatible-use-avoids-free-buffer
 (implies (and (or (fn-rtc-use-okp u s) (fn-pth-i-listener-use u s))
               (fn-rtc-handlep (fn-rtc-u-hd u))
               (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:free)))
          (not (equal (fn-rtc-h-buf (fn-rtc-u-hd u)) h)))
 :hints (("Goal" :use (fn-rtc-use-okp-lease fn-pth-i-listener-use-handle-is-leased)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-leasedp (:executable-counterpart fn-rtc-get)
     (:executable-counterpart member-equal))))))
(defthm fn-pth-i-ordinary-use-through-pool-grant
 (implies (and (natp h) (fn-rtc-use-okp u s) (fn-pth-i-uses (fn-rtc-uses s) s)
               (equal (fn-rtc-get 0 w) :wait)
               (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:free)))
          (fn-rtc-use-okp u (fn-rtc-pool-grant-state w h s)))
 :hints (("Goal" :cases ((fn-rtc-handlep (fn-rtc-u-hd u)))
  :use ((:instance fn-pth-i-compatible-use-avoids-free-buffer)
        (:instance fn-pth-i-holders-through-pool-grant-other
          (k (fn-rtc-h-buf (fn-rtc-u-hd u))) (g (fn-rtc-h-gen (fn-rtc-u-hd u))))
        (:instance fn-pth-i-ordinary-use-state-congruence (s2 (fn-rtc-pool-grant-state w h s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-pool-grant-state-frame fn-pth-i-pool-grant-other-buffer
     nfix natp (:type-prescription fn-rtc-h-buf))))))
(defthm fn-pth-i-listener-use-through-pool-grant
 (implies (and (natp h) (fn-pth-i-listener-use u s) (fn-pth-i-uses (fn-rtc-uses s) s)
               (equal (fn-rtc-get 0 w) :wait)
               (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:free)))
          (fn-pth-i-listener-use u (fn-rtc-pool-grant-state w h s)))
 :hints (("Goal" :cases ((fn-rtc-handlep (fn-rtc-u-hd u)))
  :use ((:instance fn-pth-i-compatible-use-avoids-free-buffer)
        (:instance fn-pth-i-holders-through-pool-grant-other
          (k (fn-rtc-h-buf (fn-rtc-u-hd u))) (g (fn-rtc-h-gen (fn-rtc-u-hd u)))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-listener-use fn-rtc-pool-grant-state-frame fn-pth-i-pool-grant-other-buffer
     nfix natp (:type-prescription fn-rtc-h-buf) (:executable-counterpart fn-rtc-handlep))))))
(defthm fn-pth-i-uses-through-pool-grant
 (implies (and (natp h) (fn-pth-i-uses uses s) (fn-pth-i-uses (fn-rtc-uses s) s)
               (equal (fn-rtc-get 0 w) :wait)
               (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:free)))
          (fn-pth-i-uses uses (fn-rtc-pool-grant-state w h s)))
 :hints (("Goal" :induct (fn-pth-i-uses uses s)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-uses fn-pth-i-ordinary-use-through-pool-grant
     fn-pth-i-listener-use-through-pool-grant car-cons cdr-cons)))))

; From p15c-I-grant-handle.lisp
(defthm fn-pth-i-pool-grant-use-handlep
 (implies (natp h) (fn-rtc-handlep (fn-rtc-u-hd (fn-rtc-pool-grant-use w h s))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-rtc-pool-grant-use fn-rtc-u-hd fn-rtc-handlep fn-rtc-get-of-cons
    true-listp len natp nfix car-cons cdr-cons
    (:type-prescription fn-rtc-b-gen) default-+-1 default-+-2
    (:executable-counterpart fn-rtc-get) (:executable-counterpart nfix)
    (:executable-counterpart zp) (:executable-counterpart binary-+))))))

; From p15c-I-grant-new.lisp
(defthm fn-pth-i-wait-pair-facts
 (implies (and (fn-pth-i-runtime s)
               (or (fn-rtc-use-okp w s) (fn-pth-i-listener-use w s))
               (equal (fn-rtc-get 0 w) :wait))
          (and (fn-rtc-u64p (fn-rtc-get 2 w))
               (natp (fn-rtc-get 3 w)) (< (fn-rtc-get 3 w) (fn-rtc-next-op s))
               (< (nfix (fn-rtc-get 1 w)) (fn-rtc-nslots (fn-rtc-config s)))
               (fn-rtc-current-p (nfix (fn-rtc-get 1 w)) (fn-rtc-get 2 w) s)
               (implies (equal (nfix (fn-rtc-get 1 w)) 0) (equal (fn-rtc-get 2 w) 0))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-pth-i-shaped-live-slot-in-range (id 0)))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-use-okp fn-rtc-usep fn-pth-i-listener-use fn-rtc-current-p
     fn-pth-i-runtime-listener-by-definition fn-pth-i-runtime-shape-by-definition
     member-equal natp nfix (:type-prescription nfix)
     (:executable-counterpart fn-rtc-get) (:executable-counterpart fn-rtc-u64p)
     (:executable-counterpart fn-rtc-s-inc) (:executable-counterpart fn-rtc-s-status)
     (:executable-counterpart equal) (:executable-counterpart nfix) (:executable-counterpart zp))))))
(defthm fn-pth-i-pool-grant-holders
 (implies (and (fn-pth-i-runtime s) (member-equal w (fn-rtc-uses s))
               (equal (fn-rtc-get 0 w) :wait) (natp h)
               (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:free)))
          (equal (fn-rtc-holders h (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h s)))
                                (fn-rtc-uses (fn-rtc-pool-grant-state w h s))) 1))
 :hints (("Goal"
  :use ((:instance fn-pth-i-holders-of-unleased-buffer (uses (fn-rtc-uses s))
          (g (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h s)))))
        (:instance fn-pth-i-holders-replace-wait (key (fn-rtc-key w))
          (uses (fn-rtc-uses s)) (g (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h s))))
          (v (fn-rtc-pool-grant-use w h s)))
        (:instance fn-rtc-find-use-key-of-member (u w) (e w) (uses (fn-rtc-uses s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-rtc-pool-grant-state-frame fn-rtc-pool-grant-use-fields
     fn-rtc-key fn-rtc-get-of-cons fn-rtc-leasedp fn-pth-i-pool-grant-use-handlep natp nfix
     car-cons cdr-cons (:executable-counterpart member-equal)
     (:executable-counterpart fn-rtc-get) (:executable-counterpart binary-+)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))
(defthm fn-pth-i-pool-grant-new-use
 (implies (and (fn-pth-i-runtime s)
               (or (fn-rtc-use-okp w s) (fn-pth-i-listener-use w s))
               (member-equal w (fn-rtc-uses s)) (equal (fn-rtc-get 0 w) :wait)
               (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
               (fn-rtc-pool-buf-p h (fn-rtc-config s))
               (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:free)))
          (or (fn-rtc-use-okp (fn-rtc-pool-grant-use w h s) (fn-rtc-pool-grant-state w h s))
              (fn-pth-i-listener-use (fn-rtc-pool-grant-use w h s) (fn-rtc-pool-grant-state w h s))))
 :rule-classes nil
 :hints (("Goal" :cases ((equal (nfix (fn-rtc-get 1 w)) 0))
  :use (fn-pth-i-wait-pair-facts fn-pth-i-pool-grant-holders fn-pth-i-runtime-shape-by-definition)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-shapep fn-rtc-pool-grant-use fn-rtc-pool-grant-state fn-rtc-use-okp fn-rtc-usep
     fn-pth-i-listener-use fn-rtc-current-p fn-rtc-with-accessors fn-rtc-slot-of-with
     fn-rtc-buffer-of-with fn-rtc-next-op-of-with fn-rtc-buffer-accessors
     fn-rtc-u-hd fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len fn-rtc-handlep
     fn-rtc-get-of-cons len true-listp natp nfix car-cons cdr-cons
     (:type-prescription nfix) (:type-prescription fn-rtc-b-gen)
     default-+-1 default-+-2 (:executable-counterpart equal)
     (:executable-counterpart fn-rtc-get) (:executable-counterpart member-equal)
     (:executable-counterpart binary-+) (:executable-counterpart nfix) (:executable-counterpart zp))))))
(defthm fn-pth-i-pool-grant-new-buffer-metadata
 (implies (and (fn-pth-i-runtime s)
               (or (fn-rtc-use-okp w s) (fn-pth-i-listener-use w s))
               (member-equal w (fn-rtc-uses s)) (equal (fn-rtc-get 0 w) :wait)
               (natp h) (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:free)))
          (fn-pth-i-buffer-state-okp h
           (list (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h s)))
                 (list :leased (nfix (fn-rtc-get 1 w)) (fn-rtc-get 2 w) :in) nil)
           (fn-rtc-pool-grant-state w h s)))
 :hints (("Goal" :use (fn-pth-i-wait-pair-facts fn-pth-i-pool-grant-holders)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-buffer-state-okp fn-pth-i-buffer-ownerp fn-rtc-pool-grant-state-frame
     fn-rtc-holds-iff-positive-holders fn-rtc-buffer-accessors fn-rtc-get-of-cons
     true-listp len natp nfix car-cons cdr-cons (:type-prescription nfix) (:type-prescription fn-rtc-b-gen)
     default-+-1 default-+-2
     (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
     (:executable-counterpart member-equal) (:executable-counterpart true-listp)
     (:executable-counterpart binary-+) (:executable-counterpart nfix) (:executable-counterpart zp))))))

; From p15c-I-grant-runtime.lisp
(defthm fn-pth-i-pool-grant-shapep
 (implies (and (fn-rtc-shapep s) (natp h))
          (fn-rtc-shapep (fn-rtc-pool-grant-state w h s)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-rtc-pool-grant-state fn-pth-with-buffer-physical-shape fn-pth-with-uses-keeps-shapep
    fn-rtc-with-accessors fn-rtc-get-of-cons true-listp len natp
    (:type-prescription fn-rtc-b-gen) (:type-prescription fn-rtc-buf-cap)
    default-+-1 default-+-2 car-cons cdr-cons (:executable-counterpart fn-cbor-octet-listp)
    (:executable-counterpart fn-rtc-get) (:executable-counterpart nfix) (:executable-counterpart zp))))))
(defthm fn-pth-i-pool-grant-pool
 (implies (and (fn-pth-i-runtime s)
               (or (fn-rtc-use-okp w s) (fn-pth-i-listener-use w s))
               (member-equal w (fn-rtc-uses s)) (equal (fn-rtc-get 0 w) :wait)
               (natp h) (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:free)))
          (fn-pth-i-pool 0 (fn-rtc-pool (fn-rtc-pool-grant-state w h s))
                          (fn-rtc-pool-grant-state w h s)))
 :hints (("Goal"
  :use (fn-pth-i-pool-grant-new-buffer-metadata
        (:instance fn-pth-i-old-pool-through-grant (k 0) (pool (fn-rtc-pool s)))
        (:instance fn-pth-i-pool-set (i 0) (k h) (pool (fn-rtc-pool s))
          (s (fn-rtc-pool-grant-state w h s))
          (b (list (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h s)))
                   (list :leased (nfix (fn-rtc-get 1 w)) (fn-rtc-get 2 w) :in) nil))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-rtc-pool-grant-state fn-rtc-with-accessors
     nfix natp unicity-of-0 fix default-+-1 default-+-2)))))
(defthm fn-pth-i-pool-grant-uses
 (implies (and (fn-pth-i-runtime s)
               (or (fn-rtc-use-okp w s) (fn-pth-i-listener-use w s))
               (member-equal w (fn-rtc-uses s)) (equal (fn-rtc-get 0 w) :wait)
               (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
               (fn-rtc-pool-buf-p h (fn-rtc-config s))
               (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:free)))
          (fn-pth-i-uses (fn-rtc-uses (fn-rtc-pool-grant-state w h s))
                         (fn-rtc-pool-grant-state w h s)))
 :hints (("Goal"
  :use (fn-pth-i-pool-grant-new-use
        (:instance fn-pth-i-uses-through-pool-grant (uses (fn-rtc-uses s)))
        (:instance fn-pth-i-uses-replace-wait (uses (fn-rtc-uses s))
          (key (fn-rtc-key w)) (v (fn-rtc-pool-grant-use w h s))
          (s (fn-rtc-pool-grant-state w h s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime-control-by-definition fn-rtc-pool-grant-state-frame
     fn-rtc-pool-grant-use-fields fn-rtc-key fn-rtc-get-of-cons
     car-cons cdr-cons (:executable-counterpart nfix) (:executable-counterpart zp))))))
(defthm fn-pth-i-runtime-pool-grant
 (implies (and (fn-pth-i-runtime s)
               (or (fn-rtc-use-okp w s) (fn-pth-i-listener-use w s))
               (member-equal w (fn-rtc-uses s)) (equal (fn-rtc-get 0 w) :wait)
               (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
               (fn-rtc-pool-buf-p h (fn-rtc-config s))
               (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:free)))
          (fn-pth-i-runtime (fn-rtc-pool-grant-state w h s)))
 :hints (("Goal" :use (fn-pth-i-pool-grant-pool fn-pth-i-pool-grant-uses)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-rtc-pool-grant-state-frame fn-pth-i-pool-grant-shapep)))))
(defthm fn-pth-i-runtime-grant-one
 (implies (fn-pth-i-runtime s) (fn-pth-i-runtime (mv-nth 0 (fn-rtc-grant-one s))))
 :hints (("Goal"
  :use ((:instance fn-pth-i-runtime-pool-grant
         (w (fn-rtc-oldest-wait (fn-rtc-uses s)))
         (h (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s))))
        (:instance fn-pth-i-runtime-shape-by-definition)
        (:instance fn-pth-i-uses-member (uses (fn-rtc-uses s))
          (u (fn-rtc-oldest-wait (fn-rtc-uses s))))
        (:instance fn-rtc-oldest-wait-member (uses (fn-rtc-uses s)))
        (:instance fn-rtc-free-pool-buf-is-free (i 0) (pool (fn-rtc-pool s)) (cfg (fn-rtc-config s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-grant-one-is-pool-grant-state fn-pth-i-runtime-pool-grant
     fn-pth-i-runtime-control-by-definition fn-rtc-shapep fn-rtc-buffer fn-rtc-oldest-wait-kind
     fn-rtc-free-pool-buf-natural fn-rtc-free-pool-buf-upper-bound fn-rtc-free-pool-buf-pool-index
     (:type-prescription fn-rtc-free-pool-buf-type) natp nfix
     default-+-1 default-+-2 commutativity-of-+ unicity-of-0 fix (:executable-counterpart binary-+)
     (:executable-counterpart nfix) (:executable-counterpart natp) (:executable-counterpart unary--))))))
(defthm fn-pth-i-runtime-grant
 (implies (fn-pth-i-runtime s) (fn-pth-i-runtime (mv-nth 0 (fn-rtc-grant n s))))
 :hints (("Goal" :induct (fn-rtc-grant n s)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-grant fn-pth-i-runtime-grant-one fn-hld-mv-nth-0-cons car-cons cdr-cons)))))

; Runtime I: actual product completion dispatch.

; From p15c-I-deliver-runtime.lisp
(defthm fn-pth-i-listener-use-of-with-mstate
 (equal (fn-pth-i-listener-use u (fn-rtc-with-mstate id m s)) (fn-pth-i-listener-use u s))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-listener-use fn-rtc-with-accessors fn-rtc-buffer-of-with fn-rtc-next-op-of-with)))))
(defthm fn-pth-i-uses-of-with-mstate
 (equal (fn-pth-i-uses uses (fn-rtc-with-mstate id m s)) (fn-pth-i-uses uses s))
 :hints (("Goal" :induct (fn-pth-i-uses uses s)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-uses fn-pth-i-listener-use-of-with-mstate fn-rtc-use-okp-of-with-mstate)))))
(defthm fn-pth-i-pool-of-with-mstate
 (equal (fn-pth-i-pool i pool (fn-rtc-with-mstate id m s)) (fn-pth-i-pool i pool s))
 :hints (("Goal" :induct (fn-pth-i-pool-index-induct i pool)
  :in-theory (union-theories (theory 'minimal-theory)
   '((:induction fn-pth-i-pool-index-induct) fn-pth-i-pool-unfolds
     fn-pth-i-buffer-state-okp fn-rtc-with-accessors fn-rtc-slot-of-with)))))
(defthm fn-pth-i-runtime-with-mstate
 (implies (fn-pth-i-runtime s) (fn-pth-i-runtime (fn-rtc-with-mstate id m s)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-runtime fn-pth-with-mstate-keeps-shapep fn-pth-i-uses-of-with-mstate
    fn-pth-i-pool-of-with-mstate fn-rtc-with-accessors fn-rtc-slot-of-with)))))
(defthm fn-pth-i-runtime-deliver
 (implies (fn-pth-i-runtime s) (fn-pth-i-runtime (mv-nth 0 (fn-pth-deliver s id inc ev q))))
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '(fn-pth-deliver fn-pth-i-runtime-requests fn-pth-i-runtime-with-mstate
    fn-hld-mv-nth-0-cons car-cons cdr-cons)))))

; From p15c-I-accept-runtime.lisp
(defthm fn-pth-i-uses-of-free-slot-update
 (implies (and (natp id) (fn-pth-i-uses uses s)
               (equal (fn-rtc-s-status (fn-rtc-slot id s)) :free))
          (fn-pth-i-uses uses (fn-rtc-with-slot id slot s)))
 :hints (("Goal" :induct (fn-pth-i-uses uses s)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-uses fn-pth-i-listener-use-slot-frame fn-rtc-use-okp-of-free-slot-update)))))
(defthm fn-pth-i-buffer-state-of-free-slot-update
 (implies (and (natp id) (equal (fn-rtc-s-status (fn-rtc-slot id s)) :free)
               (fn-pth-i-buffer-state-okp h b s))
          (fn-pth-i-buffer-state-okp h b (fn-rtc-with-slot id slot s)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-buffer-state-okp fn-pth-i-buffer-ownerp
    fn-rtc-with-accessors fn-rtc-slot-of-with nfix natp
    (:executable-counterpart equal) (:executable-counterpart member-equal))))))
(defthm fn-pth-i-pool-of-free-slot-update
 (implies (and (natp id) (equal (fn-rtc-s-status (fn-rtc-slot id s)) :free)
               (fn-pth-i-pool i pool s))
          (fn-pth-i-pool i pool (fn-rtc-with-slot id slot s)))
 :hints (("Goal" :induct (fn-pth-i-pool-index-induct i pool)
  :in-theory (union-theories (theory 'minimal-theory)
   '((:induction fn-pth-i-pool-index-induct) fn-pth-i-pool-unfolds
     fn-pth-i-buffer-state-of-free-slot-update)))))
(defthm fn-pth-i-runtime-activate-slot
 (implies (and (fn-pth-i-runtime s) (natp id) (< 1 id) (fn-rtc-u64p inc)
               (natp r) (< r (expt 2 64))
               (equal (fn-rtc-s-status (fn-rtc-slot id s)) :free))
          (fn-pth-i-runtime (fn-rtc-with-slot id (list inc :live r) s)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-runtime fn-pth-with-slot-keeps-shapep
    fn-pth-i-uses-of-free-slot-update fn-pth-i-pool-of-free-slot-update
    fn-rtc-slots-okp-set fn-pth-inc-tablep-set fn-rtc-slotp fn-rtc-u64p
    fn-rtc-u64p-implies-natp fn-rtc-with-accessors fn-rtc-slot-of-with
    fn-rtc-slot fn-rtc-get-of-set fn-rtc-slot-accessors fn-rtc-get-of-cons
    nfix natp len true-listp car-cons cdr-cons
    (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
    (:executable-counterpart expt) (:executable-counterpart member-equal)
    (:executable-counterpart nfix) (:executable-counterpart zp))))))
(defthm fn-pth-i-free-slot-is-dynamic
 (implies (and (fn-pth-i-runtime s) (fn-rtc-free-slot 0 (fn-rtc-slots s)))
          (and (natp (fn-rtc-free-slot 0 (fn-rtc-slots s)))
               (< 1 (fn-rtc-free-slot 0 (fn-rtc-slots s)))
               (equal (fn-rtc-s-status
                        (fn-rtc-slot (fn-rtc-free-slot 0 (fn-rtc-slots s)) s)) :free)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-rtc-free-slot-result (i 0) (slots (fn-rtc-slots s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-rtc-slot posp natp nfix
     default-+-1 default-+-2 commutativity-of-+ unicity-of-0 fix
     (:executable-counterpart binary-+) (:executable-counterpart fn-rtc-s-status)
     (:executable-counterpart nfix) (:executable-counterpart natp)
     (:executable-counterpart unary--))))))
(defthm fn-pth-i-inc-room-next-is-u64
 (implies (fn-rtc-inc-roomp slot) (fn-rtc-u64p (+ 1 (fn-rtc-s-inc slot))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-rtc-inc-roomp fn-rtc-u64p natp (:type-prescription fn-rtc-s-inc)
    default-+-1 default-+-2 (:executable-counterpart expt))))))
(defthm fn-pth-i-runtime-accept-branch
 (implies (fn-pth-i-runtime s1) (fn-pth-i-runtime (mv-nth 0 (fn-pth-accept-branch s1 out q))))
 :hints (("Goal" :use ((:instance fn-pth-i-free-slot-is-dynamic (s s1)))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-accept-branch fn-pth-i-runtime-activate-slot fn-pth-i-runtime-with-mstate
     fn-pth-i-runtime-deliver fn-pth-i-runtime-rearm fn-pth-i-inc-room-next-is-u64
     fn-hld-mv-nth-0-cons car-cons cdr-cons)))))

; From p15c-I-close-use-control.lisp
(defthm fn-pth-i-ordinary-use-control
 (implies (fn-rtc-use-okp u s)
          (and (natp (fn-rtc-get 1 u))
               (fn-rtc-current-p (fn-rtc-get 1 u) (fn-rtc-get 2 u) s)
               (implies (equal (fn-rtc-get 0 u) :close)
                (equal (fn-rtc-s-status (fn-rtc-slot (fn-rtc-get 1 u) s)) :closing))))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-rtc-use-okp fn-rtc-usep nfix natp)))))
(defthm fn-pth-i-close-state-use-control
 (implies (and (fn-rtc-use-okp u s) (member-equal u (fn-rtc-uses s))
               (natp id) (equal (fn-rtc-s-inc (fn-rtc-slot id s)) inc)
               (not (fn-rtc-kind-out-p :close id inc (fn-rtc-uses s))))
          (and (fn-rtc-current-p (nfix (fn-rtc-get 1 u)) (fn-rtc-get 2 u)
                                 (fn-rtc-close-state s id inc))
               (implies (equal (fn-rtc-get 0 u) :close)
                (equal (fn-rtc-s-status
                         (fn-rtc-slot (nfix (fn-rtc-get 1 u)) (fn-rtc-close-state s id inc))) :closing))))
 :rule-classes nil
 :hints (("Goal" :use (fn-pth-i-ordinary-use-control
        (:instance fn-rtc-uses-of-slot-member (uses (fn-rtc-uses s)))
        (:instance fn-rtc-kind-out-of-member (uses (fn-rtc-uses s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-current-p fn-rtc-close-state-slot fn-rtc-slot-accessors nfix natp
     fn-rtc-get-of-cons car-cons cdr-cons (:type-prescription fn-rtc-s-inc)
     (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))
(defthm fn-pth-i-ordinary-use-preserved-by-fields
 (implies (and (fn-rtc-use-okp u s)
               (equal (fn-rtc-config s2) (fn-rtc-config s))
               (equal (fn-rtc-next-op s2) (fn-rtc-next-op s))
               (fn-rtc-current-p (nfix (fn-rtc-get 1 u)) (fn-rtc-get 2 u) s2)
               (implies (equal (fn-rtc-get 0 u) :close)
                (equal (fn-rtc-s-status (fn-rtc-slot (nfix (fn-rtc-get 1 u)) s2)) :closing))
               (implies (fn-rtc-handlep (fn-rtc-u-hd u))
                (and (equal (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s2)
                            (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s))
                     (equal (fn-rtc-holders (fn-rtc-h-buf (fn-rtc-u-hd u))
                                           (fn-rtc-h-gen (fn-rtc-u-hd u)) (fn-rtc-uses s2))
                            (fn-rtc-holders (fn-rtc-h-buf (fn-rtc-u-hd u))
                                           (fn-rtc-h-gen (fn-rtc-u-hd u)) (fn-rtc-uses s))))))
          (fn-rtc-use-okp u s2))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-use-okp)))))

; From p15c-I-close-frames.lisp
(defthm fn-pth-i-listener-use-buffer-index
 (implies (and (fn-pth-i-listener-use u s) (fn-rtc-handlep (fn-rtc-u-hd u)))
          (< (fn-rtc-h-buf (fn-rtc-u-hd u)) (fn-rtc-nbufs (fn-rtc-config s))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-listener-use (:executable-counterpart fn-rtc-handlep))))))
(defthm fn-pth-i-close-state-used-buffer
 (implies (and (fn-rtc-shapep s)
               (or (fn-rtc-use-okp u s) (fn-pth-i-listener-use u s))
               (fn-rtc-handlep (fn-rtc-u-hd u)))
          (equal (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) (fn-rtc-close-state s id inc))
                 (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s)))
 :hints (("Goal"
  :use (fn-rtc-use-okp-lease fn-pth-i-listener-use-handle-is-leased
        fn-rtc-use-okp-buffer-index fn-pth-i-listener-use-buffer-index)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-buffer fn-rtc-close-state-accessors fn-rtc-get-of-release-all
     fn-rtc-leasedp fn-rtc-shapep fn-rtc-get-of-cons nfix natp
     (:type-prescription fn-rtc-h-buf) car-cons cdr-cons
     (:executable-counterpart fn-rtc-get) (:executable-counterpart member-equal)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))
(defthm fn-pth-i-close-state-shapep
 (implies (fn-rtc-shapep s) (fn-rtc-shapep (fn-rtc-close-state s id inc)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-rtc-close-state fn-pth-with-mstate-keeps-shapep fn-pth-with-slot-keeps-shapep
    fn-rtc-shapep fn-rtc-make-accessors fn-rtc-make-record fn-rtc-c-make-shape
    fn-rtc-c-pool-shapep-of-release-all fn-rtc-len-of-release-all fn-rtc-next-op
    nfix natp (:type-prescription fn-rtc-next-op))))))
(defthm fn-pth-i-ordinary-use-close-state
 (implies (and (fn-rtc-shapep s) (fn-rtc-use-okp u s) (member-equal u (fn-rtc-uses s))
               (natp id) (equal (fn-rtc-s-inc (fn-rtc-slot id s)) inc)
               (not (fn-rtc-kind-out-p :close id inc (fn-rtc-uses s))))
          (fn-rtc-use-okp u (fn-rtc-close-state s id inc)))
 :hints (("Goal"
  :use (fn-pth-i-close-state-used-buffer fn-pth-i-close-state-use-control
        (:instance fn-pth-i-ordinary-use-preserved-by-fields (s2 (fn-rtc-close-state s id inc))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-close-state-accessors)))))
(defthm fn-pth-i-listener-use-close-state
 (implies (and (fn-rtc-shapep s) (fn-pth-i-listener-use u s))
          (fn-pth-i-listener-use u (fn-rtc-close-state s id inc)))
 :hints (("Goal" :cases ((fn-rtc-handlep (fn-rtc-u-hd u)))
  :use (fn-pth-i-close-state-used-buffer)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-listener-use fn-rtc-close-state-accessors
     (:executable-counterpart fn-rtc-handlep))))))
(defthm fn-pth-i-uses-close-state-subset
 (implies (and (fn-rtc-shapep s) (fn-pth-i-uses uses s) (subsetp-equal uses (fn-rtc-uses s))
               (natp id) (equal (fn-rtc-s-inc (fn-rtc-slot id s)) inc)
               (not (fn-rtc-kind-out-p :close id inc (fn-rtc-uses s))))
          (fn-pth-i-uses uses (fn-rtc-close-state s id inc)))
 :hints (("Goal" :induct (fn-pth-i-uses uses s)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-uses subsetp-equal fn-pth-i-ordinary-use-close-state fn-pth-i-listener-use-close-state
     car-cons cdr-cons)))))

; From p15c-I-close-pool.lisp
(defthm fn-pth-i-workspace-owner-reconstruct
 (implies (and (fn-pth-i-buffer-ownerp o) (equal (fn-rtc-get 0 o) :workspace))
          (equal (list :workspace (fn-rtc-get 1 o) (fn-rtc-get 2 o)) o))
 :rule-classes nil
 :hints (("Goal" :expand ((len o) (len (cdr o)) (len (cddr o)) (len (cdddr o))
                          (true-listp o) (true-listp (cdr o)) (true-listp (cddr o)) (true-listp (cdddr o))
                          (fn-rtc-get 1 o) (fn-rtc-get 2 o)
                          (fn-rtc-get 1 (cdr o)) (fn-rtc-get 0 o))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-buffer-ownerp len true-listp fn-rtc-get nfix natp zp
     default-+-1 default-+-2 (:type-prescription len)
     associativity-of-+ fold-consts-in-+ (:executable-counterpart binary-+) car-cons cdr-cons car-cdr-elim
     (:executable-counterpart fn-rtc-get) (:executable-counterpart len)
     (:executable-counterpart nfix) (:executable-counterpart zp)
     (:executable-counterpart equal) (:executable-counterpart member-equal))))))
(defthm fn-pth-i-buffer-state-close-state
 (implies (and (natp id) (equal (fn-rtc-s-inc (fn-rtc-slot id s)) inc)
               (fn-pth-i-buffer-state-okp h b s))
          (fn-pth-i-buffer-state-okp h
           (if (equal (fn-rtc-b-owner b) (list :workspace id inc))
               (list (fn-rtc-b-gen b) '(:free) (fn-rtc-b-bytes b)) b)
           (fn-rtc-close-state s id inc)))
 :hints (("Goal"
  :use ((:instance fn-pth-i-workspace-owner-reconstruct (o (fn-rtc-b-owner b))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-buffer-state-okp fn-pth-i-buffer-ownerp fn-rtc-close-state-accessors
     fn-rtc-close-state-slot fn-rtc-buffer-accessors fn-rtc-get-of-cons nfix natp
     car-cons cdr-cons (:executable-counterpart fn-rtc-get)
     (:executable-counterpart equal) (:executable-counterpart member-equal)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))
(defthm fn-pth-i-pool-close-state
 (implies (and (natp id) (equal (fn-rtc-s-inc (fn-rtc-slot id s)) inc)
               (fn-pth-i-pool i pool s))
          (fn-pth-i-pool i (fn-rtc-release-all pool id inc) (fn-rtc-close-state s id inc)))
 :hints (("Goal" :induct (fn-pth-i-pool-index-induct i pool)
  :in-theory (union-theories (theory 'minimal-theory)
   '((:induction fn-pth-i-pool-index-induct) fn-pth-i-pool-unfolds
     fn-rtc-release-all car-cons cdr-cons)))
  ("Subgoal *1/1" :use ((:instance fn-pth-i-buffer-state-close-state (h i) (b (car pool)))))))

; From p15c-I-close-runtime.lisp
(defthm fn-pth-i-draining-slot-record
 (implies (and (fn-pth-i-runtime s) (natp id)
               (equal (fn-rtc-s-inc (fn-rtc-slot id s)) inc)
               (equal (fn-rtc-s-status (fn-rtc-slot id s)) :closing))
          (and (fn-rtc-u64p inc)
               (fn-rtc-slotp (list inc :draining (fn-rtc-s-res (fn-rtc-slot id s))))
               (not (null (fn-rtc-s-res (fn-rtc-slot id s))))))
 :rule-classes nil
 :hints (("Goal"
  :use (fn-pth-i-runtime-slot-facts fn-pth-i-shaped-live-slot-in-range
        (:instance fn-pth-slot-inc-is-u64-from-inc-table (j id))
        (:instance fn-rtc-slotp-resource (slot (fn-rtc-slot id s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-rtc-slotp fn-rtc-get-of-cons len true-listp natp nfix
     fn-rtc-u64p-implies-natp car-cons cdr-cons
     (:executable-counterpart member-equal) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart fn-rtc-s-status) (:executable-counterpart fn-rtc-s-inc) (:executable-counterpart fn-rtc-s-res)
     (:executable-counterpart equal) (:executable-counterpart nfix) (:executable-counterpart zp))))))
(defthm fn-pth-i-runtime-close-state
 (implies (and (fn-pth-i-runtime s) (natp id) (< 1 id)
               (equal (fn-rtc-s-inc (fn-rtc-slot id s)) inc)
               (equal (fn-rtc-s-status (fn-rtc-slot id s)) :closing)
               (not (fn-rtc-kind-out-p :close id inc (fn-rtc-uses s))))
          (fn-pth-i-runtime (fn-rtc-close-state s id inc)))
 :hints (("Goal"
  :use (fn-pth-i-draining-slot-record
        (:instance fn-pth-i-uses-close-state-subset (uses (fn-rtc-uses s)))
        (:instance fn-pth-i-pool-close-state (i 0) (pool (fn-rtc-pool s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-pth-i-close-state-shapep fn-rtc-close-state-accessors fn-rtc-close-state-slot
     fn-rtc-slots-okp-set fn-pth-inc-tablep-set fn-rtc-free-slotp fn-rtc-slot-accessors
     fn-rtc-u64p-implies-natp fn-rtc-subset-reflexive fn-rtc-get-of-cons
     nfix natp (:type-prescription fn-rtc-s-inc) car-cons cdr-cons
     (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))
(defthm fn-pth-close-branch-through-close-state-by-definition
 (equal (fn-pth-close-branch s1 id inc)
        (fn-rtc-rearm (fn-rtc-with-mstate id (fn-pthm-init) (fn-rtc-close-state s1 id inc))))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-close-branch fn-rtc-close-state fn-rtc-with-mstate fn-rtc-with-slot
    fn-rtc-make-accessors fn-rtc-with-accessors fn-rtc-slot
    fn-rtc-c-set-of-set-same fn-rtc-next-op nfix natp
    (:type-prescription fn-rtc-next-op))))))
(defthm fn-pth-i-runtime-close-branch
 (implies (and (fn-pth-i-runtime s1) (natp id) (< 1 id)
               (equal (fn-rtc-s-inc (fn-rtc-slot id s1)) inc)
               (equal (fn-rtc-s-status (fn-rtc-slot id s1)) :closing)
               (not (fn-rtc-kind-out-p :close id inc (fn-rtc-uses s1))))
          (fn-pth-i-runtime (mv-nth 0 (fn-pth-close-branch s1 id inc))))
 :hints (("Goal" :use (fn-pth-close-branch-through-close-state-by-definition)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime-close-state fn-pth-i-runtime-with-mstate fn-pth-i-runtime-rearm)))))

; From p15c-I-acting-close.lisp
(defthm fn-pth-i-kind-out-remove-matching
 (implies (and (fn-pth-i-uses uses s) (fn-rtc-find-use key uses)
               (not (member-eq (fn-rtc-get 0 (fn-rtc-find-use key uses)) '(:hand :pool))))
  (let ((u (fn-rtc-find-use key uses)))
   (not (fn-rtc-kind-out-p (fn-rtc-get 0 u) (fn-rtc-get 1 u) (fn-rtc-get 2 u)
                          (fn-rtc-remove-use key uses)))))
 :hints (("Goal" :induct (fn-rtc-remove-use key uses)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-uses fn-rtc-remove-use fn-rtc-find-use fn-rtc-remove-use-kind-subset
     fn-rtc-kind-out-of-found-use fn-rtc-kind-out-p car-cons cdr-cons)))))
(defthm fn-pth-i-end-use-removes-event-kind
 (implies (and (fn-pth-i-runtime s) (fn-rtc-completionp e)
               (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))
               (not (member-eq (fn-rtc-e-kind e) '(:hand :pool))))
          (not (fn-rtc-kind-out-p (fn-rtc-e-kind e) (fn-rtc-e-id e) (fn-rtc-e-inc e)
                                  (fn-rtc-uses (fn-rtc-end-use s e)))))
 :hints (("Goal"
  :use ((:instance fn-rtc-matching-use-fields (uses (fn-rtc-uses s)))
        (:instance fn-pth-i-kind-out-remove-matching (key (fn-rtc-key e)) (uses (fn-rtc-uses s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime-control-by-definition fn-rtc-uses-of-end-use)))))
(defthm fn-pth-i-acting-close-is-dynamic
 (implies (and (fn-pth-i-runtime s) (fn-rtc-acts-on-p s e) (equal (fn-rtc-e-kind e) :close))
          (and (natp (fn-rtc-e-id e)) (< 1 (fn-rtc-e-id e))
               (fn-rtc-completionp e) (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))
               (not (fn-rtc-hand-delivers-p s e))
               (equal (fn-rtc-s-status (fn-rtc-slot (fn-rtc-e-id e) s)) :closing)
               (equal (fn-rtc-s-inc (fn-rtc-slot (fn-rtc-e-id e) s)) (fn-rtc-e-inc e))))
 :rule-classes nil
 :hints (("Goal" :cases ((equal (fn-rtc-e-id e) 0) (equal (fn-rtc-e-id e) 1)) :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-runtime fn-rtc-acts-on-p fn-rtc-hand-delivers-p
    (:type-prescription fn-rtc-e-id) natp (:executable-counterpart fn-rtc-s-status)
    (:executable-counterpart equal))))))
(defthm fn-pth-i-acting-close-after-end-use
 (implies (and (fn-pth-i-runtime s) (fn-rtc-acts-on-p s e) (equal (fn-rtc-e-kind e) :close))
  (let ((s1 (fn-rtc-end-use s e)))
   (and (natp (fn-rtc-e-id e)) (< 1 (fn-rtc-e-id e))
        (equal (fn-rtc-s-status (fn-rtc-slot (fn-rtc-e-id e) s1)) :closing)
        (equal (fn-rtc-s-inc (fn-rtc-slot (fn-rtc-e-id e) s1)) (fn-rtc-e-inc e))
        (not (fn-rtc-kind-out-p :close (fn-rtc-e-id e) (fn-rtc-e-inc e) (fn-rtc-uses s1))))))
 :rule-classes nil
 :hints (("Goal" :use (fn-pth-i-acting-close-is-dynamic fn-pth-i-end-use-removes-event-kind)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-slot-of-end-use-when-acting (:executable-counterpart member-equal) (:executable-counterpart equal))))))
(defthm fn-pth-i-runtime-step
 (implies (fn-pth-i-runtime s) (fn-pth-i-runtime (mv-nth 0 (fn-pth-step s e q))))
 :hints (("Goal" :use (fn-pth-i-acting-close-after-end-use)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-step fn-pth-step* fn-pth-i-runtime-end-use fn-pth-i-runtime-rearm
     fn-pth-i-runtime-deliver fn-pth-i-runtime-accept-branch fn-pth-i-runtime-close-branch
     fn-pth-i-runtime-grant fn-hld-mv-nth-0-cons car-cons cdr-cons)))))

; Joint I: foreign requests and completion-to-machine storage/protocol bridge.

; From p15c-I-joint-requests.lisp
(defthm fn-pth-i-foreign-requests
 (implies (and (fn-pth-i s) (not (equal id 1)))
          (fn-pth-i (mv-nth 0 (fn-rtc-requests rs id inc s))))
 :hints (("Goal"
  :use (fn-pth-i-runtime-and-post-state-by-definition
        (:instance fn-pth-i-runtime-and-post-state-by-definition
          (s (mv-nth 0 (fn-rtc-requests rs id inc s)))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime-requests fn-pth-i-foreign-requests-preserve-owner-post-state)))))

; From p15c-I-post-storage.lisp
; Derive the storage part from I's frozen present-state conjunction.
(make-event
 (let* ((ev (get-event 'fn-pth-i-post-state (w state))) (body (car (last ev)))
        (bindings (cadr body)) (clauses (cdr (caddr body)))
        (owner '(fn-pth-i-owner-uses (fn-rtc-uses s) m))
        (out '(implies (fn-ptx-expected m)
                       (fn-rtc-kind-out-p (fn-ptx-expected m) 1 1 (fn-rtc-uses s)))))
  (if (and (eq (car body) 'let*) (eq (car (caddr body)) 'and)
           (member-equal owner clauses) (member-equal out clauses))
   (value `(defun fn-pth-i-post-storage (m s)
     (declare (xargs :guard t :verify-guards nil))
     (let* ,bindings (and ,@(remove-equal out (remove-equal owner clauses))))))
   (er soft 'fn-pth-i-post-storage "I post conjunction shape changed."))))
(defthm fn-pth-i-post-storage-and-protocol-by-definition
 (equal (fn-pth-i-post-state m s)
        (and (fn-pth-i-post-storage m s) (fn-pth-i-owner-uses (fn-rtc-uses s) m)
             (implies (fn-ptx-expected m)
                      (fn-rtc-kind-out-p (fn-ptx-expected m) 1 1 (fn-rtc-uses s)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-post-state fn-pth-i-post-storage)))))
(defthm fn-pth-i-visible-buffer-config-pool-congruence
 (implies (and (equal (fn-rtc-config s2) (fn-rtc-config s))
               (equal (fn-rtc-pool s2) (fn-rtc-pool s)))
          (equal (fn-pth-i-visible-buffer h s2 leasedp) (fn-pth-i-visible-buffer h s leasedp)))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-visible-buffer fn-rtc-buffer)))))
(defthm fn-pth-i-post-config-pool-congruence
 (implies (and (equal (fn-rtc-config s2) (fn-rtc-config s))
               (equal (fn-rtc-pool s2) (fn-rtc-pool s)))
          (equal (fn-pth-i-post p s2 leasedp) (fn-pth-i-post p s leasedp)))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-post fn-pth-i-visible-buffer fn-rtc-buffer)))))
(defthm fn-pth-i-queue-config-pool-congruence
 (implies (and (equal (fn-rtc-config s2) (fn-rtc-config s))
               (equal (fn-rtc-pool s2) (fn-rtc-pool s)))
          (equal (fn-pth-i-queue ps s2 used) (fn-pth-i-queue ps s used)))
 :rule-classes nil
 :hints (("Goal" :induct (fn-pth-i-queue ps s used)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-queue fn-pth-i-post fn-pth-i-visible-buffer fn-rtc-buffer)))))
(defthm fn-pth-i-post-storage-config-pool-congruence
 (implies (and (equal (fn-rtc-config s2) (fn-rtc-config s))
               (equal (fn-rtc-pool s2) (fn-rtc-pool s)))
          (equal (fn-pth-i-post-storage m s2) (fn-pth-i-post-storage m s)))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-pth-i-queue-config-pool-congruence (ps (fn-ptx-q m))
    (used (append (if (member-eq (fn-ptx-ph m) '(:reading :hashing :extending :extsyncing :payload-writing :log-writing :committing))
                       (list (fn-ptx-cur-bp (fn-ptx-cur m))) nil)
                  (if (consp (fn-ptx-b1 m)) (list (fn-ptx-buf-h (fn-ptx-b1 m)) (fn-ptx-buf-h (fn-ptx-b3 m))) nil)))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-post-storage fn-pth-i-post fn-pth-i-visible-buffer fn-rtc-buffer)))))
(defthm fn-pth-i-post-storage-request
 (implies (and (not (equal id 1)) (fn-pth-i-post-storage m s))
          (fn-pth-i-post-storage m (mv-nth 0 (fn-rtc-request r id inc s))))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-post-storage fn-pth-i-queue-request fn-pth-i-post-request fn-pth-i-visible-buffer-request
     fn-pth-i-post fn-pth-i-visible-buffer fn-rtc-view-own-p
     fn-pth-request-visible-buffer-frame fn-rtc-request-config-frame)))))
(defthm fn-pth-i-post-storage-requests
 (implies (and (not (equal id 1)) (fn-pth-i-post-storage m s))
          (fn-pth-i-post-storage m (mv-nth 0 (fn-rtc-requests rs id inc s))))
 :hints (("Goal" :induct (fn-rtc-requests rs id inc s)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-requests fn-pth-i-post-storage-request fn-hld-mv-nth-0-cons car-cons cdr-cons)))))
(defthm fn-pth-i-post-storage-rearm
 (equal (fn-pth-i-post-storage m (mv-nth 0 (fn-rtc-rearm s))) (fn-pth-i-post-storage m s))
 :hints (("Goal" :use ((:instance fn-pth-i-post-storage-config-pool-congruence
                        (s2 (mv-nth 0 (fn-rtc-rearm s)))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-rearm-pool-and-mstates-frame fn-rtc-rearm-frame)))))

; From p15c-I-storage-buffer-frame.lisp
(defun fn-pth-i-owner-buffer-framep (old new)
 (declare (xargs :guard t :verify-guards nil))
 (and (implies (equal (fn-rtc-b-owner old) '(:workspace 1 1)) (equal new old))
      (implies (equal (fn-rtc-b-owner old) '(:leased 1 1 :out))
       (and (equal (fn-rtc-b-bytes new) (fn-rtc-b-bytes old))
            (or (equal (fn-rtc-b-owner new) '(:workspace 1 1))
                (equal (fn-rtc-b-owner new) '(:leased 1 1 :out)))))))
(verify-guards fn-pth-i-owner-buffer-framep)
(defthm fn-pth-i-visible-buffer-of-storage-update
 (implies (and (natp h) (fn-pth-i-owner-buffer-framep (fn-rtc-buffer h s) b)
               (fn-pth-i-visible-buffer j s leasedp))
          (fn-pth-i-visible-buffer j (fn-rtc-with-buffer h b s) leasedp))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-owner-buffer-framep fn-pth-i-visible-buffer fn-rtc-buffer-of-with
    fn-rtc-with-accessors nfix natp)))))
(defthm fn-pth-i-workspace-of-storage-update
 (implies (and (natp h) (fn-pth-i-owner-buffer-framep (fn-rtc-buffer h s) b)
               (natp j) (equal (fn-rtc-b-owner (fn-rtc-buffer j s)) '(:workspace 1 1)))
          (equal (fn-rtc-buffer j (fn-rtc-with-buffer h b s)) (fn-rtc-buffer j s)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-owner-buffer-framep fn-rtc-buffer-of-with nfix natp)))))
(defthm fn-pth-i-visible-bytes-of-storage-update
 (implies (and (natp h) (fn-pth-i-owner-buffer-framep (fn-rtc-buffer h s) b)
               (natp j) (fn-rtc-view-own-p (fn-rtc-b-owner (fn-rtc-buffer j s)) 1 1))
          (equal (fn-rtc-b-bytes (fn-rtc-buffer j (fn-rtc-with-buffer h b s)))
                 (fn-rtc-b-bytes (fn-rtc-buffer j s))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-owner-buffer-framep fn-rtc-view-own-p fn-rtc-buffer-of-with nfix natp)))))
(defthm fn-pth-i-post-of-storage-update
 (implies (and (natp h) (fn-pth-i-owner-buffer-framep (fn-rtc-buffer h s) b)
               (fn-pth-i-post p s leasedp))
          (fn-pth-i-post p (fn-rtc-with-buffer h b s) leasedp))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-post fn-pth-i-visible-buffer-of-storage-update fn-rtc-with-accessors)))))
(defthm fn-pth-i-queue-of-storage-update
 (implies (and (natp h) (fn-pth-i-owner-buffer-framep (fn-rtc-buffer h s) b)
               (fn-pth-i-queue ps s used))
          (fn-pth-i-queue ps (fn-rtc-with-buffer h b s) used))
 :hints (("Goal" :induct (fn-pth-i-queue ps s used)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-queue fn-pth-i-post-of-storage-update fn-pth-i-post fn-pth-i-visible-buffer
     fn-pth-i-workspace-of-storage-update fn-rtc-with-accessors)))))
(defthm fn-pth-i-post-storage-of-buffer-update
 (implies (and (natp h) (fn-pth-i-owner-buffer-framep (fn-rtc-buffer h s) b)
               (fn-pth-i-post-storage m s))
          (fn-pth-i-post-storage m (fn-rtc-with-buffer h b s)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-pth-i-visible-buffer-of-storage-update (j (fn-ptx-cur-bp (fn-ptx-cur m))) (leasedp (fn-ptx-in-flight-p (fn-ptx-ph m))))
        (:instance fn-pth-i-visible-bytes-of-storage-update (j (fn-ptx-cur-bp (fn-ptx-cur m))))
        (:instance fn-pth-i-visible-buffer-of-storage-update (j (fn-ptx-buf-h (fn-ptx-b1 m))) (leasedp (fn-ptx-in-flight-p (fn-ptx-ph m))))
        (:instance fn-pth-i-visible-bytes-of-storage-update (j (fn-ptx-buf-h (fn-ptx-b1 m))))
        (:instance fn-pth-i-visible-buffer-of-storage-update (j (fn-ptx-buf-h (fn-ptx-b3 m))) (leasedp (fn-ptx-in-flight-p (fn-ptx-ph m))))
        (:instance fn-pth-i-visible-bytes-of-storage-update (j (fn-ptx-buf-h (fn-ptx-b3 m)))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-post-storage fn-pth-i-queue-of-storage-update
     fn-pth-i-post-of-storage-update fn-pth-i-visible-buffer-of-storage-update
     fn-pth-i-post fn-pth-i-visible-buffer fn-rtc-view-own-p
     fn-pth-i-workspace-of-storage-update fn-pth-i-visible-bytes-of-storage-update
     fn-rtc-with-accessors fn-ptx-in-flight-p
     (:executable-counterpart member-equal) (:executable-counterpart equal))))))

; From p15c-I-storage-return.lisp
(defthm fn-pth-i-owner-output-lease-is-not-input
 (implies (and (or (fn-rtc-use-okp u s) (fn-pth-i-listener-use u s))
               (fn-rtc-handlep (fn-rtc-u-hd u))
               (equal (fn-rtc-b-owner (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s)) '(:leased 1 1 :out)))
          (not (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*)))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-rtc-use-okp fn-pth-i-listener-use fn-rtc-get-of-cons member-equal
    car-cons cdr-cons (:executable-counterpart fn-rtc-get)
    (:executable-counterpart equal) (:executable-counterpart member-equal)
    (:executable-counterpart fn-rtc-buffered-kind-p) (:executable-counterpart fn-rtc-handlep)
    (:executable-counterpart nfix) (:executable-counterpart zp))))))
(defthm fn-pth-i-owner-output-lease-return
 (implies (and (fn-pth-i-runtime s) (equal (fn-rtc-b-owner b) '(:leased 1 1 :out))
               (not (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*)))
          (equal (fn-rtc-lease-return u e b s)
                 (list (+ 1 (fn-rtc-b-gen b)) '(:workspace 1 1) (fn-rtc-b-bytes b))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-runtime fn-rtc-lease-return fn-rtc-handed-to-live-p fn-rtc-current-p
    fn-rtc-get-of-cons car-cons cdr-cons
    (:executable-counterpart fn-rtc-get) (:executable-counterpart fn-rtc-s-inc)
    (:executable-counterpart fn-rtc-s-status) (:executable-counterpart equal)
    (:executable-counterpart member-equal) (:executable-counterpart nfix)
    (:executable-counterpart zp))))))
(defthm fn-pth-i-lease-return-owner-buffer-frame
 (implies (and (fn-pth-i-runtime s)
               (or (fn-rtc-use-okp u s) (fn-pth-i-listener-use u s))
               (fn-rtc-handlep (fn-rtc-u-hd u)))
          (fn-pth-i-owner-buffer-framep (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s)
           (fn-rtc-lease-return u e (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s) s)))
 :hints (("Goal"
  :use (fn-rtc-use-okp-lease fn-pth-i-listener-use-handle-is-leased fn-pth-i-owner-output-lease-is-not-input)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-owner-buffer-framep fn-rtc-leasedp fn-pth-i-owner-output-lease-return
     fn-rtc-buffer-accessors fn-rtc-get-of-cons car-cons cdr-cons
     (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
     (:executable-counterpart member-equal) (:executable-counterpart nfix) (:executable-counterpart zp))))))

; From p15c-I-storage-end-use.lisp
(defthm fn-pth-i-post-storage-with-uses
 (equal (fn-pth-i-post-storage m (fn-rtc-with-uses uses s)) (fn-pth-i-post-storage m s))
 :hints (("Goal" :use ((:instance fn-pth-i-post-storage-config-pool-congruence
                        (s2 (fn-rtc-with-uses uses s))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-with-accessors)))))
(defthm fn-pth-i-post-storage-retire
 (equal (fn-pth-i-post-storage m (fn-rtc-retire-drained id s)) (fn-pth-i-post-storage m s))
 :hints (("Goal" :use ((:instance fn-pth-i-post-storage-config-pool-congruence
                        (s2 (fn-rtc-retire-drained id s))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-retire-drained fn-rtc-with-accessors)))))
(defthm fn-pth-i-post-storage-end-lease-after-removal
 (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s)
               (fn-rtc-find-use key (fn-rtc-uses s)))
          (fn-pth-i-post-storage m
           (fn-rtc-end-lease (fn-rtc-find-use key (fn-rtc-uses s)) e
            (fn-rtc-with-uses (fn-rtc-remove-use key (fn-rtc-uses s)) s))))
 :hints (("Goal"
  :use ((:instance fn-pth-i-uses-member (uses (fn-rtc-uses s))
          (u (fn-rtc-find-use key (fn-rtc-uses s))))
        (:instance fn-rtc-find-use-is-member (k key) (uses (fn-rtc-uses s)))
        (:instance fn-pth-i-lease-return-owner-buffer-frame (u (fn-rtc-find-use key (fn-rtc-uses s))))
        (:instance fn-pth-i-post-storage-of-buffer-update
          (h (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s)))))
          (b (fn-rtc-lease-return (fn-rtc-find-use key (fn-rtc-uses s)) e
              (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s)))) s) s))
          (s (fn-rtc-with-uses (fn-rtc-remove-use key (fn-rtc-uses s)) s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-end-lease fn-rtc-with-accessors fn-rtc-buffer-of-with fn-rtc-lease-return-of-with-uses
     fn-pth-i-post-storage-with-uses fn-pth-i-runtime-control-by-definition
     (:type-prescription fn-rtc-h-buf) natp)))))
(defthm fn-pth-i-post-storage-end-use
 (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s))
          (fn-pth-i-post-storage m (fn-rtc-end-use s e)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-rtc-end-use fn-pth-i-post-storage-end-lease-after-removal fn-pth-i-post-storage-retire)))))
(defthm fn-pth-i-owner-uses-remove
 (implies (fn-pth-i-owner-uses uses m)
          (fn-pth-i-owner-uses (fn-rtc-remove-use key uses) m))
 :hints (("Goal" :induct (fn-rtc-remove-use key uses)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-remove-use fn-pth-i-owner-uses car-cons cdr-cons)))))
(defthm fn-pth-i-before-machine-after-end-use
 (implies (fn-pth-i s)
  (let ((s1 (fn-rtc-end-use s e)) (m (fn-rtc-mstate 1 s)))
   (and (fn-pth-i-runtime s1) (fn-pth-i-post-storage m s1)
        (fn-pth-i-owner-uses (fn-rtc-uses s1) m))))
 :rule-classes nil
 :hints (("Goal" :use (fn-pth-i-runtime-and-post-state-by-definition
                        (:instance fn-pth-i-post-storage-and-protocol-by-definition (m (fn-rtc-mstate 1 s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime-end-use fn-pth-i-post-storage-end-use fn-pth-i-owner-uses-remove fn-rtc-uses-of-end-use)))))

; Joint I: common owner-machine helpers and actual owner opened step.

(defthm fn-pth-i-queue-nil
 (fn-pth-i-queue nil s used)
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pth-i-queue)))))

(defthm fn-pth-i-opened-requests-empty
 (implies (equal (fn-rtc-get 0 ev) :opened)
          (not (mv-nth 1 (fn-ptx-step m ev st q))))
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '(fn-ptx-step fn-ptx-step1 fn-rtc-get-of-cons car-cons cdr-cons
    (:executable-counterpart equal) (:executable-counterpart nfix) (:executable-counterpart zp))))))

(defthm fn-pth-i-owner-uses-member
 (implies (and (fn-pth-i-owner-uses uses m) (member-equal u uses)
               (equal (fn-rtc-get 1 u) 1))
          (and (equal (fn-rtc-get 2 u) 1)
               (or (equal (fn-rtc-get 0 u) :hand)
                   (and (equal (fn-ptx-ph m) :closed) (equal (fn-rtc-get 0 u) :opened))
                   (and (fn-ptx-expected m) (equal (fn-rtc-get 0 u) (fn-ptx-expected m))))))
 :hints (("Goal" :induct (member-equal u uses)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-owner-uses member-equal car-cons cdr-cons)))))

(defthm fn-pth-i-owner-kind-out-is-protocol-kind
 (implies (and (fn-pth-i-owner-uses uses m) (not (equal kind :hand))
               (not (and (equal (fn-ptx-ph m) :closed) (equal kind :opened)))
               (not (and (fn-ptx-expected m) (equal kind (fn-ptx-expected m)))))
          (not (fn-rtc-kind-out-p kind 1 inc uses)))
 :hints (("Goal" :induct (fn-pth-i-owner-uses uses m)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-owner-uses fn-rtc-kind-out-p car-cons cdr-cons)))))

(defthm fn-pth-i-owner-uses-only-hands-after-protocol-removed
 (implies (and (fn-pth-i-owner-uses uses m)
               (not (fn-rtc-kind-out-p (fn-ptx-expected m) 1 1 uses))
               (not (fn-rtc-kind-out-p :opened 1 1 uses)))
          (fn-pth-i-owner-uses uses m2))
 :hints (("Goal" :induct (fn-pth-i-owner-uses uses m)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-owner-uses fn-rtc-kind-out-p car-cons cdr-cons)))))

(defthm fn-pth-i-owner-never-waits-for-pool
 (implies (fn-pth-i-owner-uses uses m)
          (and (not (fn-rtc-kind-out-p :wait 1 inc uses))
               (not (fn-rtc-kind-out-p :pool 1 inc uses))))
 :hints (("Goal"
  :use ((:instance fn-pth-i-owner-kind-out-is-protocol-kind (kind :wait))
        (:instance fn-pth-i-owner-kind-out-is-protocol-kind (kind :pool)))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-ptx-expected (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-pth-i-ptx-okp-m0
 (implies (fn-ptx-okp m) (fn-ptx-okp (fn-ptx-chg m :committed nil)))
 :hints (("Goal" :use ((:instance fn-ptx-step-keeps-ok (ev nil) (st nil) (q 0)))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-ptx-okp-wfp fn-ptx-step fn-ptx-step1 car-cons cdr-cons mv-nth
     (:executable-counterpart fn-rtc-get) (:executable-counterpart fn-rtc-ev-id)
     (:executable-counterpart fn-rtc-ev-inc) (:executable-counterpart equal)
     (:executable-counterpart member-equal) (:executable-counterpart nfix)
     (:executable-counterpart zp) (:executable-counterpart binary-+))))))

(defthm fn-pth-i-ptx-m0-nmsg
 (equal (fn-ptx-nmsg (fn-ptx-chg m :committed nil)) (fn-ptx-nmsg m))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-ptx-nmsg fn-ptx-spans fn-ptx-accessors-of-mk)))))

(defthm fn-pth-i-ptx-m0-elen
 (equal (fn-ptx-elen (fn-ptx-chg m :committed nil)) (fn-ptx-elen m))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-ptx-elen fn-pth-i-ptx-m0-nmsg fn-ptx-accessors-of-mk)))))

(defthm fn-pth-i-post-storage-m0
 (implies (fn-pth-i-post-storage m s)
          (fn-pth-i-post-storage (fn-ptx-chg m :committed nil) s))
 :hints (("Goal"
  :use (fn-pth-i-ptx-okp-m0)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-post-storage fn-pth-i-ptx-m0-nmsg fn-pth-i-ptx-m0-elen
     fn-ptx-elen fn-ptx-nmsg-of-mk fn-ptx-nmsg-is-g
     fn-ptx-accessors-of-mk nfix natp (:type-prescription fn-ptx-ext)
     (:type-prescription fn-ptx-nxt) (:executable-counterpart nfix))))))

(defthm fn-pth-i-post-storage-machine-facts
 (implies (fn-pth-i-post-storage m s) (fn-ptx-okp m))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pth-i-post-storage)))))

(defthm fn-pth-i-opened-storage-from-machine-checks
 (implies (and (fn-ptx-okp (fn-ptx-opened kd ext geo))
               (fn-cbor-octet-listp (fn-ptx-kd-last kd)) (< (nfix ext) (expt 2 64)))
          (fn-pth-i-post-storage (fn-ptx-opened kd ext geo) s))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-post-storage fn-ptx-opened fn-ptx-accessors-of-mk fn-pth-i-queue-nil
    fn-ptx-in-flight-p (:executable-counterpart member-equal) (:executable-counterpart equal))))))

(defthm fn-pth-i-opened-kd
 (equal (fn-ptx-kd (fn-ptx-opened kd ext geo)) kd)
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-ptx-opened fn-ptx-accessors-of-mk)))))

(defthm fn-pth-i-post-storage-opened
 (implies (and (fn-pth-i-post-storage m s) (equal (fn-rtc-get 0 ev) :opened))
          (fn-pth-i-post-storage (mv-nth 0 (fn-ptx-step m ev st q)) s))
 :hints (("Goal" :use (fn-ptx-step-keeps-ok fn-pth-i-post-storage-machine-facts fn-pth-i-post-storage-m0)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-ptx-okp-wfp fn-ptx-step fn-ptx-step1
     fn-pth-i-opened-storage-from-machine-checks fn-pth-i-opened-kd fn-rtc-get-of-cons
     nfix natp (:type-prescription nfix) car-cons cdr-cons
     (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))

(defthm fn-pth-i-post-state-with-mstate
 (equal (fn-pth-i-post-state m (fn-rtc-with-mstate id m2 s)) (fn-pth-i-post-state m s))
 :hints (("Goal"
  :use (fn-pth-i-post-storage-and-protocol-by-definition
        (:instance fn-pth-i-post-storage-and-protocol-by-definition (s (fn-rtc-with-mstate id m2 s)))
        (:instance fn-pth-i-post-storage-config-pool-congruence (s2 (fn-rtc-with-mstate id m2 s))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-with-accessors)))))

(defthm fn-pth-i-owner-machine-index
 (implies (fn-pth-i-runtime s) (< 1 (len (fn-rtc-mstates s))))
 :hints (("Goal" :use ((:instance fn-pth-i-shaped-live-slot-in-range (id 1)))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-rtc-shapep (:executable-counterpart fn-rtc-s-status)
     (:executable-counterpart member-equal) (:executable-counterpart natp))))))

(defthm fn-pth-i-no-requests-owner-deliver
 (let ((r (fn-pth-m-step (fn-rtc-mstate 1 s) ev (fn-rtc-view-state 1 1 s) (nfix q))))
  (implies (and (fn-pth-i-runtime s) (not (mv-nth 1 r)) (fn-pth-i-post-state (mv-nth 0 r) s))
           (fn-pth-i (mv-nth 0 (fn-pth-deliver s 1 1 ev q)))))
 :hints (("Goal"
  :use ((:instance fn-pth-i-runtime-and-post-state-by-definition
          (s (mv-nth 0 (fn-pth-deliver s 1 1 ev q)))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-deliver fn-rtc-view-state fn-rtc-requests fn-pth-i-runtime-with-mstate fn-pth-i-post-state-with-mstate
     fn-pth-i-owner-machine-index fn-rtc-mstate-of-with fn-hld-mv-nth-0-cons
     car-cons cdr-cons (:executable-counterpart nfix) (:executable-counterpart natp))))))

(defthm fn-pth-i-opened-closed-step-has-no-expected
 (implies (and (equal (fn-ptx-ph m) :closed) (equal (fn-rtc-get 0 ev) :opened))
          (not (fn-ptx-expected (mv-nth 0 (fn-ptx-step m ev st q)))))
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '(fn-ptx-step fn-ptx-step1 fn-ptx-broken fn-ptx-opened fn-ptx-expected
    fn-ptx-accessors-of-mk car-cons cdr-cons (:executable-counterpart equal)
    (:executable-counterpart member-equal) (:executable-counterpart nfix) (:executable-counterpart zp))))))

(defthm fn-pth-i-owner-opened-use-is-closed
 (implies (and (fn-pth-i s) (fn-rtc-completionp e)
               (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))
               (equal (fn-rtc-e-kind e) :opened) (equal (fn-rtc-e-id e) 1))
          (and (equal (fn-rtc-e-inc e) 1) (equal (fn-ptx-ph (fn-rtc-mstate 1 s)) :closed)))
 :rule-classes nil
 :hints (("Goal"
  :use (fn-pth-i-runtime-and-post-state-by-definition
        (:instance fn-pth-i-post-storage-and-protocol-by-definition (m (fn-rtc-mstate 1 s)))
        (:instance fn-rtc-matching-use-fields (uses (fn-rtc-uses s)))
        (:instance fn-rtc-find-use-is-member (k (fn-rtc-key e)) (uses (fn-rtc-uses s)))
        (:instance fn-pth-i-owner-uses-member (m (fn-rtc-mstate 1 s)) (uses (fn-rtc-uses s))
          (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-ptx-expected (:executable-counterpart member-equal) (:executable-counterpart equal))))))

(defthm fn-pth-i-owner-opened-protocol-after-end-use
 (implies (and (fn-pth-i s) (fn-rtc-completionp e)
               (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))
               (equal (fn-rtc-e-kind e) :opened) (equal (fn-rtc-e-id e) 1))
          (fn-pth-i-owner-uses (fn-rtc-uses (fn-rtc-end-use s e)) m2))
 :hints (("Goal"
  :use (fn-pth-i-owner-opened-use-is-closed fn-pth-i-before-machine-after-end-use
        fn-pth-i-runtime-and-post-state-by-definition
        (:instance fn-pth-i-end-use-removes-event-kind)
        (:instance fn-pth-i-owner-uses-only-hands-after-protocol-removed
          (uses (fn-rtc-uses (fn-rtc-end-use s e))) (m (fn-rtc-mstate 1 s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-owner-kind-out-is-protocol-kind fn-ptx-expected
     (:executable-counterpart member-equal) (:executable-counterpart equal))))))

(defthm fn-pth-i-mstate-of-end-use
 (equal (fn-rtc-mstate j (fn-rtc-end-use s e)) (fn-rtc-mstate j s))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-rtc-end-use fn-rtc-end-lease fn-rtc-retire-drained fn-rtc-mstate-of-with)))))

(defthm fn-pth-i-owner-opened-post-state
 (let ((m2 (mv-nth 0 (fn-ptx-step (fn-rtc-mstate 1 s) ev st q))))
  (implies (and (fn-pth-i s) (fn-rtc-completionp e)
                (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))
                (equal (fn-rtc-e-kind e) :opened) (equal (fn-rtc-e-id e) 1)
                (equal (fn-rtc-get 0 ev) :opened))
           (fn-pth-i-post-state m2 (fn-rtc-end-use s e))))
 :hints (("Goal"
  :use (fn-pth-i-owner-opened-use-is-closed fn-pth-i-before-machine-after-end-use
        (:instance fn-pth-i-post-storage-opened (m (fn-rtc-mstate 1 s)) (s (fn-rtc-end-use s e)))
        (:instance fn-pth-i-opened-closed-step-has-no-expected (m (fn-rtc-mstate 1 s)))
        (:instance fn-pth-i-owner-opened-protocol-after-end-use
          (m2 (mv-nth 0 (fn-ptx-step (fn-rtc-mstate 1 s) ev st q))))
        (:instance fn-pth-i-post-storage-and-protocol-by-definition (s (fn-rtc-end-use s e))
          (m (mv-nth 0 (fn-ptx-step (fn-rtc-mstate 1 s) ev st q)))))
  :in-theory (theory 'minimal-theory))))

(defthm fn-pth-i-owner-opened-delivery
 (implies (and (fn-pth-i s) (fn-rtc-completionp e)
               (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))
               (equal (fn-rtc-e-kind e) :opened) (equal (fn-rtc-e-id e) 1)
               (equal (fn-rtc-get 0 ev) :opened)
               (equal (fn-rtc-ev-id ev) 1))
          (fn-pth-i (mv-nth 0 (fn-pth-deliver (fn-rtc-end-use s e) 1 1 ev q))))
 :hints (("Goal"
  :use (fn-pth-i-before-machine-after-end-use
        (:instance fn-pth-i-no-requests-owner-deliver (s (fn-rtc-end-use s e)))
        (:instance fn-pth-i-owner-opened-post-state (st (fn-rtc-view-state 1 1 (fn-rtc-end-use s e))) (q (nfix q))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-m-step fn-pthm-step fn-pth-i-mstate-of-end-use fn-pth-i-opened-requests-empty)))))

(defthm fn-pth-i-owner-kind-out-rearm-frame
 (equal (fn-rtc-kind-out-p kind 1 1 (fn-rtc-uses (mv-nth 0 (fn-rtc-rearm s))))
        (fn-rtc-kind-out-p kind 1 1 (fn-rtc-uses s)))
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '(fn-rtc-rearm fn-rtc-arm-accept fn-rtc-arm-grant fn-rtc-issue-frame
    fn-rtc-kind-out-p fn-rtc-get-of-cons fn-hld-mv-nth-0-cons car-cons cdr-cons
    (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
    (:executable-counterpart nfix) (:executable-counterpart zp))))))

(defthm fn-pth-i-rearm
 (implies (fn-pth-i s) (fn-pth-i (mv-nth 0 (fn-rtc-rearm s))))
 :hints (("Goal"
  :use (fn-pth-i-runtime-and-post-state-by-definition
        (:instance fn-pth-i-runtime-and-post-state-by-definition (s (mv-nth 0 (fn-rtc-rearm s))))
        (:instance fn-pth-i-post-storage-and-protocol-by-definition (m (fn-rtc-mstate 1 s)))
        (:instance fn-pth-i-post-storage-and-protocol-by-definition (m (fn-rtc-mstate 1 s))
          (s (mv-nth 0 (fn-rtc-rearm s)))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime-rearm fn-pth-i-post-storage-rearm fn-pth-i-owner-uses-rearm
     fn-pth-i-owner-kind-out-rearm-frame fn-rtc-rearm-frame)))))

(defthm fn-pth-i-no-requests-deliver-refusals
 (implies (not (mv-nth 1 (fn-pth-m-step (fn-rtc-mstate id s) ev
                                       (fn-rtc-view-state id inc s) (nfix q))))
          (not (mv-nth 2 (fn-pth-deliver s id inc ev q))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-deliver fn-rtc-view-state fn-rtc-requests mv-nth car-cons cdr-cons
    (:executable-counterpart zp) (:executable-counterpart nfix) (:executable-counterpart binary-+))))))

(defthm fn-pth-i-mv-nth-2-cons-by-definition
 (equal (mv-nth 2 (cons a (cons b (cons c d)))) c)
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(mv-nth car-cons cdr-cons (:executable-counterpart zp)
    (:executable-counterpart nfix) (:executable-counterpart binary-+))))))

(defthm fn-pth-i-owner-opened-step
 (implies (and (fn-pth-i s) (fn-rtc-acts-on-p s e)
               (equal (fn-rtc-e-kind e) :opened) (equal (fn-rtc-e-id e) 1))
          (and (fn-pth-i (mv-nth 0 (fn-pth-step s e q)))
               (not (mv-nth 2 (fn-pth-step* s e q)))))
 :hints (("Goal" :use (fn-pth-i-owner-opened-use-is-closed)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-step fn-pth-step* fn-pth-i-rearm fn-pth-i-owner-opened-delivery
     fn-pth-i-no-requests-deliver-refusals fn-pth-i-opened-requests-empty fn-pth-i-mstate-of-end-use
     fn-pth-m-step fn-pthm-step fn-rtc-acts-on-p fn-rtc-hand-delivers-p
     fn-rtc-ev fn-rtc-ev-id fn-rtc-get-of-cons fn-hld-mv-nth-0-cons
     fn-pth-i-mv-nth-2-cons-by-definition car-cons cdr-cons
     (:executable-counterpart equal) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+))))))

; Full joint I: all completions without owner delivery.

; From p15c-I-joint-grant.lisp
(defthm fn-pth-i-wait-is-foreign-to-owner
 (implies (and (fn-pth-i-owner-uses uses m) (member-equal w uses)
               (equal (fn-rtc-get 0 w) :wait))
          (not (equal (nfix (fn-rtc-get 1 w)) 1)))
 :hints (("Goal"
  :use ((:instance fn-pth-i-owner-never-waits-for-pool (inc (fn-rtc-get 2 w)))
        (:instance fn-rtc-kind-out-of-member (u w)))
  :in-theory (union-theories (theory 'minimal-theory) '(nfix natp (:executable-counterpart equal))))))
(defthm fn-pth-i-owner-uses-replace-foreign
 (implies (and (not (equal (fn-rtc-get 1 key) 1)) (not (equal (fn-rtc-get 1 v) 1)))
          (equal (fn-pth-i-owner-uses (fn-rtc-replace-use key v uses) m)
                 (fn-pth-i-owner-uses uses m)))
 :hints (("Goal" :induct (fn-rtc-replace-use key v uses)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-owner-uses fn-rtc-replace-use fn-rtc-key fn-rtc-get-of-cons
     car-cons cdr-cons (:executable-counterpart nfix) (:executable-counterpart zp))))))
(defthm fn-pth-i-owner-kind-out-replace-foreign
 (implies (and (not (equal (fn-rtc-get 1 key) 1)) (not (equal (fn-rtc-get 1 v) 1)))
          (equal (fn-rtc-kind-out-p kind 1 inc (fn-rtc-replace-use key v uses))
                 (fn-rtc-kind-out-p kind 1 inc uses)))
 :hints (("Goal" :induct (fn-rtc-replace-use key v uses)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-kind-out-p fn-rtc-replace-use fn-rtc-key fn-rtc-get-of-cons
     car-cons cdr-cons (:executable-counterpart nfix) (:executable-counterpart zp))))))
(defthm fn-pth-i-post-storage-pool-grant
 (implies (and (fn-pth-i-post-storage m s) (natp h)
               (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:free)))
          (fn-pth-i-post-storage m (fn-rtc-pool-grant-state w h s)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-rtc-pool-grant-state fn-pth-i-post-storage-of-buffer-update fn-pth-i-post-storage-with-uses
    fn-pth-i-owner-buffer-framep fn-rtc-with-accessors fn-rtc-buffer-of-with
    (:executable-counterpart equal))))))
(defthm fn-pth-i-owner-uses-pool-grant
 (implies (not (equal (nfix (fn-rtc-get 1 w)) 1))
          (equal (fn-pth-i-owner-uses (fn-rtc-uses (fn-rtc-pool-grant-state w h s)) m)
                 (fn-pth-i-owner-uses (fn-rtc-uses s) m)))
 :hints (("Goal" :use ((:instance fn-pth-i-owner-uses-replace-foreign (key (fn-rtc-key w))
                        (v (fn-rtc-pool-grant-use w h s)) (uses (fn-rtc-uses s))))
  :in-theory (union-theories (theory 'minimal-theory)
  '(fn-rtc-pool-grant-state-frame fn-rtc-pool-grant-use-fields
    fn-pth-i-owner-uses-replace-foreign fn-rtc-key fn-rtc-get-of-cons
    nfix natp car-cons cdr-cons (:executable-counterpart nfix) (:executable-counterpart zp))))))
(defthm fn-pth-i-owner-kind-out-pool-grant
 (implies (not (equal (nfix (fn-rtc-get 1 w)) 1))
          (equal (fn-rtc-kind-out-p kind 1 inc (fn-rtc-uses (fn-rtc-pool-grant-state w h s)))
                 (fn-rtc-kind-out-p kind 1 inc (fn-rtc-uses s))))
 :hints (("Goal" :use ((:instance fn-pth-i-owner-kind-out-replace-foreign (key (fn-rtc-key w))
                        (v (fn-rtc-pool-grant-use w h s)) (uses (fn-rtc-uses s))))
  :in-theory (union-theories (theory 'minimal-theory)
  '(fn-rtc-pool-grant-state-frame fn-rtc-pool-grant-use-fields
    fn-pth-i-owner-kind-out-replace-foreign fn-rtc-key fn-rtc-get-of-cons
    nfix natp car-cons cdr-cons (:executable-counterpart nfix) (:executable-counterpart zp))))))
(defthm fn-pth-i-pool-grant-preserves-owner-post-state
 (implies (and (fn-pth-i-post-state m s) (natp h)
               (not (equal (nfix (fn-rtc-get 1 w)) 1))
               (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:free)))
          (fn-pth-i-post-state m (fn-rtc-pool-grant-state w h s)))
 :hints (("Goal"
  :use (fn-pth-i-post-storage-and-protocol-by-definition
        (:instance fn-pth-i-post-storage-and-protocol-by-definition (s (fn-rtc-pool-grant-state w h s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-post-storage-pool-grant fn-pth-i-owner-uses-pool-grant fn-pth-i-owner-kind-out-pool-grant)))))
(defthm fn-pth-i-grant-one-preserves-owner-post-state
 (implies (fn-pth-i-post-state m s)
          (fn-pth-i-post-state m (mv-nth 0 (fn-rtc-grant-one s))))
 :hints (("Goal"
  :use ((:instance fn-pth-i-pool-grant-preserves-owner-post-state
         (w (fn-rtc-oldest-wait (fn-rtc-uses s)))
         (h (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s))))
        (:instance fn-pth-i-post-storage-and-protocol-by-definition)
        (:instance fn-pth-i-wait-is-foreign-to-owner (uses (fn-rtc-uses s))
          (w (fn-rtc-oldest-wait (fn-rtc-uses s))))
        (:instance fn-rtc-oldest-wait-member (uses (fn-rtc-uses s)))
        (:instance fn-rtc-free-pool-buf-is-free (i 0) (pool (fn-rtc-pool s)) (cfg (fn-rtc-config s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-grant-one-is-pool-grant-state fn-pth-i-pool-grant-preserves-owner-post-state
     fn-rtc-oldest-wait-kind fn-rtc-free-pool-buf-natural fn-rtc-buffer
     (:type-prescription fn-rtc-free-pool-buf-type) natp nfix
     default-+-1 default-+-2 commutativity-of-+ unicity-of-0 fix
     (:executable-counterpart binary-+) (:executable-counterpart unary--)
     (:executable-counterpart nfix) (:executable-counterpart natp))))))
(defthm fn-pth-i-grant-one
 (implies (fn-pth-i s) (fn-pth-i (mv-nth 0 (fn-rtc-grant-one s))))
 :hints (("Goal"
  :use (fn-pth-i-runtime-and-post-state-by-definition
        (:instance fn-pth-i-runtime-and-post-state-by-definition (s (mv-nth 0 (fn-rtc-grant-one s)))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime-grant-one fn-pth-i-grant-one-preserves-owner-post-state fn-rtc-grant-one-frame)))))
(defthm fn-pth-i-grant
 (implies (fn-pth-i s) (fn-pth-i (mv-nth 0 (fn-rtc-grant n s))))
 :hints (("Goal" :induct (fn-rtc-grant n s)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-grant fn-pth-i-grant-one fn-hld-mv-nth-0-cons car-cons cdr-cons)))))

; From p15c-I-joint-foreign-deliver.lisp
(defthm fn-pth-i-foreign-with-mstate
 (implies (and (fn-pth-i s) (not (equal id 1)))
          (fn-pth-i (fn-rtc-with-mstate id m s)))
 :hints (("Goal"
  :use (fn-pth-i-runtime-and-post-state-by-definition
        (:instance fn-pth-i-runtime-and-post-state-by-definition (s (fn-rtc-with-mstate id m s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime-with-mstate fn-pth-i-post-state-with-mstate fn-rtc-mstate-of-with nfix natp
     (:executable-counterpart nfix) (:executable-counterpart natp) (:executable-counterpart equal))))))
(defthm fn-pth-i-foreign-deliver
 (implies (and (fn-pth-i s) (not (equal id 1)))
          (fn-pth-i (mv-nth 0 (fn-pth-deliver s id inc ev q))))
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '(fn-pth-deliver fn-pth-i-foreign-with-mstate fn-pth-i-foreign-requests
    fn-hld-mv-nth-0-cons car-cons cdr-cons)))))
(defthm fn-pth-i-post-state-with-slot
 (equal (fn-pth-i-post-state m (fn-rtc-with-slot id slot s)) (fn-pth-i-post-state m s))
 :hints (("Goal"
  :use (fn-pth-i-post-storage-and-protocol-by-definition
        (:instance fn-pth-i-post-storage-and-protocol-by-definition (s (fn-rtc-with-slot id slot s)))
        (:instance fn-pth-i-post-storage-config-pool-congruence (s2 (fn-rtc-with-slot id slot s))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-with-accessors)))))
(defthm fn-pth-i-activate-slot
 (implies (and (fn-pth-i s) (natp id) (< 1 id) (fn-rtc-u64p inc)
               (natp r) (< r (expt 2 64))
               (equal (fn-rtc-s-status (fn-rtc-slot id s)) :free))
          (fn-pth-i (fn-rtc-with-slot id (list inc :live r) s)))
 :hints (("Goal"
  :use (fn-pth-i-runtime-and-post-state-by-definition
        (:instance fn-pth-i-runtime-and-post-state-by-definition (s (fn-rtc-with-slot id (list inc :live r) s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime-activate-slot fn-pth-i-post-state-with-slot fn-rtc-mstate-of-with)))))
(defthm fn-pth-i-accept-branch
 (implies (fn-pth-i s1) (fn-pth-i (mv-nth 0 (fn-pth-accept-branch s1 out q))))
 :hints (("Goal" :use ((:instance fn-pth-i-runtime-and-post-state-by-definition (s s1))
                       (:instance fn-pth-i-free-slot-is-dynamic (s s1)))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-accept-branch fn-pth-i-activate-slot fn-pth-i-foreign-with-mstate
     fn-pth-i-foreign-deliver fn-pth-i-rearm fn-pth-i-inc-room-next-is-u64
     fn-hld-mv-nth-0-cons car-cons cdr-cons)))))

; From p15c-I-joint-close.lisp
(defthm fn-pth-i-close-state-owner-buffer-frame
 (implies (and (not (equal id 1)) (natp h)
               (fn-rtc-view-own-p (fn-rtc-b-owner (fn-rtc-buffer h s)) 1 1))
          (equal (fn-rtc-buffer h (fn-rtc-close-state s id inc)) (fn-rtc-buffer h s)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-rtc-buffer fn-rtc-close-state-accessors fn-rtc-get-of-release-all
    fn-rtc-view-own-p fn-rtc-get-out-of-range fn-rtc-get-of-cons nfix natp
    (:executable-counterpart fn-rtc-b-owner) (:executable-counterpart equal)
    car-cons cdr-cons (:executable-counterpart nfix) (:executable-counterpart zp))))))
(defthm fn-pth-i-visible-buffer-close-state
 (implies (and (not (equal id 1)) (fn-pth-i-visible-buffer h s leasedp))
          (fn-pth-i-visible-buffer h (fn-rtc-close-state s id inc) leasedp))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-visible-buffer fn-pth-i-close-state-owner-buffer-frame
    fn-rtc-view-own-p fn-rtc-close-state-accessors)))))
(defthm fn-pth-i-post-close-state
 (implies (and (not (equal id 1)) (fn-pth-i-post p s leasedp))
          (fn-pth-i-post p (fn-rtc-close-state s id inc) leasedp))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-post fn-pth-i-visible-buffer-close-state fn-rtc-close-state-accessors)))))
(defthm fn-pth-i-queue-close-state
 (implies (and (not (equal id 1)) (fn-pth-i-queue ps s used))
          (fn-pth-i-queue ps (fn-rtc-close-state s id inc) used))
 :hints (("Goal" :induct (fn-pth-i-queue ps s used)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-queue fn-pth-i-post-close-state fn-pth-i-post fn-pth-i-visible-buffer
     fn-pth-i-close-state-owner-buffer-frame fn-rtc-view-own-p fn-rtc-close-state-accessors)))))
(defthm fn-pth-i-post-storage-close-state
 (implies (and (not (equal id 1)) (fn-pth-i-post-storage m s))
          (fn-pth-i-post-storage m (fn-rtc-close-state s id inc)))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-post-storage fn-pth-i-queue-close-state fn-pth-i-post-close-state fn-pth-i-visible-buffer-close-state
     fn-pth-i-post fn-pth-i-visible-buffer fn-pth-i-close-state-owner-buffer-frame
     fn-rtc-view-own-p fn-rtc-close-state-accessors)))))
(defthm fn-pth-i-owner-post-state-close-state
 (implies (and (not (equal id 1)) (fn-pth-i-post-state m s))
          (fn-pth-i-post-state m (fn-rtc-close-state s id inc)))
 :hints (("Goal"
  :use (fn-pth-i-post-storage-and-protocol-by-definition
        (:instance fn-pth-i-post-storage-and-protocol-by-definition (s (fn-rtc-close-state s id inc))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-post-storage-close-state fn-rtc-close-state-accessors)))))
(defthm fn-pth-i-close-state
 (implies (and (fn-pth-i s) (natp id) (< 1 id)
               (equal (fn-rtc-s-inc (fn-rtc-slot id s)) inc)
               (equal (fn-rtc-s-status (fn-rtc-slot id s)) :closing)
               (not (fn-rtc-kind-out-p :close id inc (fn-rtc-uses s))))
          (fn-pth-i (fn-rtc-close-state s id inc)))
 :hints (("Goal"
  :use (fn-pth-i-runtime-and-post-state-by-definition
        (:instance fn-pth-i-runtime-and-post-state-by-definition (s (fn-rtc-close-state s id inc))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime-close-state fn-pth-i-owner-post-state-close-state
     fn-rtc-close-state-accessors fn-rtc-mstate fn-rtc-get-of-set nfix natp
     (:executable-counterpart nfix) (:executable-counterpart natp) (:executable-counterpart equal))))))
(defthm fn-pth-i-close-branch
 (implies (and (fn-pth-i s1) (natp id) (< 1 id)
               (equal (fn-rtc-s-inc (fn-rtc-slot id s1)) inc)
               (equal (fn-rtc-s-status (fn-rtc-slot id s1)) :closing)
               (not (fn-rtc-kind-out-p :close id inc (fn-rtc-uses s1))))
          (fn-pth-i (mv-nth 0 (fn-pth-close-branch s1 id inc))))
 :hints (("Goal" :use (fn-pth-close-branch-through-close-state-by-definition)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-close-state fn-pth-i-foreign-with-mstate fn-pth-i-rearm)))))

; From p15c-I-nonowner-step.lisp
(defthm fn-pth-i-kind-out-remove-other-instance
 (implies (not (and (equal (fn-rtc-get 0 key) kind)
                    (equal (fn-rtc-get 1 key) id) (equal (fn-rtc-get 2 key) inc)))
          (equal (fn-rtc-kind-out-p kind id inc (fn-rtc-remove-use key uses))
                 (fn-rtc-kind-out-p kind id inc uses)))
 :hints (("Goal" :induct (fn-rtc-remove-use key uses)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-remove-use fn-rtc-kind-out-p fn-rtc-key fn-rtc-get-of-cons
     car-cons cdr-cons (:executable-counterpart nfix) (:executable-counterpart zp))))))
(defthm fn-pth-i-expected-completion-delivers-owner
 (implies (and (fn-pth-i-runtime s) (fn-ptx-expected m)
               (fn-rtc-completionp e) (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))
               (equal (fn-rtc-e-kind e) (fn-ptx-expected m))
               (equal (fn-rtc-e-id e) 1) (equal (fn-rtc-e-inc e) 1))
          (mv-nth 0 (fn-pth-owner-delivery s e q)))
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '(fn-pth-i-runtime fn-pth-owner-delivery fn-rtc-acts-on-p fn-rtc-hand-delivers-p
    fn-ptx-expected fn-hld-mv-nth-0-cons car-cons cdr-cons
    (:executable-counterpart fn-rtc-s-inc) (:executable-counterpart fn-rtc-s-status)
    (:executable-counterpart equal) (:executable-counterpart fn-rtc-get)
    (:executable-counterpart nfix) (:executable-counterpart zp))))))
(defthm fn-pth-i-expected-use-survives-without-owner-delivery
 (implies (and (fn-pth-i-runtime s) (fn-ptx-expected m)
               (fn-rtc-kind-out-p (fn-ptx-expected m) 1 1 (fn-rtc-uses s))
               (not (mv-nth 0 (fn-pth-owner-delivery s e q))))
          (fn-rtc-kind-out-p (fn-ptx-expected m) 1 1 (fn-rtc-uses (fn-rtc-end-use s e))))
 :hints (("Goal"
  :use (fn-pth-i-expected-completion-delivers-owner
        (:instance fn-pth-i-kind-out-remove-other-instance
          (key (fn-rtc-key e)) (uses (fn-rtc-uses s)) (kind (fn-ptx-expected m)) (id 1) (inc 1)))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-uses-of-end-use fn-rtc-key fn-rtc-completionp fn-rtc-e-kind fn-rtc-e-id fn-rtc-e-inc
     fn-rtc-get-of-cons nfix natp car-cons cdr-cons
     (:executable-counterpart nfix) (:executable-counterpart zp))))))
(defthm fn-pth-i-end-use-without-owner-delivery
 (implies (and (fn-pth-i s) (not (mv-nth 0 (fn-pth-owner-delivery s e q))))
          (fn-pth-i (fn-rtc-end-use s e)))
 :hints (("Goal"
  :use (fn-pth-i-runtime-and-post-state-by-definition
        fn-pth-i-before-machine-after-end-use
        (:instance fn-pth-i-expected-use-survives-without-owner-delivery (m (fn-rtc-mstate 1 s)))
        (:instance fn-pth-i-post-storage-and-protocol-by-definition (m (fn-rtc-mstate 1 s)))
        (:instance fn-pth-i-post-storage-and-protocol-by-definition (m (fn-rtc-mstate 1 s)) (s (fn-rtc-end-use s e)))
        (:instance fn-pth-i-runtime-and-post-state-by-definition (s (fn-rtc-end-use s e))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-pth-i-mstate-of-end-use)))))
(defthm fn-pth-i-step-without-owner-delivery
 (implies (and (fn-pth-i s) (not (mv-nth 0 (fn-pth-owner-delivery s e q))))
          (fn-pth-i (mv-nth 0 (fn-pth-step s e q))))
 :hints (("Goal"
  :use (fn-pth-i-end-use-without-owner-delivery fn-pth-i-runtime-and-post-state-by-definition
        fn-pth-i-acting-close-after-end-use)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-owner-delivery fn-pth-step fn-pth-step*
     fn-pth-i-foreign-deliver fn-pth-i-accept-branch fn-pth-i-close-branch
     fn-pth-i-grant fn-pth-i-rearm fn-hld-mv-nth-0-cons car-cons cdr-cons
     (:executable-counterpart nfix) (:executable-counterpart zp))))))

; Owner protocol restoration and actual successful extent completion.

; From p15c-I-owner-unbuffered.lisp
(defthm fn-pth-i-owner-unbuffered-request-admitted
 (implies (and (fn-pth-i-runtime s) (fn-pth-req-data-okp r)
               (equal (fn-rtc-get 0 r) :submit) (not (equal (fn-rtc-get 1 r) :pool))
               (not (fn-rtc-buffered-kind-p (fn-rtc-get 1 r)))
               (not (fn-rtc-kind-out-p (fn-rtc-get 1 r) 1 1 (fn-rtc-uses s))))
          (not (mv-nth 2 (fn-rtc-request r 1 1 s))))
 :hints (("Goal"
  :use ((:instance fn-pth-request-factors (id 1) (inc 1))
        (:instance fn-pth-i-unbuffered-machine-kind-properties (kind (fn-rtc-get 1 r))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-req-data-okp fn-pth-req-state-okp fn-pth-i-runtime fn-rtc-live-p
     fn-rtc-get-of-cons member-equal (:executable-counterpart fn-rtc-s-inc)
     (:executable-counterpart fn-rtc-s-status) (:executable-counterpart equal)
     (:executable-counterpart nfix) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart member-equal))))))
(defthm fn-pth-i-admitted-unbuffered-request-state
 (implies (and (equal (fn-rtc-get 0 r) :submit) (not (equal (fn-rtc-get 1 r) :pool))
               (not (fn-rtc-buffered-kind-p (fn-rtc-get 1 r)))
               (not (mv-nth 2 (fn-rtc-request r id inc s))))
          (equal (mv-nth 0 (fn-rtc-request r id inc s))
                 (fn-rtc-issue (list (fn-rtc-get 1 r) id inc (fn-rtc-next-op s) nil) s)))
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '(fn-rtc-request fn-rtc-req-submit fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition
    car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart fn-rtc-get))))))
(defthm fn-pth-i-post-storage-issue
 (equal (fn-pth-i-post-storage m (fn-rtc-issue new s)) (fn-pth-i-post-storage m s))
 :hints (("Goal" :use ((:instance fn-pth-i-post-storage-config-pool-congruence (s2 (fn-rtc-issue new s))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-issue-frame)))))
(defthm fn-pth-i-owner-uses-cons-expected
 (implies (and (fn-pth-i-owner-uses uses m) (fn-ptx-expected m))
          (fn-pth-i-owner-uses (cons (list (fn-ptx-expected m) 1 1 op nil) uses) m))
 :hints (("Goal" :expand ((fn-pth-i-owner-uses (cons (list (fn-ptx-expected m) 1 1 op nil) uses) m))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-get-of-cons car-cons cdr-cons (:executable-counterpart nfix) (:executable-counterpart zp)
     (:executable-counterpart fn-rtc-get) (:executable-counterpart equal))))))
(defthm fn-pth-i-post-state-issue-expected
 (implies (and (fn-pth-i-post-storage m s) (fn-pth-i-owner-uses (fn-rtc-uses s) m)
               (fn-ptx-expected m))
          (fn-pth-i-post-state m (fn-rtc-issue (list (fn-ptx-expected m) 1 1 (fn-rtc-next-op s) nil) s)))
 :hints (("Goal"
  :use ((:instance fn-pth-i-post-storage-and-protocol-by-definition
          (s (fn-rtc-issue (list (fn-ptx-expected m) 1 1 (fn-rtc-next-op s) nil) s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-post-storage-issue fn-rtc-issue-frame fn-pth-i-owner-uses-cons-expected
     fn-rtc-kind-out-p fn-rtc-get-of-cons car-cons cdr-cons
     (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))
(defthm fn-pth-i-owner-unbuffered-request
 (let ((m (fn-rtc-mstate 1 s)))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s)
                (fn-pth-i-owner-uses (fn-rtc-uses s) m) (fn-ptx-expected m)
                (fn-pth-req-data-okp r) (equal (fn-rtc-get 0 r) :submit)
                (equal (fn-rtc-get 1 r) (fn-ptx-expected m))
                (not (equal (fn-rtc-get 1 r) :pool))
                (not (fn-rtc-buffered-kind-p (fn-rtc-get 1 r)))
                (not (fn-rtc-kind-out-p (fn-rtc-get 1 r) 1 1 (fn-rtc-uses s))))
           (and (fn-pth-i (mv-nth 0 (fn-rtc-request r 1 1 s)))
                (not (mv-nth 2 (fn-rtc-request r 1 1 s))))))
 :hints (("Goal"
  :use ((:instance fn-pth-i-owner-unbuffered-request-admitted)
        (:instance fn-pth-i-admitted-unbuffered-request-state (id 1) (inc 1))
        (:instance fn-pth-i-runtime-request (id 1) (inc 1))
        (:instance fn-pth-i-post-state-issue-expected (m (fn-rtc-mstate 1 s)))
        (:instance fn-pth-i-runtime-and-post-state-by-definition (s (mv-nth 0 (fn-rtc-request r 1 1 s)))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-issue-frame)))))

; From p15c-I-expected-protocol.lisp
(defthm fn-pth-i-owner-protocol-after-expected-completion
 (let ((m (fn-rtc-mstate 1 s)))
  (implies (and (fn-pth-i s) (fn-ptx-expected m) (fn-rtc-completionp e)
                (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))
                (equal (fn-rtc-e-kind e) (fn-ptx-expected m))
                (equal (fn-rtc-e-id e) 1) (equal (fn-rtc-e-inc e) 1))
           (and (fn-pth-i-owner-uses (fn-rtc-uses (fn-rtc-end-use s e)) nil)
                (fn-pth-i-owner-uses (fn-rtc-uses (fn-rtc-end-use s e)) m2))))
 :hints (("Goal"
  :use (fn-pth-i-before-machine-after-end-use fn-pth-i-runtime-and-post-state-by-definition
        fn-pth-i-end-use-removes-event-kind
        (:instance fn-pth-i-owner-kind-out-is-protocol-kind (kind :opened) (inc 1)
          (uses (fn-rtc-uses (fn-rtc-end-use s e))) (m (fn-rtc-mstate 1 s)))
        (:instance fn-pth-i-owner-uses-only-hands-after-protocol-removed
          (uses (fn-rtc-uses (fn-rtc-end-use s e))) (m (fn-rtc-mstate 1 s)) (m2 nil))
        (:instance fn-pth-i-owner-uses-only-hands-after-protocol-removed
          (uses (fn-rtc-uses (fn-rtc-end-use s e))) (m (fn-rtc-mstate 1 s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-owner-kind-out-is-protocol-kind fn-ptx-expected member-equal
     (:executable-counterpart equal) (:executable-counterpart member-equal))))))
(defthm fn-pth-i-hands-only-has-no-operation
 (implies (and (fn-pth-i-owner-uses uses nil) (not (equal kind :hand)))
          (not (fn-rtc-kind-out-p kind 1 inc uses)))
 :hints (("Goal" :use ((:instance fn-pth-i-owner-kind-out-is-protocol-kind (m nil)))
  :in-theory (union-theories (theory 'minimal-theory)
   '((:executable-counterpart fn-ptx-ph) (:executable-counterpart fn-ptx-expected)
     (:executable-counterpart equal))))))

; From p15c-I-single-owner-delivery.lisp
(defthm fn-pth-i-post-storage-with-mstate
 (equal (fn-pth-i-post-storage m (fn-rtc-with-mstate id m2 s)) (fn-pth-i-post-storage m s))
 :hints (("Goal" :use ((:instance fn-pth-i-post-storage-config-pool-congruence
                        (s2 (fn-rtc-with-mstate id m2 s))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-with-accessors)))))
(defthm fn-pth-i-single-owner-request-after-machine
 (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m2 s)
               (fn-pth-i-owner-uses (fn-rtc-uses s) m2) (fn-ptx-expected m2)
               (fn-pth-req-data-okp r) (equal (fn-rtc-get 0 r) :submit)
               (equal (fn-rtc-get 1 r) (fn-ptx-expected m2))
               (not (equal (fn-rtc-get 1 r) :pool))
               (not (fn-rtc-buffered-kind-p (fn-rtc-get 1 r)))
               (not (fn-rtc-kind-out-p (fn-rtc-get 1 r) 1 1 (fn-rtc-uses s))))
          (and (fn-pth-i (mv-nth 0 (fn-rtc-requests (list r) 1 1 (fn-rtc-with-mstate 1 m2 s))))
               (not (mv-nth 2 (fn-rtc-requests (list r) 1 1 (fn-rtc-with-mstate 1 m2 s))))))
 :hints (("Goal" :use ((:instance fn-pth-i-owner-unbuffered-request (s (fn-rtc-with-mstate 1 m2 s))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-runtime-with-mstate fn-pth-i-owner-machine-index fn-rtc-with-accessors fn-rtc-mstate-of-with
     fn-pth-i-post-storage-with-mstate fn-rtc-requests fn-hld-mv-nth-0-cons
     fn-pth-i-mv-nth-2-cons-by-definition binary-append car-cons cdr-cons
     (:executable-counterpart nfix) (:executable-counterpart natp))))))
(defthm fn-pth-i-single-owner-unbuffered-deliver
 (let* ((step (fn-pth-m-step (fn-rtc-mstate 1 s) ev (fn-rtc-view-state 1 1 s) (nfix q)))
        (m2 (mv-nth 0 step)))
  (implies (and (fn-pth-i-runtime s) (equal (mv-nth 1 step) (list r))
                (fn-pth-i-post-storage m2 s) (fn-pth-i-owner-uses (fn-rtc-uses s) m2)
                (fn-ptx-expected m2) (fn-pth-req-data-okp r) (equal (fn-rtc-get 0 r) :submit)
                (equal (fn-rtc-get 1 r) (fn-ptx-expected m2))
                (not (equal (fn-rtc-get 1 r) :pool))
                (not (fn-rtc-buffered-kind-p (fn-rtc-get 1 r)))
                (not (fn-rtc-kind-out-p (fn-rtc-get 1 r) 1 1 (fn-rtc-uses s))))
           (and (fn-pth-i (mv-nth 0 (fn-pth-deliver s 1 1 ev q)))
                (not (mv-nth 2 (fn-pth-deliver s 1 1 ev q))))))
 :hints (("Goal"
  :use ((:instance fn-pth-i-single-owner-request-after-machine
         (m2 (mv-nth 0 (fn-pth-m-step (fn-rtc-mstate 1 s) ev (fn-rtc-view-state 1 1 s) (nfix q))))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-deliver fn-rtc-view-state fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition
     car-cons cdr-cons)))))
(defthm fn-pth-i-timer-and-fsync-data
 (and (fn-pth-req-data-okp (fn-ptx-timer)) (fn-pth-req-data-okp (fn-ptx-fsync))))

; From p15c-I-leasedp-congruence.lisp
(defthm fn-pth-i-visible-buffer-leasedp-congruence
 (implies (iff lp1 lp2)
          (equal (fn-pth-i-visible-buffer h s lp1) (fn-pth-i-visible-buffer h s lp2)))
 :rule-classes :congruence
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pth-i-visible-buffer)))))
(defthm fn-pth-i-post-leasedp-congruence
 (implies (iff lp1 lp2)
          (equal (fn-pth-i-post p s lp1) (fn-pth-i-post p s lp2)))
 :rule-classes :congruence
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-post fn-pth-i-visible-buffer-leasedp-congruence)))))

; From p15c-I-flight-storage.lisp
(defthm fn-pth-i-flight-storage-control-change
 (let ((m2 (fn-ptx-chg m :ph ph :k k :committed nil :evd evd)))
  (implies (and (fn-pth-i-post-storage m s) (fn-ptx-in-flight-p (fn-ptx-ph m))
                (fn-ptx-in-flight-p ph) (fn-ptx-okp m2))
           (fn-pth-i-post-storage m2 s)))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-post-storage fn-pth-i-visible-buffer-leasedp-congruence fn-pth-i-post-leasedp-congruence
     fn-ptx-in-flight-p member-equal fn-ptx-accessors-of-mk
     fn-ptx-elen fn-ptx-nmsg-of-mk fn-ptx-nmsg-is-g nfix natp
     (:type-prescription fn-ptx-ext) (:type-prescription fn-ptx-nxt)
     (:executable-counterpart nfix) (:executable-counterpart equal))))))
(defthm fn-pth-i-post-storage-extend-done
 (implies (and (fn-pth-i-post-storage m s) (equal (fn-ptx-ph m) :extending)
               (equal (fn-rtc-get 0 ev) :extend) (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done))
          (fn-pth-i-post-storage (mv-nth 0 (fn-ptx-step m ev st q)) s))
 :hints (("Goal"
  :use (fn-pth-i-post-storage-machine-facts fn-ptx-step-keeps-ok
        (:instance fn-pth-i-flight-storage-control-change
          (ph :extsyncing) (k (fn-ptx-k m)) (evd (fn-ptx-evd+ m ev))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-ptx-step fn-ptx-step1 fn-ptx-okp-wfp fn-ptx-accessors-of-mk fn-ptx-in-flight-p
     fn-hld-mv-nth-0-cons nfix natp car-cons cdr-cons (:type-prescription fn-ptx-k)
     (:type-prescription fn-ptx-ext) (:type-prescription fn-ptx-nxt)
     (:executable-counterpart equal) (:executable-counterpart member-equal)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))

; From p15c-I-extend-done-delivery.lisp
(defthm fn-pth-i-hands-only-compatible-with-every-machine
 (implies (fn-pth-i-owner-uses uses nil) (fn-pth-i-owner-uses uses m))
 :hints (("Goal" :induct (fn-pth-i-owner-uses uses nil)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-owner-uses (:executable-counterpart fn-ptx-ph)
     (:executable-counterpart fn-ptx-expected) (:executable-counterpart equal))))))
(defthm fn-pth-i-direct-owner-completion
 (implies (and (fn-pth-i-runtime s) (fn-rtc-acts-on-p s e)
               (equal (fn-rtc-e-id e) 1) (not (equal (fn-rtc-e-kind e) :hand)))
          (and (fn-rtc-completionp e) (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))
               (equal (fn-rtc-e-inc e) 1) (not (fn-rtc-hand-delivers-p s e))))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-runtime fn-rtc-acts-on-p fn-rtc-hand-delivers-p
    (:executable-counterpart fn-rtc-s-inc) (:executable-counterpart fn-rtc-s-status)
    (:executable-counterpart equal))))))
(defthm fn-pth-i-mv-nth-1-cons-by-definition
 (equal (mv-nth 1 (cons a (cons b c))) b)
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(mv-nth car-cons cdr-cons (:executable-counterpart zp)
    (:executable-counterpart nfix) (:executable-counterpart binary-+))))))
(defthm fn-pth-i-extend-done-delivery
 (implies (and (fn-pth-i s) (equal (fn-ptx-ph (fn-rtc-mstate 1 s)) :extending)
               (fn-rtc-completionp e) (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))
               (equal (fn-rtc-e-kind e) :extend) (equal (fn-rtc-e-id e) 1) (equal (fn-rtc-e-inc e) 1)
               (equal (fn-rtc-ev-id ev) 1) (equal (fn-rtc-get 0 ev) :extend)
               (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done))
          (and (fn-pth-i (mv-nth 0 (fn-pth-deliver (fn-rtc-end-use s e) 1 1 ev q)))
               (not (mv-nth 2 (fn-pth-deliver (fn-rtc-end-use s e) 1 1 ev q)))))
 :hints (("Goal"
  :use (fn-pth-i-before-machine-after-end-use
        (:instance fn-pth-i-post-storage-machine-facts (m (fn-rtc-mstate 1 s)) (s (fn-rtc-end-use s e)))
        (:instance fn-pth-i-owner-protocol-after-expected-completion (m2 nil))
        (:instance fn-pth-i-post-storage-extend-done (m (fn-rtc-mstate 1 s))
          (s (fn-rtc-end-use s e)) (st (fn-rtc-view-state 1 1 (fn-rtc-end-use s e))) (q (nfix q)))
        (:instance fn-pth-i-single-owner-unbuffered-deliver (s (fn-rtc-end-use s e)) (r (fn-ptx-fsync)))
        fn-pth-i-timer-and-fsync-data)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-mstate-of-end-use fn-pth-m-step fn-pthm-step fn-ptx-step fn-ptx-step1
     fn-ptx-expected fn-ptx-okp-wfp fn-ptx-accessors-of-mk
     fn-ptx-fsync fn-rtc-get-of-cons fn-pth-i-hands-only-compatible-with-every-machine
     fn-pth-i-hands-only-has-no-operation fn-hld-mv-nth-0-cons
     fn-pth-i-mv-nth-1-cons-by-definition fn-pth-i-mv-nth-2-cons-by-definition
     nfix natp car-cons cdr-cons (:type-prescription fn-ptx-k)
     (:type-prescription fn-ptx-ext) (:type-prescription fn-ptx-nxt)
     (:executable-counterpart fn-rtc-get) (:executable-counterpart fn-rtc-buffered-kind-p)
     (:executable-counterpart member-equal) (:executable-counterpart equal) (:executable-counterpart nfix) (:executable-counterpart zp))))))

; From p15c-I-extend-done-step.lisp
(defthm fn-pth-i-owner-extend-done-step
 (implies (and (fn-pth-i s) (equal (fn-ptx-ph (fn-rtc-mstate 1 s)) :extending)
               (fn-rtc-acts-on-p s e) (equal (fn-rtc-e-id e) 1) (equal (fn-rtc-e-kind e) :extend)
               (equal (fn-rtc-get 0 (fn-rtc-delivered-outcome
                                     (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e)) :done))
          (and (fn-pth-i (mv-nth 0 (fn-pth-step s e q)))
               (not (mv-nth 2 (fn-pth-step* s e q)))))
 :hints (("Goal" :use (fn-pth-i-runtime-and-post-state-by-definition fn-pth-i-direct-owner-completion)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-step fn-pth-step* fn-pth-i-rearm fn-pth-i-extend-done-delivery
     fn-rtc-acts-on-p fn-rtc-hand-delivers-p fn-rtc-ev fn-rtc-ev-id fn-rtc-get-of-cons
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition car-cons cdr-cons
     (:executable-counterpart equal) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))

; Owner log-span success: storage, protocol restoration and actual step.
(defthm fn-pth-i-post-storage-log-done
 (implies (and (fn-pth-i-post-storage m s) (equal (fn-ptx-ph m) :log-writing)
               (equal (fn-rtc-get 0 ev) :pwrite) (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done)
               (equal (fn-rtc-get 1 (fn-rtc-get 1 ev)) (fn-ptx-span-n (fn-ptx-k m) m)))
          (fn-pth-i-post-storage (mv-nth 0 (fn-ptx-step m ev st q)) s))
 :hints (("Goal"
  :use (fn-pth-i-post-storage-machine-facts fn-ptx-step-keeps-ok
        (:instance fn-pth-i-flight-storage-control-change
          (ph :committing) (k (fn-ptx-k m)) (evd (fn-ptx-evd+ m ev))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-ptx-step fn-ptx-step1 fn-ptx-okp-wfp fn-ptx-accessors-of-mk fn-ptx-in-flight-p
     fn-hld-mv-nth-0-cons nfix natp car-cons cdr-cons (:type-prescription fn-ptx-k)
     (:type-prescription fn-ptx-ext) (:type-prescription fn-ptx-nxt)
     (:executable-counterpart equal) (:executable-counterpart member-equal)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))


(defthm fn-pth-i-log-done-delivery
 (implies (and (fn-pth-i s) (equal (fn-ptx-ph (fn-rtc-mstate 1 s)) :log-writing)
               (fn-rtc-completionp e) (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))
               (equal (fn-rtc-e-kind e) :pwrite) (equal (fn-rtc-e-id e) 1) (equal (fn-rtc-e-inc e) 1)
               (equal (fn-rtc-ev-id ev) 1) (equal (fn-rtc-get 0 ev) :pwrite)
               (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done)
               (equal (fn-rtc-get 1 (fn-rtc-get 1 ev)) (fn-ptx-span-n (fn-ptx-k (fn-rtc-mstate 1 s)) (fn-rtc-mstate 1 s))))
          (and (fn-pth-i (mv-nth 0 (fn-pth-deliver (fn-rtc-end-use s e) 1 1 ev q)))
               (not (mv-nth 2 (fn-pth-deliver (fn-rtc-end-use s e) 1 1 ev q)))))
 :hints (("Goal"
  :use (fn-pth-i-before-machine-after-end-use
        (:instance fn-pth-i-post-storage-machine-facts (m (fn-rtc-mstate 1 s)) (s (fn-rtc-end-use s e)))
        (:instance fn-pth-i-owner-protocol-after-expected-completion (m2 nil))
        (:instance fn-pth-i-post-storage-log-done (m (fn-rtc-mstate 1 s))
          (s (fn-rtc-end-use s e)) (st (fn-rtc-view-state 1 1 (fn-rtc-end-use s e))) (q (nfix q)))
        (:instance fn-pth-i-single-owner-unbuffered-deliver (s (fn-rtc-end-use s e)) (r (fn-ptx-fsync)))
        fn-pth-i-timer-and-fsync-data)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-mstate-of-end-use fn-pth-m-step fn-pthm-step fn-ptx-step fn-ptx-step1
     fn-ptx-expected fn-ptx-okp-wfp fn-ptx-accessors-of-mk
     fn-ptx-fsync fn-rtc-get-of-cons fn-pth-i-hands-only-compatible-with-every-machine
     fn-pth-i-hands-only-has-no-operation fn-hld-mv-nth-0-cons
     fn-pth-i-mv-nth-1-cons-by-definition fn-pth-i-mv-nth-2-cons-by-definition
     nfix natp car-cons cdr-cons (:type-prescription fn-ptx-k)
     (:type-prescription fn-ptx-ext) (:type-prescription fn-ptx-nxt)
     (:executable-counterpart fn-rtc-get) (:executable-counterpart fn-rtc-buffered-kind-p)
     (:executable-counterpart member-equal) (:executable-counterpart equal) (:executable-counterpart nfix) (:executable-counterpart zp))))))

; From p15c-I-log-done-step.lisp
(defthm fn-pth-i-owner-log-done-step
 (implies (and (fn-pth-i s) (equal (fn-ptx-ph (fn-rtc-mstate 1 s)) :log-writing)
               (fn-rtc-acts-on-p s e) (equal (fn-rtc-e-id e) 1) (equal (fn-rtc-e-kind e) :pwrite)
               (equal (fn-rtc-get 0 (fn-rtc-delivered-outcome
                                     (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e)) :done)
               (equal (fn-rtc-get 1 (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e))
                      (fn-ptx-span-n (fn-ptx-k (fn-rtc-mstate 1 s)) (fn-rtc-mstate 1 s))))
          (and (fn-pth-i (mv-nth 0 (fn-pth-step s e q)))
               (not (mv-nth 2 (fn-pth-step* s e q)))))
 :hints (("Goal" :use (fn-pth-i-runtime-and-post-state-by-definition fn-pth-i-direct-owner-completion)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-step fn-pth-step* fn-pth-i-rearm fn-pth-i-log-done-delivery
     fn-rtc-acts-on-p fn-rtc-hand-delivers-p fn-rtc-ev fn-rtc-ev-id fn-rtc-get-of-cons
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition car-cons cdr-cons
     (:executable-counterpart equal) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))


; Shared buffer frames and the actual owner returned-hand completion.

; From p15d-I-untracked.lisp
(defun fn-pth-i-queue-avoids (ps h)
 (declare (xargs :guard t))
 (if (consp ps)
     (and (not (equal (fn-ptx-cur-bp (car ps)) h))
          (fn-pth-i-queue-avoids (cdr ps) h)) t))
(defun fn-pth-i-storage-avoids (m h)
 (declare (xargs :guard t))
 (and (implies (member-eq (fn-ptx-ph m) '(:reading :hashing :extending :extsyncing :payload-writing :log-writing :committing))
               (not (equal (fn-ptx-cur-bp (fn-ptx-cur m)) h)))
      (implies (consp (fn-ptx-b1 m))
               (and (not (equal (fn-ptx-buf-h (fn-ptx-b1 m)) h))
                    (not (equal (fn-ptx-buf-h (fn-ptx-b3 m)) h))))
      (fn-pth-i-queue-avoids (fn-ptx-q m) h)))
(defthm fn-pth-i-queue-avoids-invisible
 (implies (and (fn-pth-i-queue ps s used)
               (not (fn-pth-i-visible-buffer h s t)))
          (fn-pth-i-queue-avoids ps h))
 :hints (("Goal" :induct (fn-pth-i-queue ps s used)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-queue fn-pth-i-post fn-pth-i-queue-avoids fn-pth-i-visible-buffer)))))
(defthm fn-pth-i-storage-avoids-invisible
 (implies (and (fn-pth-i-post-storage m s)
               (not (fn-pth-i-visible-buffer h s t)))
          (fn-pth-i-storage-avoids m h))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-post-storage fn-pth-i-post fn-pth-i-storage-avoids
     fn-pth-i-queue-avoids-invisible fn-pth-i-visible-buffer fn-ptx-in-flight-p member-equal
     (:executable-counterpart member-equal))))))
(defthm fn-pth-i-queue-untracked-update
 (implies (and (natp h) (fn-pth-i-queue-avoids ps h) (fn-pth-i-queue ps s used))
          (fn-pth-i-queue ps (fn-rtc-with-buffer h b s) used))
 :hints (("Goal" :induct (fn-pth-i-queue ps s used)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-queue fn-pth-i-post fn-pth-i-visible-buffer fn-pth-i-queue-avoids
     fn-rtc-buffer-of-with fn-rtc-with-accessors nfix natp)))))
(defthm fn-pth-i-storage-untracked-update
 (implies (and (natp h) (fn-pth-i-storage-avoids m h) (fn-pth-i-post-storage m s))
          (fn-pth-i-post-storage m (fn-rtc-with-buffer h b s)))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-post-storage fn-pth-i-post fn-pth-i-visible-buffer fn-pth-i-storage-avoids
     fn-pth-i-queue-untracked-update fn-rtc-buffer-of-with fn-rtc-with-accessors
     fn-ptx-in-flight-p nfix natp (:executable-counterpart member-equal))))))
(defthm fn-pth-i-storage-avoids-m0
 (equal (fn-pth-i-storage-avoids (fn-ptx-chg m :committed nil) h)
        (fn-pth-i-storage-avoids m h))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-storage-avoids fn-ptx-accessors-of-mk)))))

; From p15d-I-local-requests.lisp
(defthm fn-pth-i-post-storage-untracked-request
 (implies (and (fn-pth-i-post-storage m s)
               (or (and (member-eq (fn-rtc-get 0 r) '(:acquire :write :release))
                        (fn-pth-i-storage-avoids m (fn-rtc-get 1 r)))
                   (and (equal (fn-rtc-get 0 r) :submit) (equal (fn-rtc-get 1 r) :hand)
                        (fn-pth-i-storage-avoids m (fn-rtc-h-buf (fn-rtc-get 2 r))))))
          (fn-pth-i-post-storage m (mv-nth 0 (fn-rtc-request r 1 1 s))))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release fn-rtc-req-submit
     fn-pth-i-storage-untracked-update fn-pth-i-post-storage-issue fn-rtc-with-accessors
     member-equal fn-hld-mv-nth-0-cons car-cons cdr-cons (:type-prescription fn-rtc-h-buf)
     natp (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+)
     (:executable-counterpart fn-rtc-buffered-kind-p) (:executable-counterpart member-equal))))))
(defthm fn-pth-i-owner-local-request-protocol
 (implies (or (member-eq (fn-rtc-get 0 r) '(:acquire :write :release))
              (and (equal (fn-rtc-get 0 r) :submit) (equal (fn-rtc-get 1 r) :hand)))
  (and (equal (fn-pth-i-owner-uses (fn-rtc-uses (mv-nth 0 (fn-rtc-request r 1 1 s))) m)
              (fn-pth-i-owner-uses (fn-rtc-uses s) m))
       (implies (fn-rtc-kind-out-p kind 1 1 (fn-rtc-uses s))
                (fn-rtc-kind-out-p kind 1 1 (fn-rtc-uses (mv-nth 0 (fn-rtc-request r 1 1 s)))))))
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release fn-rtc-req-submit
     fn-rtc-with-accessors fn-rtc-issue-frame fn-pth-i-owner-uses fn-rtc-kind-out-p
     member-equal fn-rtc-get-of-cons fn-hld-mv-nth-0-cons car-cons cdr-cons
     (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+)
     (:executable-counterpart fn-rtc-buffered-kind-p) (:executable-counterpart member-equal))))))
(defthm fn-pth-i-owner-untracked-request
 (implies (and (fn-pth-i s)
               (or (and (member-eq (fn-rtc-get 0 r) '(:acquire :write :release))
                        (fn-pth-i-storage-avoids (fn-rtc-mstate 1 s) (fn-rtc-get 1 r)))
                   (and (equal (fn-rtc-get 0 r) :submit) (equal (fn-rtc-get 1 r) :hand)
                        (fn-pth-i-storage-avoids (fn-rtc-mstate 1 s) (fn-rtc-h-buf (fn-rtc-get 2 r))))))
          (fn-pth-i (mv-nth 0 (fn-rtc-request r 1 1 s))))
 :hints (("Goal"
  :use (fn-pth-i-runtime-and-post-state-by-definition
        (:instance fn-pth-i-runtime-and-post-state-by-definition (s (mv-nth 0 (fn-rtc-request r 1 1 s))))
        (:instance fn-pth-i-post-storage-and-protocol-by-definition (m (fn-rtc-mstate 1 s)))
        (:instance fn-pth-i-post-storage-and-protocol-by-definition
           (m (fn-rtc-mstate 1 s)) (s (mv-nth 0 (fn-rtc-request r 1 1 s)))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime-request fn-rtc-request-keeps-mstates
     fn-pth-i-post-storage-untracked-request fn-pth-i-owner-local-request-protocol)))))

; From p15d-I-return-hand-facts.lisp
(defthm fn-pth-i-holders-of-remove-found
 (implies (and (equal u (fn-rtc-find-use key uses)) u)
  (equal (fn-rtc-holders h g (fn-rtc-remove-use key uses))
         (- (fn-rtc-holders h g uses)
            (if (and (fn-rtc-handlep (fn-rtc-u-hd u))
                     (equal (fn-rtc-h-buf (fn-rtc-u-hd u)) h)
                     (equal (fn-rtc-h-gen (fn-rtc-u-hd u)) g)) 1 0))))
 :hints (("Goal" :induct (fn-rtc-remove-use key uses)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-remove-use fn-rtc-find-use fn-rtc-holders
     default-+-1 default-+-2 default-unary-minus associativity-of-+ commutativity-of-+
     commutativity-2-of-+ inverse-of-+ unicity-of-0 fix (:type-prescription fn-rtc-holders)
     car-cons cdr-cons (:executable-counterpart binary-+))))))
(defthm fn-pth-i-hand-use-facts
 (implies (and (or (fn-rtc-use-okp u s) (fn-pth-i-listener-use u s))
               (equal (fn-rtc-get 0 u) :hand))
  (let* ((hd (fn-rtc-u-hd u)) (h (fn-rtc-h-buf hd)) (b (fn-rtc-buffer h s)) (o (fn-rtc-b-owner b)))
   (and (fn-rtc-handlep hd) (< h (fn-rtc-nbufs (fn-rtc-config s)))
        (equal (fn-rtc-b-gen b) (fn-rtc-h-gen hd))
        (equal (fn-rtc-get 0 o) :handed)
        (equal (fn-rtc-get 1 o) (nfix (fn-rtc-get 1 u)))
        (equal (fn-rtc-get 2 o) (fn-rtc-get 2 u))
        (equal (fn-rtc-holders h (fn-rtc-h-gen hd) (fn-rtc-uses s)) 1))))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-use-okp fn-rtc-usep fn-rtc-u-hd fn-pth-i-listener-use natp nfix (:type-prescription nfix)
     (:executable-counterpart equal) (:executable-counterpart fn-rtc-buffered-kind-p)
     (:executable-counterpart member-equal))))))
(defthm fn-pth-i-found-hand-facts
 (let* ((u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))
        (hd (fn-rtc-u-hd u)) (h (fn-rtc-h-buf hd)) (b (fn-rtc-buffer h s)))
  (implies (and (fn-pth-i-runtime s) (fn-rtc-completionp e) u
                (equal (fn-rtc-e-kind e) :hand))
   (and (fn-rtc-handlep hd) (< h (fn-rtc-nbufs (fn-rtc-config s)))
        (equal (fn-rtc-b-gen b) (fn-rtc-h-gen hd))
        (equal (fn-rtc-get 0 (fn-rtc-b-owner b)) :handed)
        (equal (fn-rtc-get 1 (fn-rtc-b-owner b)) (nfix (fn-rtc-e-id e)))
        (equal (fn-rtc-get 2 (fn-rtc-b-owner b)) (fn-rtc-e-inc e))
        (not (fn-rtc-holds-p h (fn-rtc-h-gen hd) (fn-rtc-remove-use (fn-rtc-key e) (fn-rtc-uses s)))))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-rtc-matching-use-fields (uses (fn-rtc-uses s)))
        (:instance fn-pth-i-uses-member (uses (fn-rtc-uses s)) (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))
        (:instance fn-rtc-find-use-is-member (k (fn-rtc-key e)) (uses (fn-rtc-uses s)))
        (:instance fn-pth-i-hand-use-facts (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))
        (:instance fn-pth-i-holders-of-remove-found (key (fn-rtc-key e)) (uses (fn-rtc-uses s))
          (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))
          (h (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))))
          (g (fn-rtc-h-gen (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime-control-by-definition fn-rtc-holds-iff-positive-holders
     (:executable-counterpart binary-+) (:executable-counterpart unary--) (:executable-counterpart <))))))

; From p15d-I-return-hand-buffer.lisp
(defthm fn-pth-i-returned-hand-buffer
 (let* ((u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))
        (hd (fn-rtc-u-hd u)) (h (fn-rtc-h-buf hd)) (b (fn-rtc-buffer h s)))
  (implies (and (fn-pth-i-runtime s) (fn-rtc-completionp e) u
                (equal (fn-rtc-e-kind e) :hand) (equal (fn-rtc-e-id e) 1)
                (equal (fn-rtc-e-inc e) 1) (not (fn-rtc-hand-delivers-p s e)))
   (equal (fn-rtc-buffer h (fn-rtc-end-use s e))
          (list (+ 1 (fn-rtc-b-gen b)) '(:workspace 1 1) (fn-rtc-b-bytes b)))))
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-found-hand-facts
        (:instance fn-rtc-matching-use-fields (uses (fn-rtc-uses s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-rtc-shapep fn-rtc-end-use fn-rtc-end-lease
     fn-rtc-lease-return fn-rtc-hand-delivers-p fn-rtc-handed-to-live-p
     fn-rtc-retire-drained-frame fn-rtc-lease-return-of-with-uses
     fn-rtc-current-p fn-rtc-with-accessors fn-rtc-buffer-of-with fn-rtc-slot-of-with
     fn-rtc-buffer-accessors fn-rtc-get-of-cons car-cons cdr-cons
     natp nfix (:type-prescription fn-rtc-h-buf)
     (:executable-counterpart fn-rtc-get) (:executable-counterpart fn-rtc-s-inc)
     (:executable-counterpart fn-rtc-s-status) (:executable-counterpart equal)
     (:executable-counterpart member-equal) (:executable-counterpart nfix)
     (:executable-counterpart zp))))))
(defthm fn-pth-i-hand-buffer-untracked
 (let ((h (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))))
  (implies (and (fn-pth-i s) (fn-rtc-completionp e)
                (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))
                (equal (fn-rtc-e-kind e) :hand))
           (fn-pth-i-storage-avoids (fn-rtc-mstate 1 s) h)))
 :hints (("Goal" :use (fn-pth-i-found-hand-facts
      fn-pth-i-runtime-and-post-state-by-definition
      (:instance fn-pth-i-post-storage-and-protocol-by-definition (m (fn-rtc-mstate 1 s)))
      (:instance fn-pth-i-storage-avoids-invisible
       (m (fn-rtc-mstate 1 s))
       (h (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-visible-buffer (:executable-counterpart fn-rtc-get))))))

; From p15d-I-hand-protocol.lisp
(defthm fn-pth-i-kind-out-remove-other-kind
 (implies (and (fn-rtc-completionp e) (not (equal kind (fn-rtc-e-kind e))))
          (equal (fn-rtc-kind-out-p kind id inc (fn-rtc-remove-use (fn-rtc-key e) uses))
                 (fn-rtc-kind-out-p kind id inc uses)))
 :hints (("Goal" :induct (fn-rtc-remove-use (fn-rtc-key e) uses)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-remove-use fn-rtc-kind-out-p fn-rtc-key fn-rtc-e-kind fn-rtc-get-of-cons
     car-cons cdr-cons (:executable-counterpart nfix) (:executable-counterpart zp)
     (:executable-counterpart binary-+))))))
(defthm fn-pth-i-end-use-hand
 (implies (and (fn-pth-i s) (equal (fn-rtc-e-kind e) :hand))
          (fn-pth-i (fn-rtc-end-use s e)))
 :hints (("Goal"
  :use (fn-pth-i-before-machine-after-end-use fn-pth-i-runtime-and-post-state-by-definition
        (:instance fn-pth-i-runtime-and-post-state-by-definition (s (fn-rtc-end-use s e)))
        (:instance fn-pth-i-post-storage-and-protocol-by-definition (m (fn-rtc-mstate 1 s)))
        (:instance fn-pth-i-post-storage-and-protocol-by-definition
          (m (fn-rtc-mstate 1 s)) (s (fn-rtc-end-use s e))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-mstate-of-end-use fn-rtc-uses-of-end-use fn-pth-i-kind-out-remove-other-kind
     fn-ptx-expected (:executable-counterpart equal))))))
(defthm fn-pth-i-owner-uses-m0
 (equal (fn-pth-i-owner-uses uses (fn-ptx-chg m :committed nil))
        (fn-pth-i-owner-uses uses m))
 :hints (("Goal" :induct (fn-pth-i-owner-uses uses m)
  :expand ((fn-pth-i-owner-uses uses (fn-ptx-chg m :committed nil)) (fn-pth-i-owner-uses uses m))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-owner-uses fn-ptx-expected fn-ptx-accessors-of-mk)))))
(defthm fn-pth-i-expected-m0
 (equal (fn-ptx-expected (fn-ptx-chg m :committed nil)) (fn-ptx-expected m))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-ptx-expected fn-ptx-accessors-of-mk)))))
(defthm fn-pth-i-post-state-m0
 (implies (fn-pth-i-post-state m s)
          (fn-pth-i-post-state (fn-ptx-chg m :committed nil) s))
 :hints (("Goal"
  :use (fn-pth-i-post-storage-and-protocol-by-definition
        (:instance fn-pth-i-post-storage-and-protocol-by-definition (m (fn-ptx-chg m :committed nil))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-post-storage-m0 fn-pth-i-owner-uses-m0 fn-pth-i-expected-m0)))))
(defthm fn-pth-i-install-owner-state
 (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-state m s))
          (fn-pth-i (fn-rtc-with-mstate 1 m s)))
 :hints (("Goal" :use ((:instance fn-pth-i-runtime-and-post-state-by-definition (s (fn-rtc-with-mstate 1 m s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime-with-mstate fn-pth-i-post-state-with-mstate fn-rtc-mstate-of-with fn-pth-i-owner-machine-index
     (:executable-counterpart equal) (:executable-counterpart nfix))))))

; From p15d-I-single-local.lisp
(defthm fn-pth-i-single-owner-untracked-request-after-machine
 (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-state m s)
               (fn-pth-req-data-okp r) (fn-pth-req-state-okp r 1 1 s)
               (or (and (member-eq (fn-rtc-get 0 r) '(:acquire :write :release))
                        (fn-pth-i-storage-avoids m (fn-rtc-get 1 r)))
                   (and (equal (fn-rtc-get 0 r) :submit) (equal (fn-rtc-get 1 r) :hand)
                        (fn-pth-i-storage-avoids m (fn-rtc-h-buf (fn-rtc-get 2 r))))))
          (and (fn-pth-i (mv-nth 0 (fn-rtc-requests (list r) 1 1 (fn-rtc-with-mstate 1 m s))))
               (not (mv-nth 2 (fn-rtc-requests (list r) 1 1 (fn-rtc-with-mstate 1 m s))))))
 :hints (("Goal"
  :use ((:instance fn-pth-i-owner-untracked-request (s (fn-rtc-with-mstate 1 m s)))
        (:instance fn-pth-request-factors (s (fn-rtc-with-mstate 1 m s)) (id 1) (inc 1)))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-install-owner-state fn-pth-i-owner-machine-index fn-rtc-mstate-of-with fn-pth-req-state-okp
     fn-rtc-with-accessors fn-rtc-buffer-of-with fn-rtc-slot-of-with
     fn-rtc-live-p fn-rtc-current-p fn-rtc-requests binary-append fn-hld-mv-nth-0-cons
     fn-pth-i-mv-nth-2-cons-by-definition car-cons cdr-cons
     (:executable-counterpart nfix) (:executable-counterpart natp))))))
(defthm fn-pth-i-single-owner-untracked-deliver
 (let* ((step (fn-pth-m-step (fn-rtc-mstate 1 s) ev (fn-rtc-view-state 1 1 s) (nfix q)))
        (m (mv-nth 0 step)))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-state m s)
                (equal (mv-nth 1 step) (list r))
                (fn-pth-req-data-okp r) (fn-pth-req-state-okp r 1 1 s)
                (or (and (member-eq (fn-rtc-get 0 r) '(:acquire :write :release))
                         (fn-pth-i-storage-avoids m (fn-rtc-get 1 r)))
                    (and (equal (fn-rtc-get 0 r) :submit) (equal (fn-rtc-get 1 r) :hand)
                         (fn-pth-i-storage-avoids m (fn-rtc-h-buf (fn-rtc-get 2 r))))))
           (and (fn-pth-i (mv-nth 0 (fn-pth-deliver s 1 1 ev q)))
                (not (mv-nth 2 (fn-pth-deliver s 1 1 ev q))))))
 :hints (("Goal"
  :use ((:instance fn-pth-i-single-owner-untracked-request-after-machine
        (m (mv-nth 0 (fn-pth-m-step (fn-rtc-mstate 1 s) ev (fn-rtc-view-state 1 1 s) (nfix q))))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-deliver fn-rtc-view-state fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition
     car-cons cdr-cons)))))

; From p15d-I-return-hand-delivery.lisp
(defthm fn-pth-i-returned-hand-delivery
 (let ((h (fn-rtc-h-buf (fn-rtc-get 4 ev))) (g (fn-rtc-h-gen (fn-rtc-get 4 ev))))
  (implies (and (fn-pth-i s) (equal (fn-rtc-ev-id ev) 1) (equal (fn-rtc-get 0 ev) :hand)
                (fn-rtc-handlep (fn-rtc-get 4 ev))
                (< h (fn-rtc-nbufs (fn-rtc-config s)))
                (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:workspace 1 1))
                (equal (fn-rtc-b-gen (fn-rtc-buffer h s)) g)
                (fn-pth-i-storage-avoids (fn-rtc-mstate 1 s) h))
           (and (fn-pth-i (mv-nth 0 (fn-pth-deliver s 1 1 ev q)))
                (not (mv-nth 2 (fn-pth-deliver s 1 1 ev q))))))
 :hints (("Goal"
  :use (fn-pth-i-runtime-and-post-state-by-definition
        (:instance fn-pth-i-post-storage-and-protocol-by-definition (m (fn-rtc-mstate 1 s)))
        (:instance fn-pth-i-post-storage-machine-facts (m (fn-rtc-mstate 1 s)))
        (:instance fn-pth-i-single-owner-untracked-deliver
          (r (list :release (fn-rtc-h-buf (fn-rtc-get 4 ev)) (fn-rtc-h-gen (fn-rtc-get 4 ev))))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-m-step fn-pthm-step fn-ptx-step fn-ptx-step1 fn-ptx-okp-wfp
     fn-pth-i-post-state-m0 fn-pth-i-storage-avoids-m0
     fn-pth-req-data-okp fn-pth-req-state-okp
     fn-rtc-get-of-cons fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-1-cons-by-definition
     car-cons cdr-cons natp (:type-prescription fn-rtc-h-buf)
     (:executable-counterpart equal) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart nfix) (:executable-counterpart zp)
     (:executable-counterpart member-equal))))))

; From p15d-I-hand-handle.lisp
(defthm fn-pth-i-made-handle-properties
 (implies (and (natp h) (natp g) (natp n))
          (and (fn-rtc-handlep (list h g 0 n))
               (equal (fn-rtc-h-buf (list h g 0 n)) h)
               (equal (fn-rtc-h-gen (list h g 0 n)) g)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-rtc-handlep fn-rtc-h-buf fn-rtc-h-gen fn-rtc-get-of-cons len true-listp nfix natp
    car-cons cdr-cons (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
    (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+))))))

; From p15d-I-return-hand-step.lisp
(defthm fn-pth-i-nondelivering-owner-completion
 (implies (and (fn-pth-i-runtime s) (fn-rtc-acts-on-p s e)
               (equal (fn-rtc-e-id e) 1) (not (fn-rtc-hand-delivers-p s e)))
          (and (fn-rtc-completionp e) (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))
               (equal (fn-rtc-e-inc e) 1)))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-runtime fn-rtc-acts-on-p
    (:executable-counterpart fn-rtc-s-inc) (:executable-counterpart fn-rtc-s-status)
    (:executable-counterpart equal))))))
(defthm fn-pth-i-owner-returned-hand-step
 (implies (and (fn-pth-i s) (fn-rtc-acts-on-p s e)
               (equal (fn-rtc-e-id e) 1) (equal (fn-rtc-e-kind e) :hand)
               (not (fn-rtc-hand-delivers-p s e)))
          (and (fn-pth-i (mv-nth 0 (fn-pth-step s e q)))
               (not (mv-nth 2 (fn-pth-step* s e q)))))
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-runtime-and-post-state-by-definition fn-pth-i-nondelivering-owner-completion
        fn-pth-i-found-hand-facts fn-pth-i-hand-buffer-untracked
        fn-pth-i-returned-hand-buffer fn-pth-i-end-use-hand
        (:instance fn-pth-i-returned-hand-delivery
         (s (fn-rtc-end-use s e))
         (ev (fn-rtc-ev :hand
              (if (equal (fn-rtc-get 0 (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e)) :done)
                  '(:failed :gone) (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e))
              1 1
              (list (list (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))
                          (+ 1 (fn-rtc-b-gen (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) s)))
                          0 (len (fn-rtc-b-bytes (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) s)))))))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-step fn-pth-step* fn-pth-i-end-use-hand fn-pth-i-rearm
     fn-pth-i-mstate-of-end-use fn-rtc-config-of-end-use
     fn-rtc-ev fn-rtc-ev-id fn-rtc-get-of-cons fn-pth-i-made-handle-properties
     fn-rtc-buffer-accessors len true-listp natp nfix
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition car-cons cdr-cons
     (:type-prescription fn-rtc-b-gen) (:type-prescription fn-rtc-h-buf) (:type-prescription len)
     default-+-1 default-+-2 (:executable-counterpart equal) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+)
     (:executable-counterpart <) (:executable-counterpart member-equal))))))

(verify-guards fn-pth-i-queue-avoids)
(verify-guards fn-pth-i-storage-avoids)

; Incoming hand admission into queue or idle owner; full I.

; From p15d-I-queue-append.lisp
(defthm fn-pth-i-queue-true-listp
 (implies (fn-pth-i-queue ps s used) (true-listp ps))
 :hints (("Goal" :induct (fn-pth-i-queue ps s used)
  :in-theory (union-theories (theory 'minimal-theory) '(fn-pth-i-queue true-listp)))))
(defthm fn-pth-i-queue-append-post
 (implies (and (fn-pth-i-queue ps s used) (fn-pth-i-post p s nil)
               (equal (len (fn-rtc-b-bytes (fn-rtc-buffer (fn-ptx-cur-bp p) s))) (fn-ptx-cur-len p))
               (fn-pth-i-queue-avoids ps (fn-ptx-cur-bp p))
               (not (member-equal (fn-ptx-cur-bp p) used)))
          (fn-pth-i-queue (append ps (list p)) s used))
 :hints (("Goal" :induct (fn-pth-i-queue ps s used)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-queue fn-pth-i-queue-avoids binary-append member-equal car-cons cdr-cons
     (:executable-counterpart fn-pth-i-queue))))))
(defthm fn-pth-i-queue-fix
 (implies (fn-pth-i-queue ps s used) (equal (true-list-fix ps) ps))
 :hints (("Goal" :induct (fn-pth-i-queue ps s used)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-queue true-list-fix car-cons cdr-cons)))))
(defthm fn-pth-i-post-storage-append-post
 (let ((m2 (fn-ptx-chg m :committed nil :q (append (true-list-fix (fn-ptx-q m)) (list p)))))
  (implies (and (fn-pth-i-post-storage m s) (fn-ptx-okp m2)
                (fn-pth-i-post p s nil)
                (equal (len (fn-rtc-b-bytes (fn-rtc-buffer (fn-ptx-cur-bp p) s))) (fn-ptx-cur-len p))
                (fn-pth-i-storage-avoids m (fn-ptx-cur-bp p)))
           (fn-pth-i-post-storage m2 s)))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-post-storage fn-pth-i-storage-avoids fn-ptx-accessors-of-mk
     fn-ptx-nmsg-of-mk fn-ptx-nmsg-is-g fn-ptx-elen
     fn-pth-i-queue-append-post fn-pth-i-queue-true-listp fn-pth-i-queue-fix
     fn-ptx-in-flight-p member-equal binary-append car-cons cdr-cons
     (:type-prescription fn-ptx-ext) (:type-prescription fn-ptx-nxt) nfix natp
     (:executable-counterpart equal) (:executable-counterpart member-equal))))))

; From p15d-I-queue-protocol.lisp
(defthm fn-pth-i-expected-same-phase
 (implies (equal (fn-ptx-ph m2) (fn-ptx-ph m))
          (equal (fn-ptx-expected m2) (fn-ptx-expected m)))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-expected)))))
(defthm fn-pth-i-owner-uses-same-phase
 (implies (equal (fn-ptx-ph m2) (fn-ptx-ph m))
          (equal (fn-pth-i-owner-uses uses m2) (fn-pth-i-owner-uses uses m)))
 :rule-classes nil
 :hints (("Goal" :induct (fn-pth-i-owner-uses uses m)
  :expand ((fn-pth-i-owner-uses uses m2) (fn-pth-i-owner-uses uses m))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-owner-uses fn-ptx-expected)))))
(defthm fn-pth-i-owner-uses-append-post
 (equal (fn-pth-i-owner-uses uses (fn-ptx-chg m :committed nil :q (append (true-list-fix (fn-ptx-q m)) (list p))))
        (fn-pth-i-owner-uses uses m))
 :hints (("Goal" :use ((:instance fn-pth-i-owner-uses-same-phase
  (m2 (fn-ptx-chg m :committed nil :q (append (true-list-fix (fn-ptx-q m)) (list p))))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-accessors-of-mk)))))
(defthm fn-pth-i-expected-append-post
 (equal (fn-ptx-expected (fn-ptx-chg m :committed nil :q (append (true-list-fix (fn-ptx-q m)) (list p))))
        (fn-ptx-expected m))
 :hints (("Goal" :use ((:instance fn-pth-i-expected-same-phase
  (m2 (fn-ptx-chg m :committed nil :q (append (true-list-fix (fn-ptx-q m)) (list p))))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-accessors-of-mk)))))
(defthm fn-pth-i-post-state-append-post
 (let ((m2 (fn-ptx-chg m :committed nil :q (append (true-list-fix (fn-ptx-q m)) (list p)))))
  (implies (and (fn-pth-i-post-state m s) (fn-ptx-okp m2)
                (fn-pth-i-post p s nil)
                (equal (len (fn-rtc-b-bytes (fn-rtc-buffer (fn-ptx-cur-bp p) s))) (fn-ptx-cur-len p))
                (fn-pth-i-storage-avoids m (fn-ptx-cur-bp p)))
           (fn-pth-i-post-state m2 s)))
 :hints (("Goal"
  :use (fn-pth-i-post-storage-and-protocol-by-definition
        (:instance fn-pth-i-post-storage-and-protocol-by-definition
          (m (fn-ptx-chg m :committed nil :q (append (true-list-fix (fn-ptx-q m)) (list p))))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-post-storage-append-post fn-pth-i-owner-uses-append-post
     fn-pth-i-expected-append-post)))))
(defthm fn-pth-i-handed-queue-delivery
 (let* ((hd (fn-rtc-get 6 ev))
        (p (list (fn-ptx-atom (fn-rtc-get 4 ev)) (fn-ptx-atom (fn-rtc-get 5 ev))
                 (fn-rtc-h-buf hd) (fn-rtc-h-len hd))))
  (implies (and (fn-pth-i s) (equal (fn-rtc-ev-id ev) 1) (equal (fn-rtc-get 0 ev) :handed)
                (not (member-eq (fn-ptx-ph (fn-rtc-mstate 1 s)) '(:closed :fenced :idle)))
                (< (len (fn-ptx-q (fn-rtc-mstate 1 s))) *fn-ptx-k*)
                (fn-pth-i-post p s nil)
                (equal (len (fn-rtc-b-bytes (fn-rtc-buffer (fn-ptx-cur-bp p) s))) (fn-ptx-cur-len p))
                (fn-pth-i-storage-avoids (fn-rtc-mstate 1 s) (fn-ptx-cur-bp p)))
           (and (fn-pth-i (mv-nth 0 (fn-pth-deliver s 1 1 ev q)))
                (not (mv-nth 2 (fn-pth-deliver s 1 1 ev q))))))
 :hints (("Goal"
  :use (fn-pth-i-runtime-and-post-state-by-definition
        (:instance fn-pth-i-post-storage-and-protocol-by-definition (m (fn-rtc-mstate 1 s)))
        (:instance fn-pth-i-post-storage-machine-facts (m (fn-rtc-mstate 1 s)))
        (:instance fn-ptx-step-keeps-ok (m (fn-rtc-mstate 1 s))
         (st (fn-rtc-view-state 1 1 s)) (q (nfix q)))
        (:instance fn-pth-i-no-requests-owner-deliver))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-m-step fn-pthm-step fn-ptx-step fn-ptx-step1 fn-ptx-okp-wfp
     fn-pth-i-post-state-append-post fn-ptx-accessors-of-mk nfix natp
     (:type-prescription fn-ptx-ext) (:type-prescription fn-ptx-nxt) (:type-prescription fn-ptx-k)
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-1-cons-by-definition
     fn-pth-i-no-requests-deliver-refusals fn-rtc-get-of-cons member-equal car-cons cdr-cons
     (:executable-counterpart equal) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart nfix) (:executable-counterpart zp)
     (:executable-counterpart member-equal))))))

; From p15d-I-incoming-hand.lisp
(defthm fn-pth-i-hand-to-owner-facts
 (let* ((u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))
        (hd (fn-rtc-u-hd u)) (h (fn-rtc-h-buf hd)) (b (fn-rtc-buffer h s)) (o (fn-rtc-b-owner b)))
  (implies (and (fn-pth-i-runtime s) (fn-rtc-hand-delivers-p s e) (equal (fn-rtc-hand-to s e) 1))
   (and (fn-rtc-completionp e) u (equal (fn-rtc-e-kind e) :hand)
        (fn-rtc-handlep hd) (< h (fn-rtc-nbufs (fn-rtc-config s)))
        (equal (fn-rtc-get 0 o) :handed) (equal (fn-rtc-get 3 o) 1) (equal (fn-rtc-get 4 o) 1)
        (< 1 (fn-rtc-e-id e)) (< (fn-rtc-e-id e) (fn-rtc-nslots (fn-rtc-config s)))
        (fn-rtc-u64p (fn-rtc-e-inc e)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-found-hand-facts
        (:instance fn-pth-i-runtime-buffer-metadata
          (h (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-rtc-hand-delivers-p fn-rtc-hand-to fn-rtc-handed-to-live-p
     fn-rtc-live-p fn-pth-i-buffer-state-okp fn-pth-i-buffer-ownerp
     fn-rtc-u64p-implies-natp natp nfix posp
     (:type-prescription fn-rtc-e-id) (:type-prescription fn-rtc-h-buf)
     (:executable-counterpart fn-rtc-s-inc) (:executable-counterpart fn-rtc-s-status)
     (:executable-counterpart equal))))))
(defthm fn-pth-i-incoming-hand-buffer
 (let* ((u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))
        (h (fn-rtc-h-buf (fn-rtc-u-hd u))) (b (fn-rtc-buffer h s)))
  (implies (and (fn-pth-i-runtime s) (fn-rtc-hand-delivers-p s e) (equal (fn-rtc-hand-to s e) 1))
           (equal (fn-rtc-buffer h (fn-rtc-end-use s e))
                  (list (+ 1 (fn-rtc-b-gen b)) '(:workspace 1 1) (fn-rtc-b-bytes b)))))
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-hand-to-owner-facts fn-pth-i-found-hand-facts
        (:instance fn-rtc-matching-use-fields (uses (fn-rtc-uses s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-rtc-shapep fn-rtc-end-use fn-rtc-end-lease
     fn-rtc-lease-return fn-rtc-hand-delivers-p fn-rtc-handed-to-live-p
     fn-rtc-retire-drained-frame fn-rtc-lease-return-of-with-uses
     fn-rtc-live-p fn-rtc-current-p fn-rtc-with-accessors fn-rtc-buffer-of-with fn-rtc-slot-of-with
     fn-rtc-buffer-accessors fn-rtc-get-of-cons car-cons cdr-cons
     natp nfix (:type-prescription fn-rtc-h-buf)
     (:executable-counterpart fn-rtc-get) (:executable-counterpart fn-rtc-s-inc)
     (:executable-counterpart fn-rtc-s-status) (:executable-counterpart equal)
     (:executable-counterpart member-equal) (:executable-counterpart nfix)
     (:executable-counterpart zp))))))

; From p15d-I-handed-queue-step.lisp
(defthm fn-pth-i-owner-handed-queue-step
 (implies (and (fn-pth-i s) (fn-rtc-hand-delivers-p s e) (equal (fn-rtc-hand-to s e) 1)
               (not (member-eq (fn-ptx-ph (fn-rtc-mstate 1 s)) '(:closed :fenced :idle)))
               (< (len (fn-ptx-q (fn-rtc-mstate 1 s))) *fn-ptx-k*))
          (and (fn-pth-i (mv-nth 0 (fn-pth-step s e q)))
               (not (mv-nth 2 (fn-pth-step* s e q)))))
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-runtime-and-post-state-by-definition
        fn-pth-i-hand-to-owner-facts fn-pth-i-incoming-hand-buffer
        fn-pth-i-hand-buffer-untracked fn-pth-i-end-use-hand
        (:instance fn-pth-i-handed-queue-delivery
         (s (fn-rtc-end-use s e))
         (ev (fn-rtc-ev :handed
               (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e)
               1 1
               (list (fn-rtc-e-id e) (fn-rtc-e-inc e)
                (list (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))
                      (+ 1 (fn-rtc-b-gen (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) s)))
                      0 (len (fn-rtc-b-bytes (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) s)))))))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-step fn-pth-step* fn-pth-i-rearm fn-rtc-acts-on-p fn-rtc-hand-to
     fn-pth-i-mstate-of-end-use fn-rtc-config-of-end-use fn-rtc-ev fn-rtc-ev-id
     fn-pth-i-post fn-pth-i-visible-buffer fn-ptx-atom fn-ptx-cur-bp fn-ptx-cur-len
     fn-ptx-cur-fid fn-ptx-cur-finc fn-rtc-h-buf fn-rtc-h-len fn-rtc-buffer-accessors
     fn-rtc-get-of-cons len true-listp natp nfix fn-rtc-u64p-implies-natp
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition car-cons cdr-cons
     (:type-prescription fn-rtc-e-id) (:type-prescription fn-rtc-e-inc)
     (:type-prescription fn-rtc-b-gen) (:type-prescription fn-rtc-h-buf) (:type-prescription len)
     (:executable-counterpart equal) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+)
     (:executable-counterpart member-equal))))))

; From p15d-I-start-storage.lisp
(defthm fn-pth-i-post-storage-start
 (implies (and (fn-pth-i-post p s nil)
               (equal (len (fn-rtc-b-bytes (fn-rtc-buffer (fn-ptx-cur-bp p) s))) (fn-ptx-cur-len p))
               (fn-pth-i-queue ps s (list (fn-ptx-cur-bp p)))
               (fn-cbor-octet-listp (fn-ptx-kd-last kd))
               (< (nfix ext) (expt 2 64))
               (fn-ptx-okp (mv-nth 0 (fn-ptx-start p ps kd ext geo committed))))
          (fn-pth-i-post-storage (mv-nth 0 (fn-ptx-start p ps kd ext geo committed)) s))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-post-storage fn-pth-i-post fn-ptx-in-flight-p fn-ptx-start fn-ptx-accessors-of-mk
     fn-ptx-cur-fid fn-ptx-cur-finc fn-ptx-cur-bp fn-ptx-cur-len fn-ptx-cur-hoff
     fn-ptx-cur-ioff fn-ptx-cur-base fn-ptx-cur-glen fn-rtc-get-of-cons
     fn-hld-mv-nth-0-cons member-equal binary-append nfix natp car-cons cdr-cons
     (:type-prescription fn-ptx-cur-bp) (:type-prescription fn-ptx-cur-len)
     (:executable-counterpart equal) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart nfix) (:executable-counterpart zp)
     (:executable-counterpart member-equal))))))
(defthm fn-pth-i-idle-owner-uses-only-hands
 (implies (and (fn-pth-i-owner-uses uses m) (equal (fn-ptx-ph m) :idle))
          (fn-pth-i-owner-uses uses nil))
 :hints (("Goal" :induct (fn-pth-i-owner-uses uses m)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-owner-uses fn-ptx-expected (:executable-counterpart fn-ptx-ph)
     (:executable-counterpart fn-ptx-expected) (:executable-counterpart member-equal)
     (:executable-counterpart equal))))))

; From p15d-I-idle-machine.lisp
(defthm fn-pth-i-handed-idle-machine-projections
 (let* ((hd (fn-rtc-get 6 ev))
        (p (list (fn-ptx-atom (fn-rtc-get 4 ev)) (fn-ptx-atom (fn-rtc-get 5 ev))
                 (fn-rtc-h-buf hd) (fn-rtc-h-len hd)))
        (r (fn-pth-m-step m ev st q)))
  (implies (and (fn-ptx-wfp m) (equal (fn-ptx-ph m) :idle)
                (equal (fn-rtc-ev-id ev) 1) (equal (fn-rtc-get 0 ev) :handed))
   (and (equal (mv-nth 0 r)
               (mv-nth 0 (fn-ptx-start p nil (fn-ptx-kd m) (fn-ptx-ext m) (fn-ptx-geo m) nil)))
        (equal (mv-nth 1 r) (list (fn-ptx-timer))))))
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '(fn-pth-m-step fn-pthm-step fn-ptx-step fn-ptx-step1 fn-ptx-start fn-ptx-accessors-of-mk
    fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-1-cons-by-definition nfix natp
    (:type-prescription fn-ptx-ext) (:type-prescription fn-ptx-nxt)
    car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart member-equal))))))
(defthm fn-pth-i-owner-machine-keeps-ok
 (implies (and (fn-ptx-okp m) (equal (fn-rtc-ev-id ev) 1))
          (fn-ptx-okp (mv-nth 0 (fn-pth-m-step m ev st q))))
 :hints (("Goal" :use (fn-ptx-step-keeps-ok)
  :in-theory (union-theories (theory 'minimal-theory) '(fn-pth-m-step fn-pth-at-the-owner)))))
(defthm fn-pth-i-post-storage-scalars
 (implies (fn-pth-i-post-storage m s)
  (and (fn-ptx-okp m) (fn-cbor-octet-listp (fn-ptx-kd-last (fn-ptx-kd m)))
       (< (fn-ptx-ext m) (expt 2 64)) (< (fn-ptx-nxt m) (expt 2 64))))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pth-i-post-storage)))))
(defthm fn-pth-i-handed-idle-machine-storage
 (let* ((hd (fn-rtc-get 6 ev))
        (p (list (fn-ptx-atom (fn-rtc-get 4 ev)) (fn-ptx-atom (fn-rtc-get 5 ev))
                 (fn-rtc-h-buf hd) (fn-rtc-h-len hd))))
  (implies (and (fn-pth-i-post-storage m s) (equal (fn-ptx-ph m) :idle)
                (equal (fn-rtc-ev-id ev) 1) (equal (fn-rtc-get 0 ev) :handed)
                (fn-pth-i-post p s nil)
                (equal (len (fn-rtc-b-bytes (fn-rtc-buffer (fn-ptx-cur-bp p) s))) (fn-ptx-cur-len p)))
           (fn-pth-i-post-storage (mv-nth 0 (fn-pth-m-step m ev st q)) s)))
 :hints (("Goal"
  :use (fn-pth-i-post-storage-scalars fn-pth-i-owner-machine-keeps-ok fn-ptx-okp-wfp
        (:instance fn-pth-i-post-storage-start
         (p (list (fn-ptx-atom (fn-rtc-get 4 ev)) (fn-ptx-atom (fn-rtc-get 5 ev))
                  (fn-rtc-h-buf (fn-rtc-get 6 ev)) (fn-rtc-h-len (fn-rtc-get 6 ev))))
         (ps nil) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m)) (geo (fn-ptx-geo m)) (committed nil)))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-handed-idle-machine-projections fn-pth-i-post-storage-machine-facts
     fn-ptx-okp-wfp fn-pth-i-queue-nil nfix natp
     (:type-prescription fn-ptx-ext) (:type-prescription fn-ptx-nxt)
     (:executable-counterpart nfix))))))

; From p15d-I-idle-protocol.lisp
(defthm fn-pth-i-handed-idle-machine-protocol
 (let ((m2 (mv-nth 0 (fn-pth-m-step m ev st q))))
  (implies (and (fn-ptx-wfp m) (equal (fn-ptx-ph m) :idle)
                (equal (fn-rtc-ev-id ev) 1) (equal (fn-rtc-get 0 ev) :handed)
                (fn-pth-i-owner-uses uses m))
   (and (fn-pth-i-owner-uses uses m2) (equal (fn-ptx-expected m2) :timer)
        (not (fn-rtc-kind-out-p :timer 1 1 uses)))))
 :hints (("Goal" :use (fn-pth-i-idle-owner-uses-only-hands)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-handed-idle-machine-projections fn-ptx-start fn-hld-mv-nth-0-cons
     fn-ptx-accessors-of-mk fn-ptx-expected fn-pth-i-hands-only-compatible-with-every-machine
     fn-pth-i-hands-only-has-no-operation (:executable-counterpart member-equal)
     (:executable-counterpart equal))))))

; From p15d-I-handed-idle-delivery.lisp
(defthm fn-pth-i-handed-idle-delivery
 (let* ((hd (fn-rtc-get 6 ev))
        (p (list (fn-ptx-atom (fn-rtc-get 4 ev)) (fn-ptx-atom (fn-rtc-get 5 ev))
                 (fn-rtc-h-buf hd) (fn-rtc-h-len hd))))
  (implies (and (fn-pth-i s) (equal (fn-rtc-ev-id ev) 1) (equal (fn-rtc-get 0 ev) :handed)
                (equal (fn-ptx-ph (fn-rtc-mstate 1 s)) :idle)
                (fn-pth-i-post p s nil)
                (equal (len (fn-rtc-b-bytes (fn-rtc-buffer (fn-ptx-cur-bp p) s))) (fn-ptx-cur-len p)))
           (and (fn-pth-i (mv-nth 0 (fn-pth-deliver s 1 1 ev q)))
                (not (mv-nth 2 (fn-pth-deliver s 1 1 ev q))))))
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-timer-and-fsync-data fn-pth-i-runtime-and-post-state-by-definition
        (:instance fn-pth-i-post-storage-and-protocol-by-definition (m (fn-rtc-mstate 1 s)))
        (:instance fn-pth-i-post-storage-machine-facts (m (fn-rtc-mstate 1 s)))
        (:instance fn-ptx-okp-wfp (m (fn-rtc-mstate 1 s)))
        (:instance fn-pth-i-handed-idle-machine-storage
         (m (fn-rtc-mstate 1 s)) (st (fn-rtc-view-state 1 1 s)) (q (nfix q)))
        (:instance fn-pth-i-handed-idle-machine-protocol
         (m (fn-rtc-mstate 1 s)) (st (fn-rtc-view-state 1 1 s)) (q (nfix q)) (uses (fn-rtc-uses s)))
        (:instance fn-pth-i-single-owner-unbuffered-deliver (r (fn-ptx-timer))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-handed-idle-machine-projections
     fn-ptx-timer fn-rtc-get-of-cons car-cons cdr-cons
     (:executable-counterpart equal) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart nfix) (:executable-counterpart zp)
     (:executable-counterpart fn-rtc-buffered-kind-p) (:executable-counterpart member-equal))))))

; From p15d-I-handed-idle-step.lisp
(defthm fn-pth-i-owner-handed-idle-step
 (implies (and (fn-pth-i s) (fn-rtc-hand-delivers-p s e) (equal (fn-rtc-hand-to s e) 1)
               (equal (fn-ptx-ph (fn-rtc-mstate 1 s)) :idle))
          (and (fn-pth-i (mv-nth 0 (fn-pth-step s e q)))
               (not (mv-nth 2 (fn-pth-step* s e q)))))
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-runtime-and-post-state-by-definition
        fn-pth-i-hand-to-owner-facts fn-pth-i-incoming-hand-buffer
        fn-pth-i-end-use-hand
        (:instance fn-pth-i-handed-idle-delivery
         (s (fn-rtc-end-use s e))
         (ev (fn-rtc-ev :handed
               (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e)
               1 1
               (list (fn-rtc-e-id e) (fn-rtc-e-inc e)
                (list (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))
                      (+ 1 (fn-rtc-b-gen (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) s)))
                      0 (len (fn-rtc-b-bytes (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) s)))))))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-step fn-pth-step* fn-pth-i-rearm fn-rtc-acts-on-p fn-rtc-hand-to
     fn-pth-i-mstate-of-end-use fn-rtc-config-of-end-use fn-rtc-ev fn-rtc-ev-id
     fn-pth-i-post fn-pth-i-visible-buffer fn-ptx-atom fn-ptx-cur-bp fn-ptx-cur-len
     fn-ptx-cur-fid fn-ptx-cur-finc fn-rtc-h-buf fn-rtc-h-len fn-rtc-buffer-accessors
     fn-rtc-get-of-cons len true-listp natp nfix fn-rtc-u64p-implies-natp
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition car-cons cdr-cons
     (:type-prescription fn-rtc-e-id) (:type-prescription fn-rtc-e-inc)
     (:type-prescription fn-rtc-b-gen) (:type-prescription fn-rtc-h-buf) (:type-prescription len)
     (:executable-counterpart equal) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+)
     (:executable-counterpart member-equal))))))

; Shared replies and all actual owner incoming-hand completion branches.

; From p15d-I-answer-facts.lisp
(defthm fn-pth-i-buffer-cap-positive
 (implies (fn-pth-i-runtime s) (< 0 (fn-rtc-buf-cap h (fn-rtc-config s))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-rtc-buf-cap fn-rtc-nhome fn-rtc-nconnection-home
     posp natp default-+-1 default-+-2 default-*-1 default-*-2
     (:executable-counterpart <) (:executable-counterpart binary-*))))))
(defthm fn-pth-i-post-target-is-u64
 (implies (and (fn-pth-i-runtime s) (fn-pth-i-post p s lp))
          (and (fn-rtc-u64p (fn-ptx-cur-fid p)) (posp (fn-ptx-cur-fid p))
               (fn-rtc-u64p (fn-ptx-cur-finc p))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-runtime fn-pth-i-post fn-rtc-st-cfg-okp fn-rtc-u64p posp natp
    (:executable-counterpart expt) (:executable-counterpart <))))))
(defthm fn-pth-i-visible-owner-readers
 (implies (and (fn-pth-i-runtime s) (fn-pth-i-visible-buffer h s t))
  (and (equal (fn-ptx-gen h 1 1 s) (fn-rtc-b-gen (fn-rtc-buffer h s)))
       (equal (fn-rtc-st-v-fill h 1 1 s) (len (fn-rtc-b-bytes (fn-rtc-buffer h s))))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-runtime fn-rtc-shapep fn-pth-i-visible-buffer fn-ptx-gen
    fn-rtc-st-v-gen fn-rtc-st$a-v-gen fn-rtc-st-v-fill fn-rtc-st$a-v-fill
    fn-rtc-vb fn-rtc-view fn-rtc-c-get-of-view-pool fn-rtc-view-own-p fn-rtc-buffer
    nfix natp default-+-1 default-+-2 (:executable-counterpart natp))))))

; From p15d-I-answer-write.lisp
(defthm fn-pth-i-untracked-code-write
 (let* ((g (fn-rtc-b-gen (fn-rtc-buffer h s)))
        (r (list :write h g 0 (list code))))
  (implies (and (fn-pth-i s) (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
                (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:workspace 1 1))
                (fn-cbor-octetp code) (fn-pth-i-storage-avoids (fn-rtc-mstate 1 s) h))
   (and (fn-pth-i (mv-nth 0 (fn-rtc-request r 1 1 s)))
        (not (mv-nth 2 (fn-rtc-request r 1 1 s)))
        (equal (mv-nth 0 (fn-rtc-request r 1 1 s))
               (fn-rtc-with-buffer h (list g '(:workspace 1 1)
                (fn-rtc-splice (fn-rtc-b-bytes (fn-rtc-buffer h s)) 0 (list code))) s)))))
 :hints (("Goal"
  :use (fn-pth-i-runtime-and-post-state-by-definition fn-pth-i-buffer-cap-positive
        (:instance fn-pth-i-owner-untracked-request
          (r (list :write h (fn-rtc-b-gen (fn-rtc-buffer h s)) 0 (list code)))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-request fn-rtc-req-write fn-cbor-octet-listp fn-rtc-get-of-cons
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition
     member-equal len true-listp car-cons cdr-cons natp
     (:type-prescription len) (:type-prescription fn-rtc-buf-cap)
     (:executable-counterpart equal) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+)
     (:executable-counterpart fn-cbor-octet-listp) (:executable-counterpart <))))))

; From p15d-I-answer-hand.lisp
(defthm fn-pth-i-untracked-hand-request
 (let* ((b (fn-rtc-buffer h s))
        (r (list :submit :hand (list h (fn-rtc-b-gen b) 0 (len (fn-rtc-b-bytes b))) (list fid finc))))
  (implies (and (fn-pth-i s) (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
                (equal (fn-rtc-b-owner b) '(:workspace 1 1))
                (fn-rtc-u64p fid) (< 1 fid) (< fid (fn-rtc-nslots (fn-rtc-config s)))
                (fn-rtc-u64p finc) (fn-pth-i-storage-avoids (fn-rtc-mstate 1 s) h))
           (and (fn-pth-i (mv-nth 0 (fn-rtc-request r 1 1 s)))
                (not (mv-nth 2 (fn-rtc-request r 1 1 s))))))
 :hints (("Goal"
  :use (fn-pth-i-runtime-and-post-state-by-definition
        (:instance fn-pth-request-factors (id 1) (inc 1)
         (r (list :submit :hand (list h (fn-rtc-b-gen (fn-rtc-buffer h s)) 0
              (len (fn-rtc-b-bytes (fn-rtc-buffer h s)))) (list fid finc))))
        (:instance fn-pth-i-owner-untracked-request
         (r (list :submit :hand (list h (fn-rtc-b-gen (fn-rtc-buffer h s)) 0
              (len (fn-rtc-b-bytes (fn-rtc-buffer h s)))) (list fid finc)))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-pth-req-data-okp fn-pth-req-state-okp fn-rtc-live-p
     fn-rtc-kind-extrap fn-rtc-extrap fn-rtc-handlep fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len
     fn-rtc-get-of-cons len true-listp fn-rtc-u64p-implies-natp fn-rtc-u64p natp nfix posp car-cons cdr-cons
     (:type-prescription fn-rtc-b-gen) (:type-prescription len)
     (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+)
     (:executable-counterpart fn-rtc-buffered-kind-p) (:executable-counterpart member-equal)
     (:executable-counterpart fn-rtc-s-inc) (:executable-counterpart fn-rtc-s-status))))))

; From p15d-I-answer-physical.lisp
(defthm fn-pth-i-answer-physical-by-definition
 (let* ((h (fn-ptx-cur-bp p)) (b (fn-rtc-buffer h s))
        (g (fn-rtc-b-gen b)) (n (max 1 (len (fn-rtc-b-bytes b)))))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post p s nil))
   (equal (fn-ptx-answer p o 1 1 s)
          (list (list :write h g 0 (list (fn-ptx-code o)))
                (list :submit :hand (list h g 0 n) (list (fn-ptx-cur-fid p) (fn-ptx-cur-finc p)))))))
 :hints (("Goal" :use ((:instance fn-pth-i-visible-owner-readers (h (fn-ptx-cur-bp p))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-ptx-answer fn-pth-i-post fn-pth-i-visible-buffer nfix natp (:type-prescription len)
     (:type-prescription fn-ptx-cur-bp))))))

; From p15d-I-answer-splice.lisp
(defthm fn-pth-i-code-splice-length
 (implies (true-listp bytes)
  (equal (len (fn-rtc-splice bytes 0 (list code))) (max 1 (len bytes))))
 :hints (("Goal" :use ((:instance fn-rtc-splice-length (off 0) (data (list code))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(len true-listp max (:type-prescription len) natp car-cons cdr-cons
     (:executable-counterpart binary-+) (:executable-counterpart natp))))))

; From p15d-I-answer-core.lisp
(defthm fn-pth-i-untracked-answer-physical
 (implies (and (fn-pth-i s) (fn-pth-i-post p s nil)
               (fn-pth-i-storage-avoids (fn-rtc-mstate 1 s) (fn-ptx-cur-bp p)))
          (and (fn-pth-i (mv-nth 0 (fn-rtc-requests (list (list :write (fn-ptx-cur-bp p) (fn-rtc-b-gen (fn-rtc-buffer (fn-ptx-cur-bp p) s)) 0 (list (fn-ptx-code o)))
           (list :submit :hand (list (fn-ptx-cur-bp p) (fn-rtc-b-gen (fn-rtc-buffer (fn-ptx-cur-bp p) s)) 0
             (max 1 (len (fn-rtc-b-bytes (fn-rtc-buffer (fn-ptx-cur-bp p) s)))))
             (list (fn-ptx-cur-fid p) (fn-ptx-cur-finc p)))) 1 1 s)))
               (not (mv-nth 2 (fn-rtc-requests (list (list :write (fn-ptx-cur-bp p) (fn-rtc-b-gen (fn-rtc-buffer (fn-ptx-cur-bp p) s)) 0 (list (fn-ptx-code o)))
           (list :submit :hand (list (fn-ptx-cur-bp p) (fn-rtc-b-gen (fn-rtc-buffer (fn-ptx-cur-bp p) s)) 0
             (max 1 (len (fn-rtc-b-bytes (fn-rtc-buffer (fn-ptx-cur-bp p) s)))))
             (list (fn-ptx-cur-fid p) (fn-ptx-cur-finc p)))) 1 1 s)))))
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-runtime-shape-by-definition fn-pth-i-runtime-and-post-state-by-definition
        fn-pth-answer-code-is-octet
        (:instance fn-pth-i-post-target-is-u64 (lp nil))
        (:instance fn-rtc-c-shapep-buffer (h (fn-ptx-cur-bp p)))
        (:instance fn-pth-i-untracked-code-write (h (fn-ptx-cur-bp p)) (code (fn-ptx-code o)))
        (:instance fn-pth-i-untracked-hand-request
          (s (mv-nth 0 (fn-rtc-request
           (list :write (fn-ptx-cur-bp p) (fn-rtc-b-gen (fn-rtc-buffer (fn-ptx-cur-bp p) s)) 0 (list (fn-ptx-code o)))
           1 1 s)))
          (h (fn-ptx-cur-bp p)) (fid (fn-ptx-cur-fid p)) (finc (fn-ptx-cur-finc p))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-untracked-code-write fn-pth-i-post fn-pth-i-visible-buffer fn-rtc-shapep
     fn-rtc-requests binary-append fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition
     fn-rtc-with-accessors fn-rtc-buffer-of-with fn-rtc-mstate-of-with fn-rtc-buffer-accessors
     fn-pth-i-code-splice-length fn-rtc-splice-length fn-cbor-octet-listp-implies-true-listp
     fn-rtc-b-bytes fn-rtc-get-of-cons max len true-listp nfix natp car-cons cdr-cons
     (:type-prescription len) (:type-prescription fn-ptx-cur-bp) (:type-prescription fn-rtc-b-gen)
     (:executable-counterpart equal) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+)
     (:executable-counterpart len) (:executable-counterpart true-listp))))))

; From p15d-I-answer.lisp
(defthm fn-pth-i-untracked-answer
 (implies (and (fn-pth-i s) (fn-pth-i-post p s nil)
               (fn-pth-i-storage-avoids (fn-rtc-mstate 1 s) (fn-ptx-cur-bp p)))
          (and (fn-pth-i (mv-nth 0 (fn-rtc-requests (fn-ptx-answer p o 1 1 s) 1 1 s)))
               (not (mv-nth 2 (fn-rtc-requests (fn-ptx-answer p o 1 1 s) 1 1 s)))))
 :hints (("Goal" :use (fn-pth-i-runtime-and-post-state-by-definition fn-pth-i-untracked-answer-physical)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-answer-physical-by-definition)))))

; From p15d-I-answer-deliver.lisp
(defthm fn-pth-i-answer-with-mstate
 (equal (fn-ptx-answer p o 1 1 (fn-rtc-with-mstate j m s)) (fn-ptx-answer p o 1 1 s))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-ptx-answer fn-ptx-gen fn-rtc-st-v-gen fn-rtc-st$a-v-gen fn-rtc-st-v-fill fn-rtc-st$a-v-fill
    fn-rtc-vb fn-rtc-view fn-rtc-with-accessors)))))
(defthm fn-pth-i-answer-after-machine
 (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-state m s) (fn-pth-i-post p s nil)
               (fn-pth-i-storage-avoids m (fn-ptx-cur-bp p)))
          (and (fn-pth-i (mv-nth 0 (fn-rtc-requests (fn-ptx-answer p o 1 1 s) 1 1 (fn-rtc-with-mstate 1 m s))))
               (not (mv-nth 2 (fn-rtc-requests (fn-ptx-answer p o 1 1 s) 1 1 (fn-rtc-with-mstate 1 m s))))))
 :hints (("Goal" :use ((:instance fn-pth-i-untracked-answer (s (fn-rtc-with-mstate 1 m s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-install-owner-state fn-pth-i-answer-with-mstate fn-pth-i-post fn-pth-i-visible-buffer
     fn-rtc-mstate-of-with fn-pth-i-owner-machine-index fn-rtc-buffer-of-with fn-rtc-with-accessors
     (:executable-counterpart nfix) (:executable-counterpart natp))))))
(defthm fn-pth-i-answer-owner-deliver
 (let* ((step (fn-pth-m-step (fn-rtc-mstate 1 s) ev (fn-rtc-view-state 1 1 s) (nfix q)))
        (m (mv-nth 0 step)))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-state m s)
                (equal (mv-nth 1 step) (fn-ptx-answer p o 1 1 s))
                (fn-pth-i-post p s nil) (fn-pth-i-storage-avoids m (fn-ptx-cur-bp p)))
           (and (fn-pth-i (mv-nth 0 (fn-pth-deliver s 1 1 ev q)))
                (not (mv-nth 2 (fn-pth-deliver s 1 1 ev q))))))
 :hints (("Goal" :use ((:instance fn-pth-i-answer-after-machine
   (m (mv-nth 0 (fn-pth-m-step (fn-rtc-mstate 1 s) ev (fn-rtc-view-state 1 1 s) (nfix q))))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-deliver fn-rtc-view-state fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition
     car-cons cdr-cons)))))

; From p15d-I-handed-reply-host-delivery.lisp
(defthm fn-pth-i-handed-reply-host-delivery
 (let* ((hd (fn-rtc-get 6 (fn-rtc-ev :handed out 1 1 (list fid finc hd))))
        (p (list (fn-ptx-atom (fn-rtc-get 4 (fn-rtc-ev :handed out 1 1 (list fid finc hd)))) (fn-ptx-atom (fn-rtc-get 5 (fn-rtc-ev :handed out 1 1 (list fid finc hd))))
                 (fn-rtc-h-buf hd) (fn-rtc-h-len hd)))
        (m (fn-rtc-mstate 1 s)))
  (implies (and (fn-pth-i s) (equal (fn-rtc-ev-id (fn-rtc-ev :handed out 1 1 (list fid finc hd))) 1) (equal (fn-rtc-get 0 (fn-rtc-ev :handed out 1 1 (list fid finc hd))) :handed)
                (or (member-eq (fn-ptx-ph m) '(:closed :fenced))
                    (and (not (equal (fn-ptx-ph m) :idle)) (<= *fn-ptx-k* (len (fn-ptx-q m)))))
                (fn-pth-i-post p s nil) (fn-pth-i-storage-avoids m (fn-ptx-cur-bp p)))
           (and (fn-pth-i (mv-nth 0 (fn-pth-deliver s 1 1 (fn-rtc-ev :handed out 1 1 (list fid finc hd)) q)))
                (not (mv-nth 2 (fn-pth-deliver s 1 1 (fn-rtc-ev :handed out 1 1 (list fid finc hd)) q))))))
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-runtime-and-post-state-by-definition
        (:instance fn-pth-i-post-storage-and-protocol-by-definition (m (fn-rtc-mstate 1 s)))
        (:instance fn-pth-i-post-storage-machine-facts (m (fn-rtc-mstate 1 s)))
        (:instance fn-ptx-okp-wfp (m (fn-rtc-mstate 1 s)))
        (:instance fn-pth-i-post-state-m0 (m (fn-rtc-mstate 1 s)))
        (:instance fn-pth-i-storage-avoids-m0 (m (fn-rtc-mstate 1 s))
         (h (fn-ptx-cur-bp (list (fn-ptx-atom (fn-rtc-get 4 (fn-rtc-ev :handed out 1 1 (list fid finc hd)))) (fn-ptx-atom (fn-rtc-get 5 (fn-rtc-ev :handed out 1 1 (list fid finc hd))))
                  (fn-rtc-h-buf (fn-rtc-get 6 (fn-rtc-ev :handed out 1 1 (list fid finc hd)))) (fn-rtc-h-len (fn-rtc-get 6 (fn-rtc-ev :handed out 1 1 (list fid finc hd))))))))
        (:instance fn-pth-i-answer-owner-deliver (ev (fn-rtc-ev :handed out 1 1 (list fid finc hd))) (o :refused)
         (p (list (fn-ptx-atom (fn-rtc-get 4 (fn-rtc-ev :handed out 1 1 (list fid finc hd)))) (fn-ptx-atom (fn-rtc-get 5 (fn-rtc-ev :handed out 1 1 (list fid finc hd))))
                  (fn-rtc-h-buf (fn-rtc-get 6 (fn-rtc-ev :handed out 1 1 (list fid finc hd)))) (fn-rtc-h-len (fn-rtc-get 6 (fn-rtc-ev :handed out 1 1 (list fid finc hd)))))))
        (:instance fn-pth-i-answer-owner-deliver (ev (fn-rtc-ev :handed out 1 1 (list fid finc hd))) (o :busy)
         (p (list (fn-ptx-atom (fn-rtc-get 4 (fn-rtc-ev :handed out 1 1 (list fid finc hd)))) (fn-ptx-atom (fn-rtc-get 5 (fn-rtc-ev :handed out 1 1 (list fid finc hd))))
                  (fn-rtc-h-buf (fn-rtc-get 6 (fn-rtc-ev :handed out 1 1 (list fid finc hd)))) (fn-rtc-h-len (fn-rtc-get 6 (fn-rtc-ev :handed out 1 1 (list fid finc hd))))))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-ev fn-rtc-ev-id fn-rtc-ev-inc fn-rtc-get-of-cons
     (:executable-counterpart fn-rtc-get) (:executable-counterpart nfix) (:executable-counterpart zp)
     fn-pth-m-step fn-pthm-step fn-ptx-step fn-ptx-step1 fn-ptx-answer-reads-view
     fn-ptx-accessors-of-mk
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-1-cons-by-definition member-equal car-cons cdr-cons
     (:executable-counterpart equal) (:executable-counterpart member-equal))))))

; From p15d-I-handed-reply-step.lisp
(defthm fn-pth-i-owner-handed-reply-step
 (implies (and (fn-pth-i s) (fn-rtc-hand-delivers-p s e) (equal (fn-rtc-hand-to s e) 1)
               (or (member-eq (fn-ptx-ph (fn-rtc-mstate 1 s)) '(:closed :fenced))
                   (and (not (equal (fn-ptx-ph (fn-rtc-mstate 1 s)) :idle))
                        (<= *fn-ptx-k* (len (fn-ptx-q (fn-rtc-mstate 1 s)))))))
          (and (fn-pth-i (mv-nth 0 (fn-pth-step s e q)))
               (not (mv-nth 2 (fn-pth-step* s e q)))))
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-runtime-and-post-state-by-definition
        fn-pth-i-hand-to-owner-facts fn-pth-i-incoming-hand-buffer
        fn-pth-i-hand-buffer-untracked fn-pth-i-end-use-hand
        (:instance fn-pth-i-handed-reply-host-delivery
         (s (fn-rtc-end-use s e)) (out (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e))
         (fid (fn-rtc-e-id e)) (finc (fn-rtc-e-inc e)) (hd (list (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) (+ 1 (fn-rtc-b-gen (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) s))) 0 (len (fn-rtc-b-bytes (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) s)))))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-step fn-pth-step* fn-pth-i-rearm fn-rtc-acts-on-p fn-rtc-hand-to
     fn-pth-i-mstate-of-end-use fn-rtc-config-of-end-use fn-rtc-ev fn-rtc-ev-id
     fn-pth-i-post fn-pth-i-visible-buffer fn-ptx-atom fn-ptx-cur-bp fn-ptx-cur-len
     fn-ptx-cur-fid fn-ptx-cur-finc fn-rtc-h-buf fn-rtc-h-len fn-rtc-buffer-accessors
     fn-rtc-get-of-cons len true-listp natp nfix fn-rtc-u64p-implies-natp
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition car-cons cdr-cons
     (:type-prescription fn-rtc-e-id) (:type-prescription fn-rtc-e-inc)
     (:type-prescription fn-rtc-b-gen) (:type-prescription fn-rtc-h-buf) (:type-prescription len)
     (:executable-counterpart equal) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+)
     (:executable-counterpart member-equal))))))

; From p15d-I-handed-step.lisp
(defthm fn-pth-i-owner-handed-step
 (implies (and (fn-pth-i s) (fn-rtc-hand-delivers-p s e) (equal (fn-rtc-hand-to s e) 1))
          (and (fn-pth-i (mv-nth 0 (fn-pth-step s e q)))
               (not (mv-nth 2 (fn-pth-step* s e q)))))
 :hints (("Goal"
  :use (fn-pth-i-owner-handed-idle-step fn-pth-i-owner-handed-queue-step fn-pth-i-owner-handed-reply-step)
  :in-theory (union-theories (theory 'minimal-theory)
   '(member-equal (:type-prescription len) (:executable-counterpart equal))))))

; Output storage/protocol restoration; concrete span admission still owed.

; From p15d-I-output-storage.lisp
(defthm fn-pth-i-queue-avoids-used
 (implies (and (fn-pth-i-queue ps s used) (member-equal h used))
          (fn-pth-i-queue-avoids ps h))
 :hints (("Goal" :induct (fn-pth-i-queue ps s used)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-queue fn-pth-i-queue-avoids member-equal car-cons cdr-cons)))))
(defthm fn-pth-i-output-lease-bytes-and-gen
 (let ((b (fn-rtc-buffer h s)))
  (implies (and (natp h) (natp j))
   (and (equal (fn-rtc-b-bytes (fn-rtc-buffer j (fn-rtc-with-buffer h
                 (list (fn-rtc-b-gen b) '(:leased 1 1 :out) (fn-rtc-b-bytes b)) s)))
               (fn-rtc-b-bytes (fn-rtc-buffer j s)))
        (equal (fn-rtc-b-gen (fn-rtc-buffer j (fn-rtc-with-buffer h
                 (list (fn-rtc-b-gen b) '(:leased 1 1 :out) (fn-rtc-b-bytes b)) s)))
               (fn-rtc-b-gen (fn-rtc-buffer j s))))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-buffer-of-with fn-rtc-buffer-accessors nfix natp (:type-prescription fn-rtc-b-gen))))))
(defthm fn-pth-i-visible-output-lease
 (implies (and (natp h) (fn-pth-i-visible-buffer j s t))
  (fn-pth-i-visible-buffer j (fn-rtc-with-buffer h
   (list (fn-rtc-b-gen (fn-rtc-buffer h s)) '(:leased 1 1 :out)
         (fn-rtc-b-bytes (fn-rtc-buffer h s))) s) t))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-visible-buffer fn-rtc-buffer-of-with fn-rtc-buffer-accessors fn-rtc-with-accessors
     nfix natp (:executable-counterpart equal))))))
(defthm fn-pth-i-post-output-lease
 (implies (and (natp h) (fn-pth-i-post p s t))
  (fn-pth-i-post p (fn-rtc-with-buffer h
   (list (fn-rtc-b-gen (fn-rtc-buffer h s)) '(:leased 1 1 :out)
         (fn-rtc-b-bytes (fn-rtc-buffer h s))) s) t))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-post fn-pth-i-visible-output-lease fn-rtc-with-accessors)))))
(defthm fn-pth-i-flight-storage-output-lease
 (implies (and (fn-pth-i-post-storage m s) (fn-ptx-in-flight-p (fn-ptx-ph m))
               (natp h) (fn-pth-i-queue-avoids (fn-ptx-q m) h))
  (fn-pth-i-post-storage m (fn-rtc-with-buffer h
   (list (fn-rtc-b-gen (fn-rtc-buffer h s)) '(:leased 1 1 :out)
         (fn-rtc-b-bytes (fn-rtc-buffer h s))) s)))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-post-storage fn-ptx-in-flight-p member-equal
     fn-pth-i-visible-buffer-leasedp-congruence fn-pth-i-post-leasedp-congruence
     fn-pth-i-visible-output-lease fn-pth-i-post-output-lease fn-pth-i-output-lease-bytes-and-gen
     fn-pth-i-queue-untracked-update fn-rtc-with-accessors
     (:type-prescription fn-ptx-cur-bp) (:type-prescription fn-ptx-buf-h) natp
     (:executable-counterpart equal) (:executable-counterpart member-equal))))))

; From p15d-I-output-request.lisp
(defthm fn-pth-i-owner-uses-issue-expected
 (implies (and (fn-pth-i-owner-uses uses m) (fn-ptx-expected m))
          (fn-pth-i-owner-uses (cons (list (fn-ptx-expected m) 1 1 op hd) uses) m))
 :hints (("Goal" :expand ((fn-pth-i-owner-uses (cons (list (fn-ptx-expected m) 1 1 op hd) uses) m))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-get-of-cons car-cons cdr-cons (:executable-counterpart nfix) (:executable-counterpart zp)
     (:executable-counterpart fn-rtc-get) (:executable-counterpart equal))))))
(defthm fn-pth-i-output-request-admitted
 (implies (and (fn-pth-i-runtime s) (fn-pth-req-data-okp r)
               (equal (fn-rtc-get 0 r) :submit) (equal (fn-rtc-get 1 r) :pwrite)
               (not (fn-rtc-kind-out-p :pwrite 1 1 (fn-rtc-uses s)))
               (fn-rtc-submit-okp :pwrite (fn-rtc-get 2 r) 1 1 s))
          (not (mv-nth 2 (fn-rtc-request r 1 1 s))))
 :hints (("Goal" :use ((:instance fn-pth-request-factors (id 1) (inc 1)))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-pth-req-state-okp fn-rtc-submit-okp fn-rtc-live-p
     (:executable-counterpart fn-rtc-buffered-kind-p) (:executable-counterpart member-equal)
     (:executable-counterpart equal) (:executable-counterpart fn-rtc-s-inc)
     (:executable-counterpart fn-rtc-s-status))))))
(defthm fn-pth-i-admitted-output-request-state
 (implies (and (equal (fn-rtc-get 0 r) :submit) (equal (fn-rtc-get 1 r) :pwrite)
               (not (mv-nth 2 (fn-rtc-request r 1 1 s))))
          (equal (mv-nth 0 (fn-rtc-request r 1 1 s))
                 (fn-rtc-buffered-submit-state :pwrite (fn-rtc-get 2 r) 1 1 s)))
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-request fn-rtc-req-submit fn-rtc-buffered-submit-state fn-rtc-next-op-of-with
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition car-cons cdr-cons
     (:executable-counterpart fn-rtc-buffered-kind-p) (:executable-counterpart member-equal)
     (:executable-counterpart equal))))))
(defthm fn-pth-i-flight-post-state-buffered-submit
 (implies (and (fn-pth-i-post-storage m s) (fn-ptx-in-flight-p (fn-ptx-ph m))
               (fn-pth-i-owner-uses (fn-rtc-uses s) m) (equal (fn-ptx-expected m) :pwrite)
               (fn-pth-i-queue-avoids (fn-ptx-q m) (fn-rtc-h-buf hd)))
          (fn-pth-i-post-state m (fn-rtc-buffered-submit-state :pwrite hd 1 1 s)))
 :hints (("Goal"
  :use ((:instance fn-pth-i-post-storage-and-protocol-by-definition
         (s (fn-rtc-buffered-submit-state :pwrite hd 1 1 s)))
        (:instance fn-pth-i-owner-uses-issue-expected (uses (fn-rtc-uses s)) (op (fn-rtc-next-op s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-buffered-submit-state fn-pth-i-flight-storage-output-lease fn-pth-i-post-storage-issue
     fn-rtc-issue-frame fn-rtc-with-accessors fn-rtc-next-op-of-with fn-rtc-kind-out-p
     fn-rtc-get-of-cons car-cons cdr-cons natp (:type-prescription fn-rtc-h-buf)
     (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
     (:executable-counterpart member-equal) (:executable-counterpart nfix) (:executable-counterpart zp))))))
(defthm fn-pth-i-owner-output-request
 (let ((m (fn-rtc-mstate 1 s)))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s)
                (fn-ptx-in-flight-p (fn-ptx-ph m))
                (fn-pth-i-owner-uses (fn-rtc-uses s) m) (equal (fn-ptx-expected m) :pwrite)
                (fn-pth-req-data-okp r) (equal (fn-rtc-get 0 r) :submit) (equal (fn-rtc-get 1 r) :pwrite)
                (not (fn-rtc-kind-out-p :pwrite 1 1 (fn-rtc-uses s)))
                (fn-rtc-submit-okp :pwrite (fn-rtc-get 2 r) 1 1 s)
                (fn-pth-i-queue-avoids (fn-ptx-q m) (fn-rtc-h-buf (fn-rtc-get 2 r))))
           (and (fn-pth-i (mv-nth 0 (fn-rtc-request r 1 1 s)))
                (not (mv-nth 2 (fn-rtc-request r 1 1 s))))))
 :hints (("Goal"
  :use (fn-pth-i-output-request-admitted fn-pth-i-admitted-output-request-state
        (:instance fn-pth-i-runtime-request (id 1) (inc 1))
        (:instance fn-pth-i-flight-post-state-buffered-submit (m (fn-rtc-mstate 1 s)) (hd (fn-rtc-get 2 r)))
        (:instance fn-pth-i-runtime-and-post-state-by-definition (s (mv-nth 0 (fn-rtc-request r 1 1 s)))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-request-keeps-mstates)))))

; Actual output spans, fsync-to-first-span and next payload span; full I.

; From p15d-I-spans.lisp
(verify-guards fn-pth-i-visible-buffer)
(defun fn-pth-i-output-span (sp ps s)
 (declare (xargs :guard t))
 (let ((h (nfix (fn-rtc-get 0 sp))) (off (nfix (fn-rtc-get 1 sp))) (n (nfix (fn-rtc-get 2 sp))))
  (and (fn-pth-i-visible-buffer h s t)
       (<= (+ off n) (len (fn-rtc-b-bytes (fn-rtc-buffer h s))))
       (fn-pth-i-queue-avoids ps h))))
(defun fn-pth-i-output-spans (spans ps s)
 (declare (xargs :guard t))
 (if (consp spans)
     (and (fn-pth-i-output-span (car spans) ps s) (fn-pth-i-output-spans (cdr spans) ps s)) t))
(verify-guards fn-pth-i-output-span)
(verify-guards fn-pth-i-output-spans)
(defthm fn-pth-i-output-spans-append
 (equal (fn-pth-i-output-spans (append a b) ps s)
        (and (fn-pth-i-output-spans a ps s) (fn-pth-i-output-spans b ps s)))
 :hints (("Goal" :induct (append a b)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-output-spans binary-append car-cons cdr-cons)))))
(defthm fn-pth-i-output-spans-single
 (implies (and (natp h) (natp off) (natp n) (fn-pth-i-visible-buffer h s t)
               (<= (+ off n) (len (fn-rtc-b-bytes (fn-rtc-buffer h s))))
               (fn-pth-i-queue-avoids ps h))
          (fn-pth-i-output-spans (fn-ptx-span h off n) ps s))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-output-spans fn-pth-i-output-span fn-ptx-span fn-rtc-get-of-cons
     nfix natp zp car-cons cdr-cons (:executable-counterpart fn-rtc-get)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart equal))))))
(defthm fn-pth-i-output-spans-of-flight-storage
 (implies (and (fn-pth-i-post-storage m s) (fn-ptx-in-flight-p (fn-ptx-ph m)))
          (fn-pth-i-output-spans (fn-ptx-spans m) (fn-ptx-q m) s))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-post-storage fn-ptx-in-flight-p fn-pth-i-post
     fn-pth-i-visible-buffer-leasedp-congruence
     fn-ptx-spans fn-ptx-spans-g fn-pth-i-output-spans-append fn-pth-i-output-spans-single
     fn-pth-i-queue-avoids-used member-equal binary-append min max natp nfix
     default-+-1 default-+-2 default-unary-minus associativity-of-+ commutativity-of-+ commutativity-2-of-+
     inverse-of-+ fold-consts-in-+ unicity-of-0 fix car-cons cdr-cons
     (:type-prescription fn-ptx-cur-bp) (:type-prescription fn-ptx-cur-len)
     (:type-prescription fn-ptx-cur-ioff) (:type-prescription fn-ptx-cur-base) (:type-prescription fn-ptx-cur-glen)
     (:type-prescription fn-ptx-buf-h) (:type-prescription fn-ptx-buf-len)
     (:type-prescription fn-ptx-buf-x) (:type-prescription fn-ptx-buf-cut)
     (:executable-counterpart equal) (:executable-counterpart member-equal) (:executable-counterpart nfix))))))

; From p15d-I-span-access.lisp
(defthm fn-pth-i-output-spans-get
 (implies (and (fn-pth-i-output-spans spans ps s) (natp i) (< i (len spans)))
          (fn-pth-i-output-span (fn-rtc-get i spans) ps s))
 :hints (("Goal" :induct (fn-rtc-index-induct i 0 spans)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-index-induct fn-pth-i-output-spans fn-rtc-get len nfix natp zp car-cons cdr-cons
     default-+-1 default-+-2 (:type-prescription len)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+))))))
(defthm fn-pth-i-spans-prefix-length-bound
 (implies (and (natp i) (<= i (len spans)))
          (<= (fn-ptx-spans-len (take i spans)) (fn-ptx-spans-len spans)))
 :hints (("Goal" :induct (fn-rtc-index-induct i 0 spans)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-index-induct fn-ptx-spans-len take len zp nfix natp car-cons cdr-cons
     default-+-1 default-+-2 (:type-prescription len) (:type-prescription nfix)
     (:type-prescription fn-ptx-spans-len)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+))))))
(defthm fn-pth-i-output-span-submit-okp
 (let* ((h (nfix (fn-rtc-get 0 sp))) (off (nfix (fn-rtc-get 1 sp))) (n (nfix (fn-rtc-get 2 sp))))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-output-span sp ps s))
           (fn-rtc-submit-okp :pwrite (list h (fn-ptx-gen h 1 1 s) off n) 1 1 s)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-pth-i-visible-owner-readers (h (nfix (fn-rtc-get 0 sp))))
        (:instance fn-rtc-c-shapep-buffer (h (nfix (fn-rtc-get 0 sp))))
        fn-pth-i-runtime-shape-by-definition)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-output-span fn-pth-i-visible-buffer fn-rtc-submit-okp
     fn-rtc-handlep fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len fn-rtc-b-bytes
     fn-rtc-get-of-cons len true-listp nfix natp car-cons cdr-cons
     (:type-prescription nfix) fn-pth-post-view-gen-is-natural
     (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
     (:executable-counterpart member-equal) (:executable-counterpart nfix) (:executable-counterpart zp)
     (:executable-counterpart binary-+))))))

; From p15d-I-pwrite-data.lisp
(defthm fn-pth-data-okp-pwrite
 (implies (< (nfix pos) (expt 2 64))
          (fn-pth-req-data-okp (fn-ptx-pwrite h g off n pos)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-req-data-okp fn-ptx-pwrite fn-rtc-kind-extrap fn-rtc-extrap fn-rtc-handlep
     fn-rtc-get-of-cons len true-listp natp car-cons cdr-cons (:type-prescription nfix)
     (:executable-counterpart fn-rtc-get) (:executable-counterpart equal) (:executable-counterpart expt)
     (:executable-counterpart member-equal) (:executable-counterpart fn-rtc-buffered-kind-p)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+)
     (:executable-counterpart <))))))
(defthm fn-pth-i-output-span-buffer-avoids
 (implies (fn-pth-i-output-span sp ps s)
          (fn-pth-i-queue-avoids ps (nfix (fn-rtc-get 0 sp))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pth-i-output-span)))))

; From p15d-I-span-write.lisp
(defthm fn-pth-i-flight-frontier-bound
 (implies (and (fn-pth-i-post-storage m s) (fn-ptx-in-flight-p (fn-ptx-ph m)))
          (< (+ (fn-ptx-kd-frontier (fn-ptx-kd m)) (fn-ptx-spans-len (fn-ptx-spans m))) (expt 2 64)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-post-storage fn-ptx-elen fn-ptx-nmsg nfix natp
     (:type-prescription nfix) (:type-prescription fn-ptx-spans-len))))))
(defthm fn-pth-i-span-write-offset-is-u64
 (implies (and (fn-pth-i-post-storage m s) (fn-ptx-in-flight-p (fn-ptx-ph m))
               (natp i) (<= i (len (fn-ptx-spans m))))
          (< (nfix (+ (nfix (fn-ptx-kd-frontier (fn-ptx-kd m)))
                      (fn-ptx-spans-len (take i (fn-ptx-spans m))))) (expt 2 64)))
 :hints (("Goal" :use (fn-pth-i-flight-frontier-bound
        (:instance fn-pth-i-spans-prefix-length-bound (spans (fn-ptx-spans m))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(nfix natp (:type-prescription fn-ptx-kd-frontier) (:type-prescription fn-ptx-spans-len))))))
(defthm fn-pth-i-span-pwrite-properties
 (let ((r (fn-ptx-span-pwrite i m (fn-ptx-kd-frontier (fn-ptx-kd m)) 1 1 s)))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s) (fn-ptx-in-flight-p (fn-ptx-ph m))
                (natp i) (< i (len (fn-ptx-spans m))))
   (and (fn-pth-req-data-okp r) (equal (fn-rtc-get 0 r) :submit) (equal (fn-rtc-get 1 r) :pwrite)
        (fn-rtc-submit-okp :pwrite (fn-rtc-get 2 r) 1 1 s)
        (fn-pth-i-queue-avoids (fn-ptx-q m) (fn-rtc-h-buf (fn-rtc-get 2 r))))))
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-output-spans-of-flight-storage
        fn-pth-i-span-write-offset-is-u64
        (:instance fn-pth-i-output-spans-get (spans (fn-ptx-spans m)) (ps (fn-ptx-q m)))
        (:instance fn-pth-i-output-span-submit-okp (sp (fn-rtc-get i (fn-ptx-spans m))) (ps (fn-ptx-q m)))
        (:instance fn-pth-i-output-span-buffer-avoids (sp (fn-rtc-get i (fn-ptx-spans m))) (ps (fn-ptx-q m)))
        (:instance fn-pth-data-okp-pwrite (h (nfix (fn-rtc-get 0 (fn-rtc-get i (fn-ptx-spans m))))) (g (fn-ptx-gen (nfix (fn-rtc-get 0 (fn-rtc-get i (fn-ptx-spans m)))) 1 1 s)) (off (fn-rtc-get 1 (fn-rtc-get i (fn-ptx-spans m)))) (n (fn-rtc-get 2 (fn-rtc-get i (fn-ptx-spans m)))) (pos (+ (nfix (fn-ptx-kd-frontier (fn-ptx-kd m))) (fn-ptx-spans-len (take (nfix i) (fn-ptx-spans m)))))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-ptx-span-pwrite fn-ptx-pwrite fn-rtc-h-buf fn-rtc-get-of-cons
     fn-ptx-nfix-natp-rw fn-ptx-nfix-nfix fn-pth-post-view-gen-is-natural natp
     (:type-prescription nfix) (:type-prescription fn-ptx-kd-frontier) (:type-prescription fn-ptx-spans-len)
     car-cons cdr-cons (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+))))))

; From p15d-I-span-deliver.lisp
(defthm fn-pth-i-single-owner-output-after-machine
 (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s) (fn-ptx-in-flight-p (fn-ptx-ph m))
               (fn-pth-i-owner-uses (fn-rtc-uses s) m) (equal (fn-ptx-expected m) :pwrite)
               (fn-pth-req-data-okp r) (equal (fn-rtc-get 0 r) :submit) (equal (fn-rtc-get 1 r) :pwrite)
               (not (fn-rtc-kind-out-p :pwrite 1 1 (fn-rtc-uses s)))
               (fn-rtc-submit-okp :pwrite (fn-rtc-get 2 r) 1 1 s)
               (fn-pth-i-queue-avoids (fn-ptx-q m) (fn-rtc-h-buf (fn-rtc-get 2 r))))
  (and (fn-pth-i (mv-nth 0 (fn-rtc-requests (list r) 1 1 (fn-rtc-with-mstate 1 m s))))
       (not (mv-nth 2 (fn-rtc-requests (list r) 1 1 (fn-rtc-with-mstate 1 m s))))))
 :hints (("Goal" :use ((:instance fn-pth-i-owner-output-request (s (fn-rtc-with-mstate 1 m s))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-runtime-with-mstate fn-pth-i-owner-machine-index fn-rtc-mstate-of-with fn-rtc-with-accessors
     fn-pth-i-post-storage-with-mstate fn-rtc-submit-okp fn-rtc-buffer-of-with fn-rtc-slot-of-with
     fn-rtc-requests fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition binary-append car-cons cdr-cons
     (:executable-counterpart nfix) (:executable-counterpart natp))))))
(defthm fn-pth-i-single-owner-output-deliver
 (let* ((step (fn-pth-m-step (fn-rtc-mstate 1 s) ev (fn-rtc-view-state 1 1 s) (nfix q))) (m (mv-nth 0 step)))
  (implies (and (equal (mv-nth 1 step) (list r)) (fn-pth-i-runtime s) (fn-pth-i-post-storage m s) (fn-ptx-in-flight-p (fn-ptx-ph m))
               (fn-pth-i-owner-uses (fn-rtc-uses s) m) (equal (fn-ptx-expected m) :pwrite)
               (fn-pth-req-data-okp r) (equal (fn-rtc-get 0 r) :submit) (equal (fn-rtc-get 1 r) :pwrite)
               (not (fn-rtc-kind-out-p :pwrite 1 1 (fn-rtc-uses s)))
               (fn-rtc-submit-okp :pwrite (fn-rtc-get 2 r) 1 1 s)
               (fn-pth-i-queue-avoids (fn-ptx-q m) (fn-rtc-h-buf (fn-rtc-get 2 r))))
   (and (fn-pth-i (mv-nth 0 (fn-pth-deliver s 1 1 ev q)))
        (not (mv-nth 2 (fn-pth-deliver s 1 1 ev q))))))
 :hints (("Goal" :use ((:instance fn-pth-i-single-owner-output-after-machine
  (m (mv-nth 0 (fn-pth-m-step (fn-rtc-mstate 1 s) ev (fn-rtc-view-state 1 1 s) (nfix q))))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-deliver fn-rtc-view-state fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition car-cons cdr-cons)))))
(defthm fn-pth-i-single-owner-span-deliver
 (let* ((step (fn-pth-m-step (fn-rtc-mstate 1 s) ev (fn-rtc-view-state 1 1 s) (nfix q))) (m (mv-nth 0 step)))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s) (fn-ptx-in-flight-p (fn-ptx-ph m))
                (fn-pth-i-owner-uses (fn-rtc-uses s) m) (equal (fn-ptx-expected m) :pwrite)
                (natp i) (< i (len (fn-ptx-spans m)))
                (equal (mv-nth 1 step) (list (fn-ptx-span-pwrite i m (fn-ptx-kd-frontier (fn-ptx-kd m)) 1 1 s)))
                (not (fn-rtc-kind-out-p :pwrite 1 1 (fn-rtc-uses s))))
   (and (fn-pth-i (mv-nth 0 (fn-pth-deliver s 1 1 ev q)))
        (not (mv-nth 2 (fn-pth-deliver s 1 1 ev q))))))
 :hints (("Goal"
  :use ((:instance fn-pth-i-span-pwrite-properties
    (m (mv-nth 0 (fn-pth-m-step (fn-rtc-mstate 1 s) ev (fn-rtc-view-state 1 1 s) (nfix q)))) )
        (:instance fn-pth-i-single-owner-output-deliver
    (r (fn-ptx-span-pwrite i (mv-nth 0 (fn-pth-m-step (fn-rtc-mstate 1 s) ev (fn-rtc-view-state 1 1 s) (nfix q)))
       (fn-ptx-kd-frontier (fn-ptx-kd (mv-nth 0 (fn-pth-m-step (fn-rtc-mstate 1 s) ev (fn-rtc-view-state 1 1 s) (nfix q))))) 1 1 s))))
  :in-theory (theory 'minimal-theory))))
(defthm fn-pth-i-writing-index-in-span-list
 (implies (and (fn-ptx-okp m) (member-eq (fn-ptx-ph m) '(:payload-writing :log-writing)))
          (< (fn-ptx-k m) (len (fn-ptx-spans m))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(fn-ptx-okp fn-ptx-nspans member-equal (:type-prescription fn-ptx-k)
     (:executable-counterpart equal))))))

; From p15d-I-extsync-storage.lisp
(defthm fn-pth-i-post-storage-extsync-done
 (implies (and (fn-pth-i-post-storage m s) (equal (fn-ptx-ph m) :extsyncing)
               (equal (fn-rtc-get 0 ev) :fsync) (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done))
          (fn-pth-i-post-storage (mv-nth 0 (fn-ptx-step m ev st q)) s))
 :hints (("Goal"
  :use (fn-pth-i-post-storage-machine-facts fn-ptx-step-keeps-ok
        (:instance fn-pth-i-flight-storage-control-change
          (ph :payload-writing) (k 0) (evd (fn-ptx-evd+ m ev))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-ptx-step fn-ptx-step1 fn-ptx-okp-wfp fn-ptx-accessors-of-mk fn-ptx-in-flight-p
     fn-hld-mv-nth-0-cons nfix natp car-cons cdr-cons (:type-prescription fn-ptx-k)
     (:type-prescription fn-ptx-ext) (:type-prescription fn-ptx-nxt)
     (:executable-counterpart equal) (:executable-counterpart member-equal)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))


; From p15d-I-extsync-delivery.lisp
(defthm fn-pth-i-extsync-done-host-delivery
 (implies (and (fn-pth-i s) (equal (fn-ptx-ph (fn-rtc-mstate 1 s)) :extsyncing)
               (fn-rtc-completionp e) (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) (equal (fn-rtc-e-kind e) :fsync)
               (equal (fn-rtc-e-id e) 1) (equal (fn-rtc-e-inc e) 1)
               (equal (fn-rtc-get 0 (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e)) :done))
          (and (fn-pth-i (mv-nth 0 (fn-pth-deliver (fn-rtc-end-use s e) 1 1 (fn-rtc-ev :fsync (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e) 1 1 nil) q)))
               (not (mv-nth 2 (fn-pth-deliver (fn-rtc-end-use s e) 1 1 (fn-rtc-ev :fsync (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e) 1 1 nil) q)))))
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-before-machine-after-end-use
        (:instance fn-pth-i-post-storage-machine-facts (m (fn-rtc-mstate 1 s)) (s (fn-rtc-end-use s e)))
        (:instance fn-pth-i-owner-protocol-after-expected-completion (m2 nil))
        (:instance fn-pth-i-post-storage-extsync-done (m (fn-rtc-mstate 1 s)) (s (fn-rtc-end-use s e)) (ev (fn-rtc-ev :fsync (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e) 1 1 nil)) (st (fn-rtc-view-state 1 1 (fn-rtc-end-use s e))) (q (nfix q)))
        (:instance fn-pth-i-owner-machine-keeps-ok (m (fn-rtc-mstate 1 s)) (ev (fn-rtc-ev :fsync (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e) 1 1 nil)) (st (fn-rtc-view-state 1 1 (fn-rtc-end-use s e))) (q (nfix q)))
        (:instance fn-pth-i-writing-index-in-span-list (m (mv-nth 0 (fn-pth-m-step (fn-rtc-mstate 1 s) (fn-rtc-ev :fsync (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e) 1 1 nil) (fn-rtc-view-state 1 1 (fn-rtc-end-use s e)) (nfix q)))))
        (:instance fn-pth-i-single-owner-span-deliver (s (fn-rtc-end-use s e)) (ev (fn-rtc-ev :fsync (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e) 1 1 nil)) (i 0)))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-mstate-of-end-use fn-pth-m-step fn-pthm-step fn-ptx-step fn-ptx-step1
     fn-ptx-expected fn-ptx-okp-wfp fn-ptx-accessors-of-mk fn-ptx-in-flight-p
     fn-ptx-span-pwrite-reads-view fn-pth-i-hands-only-compatible-with-every-machine
     fn-pth-i-hands-only-has-no-operation fn-rtc-ev fn-rtc-ev-id fn-rtc-ev-inc fn-rtc-get-of-cons
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-1-cons-by-definition car-cons cdr-cons
     nfix natp (:type-prescription fn-ptx-k) (:type-prescription fn-ptx-ext) (:type-prescription fn-ptx-nxt)
     (:executable-counterpart equal) (:executable-counterpart member-equal) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+))))))

; From p15d-I-extsync-step.lisp
(defthm fn-pth-i-owner-extsync-done-step
 (implies (and (fn-pth-i s) (equal (fn-ptx-ph (fn-rtc-mstate 1 s)) :extsyncing)
               (fn-rtc-acts-on-p s e) (equal (fn-rtc-e-id e) 1) (equal (fn-rtc-e-kind e) :fsync)
               (equal (fn-rtc-get 0 (fn-rtc-delivered-outcome
                                     (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e)) :done))
          (and (fn-pth-i (mv-nth 0 (fn-pth-step s e q)))
               (not (mv-nth 2 (fn-pth-step* s e q)))))
 :hints (("Goal" :use (fn-pth-i-runtime-and-post-state-by-definition fn-pth-i-direct-owner-completion fn-pth-i-extsync-done-host-delivery)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-step fn-pth-step* fn-pth-i-rearm
     fn-rtc-acts-on-p fn-rtc-hand-delivers-p fn-rtc-ev fn-rtc-ev-id fn-rtc-get-of-cons
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition car-cons cdr-cons
     (:executable-counterpart equal) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))

; From p15d-I-payload-storage.lisp
(defthm fn-pth-i-post-storage-payload-done
 (implies (and (fn-pth-i-post-storage m s) (equal (fn-ptx-ph m) :payload-writing)
               (equal (fn-rtc-get 0 ev) :pwrite) (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done)
               (equal (fn-rtc-get 1 (fn-rtc-get 1 ev)) (fn-ptx-span-n (fn-ptx-k m) m)))
          (fn-pth-i-post-storage (mv-nth 0 (fn-ptx-step m ev st q)) s))
 :hints (("Goal"
  :use (fn-pth-i-post-storage-machine-facts fn-ptx-step-keeps-ok
        (:instance fn-pth-i-flight-storage-control-change
          (ph (if (< (+ (fn-ptx-k m) 2) (fn-ptx-nspans m)) :payload-writing :log-writing)) (k (+ 1 (fn-ptx-k m))) (evd (fn-ptx-evd+ m ev))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-ptx-step fn-ptx-step1 fn-ptx-okp-wfp fn-ptx-accessors-of-mk fn-ptx-in-flight-p
     fn-hld-mv-nth-0-cons commutativity-of-+ nfix natp car-cons cdr-cons (:type-prescription fn-ptx-k)
     (:type-prescription fn-ptx-ext) (:type-prescription fn-ptx-nxt)
     (:executable-counterpart equal) (:executable-counterpart member-equal)
     (:executable-counterpart nfix) (:executable-counterpart zp)
     (:executable-counterpart binary-+))))))


; From p15d-I-payload-delivery.lisp
(defthm fn-pth-i-payload-done-host-delivery
 (implies (and (fn-pth-i s) (equal (fn-ptx-ph (fn-rtc-mstate 1 s)) :payload-writing)
               (fn-rtc-completionp e) (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) (equal (fn-rtc-e-kind e) :pwrite)
               (equal (fn-rtc-e-id e) 1) (equal (fn-rtc-e-inc e) 1)
               (equal (fn-rtc-get 0 (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e)) :done)
               (equal (fn-rtc-get 1 (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e))
                      (fn-ptx-span-n (fn-ptx-k (fn-rtc-mstate 1 s)) (fn-rtc-mstate 1 s))))
          (and (fn-pth-i (mv-nth 0 (fn-pth-deliver (fn-rtc-end-use s e) 1 1 (fn-rtc-ev :pwrite (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e) 1 1 nil) q)))
               (not (mv-nth 2 (fn-pth-deliver (fn-rtc-end-use s e) 1 1 (fn-rtc-ev :pwrite (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e) 1 1 nil) q)))))
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-before-machine-after-end-use
        (:instance fn-pth-i-post-storage-machine-facts (m (fn-rtc-mstate 1 s)) (s (fn-rtc-end-use s e)))
        (:instance fn-pth-i-owner-protocol-after-expected-completion (m2 nil))
        (:instance fn-pth-i-post-storage-payload-done (m (fn-rtc-mstate 1 s)) (s (fn-rtc-end-use s e)) (ev (fn-rtc-ev :pwrite (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e) 1 1 nil)) (st (fn-rtc-view-state 1 1 (fn-rtc-end-use s e))) (q (nfix q)))
        (:instance fn-pth-i-owner-machine-keeps-ok (m (fn-rtc-mstate 1 s)) (ev (fn-rtc-ev :pwrite (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e) 1 1 nil)) (st (fn-rtc-view-state 1 1 (fn-rtc-end-use s e))) (q (nfix q)))
        (:instance fn-pth-i-writing-index-in-span-list (m (mv-nth 0 (fn-pth-m-step (fn-rtc-mstate 1 s) (fn-rtc-ev :pwrite (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e) 1 1 nil) (fn-rtc-view-state 1 1 (fn-rtc-end-use s e)) (nfix q)))))
        (:instance fn-pth-i-single-owner-span-deliver (s (fn-rtc-end-use s e)) (ev (fn-rtc-ev :pwrite (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e) 1 1 nil)) (i (+ 1 (fn-ptx-k (fn-rtc-mstate 1 s))))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-mstate-of-end-use fn-pth-m-step fn-pthm-step fn-ptx-step fn-ptx-step1
     fn-ptx-expected fn-ptx-okp-wfp fn-ptx-accessors-of-mk fn-ptx-in-flight-p
     fn-ptx-span-pwrite-reads-view fn-pth-i-hands-only-compatible-with-every-machine
     fn-pth-i-hands-only-has-no-operation fn-rtc-ev fn-rtc-ev-id fn-rtc-ev-inc fn-rtc-get-of-cons
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-1-cons-by-definition car-cons cdr-cons
     commutativity-of-+ nfix natp (:type-prescription fn-ptx-k) (:type-prescription fn-ptx-ext) (:type-prescription fn-ptx-nxt)
     (:executable-counterpart equal) (:executable-counterpart member-equal) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+))))))

; From p15d-I-payload-step.lisp
(defthm fn-pth-i-owner-payload-done-step
 (implies (and (fn-pth-i s) (equal (fn-ptx-ph (fn-rtc-mstate 1 s)) :payload-writing)
               (fn-rtc-acts-on-p s e) (equal (fn-rtc-e-id e) 1) (equal (fn-rtc-e-kind e) :pwrite)
               (equal (fn-rtc-get 0 (fn-rtc-delivered-outcome
                                     (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e)) :done)
               (equal (fn-rtc-get 1 (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e))
                      (fn-ptx-span-n (fn-ptx-k (fn-rtc-mstate 1 s)) (fn-rtc-mstate 1 s))))
          (and (fn-pth-i (mv-nth 0 (fn-pth-step s e q)))
               (not (mv-nth 2 (fn-pth-step* s e q)))))
 :hints (("Goal" :use (fn-pth-i-runtime-and-post-state-by-definition fn-pth-i-direct-owner-completion fn-pth-i-payload-done-host-delivery)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-step fn-pth-step* fn-pth-i-rearm
     fn-rtc-acts-on-p fn-rtc-hand-delivers-p fn-rtc-ev fn-rtc-ev-id fn-rtc-get-of-cons
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition car-cons cdr-cons
     (:executable-counterpart equal) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))


; End-transition replies preserve components before the next operation is issued.

(defthm fn-pth-i-answer-write-admitted
 (let* ((g (fn-rtc-b-gen (fn-rtc-buffer h s)))
        (r (list :write h g 0 (list code))))
  (implies (and (fn-pth-i-runtime s) (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
                (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:workspace 1 1))
                (fn-cbor-octetp code))
   (and (not (mv-nth 2 (fn-rtc-request r 1 1 s)))
        (equal (mv-nth 0 (fn-rtc-request r 1 1 s))
               (fn-rtc-with-buffer h (list g '(:workspace 1 1)
                (fn-rtc-splice (fn-rtc-b-bytes (fn-rtc-buffer h s)) 0 (list code))) s)))))
 :hints (("Goal" :use (fn-pth-i-buffer-cap-positive)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-request fn-rtc-req-write fn-cbor-octet-listp fn-rtc-get-of-cons
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition
     member-equal len true-listp car-cons cdr-cons natp
     (:type-prescription len) (:type-prescription fn-rtc-buf-cap)
     (:executable-counterpart equal) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+)
     (:executable-counterpart fn-cbor-octet-listp) (:executable-counterpart <))))))

(defthm fn-pth-i-answer-hand-admitted
 (let* ((b (fn-rtc-buffer h s))
        (r (list :submit :hand (list h (fn-rtc-b-gen b) 0 (len (fn-rtc-b-bytes b))) (list fid finc))))
  (implies (and (fn-pth-i-runtime s) (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
                (equal (fn-rtc-b-owner b) '(:workspace 1 1))
                (fn-rtc-u64p fid) (< 1 fid) (< fid (fn-rtc-nslots (fn-rtc-config s)))
                (fn-rtc-u64p finc))
           (not (mv-nth 2 (fn-rtc-request r 1 1 s)))))
 :hints (("Goal"
  :use ((:instance fn-pth-request-factors (id 1) (inc 1)
         (r (list :submit :hand (list h (fn-rtc-b-gen (fn-rtc-buffer h s)) 0
              (len (fn-rtc-b-bytes (fn-rtc-buffer h s)))) (list fid finc)))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-pth-req-data-okp fn-pth-req-state-okp fn-rtc-live-p
     fn-rtc-kind-extrap fn-rtc-extrap fn-rtc-handlep fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len
     fn-rtc-get-of-cons len true-listp fn-rtc-u64p-implies-natp fn-rtc-u64p natp nfix posp car-cons cdr-cons
     (:type-prescription fn-rtc-b-gen) (:type-prescription len)
     (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+)
     (:executable-counterpart fn-rtc-buffered-kind-p) (:executable-counterpart member-equal)
     (:executable-counterpart fn-rtc-s-inc) (:executable-counterpart fn-rtc-s-status))))))

(defthm fn-pth-i-answer-physical-admitted
 (implies (and (fn-pth-i-runtime s) (fn-pth-i-post p s nil))
          (not (mv-nth 2 (fn-rtc-requests (list (list :write (fn-ptx-cur-bp p) (fn-rtc-b-gen (fn-rtc-buffer (fn-ptx-cur-bp p) s)) 0 (list (fn-ptx-code o)))
           (list :submit :hand (list (fn-ptx-cur-bp p) (fn-rtc-b-gen (fn-rtc-buffer (fn-ptx-cur-bp p) s)) 0
             (max 1 (len (fn-rtc-b-bytes (fn-rtc-buffer (fn-ptx-cur-bp p) s)))))
             (list (fn-ptx-cur-fid p) (fn-ptx-cur-finc p)))) 1 1 s))))
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-runtime-shape-by-definition fn-pth-i-runtime-request
        fn-pth-answer-code-is-octet
        (:instance fn-pth-i-post-target-is-u64 (lp nil))
        (:instance fn-rtc-c-shapep-buffer (h (fn-ptx-cur-bp p)))
        (:instance fn-pth-i-answer-write-admitted (h (fn-ptx-cur-bp p)) (code (fn-ptx-code o)))
        (:instance fn-pth-i-answer-hand-admitted
          (s (mv-nth 0 (fn-rtc-request
           (list :write (fn-ptx-cur-bp p) (fn-rtc-b-gen (fn-rtc-buffer (fn-ptx-cur-bp p) s)) 0 (list (fn-ptx-code o)))
           1 1 s)))
          (h (fn-ptx-cur-bp p)) (fid (fn-ptx-cur-fid p)) (finc (fn-ptx-cur-finc p))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-runtime-request fn-pth-i-answer-write-admitted fn-pth-i-post fn-pth-i-visible-buffer fn-rtc-shapep
     fn-rtc-requests binary-append fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition
     fn-rtc-with-accessors fn-rtc-buffer-of-with fn-rtc-mstate-of-with fn-rtc-buffer-accessors
     fn-pth-i-code-splice-length fn-rtc-splice-length fn-cbor-octet-listp-implies-true-listp
     fn-rtc-b-bytes fn-rtc-get-of-cons max len true-listp nfix natp car-cons cdr-cons
     (:type-prescription len) (:type-prescription fn-ptx-cur-bp) (:type-prescription fn-rtc-b-gen)
     (:executable-counterpart equal) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+)
     (:executable-counterpart len) (:executable-counterpart true-listp))))))

(defthm fn-pth-i-answer-admitted
 (implies (and (fn-pth-i-runtime s) (fn-pth-i-post p s nil))
          (not (mv-nth 2 (fn-rtc-requests (fn-ptx-answer p o 1 1 s) 1 1 s))))
 :hints (("Goal" :use (fn-pth-i-answer-physical-admitted)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-answer-physical-by-definition)))))

(defthm fn-pth-i-local-request-components
 (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s)
               (fn-pth-i-owner-uses (fn-rtc-uses s) m)
               (or (and (member-eq (fn-rtc-get 0 r) '(:acquire :write :release))
                        (fn-pth-i-storage-avoids m (fn-rtc-get 1 r)))
                   (and (equal (fn-rtc-get 0 r) :submit) (equal (fn-rtc-get 1 r) :hand)
                        (fn-pth-i-storage-avoids m (fn-rtc-h-buf (fn-rtc-get 2 r))))))
  (let ((s2 (mv-nth 0 (fn-rtc-request r 1 1 s))))
   (and (fn-pth-i-runtime s2) (fn-pth-i-post-storage m s2)
        (fn-pth-i-owner-uses (fn-rtc-uses s2) m))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-runtime-request fn-pth-i-post-storage-untracked-request
    fn-pth-i-owner-local-request-protocol)))))

(defthm fn-pth-i-answer-components
 (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s)
               (fn-pth-i-owner-uses (fn-rtc-uses s) m)
               (fn-pth-i-post p s nil) (fn-pth-i-storage-avoids m (fn-ptx-cur-bp p)))
  (let ((s2 (mv-nth 0 (fn-rtc-requests (fn-ptx-answer p o 1 1 s) 1 1 s))))
   (and (fn-pth-i-runtime s2) (fn-pth-i-post-storage m s2)
        (fn-pth-i-owner-uses (fn-rtc-uses s2) m)
        (not (mv-nth 2 (fn-rtc-requests (fn-ptx-answer p o 1 1 s) 1 1 s))))))
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-answer-admitted)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-runtime-request fn-pth-i-post-storage-untracked-request
     fn-pth-i-owner-local-request-protocol fn-pth-i-answer-physical-by-definition fn-rtc-requests
     fn-pth-i-local-request-components
     fn-rtc-request-keeps-mstates fn-rtc-get-of-cons fn-rtc-h-buf
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition binary-append
     car-cons cdr-cons (:type-prescription fn-ptx-cur-bp) natp nfix
     (:executable-counterpart fn-rtc-get) (:executable-counterpart nfix)
     (:executable-counterpart binary-+) (:executable-counterpart zp)
     (:executable-counterpart member-equal) (:executable-counterpart equal))))))

(defthm fn-pth-i-use-of-owner-output
 (implies (and (or (fn-rtc-use-okp u s) (fn-pth-i-listener-use u s))
               (fn-rtc-handlep (fn-rtc-u-hd u))
               (equal (fn-rtc-b-owner (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s)) '(:leased 1 1 :out)))
          (and (equal (fn-rtc-get 1 u) 1) (not (equal (fn-rtc-get 0 u) :hand))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-rtc-use-okp fn-rtc-usep fn-pth-i-listener-use fn-rtc-get-of-cons
    car-cons cdr-cons nfix natp
    (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
    (:executable-counterpart member-equal) (:executable-counterpart fn-rtc-handlep)
    (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+))))))

(defthm fn-pth-i-hands-only-no-owner-output-hold
 (implies (and (fn-pth-i-uses uses s) (fn-pth-i-owner-uses uses nil)
               (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:leased 1 1 :out)))
          (not (fn-rtc-holds-p h g uses)))
 :hints (("Goal" :induct (fn-pth-i-uses uses s)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-uses fn-pth-i-owner-uses fn-rtc-holds-p
     fn-pth-i-use-of-owner-output car-cons cdr-cons
     (:executable-counterpart fn-ptx-ph) (:executable-counterpart fn-ptx-expected)
     (:executable-counterpart equal))))
  ("Subgoal *1/1" :use ((:instance fn-pth-i-use-of-owner-output (u (car uses)))))))

(defthm fn-pth-i-hands-only-visible-workspace
 (implies (and (fn-pth-i-runtime s) (fn-pth-i-owner-uses (fn-rtc-uses s) nil)
               (fn-pth-i-visible-buffer h s t))
          (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:workspace 1 1)))
 :hints (("Goal" :use (fn-pth-i-runtime-buffer-metadata
                       (:instance fn-pth-i-hands-only-no-owner-output-hold
                        (uses (fn-rtc-uses s)) (g (fn-rtc-b-gen (fn-rtc-buffer h s)))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-pth-i-visible-buffer fn-pth-i-buffer-state-okp
     fn-rtc-get-of-cons car-cons cdr-cons
     (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
     (:executable-counterpart member-equal) (:executable-counterpart nfix)
     (:executable-counterpart zp) (:executable-counterpart binary-+))))))

(defthm fn-pth-i-local-request-other-buffer
 (implies (and (natp j)
               (or (and (member-eq (fn-rtc-get 0 r) '(:acquire :write :release))
                        (not (equal j (nfix (fn-rtc-get 1 r)))))
                   (and (equal (fn-rtc-get 0 r) :submit) (equal (fn-rtc-get 1 r) :hand)
                        (not (equal j (fn-rtc-h-buf (fn-rtc-get 2 r)))))))
          (equal (fn-rtc-buffer j (mv-nth 0 (fn-rtc-request r 1 1 s))) (fn-rtc-buffer j s)))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release fn-rtc-req-submit
     fn-rtc-buffer-of-with fn-rtc-issue-frame fn-hld-mv-nth-0-cons
     car-cons cdr-cons natp nfix (:type-prescription fn-rtc-h-buf)
     (:executable-counterpart fn-rtc-buffered-kind-p) (:executable-counterpart member-equal)
     (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))

(defthm fn-pth-i-queue-local-request
 (implies (and (fn-pth-i-queue ps s used)
               (or (and (member-eq (fn-rtc-get 0 r) '(:acquire :write :release))
                        (fn-pth-i-queue-avoids ps (nfix (fn-rtc-get 1 r))))
                   (and (equal (fn-rtc-get 0 r) :submit) (equal (fn-rtc-get 1 r) :hand)
                        (fn-pth-i-queue-avoids ps (fn-rtc-h-buf (fn-rtc-get 2 r))))))
          (fn-pth-i-queue ps (mv-nth 0 (fn-rtc-request r 1 1 s)) used))
 :hints (("Goal" :induct (fn-pth-i-queue ps s used)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-queue fn-pth-i-post fn-pth-i-visible-buffer fn-pth-i-queue-avoids
     fn-pth-i-local-request-other-buffer fn-rtc-request-config-frame car-cons cdr-cons)))))

(defthm fn-pth-i-answer-other-buffer
 (implies (and (fn-pth-i-runtime s) (fn-pth-i-post p s nil)
               (natp j) (not (equal j (fn-ptx-cur-bp p))))
          (equal (fn-rtc-buffer j (mv-nth 0 (fn-rtc-requests (fn-ptx-answer p o 1 1 s) 1 1 s)))
                 (fn-rtc-buffer j s)))
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '(fn-pth-i-answer-physical-by-definition fn-pth-i-local-request-other-buffer fn-rtc-requests
    fn-pth-i-post fn-pth-i-visible-buffer fn-rtc-get-of-cons fn-rtc-h-buf
    fn-hld-mv-nth-0-cons car-cons cdr-cons nfix natp
    (:executable-counterpart fn-rtc-get) (:executable-counterpart nfix)
    (:executable-counterpart zp) (:executable-counterpart binary-+)
    (:executable-counterpart member-equal) (:executable-counterpart equal))))))

(defthm fn-pth-i-answer-queue
 (implies (and (fn-pth-i-runtime s) (fn-pth-i-post p s nil)
               (fn-pth-i-queue ps s used) (fn-pth-i-queue-avoids ps (fn-ptx-cur-bp p)))
          (fn-pth-i-queue ps (mv-nth 0 (fn-rtc-requests (fn-ptx-answer p o 1 1 s) 1 1 s)) used))
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '(fn-pth-i-answer-physical-by-definition fn-pth-i-queue-local-request fn-rtc-requests
    fn-rtc-get-of-cons fn-rtc-h-buf fn-hld-mv-nth-0-cons car-cons cdr-cons nfix natp
    (:type-prescription fn-ptx-cur-bp) (:executable-counterpart fn-rtc-get)
    (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+)
    (:executable-counterpart member-equal) (:executable-counterpart equal))))))

(defun fn-pth-i-post-buffers-equal (ps s1 s2)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp ps)
  (and (equal (fn-rtc-buffer (fn-ptx-cur-bp (car ps)) s1)
              (fn-rtc-buffer (fn-ptx-cur-bp (car ps)) s2))
       (fn-pth-i-post-buffers-equal (cdr ps) s1 s2)) t))

(verify-guards fn-pth-i-post-buffers-equal)

(defun fn-pth-i-posts-untracked (ps m)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp ps)
  (and (fn-pth-i-storage-avoids m (fn-ptx-cur-bp (car ps)))
       (fn-pth-i-posts-untracked (cdr ps) m)) t))

(verify-guards fn-pth-i-posts-untracked)

(defthm fn-pth-i-answer-buffer-congruence
 (implies (and (fn-pth-i-runtime s1) (fn-pth-i-runtime s2)
               (fn-pth-i-post p s1 nil) (fn-pth-i-post p s2 nil)
               (equal (fn-rtc-buffer (fn-ptx-cur-bp p) s1) (fn-rtc-buffer (fn-ptx-cur-bp p) s2)))
          (equal (fn-ptx-answer p o 1 1 s1) (fn-ptx-answer p o 1 1 s2)))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-answer-physical-by-definition)))))

(defthm fn-pth-i-refuse-all-buffer-congruence
 (implies (and (fn-pth-i-runtime s1) (fn-pth-i-runtime s2)
               (fn-pth-i-queue ps s1 used) (fn-pth-i-queue ps s2 used)
               (fn-pth-i-post-buffers-equal ps s1 s2))
          (equal (fn-ptx-refuse-all ps 1 1 s1) (fn-ptx-refuse-all ps 1 1 s2)))
 :rule-classes nil
 :hints (("Goal" :induct (fn-pth-i-queue ps s1 used)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-ptx-refuse-all fn-pth-i-queue fn-pth-i-post-buffers-equal car-cons cdr-cons)))
  ("Subgoal *1/1" :use ((:instance fn-pth-i-answer-buffer-congruence (p (car ps)) (o :refused))))))

(defthm fn-pth-i-answer-post-buffers-frame
 (implies (and (fn-pth-i-runtime s) (fn-pth-i-post p s nil)
               (fn-pth-i-queue ps s used) (fn-pth-i-queue-avoids ps (fn-ptx-cur-bp p)))
          (fn-pth-i-post-buffers-equal ps s
           (mv-nth 0 (fn-rtc-requests (fn-ptx-answer p o 1 1 s) 1 1 s))))
 :hints (("Goal" :induct (fn-pth-i-queue ps s used)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-post-buffers-equal fn-pth-i-queue fn-pth-i-post fn-pth-i-queue-avoids
     fn-pth-i-answer-other-buffer fn-pth-i-visible-buffer car-cons cdr-cons)))
  ("Subgoal *1/1" :use ((:instance fn-pth-i-answer-other-buffer (j (fn-ptx-cur-bp (car ps))))))))

(defthm fn-pth-i-queue-avoids-used-buffer
 (implies (and (fn-pth-i-queue ps s used) (member-equal h used))
          (fn-pth-i-queue-avoids ps h))
 :hints (("Goal" :induct (fn-pth-i-queue ps s used)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-queue fn-pth-i-queue-avoids member-equal car-cons cdr-cons)))))

(defun fn-pth-i-refuse-all-induct (ps s used)
 (declare (xargs :guard t :verify-guards nil :measure (len ps)
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '(len o< o-finp o-p natp (:type-prescription len)))))))
 (if (consp ps)
  (fn-pth-i-refuse-all-induct (cdr ps)
   (non-exec (mv-nth 0 (fn-rtc-requests (fn-ptx-answer (car ps) :refused 1 1 s) 1 1 s)))
   (cons (fn-ptx-cur-bp (car ps)) used)) (list s used)))

(verify-guards fn-pth-i-refuse-all-induct)

(defthm fn-pth-i-requests-append-state
 (equal (mv-nth 0 (fn-rtc-requests (append rs tail) id inc s))
        (mv-nth 0 (fn-rtc-requests tail id inc (mv-nth 0 (fn-rtc-requests rs id inc s)))))
 :hints (("Goal" :induct (fn-rtc-requests rs id inc s)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-requests binary-append fn-hld-mv-nth-0-cons car-cons cdr-cons)))))

(defthm fn-pth-i-append-associative
 (equal (append (append x y) z) (append x (append y z)))
 :hints (("Goal" :induct (binary-append x y)
  :in-theory (union-theories (theory 'minimal-theory) '(binary-append car-cons cdr-cons)))))

(defthm fn-pth-i-requests-append-refused
 (equal (mv-nth 2 (fn-rtc-requests (append rs tail) id inc s))
        (append (mv-nth 2 (fn-rtc-requests rs id inc s))
                (mv-nth 2 (fn-rtc-requests tail id inc (mv-nth 0 (fn-rtc-requests rs id inc s))))))
 :hints (("Goal" :induct (fn-rtc-requests rs id inc s)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-requests binary-append fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition
     fn-pth-i-append-associative car-cons cdr-cons)))))

(defthm fn-pth-i-refuse-all-components
 (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s)
               (fn-pth-i-owner-uses (fn-rtc-uses s) m)
               (fn-pth-i-queue ps s used) (fn-pth-i-posts-untracked ps m))
  (let ((s2 (mv-nth 0 (fn-rtc-requests (fn-ptx-refuse-all ps 1 1 s) 1 1 s))))
   (and (fn-pth-i-runtime s2) (fn-pth-i-post-storage m s2)
        (fn-pth-i-owner-uses (fn-rtc-uses s2) m)
        (not (mv-nth 2 (fn-rtc-requests (fn-ptx-refuse-all ps 1 1 s) 1 1 s))))))
 :hints (("Goal" :induct (fn-pth-i-refuse-all-induct ps s used)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '((:induction fn-pth-i-refuse-all-induct) fn-ptx-refuse-all fn-pth-i-posts-untracked fn-pth-i-requests-append-state
     fn-pth-i-requests-append-refused fn-pth-i-answer-components
     fn-pth-i-queue-avoids-used-buffer fn-rtc-requests binary-append member-equal
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition car-cons cdr-cons)))
  ("Subgoal *1/1" :expand ((fn-pth-i-queue ps s used))
   :use ((:instance fn-pth-i-answer-components (p (car ps)) (o :refused))
         (:instance fn-pth-i-answer-queue (p (car ps)) (o :refused)
          (ps (cdr ps)) (used (cons (fn-ptx-cur-bp (car ps)) used)))
         (:instance fn-pth-i-answer-post-buffers-frame (p (car ps)) (o :refused)
          (ps (cdr ps)) (used (cons (fn-ptx-cur-bp (car ps)) used)))
         (:instance fn-pth-i-refuse-all-buffer-congruence
          (ps (cdr ps)) (used (cons (fn-ptx-cur-bp (car ps)) used)) (s1 s)
          (s2 (mv-nth 0 (fn-rtc-requests (fn-ptx-answer (car ps) :refused 1 1 s) 1 1 s))))))))


; End-transition storage, protocol ordering, and full-I restoration after machine installation.

(defthm fn-pth-i-subset-member
 (implies (and (subsetp-equal x y) (member-equal a x)) (member-equal a y))
 :hints (("Goal" :induct (subsetp-equal x y)
  :in-theory (union-theories (theory 'minimal-theory) '(subsetp-equal member-equal car-cons cdr-cons)))))

(defthm fn-pth-i-subset-cons
 (implies (subsetp-equal x y) (subsetp-equal x (cons a y)))
 :hints (("Goal" :induct (subsetp-equal x y)
  :in-theory (union-theories (theory 'minimal-theory) '(subsetp-equal member-equal car-cons cdr-cons)))))

(defun fn-pth-i-queue-used-induct (ps used1 used2)
 (declare (xargs :guard t))
 (if (consp ps)
  (fn-pth-i-queue-used-induct (cdr ps) (cons (fn-ptx-cur-bp (car ps)) used1)
                                      (cons (fn-ptx-cur-bp (car ps)) used2))
  (list used1 used2)))

(verify-guards fn-pth-i-queue-used-induct)

(defthm fn-pth-i-queue-weaken-used
 (implies (and (fn-pth-i-queue ps s used1) (subsetp-equal used2 used1))
          (fn-pth-i-queue ps s used2))
 :hints (("Goal" :induct (fn-pth-i-queue-used-induct ps used1 used2)
  :in-theory (union-theories (theory 'minimal-theory)
   '((:induction fn-pth-i-queue-used-induct) fn-pth-i-subset-member fn-pth-i-subset-cons
     fn-pth-i-queue subsetp-equal member-equal car-cons cdr-cons)))))

(defthm fn-pth-i-post-storage-inactive-empty
 (implies (and (fn-ptx-okp m) (fn-cbor-octet-listp (fn-ptx-kd-last (fn-ptx-kd m)))
               (< (fn-ptx-ext m) (expt 2 64)) (< (fn-ptx-nxt m) (expt 2 64))
               (member-eq (fn-ptx-ph m) '(:closed :idle :fenced))
               (not (fn-ptx-cur m)) (not (fn-ptx-q m))
               (not (fn-ptx-b1 m)) (not (fn-ptx-b3 m)))
          (fn-pth-i-post-storage m s))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-post-storage fn-pth-i-queue fn-ptx-in-flight-p member-equal
    (:executable-counterpart member-equal))))))

(defthm fn-pth-i-queue-start-storage
 (implies (and (consp ps) (fn-pth-i-queue ps s used)
               (fn-cbor-octet-listp (fn-ptx-kd-last kd)) (< (nfix ext) (expt 2 64))
               (fn-ptx-okp (mv-nth 0 (fn-ptx-start (car ps) (cdr ps) kd ext geo committed))))
          (fn-pth-i-post-storage (mv-nth 0 (fn-ptx-start (car ps) (cdr ps) kd ext geo committed)) s))
 :hints (("Goal" :expand ((fn-pth-i-queue ps s used))
  :use ((:instance fn-pth-i-post-storage-start (p (car ps)) (ps (cdr ps)))
        (:instance fn-pth-i-queue-weaken-used (ps (cdr ps))
         (used1 (cons (fn-ptx-cur-bp (car ps)) used)) (used2 (list (fn-ptx-cur-bp (car ps))))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(subsetp-equal member-equal car-cons cdr-cons)))))

(defthm fn-pth-i-post-storage-queue-used
 (implies (fn-pth-i-post-storage m s)
  (fn-pth-i-queue (fn-ptx-q m) s
   (append (if (member-eq (fn-ptx-ph m) '(:reading :hashing :extending :extsyncing :payload-writing :log-writing :committing))
               (list (fn-ptx-cur-bp (fn-ptx-cur m))) nil)
           (if (consp (fn-ptx-b1 m)) (list (fn-ptx-buf-h (fn-ptx-b1 m)) (fn-ptx-buf-h (fn-ptx-b3 m))) nil))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pth-i-post-storage)))))

(defthm fn-pth-i-post-storage-queue
 (implies (fn-pth-i-post-storage m s) (fn-pth-i-queue (fn-ptx-q m) s nil))
 :hints (("Goal" :use (fn-pth-i-post-storage-queue-used
   (:instance fn-pth-i-queue-weaken-used (ps (fn-ptx-q m)) (used2 nil)
    (used1 (append (if (member-eq (fn-ptx-ph m) '(:reading :hashing :extending :extsyncing :payload-writing :log-writing :committing))
               (list (fn-ptx-cur-bp (fn-ptx-cur m))) nil)
           (if (consp (fn-ptx-b1 m)) (list (fn-ptx-buf-h (fn-ptx-b1 m)) (fn-ptx-buf-h (fn-ptx-b3 m))) nil)))))
  :in-theory (union-theories (theory 'minimal-theory) '(subsetp-equal)))))

(defthm fn-pth-i-post-storage-inactive-mk
 (implies (and (member-eq ph '(:closed :idle :fenced))
               (fn-ptx-okp (fn-ptx-mk ph 0 nil nil kd ext ext nil nil nil committed nil geo nil))
               (fn-cbor-octet-listp (fn-ptx-kd-last kd)) (< (nfix ext) (expt 2 64)))
          (fn-pth-i-post-storage (fn-ptx-mk ph 0 nil nil kd ext ext nil nil nil committed nil geo nil) s))
 :hints (("Goal"
  :use ((:instance fn-pth-i-post-storage-inactive-empty
         (m (fn-ptx-mk ph 0 nil nil kd ext ext nil nil nil committed nil geo nil))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-ptx-accessors-of-mk fn-ptx-ph fn-ptx-mk fn-rtc-get-of-cons
     car-cons cdr-cons nfix natp (:executable-counterpart fn-rtc-get)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+))))))

(defthm fn-pth-i-end-post-storage
 (implies (and (fn-pth-i-post-storage m s)
               (fn-cbor-octet-listp (fn-ptx-kd-last kd))
               (< (nfix ext) (expt 2 64))
               (fn-ptx-okp (mv-nth 0 (fn-ptx-end m o kd ext fenced committed 1 1 st))))
          (fn-pth-i-post-storage (mv-nth 0 (fn-ptx-end m o kd ext fenced committed 1 1 st)) s))
 :hints (("Goal" :do-not-induct t :cases (fenced (consp (fn-ptx-q m)))
  :use ((:instance fn-pth-i-post-storage-inactive-mk (ph :idle) (geo (fn-ptx-geo m)))
        (:instance fn-pth-i-post-storage-inactive-mk (ph :fenced) (geo (fn-ptx-geo m)))
        fn-pth-i-post-storage-queue
        (:instance fn-pth-i-queue-start-storage (ps (fn-ptx-q m)) (used nil) (geo (fn-ptx-geo m))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-ptx-end-0 fn-ptx-accessors-of-mk
     nfix natp (:executable-counterpart expt) (:executable-counterpart <)
     (:executable-counterpart member-equal) (:executable-counterpart equal)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))

(defthm fn-pth-i-release-workspace-admitted
 (let ((r (list :release h (fn-rtc-b-gen (fn-rtc-buffer h s)))))
  (implies (and (fn-pth-i-runtime s) (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
                (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:workspace 1 1)))
   (and (not (mv-nth 2 (fn-rtc-request r 1 1 s)))
        (equal (mv-nth 0 (fn-rtc-request r 1 1 s))
         (fn-rtc-with-buffer h (list (fn-rtc-b-gen (fn-rtc-buffer h s)) '(:free) (fn-rtc-b-bytes (fn-rtc-buffer h s))) s)))))
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '(fn-rtc-request fn-rtc-req-release fn-rtc-get-of-cons fn-hld-mv-nth-0-cons
    fn-pth-i-mv-nth-2-cons-by-definition car-cons cdr-cons
    (:executable-counterpart fn-rtc-get) (:executable-counterpart nfix)
    (:executable-counterpart zp) (:executable-counterpart binary-+)
    (:executable-counterpart member-equal) (:executable-counterpart equal))))))

(defthm fn-pth-i-release-bufs-other-buffer
 (implies (and (natp j)
               (implies (consp (fn-ptx-b1 m)) (not (equal j (fn-ptx-buf-h (fn-ptx-b1 m)))))
               (implies (consp (fn-ptx-b3 m)) (not (equal j (fn-ptx-buf-h (fn-ptx-b3 m))))))
          (equal (fn-rtc-buffer j (mv-nth 0 (fn-rtc-requests (fn-ptx-release-bufs m 1 1 st) 1 1 s)))
                 (fn-rtc-buffer j s)))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-ptx-release-bufs fn-rtc-requests binary-append fn-pth-i-local-request-other-buffer
     fn-rtc-get-of-cons fn-hld-mv-nth-0-cons car-cons cdr-cons
     (:type-prescription fn-ptx-buf-h) nfix natp
     (:executable-counterpart fn-rtc-get) (:executable-counterpart nfix)
     (:executable-counterpart zp) (:executable-counterpart binary-+)
     (:executable-counterpart member-equal) (:executable-counterpart equal))))))

(defthm fn-pth-i-release-bufs-queue
 (implies (and (fn-pth-i-queue ps s used)
               (implies (consp (fn-ptx-b1 m)) (fn-pth-i-queue-avoids ps (fn-ptx-buf-h (fn-ptx-b1 m))))
               (implies (consp (fn-ptx-b3 m)) (fn-pth-i-queue-avoids ps (fn-ptx-buf-h (fn-ptx-b3 m)))))
          (fn-pth-i-queue ps (mv-nth 0 (fn-rtc-requests (fn-ptx-release-bufs m 1 1 st) 1 1 s)) used))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-ptx-release-bufs fn-rtc-requests binary-append fn-pth-i-queue-local-request
     fn-rtc-get-of-cons fn-hld-mv-nth-0-cons car-cons cdr-cons
     (:type-prescription fn-ptx-buf-h) nfix natp
     (:executable-counterpart fn-rtc-get) (:executable-counterpart nfix)
     (:executable-counterpart zp) (:executable-counterpart binary-+)
     (:executable-counterpart member-equal) (:executable-counterpart equal))))))

(defthm fn-pth-i-release-request-admitted
 (implies (and (fn-pth-i-runtime s) (fn-pth-i-visible-buffer h s nil)
               (equal g (fn-rtc-b-gen (fn-rtc-buffer h s))))
          (not (mv-nth 2 (fn-rtc-request (list :release h g) 1 1 s))))
 :hints (("Goal" :use (fn-pth-i-release-workspace-admitted)
  :in-theory (union-theories (theory 'minimal-theory) '(fn-pth-i-visible-buffer)))))

(defthm fn-pth-i-release-bufs-components
 (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m2 s)
               (fn-pth-i-owner-uses (fn-rtc-uses s) m2)
               (implies (consp (fn-ptx-b1 m))
                (and (fn-pth-i-visible-buffer (fn-ptx-buf-h (fn-ptx-b1 m)) s nil)
                     (fn-pth-i-storage-avoids m2 (fn-ptx-buf-h (fn-ptx-b1 m)))))
               (implies (consp (fn-ptx-b3 m))
                (and (fn-pth-i-visible-buffer (fn-ptx-buf-h (fn-ptx-b3 m)) s nil)
                     (fn-pth-i-storage-avoids m2 (fn-ptx-buf-h (fn-ptx-b3 m)))))
               (implies (and (consp (fn-ptx-b1 m)) (consp (fn-ptx-b3 m)))
                 (not (equal (fn-ptx-buf-h (fn-ptx-b1 m)) (fn-ptx-buf-h (fn-ptx-b3 m))))))
  (let ((s2 (mv-nth 0 (fn-rtc-requests (fn-ptx-release-bufs m 1 1 s) 1 1 s))))
   (and (fn-pth-i-runtime s2) (fn-pth-i-post-storage m2 s2)
        (fn-pth-i-owner-uses (fn-rtc-uses s2) m2)
        (not (mv-nth 2 (fn-rtc-requests (fn-ptx-release-bufs m 1 1 s) 1 1 s))))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-pth-i-visible-owner-readers (h (fn-ptx-buf-h (fn-ptx-b1 m))))
        (:instance fn-pth-i-visible-owner-readers (h (fn-ptx-buf-h (fn-ptx-b3 m)))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-ptx-release-bufs fn-rtc-requests binary-append fn-pth-i-runtime-request
     fn-pth-i-post-storage-untracked-request fn-pth-i-owner-local-request-protocol
     fn-pth-i-visible-owner-readers fn-pth-i-release-request-admitted fn-pth-i-local-request-other-buffer fn-rtc-request-config-frame
     fn-pth-i-visible-buffer fn-rtc-buffer-of-with fn-rtc-with-accessors fn-rtc-buffer-accessors
     fn-rtc-get-of-cons fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition car-cons cdr-cons
     (:type-prescription fn-ptx-buf-h) nfix natp
     (:executable-counterpart fn-rtc-get) (:executable-counterpart nfix)
     (:executable-counterpart zp) (:executable-counterpart binary-+)
     (:executable-counterpart member-equal) (:executable-counterpart equal))))))

(defthm fn-pth-i-end-avoids-queue-used
 (implies (and (fn-pth-i-queue (fn-ptx-q m) s used) (member-equal h used))
          (fn-pth-i-storage-avoids (mv-nth 0 (fn-ptx-end m o kd ext fenced committed 1 1 st)) h))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-pth-i-queue-avoids-used (ps (fn-ptx-q m))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-ptx-end-0 fn-ptx-start-0 fn-pth-i-storage-avoids fn-pth-i-queue-avoids
     fn-ptx-accessors-of-mk fn-ptx-cur-bp fn-rtc-get-of-cons nfix natp car-cons cdr-cons
     (:type-prescription fn-ptx-cur-bp) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+)
     (:executable-counterpart member-equal) (:executable-counterpart equal))))))

(defthm fn-pth-i-release-bufs-post
 (implies (and (fn-pth-i-post p s nil)
               (implies (consp (fn-ptx-b1 m)) (not (equal (fn-ptx-cur-bp p) (fn-ptx-buf-h (fn-ptx-b1 m)))))
               (implies (consp (fn-ptx-b3 m)) (not (equal (fn-ptx-cur-bp p) (fn-ptx-buf-h (fn-ptx-b3 m))))))
          (fn-pth-i-post p (mv-nth 0 (fn-rtc-requests (fn-ptx-release-bufs m 1 1 st) 1 1 s)) nil))
 :hints (("Goal" :use ((:instance fn-pth-i-release-bufs-other-buffer (j (fn-ptx-cur-bp p))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-post fn-pth-i-visible-buffer fn-rtc-requests-config-frame)))))

(defthm fn-pth-i-release-bufs-post-buffers-frame
 (implies (and (fn-pth-i-queue ps s used)
               (implies (consp (fn-ptx-b1 m)) (fn-pth-i-queue-avoids ps (fn-ptx-buf-h (fn-ptx-b1 m))))
               (implies (consp (fn-ptx-b3 m)) (fn-pth-i-queue-avoids ps (fn-ptx-buf-h (fn-ptx-b3 m)))))
          (fn-pth-i-post-buffers-equal ps s
           (mv-nth 0 (fn-rtc-requests (fn-ptx-release-bufs m 1 1 st) 1 1 s))))
 :hints (("Goal" :induct (fn-pth-i-queue ps s used)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-post-buffers-equal fn-pth-i-queue fn-pth-i-queue-avoids fn-pth-i-post
     fn-pth-i-visible-buffer fn-pth-i-release-bufs-other-buffer car-cons cdr-cons)))))

(defthm fn-pth-i-post-buffers-equal-transitive
 (implies (and (fn-pth-i-post-buffers-equal ps s1 s2) (fn-pth-i-post-buffers-equal ps s2 s3))
          (fn-pth-i-post-buffers-equal ps s1 s3))
 :hints (("Goal" :induct (fn-pth-i-post-buffers-equal ps s1 s2)
  :in-theory (union-theories (theory 'minimal-theory) '(fn-pth-i-post-buffers-equal car-cons cdr-cons)))))

(defthm fn-pth-i-end-source-workspaces
 (let ((h1 (fn-ptx-buf-h (fn-ptx-b1 m))) (h3 (fn-ptx-buf-h (fn-ptx-b3 m)))
       (bp (fn-ptx-cur-bp (fn-ptx-cur m))))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-owner-uses (fn-rtc-uses s) nil)
                (fn-pth-i-post-storage m s)
                (member-eq (fn-ptx-ph m) '(:reading :hashing :extending :extsyncing :payload-writing :log-writing :committing)))
   (and (fn-pth-i-post (fn-ptx-cur m) s nil)
        (implies (consp (fn-ptx-b1 m))
         (and (fn-pth-i-visible-buffer h1 s nil) (fn-pth-i-visible-buffer h3 s nil)
              (consp (fn-ptx-b3 m)) (not (equal h1 h3)) (not (equal h1 bp)) (not (equal h3 bp))))
        (implies (consp (fn-ptx-b3 m)) (consp (fn-ptx-b1 m))))))
 :hints (("Goal" :do-not-induct t :cases ((equal (fn-ptx-ph m) :reading) (equal (fn-ptx-ph m) :hashing)
   (equal (fn-ptx-ph m) :extending) (equal (fn-ptx-ph m) :extsyncing)
   (equal (fn-ptx-ph m) :payload-writing) (equal (fn-ptx-ph m) :log-writing) (equal (fn-ptx-ph m) :committing))
  :use ((:instance fn-pth-i-hands-only-visible-workspace (h (fn-ptx-cur-bp (fn-ptx-cur m))))
        (:instance fn-pth-i-hands-only-visible-workspace (h (fn-ptx-buf-h (fn-ptx-b1 m))))
        (:instance fn-pth-i-hands-only-visible-workspace (h (fn-ptx-buf-h (fn-ptx-b3 m)))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-post-storage fn-pth-i-post fn-pth-i-visible-buffer fn-ptx-in-flight-p member-equal
     (:executable-counterpart member-equal) (:executable-counterpart equal))))))

(defthm fn-pth-i-end-old-buffers-untracked
 (let ((m2 (mv-nth 0 (fn-ptx-end m o kd ext fenced committed 1 1 st)))
       (bp (fn-ptx-cur-bp (fn-ptx-cur m)))
       (h1 (fn-ptx-buf-h (fn-ptx-b1 m))) (h3 (fn-ptx-buf-h (fn-ptx-b3 m))))
  (implies (and (fn-pth-i-post-storage m s)
                (member-eq (fn-ptx-ph m) '(:reading :hashing :extending :extsyncing :payload-writing :log-writing :committing)))
   (and (fn-pth-i-storage-avoids m2 bp) (fn-pth-i-queue (fn-ptx-q m) s nil)
        (fn-pth-i-queue-avoids (fn-ptx-q m) bp)
        (implies (consp (fn-ptx-b1 m))
         (and (fn-pth-i-storage-avoids m2 h1) (fn-pth-i-storage-avoids m2 h3)
              (fn-pth-i-queue-avoids (fn-ptx-q m) h1) (fn-pth-i-queue-avoids (fn-ptx-q m) h3))))))
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-post-storage-queue-used
        fn-pth-i-post-storage-queue
        (:instance fn-pth-i-end-avoids-queue-used (h (fn-ptx-cur-bp (fn-ptx-cur m))) (used (append (if (member-eq (fn-ptx-ph m) '(:reading :hashing :extending :extsyncing :payload-writing :log-writing :committing)) (list (fn-ptx-cur-bp (fn-ptx-cur m))) nil) (if (consp (fn-ptx-b1 m)) (list (fn-ptx-buf-h (fn-ptx-b1 m)) (fn-ptx-buf-h (fn-ptx-b3 m))) nil))))
        (:instance fn-pth-i-queue-avoids-used (ps (fn-ptx-q m)) (h (fn-ptx-cur-bp (fn-ptx-cur m))) (used (append (if (member-eq (fn-ptx-ph m) '(:reading :hashing :extending :extsyncing :payload-writing :log-writing :committing)) (list (fn-ptx-cur-bp (fn-ptx-cur m))) nil) (if (consp (fn-ptx-b1 m)) (list (fn-ptx-buf-h (fn-ptx-b1 m)) (fn-ptx-buf-h (fn-ptx-b3 m))) nil))))
        (:instance fn-pth-i-end-avoids-queue-used (h (fn-ptx-buf-h (fn-ptx-b1 m))) (used (append (if (member-eq (fn-ptx-ph m) '(:reading :hashing :extending :extsyncing :payload-writing :log-writing :committing)) (list (fn-ptx-cur-bp (fn-ptx-cur m))) nil) (if (consp (fn-ptx-b1 m)) (list (fn-ptx-buf-h (fn-ptx-b1 m)) (fn-ptx-buf-h (fn-ptx-b3 m))) nil))))
        (:instance fn-pth-i-queue-avoids-used (ps (fn-ptx-q m)) (h (fn-ptx-buf-h (fn-ptx-b1 m))) (used (append (if (member-eq (fn-ptx-ph m) '(:reading :hashing :extending :extsyncing :payload-writing :log-writing :committing)) (list (fn-ptx-cur-bp (fn-ptx-cur m))) nil) (if (consp (fn-ptx-b1 m)) (list (fn-ptx-buf-h (fn-ptx-b1 m)) (fn-ptx-buf-h (fn-ptx-b3 m))) nil))))
        (:instance fn-pth-i-end-avoids-queue-used (h (fn-ptx-buf-h (fn-ptx-b3 m))) (used (append (if (member-eq (fn-ptx-ph m) '(:reading :hashing :extending :extsyncing :payload-writing :log-writing :committing)) (list (fn-ptx-cur-bp (fn-ptx-cur m))) nil) (if (consp (fn-ptx-b1 m)) (list (fn-ptx-buf-h (fn-ptx-b1 m)) (fn-ptx-buf-h (fn-ptx-b3 m))) nil))))
        (:instance fn-pth-i-queue-avoids-used (ps (fn-ptx-q m)) (h (fn-ptx-buf-h (fn-ptx-b3 m))) (used (append (if (member-eq (fn-ptx-ph m) '(:reading :hashing :extending :extsyncing :payload-writing :log-writing :committing)) (list (fn-ptx-cur-bp (fn-ptx-cur m))) nil) (if (consp (fn-ptx-b1 m)) (list (fn-ptx-buf-h (fn-ptx-b1 m)) (fn-ptx-buf-h (fn-ptx-b3 m))) nil)))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(binary-append member-equal car-cons cdr-cons)))))

(defthm fn-pth-i-release-bufs-owner-uses
 (equal (fn-pth-i-owner-uses (fn-rtc-uses (mv-nth 0 (fn-rtc-requests (fn-ptx-release-bufs old 1 1 snapshot) 1 1 s))) m)
        (fn-pth-i-owner-uses (fn-rtc-uses s) m))
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '(fn-ptx-release-bufs fn-rtc-requests binary-append fn-pth-i-owner-local-request-protocol
    fn-rtc-get-of-cons fn-hld-mv-nth-0-cons car-cons cdr-cons
    (:executable-counterpart fn-rtc-get) (:executable-counterpart nfix)
    (:executable-counterpart zp) (:executable-counterpart binary-+)
    (:executable-counterpart member-equal) (:executable-counterpart equal))))))

(defthm fn-pth-i-answer-owner-uses
 (equal (fn-pth-i-owner-uses (fn-rtc-uses (mv-nth 0 (fn-rtc-requests (fn-ptx-answer p o 1 1 snapshot) 1 1 s))) m)
        (fn-pth-i-owner-uses (fn-rtc-uses s) m))
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '(fn-ptx-answer fn-rtc-requests fn-pth-i-owner-local-request-protocol
    fn-rtc-get-of-cons fn-hld-mv-nth-0-cons car-cons cdr-cons
    (:executable-counterpart fn-rtc-get) (:executable-counterpart nfix)
    (:executable-counterpart zp) (:executable-counterpart binary-+)
    (:executable-counterpart member-equal) (:executable-counterpart equal))))))

(defthm fn-pth-i-end-done-prefix
 (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s)
               (fn-pth-i-owner-uses (fn-rtc-uses s) nil)
               (member-eq (fn-ptx-ph m) '(:reading :hashing :extending :extsyncing :payload-writing :log-writing :committing))
               (fn-cbor-octet-listp (fn-ptx-kd-last kd)) (< (nfix ext) (expt 2 64))
               (fn-ptx-okp (mv-nth 0 (fn-ptx-end m o kd ext fenced committed 1 1 s))))
  (let ((s2 (mv-nth 0 (fn-rtc-requests (append (fn-ptx-release-bufs m 1 1 s) (fn-ptx-answer (fn-ptx-cur m) o 1 1 s)) 1 1 s))) (m2 (mv-nth 0 (fn-ptx-end m o kd ext fenced committed 1 1 s))))
   (and (fn-pth-i-runtime s2) (fn-pth-i-post-storage m2 s2)
        (fn-pth-i-owner-uses (fn-rtc-uses s2) nil)
        (fn-pth-i-owner-uses (fn-rtc-uses s2) m2)
        (fn-pth-i-queue (fn-ptx-q m) s2 nil)
        (fn-pth-i-post-buffers-equal (fn-ptx-q m) s s2)
        (not (mv-nth 2 (fn-rtc-requests (append (fn-ptx-release-bufs m 1 1 s) (fn-ptx-answer (fn-ptx-cur m) o 1 1 s)) 1 1 s))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-end-source-workspaces
        (:instance fn-pth-i-end-old-buffers-untracked (st s))
        (:instance fn-pth-i-end-post-storage (st s))
        (:instance fn-pth-i-release-bufs-components (m2 (mv-nth 0 (fn-ptx-end m o kd ext fenced committed 1 1 s))))
        (:instance fn-pth-i-release-bufs-post (p (fn-ptx-cur m)) (st s))
        (:instance fn-pth-i-release-bufs-other-buffer (j (fn-ptx-cur-bp (fn-ptx-cur m))) (st s))
        (:instance fn-pth-i-release-bufs-queue (ps (fn-ptx-q m)) (used nil) (st s))
        (:instance fn-pth-i-release-bufs-post-buffers-frame (ps (fn-ptx-q m)) (used nil) (st s))
        (:instance fn-pth-i-answer-buffer-congruence (p (fn-ptx-cur m)) (s1 s) (s2 (mv-nth 0 (fn-rtc-requests (fn-ptx-release-bufs m 1 1 s) 1 1 s))))
        (:instance fn-pth-i-answer-components (p (fn-ptx-cur m)) (s (mv-nth 0 (fn-rtc-requests (fn-ptx-release-bufs m 1 1 s) 1 1 s))) (m (mv-nth 0 (fn-ptx-end m o kd ext fenced committed 1 1 s))))
        (:instance fn-pth-i-answer-queue (p (fn-ptx-cur m)) (s (mv-nth 0 (fn-rtc-requests (fn-ptx-release-bufs m 1 1 s) 1 1 s))) (ps (fn-ptx-q m)) (used nil))
        (:instance fn-pth-i-answer-post-buffers-frame (p (fn-ptx-cur m)) (s (mv-nth 0 (fn-rtc-requests (fn-ptx-release-bufs m 1 1 s) 1 1 s))) (ps (fn-ptx-q m)) (used nil))
        (:instance fn-pth-i-post-buffers-equal-transitive (ps (fn-ptx-q m)) (s1 s) (s2 (mv-nth 0 (fn-rtc-requests (fn-ptx-release-bufs m 1 1 s) 1 1 s))) (s3 (mv-nth 0 (fn-rtc-requests (fn-ptx-answer (fn-ptx-cur m) o 1 1 (mv-nth 0 (fn-rtc-requests (fn-ptx-release-bufs m 1 1 s) 1 1 s))) 1 1 (mv-nth 0 (fn-rtc-requests (fn-ptx-release-bufs m 1 1 s) 1 1 s)))))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-requests-append-state fn-pth-i-requests-append-refused fn-pth-i-runtime-requests
     fn-pth-i-release-bufs-owner-uses fn-pth-i-answer-owner-uses
     fn-pth-i-hands-only-compatible-with-every-machine binary-append natp (:type-prescription fn-ptx-cur-bp))))))

(defthm fn-pth-i-timer-restores-post-state
 (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s)
               (fn-pth-i-owner-uses (fn-rtc-uses s) nil) (equal (fn-ptx-expected m) :timer))
  (let ((s2 (mv-nth 0 (fn-rtc-requests (list (fn-ptx-timer)) 1 1 s))))
   (and (fn-pth-i-runtime s2) (fn-pth-i-post-state m s2)
        (not (mv-nth 2 (fn-rtc-requests (list (fn-ptx-timer)) 1 1 s))))))
 :hints (("Goal"
  :use ((:instance fn-pth-i-owner-unbuffered-request-admitted (r (fn-ptx-timer)))
        (:instance fn-pth-i-admitted-unbuffered-request-state (r (fn-ptx-timer)) (id 1) (inc 1))
        (:instance fn-pth-i-runtime-request (r (fn-ptx-timer)) (id 1) (inc 1))
        fn-pth-i-post-state-issue-expected fn-pth-i-timer-and-fsync-data)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-hands-only-compatible-with-every-machine fn-pth-i-hands-only-has-no-operation
     fn-rtc-requests binary-append fn-ptx-timer fn-rtc-get-of-cons
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition car-cons cdr-cons
     (:executable-counterpart fn-rtc-get) (:executable-counterpart nfix)
     (:executable-counterpart zp) (:executable-counterpart binary-+)
     (:executable-counterpart fn-rtc-buffered-kind-p) (:executable-counterpart equal))))))

(defthm fn-pth-i-inactive-empty-avoids-all
 (implies (and (member-eq (fn-ptx-ph m) '(:closed :idle :fenced))
               (not (fn-ptx-q m)) (not (fn-ptx-b1 m)))
          (fn-pth-i-storage-avoids m h))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-storage-avoids fn-pth-i-queue-avoids member-equal (:executable-counterpart member-equal))))))

(defthm fn-pth-i-inactive-empty-posts-untracked
 (implies (and (member-eq (fn-ptx-ph m) '(:closed :idle :fenced))
               (not (fn-ptx-q m)) (not (fn-ptx-b1 m)))
          (fn-pth-i-posts-untracked ps m))
 :hints (("Goal" :induct (fn-pth-i-posts-untracked ps m)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-posts-untracked fn-pth-i-inactive-empty-avoids-all car-cons cdr-cons)))))

(defthm fn-pth-i-no-expected-post-state
 (implies (and (fn-pth-i-post-storage m s) (fn-pth-i-owner-uses (fn-rtc-uses s) m)
               (not (fn-ptx-expected m)))
          (fn-pth-i-post-state m s))
 :hints (("Goal" :use (fn-pth-i-post-storage-and-protocol-by-definition)
  :in-theory (theory 'minimal-theory))))

(defthm fn-pth-i-empty-append-right-nil
 (implies (not (append x y)) (equal (append x y nil) nil))
 :hints (("Goal" :do-not-induct t :cases ((consp x)) :expand ((binary-append x y) (binary-append x (binary-append y nil)))
  :in-theory (union-theories (theory 'minimal-theory) '(binary-append)))))

(defthm fn-pth-i-end-fenced-post-state
 (implies (and fenced (fn-pth-i-runtime s) (fn-pth-i-post-storage m s)
               (fn-pth-i-owner-uses (fn-rtc-uses s) nil)
               (member-eq (fn-ptx-ph m) '(:reading :hashing :extending :extsyncing :payload-writing :log-writing :committing))
               (fn-cbor-octet-listp (fn-ptx-kd-last kd)) (< (nfix ext) (expt 2 64))
               (fn-ptx-okp (mv-nth 0 (fn-ptx-end m o kd ext fenced committed 1 1 s))))
  (let ((s2 (mv-nth 0 (fn-rtc-requests (mv-nth 1 (fn-ptx-end m o kd ext fenced committed 1 1 s)) 1 1 s))))
   (and (fn-pth-i-runtime s2) (fn-pth-i-post-state (mv-nth 0 (fn-ptx-end m o kd ext fenced committed 1 1 s)) s2)
        (not (mv-nth 2 (fn-rtc-requests (mv-nth 1 (fn-ptx-end m o kd ext fenced committed 1 1 s)) 1 1 s))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-end-done-prefix fn-pth-i-post-storage-queue
        (:instance fn-pth-i-refuse-all-components (s (mv-nth 0 (fn-rtc-requests (append (fn-ptx-release-bufs m 1 1 s) (fn-ptx-answer (fn-ptx-cur m) o 1 1 s)) 1 1 s))) (m (mv-nth 0 (fn-ptx-end m o kd ext fenced committed 1 1 s))) (ps (fn-ptx-q m)) (used nil))
        (:instance fn-pth-i-refuse-all-buffer-congruence (ps (fn-ptx-q m)) (s1 s) (s2 (mv-nth 0 (fn-rtc-requests (append (fn-ptx-release-bufs m 1 1 s) (fn-ptx-answer (fn-ptx-cur m) o 1 1 s)) 1 1 s))) (used nil))
        (:instance fn-pth-i-no-expected-post-state (s (mv-nth 0 (fn-rtc-requests (fn-ptx-refuse-all (fn-ptx-q m) 1 1 (mv-nth 0 (fn-rtc-requests (append (fn-ptx-release-bufs m 1 1 s) (fn-ptx-answer (fn-ptx-cur m) o 1 1 s)) 1 1 s))) 1 1 (mv-nth 0 (fn-rtc-requests (append (fn-ptx-release-bufs m 1 1 s) (fn-ptx-answer (fn-ptx-cur m) o 1 1 s)) 1 1 s))))) (m (mv-nth 0 (fn-ptx-end m o kd ext fenced committed 1 1 s)))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-ptx-end fn-ptx-start fn-ptx-expected fn-ptx-accessors-of-mk
     fn-pth-i-inactive-empty-posts-untracked fn-pth-i-requests-append-state fn-pth-i-requests-append-refused
     fn-pth-i-empty-append-right-nil fn-pth-i-append-associative fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-1-cons-by-definition
     fn-rtc-requests fn-pth-i-mv-nth-2-cons-by-definition binary-append car-cons cdr-cons
     (:executable-counterpart member-equal) (:executable-counterpart equal))))))

(defthm fn-pth-i-end-queue-post-state
 (implies (and (not fenced) (consp (fn-ptx-q m)) (fn-pth-i-runtime s) (fn-pth-i-post-storage m s)
               (fn-pth-i-owner-uses (fn-rtc-uses s) nil)
               (member-eq (fn-ptx-ph m) '(:reading :hashing :extending :extsyncing :payload-writing :log-writing :committing))
               (fn-cbor-octet-listp (fn-ptx-kd-last kd)) (< (nfix ext) (expt 2 64))
               (fn-ptx-okp (mv-nth 0 (fn-ptx-end m o kd ext fenced committed 1 1 s))))
  (let ((s2 (mv-nth 0 (fn-rtc-requests (mv-nth 1 (fn-ptx-end m o kd ext fenced committed 1 1 s)) 1 1 s))))
   (and (fn-pth-i-runtime s2) (fn-pth-i-post-state (mv-nth 0 (fn-ptx-end m o kd ext fenced committed 1 1 s)) s2)
        (not (mv-nth 2 (fn-rtc-requests (mv-nth 1 (fn-ptx-end m o kd ext fenced committed 1 1 s)) 1 1 s))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-end-done-prefix fn-pth-i-post-storage-queue
        (:instance fn-pth-i-timer-restores-post-state (s (mv-nth 0 (fn-rtc-requests (append (fn-ptx-release-bufs m 1 1 s) (fn-ptx-answer (fn-ptx-cur m) o 1 1 s)) 1 1 s))) (m (mv-nth 0 (fn-ptx-end m o kd ext fenced committed 1 1 s)))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-ptx-end fn-ptx-start fn-ptx-expected fn-ptx-accessors-of-mk
     fn-pth-i-inactive-empty-posts-untracked fn-pth-i-requests-append-state fn-pth-i-requests-append-refused
     fn-pth-i-empty-append-right-nil fn-pth-i-append-associative fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-1-cons-by-definition
     fn-rtc-requests fn-pth-i-mv-nth-2-cons-by-definition binary-append car-cons cdr-cons
     (:executable-counterpart member-equal) (:executable-counterpart equal))))))

(defthm fn-pth-i-end-idle-post-state
 (implies (and (not fenced) (not (consp (fn-ptx-q m))) (fn-pth-i-runtime s) (fn-pth-i-post-storage m s)
               (fn-pth-i-owner-uses (fn-rtc-uses s) nil)
               (member-eq (fn-ptx-ph m) '(:reading :hashing :extending :extsyncing :payload-writing :log-writing :committing))
               (fn-cbor-octet-listp (fn-ptx-kd-last kd)) (< (nfix ext) (expt 2 64))
               (fn-ptx-okp (mv-nth 0 (fn-ptx-end m o kd ext fenced committed 1 1 s))))
  (let ((s2 (mv-nth 0 (fn-rtc-requests (mv-nth 1 (fn-ptx-end m o kd ext fenced committed 1 1 s)) 1 1 s))))
   (and (fn-pth-i-runtime s2) (fn-pth-i-post-state (mv-nth 0 (fn-ptx-end m o kd ext fenced committed 1 1 s)) s2)
        (not (mv-nth 2 (fn-rtc-requests (mv-nth 1 (fn-ptx-end m o kd ext fenced committed 1 1 s)) 1 1 s))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-end-done-prefix fn-pth-i-post-storage-queue
        (:instance fn-pth-i-no-expected-post-state (s (mv-nth 0 (fn-rtc-requests (append (fn-ptx-release-bufs m 1 1 s) (fn-ptx-answer (fn-ptx-cur m) o 1 1 s)) 1 1 s))) (m (mv-nth 0 (fn-ptx-end m o kd ext fenced committed 1 1 s)))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-ptx-end fn-ptx-start fn-ptx-expected fn-ptx-accessors-of-mk
     fn-pth-i-inactive-empty-posts-untracked fn-pth-i-requests-append-state fn-pth-i-requests-append-refused
     fn-pth-i-empty-append-right-nil fn-pth-i-append-associative fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-1-cons-by-definition
     fn-rtc-requests fn-pth-i-mv-nth-2-cons-by-definition binary-append car-cons cdr-cons
     (:executable-counterpart member-equal) (:executable-counterpart equal))))))

(defthm fn-pth-i-end-requests-post-state
 (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s)
               (fn-pth-i-owner-uses (fn-rtc-uses s) nil)
               (member-eq (fn-ptx-ph m) '(:reading :hashing :extending :extsyncing :payload-writing :log-writing :committing))
               (fn-cbor-octet-listp (fn-ptx-kd-last kd)) (< (nfix ext) (expt 2 64))
               (fn-ptx-okp (mv-nth 0 (fn-ptx-end m o kd ext fenced committed 1 1 s))))
  (let ((s2 (mv-nth 0 (fn-rtc-requests (mv-nth 1 (fn-ptx-end m o kd ext fenced committed 1 1 s)) 1 1 s))))
   (and (fn-pth-i-runtime s2) (fn-pth-i-post-state (mv-nth 0 (fn-ptx-end m o kd ext fenced committed 1 1 s)) s2)
        (not (mv-nth 2 (fn-rtc-requests (mv-nth 1 (fn-ptx-end m o kd ext fenced committed 1 1 s)) 1 1 s))))))
 :rule-classes nil
 :hints (("Goal" :use (fn-pth-i-end-fenced-post-state fn-pth-i-end-queue-post-state fn-pth-i-end-idle-post-state)
  :in-theory (theory 'minimal-theory))))

(defthm fn-pth-i-gen-with-mstate
 (equal (fn-ptx-gen h 1 1 (fn-rtc-with-mstate j m s)) (fn-ptx-gen h 1 1 s))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-ptx-gen fn-rtc-st-v-gen fn-rtc-st$a-v-gen fn-rtc-vb fn-rtc-view fn-rtc-with-accessors)))))

(defthm fn-pth-i-release-bufs-with-mstate
 (equal (fn-ptx-release-bufs old 1 1 (fn-rtc-with-mstate j m s)) (fn-ptx-release-bufs old 1 1 s))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-ptx-release-bufs fn-pth-i-gen-with-mstate)))))

(defthm fn-pth-i-refuse-all-with-mstate
 (equal (fn-ptx-refuse-all ps 1 1 (fn-rtc-with-mstate j m s)) (fn-ptx-refuse-all ps 1 1 s))
 :hints (("Goal" :induct (fn-ptx-refuse-all ps 1 1 s)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-ptx-refuse-all fn-pth-i-answer-with-mstate car-cons cdr-cons)))))

(defthm fn-pth-i-end-with-mstate
 (equal (fn-ptx-end old o kd ext fenced committed 1 1 (fn-rtc-with-mstate j m s))
        (fn-ptx-end old o kd ext fenced committed 1 1 s))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-ptx-end fn-pth-i-release-bufs-with-mstate fn-pth-i-refuse-all-with-mstate fn-pth-i-answer-with-mstate)))))

(defthm fn-pth-i-end-after-machine
 (let* ((end (fn-ptx-end m o kd ext fenced committed 1 1 s)) (m2 (mv-nth 0 end)))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s)
                (fn-pth-i-owner-uses (fn-rtc-uses s) nil)
                (member-eq (fn-ptx-ph m) '(:reading :hashing :extending :extsyncing :payload-writing :log-writing :committing))
                (fn-cbor-octet-listp (fn-ptx-kd-last kd)) (< (nfix ext) (expt 2 64)) (fn-ptx-okp m2))
   (and (fn-pth-i (mv-nth 0 (fn-rtc-requests (mv-nth 1 end) 1 1 (fn-rtc-with-mstate 1 m2 s))))
        (not (mv-nth 2 (fn-rtc-requests (mv-nth 1 end) 1 1 (fn-rtc-with-mstate 1 m2 s)))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-pth-i-end-requests-post-state
          (s (fn-rtc-with-mstate 1 (mv-nth 0 (fn-ptx-end m o kd ext fenced committed 1 1 s)) s)))
        (:instance fn-pth-i-runtime-and-post-state-by-definition
          (s (mv-nth 0 (fn-rtc-requests (mv-nth 1 (fn-ptx-end m o kd ext fenced committed 1 1 s)) 1 1
              (fn-rtc-with-mstate 1 (mv-nth 0 (fn-ptx-end m o kd ext fenced committed 1 1 s)) s))))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-end-with-mstate fn-pth-i-runtime-with-mstate fn-pth-i-post-storage-with-mstate
     fn-rtc-with-accessors fn-rtc-requests-keeps-mstates fn-rtc-mstate fn-pth-i-owner-machine-index
     fn-rtc-mstate-of-with fn-rtc-get-of-set (:executable-counterpart nfix) (:executable-counterpart natp))))))


; I-AMEND-1: hashing establishes the octet trailer consumed by commit.
(defthm fn-pth-i-b3-octets-are-cbor-octets
 (implies (fn-b3-octet-listp x) (fn-cbor-octet-listp x))
 :hints (("Goal" :induct (fn-b3-octet-listp x)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-b3-octet-listp fn-cbor-octet-listp fn-cbor-octetp)))))

(defthm fn-pth-i-finish-digest-is-octets
 (fn-cbor-octet-listp (fn-ptx-finish-digest pos st n spans id inc pool))
 :hints (("Goal"
  :use ((:instance fn-ptx-finish-digest-shape (fn-rtc-st pool)))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-b3-octets-are-cbor-octets)))))

(defthm fn-pth-i-end-does-not-enter-flight
 (not (fn-ptx-in-flight-p (fn-ptx-ph (mv-nth 0 (fn-ptx-end m o kd ext fenced committed id inc st)))))
 :hints (("Goal" :in-theory (union-theories
  (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '(fn-ptx-end-0 fn-ptx-start-0 fn-ptx-in-flight-p fn-ptx-accessors-of-mk
    fn-hld-mv-nth-0-cons car-cons cdr-cons
    (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-pth-i-hash-establishes-flight-trailer-octets
 (let ((m2 (mv-nth 0 (fn-ptx-hash m q id inc st))))
  (implies (and (equal (fn-ptx-ph m) :hashing)
                (fn-ptx-in-flight-p (fn-ptx-ph m2)))
           (fn-cbor-octet-listp (fn-rtc-get 1 (fn-ptx-hs m2)))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-pth-i-end-does-not-enter-flight
    (m (fn-ptx-chg m :committed nil)) (o :refused) (kd (fn-ptx-kd m))
    (ext (fn-ptx-ext m)) (fenced nil) (committed nil)))
  :in-theory (union-theories
   (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-ptx-hash-0 fn-ptx-accessors-of-mk fn-ptx-in-flight-p
     fn-pth-i-finish-digest-is-octets fn-rtc-get-of-cons
     car-cons cdr-cons fn-hld-mv-nth-0-cons
     (:executable-counterpart equal) (:executable-counterpart member-equal)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+))))))

(defthm fn-pth-i-step-preserves-flight-trailer-octets
 (let ((m2 (mv-nth 0 (fn-ptx-step m ev st q))))
  (implies (and (fn-ptx-in-flight-p (fn-ptx-ph m))
                (fn-cbor-octet-listp (fn-rtc-get 1 (fn-ptx-hs m))))
           (implies (fn-ptx-in-flight-p (fn-ptx-ph m2))
                    (fn-cbor-octet-listp (fn-rtc-get 1 (fn-ptx-hs m2))))))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories
   (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-ptx-end-0 fn-ptx-start-0 fn-ptx-step fn-ptx-step1-0 fn-ptx-in-flight-p fn-ptx-accessors-of-mk
     fn-pth-i-end-does-not-enter-flight fn-ptx-broken
     fn-hld-mv-nth-0-cons car-cons cdr-cons
     (:executable-counterpart equal) (:executable-counterpart member-equal))))))


; I-AMEND-1 clause is preserved by every machine step, including entry.
(defthm fn-pth-i-reading-does-not-enter-flight
 (implies (equal (fn-ptx-ph m) :reading)
          (not (fn-ptx-in-flight-p (fn-ptx-ph (mv-nth 0 (fn-ptx-read m q id inc st))))))
 :hints (("Goal" :use (fn-ptx-read-fields)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-ptx-in-flight-p member-equal (:executable-counterpart equal)
     (:executable-counterpart member-equal))))))

(defthm fn-pth-i-step-keeps-flight-trailer-clause
 (let ((m2 (mv-nth 0 (fn-ptx-step m ev st q))))
  (implies (implies (fn-ptx-in-flight-p (fn-ptx-ph m))
                    (fn-cbor-octet-listp (fn-rtc-get 1 (fn-ptx-hs m))))
           (implies (fn-ptx-in-flight-p (fn-ptx-ph m2))
                    (fn-cbor-octet-listp (fn-rtc-get 1 (fn-ptx-hs m2))))))
 :hints (("Goal" :do-not-induct t
  :cases ((fn-ptx-in-flight-p (fn-ptx-ph m)))
  :use ((:instance fn-pth-i-step-preserves-flight-trailer-octets)
        (:instance fn-pth-i-hash-establishes-flight-trailer-octets
          (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev)))
        (:instance fn-pth-i-reading-does-not-enter-flight
          (id (fn-rtc-ev-id ev)) (inc (fn-rtc-ev-inc ev))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-ptx-opened fn-ptx-end-0 fn-ptx-step fn-ptx-step1-0 fn-ptx-accessors-of-mk fn-ptx-start-0
     fn-ptx-in-flight-p fn-ptx-broken fn-pth-i-end-does-not-enter-flight
     fn-hld-mv-nth-0-cons car-cons cdr-cons
     (:executable-counterpart equal) (:executable-counterpart member-equal))))))


; Actual owner end delivery consumes the admitted end composition.
(defthm fn-pth-i-post-storage-chain-and-extents
 (implies (fn-pth-i-post-storage m s)
  (and (fn-cbor-octet-listp (fn-ptx-kd-last (fn-ptx-kd m)))
       (< (fn-ptx-ext m) (expt 2 64)) (< (fn-ptx-nxt m) (expt 2 64))
       (implies (fn-ptx-in-flight-p (fn-ptx-ph m))
                (fn-cbor-octet-listp (fn-rtc-get 1 (fn-ptx-hs m))))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-post-storage)))))

(defthm fn-pth-i-kd-commit-last
 (equal (fn-ptx-kd-last (fn-ptx-kd-commit kd trailer elen)) trailer)
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-ptx-kd-commit fn-ptx-kd-last fn-ptx-kd-mk fn-rtc-get-of-cons
    car-cons cdr-cons (:executable-counterpart nfix) (:executable-counterpart zp)
    (:executable-counterpart binary-+))))))

(defthm fn-pth-i-owner-end-deliver
 (let* ((m (fn-rtc-mstate 1 s)) (old (fn-ptx-chg m :committed nil))
        (end (fn-ptx-end old o kd ext fenced committed 1 1 s))
        (step (fn-ptx-step m ev s (nfix q))))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage old s)
                (fn-pth-i-owner-uses (fn-rtc-uses s) nil)
                (member-eq (fn-ptx-ph old) '(:reading :hashing :extending :extsyncing :payload-writing :log-writing :committing))
                (fn-cbor-octet-listp (fn-ptx-kd-last kd)) (< (nfix ext) (expt 2 64))
                (equal (fn-rtc-ev-id ev) 1) (equal (fn-rtc-ev-inc ev) 1)
                (equal (mv-nth 0 step) (mv-nth 0 end))
                (equal (mv-nth 1 step) (mv-nth 1 end))
                (fn-ptx-okp (mv-nth 0 end)))
   (and (fn-pth-i (mv-nth 0 (fn-pth-deliver s 1 1 ev q)))
        (not (mv-nth 2 (fn-pth-deliver s 1 1 ev q))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-ptx-step-reads-view (m (fn-rtc-mstate 1 s)) (st s) (q (nfix q)))
        (:instance fn-pth-i-end-after-machine
          (m (fn-ptx-chg (fn-rtc-mstate 1 s) :committed nil))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-view-state fn-pth-deliver fn-pth-m-step fn-pthm-step
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition
     car-cons cdr-cons)))))


; All actual in-flight owner completions preserve full I and have no refusals.
(defthm fn-pth-i-flight-end-machine-results
 (let* ((ph (fn-ptx-ph m)) (kind (fn-rtc-get 0 ev))
        (tag (fn-rtc-get 0 (fn-rtc-get 1 ev))) (n (fn-rtc-get 1 (fn-rtc-get 1 ev)))
        (commit (and (equal ph :committing) (equal tag :done)))
        (kd (if commit (fn-ptx-kd-commit (fn-ptx-kd m) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-elen m)) (fn-ptx-kd m)))
        (ext (if commit (fn-ptx-nxt m) (fn-ptx-ext m)))
        (o (if commit :posted (if (member-eq ph '(:extending :extsyncing)) :refused :uncertain)))
        (end (fn-ptx-end (fn-ptx-chg m :committed nil) o kd ext (not commit) commit
                        (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st)))
  (implies (and (fn-ptx-okp m)
                (or (and (equal ph :extending) (equal kind :extend) (not (equal tag :done)))
                    (and (equal ph :extsyncing) (equal kind :fsync) (not (equal tag :done)))
                    (and (member-eq ph '(:payload-writing :log-writing)) (equal kind :pwrite)
                         (not (and (equal tag :done) (equal n (fn-ptx-span-n (fn-ptx-k m) m)))))
                    (and (equal ph :committing) (equal kind :fsync))))
           (and (equal (mv-nth 0 (fn-ptx-step m ev st q)) (mv-nth 0 end))
                (equal (mv-nth 1 (fn-ptx-step m ev st q)) (mv-nth 1 end))
                (fn-ptx-okp (mv-nth 0 end)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-ptx-step-keeps-ok)
  :cases ((equal (fn-ptx-ph m) :extending) (equal (fn-ptx-ph m) :extsyncing)
          (equal (fn-ptx-ph m) :payload-writing) (equal (fn-ptx-ph m) :log-writing))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-ptx-step fn-ptx-step1 fn-ptx-okp-wfp fn-hld-mv-nth-0-cons
     fn-pth-i-mv-nth-1-cons-by-definition car-cons cdr-cons
     member-equal (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-pth-i-flight-end-host-delivery
 (let* ((m (fn-rtc-mstate 1 s)) (ph (fn-ptx-ph m))
        (tag (fn-rtc-get 0 (fn-rtc-get 1 ev))) (n (fn-rtc-get 1 (fn-rtc-get 1 ev))))
  (implies (and (fn-pth-i s) (fn-ptx-in-flight-p ph)
                (fn-rtc-completionp e) (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))
                (equal (fn-rtc-e-id e) 1) (equal (fn-rtc-e-inc e) 1)
                (equal (fn-rtc-e-kind e) (fn-ptx-expected m))
                (equal (fn-rtc-ev-id ev) 1) (equal (fn-rtc-ev-inc ev) 1)
                (equal (fn-rtc-get 0 ev) (fn-ptx-expected m))
                (or (and (member-eq ph '(:extending :extsyncing)) (not (equal tag :done)))
                    (and (member-eq ph '(:payload-writing :log-writing))
                         (not (and (equal tag :done) (equal n (fn-ptx-span-n (fn-ptx-k m) m)))))
                    (equal ph :committing)))
           (and (fn-pth-i (mv-nth 0 (fn-pth-deliver (fn-rtc-end-use s e) 1 1 ev q)))
                (not (mv-nth 2 (fn-pth-deliver (fn-rtc-end-use s e) 1 1 ev q))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :cases ((equal (fn-ptx-ph (fn-rtc-mstate 1 s)) :extending)
          (equal (fn-ptx-ph (fn-rtc-mstate 1 s)) :extsyncing)
          (equal (fn-ptx-ph (fn-rtc-mstate 1 s)) :payload-writing)
          (equal (fn-ptx-ph (fn-rtc-mstate 1 s)) :log-writing))
  :use (fn-pth-i-before-machine-after-end-use
        (:instance fn-pth-i-owner-protocol-after-expected-completion (m2 nil))
        (:instance fn-pth-i-post-storage-machine-facts (m (fn-rtc-mstate 1 s)) (s (fn-rtc-end-use s e)))
        (:instance fn-pth-i-post-storage-chain-and-extents (m (fn-rtc-mstate 1 s)) (s (fn-rtc-end-use s e)))
        (:instance fn-pth-i-post-storage-m0 (m (fn-rtc-mstate 1 s)) (s (fn-rtc-end-use s e)))
        (:instance fn-pth-i-flight-end-machine-results (m (fn-rtc-mstate 1 s)) (st (fn-rtc-end-use s e)) (q (nfix q)))
        (:instance fn-pth-i-owner-end-deliver (s (fn-rtc-end-use s e)) (kd (if (and (equal (fn-ptx-ph (fn-rtc-mstate 1 s)) :committing) (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done)) (fn-ptx-kd-commit (fn-ptx-kd (fn-rtc-mstate 1 s)) (fn-rtc-get 1 (fn-ptx-hs (fn-rtc-mstate 1 s))) (fn-ptx-elen (fn-rtc-mstate 1 s))) (fn-ptx-kd (fn-rtc-mstate 1 s)))) (ext (if (and (equal (fn-ptx-ph (fn-rtc-mstate 1 s)) :committing) (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done)) (fn-ptx-nxt (fn-rtc-mstate 1 s)) (fn-ptx-ext (fn-rtc-mstate 1 s)))) (o (if (and (equal (fn-ptx-ph (fn-rtc-mstate 1 s)) :committing) (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done)) :posted (if (member-eq (fn-ptx-ph (fn-rtc-mstate 1 s)) '(:extending :extsyncing)) :refused :uncertain)))
          (fenced (not (and (equal (fn-ptx-ph (fn-rtc-mstate 1 s)) :committing) (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done)))) (committed (and (equal (fn-ptx-ph (fn-rtc-mstate 1 s)) :committing) (equal (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done)))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-mstate-of-end-use fn-pth-i-kd-commit-last fn-ptx-expected
     fn-ptx-in-flight-p fn-ptx-accessors-of-mk member-equal nfix natp
     (:type-prescription fn-ptx-ext) (:type-prescription fn-ptx-nxt)
     (:executable-counterpart equal) (:executable-counterpart member-equal)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))

(defthm fn-pth-i-direct-owner-completion-is-expected
 (let ((m (fn-rtc-mstate 1 s)))
  (implies (and (fn-pth-i s) (fn-rtc-acts-on-p s e) (equal (fn-rtc-e-id e) 1)
                (not (equal (fn-rtc-e-kind e) :hand))
                (not (and (equal (fn-ptx-ph m) :closed) (equal (fn-rtc-e-kind e) :opened))))
           (and (fn-ptx-expected m) (equal (fn-rtc-e-kind e) (fn-ptx-expected m)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-runtime-and-post-state-by-definition
        (:instance fn-pth-i-post-storage-and-protocol-by-definition (m (fn-rtc-mstate 1 s)))
        fn-pth-i-direct-owner-completion
        (:instance fn-rtc-matching-use-fields (uses (fn-rtc-uses s)))
        (:instance fn-rtc-kind-out-of-found-use (key (fn-rtc-key e)) (uses (fn-rtc-uses s)))
        (:instance fn-pth-i-owner-kind-out-is-protocol-kind (m (fn-rtc-mstate 1 s))
          (kind (fn-rtc-e-kind e)) (inc 1) (uses (fn-rtc-uses s))))
  :in-theory (theory 'minimal-theory))))

(defthm fn-pth-i-owner-flight-end-step
 (let* ((m (fn-rtc-mstate 1 s)) (ph (fn-ptx-ph m))
        (out (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e))
        (tag (fn-rtc-get 0 out)) (n (fn-rtc-get 1 out)))
  (implies (and (fn-pth-i s) (fn-ptx-in-flight-p ph)
                (fn-rtc-acts-on-p s e) (equal (fn-rtc-e-id e) 1)
                (not (equal (fn-rtc-e-kind e) :hand))
                (or (and (member-eq ph '(:extending :extsyncing)) (not (equal tag :done)))
                    (and (member-eq ph '(:payload-writing :log-writing))
                         (not (and (equal tag :done) (equal n (fn-ptx-span-n (fn-ptx-k m) m)))))
                    (equal ph :committing)))
           (and (fn-pth-i (mv-nth 0 (fn-pth-step s e q)))
                (not (mv-nth 2 (fn-pth-step* s e q))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-runtime-and-post-state-by-definition fn-pth-i-direct-owner-completion
        fn-pth-i-direct-owner-completion-is-expected
        (:instance fn-pth-i-flight-end-host-delivery
          (ev (fn-rtc-ev (fn-rtc-e-kind e)
                (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e) 1 1 nil))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-step fn-pth-step* fn-pth-i-rearm fn-ptx-expected fn-ptx-in-flight-p member-equal
     fn-rtc-acts-on-p fn-rtc-hand-delivers-p fn-rtc-ev fn-rtc-ev-id fn-rtc-ev-inc fn-rtc-get-of-cons
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition car-cons cdr-cons
     (:executable-counterpart equal) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+))))))

(defthm fn-pth-i-owner-flight-step
 (implies (and (fn-pth-i s) (fn-ptx-in-flight-p (fn-ptx-ph (fn-rtc-mstate 1 s)))
               (fn-rtc-acts-on-p s e) (equal (fn-rtc-e-id e) 1)
               (not (equal (fn-rtc-e-kind e) :hand)))
          (and (fn-pth-i (mv-nth 0 (fn-pth-step s e q)))
               (not (mv-nth 2 (fn-pth-step* s e q)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :cases ((equal (fn-ptx-ph (fn-rtc-mstate 1 s)) :extending)
          (equal (fn-ptx-ph (fn-rtc-mstate 1 s)) :extsyncing)
          (equal (fn-ptx-ph (fn-rtc-mstate 1 s)) :payload-writing)
          (equal (fn-ptx-ph (fn-rtc-mstate 1 s)) :log-writing))
  :use (fn-pth-i-direct-owner-completion-is-expected fn-pth-i-owner-flight-end-step
        fn-pth-i-owner-extend-done-step fn-pth-i-owner-extsync-done-step
        fn-pth-i-owner-payload-done-step fn-pth-i-owner-log-done-step)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-ptx-in-flight-p fn-ptx-expected member-equal
     (:executable-counterpart equal) (:executable-counterpart member-equal))))))


; Reading: real free-home selection/admission and actual refusal completions.
(defthm fn-pth-i-free-view-is-real-home
 (implies (and (natp h) (equal (fn-rtc-st-v-owner h 1 1 s) '(:free)))
  (and (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:free))
       (equal (fn-rtc-home h (fn-rtc-config s)) 1)
       (equal (fn-ptx-gen h 1 1 s) (fn-rtc-b-gen (fn-rtc-buffer h s)))))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-st-v-owner fn-rtc-st$a-v-owner fn-ptx-gen fn-rtc-st-v-gen fn-rtc-st$a-v-gen
     fn-rtc-vb fn-rtc-view fn-rtc-c-get-of-view-pool fn-rtc-view-own-p fn-rtc-view-mine-p
     fn-rtc-buffer fn-rtc-buffer-accessors fn-rtc-get-of-cons
     nfix natp default-+-1 default-+-2 unicity-of-0 fix
     (:type-prescription fn-rtc-b-gen) car-cons cdr-cons
     (:executable-counterpart equal) (:executable-counterpart nfix)
     (:executable-counterpart zp) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart binary-+) (:executable-counterpart fn-rtc-b-owner))))))

(defthm fn-pth-i-free-selection-properties
 (let ((h (fn-ptx-free i skip 1 1 s)))
  (implies h
   (and (natp h) (< h (fn-rtc-nstatic-home (fn-rtc-config s)))
        (< h (fn-rtc-nbufs (fn-rtc-config s))) (not (equal h skip))
        (equal (fn-rtc-st-v-owner h 1 1 s) '(:free)))))
 :hints (("Goal" :induct (fn-ptx-free i skip 1 1 s)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-ptx-free fn-rtc-st-config fn-rtc-st$a-config min nfix natp
     default-+-1 default-+-2 unicity-of-0 fix
     (:type-prescription fn-rtc-nstatic-home) (:type-prescription fn-rtc-nbufs)
     (:type-prescription fn-ptx-free-natp-or-nil)
     (:executable-counterpart equal) (:executable-counterpart nfix)
     (:executable-counterpart zp) (:executable-counterpart binary-+))))))

(defthm fn-pth-i-free-selection-is-small-and-untracked
 (let ((h (fn-ptx-free i skip 1 1 s)))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s) h)
           (and (< h *fn-pth-qs*) (fn-pth-i-storage-avoids m h))))
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-free-selection-properties
        (:instance fn-pth-i-free-view-is-real-home (h (fn-ptx-free i skip 1 1 s)))
        (:instance fn-pth-i-storage-avoids-invisible (h (fn-ptx-free i skip 1 1 s))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-runtime fn-pth-i-visible-buffer (:executable-counterpart equal))))))

(defthm fn-pth-i-acquire-free-home
 (let ((r (list :acquire h)))
  (implies (and (fn-pth-i-runtime s) (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
                (equal (fn-rtc-home h (fn-rtc-config s)) 1)
                (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:free)))
           (and (not (mv-nth 2 (fn-rtc-request r 1 1 s)))
                (equal (mv-nth 0 (fn-rtc-request r 1 1 s))
                       (fn-rtc-with-buffer h (list (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h s))) '(:workspace 1 1) nil) s)))))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-runtime fn-rtc-request fn-rtc-req-acquire fn-rtc-live-p fn-rtc-current-p
     fn-rtc-s-inc fn-rtc-s-status fn-rtc-get-of-cons fn-hld-mv-nth-0-cons
     fn-pth-i-mv-nth-2-cons-by-definition nfix natp posp car-cons cdr-cons
     (:executable-counterpart equal) (:executable-counterpart nfix)
     (:executable-counterpart zp) (:executable-counterpart binary-+))))))

(defthm fn-pth-i-read-refusal-machine-results
 (let ((read (fn-ptx-read m q 1 1 s))
       (end (fn-ptx-end (fn-ptx-chg m :committed nil) :refused (fn-ptx-kd m) (fn-ptx-ext m) nil nil 1 1 s)))
  (implies (and (fn-ptx-okp m) (equal (fn-ptx-ph m) :reading)
                (not (equal (fn-ptx-ph (mv-nth 0 read)) :hashing)))
           (and (equal (mv-nth 0 read) (mv-nth 0 end))
                (equal (mv-nth 1 read) (mv-nth 1 end))
                (fn-ptx-okp (mv-nth 0 end)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-ptx-read-ok (id 1) (inc 1) (st s)))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-ptx-read fn-ptx-accessors-of-mk fn-hld-mv-nth-0-cons
     fn-pth-i-mv-nth-1-cons-by-definition car-cons cdr-cons
     (:executable-counterpart equal))))))

(defthm fn-pth-i-read-refusal-host-delivery
 (let ((m (fn-rtc-mstate 1 s)))
  (implies (and (fn-pth-i s) (equal (fn-ptx-ph m) :reading)
                (fn-rtc-completionp e) (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))
                (equal (fn-rtc-e-id e) 1) (equal (fn-rtc-e-inc e) 1) (equal (fn-rtc-e-kind e) :timer)
                (equal (fn-rtc-ev-id ev) 1) (equal (fn-rtc-ev-inc ev) 1) (equal (fn-rtc-get 0 ev) :timer)
                (not (equal (fn-ptx-ph (mv-nth 0 (fn-ptx-read m (nfix q) 1 1 (fn-rtc-end-use s e)))) :hashing)))
           (and (fn-pth-i (mv-nth 0 (fn-pth-deliver (fn-rtc-end-use s e) 1 1 ev q)))
                (not (mv-nth 2 (fn-pth-deliver (fn-rtc-end-use s e) 1 1 ev q))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-before-machine-after-end-use
        (:instance fn-pth-i-owner-protocol-after-expected-completion (m2 nil))
        (:instance fn-pth-i-post-storage-machine-facts (m (fn-rtc-mstate 1 s)) (s (fn-rtc-end-use s e)))
        (:instance fn-pth-i-post-storage-chain-and-extents (m (fn-rtc-mstate 1 s)) (s (fn-rtc-end-use s e)))
        (:instance fn-pth-i-post-storage-m0 (m (fn-rtc-mstate 1 s)) (s (fn-rtc-end-use s e)))
        (:instance fn-pth-i-read-refusal-machine-results (m (fn-rtc-mstate 1 s)) (s (fn-rtc-end-use s e)) (q (nfix q)))
        (:instance fn-pth-i-owner-end-deliver (s (fn-rtc-end-use s e)) (o :refused)
          (kd (fn-ptx-kd (fn-rtc-mstate 1 s))) (ext (fn-ptx-ext (fn-rtc-mstate 1 s))) (fenced nil) (committed nil)))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-mstate-of-end-use fn-ptx-expected fn-ptx-accessors-of-mk
     fn-ptx-step fn-ptx-step1 fn-ptx-okp-wfp fn-hld-mv-nth-0-cons
     fn-pth-i-mv-nth-1-cons-by-definition car-cons cdr-cons nfix natp
     (:type-prescription fn-ptx-ext) (:executable-counterpart equal)
     (:executable-counterpart member-equal) (:executable-counterpart nfix) (:executable-counterpart zp))))))

(defthm fn-pth-i-owner-read-refusal-step
 (let ((m (fn-rtc-mstate 1 s)))
  (implies (and (fn-pth-i s) (equal (fn-ptx-ph m) :reading)
                (fn-rtc-acts-on-p s e) (equal (fn-rtc-e-id e) 1)
                (not (equal (fn-rtc-e-kind e) :hand))
                (not (equal (fn-ptx-ph (mv-nth 0 (fn-ptx-read m (nfix q) 1 1 (fn-rtc-end-use s e)))) :hashing)))
           (and (fn-pth-i (mv-nth 0 (fn-pth-step s e q)))
                (not (mv-nth 2 (fn-pth-step* s e q))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-runtime-and-post-state-by-definition fn-pth-i-direct-owner-completion
        fn-pth-i-direct-owner-completion-is-expected
        (:instance fn-pth-i-read-refusal-host-delivery
          (ev (fn-rtc-ev :timer
                (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e) 1 1 nil))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-step fn-pth-step* fn-pth-i-rearm fn-ptx-expected
     fn-rtc-acts-on-p fn-rtc-hand-delivers-p fn-rtc-ev fn-rtc-ev-id fn-rtc-ev-inc fn-rtc-get-of-cons
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition car-cons cdr-cons
     (:executable-counterpart equal) (:executable-counterpart fn-rtc-get) (:executable-counterpart member-equal)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+))))))


; Read setup: typed request effects and composition through two owner homes.
(defthm fn-pth-i-member-append-used
 (iff (member-equal a (append x y))
      (or (member-equal a x) (member-equal a y)))
 :hints (("Goal" :induct (binary-append x y)
  :in-theory (union-theories (theory 'minimal-theory)
   '(binary-append member-equal car-cons cdr-cons)))))

(defthm fn-pth-i-queue-grow-used
 (implies (and (fn-pth-i-queue ps s used) (fn-pth-i-queue-avoids ps h))
          (fn-pth-i-queue ps s (append used (list h))))
 :hints (("Goal" :induct (fn-pth-i-queue ps s used)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-queue fn-pth-i-queue-avoids fn-pth-i-member-append-used
     binary-append member-equal car-cons cdr-cons)))))

(defthm fn-pth-i-append-nil-for-true-lists
 (implies (true-listp x) (equal (append x nil) x))
 :hints (("Goal" :induct (true-listp x)
  :in-theory (union-theories (theory 'minimal-theory) '(true-listp binary-append car-cons cdr-cons)))))

(defthm fn-pth-i-splice-empty-is-data
 (implies (fn-cbor-octet-listp data) (equal (fn-rtc-splice nil 0 data) data))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-cbor-octet-listp-implies-true-listp (xs data)))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-splice fn-rtc-true-list-fix-identity fn-pth-i-append-nil-for-true-lists
     fn-rtc-c-nthcdr-past-len binary-append nfix natp
     (:type-prescription len) (:executable-counterpart min) (:executable-counterpart len)
     (:executable-counterpart true-listp) (:executable-counterpart true-list-fix)
     (:executable-counterpart take) (:executable-counterpart nfix)
     (:executable-counterpart binary-+) (:executable-counterpart equal))))))

(defthm fn-pth-i-fill-empty-workspace
 (let ((r (list :write h g 0 data)))
  (implies (and (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
                (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:workspace 1 1))
                (equal (fn-rtc-b-gen (fn-rtc-buffer h s)) g)
                (not (fn-rtc-b-bytes (fn-rtc-buffer h s)))
                (fn-cbor-octet-listp data) (<= (len data) (fn-rtc-buf-cap h (fn-rtc-config s))))
           (and (not (mv-nth 2 (fn-rtc-request r 1 1 s)))
                (equal (mv-nth 0 (fn-rtc-request r 1 1 s))
                       (fn-rtc-with-buffer h (list g '(:workspace 1 1) data) s)))))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-request fn-rtc-req-write fn-pth-i-splice-empty-is-data fn-rtc-get-of-cons
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition nfix natp car-cons cdr-cons
     default-+-1 default-+-2 unicity-of-0 fix
     (:type-prescription len)
     (:executable-counterpart equal) (:executable-counterpart nfix)
     (:executable-counterpart zp) (:executable-counterpart len) (:executable-counterpart binary-+))))))

(defthm fn-pth-i-acquire-home-components
 (let* ((r (list :acquire h)) (s2 (mv-nth 0 (fn-rtc-request r 1 1 s))))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s) (fn-pth-i-storage-avoids m h)
                (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
                (equal (fn-rtc-home h (fn-rtc-config s)) 1)
                (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:free)))
           (and (fn-pth-i-runtime s2) (fn-pth-i-post-storage m s2)
                (equal s2 (fn-rtc-with-buffer h (list (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h s))) '(:workspace 1 1) nil) s))
                (equal (fn-rtc-uses s2) (fn-rtc-uses s))
                (not (mv-nth 2 (fn-rtc-request r 1 1 s))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-acquire-free-home
        (:instance fn-pth-i-runtime-request (r (list :acquire h)) (id 1) (inc 1))
        (:instance fn-pth-i-post-storage-untracked-request (r (list :acquire h))))
  :in-theory (union-theories (theory 'minimal-theory)
   '((:type-prescription fn-rtc-request) (:type-prescription fn-rtc-with-buffer) fn-rtc-with-accessors fn-rtc-get-of-cons car-cons cdr-cons nfix natp
     (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
     (:executable-counterpart nfix) (:executable-counterpart zp)
     (:executable-counterpart binary-+) (:executable-counterpart member-equal))))))

(defthm fn-pth-i-fill-home-components
 (let* ((r (list :write h g 0 data)) (s2 (mv-nth 0 (fn-rtc-request r 1 1 s))))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s) (fn-pth-i-storage-avoids m h)
                (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
                (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:workspace 1 1))
                (equal (fn-rtc-b-gen (fn-rtc-buffer h s)) g)
                (not (fn-rtc-b-bytes (fn-rtc-buffer h s)))
                (fn-cbor-octet-listp data) (<= (len data) (fn-rtc-buf-cap h (fn-rtc-config s))))
           (and (fn-pth-i-runtime s2) (fn-pth-i-post-storage m s2)
                (equal s2 (fn-rtc-with-buffer h (list g '(:workspace 1 1) data) s))
                (equal (fn-rtc-uses s2) (fn-rtc-uses s))
                (not (mv-nth 2 (fn-rtc-request r 1 1 s))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-fill-empty-workspace
        (:instance fn-pth-i-runtime-request (r (list :write h g 0 data)) (id 1) (inc 1))
        (:instance fn-pth-i-post-storage-untracked-request (r (list :write h g 0 data))))
  :in-theory (union-theories (theory 'minimal-theory)
   '((:type-prescription fn-rtc-request) (:type-prescription fn-rtc-with-buffer) fn-rtc-with-accessors fn-rtc-get-of-cons car-cons cdr-cons nfix natp
     (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
     (:executable-counterpart nfix) (:executable-counterpart zp)
     (:executable-counterpart binary-+) (:executable-counterpart member-equal))))))

(defthm fn-pth-i-buffer-of-acquire-home
 (implies (and (fn-pth-i-runtime s) (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
               (equal (fn-rtc-home h (fn-rtc-config s)) 1)
               (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:free)))
  (equal (fn-rtc-buffer j (mv-nth 0 (fn-rtc-request (list :acquire h) 1 1 s)))
         (if (equal (nfix j) h)
             (list (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h s))) '(:workspace 1 1) nil)
           (fn-rtc-buffer j s))))
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-acquire-free-home fn-pth-i-runtime-shape-by-definition
        (:instance fn-rtc-buffer-of-with (h j) (k h)
          (b (list (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h s))) '(:workspace 1 1) nil))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-shapep nfix natp (:type-prescription fn-rtc-request)
     (:executable-counterpart equal))))))

(defthm fn-pth-i-buffer-of-fill-home
 (implies (and (fn-pth-i-runtime s) (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
               (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:workspace 1 1))
               (equal (fn-rtc-b-gen (fn-rtc-buffer h s)) g)
               (not (fn-rtc-b-bytes (fn-rtc-buffer h s)))
               (fn-cbor-octet-listp data) (<= (len data) (fn-rtc-buf-cap h (fn-rtc-config s))))
  (equal (fn-rtc-buffer j (mv-nth 0 (fn-rtc-request (list :write h g 0 data) 1 1 s)))
         (if (equal (nfix j) h) (list g '(:workspace 1 1) data) (fn-rtc-buffer j s))))
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-fill-empty-workspace fn-pth-i-runtime-shape-by-definition
        (:instance fn-rtc-buffer-of-with (h j) (k h) (b (list g '(:workspace 1 1) data))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-shapep nfix natp (:type-prescription fn-rtc-request)
     (:executable-counterpart equal))))))

(defthm fn-pth-i-runtime-pool-length-by-definition
 (implies (fn-pth-i-runtime s)
          (equal (len (fn-rtc-pool s)) (fn-rtc-nbufs (fn-rtc-config s))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-runtime fn-rtc-shapep)))))

(defthm fn-pth-i-acquire-two-homes
 (let* ((g1 (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h1 s)))) (g3 (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h3 s))))
   (rs (list (list :acquire h1) (list :acquire h3))) (s2 (mv-nth 0 (fn-rtc-requests rs 1 1 s))))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s) (fn-pth-i-owner-uses (fn-rtc-uses s) m)
    (fn-pth-i-storage-avoids m h1) (fn-pth-i-storage-avoids m h3)
    (natp h1) (natp h3) (not (equal h1 h3))
    (< h1 (fn-rtc-nbufs (fn-rtc-config s))) (< h3 (fn-rtc-nbufs (fn-rtc-config s)))
    (equal (fn-rtc-home h1 (fn-rtc-config s)) 1) (equal (fn-rtc-home h3 (fn-rtc-config s)) 1)
    (equal (fn-rtc-b-owner (fn-rtc-buffer h1 s)) '(:free)) (equal (fn-rtc-b-owner (fn-rtc-buffer h3 s)) '(:free)))
   (and (fn-pth-i-runtime s2) (fn-pth-i-post-storage m s2)
    (equal (fn-rtc-buffer h1 s2) (list g1 '(:workspace 1 1) nil))
    (equal (fn-rtc-buffer h3 s2) (list g3 '(:workspace 1 1) nil))
    (equal (fn-rtc-uses s2) (fn-rtc-uses s))
    (not (mv-nth 2 (fn-rtc-requests rs 1 1 s))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :do-not '(preprocess)
  :use ((:instance fn-pth-i-acquire-home-components (h h1)) (:instance fn-pth-i-acquire-home-components (h h3) (s (mv-nth 0 (fn-rtc-request (list :acquire h1) 1 1 s)))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-runtime-pool-length-by-definition fn-rtc-len-of-set fn-pth-i-buffer-of-acquire-home fn-pth-i-buffer-of-fill-home fn-rtc-request-config-frame fn-rtc-requests fn-rtc-with-accessors fn-rtc-buffer-of-with fn-rtc-buffer-accessors fn-rtc-get-of-cons
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition binary-append member-equal car-cons cdr-cons
     nfix natp default-+-1 default-+-2 unicity-of-0 fix
     (:type-prescription fn-rtc-b-gen) (:type-prescription len)
     (:type-prescription fn-rtc-request) (:type-prescription fn-rtc-requests)
     (:executable-counterpart equal) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+)
     (:executable-counterpart member-equal))))))

(defthm fn-pth-i-fill-two-homes
 (let* (
   (rs (list (list :write h1 g1 0 data1) (list :write h3 g3 0 data3))) (s2 (mv-nth 0 (fn-rtc-requests rs 1 1 s))))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s) (fn-pth-i-owner-uses (fn-rtc-uses s) m)
    (fn-pth-i-storage-avoids m h1) (fn-pth-i-storage-avoids m h3)
    (natp h1) (natp h3) (not (equal h1 h3))
    (< h1 (fn-rtc-nbufs (fn-rtc-config s))) (< h3 (fn-rtc-nbufs (fn-rtc-config s)))
    (equal (fn-rtc-b-owner (fn-rtc-buffer h1 s)) '(:workspace 1 1)) (equal (fn-rtc-b-owner (fn-rtc-buffer h3 s)) '(:workspace 1 1))
    (equal (fn-rtc-b-gen (fn-rtc-buffer h1 s)) g1) (equal (fn-rtc-b-gen (fn-rtc-buffer h3 s)) g3)
    (not (fn-rtc-b-bytes (fn-rtc-buffer h1 s))) (not (fn-rtc-b-bytes (fn-rtc-buffer h3 s)))
    (fn-cbor-octet-listp data1) (fn-cbor-octet-listp data3)
    (<= (len data1) (fn-rtc-buf-cap h1 (fn-rtc-config s))) (<= (len data3) (fn-rtc-buf-cap h3 (fn-rtc-config s))))
   (and (fn-pth-i-runtime s2) (fn-pth-i-post-storage m s2)
    (equal (fn-rtc-buffer h1 s2) (list g1 '(:workspace 1 1) data1))
    (equal (fn-rtc-buffer h3 s2) (list g3 '(:workspace 1 1) data3))
    (equal (fn-rtc-uses s2) (fn-rtc-uses s))
    (not (mv-nth 2 (fn-rtc-requests rs 1 1 s))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :do-not '(preprocess)
  :use ((:instance fn-pth-i-fill-home-components (h h1) (g g1) (data data1)) (:instance fn-pth-i-fill-home-components (h h3) (g g3) (data data3) (s (mv-nth 0 (fn-rtc-request (list :write h1 g1 0 data1) 1 1 s)))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-runtime-pool-length-by-definition fn-rtc-len-of-set fn-pth-i-buffer-of-acquire-home fn-pth-i-buffer-of-fill-home fn-rtc-request-config-frame fn-rtc-requests fn-rtc-with-accessors fn-rtc-buffer-of-with fn-rtc-buffer-accessors fn-rtc-get-of-cons
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition binary-append member-equal car-cons cdr-cons
     nfix natp default-+-1 default-+-2 unicity-of-0 fix
     (:type-prescription fn-rtc-b-gen) (:type-prescription len)
     (:type-prescription fn-rtc-request) (:type-prescription fn-rtc-requests)
     (:executable-counterpart equal) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+)
     (:executable-counterpart member-equal))))))

(defthm fn-pth-i-acquire-fill-two-homes
 (let* ((g1 (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h1 s))))
        (g3 (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h3 s))))
        (rs (list (list :acquire h1) (list :acquire h3)
                  (list :write h1 g1 0 data1) (list :write h3 g3 0 data3)))
        (s2 (mv-nth 0 (fn-rtc-requests rs 1 1 s))))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s)
                (fn-pth-i-owner-uses (fn-rtc-uses s) m)
                (fn-pth-i-storage-avoids m h1) (fn-pth-i-storage-avoids m h3)
                (natp h1) (natp h3) (not (equal h1 h3))
                (< h1 (fn-rtc-nbufs (fn-rtc-config s))) (< h3 (fn-rtc-nbufs (fn-rtc-config s)))
                (equal (fn-rtc-home h1 (fn-rtc-config s)) 1) (equal (fn-rtc-home h3 (fn-rtc-config s)) 1)
                (equal (fn-rtc-b-owner (fn-rtc-buffer h1 s)) '(:free))
                (equal (fn-rtc-b-owner (fn-rtc-buffer h3 s)) '(:free))
                (fn-cbor-octet-listp data1) (fn-cbor-octet-listp data3)
                (<= (len data1) (fn-rtc-buf-cap h1 (fn-rtc-config s)))
                (<= (len data3) (fn-rtc-buf-cap h3 (fn-rtc-config s))))
           (and (fn-pth-i-runtime s2) (fn-pth-i-post-storage m s2)
                (equal (fn-rtc-buffer h1 s2) (list g1 '(:workspace 1 1) data1))
                (equal (fn-rtc-buffer h3 s2) (list g3 '(:workspace 1 1) data3))
                (equal (fn-rtc-uses s2) (fn-rtc-uses s))
                (not (mv-nth 2 (fn-rtc-requests rs 1 1 s))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-pth-i-acquire-two-homes)
       (:instance fn-pth-i-fill-two-homes (s (mv-nth 0 (fn-rtc-requests (list (list :acquire h1) (list :acquire h3)) 1 1 s))) (g1 (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h1 s)))) (g3 (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h3 s)))))
       (:instance fn-pth-i-requests-append-state (rs (list (list :acquire h1) (list :acquire h3))) (tail (list (list :write h1 (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h1 s))) 0 data1) (list :write h3 (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h3 s))) 0 data3))) (id 1) (inc 1))
       (:instance fn-pth-i-requests-append-refused (rs (list (list :acquire h1) (list :acquire h3))) (tail (list (list :write h1 (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h1 s))) 0 data1) (list :write h3 (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h3 s))) 0 data3))) (id 1) (inc 1)))
 :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '(fn-rtc-requests-config-frame fn-rtc-buffer-accessors fn-rtc-get-of-cons
    binary-append car-cons cdr-cons nfix natp default-+-1 default-+-2 unicity-of-0 fix
    (:type-prescription fn-rtc-requests) (:type-prescription fn-rtc-b-gen) (:type-prescription len)
    (:executable-counterpart equal) (:executable-counterpart fn-rtc-get)
    (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+))))))


; Present reading storage facts used by the successful read construction.
(defthm fn-pth-i-reading-storage-facts
 (implies (and (fn-pth-i-post-storage m s) (equal (fn-ptx-ph m) :reading))
  (and (not (fn-ptx-b1 m)) (not (fn-ptx-b3 m))
       (fn-pth-i-post (fn-ptx-cur m) s nil)
       (equal (len (fn-rtc-b-bytes (fn-rtc-buffer (fn-ptx-cur-bp (fn-ptx-cur m)) s)))
              (fn-ptx-cur-len (fn-ptx-cur m)))
       (fn-pth-i-queue (fn-ptx-q m) s (list (fn-ptx-cur-bp (fn-ptx-cur m))))
       (equal (len (fn-ptx-kd-last (fn-ptx-kd m))) 32)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-post-storage fn-ptx-okp fn-ptx-in-flight-p binary-append
     (:executable-counterpart equal) (:executable-counterpart member-equal)
     (:executable-counterpart consp) car-cons cdr-cons)))))


; Successful read: exact workspace bytes and hashing storage construction.

(defthm fn-pth-i-context-cat-is-append
 (equal (fn-pctx-cat x y) (append x y))
 :hints (("Goal" :induct (fn-pctx-cat x y)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pctx-cat binary-append car-cons cdr-cons)))))

(defthm fn-pth-i-frame-header-is-list
 (true-listp (fn-ptx-frame-header rlen))
 :hints (("Goal" :in-theory (enable fn-ptx-frame-header fn-frame-header fn-cbor-u32-bytes))))

(defthm fn-pth-i-read-prefix-bytes
 (implies (and (fn-cbor-octet-listp chain) (equal (len chain) 32))
  (equal (take (fn-ptx-head-len)
    (fn-pctx-cat (fn-pctx-cat (fn-ptx-frame-header rlen) (fn-pctx-cat chain pre)) ins))
   (append (fn-ptx-frame-header rlen) chain)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-cp-take-append-prefix
         (x (append (fn-ptx-frame-header rlen) chain))
         (y (append pre ins)))
        (:instance fn-cbor-octet-listp-implies-true-listp (xs chain)))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-context-cat-is-append fn-rtc-true-listp-append
     fn-ptx-frame-header-len fn-pth-i-frame-header-is-list
     fn-rtc-c-append-assoc fn-rtc-len-append fn-ptx-head-len-value
     (:executable-counterpart equal) (:executable-counterpart binary-+))))))

(defthm fn-pth-i-minus-minus-length
 (equal (- (- (len x))) (len x)))

(defthm fn-pth-i-buffer-tuple-bytes-by-definition
 (implies (equal b (list g o data)) (equal (fn-rtc-b-bytes b) data))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-buffer-accessors)))))

(defthm fn-pth-i-reading-to-hashing-storage
 (let* ((p (fn-ptx-cur m)) (kd (fn-ptx-kd m))
        (start (- *fn-ptx-sufhead-max* (len sh)))
        (end (+ *fn-ptx-sufhead-max* (len tail)))
        (rlen (+ (len pre) alen (len ins) (len sh) glen (len tail)))
        (data1 (fn-pctx-cat (fn-ptx-frame-header rlen) (fn-pctx-cat (fn-ptx-kd-last kd) pre)))
        (data3 (fn-pctx-cat (fn-bs-zeros start) (fn-pctx-cat sh tail)))
        (m2 (fn-ptx-chg m :committed nil :ph :hashing :k 0
               :cur (list (fn-ptx-cur-fid p) (fn-ptx-cur-finc p) (fn-ptx-cur-bp p)
                          alen 0 (fn-ptx-cur-txid p) ioff base glen)
               :b1 (list h1 g1 (len data1) (len ins))
               :b3 (list h3 g3 end start *fn-ptx-sufhead-max*) :hs (list 0 nil) :acc nil)))
  (implies (and (fn-pth-i-post-storage m s) (equal (fn-ptx-ph m) :reading)
                (fn-pth-i-storage-avoids m h1) (fn-pth-i-storage-avoids m h3)
                (natp alen) (natp base) (natp glen)
                (equal (fn-ptx-cur-len p) (+ base alen glen))
                (natp h1) (natp h3) (natp g1) (natp g3)
                (< h1 *fn-pth-qs*) (< h3 *fn-pth-qs*) (not (equal h1 h3))
                (< h1 (fn-rtc-nbufs (fn-rtc-config s))) (< h3 (fn-rtc-nbufs (fn-rtc-config s)))
                (equal (fn-rtc-buffer h1 s) (list g1 '(:workspace 1 1) (fn-pctx-cat data1 ins)))
                (equal (fn-rtc-buffer h3 s) (list g3 '(:workspace 1 1) data3))
                (<= (len sh) *fn-ptx-sufhead-max*)
                (<= (+ end 32) (fn-rtc-buf-cap h3 (fn-rtc-config s)))
                (fn-ptx-okp m2))
           (fn-pth-i-post-storage m2 s)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :expand ((:free (k cur ps kd ext nxt b1 b3 hs committed evd geo acc)
     (fn-pth-i-post-storage (fn-ptx-mk :hashing k cur ps kd ext nxt b1 b3 hs committed evd geo acc) s)))
  :use (fn-pth-i-reading-storage-facts fn-pth-i-post-storage-scalars
        (:instance fn-pth-i-buffer-tuple-bytes-by-definition (b (fn-rtc-buffer h1 s)) (g g1) (o '(:workspace 1 1))
         (data (fn-pctx-cat (fn-pctx-cat (fn-ptx-frame-header (+ (len pre) alen (len ins) (len sh) glen (len tail)))
                                 (fn-pctx-cat (fn-ptx-kd-last (fn-ptx-kd m)) pre)) ins)))
        (:instance fn-pth-i-read-prefix-bytes
         (chain (fn-ptx-kd-last (fn-ptx-kd m)))
         (rlen (+ (len pre) alen (len ins) (len sh) glen (len tail))))
        (:instance fn-pth-i-queue-grow-used (ps (fn-ptx-q m))
         (used (list (fn-ptx-cur-bp (fn-ptx-cur m)))) (h h1))
        (:instance fn-pth-i-queue-grow-used (ps (fn-ptx-q m))
         (used (list (fn-ptx-cur-bp (fn-ptx-cur m)) h1)) (h h3)))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-storage-avoids fn-pth-i-post fn-pth-i-visible-buffer
     fn-ptx-in-flight-p fn-ptx-accessors-of-mk fn-ptx-get-of-mk
     fn-ptx-cur-fid fn-ptx-cur-finc fn-ptx-cur-bp fn-ptx-cur-len fn-ptx-cur-base fn-ptx-cur-glen
     fn-ptx-buf-h fn-ptx-buf-g fn-ptx-buf-len fn-ptx-buf-x fn-ptx-buf-cut
     fn-ptx-nmsg-is-g fn-ptx-spans-len-g fn-pth-i-read-prefix-bytes fn-ptx-head-len-value
     fn-pth-i-context-cat-is-append fn-rtc-len-append fn-ptx-frame-header-len fn-ptx-zeros-len
     fn-rtc-buffer-accessors fn-rtc-get-of-cons binary-append min max fn-ptx-nfix-natp-rw fn-ptx-nfix-nfix natp
     (:type-prescription fn-ptx-ext) (:type-prescription fn-ptx-nxt)
     (:type-prescription fn-ptx-cur-bp) (:type-prescription fn-ptx-cur-len)
     (:type-prescription len) (:type-prescription nfix) car-cons cdr-cons
     associativity-of-+ commutativity-of-+ commutativity-2-of-+ fold-consts-in-+
     default-+-1 default-+-2 default-unary-minus distributivity-of-minus-over-+ fn-pth-i-minus-minus-length inverse-of-+ unicity-of-0 fix
     (:executable-counterpart equal) (:executable-counterpart binary-+)
     (:executable-counterpart unary--) (:executable-counterpart nfix)
     (:executable-counterpart member-equal) (:executable-counterpart consp)
     (:executable-counterpart fn-rtc-get) (:executable-counterpart zp))))))

(defthm fn-pth-i-read-header-octets
 (implies (<= (+ 32 (nfix rlen)) *fn-cbor-max-uint*)
  (fn-cbor-octet-listp (fn-ptx-frame-header rlen)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-frame-header-octets (magic *fn-lg-magic*) (version *fn-lg-version*)
          (kind *fn-lg-record-kind*) (length (+ 32 (nfix rlen)))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-ptx-frame-header (:type-prescription nfix) natp
     (:executable-counterpart fn-frame-magicp) (:executable-counterpart fn-cbor-octetp))))))

(defthm fn-pth-i-read-workspace-octets
 (implies (and (<= (+ 32 (nfix rlen)) *fn-cbor-max-uint*)
               (fn-cbor-octet-listp chain) (fn-cbor-octet-listp pre)
               (fn-cbor-octet-listp ins) (fn-cbor-octet-listp sh) (fn-cbor-octet-listp tail))
  (and (fn-cbor-octet-listp
         (fn-pctx-cat (fn-pctx-cat (fn-ptx-frame-header rlen) (fn-pctx-cat chain pre)) ins))
       (fn-cbor-octet-listp (fn-pctx-cat (fn-bs-zeros start) (fn-pctx-cat sh tail)))))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-read-header-octets fn-bs-zeros-are-octets fn-pth-i-context-cat-is-append
     fn-cbor-octet-listp-append fn-cbor-octet-listp-implies-true-listp fn-rtc-true-listp-append
     fn-pth-i-frame-header-is-list)))))

(defthm fn-pth-i-reading-success-by-definition
 (let* ( (p (fn-ptx-cur m))
 (kd (fn-ptx-kd m))
 (bp (fn-ptx-cur-bp p))
 (post-fill (fn-ptx-cur-len p))
 (d (fn-pctx-decode (fn-ptx-range bp 0 (min post-fill *fn-pctx-max*) 1 1 s)))
 (ctx (fn-pctx-get 1 d))
 (base (nfix (fn-pctx-get 2 d)))
 (glen (nfix (fn-pctx-get 6 ctx)))
 (alen (- post-fill (+ base glen)))
 (a (fn-ptx-acc-begin (list (fn-ptx-kd-txid kd) ctx)))
 (h1 (fn-ptx-free 0 nil 1 1 s))
 (h3 (fn-ptx-free 0 h1 1 1 s))
 (g1 (+ 1 (fn-ptx-gen h1 1 1 s)))
 (g3 (+ 1 (fn-ptx-gen h3 1 1 s)))
 (ok (mv-nth 0 (fn-ptx-acc-end a 0)))
 (pre (mv-nth 1 (fn-ptx-acc-end a 0)))
 (ins (mv-nth 2 (fn-ptx-acc-end a 0)))
 (ioff (if (consp ins) (nfix (mv-nth 3 (fn-ptx-acc-end a 0))) alen))
 (sh (mv-nth 4 (fn-ptx-acc-end a 0)))
 (tail (mv-nth 5 (fn-ptx-acc-end a 0)))
 (start (- *fn-ptx-sufhead-max* (min (len sh) *fn-ptx-sufhead-max*)))
 (end (+ *fn-ptx-sufhead-max* (len tail)))
 (rlen (+ (len pre) alen (len ins) (len sh) glen (len tail)))
 (data1 (fn-pctx-cat (fn-ptx-frame-header rlen) (fn-pctx-cat (fn-ptx-kd-last kd) pre)))
 (data3 (fn-pctx-cat (fn-bs-zeros start) (fn-pctx-cat sh tail)))
 (m2 (fn-ptx-chg m :committed nil :ph :hashing :k 0 :cur (list (fn-ptx-cur-fid p) (fn-ptx-cur-finc p) bp alen 0 (fn-ptx-cur-txid p) ioff base glen) :b1 (list h1 g1 (len data1) (len ins)) :b3 (list h3 g3 end start *fn-ptx-sufhead-max*) :hs (list 0 nil) :acc nil))
 (rs4 (list (list :acquire h1) (list :acquire h3) (list :write h1 g1 0 (fn-pctx-cat data1 ins)) (list :write h3 g3 0 data3)))
 (s4 (mv-nth 0 (fn-rtc-requests rs4 1 1 s))))
  (declare (ignorable s4))
  (implies (and (fn-pth-i-post-storage m s) (equal (fn-ptx-ph m) :reading)
    (equal (fn-ptx-ph (mv-nth 0 (fn-ptx-read m q 1 1 s))) :hashing))
   (and (fn-pctx-get 0 d) (equal post-fill (fn-rtc-st-v-fill bp 1 1 s))
    (<= (+ base glen) post-fill) h1 h3 ok (<= ioff alen)
    (<= (+ 32 rlen) (fn-ptx-fmax m))
    (<= (+ (len data1) (len ins)) (fn-ptx-cap h1 1 1 s))
    (<= (+ end 32) (fn-ptx-cap h3 1 1 s))
    (equal (mv-nth 0 (fn-ptx-read m q 1 1 s)) m2)
    (equal (mv-nth 1 (fn-ptx-read m q 1 1 s)) (append rs4 (list (fn-ptx-timer)))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-reading-storage-facts)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-ptx-read fn-ptx-accessors-of-mk fn-ptx-end-0 fn-ptx-start-0 fn-ptx-nfix-natp-rw
     (:type-prescription fn-ptx-ext) (:type-prescription fn-ptx-nxt)
     (:executable-counterpart nfix) (:executable-counterpart zp) natp
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-1-cons-by-definition binary-append
     car-cons cdr-cons (:executable-counterpart consp) (:executable-counterpart equal))))))

(defthm fn-pth-i-context-cat-length
 (equal (len (fn-pctx-cat x y)) (+ (len x) (len y)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-context-cat-is-append fn-rtc-len-append)))))

(defthm fn-pth-i-acceptance-end-octets
 (and (fn-cbor-octet-listp (mv-nth 1 (fn-ptx-acc-end a blen)))
      (fn-cbor-octet-listp (mv-nth 2 (fn-ptx-acc-end a blen)))
      (fn-cbor-octet-listp (mv-nth 4 (fn-ptx-acc-end a blen)))
      (fn-cbor-octet-listp (mv-nth 5 (fn-ptx-acc-end a blen)))
      (<= (len (mv-nth 4 (fn-ptx-acc-end a blen))) *fn-ptx-sufhead-max*))
 :hints (("Goal" :use (fn-ptx-acc-end-shape) :in-theory (theory 'minimal-theory))))


; Actual successful reading completion: allocation, timer and host composition.

(defthm fn-pth-i-post-storage-machine-fmax
 (implies (fn-pth-i-post-storage m s) (<= (fn-ptx-fmax m) *fn-frame-max-payload*))
 :rule-classes :linear
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-post-storage-machine-facts fn-ptx-okp-elim)))))

(defthm fn-pth-i-context-cat-octets
 (implies (and (fn-cbor-octet-listp x) (fn-cbor-octet-listp y))
  (fn-cbor-octet-listp (fn-pctx-cat x y)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-context-cat-is-append fn-cbor-octet-listp-append fn-cbor-octet-listp-implies-true-listp)))))

(defthm fn-pth-i-reading-success-home-facts
 (let* ( (p (fn-ptx-cur m))
 (kd (fn-ptx-kd m))
 (bp (fn-ptx-cur-bp p))
 (post-fill (fn-ptx-cur-len p))
 (d (fn-pctx-decode (fn-ptx-range bp 0 (min post-fill *fn-pctx-max*) 1 1 s)))
 (ctx (fn-pctx-get 1 d))
 (base (nfix (fn-pctx-get 2 d)))
 (glen (nfix (fn-pctx-get 6 ctx)))
 (alen (- post-fill (+ base glen)))
 (a (fn-ptx-acc-begin (list (fn-ptx-kd-txid kd) ctx)))
 (h1 (fn-ptx-free 0 nil 1 1 s))
 (h3 (fn-ptx-free 0 h1 1 1 s))
 (g1 (+ 1 (fn-ptx-gen h1 1 1 s)))
 (g3 (+ 1 (fn-ptx-gen h3 1 1 s)))
 (ok (mv-nth 0 (fn-ptx-acc-end a 0)))
 (pre (mv-nth 1 (fn-ptx-acc-end a 0)))
 (ins (mv-nth 2 (fn-ptx-acc-end a 0)))
 (ioff (if (consp ins) (nfix (mv-nth 3 (fn-ptx-acc-end a 0))) alen))
 (sh (mv-nth 4 (fn-ptx-acc-end a 0)))
 (tail (mv-nth 5 (fn-ptx-acc-end a 0)))
 (start (- *fn-ptx-sufhead-max* (min (len sh) *fn-ptx-sufhead-max*)))
 (end (+ *fn-ptx-sufhead-max* (len tail)))
 (rlen (+ (len pre) alen (len ins) (len sh) glen (len tail)))
 (data1 (fn-pctx-cat (fn-ptx-frame-header rlen) (fn-pctx-cat (fn-ptx-kd-last kd) pre)))
 (data3 (fn-pctx-cat (fn-bs-zeros start) (fn-pctx-cat sh tail)))
 (m2 (fn-ptx-chg m :committed nil :ph :hashing :k 0 :cur (list (fn-ptx-cur-fid p) (fn-ptx-cur-finc p) bp alen 0 (fn-ptx-cur-txid p) ioff base glen) :b1 (list h1 g1 (len data1) (len ins)) :b3 (list h3 g3 end start *fn-ptx-sufhead-max*) :hs (list 0 nil) :acc nil))
 (rs4 (list (list :acquire h1) (list :acquire h3) (list :write h1 g1 0 (fn-pctx-cat data1 ins)) (list :write h3 g3 0 data3)))
 (s4 (mv-nth 0 (fn-rtc-requests rs4 1 1 s))))
  (declare (ignorable s4 ok))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s)
    (equal (fn-ptx-ph m) :reading)
    (equal (fn-ptx-ph (mv-nth 0 (fn-ptx-read m q 1 1 s))) :hashing))
   (and (natp h1) (natp h3) (natp g1) (natp g3)
    (natp alen) (natp base) (natp glen)
    (equal post-fill (+ base alen glen))
    (< h1 *fn-pth-qs*) (< h3 *fn-pth-qs*) (not (equal h1 h3))
    (< h1 (fn-rtc-nbufs (fn-rtc-config s))) (< h3 (fn-rtc-nbufs (fn-rtc-config s)))
    (equal (fn-rtc-home h1 (fn-rtc-config s)) 1) (equal (fn-rtc-home h3 (fn-rtc-config s)) 1)
    (equal (fn-rtc-b-owner (fn-rtc-buffer h1 s)) '(:free))
    (equal (fn-rtc-b-owner (fn-rtc-buffer h3 s)) '(:free))
    (equal g1 (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h1 s))))
    (equal g3 (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h3 s))))
    (fn-pth-i-storage-avoids m h1) (fn-pth-i-storage-avoids m h3)
    (fn-cbor-octet-listp (fn-pctx-cat data1 ins)) (fn-cbor-octet-listp data3)
    (<= (len (fn-pctx-cat data1 ins)) (fn-rtc-buf-cap h1 (fn-rtc-config s)))
    (<= (len data3) (fn-rtc-buf-cap h3 (fn-rtc-config s)))
    (<= (len sh) *fn-ptx-sufhead-max*) (equal start (- *fn-ptx-sufhead-max* (len sh)))
    (<= (+ end 32) (fn-rtc-buf-cap h3 (fn-rtc-config s)))
    (fn-ptx-okp m2))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-reading-success-by-definition fn-pth-i-post-storage-machine-fmax
        (:instance fn-ptx-read-ok (id 1) (inc 1) (st s)))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-post-storage-machine-facts fn-pth-i-post-storage-chain-and-extents
     fn-pth-i-context-cat-octets fn-pth-i-read-header-octets fn-bs-zeros-are-octets
     fn-pth-i-free-selection-properties fn-pth-i-free-selection-is-small-and-untracked
     fn-pth-i-free-view-is-real-home fn-pth-i-acceptance-end-octets fn-ptx-acc-end-lens
     fn-ptx-cap fn-rtc-st-config fn-rtc-st$a-config
     fn-pth-i-context-cat-length fn-ptx-frame-header-len fn-ptx-zeros-len
     fn-ptx-nfix-natp-rw fn-ptx-nfix-nfix natp min
     (:type-prescription fn-ptx-cur-len) (:type-prescription fn-rtc-b-gen) (:type-prescription fn-ptx-read)
     (:type-prescription nfix) (:type-prescription len)
     associativity-of-+ commutativity-of-+ commutativity-2-of-+ fold-consts-in-+
     default-+-1 default-+-2 default-unary-minus distributivity-of-minus-over-+
     fn-pth-i-minus-minus-length inverse-of-+ unicity-of-0 fix
     (:executable-counterpart equal) (:executable-counterpart binary-+)
     (:executable-counterpart unary--) (:executable-counterpart nfix)
     (:executable-counterpart zp) (:executable-counterpart fn-ptx-ph))))))

(defthm fn-pth-i-view-state-with-mstate
 (equal (fn-rtc-view-state id inc (fn-rtc-with-mstate j m s)) (fn-rtc-view-state id inc s))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-rtc-view-state fn-rtc-view fn-rtc-with-accessors)))))

(defthm fn-pth-i-read-with-mstate
 (equal (fn-ptx-read old q id inc (fn-rtc-with-mstate j m s)) (fn-ptx-read old q id inc s))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-ptx-read-reads-view (m old) (st (fn-rtc-with-mstate j m s)))
        (:instance fn-ptx-read-reads-view (m old) (st s)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-pth-i-view-state-with-mstate)))))

(defthm fn-pth-i-acquire-fill-hashing-storage
 (let* ((g1 (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h1 s))))
        (g3 (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h3 s))))
        (p (fn-ptx-cur m)) (kd (fn-ptx-kd m))
        (start (- *fn-ptx-sufhead-max* (len sh)))
        (end (+ *fn-ptx-sufhead-max* (len tail)))
        (rlen (+ (len pre) alen (len ins) (len sh) glen (len tail)))
        (data1 (fn-pctx-cat (fn-ptx-frame-header rlen) (fn-pctx-cat (fn-ptx-kd-last kd) pre)))
        (data3 (fn-pctx-cat (fn-bs-zeros start) (fn-pctx-cat sh tail)))
        (m2 (fn-ptx-chg m :committed nil :ph :hashing :k 0
               :cur (list (fn-ptx-cur-fid p) (fn-ptx-cur-finc p) (fn-ptx-cur-bp p)
                          alen 0 (fn-ptx-cur-txid p) ioff base glen)
               :b1 (list h1 g1 (len data1) (len ins))
               :b3 (list h3 g3 end start *fn-ptx-sufhead-max*)  :hs (list 0 nil) :acc nil))
        (rs4 (list (list :acquire h1) (list :acquire h3)
          (list :write h1 g1 0 (fn-pctx-cat data1 ins)) (list :write h3 g3 0 data3)))
        (s4 (mv-nth 0 (fn-rtc-requests rs4 1 1 s))))
  (implies (and (fn-pth-i-post-storage m s) (fn-pth-i-runtime s)
                (fn-pth-i-owner-uses (fn-rtc-uses s) nil) (equal (fn-ptx-ph m) :reading)
                (fn-pth-i-storage-avoids m h1) (fn-pth-i-storage-avoids m h3)
                (natp alen) (natp base) (natp glen)
                (equal (fn-ptx-cur-len p) (+ base alen glen))
                (natp h1) (natp h3)
                (< h1 *fn-pth-qs*) (< h3 *fn-pth-qs*) (not (equal h1 h3))
                (< h1 (fn-rtc-nbufs (fn-rtc-config s))) (< h3 (fn-rtc-nbufs (fn-rtc-config s)))
                (equal (fn-rtc-home h1 (fn-rtc-config s)) 1) (equal (fn-rtc-home h3 (fn-rtc-config s)) 1)
                (equal (fn-rtc-b-owner (fn-rtc-buffer h1 s)) '(:free))
                (equal (fn-rtc-b-owner (fn-rtc-buffer h3 s)) '(:free))
                (fn-cbor-octet-listp (fn-pctx-cat data1 ins)) (fn-cbor-octet-listp data3)
                (<= (len (fn-pctx-cat data1 ins)) (fn-rtc-buf-cap h1 (fn-rtc-config s)))
                (<= (len data3) (fn-rtc-buf-cap h3 (fn-rtc-config s)))
                (<= (len sh) *fn-ptx-sufhead-max*)
                (<= (+ end 32) (fn-rtc-buf-cap h3 (fn-rtc-config s)))
                (fn-ptx-okp m2))
           (and (fn-pth-i-runtime s4) (fn-pth-i-post-storage m2 s4)
                (equal (fn-rtc-uses s4) (fn-rtc-uses s))
                (not (mv-nth 2 (fn-rtc-requests rs4 1 1 s))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-pth-i-acquire-fill-two-homes (data1 (fn-pctx-cat (fn-pctx-cat (fn-ptx-frame-header (+ (len pre) alen (len ins) (len sh) glen (len tail))) (fn-pctx-cat (fn-ptx-kd-last (fn-ptx-kd m)) pre)) ins)) (data3 (fn-pctx-cat (fn-bs-zeros (- *fn-ptx-sufhead-max* (len sh))) (fn-pctx-cat sh tail))))
       (:instance fn-pth-i-reading-to-hashing-storage (s (mv-nth 0 (fn-rtc-requests (list (list :acquire h1) (list :acquire h3) (list :write h1 (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h1 s))) 0 (fn-pctx-cat (fn-pctx-cat (fn-ptx-frame-header (+ (len pre) alen (len ins) (len sh) glen (len tail))) (fn-pctx-cat (fn-ptx-kd-last (fn-ptx-kd m)) pre)) ins)) (list :write h3 (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h3 s))) 0 (fn-pctx-cat (fn-bs-zeros (- *fn-ptx-sufhead-max* (len sh))) (fn-pctx-cat sh tail)))) 1 1 s))) (g1 (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h1 s)))) (g3 (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h3 s))))))
 :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '(fn-pth-i-hands-only-compatible-with-every-machine fn-rtc-requests-config-frame
    fn-ptx-nfix-natp-rw fn-ptx-nfix-nfix natp
    (:type-prescription fn-rtc-requests) (:type-prescription fn-rtc-b-gen) (:type-prescription len)
    (:executable-counterpart equal) (:executable-counterpart binary-+) (:executable-counterpart nfix) (:executable-counterpart zp))))))

(defthm fn-pth-i-reading-success-prefix
 (let* ( (p (fn-ptx-cur m))
 (kd (fn-ptx-kd m))
 (bp (fn-ptx-cur-bp p))
 (post-fill (fn-ptx-cur-len p))
 (d (fn-pctx-decode (fn-ptx-range bp 0 (min post-fill *fn-pctx-max*) 1 1 s)))
 (ctx (fn-pctx-get 1 d))
 (base (nfix (fn-pctx-get 2 d)))
 (glen (nfix (fn-pctx-get 6 ctx)))
 (alen (- post-fill (+ base glen)))
 (a (fn-ptx-acc-begin (list (fn-ptx-kd-txid kd) ctx)))
 (h1 (fn-ptx-free 0 nil 1 1 s))
 (h3 (fn-ptx-free 0 h1 1 1 s))
 (g1 (+ 1 (fn-ptx-gen h1 1 1 s)))
 (g3 (+ 1 (fn-ptx-gen h3 1 1 s)))
 (ok (mv-nth 0 (fn-ptx-acc-end a 0)))
 (pre (mv-nth 1 (fn-ptx-acc-end a 0)))
 (ins (mv-nth 2 (fn-ptx-acc-end a 0)))
 (ioff (if (consp ins) (nfix (mv-nth 3 (fn-ptx-acc-end a 0))) alen))
 (sh (mv-nth 4 (fn-ptx-acc-end a 0)))
 (tail (mv-nth 5 (fn-ptx-acc-end a 0)))
 (start (- *fn-ptx-sufhead-max* (min (len sh) *fn-ptx-sufhead-max*)))
 (end (+ *fn-ptx-sufhead-max* (len tail)))
 (rlen (+ (len pre) alen (len ins) (len sh) glen (len tail)))
 (data1 (fn-pctx-cat (fn-ptx-frame-header rlen) (fn-pctx-cat (fn-ptx-kd-last kd) pre)))
 (data3 (fn-pctx-cat (fn-bs-zeros start) (fn-pctx-cat sh tail)))
 (m2 (fn-ptx-chg m :committed nil :ph :hashing :k 0 :cur (list (fn-ptx-cur-fid p) (fn-ptx-cur-finc p) bp alen 0 (fn-ptx-cur-txid p) ioff base glen) :b1 (list h1 g1 (len data1) (len ins)) :b3 (list h3 g3 end start *fn-ptx-sufhead-max*) :hs (list 0 nil) :acc nil))
 (rs4 (list (list :acquire h1) (list :acquire h3) (list :write h1 g1 0 (fn-pctx-cat data1 ins)) (list :write h3 g3 0 data3)))
 (s4 (mv-nth 0 (fn-rtc-requests rs4 1 1 s))))
  (declare (ignorable ok))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s)
    (fn-pth-i-owner-uses (fn-rtc-uses s) nil)
    (equal (fn-ptx-ph m) :reading)
    (equal (fn-ptx-ph (mv-nth 0 (fn-ptx-read m q 1 1 s))) :hashing))
   (and (fn-pth-i-runtime s4) (fn-pth-i-post-storage m2 s4)
    (fn-pth-i-owner-uses (fn-rtc-uses s4) nil)
    (not (mv-nth 2 (fn-rtc-requests rs4 1 1 s))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-reading-success-home-facts
    (:instance fn-pth-i-acquire-fill-hashing-storage (h1 (fn-ptx-free 0 nil 1 1 s)) (h3 (fn-ptx-free 0 (fn-ptx-free 0 nil 1 1 s) 1 1 s)) (alen (- (fn-ptx-cur-len (fn-ptx-cur m)) (+ (nfix (fn-pctx-get 2 (fn-pctx-decode (fn-ptx-range (fn-ptx-cur-bp (fn-ptx-cur m)) 0 (min (fn-ptx-cur-len (fn-ptx-cur m)) *fn-pctx-max*) 1 1 s)))) (nfix (fn-pctx-get 6 (fn-pctx-get 1 (fn-pctx-decode (fn-ptx-range (fn-ptx-cur-bp (fn-ptx-cur m)) 0 (min (fn-ptx-cur-len (fn-ptx-cur m)) *fn-pctx-max*) 1 1 s)))))))) (base (nfix (fn-pctx-get 2 (fn-pctx-decode (fn-ptx-range (fn-ptx-cur-bp (fn-ptx-cur m)) 0 (min (fn-ptx-cur-len (fn-ptx-cur m)) *fn-pctx-max*) 1 1 s))))) (glen (nfix (fn-pctx-get 6 (fn-pctx-get 1 (fn-pctx-decode (fn-ptx-range (fn-ptx-cur-bp (fn-ptx-cur m)) 0 (min (fn-ptx-cur-len (fn-ptx-cur m)) *fn-pctx-max*) 1 1 s)))))) (ioff (if (consp (mv-nth 2 (fn-ptx-acc-end (fn-ptx-acc-begin (list (fn-ptx-kd-txid (fn-ptx-kd m)) (fn-pctx-get 1 (fn-pctx-decode (fn-ptx-range (fn-ptx-cur-bp (fn-ptx-cur m)) 0 (min (fn-ptx-cur-len (fn-ptx-cur m)) *fn-pctx-max*) 1 1 s))))) 0))) (nfix (mv-nth 3 (fn-ptx-acc-end (fn-ptx-acc-begin (list (fn-ptx-kd-txid (fn-ptx-kd m)) (fn-pctx-get 1 (fn-pctx-decode (fn-ptx-range (fn-ptx-cur-bp (fn-ptx-cur m)) 0 (min (fn-ptx-cur-len (fn-ptx-cur m)) *fn-pctx-max*) 1 1 s))))) 0))) (- (fn-ptx-cur-len (fn-ptx-cur m)) (+ (nfix (fn-pctx-get 2 (fn-pctx-decode (fn-ptx-range (fn-ptx-cur-bp (fn-ptx-cur m)) 0 (min (fn-ptx-cur-len (fn-ptx-cur m)) *fn-pctx-max*) 1 1 s)))) (nfix (fn-pctx-get 6 (fn-pctx-get 1 (fn-pctx-decode (fn-ptx-range (fn-ptx-cur-bp (fn-ptx-cur m)) 0 (min (fn-ptx-cur-len (fn-ptx-cur m)) *fn-pctx-max*) 1 1 s))))))))) (pre (mv-nth 1 (fn-ptx-acc-end (fn-ptx-acc-begin (list (fn-ptx-kd-txid (fn-ptx-kd m)) (fn-pctx-get 1 (fn-pctx-decode (fn-ptx-range (fn-ptx-cur-bp (fn-ptx-cur m)) 0 (min (fn-ptx-cur-len (fn-ptx-cur m)) *fn-pctx-max*) 1 1 s))))) 0))) (ins (mv-nth 2 (fn-ptx-acc-end (fn-ptx-acc-begin (list (fn-ptx-kd-txid (fn-ptx-kd m)) (fn-pctx-get 1 (fn-pctx-decode (fn-ptx-range (fn-ptx-cur-bp (fn-ptx-cur m)) 0 (min (fn-ptx-cur-len (fn-ptx-cur m)) *fn-pctx-max*) 1 1 s))))) 0))) (sh (mv-nth 4 (fn-ptx-acc-end (fn-ptx-acc-begin (list (fn-ptx-kd-txid (fn-ptx-kd m)) (fn-pctx-get 1 (fn-pctx-decode (fn-ptx-range (fn-ptx-cur-bp (fn-ptx-cur m)) 0 (min (fn-ptx-cur-len (fn-ptx-cur m)) *fn-pctx-max*) 1 1 s))))) 0))) (tail (mv-nth 5 (fn-ptx-acc-end (fn-ptx-acc-begin (list (fn-ptx-kd-txid (fn-ptx-kd m)) (fn-pctx-get 1 (fn-pctx-decode (fn-ptx-range (fn-ptx-cur-bp (fn-ptx-cur m)) 0 (min (fn-ptx-cur-len (fn-ptx-cur m)) *fn-pctx-max*) 1 1 s))))) 0)))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-hands-only-compatible-with-every-machine fn-rtc-requests-config-frame
     fn-ptx-nfix-natp-rw fn-ptx-nfix-nfix natp
     fn-rtc-buffer-accessors fn-rtc-get-of-cons fn-ptx-cap fn-rtc-st-config fn-rtc-st$a-config
     (:type-prescription fn-rtc-requests) (:type-prescription len) (:type-prescription nfix)
     car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart binary-+)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))

(defthm fn-pth-i-timer-after-prefix
 (let* ((s4 (mv-nth 0 (fn-rtc-requests rs 1 1 s)))
        (s5 (mv-nth 0 (fn-rtc-requests (append rs (list (fn-ptx-timer))) 1 1 s))))
  (implies (and (fn-pth-i-runtime s4) (fn-pth-i-post-storage m s4)
                (fn-pth-i-owner-uses (fn-rtc-uses s4) nil)
                (equal (fn-ptx-expected m) :timer) (equal (fn-rtc-mstate 1 s) m)
                (not (mv-nth 2 (fn-rtc-requests rs 1 1 s))))
   (and (fn-pth-i s5)
        (not (mv-nth 2 (fn-rtc-requests (append rs (list (fn-ptx-timer))) 1 1 s))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-pth-i-timer-restores-post-state (s (mv-nth 0 (fn-rtc-requests rs 1 1 s))))
        (:instance fn-pth-i-runtime-and-post-state-by-definition
         (s (mv-nth 0 (fn-rtc-requests (append rs (list (fn-ptx-timer))) 1 1 s)))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-requests-append-state fn-pth-i-requests-append-refused fn-rtc-requests-keeps-mstates
     binary-append (:type-prescription fn-rtc-requests))))))

(defthm fn-pth-i-reading-success-result-by-definition
 (let* ( (p (fn-ptx-cur m))
 (kd (fn-ptx-kd m))
 (bp (fn-ptx-cur-bp p))
 (post-fill (fn-ptx-cur-len p))
 (d (fn-pctx-decode (fn-ptx-range bp 0 (min post-fill *fn-pctx-max*) 1 1 s)))
 (ctx (fn-pctx-get 1 d))
 (base (nfix (fn-pctx-get 2 d)))
 (glen (nfix (fn-pctx-get 6 ctx)))
 (alen (- post-fill (+ base glen)))
 (a (fn-ptx-acc-begin (list (fn-ptx-kd-txid kd) ctx)))
 (h1 (fn-ptx-free 0 nil 1 1 s))
 (h3 (fn-ptx-free 0 h1 1 1 s))
 (g1 (+ 1 (fn-ptx-gen h1 1 1 s)))
 (g3 (+ 1 (fn-ptx-gen h3 1 1 s)))
 (ok (mv-nth 0 (fn-ptx-acc-end a 0)))
 (pre (mv-nth 1 (fn-ptx-acc-end a 0)))
 (ins (mv-nth 2 (fn-ptx-acc-end a 0)))
 (ioff (if (consp ins) (nfix (mv-nth 3 (fn-ptx-acc-end a 0))) alen))
 (sh (mv-nth 4 (fn-ptx-acc-end a 0)))
 (tail (mv-nth 5 (fn-ptx-acc-end a 0)))
 (start (- *fn-ptx-sufhead-max* (min (len sh) *fn-ptx-sufhead-max*)))
 (end (+ *fn-ptx-sufhead-max* (len tail)))
 (rlen (+ (len pre) alen (len ins) (len sh) glen (len tail)))
 (data1 (fn-pctx-cat (fn-ptx-frame-header rlen) (fn-pctx-cat (fn-ptx-kd-last kd) pre)))
 (data3 (fn-pctx-cat (fn-bs-zeros start) (fn-pctx-cat sh tail)))
 (m2 (fn-ptx-chg m :committed nil :ph :hashing :k 0 :cur (list (fn-ptx-cur-fid p) (fn-ptx-cur-finc p) bp alen 0 (fn-ptx-cur-txid p) ioff base glen) :b1 (list h1 g1 (len data1) (len ins)) :b3 (list h3 g3 end start *fn-ptx-sufhead-max*) :hs (list 0 nil) :acc nil))
 (rs4 (list (list :acquire h1) (list :acquire h3) (list :write h1 g1 0 (fn-pctx-cat data1 ins)) (list :write h3 g3 0 data3)))
 (s4 (mv-nth 0 (fn-rtc-requests rs4 1 1 s))))
  (declare (ignorable s4 ok))
  (implies (and (fn-pth-i-post-storage m s) (equal (fn-ptx-ph m) :reading)
    (equal (fn-ptx-ph (mv-nth 0 (fn-ptx-read m q 1 1 s))) :hashing))
   (and (equal (mv-nth 0 (fn-ptx-read m q 1 1 s)) m2)
        (equal (mv-nth 1 (fn-ptx-read m q 1 1 s)) (append rs4 (list (fn-ptx-timer)))))))
 :rule-classes nil
 :hints (("Goal" :use (fn-pth-i-reading-success-by-definition)
   :in-theory (set-difference-theories (theory 'minimal-theory) '(mv-nth)))))

(defthm fn-pth-i-reading-success-prefix-results
 (let* ((read (fn-ptx-read m q 1 1 s)) (m2 (mv-nth 0 read)) (rs (mv-nth 1 read))
        (rs4 (take 4 rs)) (s4 (mv-nth 0 (fn-rtc-requests rs4 1 1 s))))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s)
    (fn-pth-i-owner-uses (fn-rtc-uses s) nil)
    (equal (fn-ptx-ph m) :reading) (equal (fn-ptx-ph m2) :hashing))
   (and (fn-pth-i-runtime s4) (fn-pth-i-post-storage m2 s4)
        (fn-pth-i-owner-uses (fn-rtc-uses s4) nil)
        (not (mv-nth 2 (fn-rtc-requests rs4 1 1 s)))
        (equal rs (append rs4 (list (fn-ptx-timer)))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-reading-success-prefix fn-pth-i-reading-success-result-by-definition)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(take binary-append car-cons cdr-cons
     (:executable-counterpart equal) (:executable-counterpart zp)
     (:executable-counterpart binary-+))))))

(defthm fn-pth-i-reading-success-after-machine
 (let* ((read (fn-ptx-read m q 1 1 s)) (m2 (mv-nth 0 read)) (rs (mv-nth 1 read))
        (d (fn-rtc-with-mstate 1 m2 s)))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s)
    (fn-pth-i-owner-uses (fn-rtc-uses s) nil)
    (equal (fn-ptx-ph m) :reading) (equal (fn-ptx-ph m2) :hashing))
   (and (fn-pth-i (mv-nth 0 (fn-rtc-requests rs 1 1 d)))
        (not (mv-nth 2 (fn-rtc-requests rs 1 1 d))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-pth-i-reading-success-prefix-results
         (s (fn-rtc-with-mstate 1 (mv-nth 0 (fn-ptx-read m q 1 1 s)) s)))
        (:instance fn-pth-i-timer-after-prefix
         (m (mv-nth 0 (fn-ptx-read m q 1 1 s)))
         (rs (take 4 (mv-nth 1 (fn-ptx-read m q 1 1 s))))
         (s (fn-rtc-with-mstate 1 (mv-nth 0 (fn-ptx-read m q 1 1 s)) s))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-owner-machine-index fn-pth-i-read-with-mstate fn-pth-i-runtime-with-mstate fn-pth-i-post-storage-with-mstate
     fn-rtc-with-accessors fn-rtc-mstate-of-with fn-ptx-expected
     (:executable-counterpart member-equal) (:executable-counterpart equal) (:executable-counterpart nfix) (:executable-counterpart zp))))))

(defthm fn-pth-i-reading-success-owner-deliver
 (let ((m (fn-rtc-mstate 1 s)))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s)
    (fn-pth-i-owner-uses (fn-rtc-uses s) nil)
    (equal (fn-ptx-ph m) :reading)
    (equal (fn-rtc-ev-id ev) 1) (equal (fn-rtc-ev-inc ev) 1) (equal (fn-rtc-get 0 ev) :timer)
    (equal (fn-ptx-ph (mv-nth 0 (fn-ptx-read m (nfix q) 1 1 s))) :hashing))
   (and (fn-pth-i (mv-nth 0 (fn-pth-deliver s 1 1 ev q)))
        (not (mv-nth 2 (fn-pth-deliver s 1 1 ev q))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-pth-i-post-storage-machine-facts (m (fn-rtc-mstate 1 s)))
        (:instance fn-ptx-read-reads-view (m (fn-rtc-mstate 1 s)) (q (nfix q)) (id 1) (inc 1) (st s))
        (:instance fn-pth-i-reading-success-after-machine (m (fn-rtc-mstate 1 s)) (q (nfix q))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-deliver fn-pth-m-step fn-pthm-step fn-ptx-step fn-ptx-step1
     fn-ptx-okp-wfp fn-rtc-view-state
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition
     car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-pth-i-reading-success-host-delivery
 (let ((m (fn-rtc-mstate 1 s)))
  (implies (and (fn-pth-i s) (equal (fn-ptx-ph m) :reading)
    (fn-rtc-completionp e) (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))
    (equal (fn-rtc-e-id e) 1) (equal (fn-rtc-e-inc e) 1) (equal (fn-rtc-e-kind e) :timer)
    (equal (fn-rtc-ev-id ev) 1) (equal (fn-rtc-ev-inc ev) 1) (equal (fn-rtc-get 0 ev) :timer)
    (equal (fn-ptx-ph (mv-nth 0 (fn-ptx-read m (nfix q) 1 1 (fn-rtc-end-use s e)))) :hashing))
   (and (fn-pth-i (mv-nth 0 (fn-pth-deliver (fn-rtc-end-use s e) 1 1 ev q)))
        (not (mv-nth 2 (fn-pth-deliver (fn-rtc-end-use s e) 1 1 ev q))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-before-machine-after-end-use
        (:instance fn-pth-i-owner-protocol-after-expected-completion (m2 nil))
        (:instance fn-pth-i-reading-success-owner-deliver (s (fn-rtc-end-use s e))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-mstate-of-end-use fn-ptx-expected
     (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-pth-i-owner-reading-step
 (let ((m (fn-rtc-mstate 1 s)))
  (implies (and (fn-pth-i s) (equal (fn-ptx-ph m) :reading)
                (fn-rtc-acts-on-p s e) (equal (fn-rtc-e-id e) 1)
                (not (equal (fn-rtc-e-kind e) :hand)))
           (and (fn-pth-i (mv-nth 0 (fn-pth-step s e q)))
                (not (mv-nth 2 (fn-pth-step* s e q))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-owner-read-refusal-step fn-pth-i-runtime-and-post-state-by-definition fn-pth-i-direct-owner-completion
        fn-pth-i-direct-owner-completion-is-expected
        (:instance fn-pth-i-reading-success-host-delivery
          (ev (fn-rtc-ev :timer
                (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e) 1 1 nil))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-step fn-pth-step* fn-pth-i-rearm fn-ptx-expected
     fn-rtc-acts-on-p fn-rtc-hand-delivers-p fn-rtc-ev fn-rtc-ev-id fn-rtc-ev-inc fn-rtc-get-of-cons
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition car-cons cdr-cons
     (:executable-counterpart equal) (:executable-counterpart fn-rtc-get) (:executable-counterpart member-equal)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+))))))


; Hashing continuation and exact trailer-write storage effects.

(defthm fn-pth-i-hashing-storage-control-change
 (let ((m2 (fn-ptx-chg m :committed nil :hs hs)))
  (implies (and (fn-pth-i-post-storage m s) (equal (fn-ptx-ph m) :hashing) (fn-ptx-okp m2))
   (fn-pth-i-post-storage m2 s)))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-post-storage fn-ptx-in-flight-p fn-ptx-accessors-of-mk
     fn-ptx-nmsg-of-mk fn-ptx-nmsg-is-g fn-ptx-nfix-natp-rw natp
     (:type-prescription fn-ptx-k) (:type-prescription fn-ptx-ext) (:type-prescription fn-ptx-nxt)
     (:executable-counterpart equal) (:executable-counterpart nfix) (:executable-counterpart member-equal))))))

(defthm fn-pth-i-hash-more-machine-results
 (let* ((nw (min *fn-ptx-nw-max* (max 1 (floor (nfix q) *fn-ptx-window*))))
        (ab (fn-ptx-absorb nw (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m))
                    (fn-ptx-nmsg m) (fn-ptx-spans m) 1 1 s))
        (hash (fn-ptx-hash m q 1 1 s)))
  (implies (equal (fn-ptx-ph (mv-nth 0 hash)) :hashing)
   (and (equal (mv-nth 0 hash) (fn-ptx-chg m :committed nil :hs (list (mv-nth 0 ab) (mv-nth 1 ab))))
        (equal (mv-nth 1 hash) (list (fn-ptx-timer))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-ptx-hash fn-ptx-end-0 fn-ptx-start-0 fn-ptx-accessors-of-mk fn-ptx-nmsg
     fn-ptx-nfix-natp-rw natp (:type-prescription fn-ptx-k) (:type-prescription fn-ptx-ext) (:type-prescription fn-ptx-nxt)
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-1-cons-by-definition car-cons cdr-cons
     (:executable-counterpart equal) (:executable-counterpart nfix) (:executable-counterpart zp))))))

(defthm fn-pth-i-hash-more-post-storage
 (implies (and (fn-pth-i-post-storage m s) (equal (fn-ptx-ph m) :hashing)
               (equal (fn-ptx-ph (mv-nth 0 (fn-ptx-hash m q 1 1 s))) :hashing))
  (fn-pth-i-post-storage (mv-nth 0 (fn-ptx-hash m q 1 1 s)) s))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-pth-i-hashing-storage-control-change
          (hs (list (mv-nth 0 (fn-ptx-absorb (min *fn-ptx-nw-max* (max 1 (floor (nfix q) *fn-ptx-window*))) (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) 1 1 s))
                    (mv-nth 1 (fn-ptx-absorb (min *fn-ptx-nw-max* (max 1 (floor (nfix q) *fn-ptx-window*))) (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) 1 1 s)))))
        fn-pth-i-hash-more-machine-results (:instance fn-ptx-hash-ok (id 1) (inc 1) (st s)))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-post-storage-machine-facts)))))

(defthm fn-pth-i-timer-after-machine
 (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s)
               (fn-pth-i-owner-uses (fn-rtc-uses s) nil) (equal (fn-ptx-expected m) :timer))
  (and (fn-pth-i (mv-nth 0 (fn-rtc-requests (list (fn-ptx-timer)) 1 1 (fn-rtc-with-mstate 1 m s))))
       (not (mv-nth 2 (fn-rtc-requests (list (fn-ptx-timer)) 1 1 (fn-rtc-with-mstate 1 m s))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-pth-i-timer-after-prefix (rs nil) (s (fn-rtc-with-mstate 1 m s))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-requests fn-pth-i-runtime-with-mstate fn-pth-i-post-storage-with-mstate
     fn-rtc-with-accessors fn-rtc-mstate-of-with fn-pth-i-owner-machine-index
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition
     binary-append car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart nfix)
     (:executable-counterpart zp) (:executable-counterpart member-equal))))))

(defthm fn-pth-i-hash-more-after-machine
 (let* ((hash (fn-ptx-hash m q 1 1 s)) (m2 (mv-nth 0 hash)) (rs (mv-nth 1 hash)))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s)
    (fn-pth-i-owner-uses (fn-rtc-uses s) nil)
    (equal (fn-ptx-ph m) :hashing) (equal (fn-ptx-ph m2) :hashing))
   (and (fn-pth-i (mv-nth 0 (fn-rtc-requests rs 1 1 (fn-rtc-with-mstate 1 m2 s))))
        (not (mv-nth 2 (fn-rtc-requests rs 1 1 (fn-rtc-with-mstate 1 m2 s)))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-hash-more-machine-results fn-pth-i-hash-more-post-storage
        (:instance fn-pth-i-timer-after-machine (m (mv-nth 0 (fn-ptx-hash m q 1 1 s)))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-ptx-expected (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-pth-i-hash-more-owner-deliver
 (let ((m (fn-rtc-mstate 1 s)))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s)
    (fn-pth-i-owner-uses (fn-rtc-uses s) nil)
    (equal (fn-ptx-ph m) :hashing)
    (equal (fn-rtc-ev-id ev) 1) (equal (fn-rtc-ev-inc ev) 1) (equal (fn-rtc-get 0 ev) :timer)
    (equal (fn-ptx-ph (mv-nth 0 (fn-ptx-hash m (nfix q) 1 1 s))) :hashing))
   (and (fn-pth-i (mv-nth 0 (fn-pth-deliver s 1 1 ev q)))
        (not (mv-nth 2 (fn-pth-deliver s 1 1 ev q))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-pth-i-post-storage-machine-facts (m (fn-rtc-mstate 1 s)))
        (:instance fn-ptx-hash-reads-view (m (fn-rtc-mstate 1 s)) (q (nfix q)) (id 1) (inc 1) (st s))
        (:instance fn-pth-i-hash-more-after-machine (m (fn-rtc-mstate 1 s)) (q (nfix q))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-deliver fn-pth-m-step fn-pthm-step fn-ptx-step fn-ptx-step1
     fn-ptx-okp-wfp fn-rtc-view-state
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition
     car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-pth-i-hash-more-host-delivery
 (let ((m (fn-rtc-mstate 1 s)))
  (implies (and (fn-pth-i s) (equal (fn-ptx-ph m) :hashing)
    (fn-rtc-completionp e) (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))
    (equal (fn-rtc-e-id e) 1) (equal (fn-rtc-e-inc e) 1) (equal (fn-rtc-e-kind e) :timer)
    (equal (fn-rtc-ev-id ev) 1) (equal (fn-rtc-ev-inc ev) 1) (equal (fn-rtc-get 0 ev) :timer)
    (equal (fn-ptx-ph (mv-nth 0 (fn-ptx-hash m (nfix q) 1 1 (fn-rtc-end-use s e)))) :hashing))
   (and (fn-pth-i (mv-nth 0 (fn-pth-deliver (fn-rtc-end-use s e) 1 1 ev q)))
        (not (mv-nth 2 (fn-pth-deliver (fn-rtc-end-use s e) 1 1 ev q))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-before-machine-after-end-use
        (:instance fn-pth-i-owner-protocol-after-expected-completion (m2 nil))
        (:instance fn-pth-i-hash-more-owner-deliver (s (fn-rtc-end-use s e))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-mstate-of-end-use fn-ptx-expected
     (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-pth-i-owner-hash-more-step
 (let ((m (fn-rtc-mstate 1 s)))
  (implies (and (fn-pth-i s) (equal (fn-ptx-ph m) :hashing)
                (fn-rtc-acts-on-p s e) (equal (fn-rtc-e-id e) 1)
                (not (equal (fn-rtc-e-kind e) :hand))
                (equal (fn-ptx-ph (mv-nth 0 (fn-ptx-hash m (nfix q) 1 1 (fn-rtc-end-use s e)))) :hashing))
           (and (fn-pth-i (mv-nth 0 (fn-pth-step s e q)))
                (not (mv-nth 2 (fn-pth-step* s e q))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-runtime-and-post-state-by-definition fn-pth-i-direct-owner-completion
        fn-pth-i-direct-owner-completion-is-expected
        (:instance fn-pth-i-hash-more-host-delivery
          (ev (fn-rtc-ev :timer
                (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e) 1 1 nil))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-step fn-pth-step* fn-pth-i-rearm fn-ptx-expected
     fn-rtc-acts-on-p fn-rtc-hand-delivers-p fn-rtc-ev fn-rtc-ev-id fn-rtc-ev-inc fn-rtc-get-of-cons
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition car-cons cdr-cons
     (:executable-counterpart equal) (:executable-counterpart fn-rtc-get) (:executable-counterpart member-equal)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+))))))

(defthm fn-pth-i-splice-at-end
 (implies (and (fn-cbor-octet-listp bytes) (fn-cbor-octet-listp data))
  (equal (fn-rtc-splice bytes (len bytes) data) (append bytes data)))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-splice fn-rtc-true-list-fix-identity fn-rtc-c-take-of-len fn-rtc-c-nthcdr-past-len
     fn-pth-i-append-nil-for-true-lists fn-cbor-octet-listp-implies-true-listp
     fn-ptx-nfix-natp-rw natp min (:type-prescription len)
     default-+-1 default-+-2 unicity-of-0 fix
     (:executable-counterpart equal) (:executable-counterpart binary-+))))))

(defthm fn-pth-i-append-workspace
 (let* ((bytes (fn-rtc-b-bytes (fn-rtc-buffer h s))) (r (list :write h g (len bytes) data)))
  (implies (and (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
    (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:workspace 1 1))
    (equal (fn-rtc-b-gen (fn-rtc-buffer h s)) g)
    (fn-cbor-octet-listp bytes) (fn-cbor-octet-listp data)
    (<= (+ (len bytes) (len data)) (fn-rtc-buf-cap h (fn-rtc-config s))))
   (and (not (mv-nth 2 (fn-rtc-request r 1 1 s)))
    (equal (mv-nth 0 (fn-rtc-request r 1 1 s))
     (fn-rtc-with-buffer h (list g '(:workspace 1 1) (append bytes data)) s)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-request fn-rtc-req-write fn-pth-i-splice-at-end fn-rtc-get-of-cons
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition
     fn-ptx-nfix-natp-rw natp (:type-prescription len) car-cons cdr-cons
     (:executable-counterpart equal) (:executable-counterpart nfix) (:executable-counterpart zp))))))

(defthm fn-pth-i-hash-to-flight-storage
 (let* ((b3 (fn-ptx-b3 m)) (h (fn-ptx-buf-h b3)) (g (fn-ptx-buf-g b3))
        (bytes (fn-rtc-b-bytes (fn-rtc-buffer h s)))
        (s2 (fn-rtc-with-buffer h (list g '(:workspace 1 1) (append bytes trailer)) s))
        (m2 (fn-ptx-chg m :committed nil :ph ph :k 0 :nxt nx
              :b3 (list h g (+ (fn-ptx-buf-len b3) 32) (fn-ptx-buf-x b3) (fn-ptx-buf-cut b3))
              :hs (list (fn-ptx-nmsg m) trailer pad) :evd nil)))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s)
                (equal (fn-ptx-ph m) :hashing) (fn-ptx-in-flight-p ph)
                (fn-cbor-octet-listp trailer) (equal (len trailer) 32) (natp pad) (natp nx)
                (< nx (expt 2 64))
                (<= (+ (fn-ptx-kd-frontier (fn-ptx-kd m)) (fn-ptx-nmsg m) 32 pad) nx)
                (fn-ptx-okp m2))
           (fn-pth-i-post-storage m2 s2)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-post-storage fn-pth-i-runtime-pool-length-by-definition
     fn-pth-i-post fn-pth-i-visible-buffer fn-pth-i-queue-untracked-update fn-pth-i-queue-avoids-used
     fn-rtc-buffer-of-with fn-rtc-with-accessors fn-rtc-buffer-accessors fn-rtc-get-of-cons
     fn-ptx-accessors-of-mk fn-ptx-nmsg-is-g fn-ptx-spans-len-g fn-ptx-elen
     fn-ptx-buf-h fn-ptx-buf-g fn-ptx-buf-len fn-ptx-buf-x fn-ptx-buf-cut fn-ptx-in-flight-p
     fn-ptx-nfix-natp-rw fn-ptx-nfix-nfix min max natp
     fn-rtc-len-append binary-append member-equal car-cons cdr-cons
     (:type-prescription fn-ptx-buf-h) (:type-prescription fn-ptx-buf-g)
     (:type-prescription fn-ptx-buf-len) (:type-prescription fn-ptx-buf-x) (:type-prescription fn-ptx-buf-cut)
     (:type-prescription fn-ptx-cur-bp) (:type-prescription fn-ptx-cur-len) (:type-prescription fn-ptx-cur-glen)
     (:type-prescription fn-ptx-ext) (:type-prescription fn-ptx-nxt)
     (:type-prescription len) (:type-prescription nfix)
     associativity-of-+ commutativity-of-+ commutativity-2-of-+ fold-consts-in-+
     default-+-1 default-+-2 default-unary-minus inverse-of-+ unicity-of-0 fix
     (:executable-counterpart equal) (:executable-counterpart nfix) (:executable-counterpart zp)
     (:executable-counterpart member-equal) (:executable-counterpart binary-+))))))

(defthm fn-pth-i-hash-trailer-write-facts
 (let* ((b3 (fn-ptx-b3 m)) (h (fn-ptx-buf-h b3)) (b (fn-rtc-buffer h s)))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s) (equal (fn-ptx-ph m) :hashing))
   (and (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
        (equal (fn-rtc-b-owner b) '(:workspace 1 1))
        (equal (fn-rtc-b-gen b) (fn-ptx-buf-g b3))
        (equal (len (fn-rtc-b-bytes b)) (fn-ptx-buf-len b3))
        (fn-cbor-octet-listp (fn-rtc-b-bytes b))
        (<= (+ (fn-ptx-buf-len b3) 32) (fn-rtc-buf-cap h (fn-rtc-config s))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-runtime-shape-by-definition
        (:instance fn-rtc-c-shapep-buffer (h (fn-ptx-buf-h (fn-ptx-b3 m)))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-post-storage fn-pth-i-visible-buffer fn-rtc-b-bytes fn-ptx-in-flight-p
     fn-ptx-nfix-natp-rw natp (:type-prescription fn-ptx-buf-h)
     (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-pth-i-hash-trailer-flight-prefix
 (let* ((b3 (fn-ptx-b3 m)) (h (fn-ptx-buf-h b3)) (g (fn-ptx-buf-g b3))
        (bytes (fn-rtc-b-bytes (fn-rtc-buffer h s)))
        (r (list :write h g (fn-ptx-buf-len b3) trailer))
        (s2 (mv-nth 0 (fn-rtc-request r 1 1 s)))
        (m2 (fn-ptx-chg m :committed nil :ph ph :k 0 :nxt nx
              :b3 (list h g (+ (fn-ptx-buf-len b3) 32) (fn-ptx-buf-x b3) (fn-ptx-buf-cut b3))
              :hs (list (fn-ptx-nmsg m) trailer pad) :evd nil)))
  (declare (ignorable bytes))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s)
                (equal (fn-ptx-ph m) :hashing) (fn-ptx-in-flight-p ph)
                (fn-cbor-octet-listp trailer) (equal (len trailer) 32) (natp pad) (natp nx)
                (< nx (expt 2 64))
                (<= (+ (fn-ptx-kd-frontier (fn-ptx-kd m)) (fn-ptx-nmsg m) 32 pad) nx)
                (fn-ptx-okp m2))
           (and (fn-pth-i-runtime s2) (fn-pth-i-post-storage m2 s2)
                (equal (fn-rtc-uses s2) (fn-rtc-uses s))
                (not (mv-nth 2 (fn-rtc-request r 1 1 s))))))
 :rule-classes nil
  :hints (("Goal" :do-not-induct t
 :use (fn-pth-i-hash-trailer-write-facts fn-pth-i-hash-to-flight-storage
       (:instance fn-pth-i-append-workspace (h (fn-ptx-buf-h (fn-ptx-b3 m))) (g (fn-ptx-buf-g (fn-ptx-b3 m))) (data trailer))
       (:instance fn-pth-i-runtime-request (r (list :write (fn-ptx-buf-h (fn-ptx-b3 m)) (fn-ptx-buf-g (fn-ptx-b3 m)) (fn-ptx-buf-len (fn-ptx-b3 m)) trailer)) (id 1) (inc 1)))
 :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '(fn-rtc-request-config-frame fn-rtc-with-accessors fn-rtc-get-of-cons
    (:type-prescription fn-rtc-request) (:executable-counterpart equal)
    (:executable-counterpart member-equal) car-cons cdr-cons)))))


; Actual hashing finish: trailer write and admitted extend/pwrite tail.

(defthm fn-pth-i-owner-flight-tail
 (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s)
    (equal (fn-rtc-mstate 1 s) m) (fn-pth-i-owner-uses (fn-rtc-uses s) nil)
    (fn-ptx-in-flight-p (fn-ptx-ph m))
    (equal (fn-rtc-get 0 r) :submit) (equal (fn-rtc-get 1 r) (fn-ptx-expected m))
    (fn-pth-req-data-okp r)
    (or (and (not (equal (fn-rtc-get 1 r) :pool)) (not (fn-rtc-buffered-kind-p (fn-rtc-get 1 r))))
        (and (equal (fn-rtc-get 1 r) :pwrite)
             (fn-rtc-submit-okp :pwrite (fn-rtc-get 2 r) 1 1 s)
             (fn-pth-i-queue-avoids (fn-ptx-q m) (fn-rtc-h-buf (fn-rtc-get 2 r))))))
  (and (fn-pth-i (mv-nth 0 (fn-rtc-requests (list r) 1 1 s)))
       (not (mv-nth 2 (fn-rtc-requests (list r) 1 1 s)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-owner-output-request fn-pth-i-owner-unbuffered-request)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-hands-only-compatible-with-every-machine fn-pth-i-hands-only-has-no-operation
     fn-ptx-in-flight-p fn-ptx-expected fn-rtc-requests member-equal
     fn-rtc-requests-keeps-mstates fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition
     binary-append car-cons cdr-cons (:type-prescription fn-rtc-request)
     (:executable-counterpart member-equal) (:executable-counterpart equal)
     (:executable-counterpart fn-rtc-buffered-kind-p))))))

(defthm fn-pth-i-hash-flight-result-by-definition
 (let* ( (b3 (fn-ptx-b3 m))
 (h (fn-ptx-buf-h b3))
 (g (fn-ptx-buf-g b3))
 (kd (fn-ptx-kd m))
 (ext (fn-ptx-ext m))
 (front (fn-ptx-kd-frontier kd))
 (spans (fn-ptx-spans m))
 (nmsg (fn-ptx-nmsg m))
 (nw (min *fn-ptx-nw-max* (max 1 (floor (nfix q) *fn-ptx-window*))))
 (ab (fn-ptx-absorb nw (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) nmsg spans 1 1 s))
 (pos (mv-nth 0 ab))
 (stk (mv-nth 1 ab))
 (unit (fn-ptx-unit m))
 (trailer (fn-ptx-finish-digest pos stk nmsg spans 1 1 s))
 (pad (fn-ptx-pad-len (+ nmsg 32) unit))
 (elen (+ nmsg 32 pad))
 (needed (fn-olr-extension-needed-p front elen ext unit))
 (nx (if needed (fn-olr-extension-target front elen ext unit) ext))
 (ph (if needed :extending :payload-writing))
 (wr (list :write h g (fn-ptx-buf-len b3) trailer))
 (m2 (fn-ptx-chg m :committed nil :ph ph :k 0 :nxt nx :b3 (list h g (+ (fn-ptx-buf-len b3) 32) (fn-ptx-buf-x b3) (fn-ptx-buf-cut b3)) :hs (list nmsg trailer pad) :evd nil))
 (last-r (if needed (fn-ptx-extend ext nx) (fn-ptx-span-pwrite 0 m2 front 1 1 s)))
 (s1 (mv-nth 0 (fn-rtc-request wr 1 1 s))))
  (declare (ignorable s1))
  (implies (and (equal (fn-ptx-ph m) :hashing)
    (fn-ptx-in-flight-p (fn-ptx-ph (mv-nth 0 (fn-ptx-hash m q 1 1 s)))))
   (and (equal (mv-nth 0 (fn-ptx-hash m q 1 1 s)) m2)
        (equal (mv-nth 1 (fn-ptx-hash m q 1 1 s)) (list wr last-r))
        (implies needed (< nx (expt 2 64))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-ptx-hash fn-ptx-end-0 fn-ptx-start-0 fn-ptx-accessors-of-mk fn-ptx-nmsg fn-ptx-in-flight-p
     fn-ptx-nfix-natp-rw natp (:type-prescription fn-ptx-ext) (:type-prescription fn-ptx-nxt)
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-1-cons-by-definition car-cons cdr-cons
     (:executable-counterpart equal) (:executable-counterpart member-equal)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))

(defthm fn-pth-i-hash-flight-parameters
 (let* ( (b3 (fn-ptx-b3 m))
 (h (fn-ptx-buf-h b3))
 (g (fn-ptx-buf-g b3))
 (kd (fn-ptx-kd m))
 (ext (fn-ptx-ext m))
 (front (fn-ptx-kd-frontier kd))
 (spans (fn-ptx-spans m))
 (nmsg (fn-ptx-nmsg m))
 (nw (min *fn-ptx-nw-max* (max 1 (floor (nfix q) *fn-ptx-window*))))
 (ab (fn-ptx-absorb nw (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) nmsg spans 1 1 s))
 (pos (mv-nth 0 ab))
 (stk (mv-nth 1 ab))
 (unit (fn-ptx-unit m))
 (trailer (fn-ptx-finish-digest pos stk nmsg spans 1 1 s))
 (pad (fn-ptx-pad-len (+ nmsg 32) unit))
 (elen (+ nmsg 32 pad))
 (needed (fn-olr-extension-needed-p front elen ext unit))
 (nx (if needed (fn-olr-extension-target front elen ext unit) ext))
 (ph (if needed :extending :payload-writing))
 (wr (list :write h g (fn-ptx-buf-len b3) trailer))
 (m2 (fn-ptx-chg m :committed nil :ph ph :k 0 :nxt nx :b3 (list h g (+ (fn-ptx-buf-len b3) 32) (fn-ptx-buf-x b3) (fn-ptx-buf-cut b3)) :hs (list nmsg trailer pad) :evd nil))
 (last-r (if needed (fn-ptx-extend ext nx) (fn-ptx-span-pwrite 0 m2 front 1 1 s)))
 (s1 (mv-nth 0 (fn-rtc-request wr 1 1 s))))
  (declare (ignorable s1 last-r))
  (implies (and (fn-pth-i-post-storage m s) (equal (fn-ptx-ph m) :hashing)
    (fn-ptx-in-flight-p (fn-ptx-ph (mv-nth 0 (fn-ptx-hash m q 1 1 s)))))
   (and (fn-cbor-octet-listp trailer) (equal (len trailer) 32)
        (natp pad) (natp nx) (< nx (expt 2 64))
        (<= (+ front elen) nx) (fn-ptx-okp m2)
        (implies needed (< ext nx)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-hash-flight-result-by-definition
        (:instance fn-ptx-hash-ok (id 1) (inc 1) (st s))
        (:instance fn-ptx-extension-target-bounds (front (fn-ptx-kd-frontier (fn-ptx-kd m))) (e (+ (fn-ptx-nmsg m) 32 (fn-ptx-pad-len (+ (fn-ptx-nmsg m) 32) (fn-ptx-unit m)))) (ext (fn-ptx-ext m)) (unit (fn-ptx-unit m))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-post-storage-machine-facts fn-pth-i-post-storage-chain-and-extents
     fn-pth-i-finish-digest-is-octets fn-ptx-finish-digest-shape fn-olr-extension-needed-p
     fn-ptx-unit max posp natp fn-ptx-nfix-natp-rw fn-ptx-nfix-nfix
     (:type-prescription fn-ptx-ext) (:type-prescription fn-ptx-kd-frontier)
     (:type-prescription fn-ptx-nmsg) (:type-prescription fn-ptx-pad-len-tp) (:type-prescription nfix)
     associativity-of-+ commutativity-of-+ commutativity-2-of-+ fold-consts-in-+
     default-+-1 default-+-2 unicity-of-0 fix
     (:executable-counterpart equal) (:executable-counterpart binary-+)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))

(defthm fn-pth-i-get-nfix-by-definition
 (equal (fn-rtc-get (nfix i) x) (fn-rtc-get i x))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-get nfix natp zp car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart zp))))))

(defthm fn-pth-i-workspace-byte-update-keeps-view-gen
 (implies (and (natp h) (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:workspace 1 1)))
  (equal (fn-ptx-gen j 1 1 (fn-rtc-with-buffer h (list (fn-rtc-b-gen (fn-rtc-buffer h s)) '(:workspace 1 1) data) s))
         (fn-ptx-gen j 1 1 s)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-rtc-c-get-of-view-pool (j (nfix j)) (k 0) (id 1) (inc 1) (cfg (fn-rtc-config s)) (pool (fn-rtc-pool s)))
        (:instance fn-rtc-c-get-of-view-pool (j (nfix j)) (k 0) (id 1) (inc 1) (cfg (fn-rtc-config s))
          (pool (fn-rtc-set h (list (fn-rtc-b-gen (fn-rtc-buffer h s)) '(:workspace 1 1) data) (fn-rtc-pool s)))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-ptx-gen fn-rtc-st-v-gen fn-rtc-st$a-v-gen fn-rtc-vb fn-rtc-view
     fn-pth-i-get-nfix-by-definition fn-rtc-get-of-set fn-rtc-len-of-set fn-rtc-view-own-p fn-rtc-view-mine-p
     fn-rtc-buffer fn-rtc-buffer-of-with fn-rtc-with-accessors fn-rtc-buffer-accessors fn-rtc-get-of-cons
     fn-ptx-nfix-natp-rw fn-ptx-nfix-nfix natp
     (:type-prescription fn-rtc-b-gen) (:type-prescription nfix)
     car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+))))))

(defthm fn-pth-i-hash-trailer-write-keeps-view-gen
 (let* ((b3 (fn-ptx-b3 m)) (h (fn-ptx-buf-h b3)) (g (fn-ptx-buf-g b3))
        (wr (list :write h g (fn-ptx-buf-len b3) trailer)))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s) (equal (fn-ptx-ph m) :hashing)
                (fn-cbor-octet-listp trailer) (equal (len trailer) 32))
   (equal (fn-ptx-gen j 1 1 (mv-nth 0 (fn-rtc-request wr 1 1 s))) (fn-ptx-gen j 1 1 s))))
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-hash-trailer-write-facts
        (:instance fn-pth-i-append-workspace (h (fn-ptx-buf-h (fn-ptx-b3 m))) (g (fn-ptx-buf-g (fn-ptx-b3 m))) (data trailer))
        (:instance fn-pth-i-workspace-byte-update-keeps-view-gen (h (fn-ptx-buf-h (fn-ptx-b3 m)))
          (data (append (fn-rtc-b-bytes (fn-rtc-buffer (fn-ptx-buf-h (fn-ptx-b3 m)) s)) trailer))))
  :in-theory (set-difference-theories (theory 'minimal-theory) '(mv-nth)))))

(defthm fn-pth-i-hash-trailer-write-keeps-span-pwrite
 (let* ((b3 (fn-ptx-b3 m)) (wr (list :write (fn-ptx-buf-h b3) (fn-ptx-buf-g b3) (fn-ptx-buf-len b3) trailer)))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s) (equal (fn-ptx-ph m) :hashing)
                (fn-cbor-octet-listp trailer) (equal (len trailer) 32))
   (equal (fn-ptx-span-pwrite i new front 1 1 (mv-nth 0 (fn-rtc-request wr 1 1 s)))
          (fn-ptx-span-pwrite i new front 1 1 s))))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-ptx-span-pwrite fn-pth-i-hash-trailer-write-keeps-view-gen)))))

(defthm fn-pth-i-hash-flight-prefix
 (let* ( (b3 (fn-ptx-b3 m))
 (h (fn-ptx-buf-h b3))
 (g (fn-ptx-buf-g b3))
 (kd (fn-ptx-kd m))
 (ext (fn-ptx-ext m))
 (front (fn-ptx-kd-frontier kd))
 (spans (fn-ptx-spans m))
 (nmsg (fn-ptx-nmsg m))
 (nw (min *fn-ptx-nw-max* (max 1 (floor (nfix q) *fn-ptx-window*))))
 (ab (fn-ptx-absorb nw (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) nmsg spans 1 1 s))
 (pos (mv-nth 0 ab))
 (stk (mv-nth 1 ab))
 (unit (fn-ptx-unit m))
 (trailer (fn-ptx-finish-digest pos stk nmsg spans 1 1 s))
 (pad (fn-ptx-pad-len (+ nmsg 32) unit))
 (elen (+ nmsg 32 pad))
 (needed (fn-olr-extension-needed-p front elen ext unit))
 (nx (if needed (fn-olr-extension-target front elen ext unit) ext))
 (ph (if needed :extending :payload-writing))
 (wr (list :write h g (fn-ptx-buf-len b3) trailer))
 (m2 (fn-ptx-chg m :committed nil :ph ph :k 0 :nxt nx :b3 (list h g (+ (fn-ptx-buf-len b3) 32) (fn-ptx-buf-x b3) (fn-ptx-buf-cut b3)) :hs (list nmsg trailer pad) :evd nil))
 (last-r (if needed (fn-ptx-extend ext nx) (fn-ptx-span-pwrite 0 m2 front 1 1 s)))
 (s1 (mv-nth 0 (fn-rtc-request wr 1 1 s))))
  (declare (ignorable last-r))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s) (equal (fn-ptx-ph m) :hashing)
    (fn-ptx-in-flight-p (fn-ptx-ph (mv-nth 0 (fn-ptx-hash m q 1 1 s)))))
   (and (fn-pth-i-runtime s1) (fn-pth-i-post-storage m2 s1)
        (equal (fn-rtc-uses s1) (fn-rtc-uses s))
        (not (mv-nth 2 (fn-rtc-request wr 1 1 s))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-hash-flight-parameters
        (:instance fn-pth-i-hash-trailer-flight-prefix (ph (if (fn-olr-extension-needed-p (fn-ptx-kd-frontier (fn-ptx-kd m)) (+ (fn-ptx-nmsg m) 32 (fn-ptx-pad-len (+ (fn-ptx-nmsg m) 32) (fn-ptx-unit m))) (fn-ptx-ext m) (fn-ptx-unit m)) :extending :payload-writing)) (nx (if (fn-olr-extension-needed-p (fn-ptx-kd-frontier (fn-ptx-kd m)) (+ (fn-ptx-nmsg m) 32 (fn-ptx-pad-len (+ (fn-ptx-nmsg m) 32) (fn-ptx-unit m))) (fn-ptx-ext m) (fn-ptx-unit m)) (fn-olr-extension-target (fn-ptx-kd-frontier (fn-ptx-kd m)) (+ (fn-ptx-nmsg m) 32 (fn-ptx-pad-len (+ (fn-ptx-nmsg m) 32) (fn-ptx-unit m))) (fn-ptx-ext m) (fn-ptx-unit m)) (fn-ptx-ext m))) (trailer (fn-ptx-finish-digest (mv-nth 0 (fn-ptx-absorb (min *fn-ptx-nw-max* (max 1 (floor (nfix q) *fn-ptx-window*))) (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) 1 1 s)) (mv-nth 1 (fn-ptx-absorb (min *fn-ptx-nw-max* (max 1 (floor (nfix q) *fn-ptx-window*))) (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) 1 1 s)) (fn-ptx-nmsg m) (fn-ptx-spans m) 1 1 s)) (pad (fn-ptx-pad-len (+ (fn-ptx-nmsg m) 32) (fn-ptx-unit m)))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-ptx-in-flight-p (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-pth-data-okp-extend
 (implies (and (natp ext) (natp nx) (< ext nx) (< nx (expt 2 64)))
  (fn-pth-req-data-okp (fn-ptx-extend ext nx)))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-req-data-okp fn-ptx-extend fn-rtc-kind-extrap fn-rtc-extend-extrap fn-rtc-extrap fn-rtc-u64p
     fn-rtc-get-of-cons len true-listp natp fn-ptx-nfix-natp-rw
     car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart fn-rtc-buffered-kind-p) (:executable-counterpart member-equal)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart expt))))))

(defthm fn-pth-i-payload-has-output-span
 (implies (and (fn-pth-i-post-storage m s) (equal (fn-ptx-ph m) :payload-writing))
  (< 0 (len (fn-ptx-spans m))))
 :hints (("Goal" :do-not-induct t
  :use (fn-ptx-okp-elim)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-post-storage-machine-facts fn-ptx-nspans natp
     (:type-prescription fn-ptx-k) default-+-1 default-+-2
     (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-pth-i-hash-flight-prefix-results
 (let* ((hash (fn-ptx-hash m q 1 1 s)) (m2 (mv-nth 0 hash)) (rs (mv-nth 1 hash))
        (wr (car rs)) (s1 (mv-nth 0 (fn-rtc-request wr 1 1 s))))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s) (equal (fn-ptx-ph m) :hashing)
    (fn-ptx-in-flight-p (fn-ptx-ph m2)))
   (and (fn-pth-i-runtime s1) (fn-pth-i-post-storage m2 s1)
        (equal (fn-rtc-uses s1) (fn-rtc-uses s))
        (not (mv-nth 2 (fn-rtc-request wr 1 1 s)))
        (equal rs (list wr (cadr rs))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-hash-flight-prefix fn-pth-i-hash-flight-result-by-definition)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(car-cons cdr-cons (:executable-counterpart equal))))))

(defthm fn-pth-i-hash-with-mstate
 (equal (fn-ptx-hash old q id inc (fn-rtc-with-mstate j m s)) (fn-ptx-hash old q id inc s))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-ptx-hash-reads-view (m old) (st (fn-rtc-with-mstate j m s)))
        (:instance fn-ptx-hash-reads-view (m old) (st s)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-pth-i-view-state-with-mstate)))))

(defthm fn-pth-i-hash-flight-tail-properties
 (let* ( (b3 (fn-ptx-b3 m))
 (h (fn-ptx-buf-h b3))
 (g (fn-ptx-buf-g b3))
 (kd (fn-ptx-kd m))
 (ext (fn-ptx-ext m))
 (front (fn-ptx-kd-frontier kd))
 (spans (fn-ptx-spans m))
 (nmsg (fn-ptx-nmsg m))
 (nw (min *fn-ptx-nw-max* (max 1 (floor (nfix q) *fn-ptx-window*))))
 (ab (fn-ptx-absorb nw (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) nmsg spans 1 1 s))
 (pos (mv-nth 0 ab))
 (stk (mv-nth 1 ab))
 (unit (fn-ptx-unit m))
 (trailer (fn-ptx-finish-digest pos stk nmsg spans 1 1 s))
 (pad (fn-ptx-pad-len (+ nmsg 32) unit))
 (elen (+ nmsg 32 pad))
 (needed (fn-olr-extension-needed-p front elen ext unit))
 (nx (if needed (fn-olr-extension-target front elen ext unit) ext))
 (ph (if needed :extending :payload-writing))
 (wr (list :write h g (fn-ptx-buf-len b3) trailer))
 (m2 (fn-ptx-chg m :committed nil :ph ph :k 0 :nxt nx :b3 (list h g (+ (fn-ptx-buf-len b3) 32) (fn-ptx-buf-x b3) (fn-ptx-buf-cut b3)) :hs (list nmsg trailer pad) :evd nil))
 (last-r (if needed (fn-ptx-extend ext nx) (fn-ptx-span-pwrite 0 m2 front 1 1 s)))
 (s1 (mv-nth 0 (fn-rtc-request wr 1 1 s))))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s) (equal (fn-ptx-ph m) :hashing)
    (fn-ptx-in-flight-p (fn-ptx-ph (mv-nth 0 (fn-ptx-hash m q 1 1 s)))))
   (and (fn-pth-req-data-okp last-r) (equal (fn-rtc-get 0 last-r) :submit)
        (equal (fn-rtc-get 1 last-r) (fn-ptx-expected m2))
        (or (and (not (equal (fn-rtc-get 1 last-r) :pool))
                 (not (fn-rtc-buffered-kind-p (fn-rtc-get 1 last-r))))
            (and (equal (fn-rtc-get 1 last-r) :pwrite)
                 (fn-rtc-submit-okp :pwrite (fn-rtc-get 2 last-r) 1 1 s1)
                 (fn-pth-i-queue-avoids (fn-ptx-q m2) (fn-rtc-h-buf (fn-rtc-get 2 last-r))))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-hash-flight-parameters fn-pth-i-hash-flight-prefix
        (:instance fn-pth-data-okp-extend (ext (fn-ptx-ext m)) (nx (if (fn-olr-extension-needed-p (fn-ptx-kd-frontier (fn-ptx-kd m)) (+ (fn-ptx-nmsg m) 32 (fn-ptx-pad-len (+ (fn-ptx-nmsg m) 32) (fn-ptx-unit m))) (fn-ptx-ext m) (fn-ptx-unit m)) (fn-olr-extension-target (fn-ptx-kd-frontier (fn-ptx-kd m)) (+ (fn-ptx-nmsg m) 32 (fn-ptx-pad-len (+ (fn-ptx-nmsg m) 32) (fn-ptx-unit m))) (fn-ptx-ext m) (fn-ptx-unit m)) (fn-ptx-ext m))))
        (:instance fn-pth-i-span-pwrite-properties (m (fn-ptx-chg m :committed nil :ph (if (fn-olr-extension-needed-p (fn-ptx-kd-frontier (fn-ptx-kd m)) (+ (fn-ptx-nmsg m) 32 (fn-ptx-pad-len (+ (fn-ptx-nmsg m) 32) (fn-ptx-unit m))) (fn-ptx-ext m) (fn-ptx-unit m)) :extending :payload-writing) :k 0 :nxt (if (fn-olr-extension-needed-p (fn-ptx-kd-frontier (fn-ptx-kd m)) (+ (fn-ptx-nmsg m) 32 (fn-ptx-pad-len (+ (fn-ptx-nmsg m) 32) (fn-ptx-unit m))) (fn-ptx-ext m) (fn-ptx-unit m)) (fn-olr-extension-target (fn-ptx-kd-frontier (fn-ptx-kd m)) (+ (fn-ptx-nmsg m) 32 (fn-ptx-pad-len (+ (fn-ptx-nmsg m) 32) (fn-ptx-unit m))) (fn-ptx-ext m) (fn-ptx-unit m)) (fn-ptx-ext m)) :b3 (list (fn-ptx-buf-h (fn-ptx-b3 m)) (fn-ptx-buf-g (fn-ptx-b3 m)) (+ (fn-ptx-buf-len (fn-ptx-b3 m)) 32) (fn-ptx-buf-x (fn-ptx-b3 m)) (fn-ptx-buf-cut (fn-ptx-b3 m))) :hs (list (fn-ptx-nmsg m) (fn-ptx-finish-digest (mv-nth 0 (fn-ptx-absorb (min *fn-ptx-nw-max* (max 1 (floor (nfix q) *fn-ptx-window*))) (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) 1 1 s)) (mv-nth 1 (fn-ptx-absorb (min *fn-ptx-nw-max* (max 1 (floor (nfix q) *fn-ptx-window*))) (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) 1 1 s)) (fn-ptx-nmsg m) (fn-ptx-spans m) 1 1 s) (fn-ptx-pad-len (+ (fn-ptx-nmsg m) 32) (fn-ptx-unit m))) :evd nil)) (s (mv-nth 0 (fn-rtc-request (list :write (fn-ptx-buf-h (fn-ptx-b3 m)) (fn-ptx-buf-g (fn-ptx-b3 m)) (fn-ptx-buf-len (fn-ptx-b3 m)) (fn-ptx-finish-digest (mv-nth 0 (fn-ptx-absorb (min *fn-ptx-nw-max* (max 1 (floor (nfix q) *fn-ptx-window*))) (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) 1 1 s)) (mv-nth 1 (fn-ptx-absorb (min *fn-ptx-nw-max* (max 1 (floor (nfix q) *fn-ptx-window*))) (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) 1 1 s)) (fn-ptx-nmsg m) (fn-ptx-spans m) 1 1 s)) 1 1 s))) (i 0))
        (:instance fn-pth-i-hash-trailer-write-keeps-span-pwrite (new (fn-ptx-chg m :committed nil :ph (if (fn-olr-extension-needed-p (fn-ptx-kd-frontier (fn-ptx-kd m)) (+ (fn-ptx-nmsg m) 32 (fn-ptx-pad-len (+ (fn-ptx-nmsg m) 32) (fn-ptx-unit m))) (fn-ptx-ext m) (fn-ptx-unit m)) :extending :payload-writing) :k 0 :nxt (if (fn-olr-extension-needed-p (fn-ptx-kd-frontier (fn-ptx-kd m)) (+ (fn-ptx-nmsg m) 32 (fn-ptx-pad-len (+ (fn-ptx-nmsg m) 32) (fn-ptx-unit m))) (fn-ptx-ext m) (fn-ptx-unit m)) (fn-olr-extension-target (fn-ptx-kd-frontier (fn-ptx-kd m)) (+ (fn-ptx-nmsg m) 32 (fn-ptx-pad-len (+ (fn-ptx-nmsg m) 32) (fn-ptx-unit m))) (fn-ptx-ext m) (fn-ptx-unit m)) (fn-ptx-ext m)) :b3 (list (fn-ptx-buf-h (fn-ptx-b3 m)) (fn-ptx-buf-g (fn-ptx-b3 m)) (+ (fn-ptx-buf-len (fn-ptx-b3 m)) 32) (fn-ptx-buf-x (fn-ptx-b3 m)) (fn-ptx-buf-cut (fn-ptx-b3 m))) :hs (list (fn-ptx-nmsg m) (fn-ptx-finish-digest (mv-nth 0 (fn-ptx-absorb (min *fn-ptx-nw-max* (max 1 (floor (nfix q) *fn-ptx-window*))) (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) 1 1 s)) (mv-nth 1 (fn-ptx-absorb (min *fn-ptx-nw-max* (max 1 (floor (nfix q) *fn-ptx-window*))) (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) 1 1 s)) (fn-ptx-nmsg m) (fn-ptx-spans m) 1 1 s) (fn-ptx-pad-len (+ (fn-ptx-nmsg m) 32) (fn-ptx-unit m))) :evd nil)) (front (fn-ptx-kd-frontier (fn-ptx-kd m))) (trailer (fn-ptx-finish-digest (mv-nth 0 (fn-ptx-absorb (min *fn-ptx-nw-max* (max 1 (floor (nfix q) *fn-ptx-window*))) (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) 1 1 s)) (mv-nth 1 (fn-ptx-absorb (min *fn-ptx-nw-max* (max 1 (floor (nfix q) *fn-ptx-window*))) (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) 1 1 s)) (fn-ptx-nmsg m) (fn-ptx-spans m) 1 1 s)) (i 0)))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-payload-has-output-span fn-ptx-accessors-of-mk
     fn-ptx-expected fn-ptx-in-flight-p fn-ptx-extend fn-rtc-get-of-cons
     fn-ptx-nfix-natp-rw natp (:type-prescription fn-ptx-ext)
     car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart member-equal)
     (:executable-counterpart nfix) (:executable-counterpart zp)
     (:executable-counterpart fn-rtc-get) (:executable-counterpart fn-rtc-buffered-kind-p))))))

(defthm fn-pth-i-hash-flight-tail-results
 (let* ((hash (fn-ptx-hash m q 1 1 s)) (m2 (mv-nth 0 hash)) (rs (mv-nth 1 hash))
        (wr (car rs)) (r (cadr rs)) (s1 (mv-nth 0 (fn-rtc-request wr 1 1 s))))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s) (equal (fn-ptx-ph m) :hashing)
    (fn-ptx-in-flight-p (fn-ptx-ph m2)))
   (and (fn-pth-req-data-okp r) (equal (fn-rtc-get 0 r) :submit)
        (equal (fn-rtc-get 1 r) (fn-ptx-expected m2))
        (or (and (not (equal (fn-rtc-get 1 r) :pool)) (not (fn-rtc-buffered-kind-p (fn-rtc-get 1 r))))
            (and (equal (fn-rtc-get 1 r) :pwrite)
                 (fn-rtc-submit-okp :pwrite (fn-rtc-get 2 r) 1 1 s1)
                 (fn-pth-i-queue-avoids (fn-ptx-q m2) (fn-rtc-h-buf (fn-rtc-get 2 r))))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-hash-flight-tail-properties fn-pth-i-hash-flight-result-by-definition)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(car-cons cdr-cons (:executable-counterpart equal))))))

(defthm fn-pth-i-owner-flight-after-prefix
 (let ((s1 (mv-nth 0 (fn-rtc-request first 1 1 s))))
  (implies (and (fn-pth-i-runtime s1) (fn-pth-i-post-storage m s1)
    (equal (fn-rtc-mstate 1 s) m) (fn-pth-i-owner-uses (fn-rtc-uses s1) nil)
    (not (mv-nth 2 (fn-rtc-request first 1 1 s)))
    (fn-ptx-in-flight-p (fn-ptx-ph m))
    (equal (fn-rtc-get 0 r) :submit) (equal (fn-rtc-get 1 r) (fn-ptx-expected m))
    (fn-pth-req-data-okp r)
    (or (and (not (equal (fn-rtc-get 1 r) :pool)) (not (fn-rtc-buffered-kind-p (fn-rtc-get 1 r))))
        (and (equal (fn-rtc-get 1 r) :pwrite)
             (fn-rtc-submit-okp :pwrite (fn-rtc-get 2 r) 1 1 s1)
             (fn-pth-i-queue-avoids (fn-ptx-q m) (fn-rtc-h-buf (fn-rtc-get 2 r))))))
   (and (fn-pth-i (mv-nth 0 (fn-rtc-requests (list first r) 1 1 s)))
        (not (mv-nth 2 (fn-rtc-requests (list first r) 1 1 s))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-pth-i-owner-flight-tail (s (mv-nth 0 (fn-rtc-request first 1 1 s)))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-request-keeps-mstates fn-rtc-requests fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition
     binary-append car-cons cdr-cons (:type-prescription fn-rtc-request)
     (:executable-counterpart equal))))))

(defthm fn-pth-i-hash-flight-after-machine
 (let* ((hash (fn-ptx-hash m q 1 1 s)) (m2 (mv-nth 0 hash)) (rs (mv-nth 1 hash))
        (d (fn-rtc-with-mstate 1 m2 s)))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s)
    (fn-pth-i-owner-uses (fn-rtc-uses s) nil)
    (equal (fn-ptx-ph m) :hashing) (fn-ptx-in-flight-p (fn-ptx-ph m2)))
   (and (fn-pth-i (mv-nth 0 (fn-rtc-requests rs 1 1 d)))
        (not (mv-nth 2 (fn-rtc-requests rs 1 1 d))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-pth-i-hash-flight-prefix-results (s (fn-rtc-with-mstate 1 (mv-nth 0 (fn-ptx-hash m q 1 1 s)) s)))
        (:instance fn-pth-i-hash-flight-tail-results (s (fn-rtc-with-mstate 1 (mv-nth 0 (fn-ptx-hash m q 1 1 s)) s)))
        (:instance fn-pth-i-owner-flight-after-prefix
         (m (mv-nth 0 (fn-ptx-hash m q 1 1 s)))
         (first (car (mv-nth 1 (fn-ptx-hash m q 1 1 s))))
         (r (cadr (mv-nth 1 (fn-ptx-hash m q 1 1 s))))
         (s (fn-rtc-with-mstate 1 (mv-nth 0 (fn-ptx-hash m q 1 1 s)) s))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-hash-with-mstate fn-pth-i-runtime-with-mstate fn-pth-i-post-storage-with-mstate
     fn-rtc-with-accessors fn-rtc-mstate-of-with fn-pth-i-owner-machine-index
     (:executable-counterpart equal) (:executable-counterpart nfix) (:executable-counterpart zp))))))

(defthm fn-pth-i-hash-flight-owner-deliver
 (let ((m (fn-rtc-mstate 1 s)))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s)
    (fn-pth-i-owner-uses (fn-rtc-uses s) nil)
    (equal (fn-ptx-ph m) :hashing)
    (equal (fn-rtc-ev-id ev) 1) (equal (fn-rtc-ev-inc ev) 1) (equal (fn-rtc-get 0 ev) :timer)
    (fn-ptx-in-flight-p (fn-ptx-ph (mv-nth 0 (fn-ptx-hash m (nfix q) 1 1 s)))))
   (and (fn-pth-i (mv-nth 0 (fn-pth-deliver s 1 1 ev q)))
        (not (mv-nth 2 (fn-pth-deliver s 1 1 ev q))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-pth-i-post-storage-machine-facts (m (fn-rtc-mstate 1 s)))
        (:instance fn-ptx-hash-reads-view (m (fn-rtc-mstate 1 s)) (q (nfix q)) (id 1) (inc 1) (st s))
        (:instance fn-pth-i-hash-flight-after-machine (m (fn-rtc-mstate 1 s)) (q (nfix q))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-deliver fn-pth-m-step fn-pthm-step fn-ptx-step fn-ptx-step1
     fn-ptx-okp-wfp fn-rtc-view-state
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition
     car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-pth-i-hash-flight-host-delivery
 (let ((m (fn-rtc-mstate 1 s)))
  (implies (and (fn-pth-i s) (equal (fn-ptx-ph m) :hashing)
    (fn-rtc-completionp e) (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))
    (equal (fn-rtc-e-id e) 1) (equal (fn-rtc-e-inc e) 1) (equal (fn-rtc-e-kind e) :timer)
    (equal (fn-rtc-ev-id ev) 1) (equal (fn-rtc-ev-inc ev) 1) (equal (fn-rtc-get 0 ev) :timer)
    (fn-ptx-in-flight-p (fn-ptx-ph (mv-nth 0 (fn-ptx-hash m (nfix q) 1 1 (fn-rtc-end-use s e))))))
   (and (fn-pth-i (mv-nth 0 (fn-pth-deliver (fn-rtc-end-use s e) 1 1 ev q)))
        (not (mv-nth 2 (fn-pth-deliver (fn-rtc-end-use s e) 1 1 ev q))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-before-machine-after-end-use
        (:instance fn-pth-i-owner-protocol-after-expected-completion (m2 nil))
        (:instance fn-pth-i-hash-flight-owner-deliver (s (fn-rtc-end-use s e))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-mstate-of-end-use fn-ptx-expected
     (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-pth-i-owner-hash-flight-step
 (let ((m (fn-rtc-mstate 1 s)))
  (implies (and (fn-pth-i s) (equal (fn-ptx-ph m) :hashing)
                (fn-rtc-acts-on-p s e) (equal (fn-rtc-e-id e) 1)
                (not (equal (fn-rtc-e-kind e) :hand))
                (fn-ptx-in-flight-p (fn-ptx-ph (mv-nth 0 (fn-ptx-hash m (nfix q) 1 1 (fn-rtc-end-use s e))))))
           (and (fn-pth-i (mv-nth 0 (fn-pth-step s e q)))
                (not (mv-nth 2 (fn-pth-step* s e q))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-runtime-and-post-state-by-definition fn-pth-i-direct-owner-completion
        fn-pth-i-direct-owner-completion-is-expected
        (:instance fn-pth-i-hash-flight-host-delivery
          (ev (fn-rtc-ev :timer
                (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e) 1 1 nil))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-step fn-pth-step* fn-pth-i-rearm fn-ptx-expected
     fn-rtc-acts-on-p fn-rtc-hand-delivers-p fn-rtc-ev fn-rtc-ev-id fn-rtc-ev-inc fn-rtc-get-of-cons
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition car-cons cdr-cons
     (:executable-counterpart equal) (:executable-counterpart fn-rtc-get) (:executable-counterpart member-equal)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+))))))


; Overflow end consumes the old workspaces while carrying the next machine storage.

(defthm fn-pth-i-release-and-answer-components
 (let* ((p (fn-ptx-cur m)) (bp (fn-ptx-cur-bp p))
        (h1 (fn-ptx-buf-h (fn-ptx-b1 m))) (h3 (fn-ptx-buf-h (fn-ptx-b3 m)))
        (rs (append (fn-ptx-release-bufs m 1 1 s) (fn-ptx-answer p o 1 1 s)))
        (s2 (mv-nth 0 (fn-rtc-requests rs 1 1 s))))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m2 s)
    (fn-pth-i-owner-uses (fn-rtc-uses s) nil) (fn-pth-i-post p s nil) (fn-pth-i-storage-avoids m2 bp)
    (implies (consp (fn-ptx-b1 m))
      (and (fn-pth-i-visible-buffer h1 s nil) (fn-pth-i-storage-avoids m2 h1) (not (equal h1 bp))))
    (implies (consp (fn-ptx-b3 m))
      (and (fn-pth-i-visible-buffer h3 s nil) (fn-pth-i-storage-avoids m2 h3) (not (equal h3 bp))))
    (implies (and (consp (fn-ptx-b1 m)) (consp (fn-ptx-b3 m))) (not (equal h1 h3))))
   (and (fn-pth-i-runtime s2) (fn-pth-i-post-storage m2 s2)
        (fn-pth-i-owner-uses (fn-rtc-uses s2) nil)
        (not (mv-nth 2 (fn-rtc-requests rs 1 1 s))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-release-bufs-components
        (:instance fn-pth-i-release-bufs-post (p (fn-ptx-cur m)) (st s))
        (:instance fn-pth-i-release-bufs-other-buffer (j (fn-ptx-cur-bp (fn-ptx-cur m))) (st s))
        (:instance fn-pth-i-answer-buffer-congruence (p (fn-ptx-cur m))
          (s1 s) (s2 (mv-nth 0 (fn-rtc-requests (fn-ptx-release-bufs m 1 1 s) 1 1 s))))
        (:instance fn-pth-i-answer-components (p (fn-ptx-cur m)) (m m2)
          (s (mv-nth 0 (fn-rtc-requests (fn-ptx-release-bufs m 1 1 s) 1 1 s)))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-requests-append-state fn-pth-i-requests-append-refused fn-rtc-requests-config-frame
     fn-pth-i-release-bufs-owner-uses fn-pth-i-answer-owner-uses fn-pth-i-hands-only-compatible-with-every-machine
     natp (:type-prescription fn-ptx-cur-bp) binary-append car-cons cdr-cons (:executable-counterpart equal))))))

(defthm fn-pth-i-visible-buffer-of-owner-write
 (implies (equal (fn-rtc-get 0 r) :write)
  (equal (fn-pth-i-visible-buffer j (mv-nth 0 (fn-rtc-request r 1 1 s)) leasedp)
         (fn-pth-i-visible-buffer j s leasedp)))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-request fn-rtc-req-write fn-pth-i-visible-buffer fn-rtc-buffer-of-with
     fn-rtc-with-accessors fn-rtc-buffer-accessors fn-rtc-get-of-cons
     fn-hld-mv-nth-0-cons fn-ptx-nfix-natp-rw fn-ptx-nfix-nfix natp
     car-cons cdr-cons (:type-prescription fn-rtc-request)
     (:executable-counterpart equal) (:executable-counterpart nfix) (:executable-counterpart zp))))))

(defthm fn-pth-i-post-of-owner-write
 (implies (equal (fn-rtc-get 0 r) :write)
  (equal (fn-pth-i-post p (mv-nth 0 (fn-rtc-request r 1 1 s)) leasedp) (fn-pth-i-post p s leasedp)))
 :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
  '(fn-pth-i-post fn-pth-i-visible-buffer-of-owner-write fn-rtc-request-config-frame)))))

(defthm fn-pth-i-hashing-has-buffers-by-definition
 (implies (and (fn-pth-i-post-storage m s) (equal (fn-ptx-ph m) :hashing))
  (and (consp (fn-ptx-b1 m)) (consp (fn-ptx-b3 m))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-post-storage (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-pth-i-hash-end-prefix-after-write
 (let* ((bp (fn-ptx-cur-bp (fn-ptx-cur m)))
        (h1 (fn-ptx-buf-h (fn-ptx-b1 m))) (h3 (fn-ptx-buf-h (fn-ptx-b3 m)))
        (wr (list :write h3 (fn-ptx-buf-g (fn-ptx-b3 m)) (fn-ptx-buf-len (fn-ptx-b3 m)) trailer))
        (s1 (mv-nth 0 (fn-rtc-request wr 1 1 s)))
        (rs (append (fn-ptx-release-bufs m 1 1 s1) (fn-ptx-answer (fn-ptx-cur m) o 1 1 s1)))
        (s2 (mv-nth 0 (fn-rtc-requests rs 1 1 s1))))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s) (equal (fn-ptx-ph m) :hashing)
    (fn-pth-i-owner-uses (fn-rtc-uses s) nil) (fn-pth-i-post-storage m2 s)
    (fn-pth-i-storage-avoids m2 bp) (fn-pth-i-storage-avoids m2 h1) (fn-pth-i-storage-avoids m2 h3))
   (and (fn-pth-i-runtime s2) (fn-pth-i-post-storage m2 s2)
        (fn-pth-i-owner-uses (fn-rtc-uses s2) nil)
        (not (mv-nth 2 (fn-rtc-requests rs 1 1 s1))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-end-source-workspaces
        (:instance fn-pth-i-release-and-answer-components
         (s (mv-nth 0 (fn-rtc-request (list :write (fn-ptx-buf-h (fn-ptx-b3 m)) (fn-ptx-buf-g (fn-ptx-b3 m)) (fn-ptx-buf-len (fn-ptx-b3 m)) trailer) 1 1 s)))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-runtime-request fn-pth-i-post-storage-untracked-request
     fn-pth-i-visible-buffer-of-owner-write fn-pth-i-post-of-owner-write
     fn-pth-i-hashing-has-buffers-by-definition fn-pth-i-owner-local-request-protocol
     fn-rtc-get-of-cons natp (:type-prescription fn-ptx-buf-h)
     fn-ptx-nfix-natp-rw fn-ptx-nfix-nfix car-cons cdr-cons
     (:executable-counterpart equal) (:executable-counterpart member-equal)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))

(defthm fn-pth-i-end-machine-storage-frame-by-definition
 (equal (mv-nth 0 (fn-ptx-end m o kd ext fenced committed id inc st))
        (mv-nth 0 (fn-ptx-end m o kd ext fenced committed id inc s)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-ptx-end-0 fn-ptx-start-0)))))

(defthm fn-pth-i-hash-write-keeps-end-prefix
 (let* ((h (fn-ptx-buf-h (fn-ptx-b3 m)))
        (wr (list :write h (fn-ptx-buf-g (fn-ptx-b3 m)) (fn-ptx-buf-len (fn-ptx-b3 m)) trailer))
        (s1 (mv-nth 0 (fn-rtc-request wr 1 1 s))))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s) (equal (fn-ptx-ph m) :hashing)
    (fn-pth-i-owner-uses (fn-rtc-uses s) nil) (fn-cbor-octet-listp trailer) (equal (len trailer) 32))
   (equal (append (fn-ptx-release-bufs m 1 1 s1) (fn-ptx-answer (fn-ptx-cur m) o 1 1 s1))
          (append (fn-ptx-release-bufs m 1 1 s) (fn-ptx-answer (fn-ptx-cur m) o 1 1 s)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-end-source-workspaces
        (:instance fn-pth-i-answer-buffer-congruence (p (fn-ptx-cur m)) (s1 s)
         (s2 (mv-nth 0 (fn-rtc-request (list :write (fn-ptx-buf-h (fn-ptx-b3 m)) (fn-ptx-buf-g (fn-ptx-b3 m)) (fn-ptx-buf-len (fn-ptx-b3 m)) trailer) 1 1 s)))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-runtime-request fn-pth-i-hashing-has-buffers-by-definition
     fn-pth-i-post-of-owner-write fn-pth-i-local-request-other-buffer
     fn-ptx-release-bufs fn-pth-i-hash-trailer-write-keeps-view-gen
     fn-rtc-get-of-cons fn-ptx-nfix-natp-rw fn-ptx-nfix-nfix natp
     (:type-prescription fn-ptx-cur-bp) (:type-prescription fn-ptx-buf-h)
     car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart member-equal)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))

(defthm fn-pth-i-hash-trailer-write-admitted
 (let ((wr (list :write (fn-ptx-buf-h (fn-ptx-b3 m)) (fn-ptx-buf-g (fn-ptx-b3 m))
                 (fn-ptx-buf-len (fn-ptx-b3 m)) trailer)))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s) (equal (fn-ptx-ph m) :hashing)
                (fn-cbor-octet-listp trailer) (equal (len trailer) 32))
   (not (mv-nth 2 (fn-rtc-request wr 1 1 s)))))
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-hash-trailer-write-facts
        (:instance fn-pth-i-append-workspace (h (fn-ptx-buf-h (fn-ptx-b3 m))) (g (fn-ptx-buf-g (fn-ptx-b3 m))) (data trailer)))
  :in-theory (set-difference-theories (theory 'minimal-theory) '(mv-nth)))))

(defthm fn-pth-i-hash-end-source-prefix
 (let* ((end (fn-ptx-end m o kd ext nil committed 1 1 s)) (m2 (mv-nth 0 end))
        (wr (list :write (fn-ptx-buf-h (fn-ptx-b3 m)) (fn-ptx-buf-g (fn-ptx-b3 m))
                  (fn-ptx-buf-len (fn-ptx-b3 m)) trailer))
        (done (append (fn-ptx-release-bufs m 1 1 s) (fn-ptx-answer (fn-ptx-cur m) o 1 1 s)))
        (rs (cons wr done)) (s2 (mv-nth 0 (fn-rtc-requests rs 1 1 s))))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s) (equal (fn-ptx-ph m) :hashing)
    (fn-pth-i-owner-uses (fn-rtc-uses s) nil) (fn-cbor-octet-listp trailer) (equal (len trailer) 32)
    (fn-cbor-octet-listp (fn-ptx-kd-last kd)) (< (nfix ext) (expt 2 64)) (fn-ptx-okp m2))
   (and (fn-pth-i-runtime s2) (fn-pth-i-post-storage m2 s2)
        (fn-pth-i-owner-uses (fn-rtc-uses s2) nil)
        (not (mv-nth 2 (fn-rtc-requests rs 1 1 s))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-pth-i-end-post-storage (st s) (fenced nil))
        (:instance fn-pth-i-end-old-buffers-untracked (st s) (fenced nil))
        (:instance fn-pth-i-hash-end-prefix-after-write (m2 (mv-nth 0 (fn-ptx-end m o kd ext nil committed 1 1 s))))
        fn-pth-i-hash-write-keeps-end-prefix)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-hash-trailer-write-admitted fn-pth-i-hashing-has-buffers-by-definition
     fn-rtc-requests fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition
     binary-append car-cons cdr-cons (:type-prescription fn-rtc-request)
     (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-pth-i-empty-three-appends-right-nil
 (implies (not (append x y z)) (not (append x y z nil)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-pth-i-empty-append-right-nil (x (append x y)) (y z)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-pth-i-append-associative)))))

(defthm fn-pth-i-hash-end-requests-post-state
 (let* ((end (fn-ptx-end m o kd ext nil committed 1 1 s)) (m2 (mv-nth 0 end))
        (wr (list :write (fn-ptx-buf-h (fn-ptx-b3 m)) (fn-ptx-buf-g (fn-ptx-b3 m))
                  (fn-ptx-buf-len (fn-ptx-b3 m)) trailer))
        (rs (cons wr (mv-nth 1 end))) (s2 (mv-nth 0 (fn-rtc-requests rs 1 1 s))))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s) (equal (fn-ptx-ph m) :hashing)
    (fn-pth-i-owner-uses (fn-rtc-uses s) nil) (fn-cbor-octet-listp trailer) (equal (len trailer) 32)
    (fn-cbor-octet-listp (fn-ptx-kd-last kd)) (< (nfix ext) (expt 2 64)) (fn-ptx-okp m2))
   (and (fn-pth-i-runtime s2) (fn-pth-i-post-state m2 s2)
        (not (mv-nth 2 (fn-rtc-requests rs 1 1 s))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t :cases ((consp (fn-ptx-q m)))
  :use (fn-pth-i-hash-end-source-prefix
        (:instance fn-pth-i-timer-restores-post-state
         (m (mv-nth 0 (fn-ptx-end m o kd ext nil committed 1 1 s)))
         (s (mv-nth 0 (fn-rtc-requests
           (cons (list :write (fn-ptx-buf-h (fn-ptx-b3 m)) (fn-ptx-buf-g (fn-ptx-b3 m)) (fn-ptx-buf-len (fn-ptx-b3 m)) trailer)
             (append (fn-ptx-release-bufs m 1 1 s) (fn-ptx-answer (fn-ptx-cur m) o 1 1 s))) 1 1 s))))
        (:instance fn-pth-i-no-expected-post-state
         (m (mv-nth 0 (fn-ptx-end m o kd ext nil committed 1 1 s)))
         (s (mv-nth 0 (fn-rtc-requests
           (cons (list :write (fn-ptx-buf-h (fn-ptx-b3 m)) (fn-ptx-buf-g (fn-ptx-b3 m)) (fn-ptx-buf-len (fn-ptx-b3 m)) trailer)
             (append (fn-ptx-release-bufs m 1 1 s) (fn-ptx-answer (fn-ptx-cur m) o 1 1 s))) 1 1 s)))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-ptx-end fn-ptx-start fn-ptx-expected fn-ptx-accessors-of-mk
     fn-pth-i-requests-append-state fn-pth-i-requests-append-refused fn-pth-i-empty-append-right-nil fn-pth-i-empty-three-appends-right-nil
     fn-pth-i-append-associative fn-pth-i-hands-only-compatible-with-every-machine fn-rtc-requests fn-hld-mv-nth-0-cons
     fn-pth-i-mv-nth-1-cons-by-definition fn-pth-i-mv-nth-2-cons-by-definition
     binary-append car-cons cdr-cons (:type-prescription fn-rtc-request)
     (:executable-counterpart member-equal) (:executable-counterpart equal))))))

(defthm fn-pth-i-hash-end-after-machine
 (let* ((end (fn-ptx-end m o kd ext nil committed 1 1 s)) (m2 (mv-nth 0 end)) (wr (list :write (fn-ptx-buf-h (fn-ptx-b3 m)) (fn-ptx-buf-g (fn-ptx-b3 m)) (fn-ptx-buf-len (fn-ptx-b3 m)) trailer)) (rs (cons wr (mv-nth 1 end))))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s) (equal (fn-ptx-ph m) :hashing)
    (fn-pth-i-owner-uses (fn-rtc-uses s) nil) (fn-cbor-octet-listp trailer) (equal (len trailer) 32)
    (fn-cbor-octet-listp (fn-ptx-kd-last kd)) (< (nfix ext) (expt 2 64)) (fn-ptx-okp m2))
   (and (fn-pth-i (mv-nth 0 (fn-rtc-requests rs 1 1 (fn-rtc-with-mstate 1 m2 s))))
        (not (mv-nth 2 (fn-rtc-requests rs 1 1 (fn-rtc-with-mstate 1 m2 s)))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-pth-i-hash-end-requests-post-state (s (fn-rtc-with-mstate 1 (mv-nth 0 (fn-ptx-end m o kd ext nil committed 1 1 s)) s)))
        (:instance fn-pth-i-runtime-and-post-state-by-definition (s (mv-nth 0 (fn-rtc-requests (cons (list :write (fn-ptx-buf-h (fn-ptx-b3 m)) (fn-ptx-buf-g (fn-ptx-b3 m)) (fn-ptx-buf-len (fn-ptx-b3 m)) trailer) (mv-nth 1 (fn-ptx-end m o kd ext nil committed 1 1 s))) 1 1 (fn-rtc-with-mstate 1 (mv-nth 0 (fn-ptx-end m o kd ext nil committed 1 1 s)) s))))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-end-with-mstate fn-pth-i-runtime-with-mstate fn-pth-i-post-storage-with-mstate
     fn-rtc-with-accessors fn-rtc-requests-keeps-mstates fn-rtc-mstate fn-pth-i-owner-machine-index
     fn-rtc-mstate-of-with fn-rtc-get-of-set (:executable-counterpart nfix) (:executable-counterpart natp))))))

(defthm fn-pth-i-hash-end-machine-results
 (let* ( (b3 (fn-ptx-b3 m))
 (h (fn-ptx-buf-h b3))
 (g (fn-ptx-buf-g b3))
 (kd (fn-ptx-kd m))
 (ext (fn-ptx-ext m))
 (front (fn-ptx-kd-frontier kd))
 (spans (fn-ptx-spans m))
 (nmsg (fn-ptx-nmsg m))
 (nw (min *fn-ptx-nw-max* (max 1 (floor (nfix q) *fn-ptx-window*))))
 (ab (fn-ptx-absorb nw (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) nmsg spans 1 1 s))
 (pos (mv-nth 0 ab))
 (stk (mv-nth 1 ab))
 (unit (fn-ptx-unit m))
 (trailer (fn-ptx-finish-digest pos stk nmsg spans 1 1 s))
 (pad (fn-ptx-pad-len (+ nmsg 32) unit))
 (elen (+ nmsg 32 pad))
 (needed (fn-olr-extension-needed-p front elen ext unit))
 (nx (if needed (fn-olr-extension-target front elen ext unit) ext))
 (ph (if needed :extending :payload-writing))
 (wr (list :write h g (fn-ptx-buf-len b3) trailer))
 (m2 (fn-ptx-chg m :committed nil :ph ph :k 0 :nxt nx :b3 (list h g (+ (fn-ptx-buf-len b3) 32) (fn-ptx-buf-x b3) (fn-ptx-buf-cut b3)) :hs (list nmsg trailer pad) :evd nil))
 (last-r (if needed (fn-ptx-extend ext nx) (fn-ptx-span-pwrite 0 m2 front 1 1 s)))
 (s1 (mv-nth 0 (fn-rtc-request wr 1 1 s)))
  (end (fn-ptx-end (fn-ptx-chg m :committed nil) :refused kd ext nil nil 1 1 s))
  (hash (fn-ptx-hash m q 1 1 s)))
  (declare (ignorable m2 last-r s1))
  (implies (and (equal (fn-ptx-ph m) :hashing)
    (not (equal (fn-ptx-ph (mv-nth 0 hash)) :hashing))
    (not (fn-ptx-in-flight-p (fn-ptx-ph (mv-nth 0 hash)))))
   (and (equal (mv-nth 0 hash) (mv-nth 0 end))
        (equal (mv-nth 1 hash) (cons wr (mv-nth 1 end))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-ptx-hash fn-ptx-accessors-of-mk fn-ptx-nmsg fn-ptx-in-flight-p
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-1-cons-by-definition car-cons cdr-cons
     (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-pth-i-hash-overflow-after-machine
 (let* ((hash (fn-ptx-hash m q 1 1 s)) (m2 (mv-nth 0 hash)) (rs (mv-nth 1 hash)))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s)
    (fn-pth-i-owner-uses (fn-rtc-uses s) nil) (equal (fn-ptx-ph m) :hashing)
    (not (equal (fn-ptx-ph m2) :hashing)) (not (fn-ptx-in-flight-p (fn-ptx-ph m2))))
   (and (fn-pth-i (mv-nth 0 (fn-rtc-requests rs 1 1 (fn-rtc-with-mstate 1 m2 s))))
        (not (mv-nth 2 (fn-rtc-requests rs 1 1 (fn-rtc-with-mstate 1 m2 s)))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-hash-end-machine-results fn-pth-i-post-storage-m0
        (:instance fn-ptx-hash-ok (id 1) (inc 1) (st s))
        (:instance fn-pth-i-hash-end-after-machine (m (fn-ptx-chg m :committed nil)) (o :refused) (kd (fn-ptx-kd m)) (ext (fn-ptx-ext m)) (committed nil) (trailer (fn-ptx-finish-digest (mv-nth 0 (fn-ptx-absorb (min *fn-ptx-nw-max* (max 1 (floor (nfix q) *fn-ptx-window*))) (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) 1 1 s)) (mv-nth 1 (fn-ptx-absorb (min *fn-ptx-nw-max* (max 1 (floor (nfix q) *fn-ptx-window*))) (fn-rtc-get 0 (fn-ptx-hs m)) (fn-rtc-get 1 (fn-ptx-hs m)) (fn-ptx-nmsg m) (fn-ptx-spans m) 1 1 s)) (fn-ptx-nmsg m) (fn-ptx-spans m) 1 1 s))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-post-storage-machine-facts fn-pth-i-post-storage-chain-and-extents
     fn-pth-i-finish-digest-is-octets fn-ptx-finish-digest-shape fn-ptx-accessors-of-mk
     fn-ptx-nfix-natp-rw natp (:type-prescription fn-ptx-ext)
     (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-pth-i-hash-overflow-owner-deliver
 (let ((m (fn-rtc-mstate 1 s)))
  (implies (and (fn-pth-i-runtime s) (fn-pth-i-post-storage m s)
    (fn-pth-i-owner-uses (fn-rtc-uses s) nil)
    (equal (fn-ptx-ph m) :hashing)
    (equal (fn-rtc-ev-id ev) 1) (equal (fn-rtc-ev-inc ev) 1) (equal (fn-rtc-get 0 ev) :timer)
    (and (not (equal (fn-ptx-ph (mv-nth 0 (fn-ptx-hash m (nfix q) 1 1 s))) :hashing)) (not (fn-ptx-in-flight-p (fn-ptx-ph (mv-nth 0 (fn-ptx-hash m (nfix q) 1 1 s)))))))
   (and (fn-pth-i (mv-nth 0 (fn-pth-deliver s 1 1 ev q)))
        (not (mv-nth 2 (fn-pth-deliver s 1 1 ev q))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-pth-i-post-storage-machine-facts (m (fn-rtc-mstate 1 s)))
        (:instance fn-ptx-hash-reads-view (m (fn-rtc-mstate 1 s)) (q (nfix q)) (id 1) (inc 1) (st s))
        (:instance fn-pth-i-hash-overflow-after-machine (m (fn-rtc-mstate 1 s)) (q (nfix q))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-deliver fn-pth-m-step fn-pthm-step fn-ptx-step fn-ptx-step1
     fn-ptx-okp-wfp fn-rtc-view-state
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition
     car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-pth-i-hash-overflow-host-delivery
 (let ((m (fn-rtc-mstate 1 s)))
  (implies (and (fn-pth-i s) (equal (fn-ptx-ph m) :hashing)
    (fn-rtc-completionp e) (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))
    (equal (fn-rtc-e-id e) 1) (equal (fn-rtc-e-inc e) 1) (equal (fn-rtc-e-kind e) :timer)
    (equal (fn-rtc-ev-id ev) 1) (equal (fn-rtc-ev-inc ev) 1) (equal (fn-rtc-get 0 ev) :timer)
    (and (not (equal (fn-ptx-ph (mv-nth 0 (fn-ptx-hash m (nfix q) 1 1 (fn-rtc-end-use s e)))) :hashing)) (not (fn-ptx-in-flight-p (fn-ptx-ph (mv-nth 0 (fn-ptx-hash m (nfix q) 1 1 (fn-rtc-end-use s e))))))))
   (and (fn-pth-i (mv-nth 0 (fn-pth-deliver (fn-rtc-end-use s e) 1 1 ev q)))
        (not (mv-nth 2 (fn-pth-deliver (fn-rtc-end-use s e) 1 1 ev q))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-before-machine-after-end-use
        (:instance fn-pth-i-owner-protocol-after-expected-completion (m2 nil))
        (:instance fn-pth-i-hash-overflow-owner-deliver (s (fn-rtc-end-use s e))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-mstate-of-end-use fn-ptx-expected
     (:executable-counterpart equal) (:executable-counterpart member-equal))))))

(defthm fn-pth-i-owner-hash-overflow-step
 (let ((m (fn-rtc-mstate 1 s)))
  (implies (and (fn-pth-i s) (equal (fn-ptx-ph m) :hashing)
                (fn-rtc-acts-on-p s e) (equal (fn-rtc-e-id e) 1)
                (not (equal (fn-rtc-e-kind e) :hand))
                (and (not (equal (fn-ptx-ph (mv-nth 0 (fn-ptx-hash m (nfix q) 1 1 (fn-rtc-end-use s e)))) :hashing)) (not (fn-ptx-in-flight-p (fn-ptx-ph (mv-nth 0 (fn-ptx-hash m (nfix q) 1 1 (fn-rtc-end-use s e))))))))
           (and (fn-pth-i (mv-nth 0 (fn-pth-step s e q)))
                (not (mv-nth 2 (fn-pth-step* s e q))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-runtime-and-post-state-by-definition fn-pth-i-direct-owner-completion
        fn-pth-i-direct-owner-completion-is-expected
        (:instance fn-pth-i-hash-overflow-host-delivery
          (ev (fn-rtc-ev :timer
                (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e) 1 1 nil))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-step fn-pth-step* fn-pth-i-rearm fn-ptx-expected
     fn-rtc-acts-on-p fn-rtc-hand-delivers-p fn-rtc-ev fn-rtc-ev-id fn-rtc-ev-inc fn-rtc-get-of-cons
     fn-hld-mv-nth-0-cons fn-pth-i-mv-nth-2-cons-by-definition car-cons cdr-cons
     (:executable-counterpart equal) (:executable-counterpart fn-rtc-get) (:executable-counterpart member-equal)
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+))))))

(defthm fn-pth-i-owner-hashing-step
 (implies (and (fn-pth-i s) (equal (fn-ptx-ph (fn-rtc-mstate 1 s)) :hashing)
               (fn-rtc-acts-on-p s e) (equal (fn-rtc-e-id e) 1)
               (not (equal (fn-rtc-e-kind e) :hand)))
  (and (fn-pth-i (mv-nth 0 (fn-pth-step s e q)))
       (not (mv-nth 2 (fn-pth-step* s e q)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-owner-hash-more-step fn-pth-i-owner-hash-flight-step fn-pth-i-owner-hash-overflow-step)
  :in-theory (set-difference-theories (theory 'minimal-theory) '(mv-nth)))))


; Full joint I is inductive over the actual host completion and host-run machines.

(defthm fn-pth-i-owner-direct-step
 (implies (and (fn-pth-i s) (fn-rtc-acts-on-p s e) (equal (fn-rtc-e-id e) 1)
               (not (fn-rtc-hand-delivers-p s e)))
  (and (fn-pth-i (mv-nth 0 (fn-pth-step s e q)))
       (not (mv-nth 2 (fn-pth-step* s e q)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-owner-opened-step fn-pth-i-owner-returned-hand-step
        fn-pth-i-owner-reading-step fn-pth-i-owner-hashing-step fn-pth-i-owner-flight-step
        fn-pth-i-direct-owner-completion-is-expected)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-ptx-expected fn-ptx-in-flight-p member-equal (:executable-counterpart equal)
     (:executable-counterpart member-equal))))))

(defthm fn-pth-i-owner-delivery-classification
 (implies (and (fn-pth-i s) (mv-nth 0 (fn-pth-owner-delivery s e q)))
  (or (and (fn-rtc-hand-delivers-p s e) (equal (fn-rtc-hand-to s e) 1))
      (and (fn-rtc-acts-on-p s e) (equal (fn-rtc-e-id e) 1) (not (fn-rtc-hand-delivers-p s e)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-runtime-and-post-state-by-definition
        (:instance fn-pth-i-free-slot-is-dynamic (s (fn-rtc-end-use s e))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-owner-delivery fn-pth-i-runtime-end-use fn-rtc-hand-to
     fn-hld-mv-nth-0-cons car-cons cdr-cons (:executable-counterpart equal)
     (:executable-counterpart nfix) (:executable-counterpart zp))))))

(defthm fn-pth-i-step
 (implies (fn-pth-i s)
  (and (fn-pth-i (mv-nth 0 (fn-pth-step s e q)))
       (implies (mv-nth 0 (fn-pth-owner-delivery s e q))
                (not (mv-nth 2 (fn-pth-step* s e q))))))
 :hints (("Goal" :do-not-induct t
  :use (fn-pth-i-owner-delivery-classification fn-pth-i-owner-direct-step
        fn-pth-i-owner-handed-step fn-pth-i-step-without-owner-delivery)
  :in-theory (set-difference-theories (theory 'minimal-theory) '(mv-nth)))))

(defthm fn-pth-i-host-run
 (implies (fn-pth-i s) (fn-pth-i (fn-pth-host-run s ops q)))
 :hints (("Goal" :induct (fn-pth-host-run s ops q)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-host-run fn-pth-i-step fn-pth-i-foreign-requests fn-hld-mv-nth-0-cons
     car-cons cdr-cons (:executable-counterpart equal))))))

(defthm fn-pth-reachable-implies-i
 (implies (fn-pth-reachablep s) (fn-pth-i s))
 :hints (("Goal" :do-not-induct t :expand ((fn-pth-reachablep s))
  :use ((:instance fn-pth-i-host-run (s (mv-nth 0 (fn-pth-init (fn-hl-rtc-config (mv-nth 0 (fn-pth-reachablep-witness s)) (mv-nth 1 (fn-pth-reachablep-witness s)) (mv-nth 3 (fn-pth-reachablep-witness s)) *fn-pth-nstatic* 0 0 *fn-pth-qs* *fn-pth-cs*))))
          (ops (mv-nth 2 (fn-pth-reachablep-witness s))) (q (mv-nth 3 (fn-pth-reachablep-witness s))))
        (:instance fn-pth-i-initial-invariant (profile (mv-nth 0 (fn-pth-reachablep-witness s)))
          (mcfg (mv-nth 1 (fn-pth-reachablep-witness s))) (q (mv-nth 3 (fn-pth-reachablep-witness s)))))
  :in-theory (set-difference-theories (theory 'minimal-theory) '(mv-nth)))))


; Frozen OD and R0 follow from the carried host invariant.

(defthm fn-pth-owner-requests-are-well-typed
 (implies (and (fn-pth-reachablep s) (natp q)
               (mv-nth 0 (fn-pth-owner-delivery s e q)))
          (fn-pth-reqs-data-okp (fn-pth-owner-requests s e q)))
 :hints (("Goal" :do-not-induct t :use (fn-pth-i-step fn-pth-reachable-implies-i fn-pth-unrefused-owner-requests-data)
  :in-theory (set-difference-theories (theory 'minimal-theory) '(mv-nth)))))

(defthm fn-pth-owner-requests-are-never-refused
  (implies (and (fn-pth-reachablep s) (natp q) (mv-nth 0 (fn-pth-owner-delivery s e q)))
           (not (mv-nth 2 (fn-pth-step* s e q))))
 :hints (("Goal" :do-not-induct t :use (fn-pth-i-step fn-pth-reachable-implies-i)
  :in-theory (set-difference-theories (theory 'minimal-theory) '(mv-nth)))))


; Trace rely foundation: owned view bytes and message frames.

(defthm fn-pth-i-owned-view-buffer-is-physical
 (implies (and (natp h) (< h (len (fn-rtc-pool s)))
               (fn-rtc-view-own-p (fn-rtc-b-owner (fn-rtc-buffer h s)) 1 1))
  (equal (fn-rtc-vb h 1 1 s) (fn-rtc-buffer h s)))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-rtc-vb fn-rtc-view fn-rtc-c-get-of-view-pool fn-rtc-buffer
     natp fn-ptx-nfix-natp-rw (:type-prescription nfix)
     (:executable-counterpart equal))))))

(defthm fn-pth-i-owned-byte-is-physical
 (implies (and (natp h) (< h (len (fn-rtc-pool s)))
               (fn-rtc-view-own-p (fn-rtc-b-owner (fn-rtc-buffer h s)) 1 1))
  (equal (fn-ptx-byte h i 1 1 s)
   (if (true-listp (fn-rtc-b-bytes (fn-rtc-buffer h s)))
       (nfix (nth (nfix i) (fn-rtc-b-bytes (fn-rtc-buffer h s)))) 0)))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-ptx-byte fn-rtc-st-v-byte fn-rtc-st$a-v-byte fn-pth-i-owned-view-buffer-is-physical
     (:executable-counterpart nfix))))))

(defthm fn-pth-i-visible-byte-of-storage-update
 (implies (and (natp k) (natp h) (< h (len (fn-rtc-pool s)))
    (fn-pth-i-owner-buffer-framep (fn-rtc-buffer k s) b) (fn-pth-i-visible-buffer h s t))
  (equal (fn-ptx-byte h i 1 1 (fn-rtc-with-buffer k b s)) (fn-ptx-byte h i 1 1 s)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-pth-i-visible-buffer-of-storage-update (h k) (j h) (leasedp t))
        (:instance fn-pth-i-visible-bytes-of-storage-update (h k) (j h)))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-owned-byte-is-physical fn-pth-i-visible-buffer fn-rtc-view-own-p
     fn-rtc-with-accessors fn-rtc-len-of-set natp fn-ptx-nfix-natp-rw
     (:executable-counterpart equal) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart member-equal))))))

(defthm fn-pth-i-byte-nfix-buffer-by-definition
 (equal (fn-ptx-byte (nfix h) i 1 1 s) (fn-ptx-byte h i 1 1 s))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-ptx-byte fn-rtc-st-v-byte fn-rtc-st$a-v-byte fn-rtc-vb fn-pth-i-get-nfix-by-definition)))))

(defthm fn-pth-i-byte-of-storage-update
 (implies (and (natp k) (< (nfix h) (len (fn-rtc-pool s)))
    (fn-pth-i-owner-buffer-framep (fn-rtc-buffer k s) b) (fn-pth-i-visible-buffer (nfix h) s t))
  (equal (fn-ptx-byte h i 1 1 (fn-rtc-with-buffer k b s)) (fn-ptx-byte h i 1 1 s)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-pth-i-visible-byte-of-storage-update (h (nfix h))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-byte-nfix-buffer-by-definition natp (:type-prescription nfix))))))

(defthm fn-pth-i-visible-buffer-pool-bound
 (implies (and (fn-pth-i-runtime s) (fn-pth-i-visible-buffer h s leasedp))
  (< h (len (fn-rtc-pool s))))
 :rule-classes (:rewrite :linear)
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(fn-pth-i-visible-buffer fn-pth-i-runtime-pool-length-by-definition)))))

(defthm fn-pth-i-msg-byte-of-storage-update
 (implies (and (fn-pth-i-runtime s) (natp k)
               (fn-pth-i-owner-buffer-framep (fn-rtc-buffer k s) b)
               (fn-pth-i-output-spans spans ps s))
  (equal (fn-ptx-msg-byte i spans 1 1 (fn-rtc-with-buffer k b s)) (fn-ptx-msg-byte i spans 1 1 s)))
 :hints (("Goal" :induct (fn-ptx-msg-byte i spans 1 1 s)
  :expand ((fn-pth-i-output-spans spans ps s))
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-ptx-msg-byte fn-pth-i-output-spans fn-pth-i-output-span fn-pth-i-visible-buffer-pool-bound
     fn-pth-i-byte-of-storage-update
     fn-ptx-nfix-natp-rw fn-ptx-nfix-nfix natp car-cons cdr-cons (:type-prescription nfix))))))

(defthm fn-pth-i-msg-range-of-storage-update
 (implies (and (fn-pth-i-runtime s) (natp k)
               (fn-pth-i-owner-buffer-framep (fn-rtc-buffer k s) b)
               (fn-pth-i-output-spans spans ps s))
  (equal (fn-ptx-msg-range i n spans 1 1 (fn-rtc-with-buffer k b s)) (fn-ptx-msg-range i n spans 1 1 s)))
 :hints (("Goal" :induct (fn-ptx-msg-range i n spans 1 1 s)
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-ptx-msg-range fn-pth-i-msg-byte-of-storage-update car-cons cdr-cons)))))

(defthm fn-pth-i-message-of-storage-update
 (implies (and (fn-pth-i-runtime s) (natp k)
               (fn-pth-i-owner-buffer-framep (fn-rtc-buffer k s) b)
               (fn-pth-i-output-spans (fn-ptx-spans m) ps s))
  (equal (fn-ptx-message m 1 1 (fn-rtc-with-buffer k b s)) (fn-ptx-message m 1 1 s)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-pth-i-msg-range-of-storage-update (i 0) (n (fn-ptx-spans-len (fn-ptx-spans m))) (spans (fn-ptx-spans m))))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-message)))))

(defthm fn-pth-i-output-spans-of-hashing-storage
 (implies (and (fn-pth-i-post-storage m s) (equal (fn-ptx-ph m) :hashing))
          (fn-pth-i-output-spans (fn-ptx-spans m) (fn-ptx-q m) s))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-post-storage fn-ptx-in-flight-p fn-pth-i-post
     fn-pth-i-visible-buffer fn-pth-i-visible-buffer-leasedp-congruence
     fn-ptx-spans fn-ptx-spans-g fn-pth-i-output-spans-append fn-pth-i-output-spans-single
     fn-pth-i-queue-avoids-used member-equal binary-append min max natp nfix
     default-+-1 default-+-2 default-unary-minus associativity-of-+ commutativity-of-+ commutativity-2-of-+
     inverse-of-+ fold-consts-in-+ unicity-of-0 fix car-cons cdr-cons
     (:type-prescription fn-ptx-cur-bp) (:type-prescription fn-ptx-cur-len)
     (:type-prescription fn-ptx-cur-ioff) (:type-prescription fn-ptx-cur-base) (:type-prescription fn-ptx-cur-glen)
     (:type-prescription fn-ptx-buf-h) (:type-prescription fn-ptx-buf-len)
     (:type-prescription fn-ptx-buf-x) (:type-prescription fn-ptx-buf-cut)
     (:executable-counterpart equal) (:executable-counterpart member-equal) (:executable-counterpart nfix))))))

; R1 foreign request/message frames and general off-timer machine-state frame.
(defthm fn-pth-i-visible-byte-buffer-congruence
 (implies (and (fn-pth-i-runtime s) (fn-pth-i-runtime st) (natp h)
               (fn-pth-i-visible-buffer h s t)
               (equal (fn-rtc-config st) (fn-rtc-config s))
               (equal (fn-rtc-buffer h st) (fn-rtc-buffer h s)))
  (equal (fn-ptx-byte h i 1 1 st) (fn-ptx-byte h i 1 1 s)))
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-pth-i-owned-byte-is-physical fn-pth-i-visible-buffer fn-rtc-view-own-p
     fn-pth-i-runtime-pool-length-by-definition (:executable-counterpart equal)
     (:executable-counterpart fn-rtc-get) (:executable-counterpart member-equal))))))
(defthm fn-pth-i-byte-foreign-request
 (implies (and (fn-pth-i-runtime s) (not (equal id 1)) (fn-pth-i-visible-buffer (nfix h) s t))
  (equal (fn-ptx-byte h i 1 1 (mv-nth 0 (fn-rtc-request r id inc s))) (fn-ptx-byte h i 1 1 s)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-pth-i-visible-byte-buffer-congruence (h (nfix h))
          (st (mv-nth 0 (fn-rtc-request r id inc s)))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-runtime-request fn-rtc-request-config-frame fn-pth-request-visible-buffer-frame
     fn-pth-i-visible-buffer fn-rtc-view-own-p fn-pth-i-byte-nfix-buffer-by-definition
     fn-ptx-nfix-natp-rw natp (:type-prescription nfix)
     (:executable-counterpart equal) (:executable-counterpart fn-rtc-get)
     (:executable-counterpart member-equal))))))

(defthm fn-pth-i-output-spans-foreign-request
 (implies (and (not (equal id 1)) (fn-pth-i-output-spans spans ps s))
  (fn-pth-i-output-spans spans ps (mv-nth 0 (fn-rtc-request r id inc s))))
 :hints (("Goal" :induct (fn-pth-i-output-spans spans ps s)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-pth-i-output-spans fn-pth-i-output-span fn-pth-i-visible-buffer-request
     fn-pth-request-visible-buffer-frame fn-pth-i-visible-buffer fn-rtc-view-own-p
     fn-rtc-request-config-frame car-cons cdr-cons (:executable-counterpart fn-rtc-get)
     (:executable-counterpart equal) (:executable-counterpart member-equal))))))
(defthm fn-pth-i-msg-byte-foreign-request
 (implies (and (fn-pth-i-runtime s) (not (equal id 1)) (fn-pth-i-output-spans spans ps s))
  (equal (fn-ptx-msg-byte i spans 1 1 (mv-nth 0 (fn-rtc-request r id inc s))) (fn-ptx-msg-byte i spans 1 1 s)))
 :hints (("Goal" :induct (fn-ptx-msg-byte i spans 1 1 s)
  :expand ((fn-pth-i-output-spans spans ps s))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-ptx-msg-byte fn-pth-i-output-spans fn-pth-i-output-span fn-pth-i-byte-foreign-request
     car-cons cdr-cons)))))
(defthm fn-pth-i-msg-range-foreign-request
 (implies (and (fn-pth-i-runtime s) (not (equal id 1)) (fn-pth-i-output-spans spans ps s))
  (equal (fn-ptx-msg-range i n spans 1 1 (mv-nth 0 (fn-rtc-request r id inc s))) (fn-ptx-msg-range i n spans 1 1 s)))
 :hints (("Goal" :induct (fn-ptx-msg-range i n spans 1 1 s)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-ptx-msg-range fn-pth-i-msg-byte-foreign-request car-cons cdr-cons)))))
(defthm fn-pth-i-message-foreign-request
 (implies (and (fn-pth-i-runtime s) (not (equal id 1)) (fn-pth-i-output-spans (fn-ptx-spans m) ps s))
  (equal (fn-ptx-message m 1 1 (mv-nth 0 (fn-rtc-request r id inc s))) (fn-ptx-message m 1 1 s)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-pth-i-msg-range-foreign-request (i 0) (n (fn-ptx-spans-len (fn-ptx-spans m))) (spans (fn-ptx-spans m))))
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth)) '(fn-ptx-message)))))
(defthm fn-pth-i-message-foreign-requests
 (implies (and (fn-pth-i-runtime s) (not (equal id 1)) (fn-pth-i-output-spans (fn-ptx-spans m) ps s))
  (equal (fn-ptx-message m 1 1 (mv-nth 0 (fn-rtc-requests rs id inc s))) (fn-ptx-message m 1 1 s)))
 :hints (("Goal" :induct (fn-rtc-requests rs id inc s)
  :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
   '(fn-rtc-requests fn-pth-i-runtime-request fn-pth-i-output-spans-foreign-request
     fn-pth-i-message-foreign-request fn-hld-mv-nth-0-cons car-cons cdr-cons)))))

(defthm fn-pth-i-message-config-pool-congruence
 (implies (and (equal (fn-rtc-config st) (fn-rtc-config s)) (equal (fn-rtc-pool st) (fn-rtc-pool s)))
  (equal (fn-ptx-message m 1 1 st) (fn-ptx-message m 1 1 s)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-ptx-msg-range-reads-view (i 0) (n (fn-ptx-spans-len (fn-ptx-spans m)))
          (spans (fn-ptx-spans m)) (id 1) (inc 1) (st st))
        (:instance fn-ptx-msg-range-reads-view (i 0) (n (fn-ptx-spans-len (fn-ptx-spans m)))
          (spans (fn-ptx-spans m)) (id 1) (inc 1) (st s)))
  :in-theory (union-theories (theory 'minimal-theory) '(fn-ptx-message fn-rtc-view-state fn-rtc-view)))))
(defthm fn-pth-owner-mstate-off-timer
 (implies (not (equal (fn-rtc-get 0 ev) :timer))
  (equal (mv-nth 0 (fn-ptx-step m ev st q)) (mv-nth 0 (fn-ptx-step m ev s q))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory (union-theories (theory 'minimal-theory)
   '(fn-ptx-step fn-ptx-step1-0 fn-ptx-end-0 car-cons cdr-cons mv-nth
     (:executable-counterpart zp) (:executable-counterpart nfix)
     (:executable-counterpart equal) (:executable-counterpart member-equal))))))
