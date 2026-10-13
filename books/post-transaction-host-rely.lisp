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
   (:acquire (and (< h (fn-rtc-nbufs (fn-rtc-config s)))
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


; A24 READY: the projection equals the actual machine REQS at the
; generated product step's slot-1 delivery sites.
; Extract the argument actually bound as REQS at FN-RTC-REQUESTS inside
; FN-PTH-DELIVER, then select it at each FN-PTH-STEP* delivery site.
(make-event
 (let* ((body (car (last (get-event 'fn-pth-step* (w state)))))
        (dispatch (cadddr (caddr body)))
        (bindings (cadr dispatch))
        (clauses (cdr (caddr dispatch)))
        (deliver-body (car (last (get-event 'fn-pth-deliver (w state)))))
        (machine-call (caddr deliver-body))
        (request-binding (cadr deliver-body))
        (accept-body (car (last (get-event 'fn-pth-accept-branch (w state)))))
        (accept-if (caddr accept-body))
        (accept-let (caddr accept-if))
        (accept-call (caddr (caddr accept-let))))
  (if (not (and (equal (car deliver-body) 'mv-let)
                (equal (cadr request-binding) 'reqs)
                (equal (car (caddr (cadddr deliver-body))) 'fn-rtc-requests)
                (equal (cadr (caddr (cadddr deliver-body))) 'reqs)))
      (er soft 'fn-pth-owner-requests-are-the-step-request-list "Delivery request site changed.")
   (value
    `(defthm fn-pth-owner-requests-are-the-step-request-list
      (implies (mv-nth 0 (fn-pth-owner-delivery s e q))
       (equal (fn-pth-owner-requests s e q)
        (let* ,(remove-assoc-eq 'base bindings)
         (cond
          ,@(loop$ for clause in clauses collect
           (let* ((arm (cadr clause)) (wrapped (eq (car arm) 'let*))
                  (delivery (if wrapped (caddr arm) arm)) (call (caddr delivery)))
            (list (car clause)
             (if (eq (car call) 'fn-pth-deliver)
              (let ((answer `(if (equal ,(caddr call) 1)
                              (mv-nth 1
                               ,(sublis (pairlis$ '(s id inc ev q) (cdr call)) machine-call)) nil)))
               (if wrapped `(let* ,(cadr arm) ,answer) answer))
              (if (eq (car call) 'fn-pth-accept-branch)
               `(let ,(cadr accept-body)
                 (if ,(cadr accept-if)
                  (let* ,(cadr accept-let)
                   (if (equal ,(caddr accept-call) 1)
                    (mv-nth 1
                     ,(sublis (pairlis$ '(s id inc ev q) (cdr accept-call)) machine-call)) nil)) nil))
               nil))))))))
      )
      :rule-classes nil
      :hints (("Goal" :do-not-induct t
        :in-theory (union-theories (theory 'minimal-theory)
                    '(fn-pth-owner-delivery fn-pth-owner-requests
                      fn-rtc-view-state fn-pthm-init fn-hlm-init
                      (:executable-counterpart fn-pthm-init)
                      mv-nth car-cons cdr-cons)))))))))

