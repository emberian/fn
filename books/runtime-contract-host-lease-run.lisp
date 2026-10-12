; fn: HL5, the host lease's run (Builder A): K windows of one leased ARTICLE response send, in order,
; exactly the windows the current path writes.
(in-package "ACL2")
(include-book "runtime-contract-host-lease")
(include-book "article-stream")

; K windows of one leased ARTICLE response: each window is rendered into fn-dss-out (fn-ast-render-window,
; exactly as books/article-stream.lisp fn-ast-render-run does), the quantum (fn-hld-quantum) copies it into
; the instance's workspace H and submits its send, and the socket completes the send (fn-hld-sent ... (:done n))
; before the next window.  The run collects the window of every quantum that SENT (op non-nil).
(defun fn-hld-render-run (window fuel octets k h id inc fn-arena fn-ast-ws fn-dss-out fn-rtc-st)
  (declare (xargs :stobjs (fn-arena fn-ast-ws fn-dss-out fn-rtc-st) :guard (and (natp fuel) (natp k))
                  :verify-guards nil :measure (nfix k)))
  (if (zp k)
      (mv window nil fn-ast-ws fn-dss-out fn-rtc-st)
    (mv-let (w2 fn-ast-ws fn-dss-out)
      (fn-ast-render-window window fuel octets fn-arena fn-ast-ws fn-dss-out)
      (mv-let (fn-rtc-st op n) (fn-hld-quantum h id inc fn-dss-out fn-rtc-st)
        (let ((sent (if op (fn-dss-out-list fn-dss-out) nil)))
          (mv-let (fn-rtc-st left)
            (if op (fn-hld-sent id inc op (list :done n) fn-rtc-st) (mv fn-rtc-st nil))
            (declare (ignore left))
            (mv-let (w3 rest fn-ast-ws fn-dss-out fn-rtc-st)
              (fn-hld-render-run w2 fuel octets (- k 1) h id inc fn-arena fn-ast-ws fn-dss-out fn-rtc-st)
              (mv w3 (append sent rest) fn-ast-ws fn-dss-out fn-rtc-st))))))))

;; ---------------------------------------------------------------------------------------------
;; HL5's proof.  The facts, in the order they are used:
;;  - the settle loop and the contract's step on a :grant, :pool or :send event keep the config, any
;;    workspace buffer, any live slot, and every absent :send use (fn-hlr-step-frames, fn-hlr-settle-frames);
;;  - one quantum on a nonempty octet window sends it (fn-hlr-quantum-succeeds), the completion of that
;;    send returns the buffer to its instance as its workspace (fn-hlr-end-use-send, fn-hlr-sent-restores),
;;    so the four state hypotheses hold again (fn-hlr-window, Lemma W);
;;  - an empty window is refused and leaves the state (fn-hlr-quantum-empty);
;;  - the run follows by induction on K (the last form).
(defthm fn-hlr-deliver-is-mstate
  (implies (not (equal (fn-rtc-get 0 ev) :accept))
           (and (equal (mv-nth 0 (fn-hll-deliver s id inc ev q)) (fn-rtc-with-mstate id nil s))
                (equal (mv-nth 1 (fn-hll-deliver s id inc ev q)) nil)))
  :hints (("Goal" :in-theory (union-theories '(fn-hll-deliver fn-hll-m-step fn-hlm-step fn-rtc-requests mv-nth (:e mv-nth) (:e fn-rtc-get)) (theory 'minimal-theory)))))


(defun fn-hlr-benign-actsp (acts)
  (declare (xargs :guard t))
  (if (consp acts)
      (and (member-eq (fn-rtc-get 0 (car acts)) '(:grant :pool :accept))
           (fn-hlr-benign-actsp (cdr acts)))
    (null acts)))
(defthm fn-hlr-benign-actsp-append
  (implies (and (fn-hlr-benign-actsp a) (fn-hlr-benign-actsp b)) (fn-hlr-benign-actsp (append a b))))
(defthm fn-hlr-rearm
  (and (implies (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses s)))
                (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses (mv-nth 0 (fn-rtc-rearm s))))))
       (fn-hlr-benign-actsp (mv-nth 1 (fn-rtc-rearm s))))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-rearm fn-rtc-arm-accept fn-rtc-arm-grant fn-rtc-issue-frame fn-rtc-kind-out-cons
                                               fn-hlr-benign-actsp fn-hlr-benign-actsp-append mv-nth (:e mv-nth) car-cons cdr-cons
                                               fn-rtc-get-of-cons (:e fn-rtc-get) (:e member-eq) append (:e append) (:e equal) (:e zp) zp (:e nfix) (:e unary--) (:e binary-+))
                                             (theory 'minimal-theory))
           :do-not-induct t)))


(defthm fn-hlr-mv-nth-1-cons (equal (mv-nth 1 (cons a (cons b c))) b))
(defthm fn-hlr-replace-nosend
  (implies (and (not (equal (fn-rtc-get 0 u2) :send)) (not (fn-rtc-kind-out-p :send id inc uses)))
           (not (fn-rtc-kind-out-p :send id inc (fn-rtc-replace-use k u2 uses))))
  :hints (("Goal" :induct (fn-rtc-replace-use k u2 uses)
           :in-theory (disable fn-rtc-key))))
(defthm fn-hlr-grant-one
  (and (implies (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses s)))
                (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses (mv-nth 0 (fn-rtc-grant-one s))))))
       (fn-hlr-benign-actsp (mv-nth 1 (fn-rtc-grant-one s))))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-grant-one fn-hlr-benign-actsp fn-hlr-replace-nosend fn-rtc-with-accessors mv-nth (:e mv-nth) car-cons cdr-cons fn-rtc-get-of-cons (:e fn-rtc-get) (:e member-eq) (:e equal) (:e zp) (:e nfix) (:e unary--) (:e binary-+) zp nfix) (set-difference-theories (theory 'minimal-theory) '(mv-nth))))))
(defthm fn-hlr-grant2
  (and (implies (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses s)))
                (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses (mv-nth 0 (fn-rtc-grant n s))))))
       (fn-hlr-benign-actsp (mv-nth 1 (fn-rtc-grant n s))))
  :hints (("Goal" :induct (fn-rtc-grant n s)
           :in-theory (union-theories '(fn-rtc-grant fn-hld-mv-nth-0-cons fn-hlr-mv-nth-1-cons (:e consp) (:e null) null fn-hlr-benign-actsp fn-hlr-benign-actsp-append fn-hlr-grant-one (:e zp) zp) (set-difference-theories (theory 'minimal-theory) '(mv-nth))))
          ("Subgoal *1/2" :use ((:instance fn-hlr-grant-one)))))


(defthm fn-hlr-remove-nosend
  (implies (not (fn-rtc-kind-out-p k id inc uses))
           (not (fn-rtc-kind-out-p k id inc (fn-rtc-remove-use key uses))))
  :hints (("Goal" :induct (fn-rtc-remove-use key uses) :in-theory (disable fn-rtc-key))))
(defthm fn-hlr-end-use-nosend
  (implies (not (fn-rtc-kind-out-p k id inc (fn-rtc-uses s)))
           (not (fn-rtc-kind-out-p k id inc (fn-rtc-uses (fn-rtc-end-use s e)))))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-end-use fn-rtc-retire-drained fn-rtc-end-lease fn-hlr-remove-nosend fn-rtc-with-accessors)
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :do-not-induct t)
          ("Subgoal 4" :in-theory (enable fn-rtc-with-slot fn-rtc-with-buffer))))


(defthm fn-hlr-step-acts-config4
  (implies (member-eq (fn-rtc-get 0 e) '(:grant :pool :send))
           (and (fn-hlr-benign-actsp (mv-nth 1 (fn-hll-step* s e q)))
                (equal (fn-rtc-config (mv-nth 0 (fn-hll-step* s e q))) (fn-rtc-config s))))
  :hints (("Goal" :do-not-induct t :cases ((equal (fn-rtc-get 0 e) :grant) (equal (fn-rtc-get 0 e) :pool) (equal (fn-rtc-get 0 e) :send))
           :in-theory (union-theories '(fn-hll-step* fn-hlr-rearm fn-hlr-grant2 fn-hlr-deliver-is-mstate fn-rtc-rearm-frame fn-rtc-grant-frame
                                        fn-rtc-config-of-end-use fn-rtc-with-accessors fn-hlr-benign-actsp-append fn-rtc-e-kind fn-rtc-ev fn-rtc-hand-delivers-p (:e member-equal) member-equal
                                        fn-hld-mv-nth-0-cons fn-hlr-mv-nth-1-cons (:e fn-rtc-get) (:e member-eq) (:e equal) car-cons cdr-cons (:e zp) (:e nfix) zp nfix
                                        fn-rtc-get-of-cons fn-hlr-benign-actsp (:e consp) (:e null) null)
                                      (set-difference-theories (theory 'minimal-theory) '(mv-nth))))))


(defthm fn-hlr-step-frames
  (implies (and (fn-hll-invp s) (member-eq (fn-rtc-get 0 e) '(:grant :pool :send)))
           (and (implies (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses s)))
                         (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses (mv-nth 0 (fn-hll-step* s e q))))))
                (implies (equal (fn-rtc-get 0 (fn-rtc-b-owner (fn-rtc-buffer k s))) :workspace)
                         (equal (fn-rtc-buffer k (mv-nth 0 (fn-hll-step* s e q))) (fn-rtc-buffer k s)))
                (implies (and (natp j) (equal (fn-rtc-s-status (fn-rtc-slot j s)) :live))
                         (equal (fn-rtc-slot j (mv-nth 0 (fn-hll-step* s e q))) (fn-rtc-slot j s)))))
  :hints (("Goal" :do-not-induct t :cases ((equal (fn-rtc-get 0 e) :grant) (equal (fn-rtc-get 0 e) :pool) (equal (fn-rtc-get 0 e) :send))
           :in-theory (union-theories '(fn-hll-step* fn-hlr-rearm fn-hlr-grant2 fn-hlr-deliver-is-mstate fn-rtc-rearm-frame fn-rtc-grant-frame
                                        fn-hlr-end-use-nosend fn-rtc-end-use-keeps-workspaces fn-hld-hll-invp-is-generic-invp fn-rtc-grant-keeps-workspaces
                                        fn-rtc-live-slot-of-end-use fn-rtc-slot-of-rearm fn-rtc-buffer-of-with fn-rtc-slot-of-with
                                        fn-rtc-with-accessors fn-hlr-benign-actsp-append fn-rtc-e-kind fn-rtc-ev fn-rtc-hand-delivers-p (:e member-equal) member-equal
                                        fn-hld-mv-nth-0-cons fn-hlr-mv-nth-1-cons (:e fn-rtc-get) (:e member-eq) (:e equal) car-cons cdr-cons (:e zp) (:e nfix) zp nfix
                                        fn-rtc-get-of-cons fn-hlr-benign-actsp (:e consp) (:e null) null)
                                      (set-difference-theories (theory 'minimal-theory) '(mv-nth))))))


(defthm fn-hlr-landed-kind
  (equal (fn-rtc-get 0 (fn-rtc-landed e s)) (fn-rtc-get 0 e))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-landed fn-rtc-get-of-cons car-cons (:e zp) (:e nfix) zp nfix) (theory 'minimal-theory)))))
(defthm fn-hlr-benign-tlf
  (implies (fn-hlr-benign-actsp x) (equal (true-list-fix x) x))
  :hints (("Goal" :in-theory (enable fn-hlr-benign-actsp))))
(defthm fn-hlr-benign-cdr
  (implies (and (fn-hlr-benign-actsp x) (consp x)) (fn-hlr-benign-actsp (cdr x)))
  :hints (("Goal" :in-theory (enable fn-hlr-benign-actsp))))
(defthm fn-hlr-xstep-frames
  (implies (and (fn-hll-invp st) (member-eq (fn-rtc-get 0 e) '(:grant :pool :send)))
           (and (fn-hlr-benign-actsp (mv-nth 1 (fn-hll-x-step* e q st)))
                (equal (fn-rtc-config (mv-nth 0 (fn-hll-x-step* e q st))) (fn-rtc-config st))
                (implies (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses st)))
                         (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses (mv-nth 0 (fn-hll-x-step* e q st))))))
                (implies (equal (fn-rtc-get 0 (fn-rtc-b-owner (fn-rtc-buffer k st))) :workspace)
                         (equal (fn-rtc-buffer k (mv-nth 0 (fn-hll-x-step* e q st))) (fn-rtc-buffer k st)))
                (implies (and (natp j) (equal (fn-rtc-s-status (fn-rtc-slot j st)) :live))
                         (equal (fn-rtc-slot j (mv-nth 0 (fn-hll-x-step* e q st))) (fn-rtc-slot j st)))))
  :hints (("Goal" :in-theory (union-theories '(fn-hll-x-step*-is fn-hld-hll-invp-st-p fn-hlr-step-frames fn-hlr-step-acts-config4 fn-hlr-landed-kind)
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth))))))
(defthm fn-hlr-settle-frames
  (implies (and (fn-hll-invp st) (fn-hlr-benign-actsp work))
           (and (equal (fn-rtc-config (mv-nth 0 (fn-hld-settle work fuel st))) (fn-rtc-config st))
                (implies (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses st)))
                         (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses (mv-nth 0 (fn-hld-settle work fuel st))))))
                (implies (equal (fn-rtc-get 0 (fn-rtc-b-owner (fn-rtc-buffer k st))) :workspace)
                         (equal (fn-rtc-buffer k (mv-nth 0 (fn-hld-settle work fuel st))) (fn-rtc-buffer k st)))
                (implies (and (natp j) (equal (fn-rtc-s-status (fn-rtc-slot j st)) :live))
                         (equal (fn-rtc-slot j (mv-nth 0 (fn-hld-settle work fuel st))) (fn-rtc-slot j st)))))
  :hints (("Goal" :induct (fn-hld-settle work fuel st)
           :in-theory (union-theories '((:induction fn-hld-settle) fn-hld-settle fn-hlr-xstep-frames
                                        fn-hld-x-step*-keeps-invp fn-hlr-benign-tlf fn-hlr-benign-cdr
                                        fn-hlr-benign-actsp-append fn-hlr-benign-actsp
                                        fn-hld-mv-nth-0-cons fn-hlr-mv-nth-1-cons (:e fn-rtc-get) (:e member-eq) (:e equal) car-cons cdr-cons (:e zp) (:e nfix) zp nfix
                                        fn-rtc-get-of-cons (:e consp) (:e null) null member-equal (:e member-equal))
                                      (set-difference-theories (theory 'minimal-theory) '(mv-nth))))))


(defthm fn-hlr-submit-okp-send
  (implies (and (natp h) (< h (fn-rtc-nbufs (fn-rtc-config p)))
                (equal (fn-rtc-b-owner (fn-rtc-buffer h p)) (list :workspace id inc))
                (natp g) (equal (fn-rtc-b-gen (fn-rtc-buffer h p)) g)
                (natp n) (<= n (len (fn-rtc-b-bytes (fn-rtc-buffer h p))))
                (<= n (fn-rtc-buf-cap h (fn-rtc-config p))))
           (fn-rtc-submit-okp :send (list h g 0 n) id inc p))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-submit-okp fn-rtc-handlep fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len
                                               fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e member-eq) (:e equal) (:e zp) (:e nfix) zp nfix natp
                                               (:e len) (:e true-listp) true-listp len (:e <) (:e +) (:e unary--) (:e binary-+)
                                               (:type-prescription len) (:e consp) (:e fn-rtc-get) (:e member-equal) member-equal
                                              )
                                             (theory 'minimal-theory)))))
(defthm fn-hlr-next-op-of-with-buffer
  (equal (fn-rtc-next-op (fn-rtc-with-buffer h b s)) (fn-rtc-next-op s))
  :hints (("Goal" :in-theory (enable fn-rtc-with-buffer fn-rtc-make fn-rtc-next-op))))
(defthm fn-hlr-submit-send
  (implies (and (natp h) (< h (fn-rtc-nbufs (fn-rtc-config p)))
                (equal (fn-rtc-b-owner (fn-rtc-buffer h p)) (list :workspace id inc))
                (natp g) (equal (fn-rtc-b-gen (fn-rtc-buffer h p)) g)
                (fn-rtc-live-p id inc p)
                (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses p)))
                (natp n) (<= n (len (fn-rtc-b-bytes (fn-rtc-buffer h p))))
                (<= n (fn-rtc-buf-cap h (fn-rtc-config p))))
           (and (not (mv-nth 2 (fn-rtc-req-submit (list :submit :send (list h g 0 n) nil) id inc p)))
                (equal (mv-nth 0 (fn-rtc-req-submit (list :submit :send (list h g 0 n) nil) id inc p))
                       (fn-rtc-issue (list :send id inc (fn-rtc-next-op p) (list h g 0 n))
                                     (fn-rtc-with-buffer h (list g (list :leased id inc :out) (fn-rtc-b-bytes (fn-rtc-buffer h p))) p)))))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-req-submit fn-hlr-submit-okp-send fn-rtc-buffered-kind-p fn-rtc-kind-extrap fn-rtc-extrap
                                               fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e member-eq) (:e equal) (:e zp) (:e nfix) zp nfix natp
                                               (:e len) (:e true-listp) true-listp len (:e <) (:e +) (:e unary--) (:e binary-+) (:e consp) (:e member-equal) member-equal
                                               fn-rtc-with-accessors fn-hlr-next-op-of-with-buffer fn-rtc-h-buf (:e fn-rtc-h-buf)
                                               mv-nth (:e mv-nth) (:e eq) eq (:e atom) atom (:e implies) implies)
                                             (theory 'minimal-theory)))))
(defthm fn-hlr-submit-send-facts
  (implies (and (natp h) (< h (fn-rtc-nbufs (fn-rtc-config p))) (< h (len (fn-rtc-pool p)))
                (equal (fn-rtc-b-owner (fn-rtc-buffer h p)) (list :workspace id inc))
                (natp g) (equal (fn-rtc-b-gen (fn-rtc-buffer h p)) g)
                (fn-rtc-live-p id inc p)
                (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses p)))
                (natp n) (<= n (len (fn-rtc-b-bytes (fn-rtc-buffer h p))))
                (<= n (fn-rtc-buf-cap h (fn-rtc-config p))))
           (let ((q (mv-nth 0 (fn-rtc-req-submit (list :submit :send (list h g 0 n) nil) id inc p))))
             (and (not (mv-nth 2 (fn-rtc-req-submit (list :submit :send (list h g 0 n) nil) id inc p)))
                  (equal (fn-rtc-uses q) (cons (list :send id inc (fn-rtc-next-op p) (list h g 0 n)) (fn-rtc-uses p)))
                  (equal (fn-rtc-b-owner (fn-rtc-buffer h q)) (list :leased id inc :out))
                  (equal (fn-rtc-b-gen (fn-rtc-buffer h q)) g)
                  (equal (fn-rtc-slots q) (fn-rtc-slots p))
                  (equal (fn-rtc-config q) (fn-rtc-config p))
                  (equal (fn-rtc-next-op q) (+ 1 (fn-rtc-next-op p))))))
  :hints (("Goal" :use fn-hlr-submit-send
           :in-theory (union-theories '(fn-rtc-issue-frame fn-rtc-with-accessors fn-rtc-buffer-of-with fn-hlr-next-op-of-with-buffer
                                        fn-rtc-b-owner fn-rtc-b-gen fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) zp nfix natp)
                                      (set-difference-theories (theory 'minimal-theory) '(mv-nth))))))


(defthm fn-hlr-len-splice-ge
  (implies (and (natp off) (<= off (len bytes)))
           (<= (+ off (len data)) (len (fn-rtc-splice bytes off data))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (fn-rtc-splice) (take nthcdr)))))
(defthm fn-hlr-splice-okp-natp
  (implies (fn-rtc-splice-okp h off data s) (natp h))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-rtc-splice-okp))))
(defthm fn-hlr-get-nfix-b (equal (fn-rtc-get (nfix i) l) (fn-rtc-get i l))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-rtc-get))))
(defthm fn-hlr-buffer-nfix (equal (fn-rtc-buffer (nfix k) s) (fn-rtc-buffer k s))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-buffer) (theory 'minimal-theory))
           :use ((:instance fn-hlr-get-nfix-b (i k) (l (fn-rtc-pool s)))))))
(defthm fn-hlr-put-frame2
  (implies (natp h) (and (equal (fn-rtc-uses (fn-rtc-st$a-put h off o s)) (fn-rtc-uses s))
       (equal (fn-rtc-slots (fn-rtc-st$a-put h off o s)) (fn-rtc-slots s))
       (equal (fn-rtc-config (fn-rtc-st$a-put h off o s)) (fn-rtc-config s))
       (equal (fn-rtc-next-op (fn-rtc-st$a-put h off o s)) (fn-rtc-next-op s))
       (equal (fn-rtc-b-owner (fn-rtc-buffer k (fn-rtc-st$a-put h off o s))) (fn-rtc-b-owner (fn-rtc-buffer k s)))
       (equal (fn-rtc-b-gen (fn-rtc-buffer k (fn-rtc-st$a-put h off o s))) (fn-rtc-b-gen (fn-rtc-buffer k s)))))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-st$a-put fn-rtc-st$a-splice fn-rtc-with-accessors fn-rtc-buffer-of-with fn-hlr-next-op-of-with-buffer
                                               fn-rtc-b-owner fn-rtc-b-gen fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) zp nfix fn-hlr-buffer-nfix fn-hlr-splice-okp-natp natp fn-rtc-buffer-of-non-natp)
                                             (theory 'minimal-theory)))))


(defthm fn-hlr-len-of-set (equal (len (fn-rtc-set j v l)) (len l))
  :hints (("Goal" :in-theory (enable fn-rtc-set))))
(defthm fn-hlr-put-pool-len
  (implies (natp h)
           (equal (len (fn-rtc-pool (fn-rtc-st$a-put h off o s))) (len (fn-rtc-pool s))))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-st$a-put fn-rtc-st$a-splice fn-rtc-with-accessors fn-hlr-len-of-set) (theory 'minimal-theory)))))
(defthm fn-hlr-put-len
  (implies (and (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s))) (< h (len (fn-rtc-pool s)))
                (equal (fn-rtc-get 0 (fn-rtc-b-owner (fn-rtc-buffer h s))) :workspace)
                (natp off) (<= off (len (fn-rtc-b-bytes (fn-rtc-buffer h s))))
                (fn-cbor-octetp o) (<= (+ 1 off) (fn-rtc-buf-cap h (fn-rtc-config s))))
           (<= (+ 1 off) (len (fn-rtc-b-bytes (fn-rtc-buffer h (fn-rtc-st$a-put h off o s))))))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-st$a-put fn-rtc-st$a-splice fn-rtc-splice-okp fn-rtc-splice-target-p fn-rtc-with-accessors fn-rtc-buffer-of-with
                                               fn-hlr-len-splice-ge fn-rtc-b-bytes fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) zp nfix natp
                                               (:e len) len (:e consp) fn-cbor-octet-listp (:e fn-cbor-octet-listp) (:e true-listp))
                                             (theory 'minimal-theory)))))
(defthm fn-hlr-puts-frame
  (implies (natp h)
           (and (equal (fn-rtc-uses (fn-rtc-st$a-puts h off w s)) (fn-rtc-uses s))
                (equal (fn-rtc-slots (fn-rtc-st$a-puts h off w s)) (fn-rtc-slots s))
                (equal (fn-rtc-config (fn-rtc-st$a-puts h off w s)) (fn-rtc-config s))
                (equal (fn-rtc-next-op (fn-rtc-st$a-puts h off w s)) (fn-rtc-next-op s))
                (equal (len (fn-rtc-pool (fn-rtc-st$a-puts h off w s))) (len (fn-rtc-pool s)))
                (equal (fn-rtc-b-owner (fn-rtc-buffer k (fn-rtc-st$a-puts h off w s))) (fn-rtc-b-owner (fn-rtc-buffer k s)))
                (equal (fn-rtc-b-gen (fn-rtc-buffer k (fn-rtc-st$a-puts h off w s))) (fn-rtc-b-gen (fn-rtc-buffer k s)))))
  :hints (("Goal" :induct (fn-rtc-st$a-puts h off w s)
           :in-theory (union-theories '((:induction fn-rtc-st$a-puts) fn-rtc-st$a-puts fn-hlr-put-frame2 fn-hlr-put-pool-len) (theory 'minimal-theory)))))
(defthm fn-hlr-len-nonneg (<= 0 (len x)) :rule-classes :linear)
(defthm fn-hlr-puts-len2
  (implies (and (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s))) (< h (len (fn-rtc-pool s)))
                (equal (fn-rtc-get 0 (fn-rtc-b-owner (fn-rtc-buffer h s))) :workspace)
                (natp off) (<= off (len (fn-rtc-b-bytes (fn-rtc-buffer h s))))
                (fn-cbor-octet-listp w) (<= (+ off (len w)) (fn-rtc-buf-cap h (fn-rtc-config s))))
           (<= (+ off (len w)) (len (fn-rtc-b-bytes (fn-rtc-buffer h (fn-rtc-st$a-puts h off w s))))))
  :hints (("Goal" :induct (fn-rtc-st$a-puts h off w s)
           :in-theory (union-theories '((:induction fn-rtc-st$a-puts) fn-rtc-st$a-puts fn-hlr-put-frame2 fn-hlr-put-pool-len fn-hlr-put-len fn-hlr-puts-frame fn-hlr-len-nonneg
                                        fn-cbor-octet-listp (:e len) len natp nfix (:e nfix) (:e zp) zp car-cons cdr-cons (:e consp))
                                      (theory 'minimal-theory)))))


(defthm fn-hlr-buffer-facts
  (implies (and (fn-rtc-invp s) (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s))))
           (and (natp (fn-rtc-b-gen (fn-rtc-buffer h s)))
                (fn-cbor-octet-listp (fn-rtc-b-bytes (fn-rtc-buffer h s)))
                (<= (len (fn-rtc-b-bytes (fn-rtc-buffer h s))) (fn-rtc-buf-cap h (fn-rtc-config s)))))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-buffer-okp fn-rtc-bufferp fn-rtc-b-gen fn-rtc-b-bytes (:type-prescription nfix) natp) (theory 'minimal-theory))
           :use (fn-rtc-invp-implies-core-invp fn-rtc-core-invp-buffer))))
(defthm fn-hlr-pool-len-facts
  (implies (fn-rtc-invp s) (equal (len (fn-rtc-pool s)) (fn-rtc-nbufs (fn-rtc-config s)))))
(defthm fn-hlr-live-of-slots
  (implies (equal (fn-rtc-slots a) (fn-rtc-slots b))
           (equal (fn-rtc-live-p id inc a) (fn-rtc-live-p id inc b)))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-live-p fn-rtc-slot) (theory 'minimal-theory)))))
(defthm fn-hlr-live-of-puts
  (implies (natp h) (equal (fn-rtc-live-p id inc (fn-rtc-st$a-puts h off w s)) (fn-rtc-live-p id inc s)))
  :hints (("Goal" :in-theory (union-theories '(fn-hlr-live-of-slots fn-hlr-puts-frame) (theory 'minimal-theory))
           :use ((:instance fn-hlr-live-of-slots (a (fn-rtc-st$a-puts h off w s)) (b s))))))
(defthm fn-hlr-fix-len (equal (fix (len x)) (len x)))
(defthm fn-hlr-pure-quantum
  (implies (and (fn-rtc-invp s) (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
                (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) (list :workspace id inc))
                (fn-rtc-live-p id inc s)
                (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses s)))
                (consp out) (fn-cbor-octet-listp out)
                (<= (len out) (fn-rtc-buf-cap h (fn-rtc-config s))))
           (let* ((g (fn-rtc-b-gen (fn-rtc-buffer h s)))
                  (p (fn-rtc-st$a-puts h 0 out s))
                  (q (mv-nth 0 (fn-rtc-req-submit (list :submit :send (list h g 0 (len out)) nil) id inc p))))
             (and (not (mv-nth 2 (fn-rtc-req-submit (list :submit :send (list h g 0 (len out)) nil) id inc p)))
                  (equal (fn-rtc-uses q) (cons (list :send id inc (fn-rtc-next-op s) (list h g 0 (len out))) (fn-rtc-uses s)))
                  (equal (fn-rtc-b-owner (fn-rtc-buffer h q)) (list :leased id inc :out))
                  (equal (fn-rtc-b-gen (fn-rtc-buffer h q)) g)
                  (equal (fn-rtc-slots q) (fn-rtc-slots s))
                  (equal (fn-rtc-config q) (fn-rtc-config s))
                  (equal (fn-rtc-next-op q) (+ 1 (fn-rtc-next-op s))))))
  :hints (("Goal" :use ((:instance fn-hlr-submit-send-facts (p (fn-rtc-st$a-puts h 0 out s)) (g (fn-rtc-b-gen (fn-rtc-buffer h s))) (n (len out))) (:instance fn-hlr-puts-len2 (off 0) (w out)) (:instance fn-hlr-pool-len-facts) (:instance fn-hlr-buffer-facts))
           :in-theory (union-theories '(fn-hlr-puts-frame fn-hlr-puts-len2 fn-hlr-submit-send-facts fn-hlr-buffer-facts fn-hlr-pool-len-facts
                                               fn-hlr-live-of-puts fn-hlr-fix-len unicity-of-0 natp (:e natp) fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) zp nfix (:e len) len (:e consp)
                                               fn-hlr-len-nonneg (:type-prescription len))
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth))))))


(defthm fn-hlr-len-pos (implies (consp x) (< 0 (len x))) :rule-classes :linear)
(defthm fn-hlr-quantum-succeeds
  (implies (and (fn-hll-invp st) (fn-hl-render-ready-p h id inc st) (fn-rtc-live-p id inc st)
                (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses st)))
                (consp out) (fn-dss-out-p out)
                (<= (len out) (fn-rtc-buf-cap h (fn-rtc-config st))))
           (let ((q (mv-nth 0 (fn-hld-quantum h id inc out st))) (g (fn-rtc-b-gen (fn-rtc-buffer h st))))
             (and (equal (mv-nth 1 (fn-hld-quantum h id inc out st)) (fn-rtc-next-op st))
                  (equal (mv-nth 2 (fn-hld-quantum h id inc out st)) (len out))
                  (equal (fn-rtc-uses q) (cons (list :send id inc (fn-rtc-next-op st) (list h g 0 (len out))) (fn-rtc-uses st)))
                  (equal (fn-rtc-b-owner (fn-rtc-buffer h q)) (list :leased id inc :out))
                  (equal (fn-rtc-b-gen (fn-rtc-buffer h q)) g)
                  (equal (fn-rtc-slots q) (fn-rtc-slots st))
                  (equal (fn-rtc-config q) (fn-rtc-config st))
                  (equal (fn-rtc-next-op q) (+ 1 (fn-rtc-next-op st))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-hld-quantum fn-dss-out-len-is-len fn-hld-readers fn-rtc-x-live-p-is fn-hl-render-ready-p
                                        (:e len) (:e <) (:e zp) (:e nfix) car-cons cdr-cons fn-hlr-len-nonneg fn-hlr-len-pos
                                        fn-hld-nthcdr-0 natp fn-rtc-request (:e fn-rtc-get) fn-rtc-get-of-cons
                                        fn-hld-hll-invp-is-generic-invp fn-hld-hll-invp-st-p fn-dss-out-p-is-octet-listp)
                                      (set-difference-theories (theory 'minimal-theory) '(mv-nth)))
           :use ((:instance fn-hld-copy-is-puts (i 0))
                 (:instance fn-hld-puts-keeps-st-p (off 0) (w out))
                 (:instance fn-rtc-x-request-is (r (list :submit :send (list h (fn-rtc-b-gen (fn-rtc-buffer h st)) 0 (len out)) nil))
                            (fn-rtc-st (fn-rtc-st$a-puts h 0 out st)))
                 (:instance fn-hlr-pure-quantum (s st))
                 (:instance fn-hlr-live-of-puts (off 0) (w out) (s st))))))


(defthm fn-hlr-live-natp-inc
  (implies (fn-rtc-live-p id inc s) (natp inc))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-live-p fn-rtc-s-inc (:type-prescription nfix) natp) (theory 'minimal-theory)))))
(defthm fn-hlr-ws-posp-id
  (implies (and (fn-rtc-invp s) (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
                (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) (list :workspace id inc)))
           (posp id))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-buffer-okp posp nfix natp fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) zp)
                                             (theory 'minimal-theory))
           :use (fn-rtc-invp-implies-core-invp fn-rtc-core-invp-buffer))))
(defun fn-hlr-no-h (h uses)
  (declare (xargs :guard t))
  (if (consp uses)
      (and (not (and (fn-rtc-handlep (fn-rtc-u-hd (car uses))) (equal (fn-rtc-h-buf (fn-rtc-u-hd (car uses))) h)))
           (fn-hlr-no-h h (cdr uses)))
    t))
(defthm fn-hlr-no-h-not-holds
  (implies (fn-hlr-no-h h uses) (not (fn-rtc-holds-p h g uses)))
  :hints (("Goal" :in-theory (disable fn-rtc-handlep fn-rtc-u-hd fn-rtc-h-buf fn-rtc-h-gen))))
(defthm fn-hlr-ws-use-not-h
  (implies (and (fn-rtc-invp s) (member-equal u (fn-rtc-uses s)) (fn-rtc-handlep (fn-rtc-u-hd u))
                (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) (list :workspace id inc)))
           (not (equal (fn-rtc-h-buf (fn-rtc-u-hd u)) h)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use (fn-rtc-leasedp-of-use (:instance fn-rtc-workspace-not-leased)))))
(defun fn-hlr-ind (us) (declare (xargs :guard t)) (if (consp us) (fn-hlr-ind (cdr us)) us))
(defthm fn-hlr-ws-no-h
  (implies (and (fn-rtc-invp s) (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) (list :workspace id inc))
                (subsetp-equal us (fn-rtc-uses s)))
           (fn-hlr-no-h h us))
  :hints (("Goal" :induct (fn-hlr-ind us)
           :in-theory (union-theories '(fn-hlr-no-h subsetp-equal fn-hlr-ws-use-not-h (:induction fn-hlr-ind) car-cons cdr-cons) (theory 'minimal-theory)))))
(defthm fn-hlr-subsetp-refl (subsetp-equal x x))
(defthm fn-hlr-ws-not-holds
  (implies (and (fn-rtc-invp s) (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) (list :workspace id inc)))
           (not (fn-rtc-holds-p h g (fn-rtc-uses s))))
  :hints (("Goal" :in-theory (union-theories '(fn-hlr-no-h-not-holds fn-hlr-ws-no-h) (theory 'minimal-theory))
           :use ((:instance fn-hlr-ws-no-h (us (fn-rtc-uses s))) (:instance fn-hlr-subsetp-refl (x (fn-rtc-uses s)))))))


(defthm fn-hlr-key-of-send
  (equal (fn-rtc-key (list :send id inc op x)) (list :send id inc op))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-key fn-rtc-get-of-cons car-cons cdr-cons (:e zp) (:e nfix) zp nfix) (theory 'minimal-theory)))))
(defthm fn-hlr-retire-keeps
  (and (equal (fn-rtc-uses (fn-rtc-retire-drained i s)) (fn-rtc-uses s))
       (equal (fn-rtc-buffer h (fn-rtc-retire-drained i s)) (fn-rtc-buffer h s)))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-retire-drained fn-rtc-with-accessors fn-rtc-buffer-of-with) (theory 'minimal-theory)))))
(defthm fn-hlr-end-lease-send
  (implies (and (natp id) (natp inc) (natp h) (natp g) (natp n) (< h (len (fn-rtc-pool s)))
                (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) (list :leased id inc :out))
                (equal (fn-rtc-b-gen (fn-rtc-buffer h s)) g)
                (fn-rtc-live-p id inc s)
                (not (fn-rtc-holds-p h g (fn-rtc-uses s))))
           (and (equal (fn-rtc-uses (fn-rtc-end-lease (list :send id inc op (list h g 0 n)) e s)) (fn-rtc-uses s))
                (equal (fn-rtc-b-owner (fn-rtc-buffer h (fn-rtc-end-lease (list :send id inc op (list h g 0 n)) e s)))
                       (list :workspace id inc))))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-end-lease fn-rtc-lease-return fn-rtc-u-hd fn-rtc-handlep fn-rtc-h-buf fn-rtc-h-gen
                                               fn-rtc-with-accessors fn-rtc-buffer-of-with fn-rtc-handed-to-live-p fn-rtc-current-p fn-rtc-live-p
                                               fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) zp nfix natp (:e member-eq) member-eq (:e equal)
                                               fn-rtc-b-owner fn-rtc-b-gen (:type-prescription nfix) (:e consp) (:e len) len)
                                             (theory 'minimal-theory)))))
(defthm fn-hlr-completionp-send
  (implies (and (natp id) (natp inc) (natp op) (natp n))
           (fn-rtc-completionp (list :send id inc op (list :done n))))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-completionp fn-rtc-outcomep fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) zp nfix
                                               natp (:e member-eq) member-eq (:e equal) (:e len) len (:e true-listp) true-listp (:e consp) (:e fn-rtc-get))
                                             (theory 'minimal-theory)))))
(defthm fn-hlr-find-use-send
  (equal (fn-rtc-find-use (list :send id inc op) (cons (list :send id inc op x) uses0)) (list :send id inc op x))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-find-use fn-hlr-key-of-send car-cons cdr-cons) (theory 'minimal-theory)))))
(defthm fn-hlr-remove-use-send
  (equal (fn-rtc-remove-use (list :send id inc op) (cons (list :send id inc op x) uses0)) uses0)
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-remove-use fn-hlr-key-of-send car-cons cdr-cons) (theory 'minimal-theory)))))
(defthm fn-hlr-end-use-send-eq
  (implies (and (equal (fn-rtc-uses q) (cons (list :send id inc op (list h g 0 n)) uses0))
                (natp id) (natp inc) (natp op) (natp n))
           (equal (fn-rtc-end-use q (list :send id inc op (list :done n)))
                  (fn-rtc-retire-drained id (fn-rtc-end-lease (list :send id inc op (list h g 0 n)) (list :send id inc op (list :done n))
                                                              (fn-rtc-with-uses uses0 q)))))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-end-use-structure fn-hlr-key-of-send fn-hlr-completionp-send fn-hlr-find-use-send fn-hlr-remove-use-send
                                               fn-rtc-e-id fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) zp nfix (:e equal)
                                               natp)
                                             (theory 'minimal-theory))
           :use ((:instance fn-rtc-end-use-structure (s q) (e (list :send id inc op (list :done n))))
                 (:instance fn-hlr-find-use-send (x (list h g 0 n)))
                 (:instance fn-hlr-remove-use-send (x (list h g 0 n)))
                 (:instance fn-hlr-key-of-send (x (list :done n)))
                 fn-hlr-completionp-send))))
(defthm fn-hlr-live-of-with-uses
  (equal (fn-rtc-live-p id inc (fn-rtc-with-uses u s)) (fn-rtc-live-p id inc s))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-live-p fn-rtc-slot fn-rtc-with-accessors) (theory 'minimal-theory)))))
(defthm fn-hlr-end-use-send
  (implies (and (equal (fn-rtc-uses q) (cons (list :send id inc op (list h g 0 n)) uses0))
                (natp id) (natp inc) (natp op) (natp h) (natp g) (natp n) (< h (len (fn-rtc-pool q)))
                (equal (fn-rtc-b-owner (fn-rtc-buffer h q)) (list :leased id inc :out))
                (equal (fn-rtc-b-gen (fn-rtc-buffer h q)) g)
                (fn-rtc-live-p id inc q)
                (not (fn-rtc-holds-p h g uses0)))
           (and (equal (fn-rtc-uses (fn-rtc-end-use q (list :send id inc op (list :done n)))) uses0)
                (equal (fn-rtc-b-owner (fn-rtc-buffer h (fn-rtc-end-use q (list :send id inc op (list :done n)))))
                       (list :workspace id inc))))
  :hints (("Goal" :in-theory (union-theories '(fn-hlr-end-use-send-eq fn-hlr-retire-keeps fn-hlr-end-lease-send fn-rtc-with-accessors fn-rtc-buffer-of-with fn-hlr-live-of-with-uses natp)
                                             (theory 'minimal-theory)))))


(defthm fn-hlr-landed-send
  (implies (equal (fn-rtc-uses q) (cons (list :send id inc op x) uses0))
           (equal (fn-rtc-landed (list :send id inc op o) q) (list :send id inc op o)))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-landed fn-hlr-find-use-send fn-hlr-key-of-send fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) zp nfix
                                               (:e member-eq) member-eq (:e equal))
                                             (theory 'minimal-theory)))))
(defthm fn-hlr-acts-on-send
  (implies (and (equal (fn-rtc-uses q) (cons (list :send id inc op x) uses0))
                (natp id) (natp inc) (natp op) (natp n)
                (fn-rtc-live-p id inc q))
           (fn-rtc-acts-on-p q (list :send id inc op (list :done n))))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-acts-on-p fn-hlr-completionp-send fn-hlr-key-of-send fn-hlr-find-use-send fn-rtc-live-p
                                               fn-rtc-e-id fn-rtc-e-inc fn-rtc-e-kind fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) zp nfix natp
                                               (:e equal))
                                             (theory 'minimal-theory))
           :use ((:instance fn-hlr-find-use-send (uses0 uses0))))))
(defthm fn-hlr-step-send
  (implies (and (equal (fn-rtc-uses q) (cons (list :send id inc op (list h g 0 n)) uses0))
                (natp id) (natp inc) (natp op) (natp h) (natp g) (natp n) (< h (len (fn-rtc-pool q)))
                (equal (fn-rtc-b-owner (fn-rtc-buffer h q)) (list :leased id inc :out))
                (equal (fn-rtc-b-gen (fn-rtc-buffer h q)) g)
                (fn-rtc-live-p id inc q)
                (not (fn-rtc-holds-p h g uses0))
                (not (fn-rtc-kind-out-p :send id inc uses0)))
           (let ((s2 (mv-nth 0 (fn-hll-step* q (list :send id inc op (list :done n)) q1))))
             (and (equal (fn-rtc-b-owner (fn-rtc-buffer h s2)) (list :workspace id inc))
                  (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses s2))))))
  :hints (("Goal" :in-theory (union-theories '(fn-hll-step* fn-hlr-acts-on-send fn-hlr-deliver-is-mstate fn-rtc-rearm-frame fn-hlr-rearm fn-hlr-end-use-send
                                               fn-rtc-with-accessors fn-rtc-buffer-of-with fn-rtc-e-kind fn-rtc-e-id fn-rtc-e-inc fn-rtc-ev fn-rtc-hand-delivers-p
                                               fn-hld-mv-nth-0-cons fn-hlr-mv-nth-1-cons fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) zp nfix natp
                                               (:e equal) (:e member-equal) member-equal (:e member-eq) member-eq)
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth))))))


(defthm fn-hlr-live-status
  (implies (fn-rtc-live-p id inc s) (equal (fn-rtc-s-status (fn-rtc-slot id s)) :live))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-live-p) (theory 'minimal-theory)))))
(defthm fn-hlr-live-via-slot
  (implies (and (fn-rtc-live-p id inc s) (equal (fn-rtc-slot id s2) (fn-rtc-slot id s)))
           (fn-rtc-live-p id inc s2))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-live-p) (theory 'minimal-theory)))))
(defthm fn-hlr-xstep-send
  (implies (and (fn-hll-invp q)
                (equal (fn-rtc-uses q) (cons (list :send id inc op (list h g 0 n)) uses0))
                (natp id) (natp inc) (natp op) (natp h) (natp g) (natp n) (< h (len (fn-rtc-pool q)))
                (equal (fn-rtc-b-owner (fn-rtc-buffer h q)) (list :leased id inc :out))
                (equal (fn-rtc-b-gen (fn-rtc-buffer h q)) g)
                (fn-rtc-live-p id inc q)
                (not (fn-rtc-holds-p h g uses0))
                (not (fn-rtc-kind-out-p :send id inc uses0)))
           (let ((s2 (mv-nth 0 (fn-hll-x-step* (list :send id inc op (list :done n)) 1 q))))
             (and (equal (fn-rtc-b-owner (fn-rtc-buffer h s2)) (list :workspace id inc))
                  (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses s2))))))
  :hints (("Goal" :in-theory (union-theories '(fn-hll-x-step*-is fn-hld-hll-invp-st-p fn-hlr-landed-send fn-hlr-step-send)
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth))))))
(defthm fn-hlr-sent-restores
  (implies (and (fn-hll-invp q)
                (equal (fn-rtc-uses q) (cons (list :send id inc op (list h g 0 n)) uses0))
                (natp id) (natp inc) (natp op) (natp h) (natp g) (natp n) (< h (len (fn-rtc-pool q)))
                (equal (fn-rtc-b-owner (fn-rtc-buffer h q)) (list :leased id inc :out))
                (equal (fn-rtc-b-gen (fn-rtc-buffer h q)) g)
                (fn-rtc-live-p id inc q)
                (not (fn-rtc-holds-p h g uses0))
                (not (fn-rtc-kind-out-p :send id inc uses0)))
           (let ((s3 (mv-nth 0 (fn-hld-sent id inc op (list :done n) q))))
             (and (fn-hll-invp s3)
                  (equal (fn-rtc-b-owner (fn-rtc-buffer h s3)) (list :workspace id inc))
                  (fn-rtc-live-p id inc s3)
                  (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses s3)))
                  (equal (fn-rtc-config s3) (fn-rtc-config q)))))
  :hints (("Goal" :in-theory (union-theories '(fn-hld-sent fn-hld-sent-event fn-hlr-settle-frames fn-hlr-xstep-frames fn-hlr-xstep-send fn-hld-x-step*-keeps-invp fn-hld-settle-keeps-invp
                                               fn-hlr-benign-tlf fn-hld-mv-nth-0-cons fn-hlr-mv-nth-1-cons fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) zp nfix natp
                                               (:e equal) (:e member-equal) member-equal (:e member-eq) member-eq fn-hlr-live-status fn-hlr-live-via-slot)
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth))))))


(defthm fn-hlr-next-op-natp
  (implies (fn-rtc-invp s) (natp (fn-rtc-next-op s))))
(defthm fn-hlr-slot-of-slots
  (implies (equal (fn-rtc-slots a) (fn-rtc-slots b)) (equal (fn-rtc-slot id a) (fn-rtc-slot id b)))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-slot) (theory 'minimal-theory)))))
(defthm fn-hlr-posp-natp (implies (posp x) (natp x)))
(defthm fn-hlr-natp-len (natp (len x)))
(defthm fn-hlr-next-op-true (implies (fn-rtc-invp s) (fn-rtc-next-op s))
  :hints (("Goal" :use fn-hlr-next-op-natp :in-theory (union-theories '(natp) (theory 'minimal-theory)))))
(defthm fn-hlr-window
  (implies (and (fn-hll-invp st) (fn-hl-render-ready-p h id inc st) (fn-rtc-live-p id inc st)
                (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses st)))
                (consp out) (fn-dss-out-p out)
                (<= (len out) (fn-rtc-buf-cap h (fn-rtc-config st))))
           (let* ((q (mv-nth 0 (fn-hld-quantum h id inc out st)))
                  (s2 (mv-nth 0 (fn-hld-sent id inc (fn-rtc-next-op st) (list :done (len out)) q))))
             (and (fn-rtc-next-op st)
                  (equal (mv-nth 1 (fn-hld-quantum h id inc out st)) (fn-rtc-next-op st))
                  (equal (mv-nth 2 (fn-hld-quantum h id inc out st)) (len out))
                  (fn-hll-invp s2)
                  (fn-hl-render-ready-p h id inc s2)
                  (fn-rtc-live-p id inc s2)
                  (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses s2)))
                  (equal (fn-rtc-config s2) (fn-rtc-config st)))))
  :hints (("Goal" :use ((:instance fn-hlr-sent-restores (q (mv-nth 0 (fn-hld-quantum h id inc out st))) (op (fn-rtc-next-op st))
                                   (g (fn-rtc-b-gen (fn-rtc-buffer h st))) (n (len out)) (uses0 (fn-rtc-uses st)))
                 (:instance fn-hld-hll-invp-is-generic-invp (s st)) (:instance fn-hlr-ws-posp-id (s st)) (:instance fn-hlr-live-natp-inc (s st)) (:instance fn-hlr-posp-natp (x id)) (:instance fn-hlr-slot-of-slots (a (mv-nth 0 (fn-hld-quantum h id inc out st))) (b st))
                 (:instance fn-hld-hll-invp-is-generic-invp (s (mv-nth 0 (fn-hld-quantum h id inc out st)))))
           :in-theory (union-theories '(fn-hlr-next-op-true fn-hlr-natp-len fn-hlr-quantum-succeeds fn-hld-quantum-keeps-invp fn-hld-hll-invp-is-generic-invp
                                               fn-hl-render-ready-p fn-hlr-next-op-natp fn-hlr-buffer-facts fn-hlr-pool-len-facts
                                               fn-hlr-ws-not-holds fn-hlr-live-via-slot fn-hlr-slot-of-slots fn-dss-out-p-is-octet-listp
                                               fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) zp nfix (:e equal))
                                             (set-difference-theories (theory 'minimal-theory) '(mv-nth))))))


(defthm fn-hlr-render-octets
  (implies (fn-ast-windowp window fn-arena)
           (fn-cbor-octet-listp (mv-nth 2 (fn-ast-render-window window fuel octets fn-arena fn-ast-ws fn-dss-out))))
  :hints (("Goal" :in-theory (e/d (fn-ast-windowp) (fn-ast-render-window-aux fn-ast-window-cur fn-ast-window-pending))
           :use ((:instance fn-ast-render-window-aux-facts
                  (cur (fn-ast-window-cur window)) (pending (fn-ast-window-pending window))
                  (fuel (nfix fuel)) (left (min (nfix octets) *fn-ast-window-max*))
                  (fn-dss-out nil))))))


(defthm fn-hlr-octets-atom2 (implies (and (fn-dss-out-p out) (not (consp out))) (equal out nil))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-dss-out-p fn-cbor-octet-listp))))
(defthm fn-hlr-quantum-empty
  (implies (and (fn-rtc-st-p st) (fn-dss-out-p out) (not (consp out)))
           (and (equal (mv-nth 0 (fn-hld-quantum h id inc out st)) st)
                (equal (mv-nth 1 (fn-hld-quantum h id inc out st)) nil)))
  :hints (("Goal" :in-theory (union-theories '(fn-hld-quantum fn-dss-out-len-is-len mv-nth (:e mv-nth) (:e len) len (:e <) (:e consp) (:e zp) (:e nfix) car-cons cdr-cons)
                                             (theory 'minimal-theory))
           :use fn-hlr-octets-atom2)))


(defthm fn-hld-leased-run-is-the-render-run
  (implies (and (fn-hll-invp st)
                (fn-hl-render-ready-p h id inc st)
                (fn-rtc-live-p id inc st)
                (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses st)))
                (<= (nfix octets) (fn-rtc-buf-cap h (fn-rtc-config st)))
                (fn-dss-out-p out)
                (fn-ast-windowp window arena))
           (equal (mv-nth 1 (fn-hld-render-run window fuel octets k h id inc arena ws out st))
                  (mv-nth 1 (fn-ast-render-run window fuel octets k arena ws out))))
  :hints (("Goal" :induct (fn-hld-render-run window fuel octets k h id inc arena ws out st)
           :in-theory (union-theories '(fn-hld-render-run fn-ast-render-run fn-hlr-window fn-hlr-quantum-empty fn-hlr-next-op-natp fn-hlr-render-octets fn-ast-render-window-keeps-windowp
                                        fn-ast-render-window-byte-bound fn-dss-out-list-is-identity fn-dss-out-p-is-octet-listp fn-hld-hll-invp-st-p fn-hld-hll-invp-is-generic-invp
                                        fn-hld-mv-nth-0-cons fn-hlr-mv-nth-1-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) zp natp)
                                      (set-difference-theories (theory 'minimal-theory) '(mv-nth))))
          ("Subgoal *1/2" :in-theory (union-theories '(fn-hld-render-run fn-ast-render-run fn-hlr-window fn-hlr-quantum-empty fn-hlr-next-op-natp fn-hlr-render-octets fn-ast-render-window-keeps-windowp
                                        fn-ast-render-window-byte-bound fn-dss-out-list-is-identity fn-dss-out-p-is-octet-listp fn-hld-hll-invp-st-p fn-hld-hll-invp-is-generic-invp
                                        fn-hld-mv-nth-0-cons fn-hlr-mv-nth-1-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) zp natp)
                                      (set-difference-theories (theory 'minimal-theory) '(mv-nth))) :cases ((consp (mv-nth 2 (fn-ast-render-window window fuel octets arena ws out))))
           :use ((:instance fn-hlr-next-op-natp (s st))
                 (:instance fn-hld-hll-invp-is-generic-invp (s st))
                 (:instance fn-hlr-octets-atom2 (out (mv-nth 2 (fn-ast-render-window window fuel octets arena ws out))))
                 (:instance fn-hlr-window (out (mv-nth 2 (fn-ast-render-window window fuel octets arena ws out))))
                 (:instance fn-hlr-render-octets (fn-arena arena) (fn-ast-ws ws) (fn-dss-out out))
                 (:instance fn-ast-render-window-byte-bound (fn-arena arena) (fn-ast-ws ws) (fn-dss-out out))
                 (:instance fn-ast-render-window-keeps-windowp (fn-arena arena) (fn-ast-ws ws) (fn-dss-out out))))))
