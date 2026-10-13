; fn: the host lease's executor (Builder A, the host lease; STATEMENTS-DRAFT's HOST EXECUTOR DESIGN).
;
; One ARTICLE response is one instance of the runtime contract over the process's one `fn-rtc-st':
;  begin    the host completes the listener's outstanding :accept with the connection's id as the
;           resource; the instance's machine (`fn-hlm-step') asks for a pool buffer on that :accept,
;           (:submit :pool nil nil), and the request waits in issue order; the host completes every
;           :grant and :pool action at once (`fn-hld-settle'), so when a pool buffer is free the
;           instance holds it as its workspace H when begin returns.
;  quantum  under the owner mutex the render leaves its window in `fn-dss-out' (adapter A2 until C's
;           window kind renders in place through fn-rtc-st-put); `fn-hld-quantum' copies it into H at
;           0, one fn-rtc-st-put per octet (no list, no vector), and submits (:submit :send (h g 0 n)):
;           exactly `fn-hl-quantum-state', so HL5a is the quantum's keystone.  The host writes the
;           array range [base(H), base(H)+n) of the stobj's one octet array, off the mutex, with no
;           copy (HL1b: no render touches H while the send is outstanding).
;  sent     the host completes the :send with the octets the socket took; H is the workspace again.
;  end      the host closes the instance; its close completion releases H to the pool, re-arms the
;           grant, and the next waiter is granted (settled at once).
; The machine is passive past the :accept: every other request is the host's, through the
; contract's own request functions, so every contract keystone about requests covers it.
(in-package "ACL2")
(include-book "runtime-contract-host-send")
(include-book "runtime-contract-u64")
(include-book "runtime-contract-layer")
(include-book "runtime-contract-host-pool")
(include-book "def-span-scan")

; -----------------------------------------------------------------------------
; The leased reader's machine: on its :accept it asks for a pool buffer; it requests nothing else.

(defun fn-hlm-step (m ev fn-rtc-st q)
  (declare (xargs :stobjs fn-rtc-st) (ignore m q))
  (let ((ignore-st (fn-rtc-st-config fn-rtc-st)))
    (declare (ignore ignore-st))
    (if (eq (fn-rtc-get 0 ev) :accept)
        (mv nil (list (list :submit :pool nil nil)) 1)
      (mv nil nil 1))))

(defthm fn-hlm-step-reads-view
  (equal (fn-hlm-step m ev (fn-rtc-view-state (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st) q) (fn-hlm-step m ev st q))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(fn-hlm-step fn-rtc-v-readers-of-view-state)))))

(defthm fn-hlm-step-facts
  (and (equal (mv-nth 2 (fn-hlm-step m ev st q)) 1)
       (equal (fn-rtc-reqs-octets (mv-nth 1 (fn-hlm-step m ev st q))) 0)
       (<= (len (mv-nth 1 (fn-hlm-step m ev st q))) 1)
       (<= (fn-rtc-size (mv-nth 0 (fn-hlm-step m ev st q))) 1)))

(defun fn-hlm-init () (declare (xargs :guard t)) nil)
(defun fn-hlm-static-init (j) (declare (xargs :guard t) (ignore j)) nil)
(defun fn-hlm-committedp (m) (declare (xargs :guard t) (ignore m)) nil)
(defun fn-hlm-c () (declare (xargs :guard t)) 1)
(defun fn-hlm-max-reqs () (declare (xargs :guard t)) 1)
(defun fn-hlm-max-state () (declare (xargs :guard t)) 1)

(fn-rtc-def-layer fn-hll
  :step fn-hlm-step :init fn-hlm-init :static-init fn-hlm-static-init :committedp fn-hlm-committedp
  :c fn-hlm-c :max-reqs fn-hlm-max-reqs :max-state fn-hlm-max-state :reads-view fn-hlm-step-reads-view
  :hints (("Goal" :in-theory (enable fn-hll-m-step)
           :use ((:instance fn-hlm-step-facts (st pool))))))

; -----------------------------------------------------------------------------
; The host's driver.  Every function is the contract's own executable layer (fn-hll-x-step*, the
; request functions) over the one stobj; the host calls these under the owner mutex and only
; writes a send's array range itself.

; Complete at once every :grant, :pool, :close and :opened action in WORK (the in-process
; completions, A-HOST-COMPLETES), and those their completions emit.  An :accept stays outstanding
; (the next begin completes it), a :send is the socket's.  Returns the actions left when FUEL ran
; out (nil when every one settled).
(defun fn-hld-settle (work fuel fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :guard (and (natp fuel) (true-listp work)) :measure (nfix fuel)))
  (if (or (zp fuel) (atom work))
      (mv fn-rtc-st (if (atom work) nil work))
    (let ((a (car work)))
      (if (member-eq (fn-rtc-get 0 a) '(:grant :pool :close :opened))
          (mv-let (fn-rtc-st acts refused cost)
            (fn-hll-x-step* (list (fn-rtc-get 0 a) (fn-rtc-get 1 a) (fn-rtc-get 2 a) (fn-rtc-get 3 a) '(:done 0))
                            1 fn-rtc-st)
            (declare (ignore refused cost))
            (fn-hld-settle (append (cdr work) (true-list-fix acts)) (- fuel 1) fn-rtc-st))
        (fn-hld-settle (cdr work) (- fuel 1) fn-rtc-st)))))

; The settle fuel: every buffer granted, every slot closed, and the init's :opened, twice over.
(defun fn-hld-fuel (fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let ((cfg (fn-rtc-st-config fn-rtc-st)))
    (+ 4 (* 2 (+ (fn-rtc-nbufs cfg) (fn-rtc-nslots cfg))))))

; A fresh contract state for the run: listener, the owner (static 1), one slot per connection, no
; home buffers, the leased pool (HL4: fn-hl-rtc-config).  (mv st okp left): OKP is nil, and the state
; untouched, when the configuration is past the stobj's limits (fn-rtc-st-cfg-okp).
(defun fn-hld-init (profile cfg q fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :guard-hints (("Goal" :in-theory (disable fn-hll-x-init fn-hl-rtc-config fn-rtc-st-cfg-okp)))))
  (let ((c (fn-hl-rtc-config profile cfg q 1 0 0)))
    (if (fn-rtc-st-cfg-okp c)
        (mv-let (fn-rtc-st acts) (fn-hll-x-init c fn-rtc-st)
          (mv-let (fn-rtc-st left) (fn-hld-settle (true-list-fix acts) (fn-hld-fuel fn-rtc-st) fn-rtc-st)
            (mv fn-rtc-st t left)))
      (mv fn-rtc-st nil nil))))

; Begin a response for resource R (the connection id): (mv st id inc left).  ID is nil when no
; slot is free or no :accept is outstanding.
(defun fn-hld-begin (r fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :guard-hints (("Goal" :in-theory (disable fn-hll-x-step* fn-rtc-x-request fn-hld-settle)))))
  (let ((uses (fn-rtc-st-uses fn-rtc-st))
        (j (fn-rtc-st-free-slot fn-rtc-st)))
    (if (and (natp r) (< r (expt 2 64)) (natp j) (fn-rtc-inc-roomp (fn-rtc-st-slot j fn-rtc-st))
             (fn-rtc-kind-out-p :accept 0 0 uses))
        (let ((jinc (+ 1 (fn-rtc-s-inc (fn-rtc-st-slot j fn-rtc-st))))
              (op (fn-rtc-kind-op :accept 0 0 uses)))
          (mv-let (fn-rtc-st acts refused cost)
            (fn-hll-x-step* (list :accept 0 0 op (list :done r)) 1 fn-rtc-st)
            (declare (ignore refused cost))
            (mv-let (fn-rtc-st left) (fn-hld-settle (true-list-fix acts) (fn-hld-fuel fn-rtc-st) fn-rtc-st)
              (mv fn-rtc-st j jinc left))))
      (mv fn-rtc-st nil
          (if (fn-rtc-x-slots-exhaustedp fn-rtc-st)
              :rtc-slots-exhausted nil)
          nil))))

; The pool buffer that is (ID INC)'s workspace, at or above H; nil when the request still waits.
(defun fn-hld-workspace (h id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :guard (natp h)
                  :measure (nfix (- (fn-rtc-nbufs (fn-rtc-st-config fn-rtc-st)) (nfix h)))))
  (let ((h (nfix h)))
    (if (< h (fn-rtc-nbufs (fn-rtc-st-config fn-rtc-st)))
        (if (equal (fn-rtc-st-owner h fn-rtc-st) (list :workspace id inc))
            h
          (fn-hld-workspace (+ 1 h) id inc fn-rtc-st))
      nil)))

; Octets [I, N) of the render's window into H at I, one put each.
(defun fn-hld-copy (i n h fn-dss-out fn-rtc-st)
  (declare (xargs :stobjs (fn-dss-out fn-rtc-st) :guard (and (natp i) (natp n))
                  :measure (nfix (- (nfix n) (nfix i)))))
  (let ((i (nfix i)))
    (if (and (< i (nfix n)) (< i (fn-dss-out-len fn-dss-out)))
        (let ((fn-rtc-st (fn-rtc-st-put h i (fn-dss-out-get i fn-dss-out) fn-rtc-st)))
          (fn-hld-copy (+ 1 i) n h fn-dss-out fn-rtc-st))
      fn-rtc-st)))

; One leased quantum: the window in fn-dss-out into H at 0 and its :send submitted.
; (mv st op n): OP is the send's operation number, nil when the quantum's conditions fail (H not
; the instance's workspace, the instance not live, a send outstanding, an empty window or one past
; H's capacity) and then the state is unchanged.
(defun fn-hld-quantum (h id inc fn-dss-out fn-rtc-st)
  (declare (xargs :stobjs (fn-dss-out fn-rtc-st)))
  (let ((n (fn-dss-out-len fn-dss-out))
        (cfg (fn-rtc-st-config fn-rtc-st)))
    (if (and (natp h) (< h (fn-rtc-nbufs cfg))
             (equal (fn-rtc-st-owner h fn-rtc-st) (list :workspace id inc))
             (fn-rtc-x-live-p id inc fn-rtc-st)
             (not (fn-rtc-kind-out-p :send id inc (fn-rtc-st-uses fn-rtc-st)))
             (< 0 n) (<= n (fn-rtc-buf-cap h cfg)))
        (let* ((g (fn-rtc-st-gen h fn-rtc-st))
               (op (fn-rtc-st-next-op fn-rtc-st))
               (fn-rtc-st (fn-hld-copy 0 n h fn-dss-out fn-rtc-st)))
          (mv-let (fn-rtc-st acts refused cost)
            (fn-rtc-x-request (list :submit :send (list h g 0 n) nil) id inc fn-rtc-st)
            (declare (ignore acts cost))
            (mv fn-rtc-st (if refused nil op) n)))
      (mv fn-rtc-st nil 0))))

; The completion the host delivers for its send: a contract completion by its guard (an operation
; number, the instance, and an outcome the contract reads), checked at the host's call.
(defun fn-hld-sent-event (id inc op outcome)
  (declare (xargs :guard (and (natp id) (natp inc) (natp op) (fn-rtc-outcomep outcome))))
  (list :send id inc op outcome))

; The socket took the send's octets: complete it with OUTCOME, (:done n) or (:failed reason).
(defun fn-hld-sent (id inc op outcome fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st
                  :guard (and (natp id) (natp inc) (natp op) (fn-rtc-outcomep outcome))
                  :guard-hints (("Goal" :in-theory (disable fn-hll-x-step* fn-rtc-x-request fn-hld-settle)))))
  (mv-let (fn-rtc-st acts refused cost)
    (fn-hll-x-step* (fn-hld-sent-event id inc op outcome) 1 fn-rtc-st)
    (declare (ignore refused cost))
    (fn-hld-settle (true-list-fix acts) (fn-hld-fuel fn-rtc-st) fn-rtc-st)))

; End the response: close the instance; its close completion releases its workspace to the pool
; and grants the next waiter.  (mv st left).
(defun fn-hld-end (id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :guard-hints (("Goal" :in-theory (disable fn-hll-x-step* fn-rtc-x-request fn-hld-settle)))))
  (mv-let (fn-rtc-st acts refused cost)
    (fn-rtc-x-request '(:close) id inc fn-rtc-st)
    (declare (ignore refused cost))
    (fn-hld-settle (true-list-fix acts) (fn-hld-fuel fn-rtc-st) fn-rtc-st)))

;; The array offset the host writes a window of H from: buffer H's base (the quantum's keystone's range
;; starts there, fn-hld-window-base-is-the-base).
(defun fn-hld-window-base (h fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (fn-rtc-buf-base h (fn-rtc-st-config fn-rtc-st)))

; -----------------------------------------------------------------------------
; The quantum's keystone: what fn-hld-quantum leaves is HL5a's state, so the array range the host writes
; for the send it submits is the render's window (fn-hld-quantum-sends-the-window).

(defthm fn-hld-nthcdr-len-atom
  (not (consp (nthcdr (len x) x)))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm fn-hld-copy-is-puts
  (implies (and (natp i) (<= i (len out)))
           (equal (fn-hld-copy i (len out) h out st)
                  (fn-rtc-st$a-puts h i (nthcdr i out) st)))
  :hints (("Goal" :induct (fn-hld-copy i (len out) h out st)
           :in-theory (e/d (fn-dss-out-get fn-rtc-st-put fn-octets$a-get)
                           (fn-rtc-st$a-put fn-rtc-st$a-puts len nthcdr)))
          ("Subgoal *1/2" :expand ((fn-rtc-st$a-puts h i (nthcdr i out) st)))
          ("Subgoal *1/1" :expand ((fn-rtc-st$a-puts h i (nthcdr i out) st))
           :use ((:instance fn-rtc-c-nthcdr-is-cons (l out))))))

(defthm fn-hld-puts-keeps-st-p
  (implies (fn-rtc-st-p st) (fn-rtc-st-p (fn-rtc-st$a-puts h off w st)))
  :hints (("Goal" :induct (fn-rtc-st$a-puts h off w st)
           :in-theory (union-theories '(fn-rtc-st-p (:induction fn-rtc-st$a-puts)) (theory 'minimal-theory)))
          ("Subgoal *1/2" :expand ((fn-rtc-st$a-puts h off w st)))
          ("Subgoal *1/1" :expand ((fn-rtc-st$a-puts h off w st))
           :use ((:instance fn-rtc-st-put{preserved} (fn-rtc-st st) (o (car w)))))))

(defthm fn-hld-readers
  (and (equal (fn-rtc-st-owner h st) (fn-rtc-b-owner (fn-rtc-buffer h st)))
       (equal (fn-rtc-st-gen h st) (fn-rtc-b-gen (fn-rtc-buffer h st)))
       (equal (fn-rtc-st-next-op st) (fn-rtc-next-op st))
       (equal (fn-rtc-st-uses st) (fn-rtc-uses st))
       (equal (fn-rtc-st-config st) (fn-rtc-config st)))
  :hints (("Goal" :in-theory (enable fn-rtc-st-owner fn-rtc-st$a-owner fn-rtc-st-gen fn-rtc-st$a-gen fn-rtc-b-owner fn-rtc-b-gen
                                     fn-rtc-st-next-op fn-rtc-st$a-next-op fn-rtc-st-uses fn-rtc-st$a-uses
                                     fn-rtc-st-config fn-rtc-st$a-config))))

(in-theory (disable fn-hld-readers))

(defthm fn-hld-window-base-is-the-base
  (equal (fn-hld-window-base h st) (fn-rtc-buf-base h (fn-rtc-config st)))
  :hints (("Goal" :in-theory (union-theories '(fn-hld-window-base fn-hld-readers) (theory 'minimal-theory)))))

(defthm fn-hld-nthcdr-0 (equal (nthcdr 0 x) x))
(defthm fn-hld-quantum-is-the-quantum-state
  (implies (and (fn-rtc-st-p st) (fn-cbor-octet-listp out)
                (mv-nth 1 (fn-hld-quantum h id inc out st)))
           (and (equal (mv-nth 0 (fn-hld-quantum h id inc out st)) (fn-hl-quantum-state h out id inc st))
                (equal (mv-nth 1 (fn-hld-quantum h id inc out st)) (fn-rtc-next-op st))
                (fn-hl-render-ready-p h id inc st)
                (fn-rtc-live-p id inc st)
                (not (fn-rtc-kind-out-p :send id inc (fn-rtc-uses st)))
                (<= (len out) (fn-rtc-buf-cap h (fn-rtc-config st)))))
  :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-hld-quantum fn-hl-quantum-state fn-hl-render-ready-p
                                               fn-dss-out-len-is-len fn-hld-readers fn-rtc-x-live-p-is fn-rtc-b-gen
                                               fn-hld-puts-keeps-st-p fn-rtc-st-p-is-shapep natp nfix (:type-prescription fn-rtc-nbufs) (:e zp) fn-hld-nthcdr-0 fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get)
                                               (:type-prescription len))
                                             (theory 'minimal-theory))
           :use ((:instance fn-hld-copy-is-puts (i 0))
                 (:instance fn-hld-puts-keeps-st-p (off 0) (w out))
                 (:instance fn-rtc-c-shapep-buffer (s st))
                 (:instance fn-rtc-x-request-is (r (list :submit :send (list h (fn-rtc-get 0 (fn-rtc-buffer h st)) 0 (len out)) nil))
                            (fn-rtc-st (fn-rtc-st$a-puts h 0 out st)))
                 (:instance fn-rtc-request (r (list :submit :send (list h (fn-rtc-get 0 (fn-rtc-buffer h st)) 0 (len out)) nil))
                            (s (fn-rtc-st$a-puts h 0 out st)))))))

(defthm fn-hld-quantum-sends-the-window
  (implies (and (fn-rtc-st-p st) (fn-dss-out-p out)
                (mv-nth 1 (fn-hld-quantum h id inc out st))
                (fn-rtc-st$corr c (mv-nth 0 (fn-hld-quantum h id inc out st))))
           (and (member-equal (list :send id inc (mv-nth 1 (fn-hld-quantum h id inc out st))
                                    (list h (fn-rtc-get 0 (fn-rtc-buffer h st)) 0 (len out)))
                              (fn-rtc-uses (mv-nth 0 (fn-hld-quantum h id inc out st))))
                (equal (fn-rtc-c-octets (fn-rtc-buf-base h (fn-rtc-config st)) (len out)
                                        (nth *fn-rtc-c-bytesi* c))
                       out)))
  :hints (("Goal" :in-theory (union-theories '(fn-dss-out-p-is-octet-listp) (theory 'minimal-theory))
           :use (fn-hld-quantum-is-the-quantum-state
                 (:instance fn-hl-leased-quantum-sends-the-window (s st))))))

; -----------------------------------------------------------------------------
; The invariant on the host's states.  The leased machine's states are all nil (size 1), and the contract's
; encapsulate forces fn-rtc-m-max-state >= size(m-init) >= 1, so the leased layer's invariant is the generic
; fn-rtc-invp: every generic keystone assuming it applies to the host lease's states.

(defthm fn-hld-size-pos
  (<= 1 (fn-rtc-size x))
  :rule-classes :linear)
(defthm fn-hld-hll-mstates-okp-is-generic
  (implies (fn-hll-mstates-okp ms) (fn-rtc-mstates-okp ms))
  :hints (("Goal" :induct (fn-rtc-mstates-okp ms)
           :in-theory (enable fn-rtc-mstates-okp fn-hll-mstates-okp fn-hlm-max-state))
          ("Subgoal *1/1" :use ((:instance fn-hld-size-pos (x (fn-rtc-m-init)))
                                fn-rtc-m-init-is-bounded))))
(defthm fn-hld-hll-invp-is-generic-invp
  (implies (fn-hll-invp s) (fn-rtc-invp s))
  :hints (("Goal" :in-theory (union-theories '(fn-hll-invp fn-rtc-invp fn-hld-hll-mstates-okp-is-generic)
                                             (theory 'minimal-theory)))))

(make-event
 (let* ((prefix 'fn-hll)
        (copied (fn-rtc-layer-alist prefix (append *fn-rtc-layer-spec-fns* *fn-rtc-layer-exec-fns*)))
        (alist (append '((fn-rtc-m-init . fn-hlm-init) (fn-rtc-m-static-init . fn-hlm-static-init)
                         (fn-rtc-m-step . fn-hll-m-step) (fn-rtc-m-committedp . fn-hlm-committedp)
                         (fn-rtc-m-c . fn-hlm-c) (fn-rtc-m-max-reqs . fn-hlm-max-reqs)
                         (fn-rtc-m-max-state . fn-hlm-max-state) (fn-rtc-mx-step . fn-hlm-step))
                       copied))
        (obligations (cons 'natp (fn-rtc-layer-names prefix
                                   '(fn-rtc-m-constants fn-rtc-mx-step-is-m-step fn-rtc-m-step-is-charged
                                     fn-rtc-m-step-requests-are-bounded fn-rtc-m-init-is-bounded
                                     fn-rtc-m-step-state-is-bounded fn-rtc-m-init-is-uncommitted
                                     fn-rtc-m-static-init-is-bounded fn-rtc-m-static-init-is-uncommitted
                                     fn-rtc-m-commits-only-on-fsync-done)))))
   (cons 'progn (fn-rtc-layer-keystone-events '(fn-rtc-x-init-is) prefix alist (fn-rtc-layer-fi-alist alist)
                                              (strip-cdrs copied) obligations (w state)))))

(defthm fn-hld-hll-invp-st-p
  (implies (fn-hll-invp s) (fn-rtc-st-p s))
  :hints (("Goal" :use (fn-hld-hll-invp-is-generic-invp fn-rtc-invp-implies-st-p)
           :in-theory (theory 'minimal-theory))))
(defthm fn-hld-x-step*-keeps-invp
  (implies (fn-hll-invp st) (fn-hll-invp (mv-nth 0 (fn-hll-x-step* e q st))))
  :hints (("Goal" :in-theory (union-theories '(fn-hld-hll-invp-st-p fn-hll-x-step*-is fn-hll-step) (theory 'minimal-theory))
           :use ((:instance fn-hll-step-preserves-invp (s st) (e (fn-rtc-landed e st)))))))

(defthm fn-hld-mv-nth-0-cons (equal (mv-nth 0 (cons a b)) a))
(defthm fn-hld-settle-keeps-invp
  (implies (fn-hll-invp st) (fn-hll-invp (mv-nth 0 (fn-hld-settle work fuel st))))
  :hints (("Goal" :induct (fn-hld-settle work fuel st)
           :expand ((fn-hld-settle work fuel st))
           :in-theory (union-theories '(fn-hld-x-step*-keeps-invp (:induction fn-hld-settle) fn-hld-mv-nth-0-cons)
                                      (theory 'minimal-theory)))))

(defthm fn-hld-init-establishes-invp
  (implies (mv-nth 1 (fn-hld-init profile cfg q st))
           (fn-hll-invp (mv-nth 0 (fn-hld-init profile cfg q st))))
  :hints (("Goal" :in-theory (union-theories '(fn-hld-init fn-hll-x-init-is fn-hld-settle-keeps-invp fn-rtc-st-cfg-okp
                                               fn-hld-mv-nth-0-cons)
                                             (theory 'minimal-theory))
           :use ((:instance fn-hll-init-establishes-invp (cfg (fn-hl-rtc-config profile cfg q 1 0 0)))))))

(defthm fn-hld-begin-keeps-invp
  (implies (fn-hll-invp st) (fn-hll-invp (mv-nth 0 (fn-hld-begin r st))))
  :hints (("Goal" :in-theory (union-theories '(fn-hld-begin fn-hld-x-step*-keeps-invp fn-hld-settle-keeps-invp
                                               fn-hld-mv-nth-0-cons)
                                             (theory 'minimal-theory)))))
(defthm fn-hld-sent-keeps-invp
  (implies (fn-hll-invp st) (fn-hll-invp (mv-nth 0 (fn-hld-sent id inc op outcome st))))
  :hints (("Goal" :in-theory (union-theories '(fn-hld-sent fn-hld-x-step*-keeps-invp fn-hld-settle-keeps-invp)
                                             (theory 'minimal-theory)))))

; -----------------------------------------------------------------------------
; Quantum and end keep the invariant.  The leased layer's invariant is the generic one plus the leased
; machine's states (fn-hld-hll-invp-is); the host's own requests in a quantum (the window's puts, which are the
; :write request (HL3), then (:submit :send ...)) and in end ((:close)) leave every machine state alone and keep
; the generic invariant: neither frees a pool buffer, issues a :wait, nor touches the :accept and :grant uses,
; so both admission clauses hold as before, with no re-arm.

(defthm fn-hld-hll-invp-is
  (iff (fn-hll-invp s) (and (fn-rtc-invp s) (fn-hll-mstates-okp (fn-rtc-mstates s))))
  :hints (("Goal" :in-theory (union-theories '(fn-hll-invp fn-rtc-invp fn-hld-hll-mstates-okp-is-generic iff)
                                             (theory 'minimal-theory)))))
(in-theory (disable fn-hld-hll-invp-is))

(local (progn
(defthm fn-hld-put-tables
  (and (equal (fn-rtc-config (fn-rtc-st$a-put h off o s)) (fn-rtc-config s))
       (equal (fn-rtc-slots (fn-rtc-st$a-put h off o s)) (fn-rtc-slots s))
       (equal (fn-rtc-mstates (fn-rtc-st$a-put h off o s)) (fn-rtc-mstates s))
       (equal (fn-rtc-uses (fn-rtc-st$a-put h off o s)) (fn-rtc-uses s)))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-st$a-put fn-rtc-st$a-splice fn-rtc-with-accessors) (theory 'minimal-theory)))))
(defthm fn-hld-put-keeps-invp
  (implies (fn-rtc-invp s) (fn-rtc-invp (fn-rtc-st$a-put h off o s)))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-st$a-put fn-rtc-st-splice) (theory 'minimal-theory))
           :use ((:instance fn-rtc-splice-keeps-invp (st s) (data (list o)))))))
(defthm fn-hld-puts-keeps-invp
  (implies (fn-rtc-invp s)
           (and (fn-rtc-invp (fn-rtc-st$a-puts h off w s))
                (equal (fn-rtc-mstates (fn-rtc-st$a-puts h off w s)) (fn-rtc-mstates s))
                (equal (fn-rtc-slots (fn-rtc-st$a-puts h off w s)) (fn-rtc-slots s))
                (equal (fn-rtc-config (fn-rtc-st$a-puts h off w s)) (fn-rtc-config s))))
  :hints (("Goal" :induct (fn-rtc-st$a-puts h off w s)
           :in-theory (union-theories '((:induction fn-rtc-st$a-puts) fn-hld-put-keeps-invp fn-hld-put-tables)
                                      (theory 'minimal-theory)))
          ("Subgoal *1/2" :expand ((fn-rtc-st$a-puts h off w s)))
          ("Subgoal *1/1" :expand ((fn-rtc-st$a-puts h off w s)))))

(defun fn-hld-set-ind (k i pool)
  (if (or (zp k) (atom pool)) (list k i pool)
    (fn-hld-set-ind (- k 1) (+ 1 (nfix i)) (cdr pool))))
(defthm fn-hld-free-pool-buf-of-set-nonfree
  (implies (and (natp k)
                (not (equal (fn-rtc-b-owner b) '(:free)))
                (not (equal (fn-rtc-b-owner (fn-rtc-get k pool)) '(:free))))
           (equal (fn-rtc-free-pool-buf i (fn-rtc-set k b pool) cfg)
                  (fn-rtc-free-pool-buf i pool cfg)))
  :hints (("Goal" :induct (fn-hld-set-ind k i pool)
           :expand ((:free (x xs) (fn-rtc-free-pool-buf i (cons x xs) cfg))
                    (fn-rtc-free-pool-buf i pool cfg)
                    (fn-rtc-set k b pool) (fn-rtc-get k pool))
           :in-theory (disable fn-rtc-b-owner fn-rtc-pool-buf-p))))
(defthm fn-hld-free-pool-of-set-buffer-nonfree
  (implies (and (natp k)
                (not (equal (fn-rtc-b-owner b) '(:free)))
                (not (equal (fn-rtc-b-owner (fn-rtc-buffer k s)) '(:free))))
           (equal (fn-rtc-free-pool-buf i (fn-rtc-set k b (fn-rtc-pool s)) cfg)
                  (fn-rtc-free-pool-buf i (fn-rtc-pool s) cfg)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance fn-hld-free-pool-buf-of-set-nonfree (pool (fn-rtc-pool s)))
                 (:instance fn-rtc-buffer (h k))))))

; A non-pool submit and a close leave the grant and accept clauses' terms alone.
(defthm fn-hld-submit-admission-frame
  (implies (and (posp id) (not (equal (fn-rtc-get 1 r) :pool)))
           (let ((s2 (mv-nth 0 (fn-rtc-req-submit r id inc s))))
             (and (equal (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses s2)) (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses s)))
                  (equal (fn-rtc-oldest-wait (fn-rtc-uses s2)) (fn-rtc-oldest-wait (fn-rtc-uses s)))
                  (equal (fn-rtc-free-pool-buf 0 (fn-rtc-pool s2) (fn-rtc-config s))
                         (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s)))
                  (equal (fn-rtc-mstates s2) (fn-rtc-mstates s)))))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-req-submit fn-rtc-issue-frame fn-rtc-with-accessors fn-rtc-buffer-accessors
                                               fn-rtc-kind-out-cons fn-rtc-oldest-wait-cons-other
                                               fn-hld-free-pool-of-set-buffer-nonfree (:type-prescription nfix) (:e equal)
                                               fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e binary-+)
                                               member-equal (:e member-equal) posp natp mv-nth (:e mv-nth)
                                               (:type-prescription fn-rtc-h-buf) fn-rtc-h-buf)
                                             (theory 'minimal-theory)))))
(defthm fn-hld-close-admission-frame
  (implies (posp id)
           (let ((s2 (mv-nth 0 (fn-rtc-req-close r id inc s))))
             (and (equal (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses s2)) (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses s)))
                  (equal (fn-rtc-oldest-wait (fn-rtc-uses s2)) (fn-rtc-oldest-wait (fn-rtc-uses s)))
                  (equal (fn-rtc-pool s2) (fn-rtc-pool s))
                  (equal (fn-rtc-config s2) (fn-rtc-config s))
                  (equal (fn-rtc-mstates s2) (fn-rtc-mstates s)))))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-req-close fn-rtc-issue-frame fn-rtc-with-accessors
                                               fn-rtc-kind-out-cons fn-rtc-oldest-wait-cons-other
                                               fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get) (:e zp) (:e nfix) (:e binary-+)
                                               (:e equal) posp natp mv-nth (:e mv-nth))
                                             (theory 'minimal-theory)))))
))

(defthm fn-hld-request-keeps-invp
  (implies (and (fn-rtc-invp s) (fn-rtc-instance-active-p id inc s)
                (or (equal (fn-rtc-get 0 r) :close)
                    (and (equal (fn-rtc-get 0 r) :submit) (not (equal (fn-rtc-get 1 r) :pool)))))
           (and (fn-rtc-invp (mv-nth 0 (fn-rtc-request r id inc s)))
                (equal (fn-rtc-mstates (mv-nth 0 (fn-rtc-request r id inc s))) (fn-rtc-mstates s))))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-invp-is-core-and-admission fn-rtc-request-preserves-core-invp
                                               fn-rtc-request-preserves-free-slot fn-rtc-request-preserves-accept
                                               fn-rtc-request-config-frame fn-hld-submit-admission-frame
                                               fn-hld-close-admission-frame posp natp)
                                             (theory 'minimal-theory))
           :use ((:instance fn-rtc-instance-active-p)
                 (:instance fn-rtc-request)))))

(local (progn
(defthm fn-hld-get-past-len
  (implies (<= (len l) (nfix i)) (equal (fn-rtc-get i l) nil))
  :hints (("Goal" :in-theory (enable fn-rtc-get))))
(defthm fn-hld-held-is-active
  (implies (and (fn-rtc-core-invp s) (posp id) (equal (fn-rtc-s-inc (fn-rtc-slot id s)) inc)
                (member-eq (fn-rtc-s-status (fn-rtc-slot id s)) '(:live :closing)))
           (fn-rtc-instance-active-p id inc s))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-instance-active-p (:e fn-rtc-s-status) posp natp nfix
                                               member-equal (:e member-equal) (:type-prescription fn-rtc-s-inc))
                                             (theory 'minimal-theory))
           :use ((:instance fn-rtc-slot) (:instance fn-rtc-core-invp)
                 (:instance fn-hld-get-past-len (i id) (l (fn-rtc-slots s)))))))
(defthm fn-hld-live-is-active
  (implies (and (fn-rtc-core-invp s) (fn-rtc-live-p id inc s) (posp id))
           (fn-rtc-instance-active-p id inc s))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-live-p fn-hld-held-is-active member-equal (:e member-equal))
                                             (theory 'minimal-theory)))))
(defthm fn-hld-workspace-okp
  (implies (and (fn-rtc-buffer-okp h b s) (equal (fn-rtc-b-owner b) o) (equal (fn-rtc-get 0 o) :workspace))
           (let ((id (fn-rtc-get 1 o)) (inc (fn-rtc-get 2 o)))
             (and (posp id) (equal (fn-rtc-s-inc (fn-rtc-slot id s)) inc)
                  (member-eq (fn-rtc-s-status (fn-rtc-slot id s)) '(:live :closing)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-buffer-okp posp natp nfix fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get))
                                             (theory 'minimal-theory)))))
(defthm fn-hld-workspace-owner-is-active-o
  (implies (and (fn-rtc-core-invp s) (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
                (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) o) (equal (fn-rtc-get 0 o) :workspace))
           (fn-rtc-instance-active-p (fn-rtc-get 1 o) (fn-rtc-get 2 o) s))
  :rule-classes nil
  :hints (("Goal" :use (fn-rtc-core-invp-buffer (:instance fn-hld-workspace-okp (b (fn-rtc-buffer h s))))
           :in-theory (union-theories '(fn-hld-held-is-active) (theory 'minimal-theory)))))
(defthm fn-hld-workspace-fields
  (implies (equal x (list :workspace id inc))
           (and (equal (fn-rtc-get 0 x) :workspace) (equal (fn-rtc-get 1 x) id) (equal (fn-rtc-get 2 x) inc)))
  :rule-classes nil)
))

; An instance holding a workspace is active (so its requests are the contract's).
(defthm fn-hld-workspace-owner-is-active
  (implies (and (fn-rtc-core-invp s) (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
                (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) (list :workspace id inc)))
           (fn-rtc-instance-active-p id inc s))
  :hints (("Goal" :use ((:instance fn-hld-workspace-owner-is-active-o (o (list :workspace id inc)))
                        (:instance fn-hld-workspace-fields (x (fn-rtc-b-owner (fn-rtc-buffer h s)))))
           :in-theory (union-theories '(fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get)) (theory 'minimal-theory)))))

(local (defthm fn-hld-close-refused-when-inactive
  (implies (and (fn-rtc-core-invp s) (not (fn-rtc-instance-active-p id inc s)))
           (equal (mv-nth 0 (fn-rtc-req-close r id inc s)) s))
  :hints (("Goal" :in-theory (e/d (fn-rtc-req-close) (fn-rtc-core-invp fn-rtc-instance-active-p fn-rtc-live-p fn-rtc-issue
                                                     fn-rtc-with-slot fn-rtc-slot fn-rtc-s-res fn-rtc-use-bound))
           :use (fn-hld-live-is-active)))))
(defthm fn-hld-close-keeps-invp
  (implies (fn-rtc-invp s)
           (and (fn-rtc-invp (mv-nth 0 (fn-rtc-request '(:close) id inc s)))
                (equal (fn-rtc-mstates (mv-nth 0 (fn-rtc-request '(:close) id inc s))) (fn-rtc-mstates s))))
  :hints (("Goal" :cases ((fn-rtc-instance-active-p id inc s))
           :in-theory (union-theories '(fn-rtc-request (:e fn-rtc-get) fn-hld-close-refused-when-inactive)
                                      (theory 'minimal-theory))
           :use ((:instance fn-hld-request-keeps-invp (r '(:close)))
                 fn-rtc-invp-is-core-and-admission))))
(defthm fn-hld-close-keeps-hll-invp
  (implies (fn-hll-invp st) (fn-hll-invp (mv-nth 0 (fn-rtc-request '(:close) id inc st))))
  :hints (("Goal" :in-theory (union-theories '(fn-hld-hll-invp-is fn-hld-close-keeps-invp) (theory 'minimal-theory)))))
(defthm fn-hld-end-keeps-invp
  (implies (fn-hll-invp st) (fn-hll-invp (mv-nth 0 (fn-hld-end id inc st))))
  :hints (("Goal" :in-theory (union-theories '(fn-hld-end fn-rtc-x-request-is fn-hld-hll-invp-st-p fn-hld-close-keeps-hll-invp
                                               fn-hld-settle-keeps-invp)
                                             (theory 'minimal-theory)))))

; The quantum: what fn-hld-quantum leaves is ST (refused) or HL5a's quantum state of a render-ready workspace.
(local (defthm fn-hld-quantum-state-cases
  (implies (and (fn-rtc-st-p st) (fn-cbor-octet-listp out))
           (or (equal (mv-nth 0 (fn-hld-quantum h id inc out st)) st)
               (and (equal (mv-nth 0 (fn-hld-quantum h id inc out st)) (fn-hl-quantum-state h out id inc st))
                    (fn-hl-render-ready-p h id inc st))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (union-theories '(fn-hld-quantum fn-hl-quantum-state fn-hl-render-ready-p
                                               fn-dss-out-len-is-len fn-hld-readers fn-rtc-x-live-p-is fn-rtc-b-gen
                                               fn-hld-puts-keeps-st-p fn-rtc-st-p-is-shapep natp nfix (:type-prescription fn-rtc-nbufs) (:e zp) fn-hld-nthcdr-0 fn-rtc-get-of-cons car-cons cdr-cons (:e fn-rtc-get)
                                               (:type-prescription len))
                                             (theory 'minimal-theory))
           :use ((:instance fn-hld-copy-is-puts (i 0))
                 (:instance fn-hld-puts-keeps-st-p (off 0) (w out))
                 (:instance fn-rtc-c-shapep-buffer (s st))
                 (:instance fn-rtc-x-request-is (r (list :submit :send (list h (fn-rtc-get 0 (fn-rtc-buffer h st)) 0 (len out)) nil))
                            (fn-rtc-st (fn-rtc-st$a-puts h 0 out st)))
                 (:instance fn-rtc-request (r (list :submit :send (list h (fn-rtc-get 0 (fn-rtc-buffer h st)) 0 (len out)) nil))
                            (s (fn-rtc-st$a-puts h 0 out st))))))))
(local (defthm fn-hld-active-of-puts
  (implies (fn-rtc-invp s)
           (equal (fn-rtc-instance-active-p id inc (fn-rtc-st$a-puts h off w s))
                  (fn-rtc-instance-active-p id inc s)))
  :hints (("Goal" :in-theory (union-theories '(fn-rtc-instance-active-p fn-hld-puts-keeps-invp) (theory 'minimal-theory))
           :use ((:instance fn-rtc-slot (s (fn-rtc-st$a-puts h off w s))) (:instance fn-rtc-slot))))))
(defthm fn-hld-quantum-state-keeps-invp
  (implies (and (fn-rtc-invp s) (fn-cbor-octet-listp out) (fn-hl-render-ready-p h id inc s))
           (and (fn-rtc-invp (fn-hl-quantum-state h out id inc s))
                (equal (fn-rtc-mstates (fn-hl-quantum-state h out id inc s)) (fn-rtc-mstates s))))
  :hints (("Goal" :in-theory (union-theories '(fn-hl-quantum-state fn-hl-render-ready-p fn-rtc-request (:e fn-rtc-get)
                                               fn-rtc-get-of-cons car-cons cdr-cons fn-hld-puts-keeps-invp fn-hld-active-of-puts
                                               (:e zp) (:e nfix) (:e binary-+) (:e unary--))
                                             (theory 'minimal-theory))
           :use ((:instance fn-hld-request-keeps-invp
                            (r (list :submit :send (list h (fn-rtc-get 0 (fn-rtc-buffer h s)) 0 (len out)) nil))
                            (s (fn-rtc-st$a-puts h 0 out s)))
                 (:instance fn-hld-workspace-owner-is-active)
                 (:instance fn-rtc-invp-is-core-and-admission)))))
(defthm fn-hld-quantum-keeps-invp
  (implies (and (fn-hll-invp st) (fn-dss-out-p out))
           (fn-hll-invp (mv-nth 0 (fn-hld-quantum h id inc out st))))
  :hints (("Goal" :in-theory (union-theories '(fn-hld-hll-invp-is fn-hld-hll-invp-st-p fn-dss-out-p-is-octet-listp
                                               fn-hld-quantum-state-keeps-invp)
                                             (theory 'minimal-theory))
           :use ((:instance fn-hld-quantum-state-cases)
                 (:instance fn-hld-hll-invp-st-p (s st))))))

; Permanent retirement is a terminal begin result; temporary occupancy remains NIL.
(defthm fn-hld-begin-exhausted-iff
  (implies (and (fn-rtc-st-p fn-rtc-st) (fn-rtc-invp fn-rtc-st))
           (iff (equal (mv-nth 2 (fn-hld-begin r fn-rtc-st)) :rtc-slots-exhausted)
                (fn-rtc-slots-exhaustedp 0
                  (fn-rtc-nstatic (fn-rtc-config fn-rtc-st))
                  (fn-rtc-slots fn-rtc-st))))
  :hints (("Goal" :in-theory
           (e/d (fn-hld-begin fn-rtc-st-free-slot fn-rtc-st-slot
                 fn-rtc-x-slots-exhaustedp-is)
                (fn-hll-x-step* fn-hld-settle fn-hld-fuel fn-rtc-kind-out-p
                 fn-rtc-kind-op fn-rtc-inc-roomp fn-rtc-free-slot fn-rtc-slot
                 fn-rtc-s-inc fn-rtc-st-uses fn-rtc-slots-exhaustedp
                 fn-rtc-nstatic fn-rtc-invp mv-nth))
           :use ((:instance fn-rtc-exhausted-means-no-free-slot (s fn-rtc-st))))))
