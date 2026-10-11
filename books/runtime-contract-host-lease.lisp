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
(include-book "runtime-contract-host-pool")
(include-book "runtime-contract-layer")
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
; home buffers, the leased pool (HL4: fn-hl-rtc-config).
(defun fn-hld-init (profile cfg q fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :guard-hints (("Goal" :in-theory (disable fn-hll-x-init fn-hl-rtc-config)))))
  (mv-let (fn-rtc-st acts) (fn-hll-x-init (fn-hl-rtc-config profile cfg q 1 0 0) fn-rtc-st)
    (fn-hld-settle (true-list-fix acts) (fn-hld-fuel fn-rtc-st) fn-rtc-st)))

; Begin a response for resource R (the connection id): (mv st id inc left).  ID is nil when no
; slot is free or no :accept is outstanding.
(defun fn-hld-begin (r fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :guard-hints (("Goal" :in-theory (disable fn-hll-x-step* fn-rtc-x-request fn-hld-settle)))))
  (let ((uses (fn-rtc-st-uses fn-rtc-st))
        (j (fn-rtc-st-free-slot fn-rtc-st)))
    (if (and (natp r) (< r (expt 2 64)) (natp j) (fn-rtc-kind-out-p :accept 0 0 uses))
        (let ((jinc (+ 1 (fn-rtc-s-inc (fn-rtc-st-slot j fn-rtc-st))))
              (op (fn-rtc-kind-op :accept 0 0 uses)))
          (mv-let (fn-rtc-st acts refused cost)
            (fn-hll-x-step* (list :accept 0 0 op (list :done r)) 1 fn-rtc-st)
            (declare (ignore refused cost))
            (mv-let (fn-rtc-st left) (fn-hld-settle (true-list-fix acts) (fn-hld-fuel fn-rtc-st) fn-rtc-st)
              (mv fn-rtc-st j jinc left))))
      (mv fn-rtc-st nil nil nil))))

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

; The socket took the send's octets: complete it with OUTCOME, (:done n) or (:failed reason).
(defun fn-hld-sent (id inc op outcome fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :guard-hints (("Goal" :in-theory (disable fn-hll-x-step* fn-rtc-x-request fn-hld-settle)))))
  (mv-let (fn-rtc-st acts refused cost)
    (fn-hll-x-step* (list :send id inc op outcome) 1 fn-rtc-st)
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
