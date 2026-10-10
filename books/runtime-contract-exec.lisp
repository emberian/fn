; fn: the runtime contract's executable layer over `fn-rtc-st'.
;
; The layer of books/runtime-contract.lisp written once more, over the
; abstract stobj of books/runtime-contract-pool.lisp instead of a list: every
; state read and write is an export, whose :logic is the contract's own
; operation, so each function here is proved EQUAL to its contract twin and
; the contract's keystones hold of it unchanged.  The machine is the
; constrained `fn-rtc-mx-step', which reads the state only through the borrow
; readers; `fn-rtc-def-layer' (books/runtime-contract-layer.lisp) instances
; this text for a concrete machine.
;
; One difference, and it is the point of the executable pool: an :in
; completion carries no data.  The worker has already written the octets
; into the buffer's cells in place (`fn-rtc-st-splice', the host's landing,
; while the buffer is :in-leased and hidden from every machine), so the
; executable lease end only advances the generation and returns the buffer;
; it checks the completion's count against the handle and the buffer's fill
; instead of walking a data list.  The contract's step sees the completion
; with the landed octets as its data (`fn-rtc-landed'):
;
;   (fn-rtc-x-step* e q st) = (fn-rtc-step* st (fn-rtc-landed e st) q)
;
; for every shaped state, every event and every quantum.  That the landed
; octets are the octets the operation produced is the host's assumption
; A-HOST-LANDS (books/assumptions-runtime.lisp; its consequence is proved in
; books/runtime-contract-landing.lisp): a worker
; writes exactly an input operation's octets at its handle's offset before
; the host delivers its completion.

(in-package "ACL2")
(include-book "runtime-contract-pool")

; -----------------------------------------------------------------------------
; The completion the contract sees: an :in completion that reports octets
; carries, as its data, the octets in its buffer at the handle's offset.

(defun fn-rtc-landed (e s)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))
         (hd (fn-rtc-u-hd u)) (o (fn-rtc-e-outcome e)))
    (if (and (fn-rtc-completionp e) u
             (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*)
             (member-eq (fn-rtc-get 0 o) '(:done :short)))
        (list (fn-rtc-get 0 e) (fn-rtc-get 1 e) (fn-rtc-get 2 e) (fn-rtc-get 3 e) o
              (take (nfix (fn-rtc-get 1 o))
                    (nthcdr (fn-rtc-h-off hd) (fn-rtc-bytes (fn-rtc-h-buf hd) s))))
      e)))

;; -----------------------------------------------------------------------------
; The machine, constrained: the contract's machine stepped with the view state
; of the instance the event names (`fn-rtc-deliver' passes
; (fn-rtc-view-state id inc s), and every event the layer delivers names its
; instance at positions 2 and 3).  A concrete machine reads the state only
; through the configuration and the view readers (fn-rtc-st-v-owner -v-gen
; -v-fill -v-byte -v-pool) at (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev).

(encapsulate
  (((fn-rtc-mx-step * * fn-rtc-st *) => (mv * * *)))
  (local (defun fn-rtc-mx-step (m ev fn-rtc-st q)
           (declare (xargs :stobjs fn-rtc-st))
           (fn-rtc-m-step m ev
                          (fn-rtc-make (fn-rtc-st-config fn-rtc-st) nil
                                       (fn-rtc-st-v-pool (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) fn-rtc-st)
                                       nil nil 0)
                          q)))
  (defthm fn-rtc-mx-step-is-m-step
    (equal (fn-rtc-mx-step m ev fn-rtc-st q)
           (fn-rtc-m-step m ev (fn-rtc-view-state (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) fn-rtc-st) q))))

; -----------------------------------------------------------------------------
; Every export keeps the stobj's recognizer (its {preserved} obligation as a
; rule), and the guard proofs below reason with these alone.

(defthm fn-rtc-st-p-of-set-slot
  (implies (fn-rtc-st-p fn-rtc-st) (fn-rtc-st-p (fn-rtc-st-set-slot id slot fn-rtc-st)))
  :hints (("Goal" :use fn-rtc-st-set-slot{preserved}
           :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-st-p fn-rtc-st-set-slot)))))

(defthm fn-rtc-st-p-of-set-mstate
  (implies (fn-rtc-st-p fn-rtc-st) (fn-rtc-st-p (fn-rtc-st-set-mstate id m fn-rtc-st)))
  :hints (("Goal" :use fn-rtc-st-set-mstate{preserved}
           :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-st-p fn-rtc-st-set-mstate)))))

(defthm fn-rtc-st-p-of-set-uses
  (implies (fn-rtc-st-p fn-rtc-st) (fn-rtc-st-p (fn-rtc-st-set-uses uses fn-rtc-st)))
  :hints (("Goal" :use fn-rtc-st-set-uses{preserved}
           :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-st-p fn-rtc-st-set-uses)))))

(defthm fn-rtc-st-p-of-issue
  (implies (fn-rtc-st-p fn-rtc-st) (fn-rtc-st-p (fn-rtc-st-issue use fn-rtc-st)))
  :hints (("Goal" :use fn-rtc-st-issue{preserved}
           :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-st-p fn-rtc-st-issue)))))

(defthm fn-rtc-st-p-of-set-meta
  (implies (fn-rtc-st-p fn-rtc-st) (fn-rtc-st-p (fn-rtc-st-set-meta h gen owner fn-rtc-st)))
  :hints (("Goal" :use fn-rtc-st-set-meta{preserved}
           :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-st-p fn-rtc-st-set-meta)))))

(defthm fn-rtc-st-p-of-reset
  (implies (fn-rtc-st-p fn-rtc-st) (fn-rtc-st-p (fn-rtc-st-reset h gen owner fn-rtc-st)))
  :hints (("Goal" :use fn-rtc-st-reset{preserved}
           :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-st-p fn-rtc-st-reset)))))

(defthm fn-rtc-st-p-of-splice
  (implies (fn-rtc-st-p fn-rtc-st) (fn-rtc-st-p (fn-rtc-st-splice h off data fn-rtc-st)))
  :hints (("Goal" :use fn-rtc-st-splice{preserved}
           :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-st-p fn-rtc-st-splice)))))

(defthm fn-rtc-st-p-of-release-all
  (implies (fn-rtc-st-p fn-rtc-st) (fn-rtc-st-p (fn-rtc-st-release-all id inc fn-rtc-st)))
  :hints (("Goal" :use fn-rtc-st-release-all{preserved}
           :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-st-p fn-rtc-st-release-all)))))

(defthm fn-rtc-st-p-of-init
  (implies (fn-rtc-st-p fn-rtc-st) (fn-rtc-st-p (fn-rtc-st-init cfg fn-rtc-st)))
  :hints (("Goal" :use fn-rtc-st-init{preserved}
           :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-st-p fn-rtc-st-init)))))

(defthm fn-rtc-st-reader-types
  (and (natp (fn-rtc-st-fill h fn-rtc-st))
       (natp (fn-rtc-st-gen h fn-rtc-st))
       (natp (fn-rtc-st-next-op fn-rtc-st)))
  :rule-classes ((:type-prescription :corollary (natp (fn-rtc-st-fill h fn-rtc-st)))
                 (:type-prescription :corollary (natp (fn-rtc-st-gen h fn-rtc-st)))
                 (:type-prescription :corollary (natp (fn-rtc-st-next-op fn-rtc-st)))))

(in-theory (disable fn-rtc-st-p fn-rtc-st$ap fn-rtc-shapep
                    fn-rtc-st-config fn-rtc-st-slot fn-rtc-st-mstate fn-rtc-st-uses fn-rtc-st-next-op
                    fn-rtc-st-owner fn-rtc-st-gen fn-rtc-st-fill fn-rtc-st-byte fn-rtc-st-free-slot
                    fn-rtc-st-v-owner fn-rtc-st-v-gen fn-rtc-st-v-fill fn-rtc-st-v-byte fn-rtc-st-v-pool
                    fn-rtc-st-set-slot fn-rtc-st-set-mstate fn-rtc-st-set-uses fn-rtc-st-issue
                    fn-rtc-st-set-meta fn-rtc-st-reset fn-rtc-st-splice fn-rtc-st-release-all fn-rtc-st-init))

; -----------------------------------------------------------------------------
; The layer over the stobj.  Each function is its contract twin with state
; reads and writes as exports; results put the stobj first, as the twins
; return their state first.

(defun fn-rtc-x-current-p (id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let ((slot (fn-rtc-st-slot id fn-rtc-st)))
    (and (equal (fn-rtc-s-inc slot) inc)
         (not (eq (fn-rtc-s-status slot) :free)))))

(defun fn-rtc-x-live-p (id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let ((slot (fn-rtc-st-slot id fn-rtc-st)))
    (and (equal (fn-rtc-s-inc slot) inc)
         (eq (fn-rtc-s-status slot) :live))))

; The outcome an instance is told (`fn-rtc-delivered-outcome'), with an :in
; completion's octets checked by count against the handle and the buffer's
; fill FL rather than walked.
(defun fn-rtc-x-delivered-outcome (u e fl)
  (declare (xargs :guard (natp fl)))
  (let* ((kind (fn-rtc-get 0 u)) (hd (fn-rtc-u-hd u)) (o (fn-rtc-e-outcome e))
         (tag (fn-rtc-get 0 o)) (n (fn-rtc-get 1 o)))
    (cond ((eq tag :failed)
           (if (member-eq n *fn-rtc-failure-reasons*) o '(:failed :other)))
          ((not (member-eq tag '(:done :short))) o)
          ((member-eq kind '(:hand :pool :grant))
           (if (and (eq tag :done) (equal n 0)) o '(:failed :malformed-completion)))
          ((member-eq kind *fn-rtc-in-kinds*)
           (if (and (natp n)
                    (<= n (fn-rtc-h-len hd))
                    (or (zp n) (<= (+ (fn-rtc-h-off hd) n) fl)))
               o
             '(:failed :malformed-completion)))
          ((member-eq kind *fn-rtc-out-kinds*)
           (if (<= (nfix n) (fn-rtc-h-len hd)) o '(:failed :malformed-completion)))
          (t o))))

(defun fn-rtc-x-handed-to-live-p (o out fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (and (eq (fn-rtc-get 0 o) :handed)
       (eq (fn-rtc-get 0 out) :done)
       (fn-rtc-x-live-p (nfix (fn-rtc-get 3 o)) (fn-rtc-get 4 o) fn-rtc-st)))

; U has been removed from the uses.  If no use still holds its buffer at its
; generation, the lease ends (`fn-rtc-lease-return'): generation + 1, to a
; delivered hand's target, else back to its return pair's workspace when that
; instance is live or closing, else :free; the octets are where the worker
; left them.
(defun fn-rtc-x-end-lease (u e fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let ((hd (fn-rtc-u-hd u)))
    (if (or (not (fn-rtc-handlep hd))
            (fn-rtc-holds-p (fn-rtc-h-buf hd) (fn-rtc-h-gen hd) (fn-rtc-st-uses fn-rtc-st)))
        fn-rtc-st
      (let* ((h (fn-rtc-h-buf hd)) (o (fn-rtc-st-owner h fn-rtc-st))
             (rid (nfix (fn-rtc-get 1 o))) (rinc (fn-rtc-get 2 o))
             (back (and (fn-rtc-x-current-p rid rinc fn-rtc-st)
                        (member-eq (fn-rtc-s-status (fn-rtc-st-slot rid fn-rtc-st)) '(:live :closing))))
             (out (fn-rtc-x-delivered-outcome u e (fn-rtc-st-fill h fn-rtc-st))))
        (fn-rtc-st-set-meta h (+ 1 (fn-rtc-st-gen h fn-rtc-st))
                            (cond ((fn-rtc-x-handed-to-live-p o out fn-rtc-st)
                                   (list :workspace (nfix (fn-rtc-get 3 o)) (fn-rtc-get 4 o)))
                                  (back (list :workspace rid rinc))
                                  (t '(:free)))
                            fn-rtc-st)))))

(defun fn-rtc-x-retire-drained (id fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let ((slot (fn-rtc-st-slot id fn-rtc-st)))
    (if (and (eq (fn-rtc-s-status slot) :draining)
             (not (fn-rtc-uses-of-slot-p id (fn-rtc-s-inc slot) (fn-rtc-st-uses fn-rtc-st))))
        (fn-rtc-st-set-slot id (list (fn-rtc-s-inc slot) :free nil) fn-rtc-st)
      fn-rtc-st)))

(defun fn-rtc-x-end-use (e fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let* ((key (fn-rtc-key e))
         (u (fn-rtc-find-use key (fn-rtc-st-uses fn-rtc-st))))
    (if (not (and (fn-rtc-completionp e) u))
        fn-rtc-st
      (let* ((fn-rtc-st (fn-rtc-st-set-uses (fn-rtc-remove-use key (fn-rtc-st-uses fn-rtc-st)) fn-rtc-st))
             (fn-rtc-st (fn-rtc-x-end-lease u e fn-rtc-st)))
        (fn-rtc-x-retire-drained (fn-rtc-e-id e) fn-rtc-st)))))

; Requests from instance (ID INC): (mv st actions refused cost).

(defun fn-rtc-x-req-acquire (r id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let ((h (fn-rtc-get 1 r)) (cfg (fn-rtc-st-config fn-rtc-st)))
    (if (and (natp h) (< h (fn-rtc-nbufs cfg))
             (equal (fn-rtc-home h cfg) (nfix id))
             (equal (fn-rtc-st-owner h fn-rtc-st) '(:free)))
        (let ((fn-rtc-st (fn-rtc-st-reset h (+ 1 (fn-rtc-st-gen h fn-rtc-st))
                                          (list :workspace id inc) fn-rtc-st)))
          (mv fn-rtc-st nil nil 1))
      (mv fn-rtc-st nil (list r) 1))))

(defun fn-rtc-x-req-write (r id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let ((h (fn-rtc-get 1 r)) (g (fn-rtc-get 2 r)) (off (fn-rtc-get 3 r))
        (data (fn-rtc-get 4 r)))
    (if (and (natp h) (< h (fn-rtc-nbufs (fn-rtc-st-config fn-rtc-st)))
             (equal (fn-rtc-st-owner h fn-rtc-st) (list :workspace id inc))
             (equal (fn-rtc-st-gen h fn-rtc-st) g)
             (natp off) (<= off (fn-rtc-st-fill h fn-rtc-st))
             (fn-cbor-octet-listp data)
             (<= (+ off (len data)) (fn-rtc-buf-cap h (fn-rtc-st-config fn-rtc-st))))
        (let ((fn-rtc-st (fn-rtc-st-splice h off data fn-rtc-st)))
          (mv fn-rtc-st nil nil (+ 1 (len data))))
      (mv fn-rtc-st nil (list r) 1))))

(defun fn-rtc-x-req-release (r id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let ((h (fn-rtc-get 1 r)) (g (fn-rtc-get 2 r)))
    (if (and (natp h) (< h (fn-rtc-nbufs (fn-rtc-st-config fn-rtc-st)))
             (equal (fn-rtc-st-owner h fn-rtc-st) (list :workspace id inc))
             (equal (fn-rtc-st-gen h fn-rtc-st) g))
        (let ((fn-rtc-st (fn-rtc-st-set-meta h g '(:free) fn-rtc-st)))
          (mv fn-rtc-st nil nil 1))
      (mv fn-rtc-st nil (list r) 1))))

(defun fn-rtc-x-req-close (r id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let ((slot (fn-rtc-st-slot id fn-rtc-st)))
    (if (and (fn-rtc-x-live-p id inc fn-rtc-st)
             (< (fn-rtc-nstatic (fn-rtc-st-config fn-rtc-st)) (nfix id)))
        (let* ((op (fn-rtc-st-next-op fn-rtc-st))
               (fn-rtc-st (fn-rtc-st-set-slot id (list inc :closing (fn-rtc-s-res slot)) fn-rtc-st))
               (fn-rtc-st (fn-rtc-st-issue (list :close id inc op nil) fn-rtc-st)))
          (mv fn-rtc-st
              (list (list :close id inc op (list (fn-rtc-s-res slot))))
              nil
              (+ 1 (fn-rtc-use-bound (fn-rtc-st-config fn-rtc-st)))))
      (mv fn-rtc-st nil (list r) 1))))

(defun fn-rtc-x-submit-okp (kind hd id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let* ((h (fn-rtc-h-buf hd)) (o (fn-rtc-st-owner h fn-rtc-st))
         (fl (fn-rtc-st-fill h fn-rtc-st)) (cfg (fn-rtc-st-config fn-rtc-st))
         (own (equal o (list :workspace id inc))))
    (and (fn-rtc-handlep hd)
         (< h (fn-rtc-nbufs cfg))
         (equal (fn-rtc-st-gen h fn-rtc-st) (fn-rtc-h-gen hd))
         (cond
          ((member-eq kind *fn-rtc-in-kinds*)
           (and own
                (<= (fn-rtc-h-off hd) fl)
                (<= (+ (fn-rtc-h-off hd) (fn-rtc-h-len hd)) (fn-rtc-buf-cap h cfg))))
          ((eq kind :hand)
           (and own
                (equal (fn-rtc-h-off hd) 0)
                (equal (fn-rtc-h-len hd) fl)))
          (t
           (and (or own (equal o (list :leased id inc :out)))
                (<= (+ (fn-rtc-h-off hd) (fn-rtc-h-len hd)) fl)
                (<= (+ (fn-rtc-h-off hd) (fn-rtc-h-len hd)) (fn-rtc-buf-cap h cfg))))))))

(defun fn-rtc-x-hand-target-okp (extra id fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let ((to (fn-rtc-get 0 extra)) (tinc (fn-rtc-get 1 extra))
        (cfg (fn-rtc-st-config fn-rtc-st)))
    (and (natp to) (natp tinc)
         (<= 1 to) (< to (fn-rtc-nslots cfg))
         (not (equal to (nfix id)))
         (implies (< (fn-rtc-nstatic cfg) (nfix id)) (<= to (fn-rtc-nstatic cfg))))))

(defun fn-rtc-x-req-submit (r id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let* ((kind (fn-rtc-get 1 r)) (hd (fn-rtc-get 2 r)) (extra (fn-rtc-get 3 r))
         (res (fn-rtc-s-res (fn-rtc-st-slot id fn-rtc-st)))
         (cost (+ 1 (fn-rtc-use-bound (fn-rtc-st-config fn-rtc-st)))))
    (cond
     ((not (and (member-eq kind *fn-rtc-machine-kinds*)
                (fn-rtc-x-live-p id inc fn-rtc-st)
                (fn-rtc-extrap extra)
                (implies (eq kind :hand) (fn-rtc-x-hand-target-okp extra id fn-rtc-st))
                (or (eq kind :hand)
                    (not (fn-rtc-kind-out-p (if (eq kind :pool) :wait kind) id inc
                                            (fn-rtc-st-uses fn-rtc-st))))))
      (mv fn-rtc-st nil (list r) cost))
     ((eq kind :pool)
      (if (and (null hd) (null extra))
          (let* ((op (fn-rtc-st-next-op fn-rtc-st))
                 (fn-rtc-st (fn-rtc-st-issue (list :wait id inc op nil) fn-rtc-st)))
            (mv fn-rtc-st nil nil cost))
        (mv fn-rtc-st nil (list r) cost)))
     ((not (fn-rtc-buffered-kind-p kind))
      (if (null hd)
          (let* ((op (fn-rtc-st-next-op fn-rtc-st))
                 (fn-rtc-st (fn-rtc-st-issue (list kind id inc op nil) fn-rtc-st)))
            (mv fn-rtc-st (list (list kind id inc op (cons res extra))) nil cost))
        (mv fn-rtc-st nil (list r) cost)))
     ((not (fn-rtc-x-submit-okp kind hd id inc fn-rtc-st))
      (mv fn-rtc-st nil (list r) cost))
     (t
      (let* ((h (fn-rtc-h-buf hd))
             (dir (if (member-eq kind *fn-rtc-in-kinds*) :in :out))
             (o2 (if (eq kind :hand)
                     (list :handed id inc (fn-rtc-get 0 extra) (fn-rtc-get 1 extra))
                   (list :leased id inc dir)))
             (fn-rtc-st (if (equal (fn-rtc-st-owner h fn-rtc-st) (list :workspace id inc))
                            (fn-rtc-st-set-meta h (fn-rtc-st-gen h fn-rtc-st) o2 fn-rtc-st)
                          fn-rtc-st))
             (op (fn-rtc-st-next-op fn-rtc-st))
             (fn-rtc-st (fn-rtc-st-issue (list kind id inc op hd) fn-rtc-st)))
        (mv fn-rtc-st (list (list kind id inc op (list* hd res extra))) nil cost))))))

(defun fn-rtc-x-req-cancel (r id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let ((kind (fn-rtc-get 1 r)) (uses (fn-rtc-st-uses fn-rtc-st))
        (cost (+ 1 (fn-rtc-use-bound (fn-rtc-st-config fn-rtc-st)))))
    (if (and (member-eq kind *fn-rtc-machine-kinds*)
             (not (member-eq kind '(:hand :pool)))
             (fn-rtc-x-current-p id inc fn-rtc-st)
             (fn-rtc-kind-out-p kind id inc uses))
        (mv fn-rtc-st (list (list :cancel id inc (fn-rtc-kind-op kind id inc uses) (list kind))) nil cost)
      (mv fn-rtc-st nil (list r) cost))))

(defun fn-rtc-x-request (r id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (case (fn-rtc-get 0 r)
    (:acquire (fn-rtc-x-req-acquire r id inc fn-rtc-st))
    (:write (fn-rtc-x-req-write r id inc fn-rtc-st))
    (:release (fn-rtc-x-req-release r id inc fn-rtc-st))
    (:close (fn-rtc-x-req-close r id inc fn-rtc-st))
    (:submit (fn-rtc-x-req-submit r id inc fn-rtc-st))
    (:cancel (fn-rtc-x-req-cancel r id inc fn-rtc-st))
    (otherwise (mv fn-rtc-st nil (list r) 1))))

(defthm fn-rtc-x-request-lists
  (and (true-listp (mv-nth 1 (fn-rtc-x-request r id inc fn-rtc-st)))
       (true-listp (mv-nth 2 (fn-rtc-x-request r id inc fn-rtc-st))))
  :hints (("Goal" :expand ((fn-rtc-x-request r id inc fn-rtc-st)
                           (fn-rtc-x-req-acquire r id inc fn-rtc-st) (fn-rtc-x-req-write r id inc fn-rtc-st)
                           (fn-rtc-x-req-release r id inc fn-rtc-st) (fn-rtc-x-req-close r id inc fn-rtc-st)
                           (fn-rtc-x-req-submit r id inc fn-rtc-st) (fn-rtc-x-req-cancel r id inc fn-rtc-st))
           :in-theory (disable fn-rtc-x-req-submit fn-rtc-x-req-cancel fn-rtc-x-req-close
                               fn-rtc-x-req-write fn-rtc-x-req-acquire fn-rtc-x-req-release
                               fn-rtc-x-submit-okp fn-rtc-x-live-p fn-rtc-x-current-p fn-rtc-kind-out-p
                               fn-rtc-kind-op fn-rtc-extrap fn-rtc-buffered-kind-p fn-rtc-use-bound
                               fn-rtc-s-res fn-rtc-h-buf fn-rtc-x-hand-target-okp member-equal))))

(in-theory (disable fn-rtc-x-req-submit fn-rtc-x-req-cancel fn-rtc-x-req-close
                    fn-rtc-x-req-write fn-rtc-x-req-acquire fn-rtc-x-req-release fn-rtc-x-request))

(defun fn-rtc-x-requests (reqs id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (if (consp reqs)
      (mv-let (fn-rtc-st acts1 ref1 c1)
        (fn-rtc-x-request (car reqs) id inc fn-rtc-st)
        (mv-let (fn-rtc-st acts2 ref2 c2)
          (fn-rtc-x-requests (cdr reqs) id inc fn-rtc-st)
          (mv fn-rtc-st (append acts1 acts2) (append ref1 ref2) (+ (nfix c1) (nfix c2)))))
    (mv fn-rtc-st nil nil 0)))

(defthm fn-rtc-x-requests-lists
  (true-listp (mv-nth 1 (fn-rtc-x-requests reqs id inc fn-rtc-st))))

; -----------------------------------------------------------------------------
; Admission: the listener's :accept and :grant.

; The first free pool buffer at or after H (H at least the first pool
; buffer; the home buffers below it are never pool buffers).
(defun fn-rtc-x-free-pool-buf-loop (h n fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :guard (and (natp h) (natp n))
                  :measure (nfix (- (nfix n) (nfix h)))))
  (let ((h (nfix h)))
    (if (< h (nfix n))
        (if (equal (fn-rtc-st-owner h fn-rtc-st) '(:free))
            h
          (fn-rtc-x-free-pool-buf-loop (+ 1 h) n fn-rtc-st))
      nil)))

(defun fn-rtc-x-free-pool-buf (fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let ((cfg (fn-rtc-st-config fn-rtc-st)))
    (fn-rtc-x-free-pool-buf-loop (fn-rtc-nhome cfg) (fn-rtc-nbufs cfg) fn-rtc-st)))

(defun fn-rtc-x-arm-accept (fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (if (and (fn-rtc-st-free-slot fn-rtc-st)
           (not (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-st-uses fn-rtc-st))))
      (let* ((op (fn-rtc-st-next-op fn-rtc-st))
             (fn-rtc-st (fn-rtc-st-issue (list :accept 0 0 op nil) fn-rtc-st)))
        (mv fn-rtc-st (list (list :accept 0 0 op (list nil)))))
    (mv fn-rtc-st nil)))

(defun fn-rtc-x-arm-grant (fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (if (and (fn-rtc-x-free-pool-buf fn-rtc-st)
           (fn-rtc-oldest-wait (fn-rtc-st-uses fn-rtc-st))
           (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-st-uses fn-rtc-st))))
      (let* ((op (fn-rtc-st-next-op fn-rtc-st))
             (fn-rtc-st (fn-rtc-st-issue (list :grant 0 0 op nil) fn-rtc-st)))
        (mv fn-rtc-st (list (list :grant 0 0 op (list nil)))))
    (mv fn-rtc-st nil)))

(defun fn-rtc-x-rearm (fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (mv-let (fn-rtc-st a1) (fn-rtc-x-arm-accept fn-rtc-st)
    (mv-let (fn-rtc-st a2) (fn-rtc-x-arm-grant fn-rtc-st)
      (mv fn-rtc-st (append a1 a2)))))

(defthm fn-rtc-x-rearm-lists
  (true-listp (mv-nth 1 (fn-rtc-x-rearm fn-rtc-st))))

(defun fn-rtc-x-grant-one (fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let ((h (fn-rtc-x-free-pool-buf fn-rtc-st))
        (w (fn-rtc-oldest-wait (fn-rtc-st-uses fn-rtc-st))))
    (if (and h w)
        (let* ((id (nfix (fn-rtc-get 1 w))) (inc (fn-rtc-get 2 w)) (op (fn-rtc-get 3 w))
               (g (+ 1 (fn-rtc-st-gen h fn-rtc-st)))
               (hd (list h g 0 0))
               (res (fn-rtc-s-res (fn-rtc-st-slot id fn-rtc-st)))
               (fn-rtc-st (fn-rtc-st-set-uses (fn-rtc-replace-use (fn-rtc-key w) (list :pool id inc op hd)
                                                                  (fn-rtc-st-uses fn-rtc-st))
                                              fn-rtc-st))
               (fn-rtc-st (fn-rtc-st-reset h g (list :leased id inc :in) fn-rtc-st)))
          (mv fn-rtc-st (list (list :pool id inc op (list hd res)))))
      (mv fn-rtc-st nil))))

(defun fn-rtc-x-grant (n fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :guard (natp n)))
  (if (zp n)
      (mv fn-rtc-st nil)
    (mv-let (fn-rtc-st a1) (fn-rtc-x-grant-one fn-rtc-st)
      (if (consp a1)
          (mv-let (fn-rtc-st a2) (fn-rtc-x-grant (- n 1) fn-rtc-st)
            (mv fn-rtc-st (append a1 a2)))
        (mv fn-rtc-st nil)))))

(defthm fn-rtc-x-grant-lists
  (true-listp (mv-nth 1 (fn-rtc-x-grant n fn-rtc-st)))
  :hints (("Goal" :in-theory (disable fn-rtc-x-grant-one))))

; -----------------------------------------------------------------------------
; Which completions act on an instance (`fn-rtc-acts-on-p').

(defun fn-rtc-x-hand-delivers-p (e fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (and (fn-rtc-completionp e)
       (eq (fn-rtc-e-kind e) :hand)
       (let* ((u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-st-uses fn-rtc-st)))
              (hd (fn-rtc-u-hd u)))
         (and u (fn-rtc-handlep hd)
              (fn-rtc-x-handed-to-live-p
               (fn-rtc-st-owner (fn-rtc-h-buf hd) fn-rtc-st)
               (fn-rtc-x-delivered-outcome u e (fn-rtc-st-fill (fn-rtc-h-buf hd) fn-rtc-st))
               fn-rtc-st)))))

(defun fn-rtc-x-acts-on-p (e fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (or (and (fn-rtc-completionp e)
           (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-st-uses fn-rtc-st))
           (let ((slot (fn-rtc-st-slot (fn-rtc-e-id e) fn-rtc-st)))
             (and (equal (fn-rtc-s-inc slot) (fn-rtc-e-inc e))
                  (if (eq (fn-rtc-e-kind e) :close)
                      (eq (fn-rtc-s-status slot) :closing)
                    (eq (fn-rtc-s-status slot) :live)))))
      (fn-rtc-x-hand-delivers-p e fn-rtc-st)))

; -----------------------------------------------------------------------------
; Delivery and the branches.

(defun fn-rtc-x-deliver (id inc ev q fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (mv-let (m2 reqs cm)
    (fn-rtc-mx-step (fn-rtc-st-mstate id fn-rtc-st) ev fn-rtc-st (nfix q))
    (let ((fn-rtc-st (fn-rtc-st-set-mstate id m2 fn-rtc-st)))
      (mv-let (fn-rtc-st acts refused cr)
        (fn-rtc-x-requests reqs id inc fn-rtc-st)
        (mv fn-rtc-st acts refused (+ (nfix cm) (nfix cr)))))))

(defun fn-rtc-x-accept-branch (out q fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let ((j (fn-rtc-st-free-slot fn-rtc-st))
        (r (fn-rtc-get 1 out)))
    (if (and (eq (fn-rtc-get 0 out) :done) j (natp r) (< r (expt 2 64)))
        (let* ((jinc (+ 1 (fn-rtc-s-inc (fn-rtc-st-slot j fn-rtc-st))))
               (fn-rtc-st (fn-rtc-st-set-slot j (list jinc :live r) fn-rtc-st))
               (fn-rtc-st (fn-rtc-st-set-mstate j (fn-rtc-m-init) fn-rtc-st)))
          (mv-let (fn-rtc-st acts refused c)
            (fn-rtc-x-deliver j jinc (fn-rtc-ev :accept out j jinc nil) q fn-rtc-st)
            (mv-let (fn-rtc-st acts2) (fn-rtc-x-rearm fn-rtc-st)
              (mv fn-rtc-st (append acts acts2) refused c))))
      (mv-let (fn-rtc-st acts2) (fn-rtc-x-rearm fn-rtc-st)
        (mv fn-rtc-st acts2 nil 0)))))

(defun fn-rtc-x-close-branch (id inc fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let* ((fn-rtc-st (fn-rtc-st-release-all id inc fn-rtc-st))
         (status (if (fn-rtc-uses-of-slot-p id inc (fn-rtc-st-uses fn-rtc-st)) :draining :free))
         (res (fn-rtc-s-res (fn-rtc-st-slot id fn-rtc-st)))
         (fn-rtc-st (fn-rtc-st-set-slot id (list inc status (if (eq status :free) nil res)) fn-rtc-st))
         (fn-rtc-st (fn-rtc-st-set-mstate id (fn-rtc-m-init) fn-rtc-st)))
    (fn-rtc-x-rearm fn-rtc-st)))

(defthm fn-rtc-x-deliver-cost
  (natp (mv-nth 3 (fn-rtc-x-deliver id inc ev q fn-rtc-st)))
  :hints (("Goal" :expand ((fn-rtc-x-deliver id inc ev q fn-rtc-st)))))

(defthm fn-rtc-x-accept-branch-cost
  (natp (mv-nth 3 (fn-rtc-x-accept-branch out q fn-rtc-st)))
  :hints (("Goal" :expand ((fn-rtc-x-accept-branch out q fn-rtc-st))
           :in-theory (disable fn-rtc-x-deliver fn-rtc-x-rearm))))

(in-theory (disable fn-rtc-x-acts-on-p fn-rtc-x-hand-delivers-p fn-rtc-x-end-use fn-rtc-x-delivered-outcome
                    fn-rtc-x-accept-branch fn-rtc-x-close-branch fn-rtc-x-deliver fn-rtc-x-rearm
                    fn-rtc-x-grant))

; One step: (mv st actions refused cost), `fn-rtc-step*' over the stobj.
(defthm fn-rtc-x-deliver-lists
  (true-listp (mv-nth 1 (fn-rtc-x-deliver id inc ev q fn-rtc-st)))
  :hints (("Goal" :expand ((fn-rtc-x-deliver id inc ev q fn-rtc-st)))))

(defthm fn-rtc-x-accept-branch-lists
  (true-listp (mv-nth 1 (fn-rtc-x-accept-branch out q fn-rtc-st)))
  :hints (("Goal" :expand ((fn-rtc-x-accept-branch out q fn-rtc-st)))))

(defthm fn-rtc-x-close-branch-lists
  (true-listp (mv-nth 1 (fn-rtc-x-close-branch id inc fn-rtc-st)))
  :hints (("Goal" :expand ((fn-rtc-x-close-branch id inc fn-rtc-st)))))

(defun fn-rtc-x-step* (e q fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st
                  :guard-hints (("Goal" :in-theory (disable fn-rtc-ev fn-rtc-find-use fn-rtc-x-end-use
                                                            fn-rtc-grant-unit fn-rtc-use-bound)))))
  (let* ((cfg (fn-rtc-st-config fn-rtc-st))
         (base (+ 4 (* 8 (fn-rtc-use-bound cfg)) (* 2 (fn-rtc-nslots cfg)) (fn-rtc-nbufs cfg))))
    (if (not (fn-rtc-x-acts-on-p e fn-rtc-st))
        (let ((fn-rtc-st (fn-rtc-x-end-use e fn-rtc-st)))
          (mv-let (fn-rtc-st acts) (fn-rtc-x-rearm fn-rtc-st)
            (mv fn-rtc-st acts nil base)))
      (let* ((kind (fn-rtc-e-kind e)) (id (fn-rtc-e-id e)) (inc (fn-rtc-e-inc e))
             (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-st-uses fn-rtc-st)))
             (h (fn-rtc-h-buf (fn-rtc-u-hd u)))
             (out (fn-rtc-x-delivered-outcome u e (fn-rtc-st-fill h fn-rtc-st)))
             (base (+ base (if (member-eq kind *fn-rtc-in-kinds*)
                               (fn-rtc-h-len (fn-rtc-u-hd u))
                             0)))
             (delivers (fn-rtc-x-hand-delivers-p e fn-rtc-st))
             (o (fn-rtc-st-owner h fn-rtc-st))
             (hd2 (list h (+ 1 (fn-rtc-st-gen h fn-rtc-st)) 0 (fn-rtc-st-fill h fn-rtc-st)))
             (fn-rtc-st (fn-rtc-x-end-use e fn-rtc-st)))
        (cond
         (delivers
          (let ((to (nfix (fn-rtc-get 3 o))) (tinc (fn-rtc-get 4 o)))
            (mv-let (fn-rtc-st acts refused c)
              (fn-rtc-x-deliver to tinc (fn-rtc-ev :handed out to tinc (list id inc hd2)) q fn-rtc-st)
              (mv-let (fn-rtc-st acts2) (fn-rtc-x-rearm fn-rtc-st)
                (mv fn-rtc-st (append acts acts2) refused (+ base c))))))
         ((eq kind :accept)
          (mv-let (fn-rtc-st acts refused c) (fn-rtc-x-accept-branch out q fn-rtc-st)
            (mv fn-rtc-st acts refused (+ base (nfix c)))))
         ((eq kind :close)
          (mv-let (fn-rtc-st acts) (fn-rtc-x-close-branch id inc fn-rtc-st)
            (mv fn-rtc-st acts nil (+ base (fn-rtc-nbufs cfg)))))
         ((eq kind :grant)
          (mv-let (fn-rtc-st acts) (fn-rtc-x-grant (fn-rtc-npool cfg) fn-rtc-st)
            (mv-let (fn-rtc-st acts2) (fn-rtc-x-rearm fn-rtc-st)
              (mv fn-rtc-st (append acts acts2) nil
                  (+ base (* (fn-rtc-npool cfg) (fn-rtc-grant-unit cfg)))))))
         ((eq kind :pool)
          (mv-let (fn-rtc-st acts refused c)
            (fn-rtc-x-deliver id inc (fn-rtc-ev kind out id inc (list hd2)) q fn-rtc-st)
            (mv-let (fn-rtc-st acts2) (fn-rtc-x-rearm fn-rtc-st)
              (mv fn-rtc-st (append acts acts2) refused (+ base c)))))
         ((eq kind :hand)
          (mv-let (fn-rtc-st acts refused c)
            (fn-rtc-x-deliver id inc
                              (fn-rtc-ev kind (if (eq (fn-rtc-get 0 out) :done) '(:failed :gone) out)
                                         id inc (list hd2))
                              q fn-rtc-st)
            (mv-let (fn-rtc-st acts2) (fn-rtc-x-rearm fn-rtc-st)
              (mv fn-rtc-st (append acts acts2) refused (+ base c)))))
         (t
          (mv-let (fn-rtc-st acts refused c)
            (fn-rtc-x-deliver id inc (fn-rtc-ev kind out id inc nil) q fn-rtc-st)
            (mv-let (fn-rtc-st acts2) (fn-rtc-x-rearm fn-rtc-st)
              (mv fn-rtc-st (append acts acts2) refused (+ base c))))))))))

(defun fn-rtc-x-step (e q fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (mv-let (fn-rtc-st acts refused cost) (fn-rtc-x-step* e q fn-rtc-st)
    (declare (ignore refused cost))
    (mv fn-rtc-st acts)))

; The static instances J .. J+N-1: live at incarnation 1 in their initial
; states.
(defun fn-rtc-x-statics (j n fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :guard (and (natp j) (natp n)) :measure (nfix n)))
  (if (zp n)
      fn-rtc-st
    (let* ((fn-rtc-st (fn-rtc-st-set-slot j *fn-rtc-static-slot* fn-rtc-st))
           (fn-rtc-st (fn-rtc-st-set-mstate j (fn-rtc-m-static-init j) fn-rtc-st)))
      (fn-rtc-x-statics (+ 1 (nfix j)) (- n 1) fn-rtc-st))))

; A fresh state for configuration CFG: the static instances live, the
; listener's :accept armed.
(defun fn-rtc-x-init (cfg fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let* ((fn-rtc-st (fn-rtc-st-init cfg fn-rtc-st))
         (fn-rtc-st (fn-rtc-x-statics 1 (fn-rtc-nstatic (fn-rtc-st-config fn-rtc-st)) fn-rtc-st)))
    (fn-rtc-x-rearm fn-rtc-st)))
