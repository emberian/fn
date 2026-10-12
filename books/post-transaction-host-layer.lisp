; The process product: POST at slot 1, the leased reader at every other slot.
(in-package "ACL2")
(include-book "post-transaction-layer")
(include-book "runtime-contract-host-lease")
(local (in-theory (current-theory 'fn-ptx-p5)))
(set-verify-guards-eagerness 2)

(defun fn-pthm-step (m ev fn-rtc-st q)
  (declare (xargs :stobjs fn-rtc-st))
  (if (equal (fn-rtc-ev-id ev) 1) (fn-ptx-step m ev fn-rtc-st q) (fn-hlm-step m ev fn-rtc-st q)))
(defun fn-pthm-init () (fn-hlm-init))
(defun fn-pthm-static-init (j) (if (equal j 1) (fn-ptx-closed) (fn-hlm-static-init j)))

(defun fn-pthm-committedp (m) (declare (xargs :guard t)) (fn-ptx-committedp m))
(defun fn-pthm-c () (declare (xargs :guard t)) (max (fn-ptx-c) (fn-hlm-c)))
(defun fn-pthm-max-reqs () (declare (xargs :guard t)) (max (fn-ptx-max-reqs) (fn-hlm-max-reqs)))
(defun fn-pthm-max-state () (declare (xargs :guard t)) (max (fn-ptx-max-state) (fn-hlm-max-state)))

(defthm fn-pthm-step-reads-view
  (equal (fn-pthm-step m ev (fn-rtc-view-state (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st) q)
         (fn-pthm-step m ev st q))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pthm-step))
           :use (fn-ptx-step-reads-view fn-hlm-step-reads-view))))

; The generator's defun-nx model takes arbitrary logical view states.
; Eagerness 1 verifies its executable stobj copies without imposing stobj shape on that model.
(set-verify-guards-eagerness 1)

(fn-rtc-def-layer fn-pth
  :step fn-pthm-step :init fn-pthm-init :static-init fn-pthm-static-init
  :committedp fn-pthm-committedp :c fn-pthm-c :max-reqs fn-pthm-max-reqs :max-state fn-pthm-max-state
  :reads-view fn-pthm-step-reads-view
  :hints (("Goal" :in-theory (e/d (fn-pth-m-step fn-pthm-step fn-pthm-init fn-pthm-static-init
                                   fn-pthm-committedp fn-pthm-c fn-pthm-max-reqs fn-pthm-max-state
                                   fn-hlm-step fn-hlm-init fn-hlm-static-init fn-hlm-c
                                   fn-hlm-max-reqs fn-hlm-max-state)
                                  (fn-ptx-step fn-ptx-closed fn-ptx-committedp fn-ptx-c fn-ptx-max-reqs))
           :use ((:instance fn-ptx-step-facts (st pool) (q (nfix q)))
                 (:instance fn-ptx-step-nfix-q (st pool))
                 (:instance fn-ptx-commits-only-on-fsync-done (st pool))
                 (:instance fn-hlm-step-facts (st pool))
                 fn-ptx-closed-facts))))

; The store-opened facts of contract v2.2 for this instance (KO1 fn-rtc-init-arms-the-opened, KO1a
; fn-rtc-init-emits-the-opened, KO1b fn-rtc-opened-use-is-static, KO2 fn-rtc-opened-acts-at-most-once,
; KO2r fn-rtc-machine-cannot-request-the-opened, KO1c fn-rtc-opened-acts-once-per-incarnation, KO3
; fn-rtc-opened-steps-its-slot), by the generator's functional instance: the machine's :opened
; arrives once, at its static slot, and steps exactly that slot's machine.
;; KO1c quantifies over runs (fn-rtc-run), which the generator does not copy: the instance's run.
(defun fn-pth-run (s events q)
  (if (consp events)
      (mv-let (s2 acts) (fn-pth-step s (car events) q)
        (declare (ignore acts))
        (fn-pth-run s2 (cdr events) q))
    s))

(make-event
 (let* ((prefix 'fn-pth)
        (copied (fn-rtc-layer-alist prefix (append *fn-rtc-layer-spec-fns* *fn-rtc-layer-exec-fns*)))
        (alist (append '((fn-rtc-m-init . fn-pthm-init) (fn-rtc-m-static-init . fn-pthm-static-init)
                         (fn-rtc-m-step . fn-pth-m-step) (fn-rtc-m-committedp . fn-pthm-committedp)
                         (fn-rtc-m-c . fn-pthm-c) (fn-rtc-m-max-reqs . fn-pthm-max-reqs)
                         (fn-rtc-m-max-state . fn-pthm-max-state) (fn-rtc-mx-step . fn-pthm-step)
                         (fn-rtc-run . fn-pth-run))
                       copied))
        (obligations (cons 'natp (fn-rtc-layer-names prefix
                                   '(fn-rtc-m-constants fn-rtc-mx-step-is-m-step fn-rtc-m-step-is-charged
                                     fn-rtc-m-step-requests-are-bounded fn-rtc-m-init-is-bounded
                                     fn-rtc-m-step-state-is-bounded fn-rtc-m-init-is-uncommitted
                                     fn-rtc-m-static-init-is-bounded fn-rtc-m-static-init-is-uncommitted
                                     fn-rtc-m-commits-only-on-fsync-done)))))
   (cons 'progn
         (fn-rtc-layer-keystone-events
          '(fn-rtc-init-arms-the-opened fn-rtc-init-emits-the-opened fn-rtc-opened-use-is-static
            fn-rtc-opened-acts-at-most-once fn-rtc-machine-cannot-request-the-opened
            fn-rtc-opened-steps-its-slot)
          prefix alist (fn-rtc-layer-fi-alist alist) (cons 'fn-pth-run (strip-cdrs copied)) obligations (w state)))))

; KO1c: the generator's one-step theory unrolls the run in the goal itself, so the instance is
; taken in the minimal theory and the copies' definitions (with the run's) prove its constraints.
(defthm fn-pth-run-def
  (equal (fn-pth-run s events q)
         (if (consp events)
             (fn-pth-run (mv-nth 0 (fn-pth-step s (car events) q)) (cdr events) q)
           s))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-pth-run) (theory 'minimal-theory)))))
(make-event
 (let* ((prefix 'fn-pth)
        (copied (fn-rtc-layer-alist prefix (append *fn-rtc-layer-spec-fns* *fn-rtc-layer-exec-fns*)))
        (alist (append '((fn-rtc-m-init . fn-pthm-init) (fn-rtc-m-static-init . fn-pthm-static-init)
                         (fn-rtc-m-step . fn-pth-m-step) (fn-rtc-m-committedp . fn-pthm-committedp)
                         (fn-rtc-m-c . fn-pthm-c) (fn-rtc-m-max-reqs . fn-pthm-max-reqs)
                         (fn-rtc-m-max-state . fn-pthm-max-state) (fn-rtc-mx-step . fn-pthm-step)
                         (fn-rtc-run . fn-pth-run))
                       copied))
        (obligations (cons 'natp (fn-rtc-layer-names prefix
                                   '(fn-rtc-m-constants fn-rtc-mx-step-is-m-step fn-rtc-m-step-is-charged
                                     fn-rtc-m-step-requests-are-bounded fn-rtc-m-init-is-bounded
                                     fn-rtc-m-step-state-is-bounded fn-rtc-m-init-is-uncommitted
                                     fn-rtc-m-static-init-is-bounded fn-rtc-m-static-init-is-uncommitted
                                     fn-rtc-m-commits-only-on-fsync-done)))))
   `(defthm fn-pth-opened-acts-once-per-incarnation
      ,(fn-rtc-layer-rename (getpropc 'fn-rtc-opened-acts-once-per-incarnation 'untranslated-theorem nil (w state)) alist)
      :hints (("Goal" :use ((:functional-instance fn-rtc-opened-acts-once-per-incarnation ,@(fn-rtc-layer-fi-alist alist)))
               :in-theory (theory 'minimal-theory))
              (and stable-under-simplificationp
                   '(:in-theory (union-theories (theory 'minimal-theory) ',(append (strip-cdrs copied) obligations))
                     :use (fn-pth-run-def)))))))

(defthm fn-pth-at-the-owner
  (implies (equal (fn-rtc-ev-id ev) 1)
           (equal (fn-pthm-step m ev st q) (fn-ptx-step m ev st q)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pthm-step)))))

(defthm fn-pth-at-a-connection
  (implies (not (equal (fn-rtc-ev-id ev) 1))
           (equal (fn-pthm-step m ev st q) (fn-hlm-step m ev st q)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-pthm-step)))))

; The generated predicate checks all cons cells against the common product bound.
; Split out the listener (slot 0), the owner (slot 1), and the remaining cells.
(defthm fn-pth-mstates-okp-split
  (equal (fn-pth-mstates-okp ms)
         (and (implies (consp ms) (<= (fn-rtc-size (car ms)) (fn-pthm-max-state)))
              (implies (consp (cdr ms)) (<= (fn-rtc-size (cadr ms)) (fn-pthm-max-state)))
              (fn-pth-mstates-okp (cddr ms))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-pth-mstates-okp ms) (fn-pth-mstates-okp (cdr ms))
                            (fn-pth-mstates-okp (cddr ms)))
           :in-theory (union-theories (theory 'minimal-theory) '(car-cons cdr-cons)))))

(defthm fn-pth-owner-state-is-bounded
  (implies (fn-pth-invp s)
           (<= (fn-rtc-size (nth 1 (fn-rtc-mstates s))) (fn-pthm-max-state)))
  :hints (("Goal" :use ((:instance fn-pth-machine-states-are-bounded (j 1)))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-rtc-mstate fn-rtc-c-get-is-nth fn-pth-invp nfix natp)))))

(defthm fn-pth-connection-state-is-bounded
  (implies (and (fn-pth-invp s) (natp j) (not (equal j 1)))
           (<= (fn-rtc-size (nth j (fn-rtc-mstates s))) (fn-pthm-max-state)))
  :hints (("Goal" :use (fn-pth-machine-states-are-bounded)
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-rtc-mstate fn-rtc-c-get-is-nth fn-pth-invp nfix natp)))))
