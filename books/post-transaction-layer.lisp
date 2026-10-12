; The POST transaction machine as a runtime-contract layer instance (Builder P, landing 1).
;
; fn-rtc-def-layer instantiates the contract (v2.2) with the machine fn-ptx-step over the pool
; stobj: every slot's machine is fn-ptx, a static slot starts :closed (fn-ptx-closed) and opens on
; the :opened completion fn-rtc-init arms for it, and a connection slot holds a :closed machine
; that refuses every post.  The instance's keystones (fn-ptl-<keystone>, T1-T15) and its exec
; equality fn-ptl-mx-step-is-m-step (the stobj step is the logic step over the slot's view) come
; from the generator, and the store-opened facts KO1-KO3 of contract v2.2 (not in the generator's
; list) by the same functional instance below.  The machine's obligations are the machine book's
; fn-ptx-step-facts, fn-ptx-step-reads-view and fn-ptx-commits-only-on-fsync-done.
(in-package "ACL2")
(include-book "post-transaction")
(include-book "runtime-contract-opened")
; The obligations are discharged from the machine's lemmas by :use, in the machine's theory as of
; its P5 statement (its later proof lemmas loop the rewriter on the generator's goals).
(local (in-theory (current-theory 'fn-ptx-p5)))
; The machine's guards are verified with guard T (landing 2), so the generator verifies the instance's
; exec copies' guards too: fn-ptl-x-step is common-lisp-compliant, guarded by fn-rtc-st-p alone.

(defun fn-ptx-static-init (j) (declare (xargs :guard t) (ignore j)) (fn-ptx-closed))

; The layer's invariant runs (fn-ptl-mstates-okp, fn-ptl-invp) and reads these bounds.

(defthm fn-ptx-closed-facts
  (and (equal (fn-rtc-size (fn-ptx-closed)) 29)
       (not (fn-ptx-committedp (fn-ptx-closed))))
  :rule-classes nil)

(fn-rtc-def-layer fn-ptl
  :step fn-ptx-step :init fn-ptx-closed :static-init fn-ptx-static-init
  :committedp fn-ptx-committedp :c fn-ptx-c :max-reqs fn-ptx-max-reqs :max-state fn-ptx-max-state
  :reads-view fn-ptx-step-reads-view
  :hints (("Goal" :in-theory (e/d (fn-ptl-m-step fn-ptx-static-init)
                                  (fn-ptx-step fn-ptx-closed fn-ptx-committedp fn-ptx-c fn-ptx-max-reqs))
           :use ((:instance fn-ptx-step-facts (st pool) (q (nfix q)))
                 (:instance fn-ptx-step-nfix-q (st pool))
                 (:instance fn-ptx-commits-only-on-fsync-done (st pool))
                 fn-ptx-closed-facts))))

; The store-opened facts of contract v2.2 for this instance (KO1 fn-rtc-init-arms-the-opened, KO1a
; fn-rtc-init-emits-the-opened, KO1b fn-rtc-opened-use-is-static, KO2 fn-rtc-opened-acts-at-most-once,
; KO2r fn-rtc-machine-cannot-request-the-opened, KO1c fn-rtc-opened-acts-once-per-incarnation, KO3
; fn-rtc-opened-steps-its-slot), by the generator's functional instance: the machine's :opened
; arrives once, at its static slot, and steps exactly that slot's machine.
;; KO1c quantifies over runs (fn-rtc-run), which the generator does not copy: the instance's run.
(defun fn-ptl-run (s events q)
  (if (consp events)
      (mv-let (s2 acts) (fn-ptl-step s (car events) q)
        (declare (ignore acts))
        (fn-ptl-run s2 (cdr events) q))
    s))

(make-event
 (let* ((prefix 'fn-ptl)
        (copied (fn-rtc-layer-alist prefix (append *fn-rtc-layer-spec-fns* *fn-rtc-layer-exec-fns*)))
        (alist (append '((fn-rtc-m-init . fn-ptx-closed) (fn-rtc-m-static-init . fn-ptx-static-init)
                         (fn-rtc-m-step . fn-ptl-m-step) (fn-rtc-m-committedp . fn-ptx-committedp)
                         (fn-rtc-m-c . fn-ptx-c) (fn-rtc-m-max-reqs . fn-ptx-max-reqs)
                         (fn-rtc-m-max-state . fn-ptx-max-state) (fn-rtc-mx-step . fn-ptx-step)
                         (fn-rtc-run . fn-ptl-run))
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
          prefix alist (fn-rtc-layer-fi-alist alist) (cons 'fn-ptl-run (strip-cdrs copied)) obligations (w state)))))

; KO1c: the generator's one-step theory unrolls the run in the goal itself, so the instance is
; taken in the minimal theory and the copies' definitions (with the run's) prove its constraints.
(defthm fn-ptl-run-def
  (equal (fn-ptl-run s events q)
         (if (consp events)
             (fn-ptl-run (mv-nth 0 (fn-ptl-step s (car events) q)) (cdr events) q)
           s))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(fn-ptl-run) (theory 'minimal-theory)))))
(make-event
 (let* ((prefix 'fn-ptl)
        (copied (fn-rtc-layer-alist prefix (append *fn-rtc-layer-spec-fns* *fn-rtc-layer-exec-fns*)))
        (alist (append '((fn-rtc-m-init . fn-ptx-closed) (fn-rtc-m-static-init . fn-ptx-static-init)
                         (fn-rtc-m-step . fn-ptl-m-step) (fn-rtc-m-committedp . fn-ptx-committedp)
                         (fn-rtc-m-c . fn-ptx-c) (fn-rtc-m-max-reqs . fn-ptx-max-reqs)
                         (fn-rtc-m-max-state . fn-ptx-max-state) (fn-rtc-mx-step . fn-ptx-step)
                         (fn-rtc-run . fn-ptl-run))
                       copied))
        (obligations (cons 'natp (fn-rtc-layer-names prefix
                                   '(fn-rtc-m-constants fn-rtc-mx-step-is-m-step fn-rtc-m-step-is-charged
                                     fn-rtc-m-step-requests-are-bounded fn-rtc-m-init-is-bounded
                                     fn-rtc-m-step-state-is-bounded fn-rtc-m-init-is-uncommitted
                                     fn-rtc-m-static-init-is-bounded fn-rtc-m-static-init-is-uncommitted
                                     fn-rtc-m-commits-only-on-fsync-done)))))
   `(defthm fn-ptl-opened-acts-once-per-incarnation
      ,(fn-rtc-layer-rename (getpropc 'fn-rtc-opened-acts-once-per-incarnation 'untranslated-theorem nil (w state)) alist)
      :hints (("Goal" :use ((:functional-instance fn-rtc-opened-acts-once-per-incarnation ,@(fn-rtc-layer-fi-alist alist)))
               :in-theory (theory 'minimal-theory))
              (and stable-under-simplificationp
                   '(:in-theory (union-theories (theory 'minimal-theory) ',(append (strip-cdrs copied) obligations))
                     :use (fn-ptl-run-def)))))))
