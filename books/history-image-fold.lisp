; fn: readers of the history image by access pattern (lane composed-owner,
; 2026-09-29, row A5 of build/coordinator/COMPLETE-BEFORE-6.6.0.md).
; Prefix fn-hif-.
;
; A reader of the store's records reads them in one of a few patterns
; (GPT-6's review of 2026-09-28: count, indexed access, bounded cursor, fold,
; append/prefix, snapshot).  Over the image each pattern has ONE refinement
; here, proved once and instantiated per reader, rather than a twin of every
; caller:
;
;   indexed    `fn-hrc-get' / `fn-hrc-at' (books/history-records*.lisp;
;              fn-hib-get-keeps): record SEQ, or a named verdict
;   count      `fn-hrc-count' (fn-hrc-count-is-len): O(1)
;   fold       `fn-hif-run' below: rows [I, U) read with `fn-hrc-at' (no
;              fill, no I/O: a pure read of the concrete), the step applied
;              to each; it stops at the first row that is not verified and
;              answers the need-verdict with the CURSOR and the accumulator,
;              so the host serves the page OUTSIDE the owner and resumes
;   cursor     the same run over [I, min(U, I+K)): a bounded quantum, resumed
;              (`fn-hif-run-resume': the runs compose)
;
; KEYSTONE fn-hif-run-is-foldl: over a concrete that holds H, the run's
; accumulator is the left fold of the step over H's rows [I, J) where J is
; the cursor it answers; it answers :done exactly at J = U; any other
; verdict is a need-verdict for a row H has -- never a partial answer
; presented as whole, never absence.  The step is a constrained function;
; a reader instantiates the run with its own step (`fn-hif-def-fold').
(in-package "ACL2")
(include-book "history-image-binding")
(local (include-book "arithmetic/top" :dir :system))

(encapsulate
  (((fn-hif-f * *) => *))
  (local (defun fn-hif-f (acc ev) (declare (ignore ev)) acc)))

(defun fn-hif-foldl (acc evs)
  (if (atom evs) acc (fn-hif-foldl (fn-hif-f acc (car evs)) (cdr evs))))

(defun fn-hif-run (i u acc fn-hrecs$c)
  ; Rows I..U-1 folded with the step while each reads (:ok); (mv VERDICT
  ; CURSOR ACC): :done at CURSOR = U, else the read's verdict at the first
  ; row that did not read (a need-verdict: serve the page, resume at CURSOR
  ; with ACC), or the row's refusal ((:refused :seq) past the history).
  ; Reads only: no page is filled here, so it runs under the owner in time
  ; bounded by its rows, and the I/O it needs runs outside.
  (declare (xargs :stobjs fn-hrecs$c :guard (and (natp i) (natp u) (fn-hrc-wfp fn-hrecs$c))
                  :measure (nfix (- (nfix u) (nfix i))) :verify-guards nil
                  :hints (("Goal" :in-theory (disable fn-hrc-at)))))
  (if (mbe :logic (zp (- (nfix u) (nfix i))) :exec (<= u i))
      (mv :done (nfix i) acc)
    (mv-let (v r) (fn-hrc-at (nfix i) fn-hrecs$c)
      (cond ((not (eq v :ok)) (mv v (nfix i) acc))
            ((and (consp r) (eq (car r) :ok) (consp (cdr r)))
             (fn-hif-run (+ 1 (nfix i)) u (fn-hif-f acc (cadr r)) fn-hrecs$c))
            (t (mv r (nfix i) acc))))))


(defthm fn-hif-foldl-nil (equal (fn-hif-foldl acc nil) acc))
(defthm fn-hif-foldl-cons (equal (fn-hif-foldl acc (cons e x)) (fn-hif-foldl (fn-hif-f acc e) x)))

(defthm fn-hif-at-ok
  (implies (and (fn-hrs-rel h c) (fn-hrc-wfp c) (natp i) (< i (len h))
                (equal (mv-nth 0 (fn-hrc-at i c)) :ok))
           (equal (mv-nth 1 (fn-hrc-at i c)) (list :ok (nth i h))))
  :hints (("Goal" :use ((:instance fn-hrc-at-is-nth (fn-hrecs$c c) (seq i)))
           :in-theory (union-theories '((:e <)) (theory 'minimal-theory)))))
(defthm fn-hif-at-need
  (implies (and (fn-hrs-rel h c) (fn-hrc-wfp c) (natp i)
                (not (equal (mv-nth 0 (fn-hrc-at i c)) :ok)))
           (fn-hp-need-verdictp (mv-nth 0 (fn-hrc-at i c))))
  :hints (("Goal" :use ((:instance fn-hrc-at-is-nth (fn-hrecs$c c) (seq i)))
           :in-theory (theory 'minimal-theory))))

(defthm fn-hif-need-not-done
  (implies (fn-hp-need-verdictp v) (not (equal v :done)))
  :hints (("Goal" :in-theory (enable fn-hp-need-verdictp))))


(defun fn-hif-seg (i j h)
  ; H's rows I..J-1
  (declare (xargs :measure (nfix (- (nfix j) (nfix i)))))
  (if (zp (- (nfix j) (nfix i))) nil (cons (nth (nfix i) h) (fn-hif-seg (+ 1 (nfix i)) j h))))

(defthm fn-hif-run-cursor
  (let ((j (mv-nth 1 (fn-hif-run i u acc c))))
    (implies (and (natp i) (natp u) (<= i u))
             (and (natp j) (<= i j) (<= j u))))
  :hints (("Goal" :induct (fn-hif-run i u acc c) :in-theory (disable fn-hrc-at))))


(defthm fn-hif-run-step-ok
  (implies (and (natp i) (< i (nfix u)) (equal (mv-nth 0 (fn-hrc-at i c)) :ok)
                (equal (mv-nth 1 (fn-hrc-at i c)) (list :ok ev)))
           (equal (fn-hif-run i u acc c) (fn-hif-run (+ 1 i) u (fn-hif-f acc ev) c)))
  :hints (("Goal" :expand ((fn-hif-run i u acc c))
           :in-theory (union-theories '(nfix natp zp (:e zp) car-cons cdr-cons mv-nth (:e equal) eq)
                                      (theory 'minimal-theory)))))

(defthm fn-hif-run-step-need
  (implies (and (natp i) (< i (nfix u)) (not (equal (mv-nth 0 (fn-hrc-at i c)) :ok)))
           (equal (fn-hif-run i u acc c) (mv (mv-nth 0 (fn-hrc-at i c)) i acc)))
  :hints (("Goal" :expand ((fn-hif-run i u acc c))
           :in-theory (union-theories '(nfix natp zp (:e zp) car-cons cdr-cons (:e equal) eq)
                                      (theory 'minimal-theory)))))
(defthm fn-hif-run-base
  (implies (and (natp i) (not (< i (nfix u))))
           (equal (fn-hif-run i u acc c) (mv :done i acc)))
  :hints (("Goal" :expand ((fn-hif-run i u acc c))
           :in-theory (union-theories '(nfix natp zp (:e zp) car-cons cdr-cons (:e equal) eq)
                                      (theory 'minimal-theory)))))
(defthm fn-hif-seg-empty
  (implies (and (natp i) (not (< i (nfix j)))) (equal (fn-hif-seg i j h) nil)))
(defthm fn-hif-seg-step
  (implies (and (natp i) (< i (nfix j))) (equal (fn-hif-seg i j h) (cons (nth i h) (fn-hif-seg (+ 1 i) j h)))))


(local
 (defthm fn-hif-mv3
   (and (equal (mv-nth 0 (list a b c)) a) (equal (mv-nth 1 (list a b c)) b) (equal (mv-nth 2 (list a b c)) c))))

(defthm fn-hif-run-step-row
  (implies (and (fn-hrs-rel h c) (fn-hrc-wfp c) (natp i) (< i (nfix u)) (< i (len h))
                (equal (mv-nth 0 (fn-hrc-at i c)) :ok))
           (equal (fn-hif-run i u acc c) (fn-hif-run (+ 1 i) u (fn-hif-f acc (nth i h)) c)))
  :hints (("Goal" :use ((:instance fn-hif-at-ok) (:instance fn-hif-run-step-ok (ev (nth i h))))
           :in-theory (theory 'minimal-theory))))
; KEYSTONE (the fold over the image).
(defthm fn-hif-run-is-foldl
  (implies (and (fn-hrs-rel h c) (fn-hrc-wfp c) (natp i) (natp u) (<= i u) (<= u (len h)))
           (let* ((r (fn-hif-run i u acc c)) (v (mv-nth 0 r)) (j (mv-nth 1 r)) (a (mv-nth 2 r)))
             (and (natp j) (<= i j) (<= j u)
                  (equal a (fn-hif-foldl acc (fn-hif-seg i j h)))
                  (equal (equal v :done) (equal j u))
                  (implies (not (equal v :done)) (fn-hp-need-verdictp v)))))
  :hints (("Goal" :induct (fn-hif-run i u acc c)
           :in-theory (set-difference-theories (union-theories '((:induction fn-hif-run) fn-hif-run-step-row fn-hif-run-step-need fn-hif-run-base
                                        fn-hif-at-ok fn-hif-at-need fn-hif-need-not-done fn-hif-seg-empty fn-hif-seg-step
                                        fn-hif-foldl-nil fn-hif-foldl-cons nfix natp zp (:e zp) car-cons cdr-cons
                                        fn-hif-mv3 (:e equal) eq (:e fn-hp-need-verdictp) (:t len))
                                      (theory 'minimal-theory)) '(mv-nth)))))

(local
 (defthm fn-hif-foldl-append
   (equal (fn-hif-foldl acc (append x y)) (fn-hif-foldl (fn-hif-foldl acc x) y))))

(defthm fn-hif-seg-split
  (implies (and (natp i) (natp j) (natp k) (<= i j) (<= j k))
           (equal (fn-hif-seg i k h) (append (fn-hif-seg i j h) (fn-hif-seg j k h))))
  :hints (("Goal" :induct (fn-hif-seg i j h))))

; The runs compose: a run stopped at cursor J with accumulator A, resumed at
; J with A (after the page it needed was served, the concrete still holding
; H), folds exactly H's rows [I, K) -- the quantum-bounded cursor and the
; asynchronous resume are the same fold.
(defthm fn-hif-run-resume
  (implies (and (natp i) (natp j) (natp k) (<= i j) (<= j k)
                (equal a (fn-hif-foldl acc (fn-hif-seg i j h))))
           (equal (fn-hif-foldl a (fn-hif-seg j k h)) (fn-hif-foldl acc (fn-hif-seg i k h))))
  :hints (("Goal" :use ((:instance fn-hif-seg-split)) :in-theory (disable fn-hif-seg-split fn-hif-seg))))

; A reader's fold over the image: (fn-hif-def-fold NAME STEP FOLDL) defines
; NAME, the run with STEP (a guard-T function of the accumulator and a
; record) in place of the constrained step, FOLDL, STEP's left fold over a
; list, NAME-IS-FOLDL, the keystone for NAME by functional instance of
; `fn-hif-run-is-foldl', and verifies NAME's guards.  One refinement, proved
; once, instantiated per reader.
(defmacro fn-hif-def-fold (name step foldl)
  `(progn
     (defun ,foldl (acc evs)
       (declare (xargs :guard t))
       (if (atom evs) acc (,foldl (,step acc (car evs)) (cdr evs))))
     (defun ,name (i u acc fn-hrecs$c)
       (declare (xargs :stobjs fn-hrecs$c :guard (and (natp i) (natp u) (fn-hrc-wfp fn-hrecs$c))
                       :measure (nfix (- (nfix u) (nfix i)))
                       :hints (("Goal" :in-theory (disable fn-hrc-at)))
                       :verify-guards nil))
       (if (mbe :logic (zp (- (nfix u) (nfix i))) :exec (<= u i))
           (mv :done (nfix i) acc)
         (mv-let (v r) (fn-hrc-at (nfix i) fn-hrecs$c)
           (cond ((not (eq v :ok)) (mv v (nfix i) acc))
                 ((and (consp r) (eq (car r) :ok) (consp (cdr r)))
                  (,name (+ 1 (nfix i)) u (,step acc (cadr r)) fn-hrecs$c))
                 (t (mv r (nfix i) acc))))))
     (defthm ,(packn (list name '-is-foldl))
       (implies (and (fn-hrs-rel h c) (fn-hrc-wfp c) (natp i) (natp u) (<= i u) (<= u (len h)))
                (let* ((r (,name i u acc c)) (v (mv-nth 0 r)) (j (mv-nth 1 r)) (a (mv-nth 2 r)))
                  (and (natp j) (<= i j) (<= j u)
                       (equal a (,foldl acc (fn-hif-seg i j h)))
                       (equal (equal v :done) (equal j u))
                       (implies (not (equal v :done)) (fn-hp-need-verdictp v)))))
       :hints (("Goal" :use ((:functional-instance fn-hif-run-is-foldl
                                                   (fn-hif-f ,step) (fn-hif-run ,name) (fn-hif-foldl ,foldl)))
                :in-theory (union-theories '(,name ,foldl) (theory 'minimal-theory)))))
     (verify-guards ,name
       :hints (("Goal" :in-theory (union-theories '(nfix natp zp (:e zp) (:t nfix) eq) (theory 'minimal-theory)))))))

; Two instances: the count of the rows read, and the rows themselves
; (newest first) -- the witnesses tests/acl2/history-image-binding-tests.lisp
; runs over committed images.
(defun fn-hif-count-step (acc ev)
  (declare (xargs :guard t) (ignore ev))
  (+ 1 (nfix acc)))
(fn-hif-def-fold fn-hif-count-run fn-hif-count-step fn-hif-count-foldl)

(defun fn-hif-collect-step (acc ev)
  (declare (xargs :guard t))
  (cons ev acc))
(fn-hif-def-fold fn-hif-collect-run fn-hif-collect-step fn-hif-collect-foldl)
