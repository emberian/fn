; Common buffered cursor shell. Consumer declarations provide one indivisible
; candidate step; the shell owns retained output, not a cache entry. Output
; drain never revisits a candidate. A suspended operation retains its opaque
; identity/custody until the owning operation supplies its validated receipt.
;
; This shell bounds VISITS and emitted BYTES separately. It does not claim a
; working-allocation bound for the consumer's one candidate: declarations must
; supply a resumable renderer or a proved profile-derived unit bound. In
; particular, wrapping an arbitrary OVER/HDR row does not bound its payload
; allocation or make a multi-entry cold read terminate.
;
; DEMAND (lane generators with cold-line, 2026-10-04).  The host runs a
; quantum under the realizer's no-I/O mode: a payload head the quantum needs
; and the realizer does not hold is a cold miss, the line is re-run once the
; miss is read off the owner, and the realizer keeps fn-arx-read-cache-entries
; of them.  A quantum whose steps read more heads than that evicts its own
; earlier entries on every re-run and never runs warm (owner.lisp, ONE
; deadline per LINE).  ACL2 cannot see whether a read is warm, so the bound
; that matters is READS PER QUANTUM, and a declaration states it as a metric
; over PROGRESS: `:demand-metric D' is the number of payload heads the
; consumer has touched by this progress (or an over-approximation of it; the
; shell reads D as (nfix D)), and `:demand-proof' names the admitted theorem
; that one call raises it by at most one, (<= (- (nfix D') (nfix D)) 1),
; checked against the world like :visit-proof.  The shell then proves
; NAME-STEP-DEMAND-BOUND (one step raises (nfix D) by at most one) and, in
; def-cursor/batch, NAME-BATCH-DEMAND-BOUND: a batch with budget Q raises it
; by at most (nfix Q), so a caller that passes Q < fn-arx-read-cache-entries
; gets a quantum whose misses fit the cache.  That the heads a step actually
; reads are counted by its D is the consumer's claim about its own reader,
; stated beside the instance; the shell proves only the sum.
(in-package "ACL2")
(include-book "immutable-list")

(defun fn-cur-split (xs n)
  (declare (xargs :guard (natp n) :verify-guards nil :measure (nfix n)
                  :hints (("Goal" :in-theory
                           (union-theories '(nfix natp zp o< o-p o-finp o-first-expt
                                                  o-first-coeff o-rst)
                                           (theory 'minimal-theory))))))
  (if (or (atom xs) (zp n))
      (mv nil xs)
    (mv-let (front rest) (fn-cur-split (cdr xs) (1- n))
      ;; A fully exhausted immutable input is already the desired front.
      ;; Reuse it instead of copying the whole output again. A nonempty
      ;; remainder still needs a separate prefix; no length scan is added.
      (mv (mbe :logic (cons (car xs) front)
               :exec (if rest (cons (car xs) front) xs)) rest))))

(defthm fn-cur-split-residual
  (equal (append (mv-nth 0 (fn-cur-split xs n))
                 (mv-nth 1 (fn-cur-split xs n)))
         xs))

(local
 (defthm fn-cur-split-exhausted-is-source
   (implies (not (mv-nth 1 (fn-cur-split xs n)))
            (equal (mv-nth 0 (fn-cur-split xs n)) xs))
   :hints (("Goal" :induct (fn-cur-split xs n)
            :in-theory (union-theories '(fn-cur-split mv-nth zp car-cons cdr-cons car-cdr-elim)
                                      (theory 'minimal-theory))))))

(verify-guards fn-cur-split
  :hints (("Goal" :use ((:instance fn-cur-split-exhausted-is-source
                                  (xs (cdr xs)) (n (1- n)))
                       (:instance car-cdr-elim (x xs)))
           :in-theory (theory 'minimal-theory))))

(defthm fn-cur-split-byte-bound
  (<= (len (car (fn-cur-split xs n))) (nfix n))
  :rule-classes :linear)

(defthm fn-cur-split-keeps-true-listp
  (implies (true-listp xs) (true-listp (mv-nth 1 (fn-cur-split xs n)))))

(defun fn-cur-at (n cur)
  (declare (xargs :guard (natp n)))
  (if (consp cur)
      (if (zp n) (car cur) (fn-cur-at (1- n) (cdr cur)))
    nil))

(defun fn-cur-context (cur) (declare (xargs :guard t)) (fn-cur-at 0 cur))
(defun fn-cur-progress (cur) (declare (xargs :guard t)) (fn-cur-at 1 cur))
(defun fn-cur-pending (cur) (declare (xargs :guard t)) (fn-cur-at 2 cur))
(defun fn-cur-dependency (cur) (declare (xargs :guard t)) (fn-cur-at 3 cur))
(defun fn-cur-make (context progress pending dependency)
  (declare (xargs :guard t))
  (mbe :logic (list context progress pending dependency)
       :exec (fn-list/immutable context progress pending dependency)))

; :step is an existing consumer entry of shape (mv OCTETS PROGRESS'). The
; declared :call binds PROGRESS and the extra formals. One call visits at
; most one candidate; that obligation is the consumer's named :visit-proof.
; CONTEXT is immutable across output drain and suspension; a consumer may
; keep its snapshot/configuration/capture identity here. The shell never
; settles a dependency by observing a cache or a timeout.
(defun fn-cur-visit-proof-event (name statement state)
  (declare (xargs :mode :program :stobjs state))
  (let ((formula (getpropc name 'theorem nil (w state))))
    (if (not formula)
        (er soft 'def-cursor "~x0 must name an admitted visit theorem." name)
      (er-let* ((translated (translate statement t t t 'def-cursor (w state) state)))
        (if (equal translated formula)
            (value '(value-triple :cursor-visit-proof-matches))
          (er soft 'def-cursor "~x0 does not prove this consumer's literal one-candidate metric: ~x1" name statement))))))

(defmacro def-cursor/output (name formals &key call stobjs visit-proof visit-metric output-phase output-proof
                                  demand-metric demand-proof)
  (let ((step (intern-in-package-of-symbol
               (concatenate 'string (symbol-name name) "-STEP") name))
        (byte-bound (intern-in-package-of-symbol
                     (concatenate 'string (symbol-name name) "-STEP-BYTE-BOUND") name))
        (call-bound (intern-in-package-of-symbol
                     (concatenate 'string (symbol-name name) "-STEP-CALL-BOUND") name))
        (demand-bound (intern-in-package-of-symbol
                       (concatenate 'string (symbol-name name) "-STEP-DEMAND-BOUND") name)))
    (if (or (not (symbolp name)) (not (true-listp formals))
            (not (consp call)) (not (symbolp visit-proof)) (not visit-proof)
            (not (consp visit-metric))
            (and output-phase (or (not (symbolp output-proof)) (not output-proof)))
            (and (or demand-metric demand-proof)
                 (or (not (consp demand-metric)) (not (symbolp demand-proof)) (not demand-proof))))
        '(assert-event nil :msg "def-cursor requires a call and named one-candidate visit proof (and, with :demand-metric, a named one-read demand proof)")
      `(progn
         (make-event
          (fn-cur-visit-proof-event
           ',visit-proof
           '(<= (- ,visit-metric
                   ,(subst `(mv-nth 1 ,call) 'progress visit-metric)) 1)
           state))
         ,@(if demand-metric
               `((make-event
                  (fn-cur-visit-proof-event
                   ',demand-proof
                   '(<= (- (nfix ,(subst `(mv-nth 1 ,call) 'progress demand-metric))
                           (nfix ,demand-metric))
                        1)
                   state)))
             nil)
         ,@(if output-phase
               `((make-event
                  (fn-cur-visit-proof-event
                   ',output-proof
                   '(implies ,output-phase
                             (equal (- ,visit-metric
                                       ,(subst `(mv-nth 1 ,call) 'progress visit-metric)) 0))
                   state)))
             nil)
         (defun ,step (cur visits bytes ,@formals)
           (declare (xargs :guard (and (natp visits) (natp bytes))
                           ,@(if stobjs `(:stobjs ,stobjs) nil)
                           :verify-guards nil))
           (let ((context (fn-cur-context cur))
                 (progress (fn-cur-progress cur))
                 (pending (fn-cur-pending cur))
                 (dependency (fn-cur-dependency cur)))
             (cond
              (dependency (mv nil cur 0 :suspended))
              ((zp bytes) (mv nil cur 0 :yield))
              ((consp pending)
               (mv-let (front rest) (fn-cur-split pending bytes)
                 (mv front (fn-cur-make context progress rest nil) 0 :output)))
              ((not progress) (mv nil cur 0 :done))
              ((and (zp visits) (not ,output-phase)) (mv nil cur 0 :yield))
              (t
               (mv-let (octets next) ,call
                 (mv-let (front rest) (fn-cur-split octets bytes)
                   (mv front (fn-cur-make context next rest nil)
                       (if ,output-phase 0 1)
                       (if ,output-phase :output :candidate))))))))
         (defthm ,byte-bound
           (<= (len (mv-nth 0 (,step cur visits bytes ,@formals))) (nfix bytes))
           :rule-classes :linear
           :hints (("Goal" :in-theory (e/d (,step) (fn-cur-split)))))
         (defthm ,call-bound
           (<= (mv-nth 2 (,step cur visits bytes ,@formals)) (nfix visits))
           :rule-classes :linear
           :hints (("Goal" :in-theory (e/d (,step) (fn-cur-split)))))
         ,@(if demand-metric
               `((defthm ,demand-bound
                   (<= (- (nfix ,(subst `(fn-cur-progress (mv-nth 1 (,step cur visits bytes ,@formals)))
                                        'progress demand-metric))
                          (nfix ,(subst '(fn-cur-progress cur) 'progress demand-metric)))
                       1)
                   :rule-classes :linear
                   :hints (("Goal" :in-theory (e/d (,step) (fn-cur-split))
                            :use ((:instance ,demand-proof (progress (fn-cur-progress cur))))))))
             nil)
         (table fn-cursor ',name
                '(:step ,step :call ,call :visit-proof ,visit-proof :visit-metric ,visit-metric
                  :output-phase ,output-phase :output-proof ,output-proof
                  :demand-metric ,demand-metric :demand-proof ,demand-proof
                  :demand-bound ,(and demand-metric demand-bound)
                  :context-preserved t :output-residual fn-cur-split-residual
                  :byte-bound fn-cur-split-byte-bound
                  :working-bound :consumer-owed :dependency-settlement :operation-owned))))))

(defmacro def-cursor (name formals &key call stobjs visit-proof visit-metric demand-metric demand-proof)
  `(def-cursor/output ,name ,formals :call ,call :stobjs ,stobjs
     :visit-proof ,visit-proof :visit-metric ,visit-metric
     :demand-metric ,demand-metric :demand-proof ,demand-proof))
