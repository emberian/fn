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
(in-package "ACL2")

(defun fn-cur-split (xs n)
  (declare (xargs :guard (natp n)))
  (if (or (atom xs) (zp n))
      (mv nil xs)
    (mv-let (front rest) (fn-cur-split (cdr xs) (1- n))
      (mv (cons (car xs) front) rest))))

(defthm fn-cur-split-residual
  (equal (append (mv-nth 0 (fn-cur-split xs n))
                 (mv-nth 1 (fn-cur-split xs n)))
         xs))

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
  (list context progress pending dependency))

; :step is an existing consumer entry of shape (mv OCTETS PROGRESS'). The
; declared :call binds PROGRESS and the extra formals. One call visits at
; most one candidate; that obligation is the consumer's named :visit-proof.
; CONTEXT is immutable across output drain and suspension; a consumer may
; keep its snapshot/configuration/capture identity here. The shell never
; settles a dependency by observing a cache or a timeout.
(defmacro def-cursor (name formals &key call stobjs visit-proof)
  (let ((step (intern-in-package-of-symbol
               (concatenate 'string (symbol-name name) "-STEP") name))
        (byte-bound (intern-in-package-of-symbol
                     (concatenate 'string (symbol-name name) "-STEP-BYTE-BOUND") name))
        (call-bound (intern-in-package-of-symbol
                     (concatenate 'string (symbol-name name) "-STEP-CALL-BOUND") name)))
    (if (or (not (symbolp name)) (not (true-listp formals))
            (not (consp call)) (not (symbolp visit-proof)) (not visit-proof))
        '(assert-event nil :msg "def-cursor requires a call and named one-candidate visit proof")
      `(progn
         (make-event
          (if (getpropc ',visit-proof 'theorem nil (w state))
              '(value-triple :cursor-visit-proof-present)
            '(assert-event nil :msg "def-cursor visit-proof must name an admitted theorem")))
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
              ((zp visits) (mv nil cur 0 :yield))
              (t
               (mv-let (octets next) ,call
                 (mv-let (front rest) (fn-cur-split octets bytes)
                   (mv front (fn-cur-make context next rest nil) 1 :candidate)))))))
         (defthm ,byte-bound
           (<= (len (mv-nth 0 (,step cur visits bytes ,@formals))) (nfix bytes))
           :rule-classes :linear
           :hints (("Goal" :in-theory (e/d (,step) (fn-cur-split)))))
         (defthm ,call-bound
           (<= (mv-nth 2 (,step cur visits bytes ,@formals)) (nfix visits))
           :rule-classes :linear
           :hints (("Goal" :in-theory (e/d (,step) (fn-cur-split)))))
         (table fn-cursor ',name
                '(:step ,step :call ,call :visit-proof ,visit-proof
                  :context-preserved t :output-residual fn-cur-split-residual
                  :byte-bound fn-cur-split-byte-bound
                  :working-bound :consumer-owed :dependency-settlement :operation-owned))))))
