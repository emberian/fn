; Checked selection and constraint satisfaction are separate from logical-body
; equivalence. An attachment never turns a constrained symbol into a definition.
(in-package "ACL2")
(include-book "translation-validation")

(defun fn2-av-constraint (fn world)
 (declare (xargs :verify-guards nil))
 (let* ((prop (getpropc fn 'constraint-lst-etc nil world))
        (owner (if (and (consp prop) (symbolp (car prop)) (car prop)
                        (not (eq (car prop) t))) (car prop) fn))
        (resolved (if (eq owner fn) prop
                    (getpropc owner 'constraint-lst-etc nil world))))
  ; Only known encapsulate constraints are accepted. Unknown constraints,
  ; absent metadata and ordinary defining axioms are not silently empty.
  (and (consp resolved) (consp (car resolved))
       (pseudo-term-listp (car resolved))
       (true-listp (cdr resolved))
       (equal (len (car resolved)) (len (cdr resolved)))
       (list owner (car resolved) (cdr resolved)))))

(defun fn2-av-same-pairs-p (a b)
 (and (alistp a) (alistp b)
      (equal (len a) (len b))
      (no-duplicatesp-equal (strip-cars a))
      (no-duplicatesp-equal (strip-cars b))
      (subsetp-equal a b) (subsetp-equal b a)))

(defun fn2-av-attachment-group (fn world)
 (declare (xargs :verify-guards nil))
 (let ((prop (getpropc fn 'attachment nil world)))
  (if (and prop (symbolp prop)) (getpropc prop 'attachment nil world) prop)))

(defun fn2-av-groups-live-p (remaining pairs world)
 (declare (xargs :verify-guards nil))
 (if (atom remaining) (null remaining)
  (and (fn2-av-same-pairs-p pairs (fn2-av-attachment-group (caar remaining) world))
       (fn2-av-groups-live-p (cdr remaining) pairs world))))

(defun fn2-av-instance-records (owner pairs records)
 (declare (xargs :verify-guards nil))
 (if (atom records) nil
  (append
   (and (equal owner (access proved-functional-instances-alist-entry
                                  (car records) :constraint-event-name))
        (fn2-av-same-pairs-p pairs
         (access proved-functional-instances-alist-entry
                 (car records) :restricted-alist))
        (list (car records)))
   (fn2-av-instance-records owner pairs (cdr records)))))

(defun fn2-av-pairs-live-p (pairs constraint world)
 (declare (xargs :verify-guards nil))
 (if (atom pairs) (null pairs)
  (let* ((stub (caar pairs)) (impl (cdar pairs)))
   (and (symbolp stub) stub (symbolp impl) impl
        (function-symbolp stub world) (function-symbolp impl world)
        (equal (fn2-tv-attachment stub world) (car pairs))
        (equal (fn2-av-constraint stub world) constraint)
        (equal (len (formals stub world)) (len (formals impl world)))
        (not (equal (getpropc stub 'stobjs-in :missing world) :missing))
        (not (equal (getpropc stub 'stobjs-out :missing world) :missing))
        (not (equal (getpropc stub 'guard :missing world) :missing))
        (not (equal (getpropc impl 'guard :missing world) :missing))
        (equal (getpropc stub 'stobjs-in :missing world)
               (getpropc impl 'stobjs-in :missing world))
        (equal (getpropc stub 'stobjs-out :missing world)
               (getpropc impl 'stobjs-out :missing world))
        (eq (getpropc stub 'symbol-class :missing world) :common-lisp-compliant)
        (eq (getpropc impl 'symbol-class :missing world) :common-lisp-compliant)
        (not (equal (getpropc impl 'unnormalized-body :missing world) :missing))
        (fn2-av-pairs-live-p (cdr pairs) constraint world)))))

(defun fn2-av-member-records (pairs world)
 (declare (xargs :verify-guards nil))
 (if (atom pairs) nil
  (cons (list (fn2-tv-function (caar pairs) world)
              (fn2-tv-function (cdar pairs) world)
              (getpropc (caar pairs) 'symbol-class :missing world)
              (getpropc (cdar pairs) 'symbol-class :missing world))
        (fn2-av-member-records (cdr pairs) world))))

(defun fn2-av-packet (pairs world)
 (declare (xargs :verify-guards nil))
 (let* ((constraint (and (consp pairs) (fn2-av-constraint (caar pairs) world)))
        (instances (and constraint
          (fn2-av-instance-records (car constraint) pairs
           (global-val 'proved-functional-instances-alist world)))))
  (and (consp pairs) (alistp pairs) (no-duplicatesp-equal (strip-cars pairs))
       constraint instances (fn2-av-groups-live-p pairs pairs world)
       (fn2-av-pairs-live-p pairs constraint world)
       (list :schema 1
             :pairs (fn2-tv-object pairs)
             :members (fn2-tv-object (fn2-av-member-records pairs world))
             :constraint-owner (fn2-tv-object (car constraint))
             :constraints (fn2-tv-object (cadr constraint))
             :origins (fn2-tv-object (caddr constraint))
             :proved-instances (fn2-tv-object instances)))))

(defmacro fn2-av-check-packet (expected pairs)
 `(make-event
   (let ((actual (fn2-av-packet ,pairs (w state))))
    (if (and actual (equal ,expected actual))
        '(value-triple :selected-tuple-constraints-match-live-world)
      (er soft 'fn2-av-check-packet
       "Selected tuple, ABI, guard status or full admitted constraints differ.")))))

; Produce a demand predicate from the actual logical caller body. IF only
; demands its selected branch; lambda arguments retain their lexical scope.
; Unsupported executable/logical special forms refuse, never erase a path.
(mutual-recursion
 (defun fn2-av-demand (term pairs world)
  (declare (xargs :verify-guards nil :measure (acl2-count term)))
  (cond
   ((atom term) (mv nil ''t 0))
   ((eq (car term) 'quote) (mv nil ''t 0))
   ((member-eq (car term) '(return-last synp hide))
    (mv :unsupported-special nil 0))
   ((and (eq (car term) 'if) (equal (len term) 4))
    (mv-let (e0 d0 n0) (fn2-av-demand (cadr term) pairs world)
     (mv-let (e1 d1 n1) (fn2-av-demand (caddr term) pairs world)
      (mv-let (e2 d2 n2) (fn2-av-demand (cadddr term) pairs world)
       (mv (or e0 e1 e2) `(and ,d0 (if ,(cadr term) ,d1 ,d2)) (+ n0 n1 n2))))))
   ((consp (car term))
    (if (not (and (eq (caar term) 'lambda) (equal (len (car term)) 3)
                  (equal (len (cadar term)) (len (cdr term)))))
        (mv :unsupported-lambda nil 0)
     (mv-let (ea da na) (fn2-av-demand-list (cdr term) pairs world)
      (mv-let (eb db nb) (fn2-av-demand (caddar term) pairs world)
       (mv (or ea eb) `(and ,da ((lambda ,(cadar term) ,db) ,@(cdr term))) (+ na nb))))))
   (t
    (mv-let (err demand count) (fn2-av-demand-list (cdr term) pairs world)
     (let ((pair (assoc-eq (car term) pairs)))
      (if (not pair) (mv err demand count)
       (let ((sf (formals (car pair) world)) (gf (formals (cdr pair) world))
             (sg (getpropc (car pair) 'guard :missing world))
             (gg (getpropc (cdr pair) 'guard :missing world)))
        (if (or (not (equal (len sf) (len (cdr term))))
                (not (equal (len gf) (len (cdr term))))
                (equal sg :missing) (equal gg :missing))
            (mv :missing-call-domain nil 0)
          (mv err `(and ,demand ((lambda ,sf ,sg) ,@(cdr term))
                               ((lambda ,gf ,gg) ,@(cdr term))) (+ 1 count))))))))))
 (defun fn2-av-demand-list (terms pairs world)
  (declare (xargs :verify-guards nil :measure (acl2-count terms)))
  (if (atom terms) (mv nil ''t 0)
   (mv-let (e0 d0 n0) (fn2-av-demand (car terms) pairs world)
    (mv-let (e1 d1 n1) (fn2-av-demand-list (cdr terms) pairs world)
     (mv (or e0 e1) `(and ,d0 ,d1) (+ n0 n1)))))))

(defun fn2-av-caller-event (caller pairs theorem world)
 (declare (xargs :verify-guards nil))
 (let ((body (getpropc caller 'unnormalized-body :missing world))
       (guard (getpropc caller 'guard :missing world)))
  (mv-let (err demand count) (fn2-av-demand body pairs world)
   (if (or err (zp count) (equal body :missing) (equal guard :missing)
           (not (eq (getpropc caller 'symbol-class :missing world) :common-lisp-compliant)))
       `(make-event (er soft 'fn2-av-caller-event "Unresolved actual caller domain ~x0: ~x1." ',caller ',err))
    `(defthm ,theorem (implies ,guard ,demand) :rule-classes nil)))))

; Ordinary output, outside certifying events. The consumer rechecks every
; exported field in its qualified live world before using the kernel record.
(defun fn2-av-export (path pairs state)
 (declare (xargs :stobjs state :verify-guards nil))
 (let ((packet (fn2-av-packet pairs (w state))))
  (if (not packet)
      (prog2$ (er hard 'fn2-av-export "No complete checked attachment tuple.") state)
   (mv-let (channel state) (open-output-channel path :character state)
    (if (not channel)
        (prog2$ (er hard 'fn2-av-export "Cannot write ~x0." path) state)
      (let ((state (prin1$ packet channel state)))
       (close-output-channel channel state)))))))
