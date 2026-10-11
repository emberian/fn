; fn: `fn-rtc-def-layer', the runtime contract instanced for a concrete
; machine.
(in-package "ACL2")
(include-book "runtime-contract-landing")
(include-book "runtime-contract-budget")

(defthm fn-rtc-view-pool-idempotent
  (equal (fn-rtc-view-pool id inc cfg h (fn-rtc-view-pool id inc cfg h pool))
         (fn-rtc-view-pool id inc cfg h pool))
  :hints (("Goal" :induct (fn-rtc-view-pool id inc cfg h pool)
           :expand ((:free (a b) (fn-rtc-view-pool id inc cfg h (cons a b))))
           :in-theory (union-theories (theory 'minimal-theory) '(car-cons cdr-cons fn-rtc-view-pool fn-rtc-view-own-p fn-rtc-view-mine-p fn-rtc-b-owner fn-rtc-b-gen fn-rtc-get member-equal nfix natp zp (:type-prescription nfix))))))

(defthm fn-rtc-v-readers-of-view-state
  (and (equal (fn-rtc-st-config (fn-rtc-view-state id inc st)) (fn-rtc-st-config st))
       (equal (fn-rtc-st-v-owner h id inc (fn-rtc-view-state id inc st)) (fn-rtc-st-v-owner h id inc st))
       (equal (fn-rtc-st-v-gen h id inc (fn-rtc-view-state id inc st)) (fn-rtc-st-v-gen h id inc st))
       (equal (fn-rtc-st-v-fill h id inc (fn-rtc-view-state id inc st)) (fn-rtc-st-v-fill h id inc st))
       (equal (fn-rtc-st-v-byte h i id inc (fn-rtc-view-state id inc st)) (fn-rtc-st-v-byte h i id inc st))
       (equal (fn-rtc-st-v-pool id inc (fn-rtc-view-state id inc st)) (fn-rtc-st-v-pool id inc st)))
  :hints (("Goal" :in-theory (enable fn-rtc-view-state fn-rtc-view fn-rtc-vb
                                     fn-rtc-st-config fn-rtc-st-v-owner fn-rtc-st-v-gen fn-rtc-st-v-fill
                                     fn-rtc-st-v-byte fn-rtc-st-v-pool))))

(defthm fn-rtc-view-state-of-view-state
  (equal (fn-rtc-view-state id inc (fn-rtc-view-state id inc st)) (fn-rtc-view-state id inc st)))

(in-theory (disable fn-rtc-view-state))

(defconst *fn-rtc-layer-spec-fns*
  '(fn-rtc-mstates-okp fn-rtc-invp fn-rtc-deliver fn-rtc-accept-branch fn-rtc-close-branch
    fn-rtc-step* fn-rtc-step fn-rtc-step-cost fn-rtc-step-actions-bound fn-rtc-step-c fn-rtc-static-mstates fn-rtc-init))

(defconst *fn-rtc-layer-exec-fns*
  '(fn-rtc-x-free-pool-buf-loop fn-rtc-x-free-pool-buf fn-rtc-x-arm-grant fn-rtc-x-rearm
    fn-rtc-x-grant-one fn-rtc-x-grant fn-rtc-x-deliver fn-rtc-x-accept-branch fn-rtc-x-close-branch
    fn-rtc-x-step* fn-rtc-x-step fn-rtc-x-statics fn-rtc-x-init))

(defun fn-rtc-layer-name (prefix f)
  (declare (xargs :mode :program))
  (intern-in-package-of-symbol
   (concatenate 'string (symbol-name prefix) "-"
                (subseq (symbol-name f) 7 (length (symbol-name f))))
   prefix))

(defun fn-rtc-layer-alist (prefix fns)
  (declare (xargs :mode :program))
  (if (endp fns) nil
    (cons (cons (car fns) (fn-rtc-layer-name prefix (car fns)))
          (fn-rtc-layer-alist prefix (cdr fns)))))

(defun fn-rtc-layer-rename (x alist)
  (declare (xargs :mode :program))
  (cond ((symbolp x) (let ((p (assoc-eq x alist))) (if p (cdr p) x)))
        ((atom x) x)
        ((eq (car x) 'quote) x)
        (t (cons (fn-rtc-layer-rename (car x) alist) (fn-rtc-layer-rename (cdr x) alist)))))

(defun fn-rtc-layer-measure (decls)
  (declare (xargs :mode :program))
  (cond ((endp decls) nil)
        (t (let* ((d (car decls))
                  (xargs (and (consp d) (eq (car d) 'declare) (assoc-eq 'xargs (cdr d))))
                  (m (and xargs (member-eq :measure (cdr xargs)))))
             (if m (list :measure (cadr m)) (fn-rtc-layer-measure (cdr decls)))))))

; A spec copy: logic only (it serves the functional instances, never runs).
(defun fn-rtc-layer-spec-copy (f alist wrld)
  (declare (xargs :mode :program))
  (let* ((ev (get-event f wrld)) (formals (caddr ev)) (rest (cdddr ev))
         (decls (butlast rest 1)) (body (car (last rest))))
    `(defun ,(cdr (assoc-eq f alist)) ,formals
       (declare (xargs :guard t :verify-guards nil :normalize nil ,@(fn-rtc-layer-measure decls)))
       ,(fn-rtc-layer-rename body alist))))

; An executable copy: the same declarations, so the same stobj discipline and
; guards.
(defun fn-rtc-layer-exec-copy (f alist wrld)
  (declare (xargs :mode :program))
  (let* ((ev (get-event f wrld)) (formals (caddr ev)) (rest (cdddr ev))
         (decls (butlast rest 1)) (body (car (last rest))))
    `(defun ,(cdr (assoc-eq f alist)) ,formals
       ,@(fn-rtc-layer-rename decls alist)
       (declare (xargs :normalize nil))
       ,(fn-rtc-layer-rename body alist))))

; Type facts the copies' guard proofs read, per executable copy: the call
; shape, then the output positions that are true lists and the one that is
; a natural.
(defconst *fn-rtc-layer-exec-types*
  '((fn-rtc-x-free-pool-buf-loop (fn-rtc-x-free-pool-buf-loop h n fn-rtc-st) nil :maybe-nat)
    (fn-rtc-x-free-pool-buf (fn-rtc-x-free-pool-buf fn-rtc-st) nil :maybe-nat)
    (fn-rtc-x-arm-grant (fn-rtc-x-arm-grant fn-rtc-st) (1) nil)
    (fn-rtc-x-rearm (fn-rtc-x-rearm fn-rtc-st) (1) nil)
    (fn-rtc-x-grant-one (fn-rtc-x-grant-one fn-rtc-st) (1) nil)
    (fn-rtc-x-grant (fn-rtc-x-grant n fn-rtc-st) (1) nil)
    (fn-rtc-x-init (fn-rtc-x-init cfg fn-rtc-st) (1) nil)
    (fn-rtc-x-deliver (fn-rtc-x-deliver id inc ev q fn-rtc-st) (1) 3)
    (fn-rtc-x-accept-branch (fn-rtc-x-accept-branch out q fn-rtc-st) (1) 3)
    (fn-rtc-x-close-branch (fn-rtc-x-close-branch id inc fn-rtc-st) (1) nil)))

(defun fn-rtc-layer-type-lemma (f alist)
  (declare (xargs :mode :program))
  (let ((row (assoc-eq f *fn-rtc-layer-exec-types*)))
    (and row
         (let* ((call (fn-rtc-layer-rename (cadr row) alist))
                (lists (caddr row)) (nat (cadddr row))
                (name (intern-in-package-of-symbol
                       (concatenate 'string (symbol-name (car call)) "-TYPES") (car call))))
           `((defthm ,name
               (and ,@(loop$ for i in lists collect `(true-listp (mv-nth ,i ,call)))
                    ,@(if (eq nat :maybe-nat) `((or (null ,call) (natp ,call)))
                        (and nat `((natp (mv-nth ,nat ,call))))))
               :hints (("Goal" :expand (,call)
                        ,@(and (member-eq f '(fn-rtc-x-free-pool-buf-loop fn-rtc-x-grant))
                               `(:induct ,call))
                        :in-theory ,(fn-rtc-layer-rename
                                     (append '(disable fn-rtc-mx-step fn-rtc-x-requests)
                                             (and (member-eq f '(fn-rtc-x-rearm fn-rtc-x-grant-one fn-rtc-x-grant
                                                                 fn-rtc-x-deliver fn-rtc-x-accept-branch fn-rtc-x-close-branch
                                                                 fn-rtc-x-init))
                                                  '(fn-rtc-x-rearm))
                                             (and (member-eq f '(fn-rtc-x-deliver fn-rtc-x-accept-branch
                                                                 fn-rtc-x-close-branch fn-rtc-x-init))
                                                  '(fn-rtc-x-deliver)))
                                     alist)))))))))

(defun fn-rtc-layer-copies (fns kind alist wrld)
  (declare (xargs :mode :program))
  (if (endp fns) nil
    (append (list (if (eq kind :spec)
                      (fn-rtc-layer-spec-copy (car fns) alist wrld)
                    (fn-rtc-layer-exec-copy (car fns) alist wrld)))
            (and (eq kind :exec) (fn-rtc-layer-type-lemma (car fns) alist))
            (list `(in-theory (disable ,(cdr (assoc-eq (car fns) alist)))))
            (fn-rtc-layer-copies (cdr fns) kind alist wrld))))

; -----------------------------------------------------------------------------
; The layer state read back as the contract's list through the exports
; (`fn-rtc-x-state'), equal to the stobj's logical value: an executable
; observation of exactly the state the keystones are about.

(defun fn-rtc-x-bytes (h i n fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :guard (and (natp i) (natp n))
                  :measure (nfix (- (nfix n) (nfix i)))))
  (let ((i (nfix i)))
    (if (< i (nfix n))
        (cons (fn-rtc-st-byte h i fn-rtc-st) (fn-rtc-x-bytes h (+ 1 i) n fn-rtc-st))
      nil)))

(defun fn-rtc-x-buffers (h n fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :guard (and (natp h) (natp n))
                  :measure (nfix (- (nfix n) (nfix h)))))
  (let ((h (nfix h)))
    (if (< h (nfix n))
        (cons (list (fn-rtc-st-gen h fn-rtc-st) (fn-rtc-st-owner h fn-rtc-st)
                    (fn-rtc-x-bytes h 0 (fn-rtc-st-fill h fn-rtc-st) fn-rtc-st))
              (fn-rtc-x-buffers (+ 1 h) n fn-rtc-st))
      nil)))

(defun fn-rtc-x-slots (i n fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :guard (and (natp i) (natp n))
                  :measure (nfix (- (nfix n) (nfix i)))))
  (let ((i (nfix i)))
    (if (< i (nfix n))
        (cons (fn-rtc-st-slot i fn-rtc-st) (fn-rtc-x-slots (+ 1 i) n fn-rtc-st))
      nil)))

(defun fn-rtc-x-mstates (i n fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st :guard (and (natp i) (natp n))
                  :measure (nfix (- (nfix n) (nfix i)))))
  (let ((i (nfix i)))
    (if (< i (nfix n))
        (cons (fn-rtc-st-mstate i fn-rtc-st) (fn-rtc-x-mstates (+ 1 i) n fn-rtc-st))
      nil)))

(defun fn-rtc-x-state (fn-rtc-st)
  (declare (xargs :stobjs fn-rtc-st))
  (let ((cfg (fn-rtc-st-config fn-rtc-st)))
    (list cfg
          (fn-rtc-x-slots 0 (fn-rtc-nslots cfg) fn-rtc-st)
          (fn-rtc-x-buffers 0 (fn-rtc-nbufs cfg) fn-rtc-st)
          (fn-rtc-st-uses fn-rtc-st)
          (fn-rtc-x-mstates 0 (fn-rtc-nslots cfg) fn-rtc-st)
          (fn-rtc-st-next-op fn-rtc-st))))

(local (defthm fn-rtc-xs-get-is-nth
  (equal (fn-rtc-get i l) (nth (nfix i) l))
  :hints (("Goal" :in-theory (enable nth)))))

(local (defun fn-rtc-xs-ind (i n)
  (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
  (let ((i (nfix i))) (if (< i (nfix n)) (fn-rtc-xs-ind (+ 1 i) n) (list i n)))))

(local (defthm fn-rtc-xs-nthcdr-cons
  (implies (and (natp i) (< i (len l)))
           (equal (nthcdr i l) (cons (nth i l) (nthcdr (+ 1 i) l))))
  :hints (("Goal" :in-theory (enable nth nthcdr)))))

(local (defthm fn-rtc-xs-take-nthcdr
  (implies (and (natp i) (natp n) (<= i n) (<= n (len l)))
           (equal (take (- n i) (nthcdr i l))
                  (if (< i n) (cons (nth i l) (take (- n (+ 1 i)) (nthcdr (+ 1 i) l))) nil)))
  :hints (("Goal" :in-theory (disable fn-rtc-xs-nthcdr-cons) :use fn-rtc-xs-nthcdr-cons))))

(local (defthm fn-rtc-x-slots-is
  (implies (and (natp i) (natp n) (<= i n) (<= n (len (fn-rtc-slots st))))
           (equal (fn-rtc-x-slots i n st) (take (- n i) (nthcdr i (fn-rtc-slots st)))))
  :hints (("Goal" :induct (fn-rtc-xs-ind i n)
           :in-theory (enable fn-rtc-st-slot fn-rtc-slot)))))

(local (defthm fn-rtc-x-mstates-is
  (implies (and (natp i) (natp n) (<= i n) (<= n (len (fn-rtc-mstates st))))
           (equal (fn-rtc-x-mstates i n st) (take (- n i) (nthcdr i (fn-rtc-mstates st)))))
  :hints (("Goal" :induct (fn-rtc-xs-ind i n)
           :in-theory (enable fn-rtc-st-mstate fn-rtc-mstate)))))

(local (defthm fn-rtc-x-bytes-is
  (implies (and (natp i) (natp n) (<= i n) (<= n (len (fn-rtc-bytes h st)))
                (true-listp (fn-rtc-bytes h st)))
           (equal (fn-rtc-x-bytes h i n st) (take (- n i) (nthcdr i (fn-rtc-bytes h st)))))
  :hints (("Goal" :induct (fn-rtc-xs-ind i n)
           :in-theory (e/d (fn-rtc-st-byte) (fn-rtc-bytes))))))

(local (defthm fn-rtc-xs-take-len
  (implies (true-listp l) (equal (take (len l) l) l))))

(local (defun fn-rtc-xs-sub (i n l)
  (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
  (let ((i (nfix i))) (if (< i (nfix n)) (cons (nth i l) (fn-rtc-xs-sub (+ 1 i) n l)) nil))))

(local (defthm fn-rtc-xs-sub-is-take-nthcdr
  (implies (and (natp i) (natp n) (<= i n) (<= n (len l)))
           (equal (fn-rtc-xs-sub i n l) (take (- n i) (nthcdr i l))))
  :hints (("Goal" :induct (fn-rtc-xs-sub i n l)))))

(local (defthm fn-rtc-xs-three-list
  (implies (and (true-listp b) (equal (len b) 3))
           (equal (list (nth 0 b) (nth 1 b) (nth 2 b)) b))
  :hints (("Goal" :in-theory (enable nth len)
           :expand ((len b) (len (cdr b)) (len (cddr b)) (len (cdddr b)))))))

(local (defthm fn-rtc-xs-octets-empty
  (implies (and (fn-cbor-octet-listp x) (equal (len x) 0)) (equal x nil))
  :rule-classes :forward-chaining))

(local (defthm fn-rtc-xs-buffer-rebuilt-1
  (implies (and (fn-rtc-shapep st) (natp h) (< h (fn-rtc-nbufs (fn-rtc-config st))))
           (equal (list (fn-rtc-st-gen h st) (fn-rtc-st-owner h st)
                        (fn-rtc-x-bytes h 0 (fn-rtc-st-fill h st) st))
                  (fn-rtc-buffer h st)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
             '(fn-rtc-st-gen fn-rtc-st$a-gen fn-rtc-gen fn-rtc-b-gen
               fn-rtc-st-owner fn-rtc-st$a-owner fn-rtc-b-owner
               fn-rtc-st-fill fn-rtc-st$a-fill fn-rtc-bytes fn-rtc-b-bytes
               fn-rtc-xs-take-len fn-cbor-octet-listp-implies-true-listp
               nfix natp nthcdr zp unicity-of-0 commutativity-of-+ fix (:type-prescription len)))
           :use ((:instance fn-rtc-c-shapep-buffer (s st))
                 (:instance fn-rtc-x-bytes-is (i 0) (n (len (fn-rtc-bytes h st))))
                 (:instance fn-rtc-xs-three-list (b (fn-rtc-buffer h st)))
                 (:instance fn-rtc-xs-get-is-nth (i 0) (l (fn-rtc-buffer h st)))
                 (:instance fn-rtc-xs-get-is-nth (i 1) (l (fn-rtc-buffer h st)))
                 (:instance fn-rtc-xs-get-is-nth (i 2) (l (fn-rtc-buffer h st))))))))

(local (defthm fn-rtc-xs-buffer-rebuilt
  (implies (and (fn-rtc-shapep st) (natp h) (< h (fn-rtc-nbufs (fn-rtc-config st))))
           (equal (list (fn-rtc-st-gen h st) (fn-rtc-st-owner h st)
                        (fn-rtc-x-bytes h 0 (fn-rtc-st-fill h st) st))
                  (nth h (fn-rtc-pool st))))
  :hints (("Goal" :use (fn-rtc-xs-buffer-rebuilt-1
                        (:instance fn-rtc-xs-get-is-nth (i h) (l (fn-rtc-pool st))))
           :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-buffer nfix natp))))))

(local (defthm fn-rtc-x-buffers-is-sub
  (implies (and (fn-rtc-shapep st) (natp h) (natp n) (<= n (fn-rtc-nbufs (fn-rtc-config st))))
           (equal (fn-rtc-x-buffers h n st) (fn-rtc-xs-sub h n (fn-rtc-pool st))))
  :hints (("Goal" :induct (fn-rtc-xs-sub h n (fn-rtc-pool st))
           :in-theory (disable fn-rtc-shapep fn-rtc-x-bytes fn-rtc-st-gen fn-rtc-st-owner fn-rtc-st-fill
                               fn-rtc-nbufs fn-rtc-xs-buffer-rebuilt))
          ("Subgoal *1/1" :use ((:instance fn-rtc-xs-buffer-rebuilt (h (nfix h))))))))

(local (defthm fn-rtc-xs-shapep-len-pool
  (implies (fn-rtc-shapep st) (equal (len (fn-rtc-pool st)) (fn-rtc-nbufs (fn-rtc-config st))))
  :hints (("Goal" :in-theory (enable fn-rtc-shapep)))))

(local (defthm fn-rtc-x-buffers-is
  (implies (and (fn-rtc-shapep st) (natp h) (natp n) (<= h n) (<= n (fn-rtc-nbufs (fn-rtc-config st))))
           (equal (fn-rtc-x-buffers h n st) (take (- n h) (nthcdr h (fn-rtc-pool st)))))
  :hints (("Goal" :in-theory (disable fn-rtc-shapep fn-rtc-x-buffers)))))

(local (defthm fn-rtc-xs-six-list
  (implies (fn-rtc-shapep st)
           (equal (list (fn-rtc-config st) (fn-rtc-slots st) (fn-rtc-pool st) (fn-rtc-uses st)
                        (fn-rtc-mstates st) (fn-rtc-next-op st))
                  st))
  :hints (("Goal" :in-theory (enable fn-rtc-shapep fn-rtc-config fn-rtc-slots fn-rtc-pool fn-rtc-uses
                                     fn-rtc-mstates fn-rtc-next-op nth len)
           :expand ((len st) (len (cdr st)) (len (cddr st)) (len (cdddr st)) (len (cddddr st))
                    (len (cdr (cddddr st))) (len (cddr (cddddr st))))))))

(local (defthm fn-rtc-xs-shape-facts
  (implies (fn-rtc-shapep st)
           (and (true-listp (fn-rtc-slots st)) (equal (len (fn-rtc-slots st)) (fn-rtc-nslots (fn-rtc-config st)))
                (true-listp (fn-rtc-mstates st)) (equal (len (fn-rtc-mstates st)) (fn-rtc-nslots (fn-rtc-config st)))
                (true-listp (fn-rtc-pool st)) (equal (len (fn-rtc-pool st)) (fn-rtc-nbufs (fn-rtc-config st)))))
  :hints (("Goal" :in-theory (enable fn-rtc-shapep)
           :use ((:instance fn-rtc-pool-shapep-true-listp (pool (fn-rtc-pool st)) (h 0) (cfg (fn-rtc-config st))))))
  :rule-classes nil))

(local (defthm fn-rtc-xs-take-nthcdr-0-len
  (implies (and (true-listp l) (equal n (len l))) (equal (take n (nthcdr 0 l)) l))))

(local (defthm fn-rtc-xs-whole-lists
  (implies (fn-rtc-shapep st)
           (and (equal (fn-rtc-x-slots 0 (fn-rtc-nslots (fn-rtc-config st)) st) (fn-rtc-slots st))
                (equal (fn-rtc-x-mstates 0 (fn-rtc-nslots (fn-rtc-config st)) st) (fn-rtc-mstates st))
                (equal (fn-rtc-x-buffers 0 (fn-rtc-nbufs (fn-rtc-config st)) st) (fn-rtc-pool st))))
  :hints (("Goal" :use (fn-rtc-xs-shape-facts
                        (:instance fn-rtc-x-slots-is (i 0) (n (fn-rtc-nslots (fn-rtc-config st))))
                        (:instance fn-rtc-x-mstates-is (i 0) (n (fn-rtc-nslots (fn-rtc-config st))))
                        (:instance fn-rtc-x-buffers-is (h 0) (n (fn-rtc-nbufs (fn-rtc-config st))))
                        (:instance fn-rtc-xs-take-nthcdr-0-len (l (fn-rtc-slots st)) (n (fn-rtc-nslots (fn-rtc-config st))))
                        (:instance fn-rtc-xs-take-nthcdr-0-len (l (fn-rtc-mstates st)) (n (fn-rtc-nslots (fn-rtc-config st))))
                        (:instance fn-rtc-xs-take-nthcdr-0-len (l (fn-rtc-pool st)) (n (fn-rtc-nbufs (fn-rtc-config st)))))
           :in-theory (union-theories (theory 'minimal-theory) '((:type-prescription fn-rtc-nslots) (:type-prescription fn-rtc-nbufs) natp (:executable-counterpart natp) (:type-prescription len) unicity-of-0 commutativity-of-+ fix))))))

(defthm fn-rtc-x-state-is
  (implies (fn-rtc-st-p st) (equal (fn-rtc-x-state st) st))
  :hints (("Goal" :use (fn-rtc-xs-six-list fn-rtc-xs-whole-lists (:instance fn-rtc-st-p-is-shapep (x st)))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-rtc-x-state fn-rtc-st-config fn-rtc-st$a-config fn-rtc-st-uses fn-rtc-st$a-uses
                                        fn-rtc-st-next-op fn-rtc-st$a-next-op)))))

; -----------------------------------------------------------------------------
; The keystones an instance receives, by functional instance.

(defconst *fn-rtc-layer-keystones*
  '(fn-rtc-init-establishes-invp                        ; T1
    fn-rtc-step-preserves-invp                          ; T2
    fn-rtc-outstanding-use-is-leased                    ; T3
    fn-rtc-completion-ends-its-use                      ; T4
    fn-rtc-outstanding-use-is-stable                    ; T5
    fn-rtc-unmatched-completion-is-discarded            ; T6
    fn-rtc-machine-changes-only-when-delivered-to   ; T7
    fn-rtc-other-workspaces-are-untouched               ; T8
    fn-rtc-generation-is-monotone                       ; T9
    fn-rtc-every-action-is-outstanding                  ; T10
    fn-rtc-commit-only-on-own-barrier-completion        ; T11
    fn-rtc-step-is-charged                              ; T12
    fn-rtc-last-completion-retires-a-draining-slot      ; T13
    fn-rtc-machine-states-are-bounded                   ; T15
    fn-rtc-x-step*-is fn-rtc-x-step-is
    fn-rtc-x-step-after-landing fn-rtc-landing-then-step-is-the-contract-step
    fn-rtc-host-landing-is-the-contract-step))

(defun fn-rtc-layer-names (prefix fs)
  (declare (xargs :mode :program))
  (if (endp fs) nil (cons (fn-rtc-layer-name prefix (car fs)) (fn-rtc-layer-names prefix (cdr fs)))))

(defun fn-rtc-layer-fi-alist (alist)
  (declare (xargs :mode :program))
  (if (endp alist) nil
    (cons (list (caar alist) (cdar alist)) (fn-rtc-layer-fi-alist (cdr alist)))))

(defun fn-rtc-layer-keystone-events (thms prefix alist fi copies obligations wrld)
  (declare (xargs :mode :program))
  (if (endp thms) nil
    (cons `(defthm ,(fn-rtc-layer-name prefix (car thms))
             ,(fn-rtc-layer-rename (getpropc (car thms) 'untranslated-theorem nil wrld) alist)
             :hints (("Goal" :use ((:functional-instance ,(car thms) ,@fi))
                      :in-theory (union-theories (theory 'minimal-theory) ',(append copies obligations)))))
          (fn-rtc-layer-keystone-events (cdr thms) prefix alist fi copies obligations wrld))))

(defun fn-rtc-def-layer-events (prefix step init static-init committedp c max-reqs max-state reads-view hints wrld)
  (declare (xargs :mode :program))
  (let* ((m-step (fn-rtc-layer-name prefix 'fn-rtc-m-step))
         (copied (fn-rtc-layer-alist prefix (append *fn-rtc-layer-spec-fns* *fn-rtc-layer-exec-fns*)))
         (alist (append `((fn-rtc-m-init . ,init) (fn-rtc-m-static-init . ,static-init) (fn-rtc-m-step . ,m-step)
                          (fn-rtc-m-committedp . ,committedp) (fn-rtc-m-c . ,c)
                          (fn-rtc-m-max-reqs . ,max-reqs) (fn-rtc-m-max-state . ,max-state)
                          (fn-rtc-mx-step . ,step))
                        copied))
         (fi (fn-rtc-layer-fi-alist alist))
         (copies (strip-cdrs copied))
         (obligations (append (list 'natp)
                              (fn-rtc-layer-names prefix
                                                  '(fn-rtc-m-constants fn-rtc-mx-step-is-m-step fn-rtc-m-step-is-charged
                                                    fn-rtc-m-step-requests-are-bounded fn-rtc-m-init-is-bounded
                                                    fn-rtc-m-step-state-is-bounded fn-rtc-m-init-is-uncommitted
                                                    fn-rtc-m-static-init-is-bounded fn-rtc-m-static-init-is-uncommitted
                                                    fn-rtc-m-commits-only-on-fsync-done)))))
    `(progn
       (defun-nx ,m-step (m ev vst q)
         (,step m ev vst q))
       ;; the machine's obligations: the constraints of `fn-rtc-m-step' and
       ;; `fn-rtc-mx-step', stated of this machine
       (defthm ,(fn-rtc-layer-name prefix 'fn-rtc-m-constants)
         (and (natp (,c)) (natp (,max-reqs)) (natp (,max-state)))
         :rule-classes ((:type-prescription :corollary (natp (,c)))
                        (:type-prescription :corollary (natp (,max-reqs)))
                        (:type-prescription :corollary (natp (,max-state)))))
       (defthm ,(fn-rtc-layer-name prefix 'fn-rtc-m-step-is-charged)
         (implies (natp q)
                  (and (natp (mv-nth 2 (,m-step m ev pool q)))
                       (<= (+ (mv-nth 2 (,m-step m ev pool q))
                              (fn-rtc-reqs-octets (mv-nth 1 (,m-step m ev pool q))))
                           (+ q (,c)))))
         :hints ,hints)
       (defthm ,(fn-rtc-layer-name prefix 'fn-rtc-m-step-requests-are-bounded)
         (<= (len (mv-nth 1 (,m-step m ev pool q))) (,max-reqs))
         :hints ,hints)
       (defthm ,(fn-rtc-layer-name prefix 'fn-rtc-m-init-is-bounded)
         (<= (fn-rtc-size (,init)) (,max-state))
         :hints ,hints)
       (defthm ,(fn-rtc-layer-name prefix 'fn-rtc-m-static-init-is-bounded)
         (<= (fn-rtc-size (,static-init j)) (,max-state))
         :hints ,hints)
       (defthm ,(fn-rtc-layer-name prefix 'fn-rtc-m-static-init-is-uncommitted)
         (not (,committedp (,static-init j)))
         :hints ,hints)
       (defthm ,(fn-rtc-layer-name prefix 'fn-rtc-m-step-state-is-bounded)
         (<= (fn-rtc-size (mv-nth 0 (,m-step m ev pool q))) (,max-state))
         :hints ,hints)
       (defthm ,(fn-rtc-layer-name prefix 'fn-rtc-m-init-is-uncommitted)
         (not (,committedp (,init)))
         :hints ,hints)
       (defthm ,(fn-rtc-layer-name prefix 'fn-rtc-m-commits-only-on-fsync-done)
         (implies (and (not (,committedp m))
                       (,committedp (mv-nth 0 (,m-step m ev pool q))))
                  (fn-rtc-fsync-done-p ev))
         :hints ,hints)
       (defthm ,(fn-rtc-layer-name prefix 'fn-rtc-mx-step-is-m-step)
         (equal (,step m ev fn-rtc-st q)
                (,m-step m ev (fn-rtc-view-state (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) fn-rtc-st) q))
         :hints (("Goal" :use ((:instance ,reads-view (st fn-rtc-st)))
                  :in-theory (union-theories (theory 'minimal-theory)
                                             '(,m-step)))))
       (in-theory (disable ,(fn-rtc-layer-name prefix 'fn-rtc-mx-step-is-m-step)))
       (in-theory (disable ,step ,m-step))
       ,@(fn-rtc-layer-rename
          (append (fn-rtc-layer-copies *fn-rtc-layer-spec-fns* :spec copied wrld)
                  (fn-rtc-layer-copies *fn-rtc-layer-exec-fns* :exec copied wrld))
          alist)
       ;; the invariant runs: an exercise checks it after every step
       (verify-guards ,(fn-rtc-layer-name prefix 'fn-rtc-mstates-okp))
       (verify-guards ,(fn-rtc-layer-name prefix 'fn-rtc-invp))
       ,@(fn-rtc-layer-keystone-events *fn-rtc-layer-keystones* prefix alist fi copies obligations wrld))))

; (fn-rtc-def-layer PREFIX :step STEP :init INIT :static-init STATIC-INIT
;   :committedp CP :c C :max-reqs MR :max-state MS :reads-view LEMMA :hints HINTS)
;
; STEP is the machine over the stobj, (STEP m ev fn-rtc-st q) =>
; (mv m2 requests cost), reading configuration and the view readers
; fn-rtc-st-v-owner/-gen/-fill/-byte/-pool at the event's id and incarnation.
; LEMMA proves, in exactly these variables,
; (equal (STEP m ev (fn-rtc-view-state (fn-rtc-ev-id ev) (fn-rtc-ev-inc ev) st) q)
;        (STEP m ev st q)). INIT and STATIC-INIT produce the connection and
; static instance initial states; CP observes commits; C, MR and MS are bounds.
; HINTS prove the machine's constraints over PREFIX-m-step, whose state
; argument is already a view state. The executable layer is PREFIX-x-step
; and PREFIX-x-step*; PREFIX-x-init initializes this instance's machines.
; Its keystones are PREFIX-<keystone> for *fn-rtc-layer-keystones*.
(defmacro fn-rtc-def-layer (prefix &key step init static-init committedp c max-reqs max-state reads-view hints)
  `(make-event (fn-rtc-def-layer-events ',prefix ',step ',init ',static-init ',committedp ',c ',max-reqs ',max-state
                                        ',reads-view ',hints (w state))))
