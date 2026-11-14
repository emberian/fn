(in-package "ACL2")
(include-book "../books/square-evidence")
(include-book "std/testing/must-fail" :dir :system)

; Actual mutation: retain the returned status and changed cell, clobber sibling.
(defstobj fn2-evidence-cell
 (fn2-evidence-value :type (unsigned-byte 8) :initially 0)
 (fn2-evidence-sibling :type (unsigned-byte 8) :initially 91))
(defun fn2-evidence-write (value fn2-evidence-cell)
 (declare (xargs :stobjs fn2-evidence-cell :guard (unsigned-byte-p 8 value)))
 (mv :ok (update-fn2-evidence-value value fn2-evidence-cell)))
(defun fn2-evidence-write-expected (value before)
 (list :ok (list value (cadr before))))
(defun fn2-evidence-write-resultp (value before code after)
 (equal (list code after) (fn2-evidence-write-expected value before)))
(defun-nx fn2-evidence-write-observed (value cell)
 (declare (xargs :guard (and (fn2-evidence-cellp cell) (unsigned-byte-p 8 value))))
 (mv-let (code after) (fn2-evidence-write value cell) (list code after)))
(defun-nx fn2-evidence-write-mutant (value cell)
 (declare (xargs :guard (and (fn2-evidence-cellp cell) (unsigned-byte-p 8 value))))
 (mv-let (code after) (fn2-evidence-write value cell)
  (list code (update-fn2-evidence-sibling 0 after))))
(defthm fn2-evidence-write-resultp-unfolds
 (equal
  (mv-let (code after) (fn2-evidence-write value cell)
   (fn2-evidence-write-resultp value cell code after))
  (equal (fn2-evidence-write-observed value cell)
         (fn2-evidence-write-expected value cell)))
 :rule-classes nil)
; Logically valid but its unnecessarily restricted domain is not implied by H.
(defthm fn2-evidence-write-positive-only-unfolds
 (implies (< 0 value)
  (equal
   (mv-let (code after) (fn2-evidence-write value cell)
    (fn2-evidence-write-resultp value cell code after))
   (equal (fn2-evidence-write-observed value cell)
          (fn2-evidence-write-expected value cell))))
 :rule-classes nil)
(defthm fn2-evidence-write-wrong-conclusion-unfolds
 (equal
  (mv-let (code after) (fn2-evidence-write 0 cell)
   (fn2-evidence-write-resultp 0 cell code after))
  (equal (fn2-evidence-write-observed 0 cell)
         (fn2-evidence-write-expected 0 cell)))
 :rule-classes nil)
(defun fn2-evidence-correspondence-runtime-control ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-evidence-cell
  (mv-let (answer fn2-evidence-cell)
   (mv-let (code fn2-evidence-cell) (fn2-evidence-write 42 fn2-evidence-cell)
    (let* ((before-mutation (list code (fn2-evidence-value fn2-evidence-cell)
                                      (fn2-evidence-sibling fn2-evidence-cell)))
           (fn2-evidence-cell (update-fn2-evidence-sibling 0 fn2-evidence-cell)))
     (mv (and (equal before-mutation '(:ok 42 91))
              (equal (fn2-evidence-value fn2-evidence-cell) 42)
              (not (equal (fn2-evidence-sibling fn2-evidence-cell) 91)))
         fn2-evidence-cell)))
   answer)))
(assert-event (fn2-evidence-correspondence-runtime-control))
(defthm-owed fn2-evidence-opaque-write (value cell)
 (implies (and (fn2-evidence-cellp cell) (unsigned-byte-p 8 value))
  (mv-let (code after) (fn2-evidence-write value cell)
   (fn2-evidence-write-resultp value cell code after)))
 :sides (:concrete fn2-evidence-write-observed :reference fn2-evidence-write-expected)
 :teeth (fn2-evidence-correspondence-runtime-control))

; All three have good ground values. Missing, redirected and domain-narrowing
; correspondences must nevertheless refuse before installing evidence.
(must-fail
 (defsquare-evidence fn2-evidence-opaque-write
  :positive ((value '42) (cell '(0 91)))
  :negative (:kind :mutation :at fn2-evidence-write-observed
             :replace fn2-evidence-write-mutant :bindings ((value '42) (cell '(0 91))))))
(must-fail
 (defsquare-evidence fn2-evidence-opaque-write
  :correspondence fn2-evidence-write-wrong-conclusion-unfolds
  :positive ((value '42) (cell '(0 91)))
  :negative (:kind :mutation :at fn2-evidence-write-observed
             :replace fn2-evidence-write-mutant :bindings ((value '42) (cell '(0 91))))))
(must-fail
 (defsquare-evidence fn2-evidence-opaque-write
  :correspondence fn2-evidence-write-positive-only-unfolds
  :positive ((value '42) (cell '(0 91)))
  :negative (:kind :mutation :at fn2-evidence-write-observed
             :replace fn2-evidence-write-mutant :bindings ((value '42) (cell '(0 91))))))

; Logical wrapper execution is opened explicitly; the kernel proves the
; original MV-LET predicate as well as its exact endpoint equality.
(local (in-theory (disable (:executable-counterpart fn2-evidence-write-observed)
                           (:executable-counterpart fn2-evidence-write-mutant))))
(defsquare-evidence fn2-evidence-opaque-write
 :correspondence fn2-evidence-write-resultp-unfolds
 :positive ((value '42) (cell '(0 91)))
 :negative (:kind :mutation :at fn2-evidence-write-observed
            :replace fn2-evidence-write-mutant :bindings ((value '42) (cell '(0 91)))))
(fn2-assert-square-evidence fn2-evidence-opaque-write)
(assert-event
 (equal (fn2-decl-get :proof (fn2-decl-row '(:square fn2-evidence-opaque-write) (w state)))
        '(:owed)))

; Coherently replace both theorem locator and recorded theorem body. A real
; admitted theorem about a different C still cannot redirect the original row.
(encapsulate ()
 (local
  (make-event
   (let* ((row (fn2-decl-row '(:square fn2-evidence-opaque-write) (w state)))
          (e (fn2-decl-get :evidence row))
          (e (fn2-decl-set :correspondence 'fn2-evidence-write-wrong-conclusion-unfolds e))
          (e (fn2-decl-set :correspondence-body
               (getpropc 'fn2-evidence-write-wrong-conclusion-unfolds 'theorem nil (w state)) e)))
    (value `(table fn2-squares 'fn2-evidence-opaque-write
                   ',(fn2-decl-set :evidence e row))))))
 (local (must-fail (fn2-assert-square-evidence fn2-evidence-opaque-write))))
(fn2-assert-square-evidence fn2-evidence-opaque-write)

; Derived fields are checked rather than treated as authoritative metadata.
(assert-event
 (let* ((row (fn2-decl-row '(:square fn2-evidence-opaque-write) (w state)))
        (e (fn2-decl-get :evidence row)))
  (mv-let (hyp conclusion)
    (fn2-evidence-parts (fn2-decl-statement-body (fn2-decl-get :statement row) (w state)))
   (declare (ignore hyp))
   (and (not (fn2-evidence-normalization-currentp
               (fn2-decl-set :normalization-domain ''nil e) conclusion (w state)))
        (not (fn2-evidence-normalization-currentp
               (fn2-decl-set :normalized-conclusion ''t e) conclusion (w state)))))))

; A correspondence valid only inside the removed premise cannot establish a
; sensitivity control outside that domain, even if its positive domain holds.
(defun fn2-evidence-domain-clamp (x) (if (natp x) x 0))
(defun fn2-evidence-domain-identity (x) x)
(defun fn2-evidence-domain-resultp (x)
 (equal (fn2-evidence-domain-clamp x) (fn2-evidence-domain-identity x)))
(defthm fn2-evidence-domain-resultp-unfolds
 (equal (fn2-evidence-domain-resultp x)
        (equal (fn2-evidence-domain-clamp x) (fn2-evidence-domain-identity x)))
 :rule-classes nil)
(defthm fn2-evidence-domain-only-unfolds
 (implies (natp x)
  (equal (fn2-evidence-domain-resultp x)
         (equal (fn2-evidence-domain-clamp x) (fn2-evidence-domain-identity x))))
 :rule-classes nil)
(defthm fn2-evidence-domain-extra-variable-unfolds
 (implies (natp extra)
  (equal (fn2-evidence-domain-resultp x)
         (equal (fn2-evidence-domain-clamp x) (fn2-evidence-domain-identity x))))
 :rule-classes nil)
(defthm-owed fn2-evidence-opaque-domain (x)
 (implies (natp x) (fn2-evidence-domain-resultp x))
 :sides (:concrete fn2-evidence-domain-clamp :reference fn2-evidence-domain-identity)
 :teeth (fn2-evidence-correspondence-runtime-control))
(must-fail
 (defsquare-evidence fn2-evidence-opaque-domain
  :correspondence fn2-evidence-domain-extra-variable-unfolds
  :positive ((x '3))
  :negative (:kind :hypothesis-removal :remove (natp x) :bindings ((x '-1)))))
(must-fail
 (defsquare-evidence fn2-evidence-opaque-domain
  :correspondence fn2-evidence-domain-only-unfolds
  :positive ((x '3))
  :negative (:kind :hypothesis-removal :remove (natp x) :bindings ((x '-1)))))
(defsquare-evidence fn2-evidence-opaque-domain
 :correspondence fn2-evidence-domain-resultp-unfolds
 :positive ((x '3))
 :negative (:kind :hypothesis-removal :remove (natp x) :bindings ((x '-1))))
(fn2-assert-square-evidence fn2-evidence-opaque-domain)
