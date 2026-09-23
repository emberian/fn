; byte-store-sweep-tests.lisp -- teeth for K-sweep (books/byte-store-keystones).
;
; Finding F2 of planning/evidence/campaign-dabebb84-2026-09-22.md: a death at
; frontier-staged-durable leaves the allocator's stage in :staging.  The
; witness is that exact cut of the real allocator program over the concrete
; metadata seam (the executable attachments of books/byte-store-frame, the
; same route tests/acl2/byte-store-relation-tests.lisp takes), and the sweep's
; unlink of that stage.  Witnesses are functions because ACL2 ignores
; defattach while evaluating defconsts.

(in-package "ACL2")
(include-book "../../books/byte-store-keystones")
(include-book "../../books/byte-store-relation")
(include-book "../../books/byte-store-frame")

(defun bss-stage () ".allocation-4242-000000000000000000000001")

(defun bss-run ()
  (fn-bs-run (fn-bs-initial-image 4 (fn-bs-initial-config-octets)
                                  (fn-bs-initial-frontier-octets))
             (fn-sf-initial-state)
             (fn-bs-frontier-program (bss-stage) (fn-bs-frontier-encode-impl 1))
             nil nil nil))

; The byte state an unlink leaves, as a value: an mv-returning call cannot
; sit under mv-nth in executable code.
(defun bss-unlinked (bs dir name)
  (mv-let (result bs1) (fn-bs-unlink bs dir name :ok)
    (declare (ignore result))
    bs1))

(defun bss-cut-index (steps name i)
  (cond ((atom steps) nil)
        ((equal (car steps) (list :cut name)) i)
        (t (bss-cut-index (cdr steps) name (1+ i)))))

; The pair at frontier-staged-durable: the stage is durable and named in
; :staging, the rename has not happened.
(defun bss-at-cut ()
  (nth (bss-cut-index (fn-bs-frontier-program (bss-stage) (fn-bs-frontier-encode-impl 1))
                      "frontier-staged-durable" 0)
       (bss-run)))

(assert-event (natp (bss-cut-index (fn-bs-frontier-program (bss-stage) (fn-bs-frontier-encode-impl 1))
                                   "frontier-staged-durable" 0)))
(assert-event (fn-bs-inop (fn-bs-lookup (car (bss-at-cut)) :staging (bss-stage))))
(assert-event (fn-bs-store-relation (car (bss-at-cut)) (cdr (bss-at-cut))))
(assert-event (fn-bs-scan-okp (fn-bs-scan-store (car (bss-at-cut)))))

; fn-bs-staging-unlink-keeps-relation-and-scan, the witness: the sweep's
; unlink of that stage removes the name, keeps the relation to the same
; kernel state, and keeps the scan (frontier 0, no records).
(assert-event
 (let* ((bs (car (bss-at-cut))) (ks (cdr (bss-at-cut)))
        (bs1 (bss-unlinked bs :staging (bss-stage))))
   (and (not (equal bs1 bs))
        (null (fn-bs-lookup bs1 :staging (bss-stage)))
        (fn-bs-store-relation bs1 ks)
        (equal (fn-bs-scan-store bs1) (fn-bs-scan-store bs))
        (equal (fn-bs-scan-frontier (fn-bs-scan-store bs1)) 0))))

; fn-bs-recover-sweep-keeps-relation-at-every-cut, the witness: the sweep
; program over that name and a name that is not there (ENOENT, a concurrent
; removal) keeps every pair related with the original scan.
(assert-event
 (let ((bs (car (bss-at-cut))) (ks (cdr (bss-at-cut))))
   (fn-bs-sweep-run-okp
    (fn-bs-run bs ks (fn-bs-recover-sweep-program (list (bss-stage))) nil nil nil)
    ks (fn-bs-scan-store bs))))

; Teeth.  The theorem is about :staging.  The same unlink in the root
; directory, at the frontier's name, is the separating case: the scan faults
; at the frontier and the relation is gone.
(assert-event
 (let* ((bs (car (bss-at-cut))) (ks (cdr (bss-at-cut)))
        (bs1 (bss-unlinked bs :root *fn-bs-frontier-name*)))
   (and (not (fn-bs-scan-okp (fn-bs-scan-store bs1)))
        (not (equal (fn-bs-scan-store bs1) (fn-bs-scan-store bs)))
        (not (fn-bs-store-relation bs1 ks)))))

; The relation hypothesis: from an unrelated state (a zero write unit) the
; unlink cannot produce a related one.
(assert-event
 (let* ((bs (fn-bs-initial-image 0 (fn-bs-initial-config-octets)
                                 (fn-bs-initial-frontier-octets)))
        (bs1 (bss-unlinked bs :staging (bss-stage))))
   (and (not (fn-bs-store-relation bs (fn-sf-initial-state)))
        (not (fn-bs-store-relation bs1 (fn-sf-initial-state))))))
