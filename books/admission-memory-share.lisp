; K-BOUND's hard lemma (Builder M, memory landing 4b): a held row interned under an
; admitted profile is within the per-row invariant (books/admission-memory.lisp
; fn-adm-row-within-p).  Statement approved by Codex
; (build/memory/l4b/m11/kbound9/premises.lisp, codex-kbound11.final.md).
; DEFINITIONS ONLY so far: fn-adm-held-share and fn-adm-hstxa-share are not yet proved
; (build/memory/l4b/m13/share-continuation.md).
(in-package "ACL2")
(include-book "admission-memory")
(include-book "catalog-record")
(include-book "store-intern")

(defun fn-adm-u64-cdrs-p (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp (car x))
           (unsigned-byte-p 64 (cdr (car x)))
           (fn-adm-u64-cdrs-p (cdr x)))
    t))

; The numbered-row domain, a producer fact of every numbering: distinct member keys,
; u64 counters and withdrawal fields.
(defun fn-adm-numbers-domain-p (h)
  (declare (xargs :verify-guards nil))
  (and (no-duplicatesp-equal (strip-cars (fn-held-numbers h)))
       (subsetp-equal (strip-cars (fn-held-numbers h)) (fn-record-groups h))
       (fn-adm-u64-cdrs-p (fn-held-numbers h))
       (or (null (fn-held-withdrawn h))
           (and (unsigned-byte-p 64 (car (fn-held-withdrawn h)))
                (unsigned-byte-p 64 (cdr (fn-held-withdrawn h)))))))
