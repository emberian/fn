; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-new-row-corr-readback")

(defun-nx fn-lb-log-model-next-range (payload) (if (fn-rcl-tombstonep payload) (fn-la-tombstone-raw payload) (fn-la-payload-wire payload)))

(defun-nx fn-lb-log-model-next-prefix (row payload) (append (fn-lb-log-model-pre row payload) (fn-lb-log-model-next-range payload) (fn-lb-log-model-home-frame row)))

(defun-nx fn-lb-log-model-next-entry (row payload segment) (list (len (caddr segment)) (len (cadr segment)) (len (fn-lb-log-model-next-prefix row payload)) (+ (len (cadr segment)) (len (fn-lb-log-model-pre row payload))) (len (fn-lb-log-model-next-range payload)) (fn-record-payload row) payload (fn-lb-log-model-homes row) (fn-record-sequence row)))

(local (defthm fn-lblav-nth-of-cons
 (equal (nth i (cons value rest)) (if (zp i) value (nth (- (nfix i) 1) rest)))
 :hints (("Goal" :in-theory (enable nth)))))

(defthm fn-lb-log-append-to-segment-directory-by-definition
 (equal (caddr (fn-lb-log-model-append-to-segment row payload segment))
        (append (caddr segment) (list (fn-lb-log-model-next-entry row payload segment))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lb-log-model-append-to-segment fn-lb-log-model-next-entry fn-lb-log-model-next-prefix fn-lb-log-model-next-range car-cons cdr-cons)))))

(defthm fn-lb-log-append-to-segment-bytes-by-definition
 (equal (cadr (fn-lb-log-model-append-to-segment row payload segment))
        (append (cadr segment) (fn-lb-log-model-next-prefix row payload)
                (fn-blake3-stobj (fn-lb-log-model-next-prefix row payload))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory) '(fn-lb-log-model-append-to-segment fn-lb-log-model-next-entry fn-lb-log-model-next-prefix fn-lb-log-model-next-range car-cons cdr-cons)))))

(defthm fn-lb-log-next-entry-ordinal-by-definition
 (equal (nth 0 (fn-lb-log-model-next-entry row payload segment)) (len (caddr segment)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lb-log-model-next-entry fn-lblav-nth-of-cons
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+))))))

(defthm fn-lb-log-next-entry-entry-offset-by-definition
 (equal (nth 1 (fn-lb-log-model-next-entry row payload segment)) (len (cadr segment)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lb-log-model-next-entry fn-lblav-nth-of-cons
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+))))))

(defthm fn-lb-log-next-entry-protected-length-by-definition
 (equal (nth 2 (fn-lb-log-model-next-entry row payload segment)) (len (fn-lb-log-model-next-prefix row payload)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lb-log-model-next-entry fn-lblav-nth-of-cons
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+))))))

(defthm fn-lb-log-next-entry-served-offset-by-definition
 (equal (nth 3 (fn-lb-log-model-next-entry row payload segment)) (+ (len (cadr segment)) (len (fn-lb-log-model-pre row payload))))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lb-log-model-next-entry fn-lblav-nth-of-cons
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+))))))

(defthm fn-lb-log-next-entry-served-length-by-definition
 (equal (nth 4 (fn-lb-log-model-next-entry row payload segment)) (len (fn-lb-log-model-next-range payload)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lb-log-model-next-entry fn-lblav-nth-of-cons
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+))))))

(defthm fn-lb-log-next-entry-handle-by-definition
 (equal (nth 5 (fn-lb-log-model-next-entry row payload segment)) (fn-record-payload row))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lb-log-model-next-entry fn-lblav-nth-of-cons
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+))))))

(defthm fn-lb-log-next-entry-payload-by-definition
 (equal (nth 6 (fn-lb-log-model-next-entry row payload segment)) payload)
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lb-log-model-next-entry fn-lblav-nth-of-cons
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+))))))

(defthm fn-lb-log-next-entry-homes-by-definition
 (equal (nth 7 (fn-lb-log-model-next-entry row payload segment)) (fn-lb-log-model-homes row))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lb-log-model-next-entry fn-lblav-nth-of-cons
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+))))))

(defthm fn-lb-log-next-entry-sequence-by-definition
 (equal (nth 8 (fn-lb-log-model-next-entry row payload segment)) (fn-record-sequence row))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lb-log-model-next-entry fn-lblav-nth-of-cons
     (:executable-counterpart nfix) (:executable-counterpart zp) (:executable-counterpart binary-+))))))
