; ID fields in an admitted run entry parse as natural numbers.
(in-package "ACL2")
(include-book "runs-page")

(local
 (defthm fn2-run-parse-field-octet-tail
   (implies (fn-b3-octet-listp rest)
            (fn-b3-octet-listp
             (mv-nth 2 (fn2-layout-parse-field k bytes rest pos v hi size ref phase next))))
   :hints (("Goal" :induct (fn2-layout-parse-field k bytes rest pos v hi size ref phase next)
            :in-theory (disable fn2-layout-byte)))))

(local (defthm fn2-run-byte-of-octet-list
 (implies (and (fn-b3-octet-listp xs) (consp xs))
          (unsigned-byte-p 8 (car xs)))
 :hints (("Goal" :expand (fn-b3-octet-listp xs)))))
(local (defthm fn2-run-octet-tail
 (implies (fn-b3-octet-listp xs) (fn-b3-octet-listp (cdr xs)))
 :hints (("Goal" :expand (fn-b3-octet-listp xs)))))
(local (defthm fn2-run-id-byte-returns-step
 (not (equal (car (fn2-layout-byte (list :id id) pos v hi size phase byte)) :ok))
 :hints (("Goal" :in-theory (enable fn2-layout-byte)))))
(local (defthm fn2-run-id-byte-natural-type
 (implies (and (natp pos) (natp v) (unsigned-byte-p 8 byte))
          (natp (mv-nth 1 (fn2-layout-byte (list :id id) pos v hi size phase byte))))
 :rule-classes (:rewrite :type-prescription)
 :hints (("Goal" :in-theory (enable fn2-layout-byte)))))
(local
 (defthm fn2-run-parse-id-natural
   (let ((out (fn2-layout-parse-field (list :id id) bytes rest pos v hi size ref phase next)))
     (implies (and (fn-b3-octet-listp rest) (natp pos) (natp v)
                   (eq (mv-nth 0 out) :ok))
              (natp (mv-nth 1 out))))
   :rule-classes :type-prescription
   :hints (("Goal" :induct (fn2-layout-parse-field (list :id id) bytes rest pos v hi size ref phase next)
            :in-theory (disable fn2-layout-byte fn-b3-octet-listp unsigned-byte-p)))))

; Follow the parser remainder and field index together.
(defun-nx fn2-run-parse-at-induct (i layout bytes)
  (declare (xargs :verify-guards nil :measure (nfix i)))
  (if (or (zp i) (atom layout)) bytes
    (fn2-run-parse-at-induct (1- i) (cdr layout)
                             (mv-nth 2 (fn2-layout-parse-field (cadar layout) bytes bytes 0 0 0 0 0 0 0)))))

(local
 (defthm fn2-run-parsed-id-natural
  (let ((out (fn2-layout-parse layout bytes)))
    (implies (and (fn-b3-octet-listp bytes)
                  (equal (cadr (nth i layout)) (list :id id))
                  (natp i) (eq (mv-nth 0 out) :ok))
             (natp (nth i (mv-nth 1 out)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-run-parse-at-induct i layout bytes)
           :expand ((fn2-layout-parse layout bytes))
           :in-theory (disable fn2-layout-parse-field fn-b3-octet-listp))
          ("Subgoal *1/1" :use
           ((:instance fn2-run-parse-id-natural (rest bytes) (pos 0) (v 0)
                       (hi 0) (size 0) (ref 0) (phase 0) (next 0)))))))

(defthm fn2-run-layout-id-natural
 (implies (and (fn2-run-values-layoutp layout values)
               (equal (cadr (nth i layout)) (list :id id)) (natp i))
          (natp (nth i values)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-run-parsed-id-natural (bytes (fn2-layout-octets layout values))))
          :in-theory (e/d (fn2-run-values-layoutp) (fn2-layout-parse fn2-layout-octets fn-b3-octet-listp nth)))))
