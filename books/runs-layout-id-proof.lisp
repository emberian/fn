; ID fields in an admitted run entry parse as unsigned 60-bit values.
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

(local
 (defun fn2-run-id-accumulatorp (pos v hi)
 (declare (xargs :verify-guards nil))
 (and (unsigned-byte-p 60 v) (or (not (equal hi 0)) (< 8 pos) (< v (expt 128 (nfix pos)))))))

(local
 (defthm fn2-run-id-accumulates-digit
 (let* ((wide (or (not (equal hi 0)) (> pos 8) (and (equal pos 8) (>= low 16))))
        (nv (if wide v (+ v (ash low (* 7 (min 8 pos)))))))
  (implies (and (natp pos) (natp low) (< low 128) (fn2-run-id-accumulatorp pos v hi))
           (and (unsigned-byte-p 60 nv)
                (fn2-run-id-accumulatorp (1+ pos) nv (if wide 1 0)))))
 :rule-classes nil
 :hints (("Goal" :cases ((equal pos 0) (equal pos 1) (equal pos 2) (equal pos 3) (equal pos 4) (equal pos 5) (equal pos 6) (equal pos 7) (equal pos 8))
          :in-theory (e/d (fn2-run-id-accumulatorp unsigned-byte-p ash) (expt))))))

(local
 (defthm fn2-run-id-step-width
 (let* ((step (fn2-layout-byte (list :id id) pos v hi size 0 byte)) (code (car step)))
  (implies (and (natp pos) (unsigned-byte-p 8 byte) (fn2-run-id-accumulatorp pos v hi))
           (and (not (equal code :ok)) (not (equal code :payload))
                (equal (mv-nth 4 step) 0) (unsigned-byte-p 60 (mv-nth 1 step))
                (implies (equal code :part)
                         (fn2-run-id-accumulatorp (+ 1 pos) (mv-nth 1 step) (mv-nth 2 step))))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-run-id-accumulates-digit (low (mod byte 128))))
          :in-theory (e/d (fn2-layout-byte) (fn2-run-id-accumulatorp ash mod))))))

(local
 (defthm fn2-run-parse-id-width
 (let ((parse (fn2-layout-parse-field (list :id id) bytes rest pos v hi size ref phase next)))
  (implies (and (fn-b3-octet-listp rest) (natp pos) (equal phase 0)
                (fn2-run-id-accumulatorp pos v hi) (equal (car parse) :ok))
           (unsigned-byte-p 60 (mv-nth 1 parse))))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-layout-parse-field (list :id id) bytes rest pos v hi size ref phase next)
          :do-not '(preprocess)
          :in-theory (disable fn2-layout-byte fn2-run-id-accumulatorp unsigned-byte-p fn-b3-octet-listp))
         (and (equal (access clause-id id :pool-lst) '(1))
              (equal (len (access clause-id id :case-lst)) 1)
              (equal (access clause-id id :primes) 0)
              '(:use ((:instance fn2-run-id-step-width (byte (car rest)))))))))

; Follow the parser remainder and field index together.
(defun-nx fn2-run-parse-at-induct (i layout bytes)
  (declare (xargs :verify-guards nil :measure (nfix i)))
  (if (or (zp i) (atom layout)) bytes
    (fn2-run-parse-at-induct (1- i) (cdr layout)
                             (mv-nth 2 (fn2-layout-parse-field (cadar layout) bytes bytes 0 0 0 0 0 0 0)))))

(local
 (defthm fn2-run-parsed-id-width
  (let ((out (fn2-layout-parse layout bytes)))
    (implies (and (fn-b3-octet-listp bytes)
                  (equal (cadr (nth i layout)) (list :id id))
                  (natp i) (eq (mv-nth 0 out) :ok))
             (unsigned-byte-p 60 (nth i (mv-nth 1 out)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-run-parse-at-induct i layout bytes)
           :expand ((fn2-layout-parse layout bytes))
           :in-theory (disable fn2-layout-parse-field fn-b3-octet-listp unsigned-byte-p))
          ("Subgoal *1/1" :use
           ((:instance fn2-run-parse-id-width (rest bytes) (pos 0) (v 0)
                       (hi 0) (size 0) (ref 0) (phase 0) (next 0)))))))

(defthm fn2-run-layout-id-width
 (implies (and (fn2-run-values-layoutp layout values)
               (equal (cadr (nth i layout)) (list :id id)) (natp i))
          (unsigned-byte-p 60 (nth i values)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-run-parsed-id-width (bytes (fn2-layout-octets layout values))))
          :in-theory (e/d (fn2-run-values-layoutp) (fn2-layout-parse fn2-layout-octets fn-b3-octet-listp unsigned-byte-p nth)))))

(defthm fn2-run-layout-id-natural
 (implies (and (fn2-run-values-layoutp layout values)
               (equal (cadr (nth i layout)) (list :id id)) (natp i))
          (natp (nth i values)))
 :rule-classes nil
 :hints (("Goal" :use (fn2-run-layout-id-width)
          :in-theory (disable fn2-run-values-layoutp nth))))
