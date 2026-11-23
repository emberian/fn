; Input admitted by the run adapter fits within one page decoder call.
(in-package "ACL2")
(include-book "runs-served")
(local (include-book "runs-page-reader-proof"))

(local
 (defthm fn2-run-overwide-varint-refused
 (implies (and (member-equal (fn2-layout-kind-code k) '(5 8 10))
               (not (equal k '(:zero 0))) (equal phase 0) (natp pos)
               (or (< 8 pos) (not (equal hi 0))))
          (not (equal (car (fn2-layout-parse-field k bytes rest pos v hi size ref phase next)) :ok)))
 :hints (("Goal" :induct (fn2-layout-parse-field k bytes rest pos v hi size ref phase next)
          :in-theory (e/d (fn2-layout-parse-field fn2-layout-byte)
                          (fn2-layout-kind-code mod floor ash take nthcdr))))))

(local
 (defun fn2-run-field-remaining-bytes (k pos size phase)
 (declare (xargs :verify-guards nil))
 (let ((tag (fn2-layout-kind-code k)))
   (cond ((equal phase 1) (max 1 (- (nfix size) (nfix pos))))
         ((equal tag 7) 33)
         ((equal tag 9) 1)
         (t (+ (nfix (- 9 (nfix pos))) (if (equal tag 10) (nfix (cadr k)) 0)))))))

(local
 (defthm fn2-run-field-step-spends-one-byte
 (let* ((step (fn2-layout-byte k pos v hi size phase byte))
        (code (car step))
        (left (fn2-run-field-remaining-bytes k pos size phase)))
   (implies (and (member-equal (fn2-layout-kind-code k) '(5 7 8 9 10))
                 (or (not (equal (fn2-layout-kind-code k) 10)) (posp (cadr k)))
                 (or (equal phase 0) (equal phase 1)) (natp pos) (natp size) (natp v)
                 (unsigned-byte-p 8 byte)
                 (or (equal phase 1) (not (member-equal (fn2-layout-kind-code k) '(5 8 10)))
                     (<= pos 8)))
            (and (<= 1 left)
                 (implies (member-eq code '(:part :payload))
                          (<= (1+ (fn2-run-field-remaining-bytes k (if (eq code :payload) 0 (1+ pos))
                                   (mv-nth 3 step) (mv-nth 4 step))) left)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn2-run-field-remaining-bytes fn2-layout-byte)
                                 (fn2-layout-kind-code floor mod ash take nthcdr))))))

(local
 (defthm fn2-run-field-transition-phase
 (let ((step (fn2-layout-byte k pos v hi size phase byte)))
  (and (not (eq (car step) :ok))
       (implies (or (equal phase 0) (equal phase 1))
                (or (equal (mv-nth 4 step) 0) (equal (mv-nth 4 step) 1)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn2-layout-byte) (fn2-layout-kind-code nfix mod ash member-equal))))))

(local
 (defthm fn2-run-octets-have-first-byte
 (implies (and (fn-b3-octet-listp xs) (consp xs))
          (and (unsigned-byte-p 8 (car xs)) (fn-b3-octet-listp (cdr xs))))
 :hints (("Goal" :expand (fn-b3-octet-listp xs)))))

(local
 (defun fn2-run-budgeted-fieldp (k pos v hi size phase)
 (declare (xargs :verify-guards nil))
 (and (member-equal (fn2-layout-kind-code k) '(5 7 8 9 10))
      (not (equal k '(:zero 0)))
      (or (not (equal (fn2-layout-kind-code k) 10)) (posp (cadr k)))
      (or (equal phase 0) (equal phase 1))
      (natp pos) (natp hi) (natp v) (natp size))))

(local
 (defthm fn2-run-accepted-transition-budget
 (let* ((step (fn2-layout-byte k pos v hi size phase (car rest)))
        (code (car step)) (np (if (eq code :payload) 0 (1+ (nfix pos))))
        (left (fn2-run-field-remaining-bytes k pos size phase)))
  (implies (and (fn2-run-budgeted-fieldp k pos v hi size phase) (consp rest) (fn-b3-octet-listp rest)
                (equal (car (fn2-layout-parse-field k bytes rest pos v hi size ref phase next)) :ok))
           (and (not (equal k '(:zero 0))) (not (equal code :ok)) (<= 1 left)
                (implies (member-eq code '(:part :payload))
                         (and (fn2-run-budgeted-fieldp k np (mv-nth 1 step) (mv-nth 2 step)
                                                       (mv-nth 3 step) (mv-nth 4 step))
                              (<= (1+ (fn2-run-field-remaining-bytes k np (mv-nth 3 step) (mv-nth 4 step)))
                                  left))))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-run-field-step-spends-one-byte (byte (car rest)))
                       (:instance fn2-run-field-transition-phase (byte (car rest)))
                       (:instance fn2-run-layout-byte-naturals (byte (car rest)) (high hi) (payload phase))
                       (:instance fn2-run-octets-have-first-byte (xs rest))
                       fn2-run-overwide-varint-refused)
          :in-theory (e/d (fn2-run-budgeted-fieldp)
                          (member-equal fn2-layout-kind-code fn2-layout-byte fn2-run-field-remaining-bytes
                           fn2-layout-parse-field unsigned-byte-p fn-b3-octet-listp))))))

(local
 (defthm fn2-run-zero-padding-outside-row-budget
 (not (fn2-run-budgeted-fieldp '(:zero 0) pos v hi size phase))
 :hints (("Goal" :in-theory (enable fn2-run-budgeted-fieldp)))))

(local
 (defthm fn2-run-accepted-field-budget
 (let ((parse (fn2-layout-parse-field k bytes rest pos v hi size ref phase next)))
  (implies (and (fn2-run-budgeted-fieldp k pos v hi size phase)
                (fn-b3-octet-listp rest) (equal (car parse) :ok))
           (and (fn-b3-octet-listp (mv-nth 2 parse))
                (<= (len rest) (+ (fn2-run-field-remaining-bytes k pos size phase) (len (mv-nth 2 parse)))))))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-layout-parse-field k bytes rest pos v hi size ref phase next)
          :do-not '(preprocess)
          :expand ((:free (pos v hi size ref phase next) (fn2-layout-parse-field k bytes rest pos v hi size ref phase next)))
          :in-theory (e/d ((:induction fn2-layout-parse-field))
                          (fn2-run-budgeted-fieldp nfix (:definition fn2-layout-parse-field) fn2-run-field-remaining-bytes
                           fn2-layout-byte fn2-layout-kind-code fn-b3-octet-listp unsigned-byte-p member-equal take nthcdr)))
          (and (equal (access clause-id id :pool-lst) '(1))
               (equal (len (access clause-id id :case-lst)) 1)
               (equal (access clause-id id :primes) 0)
               '(:use fn2-run-accepted-transition-budget)))))

(local
 (defun fn2-run-row-decoder-bound (layout)
 (declare (xargs :verify-guards nil))
 (if (atom layout) 0
   (let ((tail (fn2-run-row-decoder-bound (cdr layout))) (k (cadar layout)))
     (and tail (fn2-run-budgeted-fieldp k 0 0 0 0 0)
          (+ (fn2-run-field-remaining-bytes k 0 0 0) tail))))))

(local
 (defthm fn2-run-admitted-layout-byte-budget
 (let ((parse (fn2-layout-parse layout bytes)) (budget (fn2-run-row-decoder-bound layout)))
   (implies (and budget (fn-b3-octet-listp bytes) (equal (car parse) :ok))
            (<= (len bytes) (+ budget (len (mv-nth 2 parse))))))
 :rule-classes nil
 :hints (("Goal" :induct (fn2-layout-parse layout bytes)
          :expand ((fn2-layout-parse layout bytes) (fn2-run-row-decoder-bound layout))
          :in-theory (disable fn2-layout-parse-field fn2-run-field-remaining-bytes
                              fn2-run-budgeted-fieldp fn-b3-octet-listp))
         ("Subgoal *1/3" :use ((:instance fn2-run-accepted-field-budget
              (k (cadar layout)) (rest bytes) (pos 0) (v 0) (hi 0) (size 0)
              (ref 0) (phase 0) (next 0)))))))

(defthm fn2-run-overview-admission-fits-decoder
 (implies (and (or (equal layout *fn2-overview-entry*) (equal layout *fn2-overview-index*))
               (fn2-run-values-layoutp layout row))
          (and (<= (len (fn2-layout-octets layout row)) (if (equal layout *fn2-overview-entry*) 1069 106))
               (<= (len (fn2-layout-octets layout row)) *fn2-codec-decode-fuel*)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn2-run-admitted-layout-byte-budget
                         (bytes (fn2-layout-octets layout row))))
          :in-theory (e/d (fn2-run-values-layoutp)
                          (fn2-layout-parse fn2-layout-octets fn-b3-octet-listp)))))
