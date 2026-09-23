(in-package "ACL2")
(include-book "../../books/byte-store-fault-keystones")
(include-book "../../books/byte-store-frame")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../../books/codec-attach")

(defconst *fn-bsfk-groups* '("fn.letters" "fn.test"))
(defconst *fn-bsfk-capacity* 10)
(defconst *fn-bsfk-record*
  (fn-record-make 0 0 0 "<k7@example.invalid>" '(90)
                  *fn-bsfk-groups* "archive" "subject" "evidence" 2))
(defconst *fn-bsfk-frontier-run*
  (fn-bs-run *fn-bs-initialized-store* (fn-sf-initial-state)
             *fn-bs-p-frontier* nil *fn-bsfk-groups* *fn-bsfk-capacity*))
(defconst *fn-bsfk-reserved* (cdr (car (last *fn-bsfk-frontier-run*))))
(defconst *fn-bsfk-staged*
  (fn-sf-prepare-record *fn-bsfk-reserved* *fn-bsfk-record*
                        *fn-bsfk-groups* *fn-bsfk-capacity*))
(defconst *fn-bsfk-record-run*
  (fn-bs-run (car (car (last *fn-bsfk-frontier-run*))) *fn-bsfk-staged*
             *fn-bs-p-record* nil *fn-bsfk-groups* *fn-bsfk-capacity*))

(defun fn-bsfk-link-conclusion (bs ks stage name outcome)
  (mv-let (result bs1)
    (fn-bs-link bs :staging stage :transactions name outcome)
    (and (equal result (car outcome))
         (fn-sf-fencedp (fn-sf-record-link-result ks :error))
         (not (fn-bs-dir-quietp bs1 :transactions))
         (fn-bs-dir-quietp (fn-bs-fence-dir bs1 :transactions) :transactions))))

(defun fn-bsfk-rename-conclusion (bs ks stage outcome)
  (mv-let (result bs1)
    (fn-bs-rename bs :staging stage :root *fn-bs-frontier-name* outcome)
    (and (equal result (car outcome))
         (fn-sf-fencedp (fn-sf-frontier-replace-result ks :error))
         (not (fn-bs-dir-quietp bs1 :root))
         (fn-bs-dir-quietp (fn-bs-fence-dir bs1 :root) :root))))

(defun fn-bsfk-dir-conclusion (bs ks dir outcome)
  (mv-let (result bs1) (fn-bs-fsync-dir bs dir outcome)
    (and (equal result (car outcome))
         (fn-bs-dir-quietp bs1 dir)
         (fn-sf-fencedp
          (if (equal dir :transactions)
              (fn-sf-record-dir-result ks :error)
            (fn-sf-frontier-dir-result ks :error))))))

(defconst *fn-bsfk-bad-record-state*
  (fn-sf-make :record-data-durable "bad" nil nil nil nil nil nil))
(defconst *fn-bsfk-bad-frontier-state*
  (fn-sf-make :frontier-data-durable "bad" nil nil nil nil nil nil))
(defconst *fn-bsfk-bad-record-attempted-state*
  (fn-sf-make :record-attempted "bad" nil nil nil nil nil nil))
(defconst *fn-bsfk-bad-frontier-attempted-state*
  (fn-sf-make :frontier-attempted "bad" nil nil nil nil nil nil))

; Full premise and conclusion of the issued-link fact at a reachable pair.
(assert-event
 (let* ((pair (nth 6 *fn-bsfk-record-run*))
        (bs (car pair)) (ks (cdr pair))
        (outcome (cons :eio :issued)))
   (and (fn-sf-statep ks)
        (equal (fn-sf-phase ks) :record-data-durable)
        (fn-bs-inop (fn-bs-lookup bs :staging ".stage-1"))
        (not (fn-bs-lookup bs :transactions "00000000000000000000.txn"))
        (equal (cdr outcome) :issued)
        (fn-bsfk-link-conclusion bs ks ".stage-1"
                                  "00000000000000000000.txn" outcome))))

; Each remaining issued-link hypothesis is essential.
(must-fail (assert-event
 (let* ((pair (nth 6 *fn-bsfk-record-run*)) (bs (car pair)))
   (and (not (fn-sf-statep *fn-bsfk-bad-record-state*))
        (equal (fn-sf-phase *fn-bsfk-bad-record-state*) :record-data-durable)
        (fn-bs-inop (fn-bs-lookup bs :staging ".stage-1"))
        (not (fn-bs-lookup bs :transactions "00000000000000000000.txn"))
        (fn-bsfk-link-conclusion bs *fn-bsfk-bad-record-state* ".stage-1"
                                  "00000000000000000000.txn" (cons :eio :issued))))))
(must-fail (assert-event
 (let* ((pair (nth 5 *fn-bsfk-record-run*)) (bs (car pair)) (ks (cdr pair)))
   (and (fn-sf-statep ks) (not (equal (fn-sf-phase ks) :record-data-durable))
        (fn-bs-inop (fn-bs-lookup bs :staging ".stage-1"))
        (not (fn-bs-lookup bs :transactions "00000000000000000000.txn"))
        (fn-bsfk-link-conclusion bs ks ".stage-1"
                                  "00000000000000000000.txn" (cons :eio :issued))))))
(must-fail (assert-event
 (let* ((pair (nth 6 *fn-bsfk-record-run*)) (bs (car pair)) (ks (cdr pair)))
   (and (not (fn-bs-inop (fn-bs-lookup bs :staging ".missing")))
        (fn-bsfk-link-conclusion bs ks ".missing"
                                  "00000000000000000000.txn" (cons :eio :issued))))))
(must-fail (assert-event
 (let* ((pair (nth 7 *fn-bsfk-record-run*)) (bs (car pair)) (ks (cdr pair)))
   (and (fn-bs-lookup bs :transactions "00000000000000000000.txn")
        (fn-bsfk-link-conclusion bs ks ".stage-1"
                                  "00000000000000000000.txn" (cons :eio :issued))))))
(must-fail (assert-event
 (let* ((pair (nth 6 *fn-bsfk-record-run*)) (bs (car pair)) (ks (cdr pair)))
   (and (not (equal (cdr (cons :eio :not-issued)) :issued))
        (fn-bsfk-link-conclusion bs ks ".stage-1"
                                  "00000000000000000000.txn"
                                  (cons :eio :not-issued))))))

; Reachable non-degenerate witness at record-linked: one pending final-name
; operation, an uncertain kernel phase, and recovery's directory fence drains
; the exact operation.
(assert-event
 (let* ((pair (nth 8 *fn-bsfk-record-run*))
        (bs (car pair))
        (ks (cdr pair)))
   (and (equal (fn-sf-phase ks) :record-data-durable)
        (not (fn-bs-dir-quietp bs :transactions))
        (fn-sf-fencedp (fn-sf-record-link-result ks :error))
        (fn-bs-dir-quietp (fn-bs-fence-dir bs :transactions) :transactions))))

; Without an issued operation there is nothing for recovery to drain.
(must-fail
 (assert-event
  (mv-let (result bs)
    (fn-bs-link (car (nth 6 *fn-bsfk-record-run*)) :staging ".stage-1"
                :transactions "00000000000000000000.txn"
                (cons :eio :not-issued))
    (declare (ignore result))
    (not (fn-bs-dir-quietp bs :transactions)))))

; Reachable allocator witness after rename: both the :root replacement and
; staging deletion are pending, while fencing :root drains exactly the former.
(assert-event
 (let* ((pair (nth 8 *fn-bsfk-frontier-run*))
        (bs (car pair))
        (ks (cdr pair)))
   (and (equal (fn-sf-phase ks) :frontier-data-durable)
        (not (fn-bs-dir-quietp bs :root))
        (fn-sf-fencedp (fn-sf-frontier-replace-result ks :error))
        (fn-bs-dir-quietp (fn-bs-fence-dir bs :root) :root)
        (not (fn-bs-dir-quietp (fn-bs-fence-dir bs :root) :staging)))))

; A failure reported before rename was issued leaves :root quiet.
(must-fail
 (assert-event
  (mv-let (result bs)
    (fn-bs-rename (car (nth 7 *fn-bsfk-frontier-run*))
                  :staging ".allocation-1" :root
                  *fn-bs-frontier-name* (cons :eio :not-issued))
    (declare (ignore result))
    (not (fn-bs-dir-quietp bs :root)))))

; The reachable record-attempted state has one unresolved transaction entry.
; Any error result resolves that physical choice and fences the kernel.
(assert-event
 (let* ((pair (nth 10 *fn-bsfk-record-run*))
        (bs (car pair))
        (ks (cdr pair)))
   (mv-let (result bs1)
     (fn-bs-fsync-dir bs :transactions (cons :eio '(:drop)))
     (and (equal result :eio)
          (equal (fn-sf-phase ks) :record-attempted)
          (fn-bs-dir-quietp bs1 :transactions)
          (fn-sf-fencedp (fn-sf-record-dir-result ks :error))))))

; Fencing the unrelated staging directory cannot resolve the authority choice.
(must-fail
 (assert-event
  (let* ((pair (nth 10 *fn-bsfk-record-run*))
         (bs (car pair)))
    (mv-let (result bs1)
      (fn-bs-fsync-dir bs :staging (cons :eio '(:drop)))
      (declare (ignore result))
      (fn-bs-dir-quietp bs1 :transactions)))))

(assert-event
 (let* ((pair (nth 10 *fn-bsfk-frontier-run*))
        (bs (car pair))
        (ks (cdr pair)))
   (mv-let (result bs1)
     (fn-bs-fsync-dir bs :root (cons :eio '(:apply :drop)))
     (and (equal result :eio)
          (equal (fn-sf-phase ks) :frontier-attempted)
          (fn-bs-dir-quietp bs1 :root)
          (fn-sf-fencedp (fn-sf-frontier-dir-result ks :error))))))

(must-fail
 (assert-event
  (let* ((pair (nth 10 *fn-bsfk-frontier-run*))
         (bs (car pair)))
    (mv-let (result bs1)
      (fn-bs-fsync-dir bs :transactions (cons :eio nil))
      (declare (ignore result))
      (fn-bs-dir-quietp bs1 :root)))))

; Full issued-rename fact and one counterexample per essential hypothesis.
(assert-event
 (let* ((pair (nth 7 *fn-bsfk-frontier-run*))
        (bs (car pair)) (ks (cdr pair)) (outcome (cons :eio :issued)))
   (and (fn-sf-statep ks)
        (equal (fn-sf-phase ks) :frontier-data-durable)
        (fn-bs-inop (fn-bs-lookup bs :staging ".allocation-1"))
        (equal (cdr outcome) :issued)
        (fn-bsfk-rename-conclusion bs ks ".allocation-1" outcome))))
(must-fail (assert-event
 (let* ((pair (nth 7 *fn-bsfk-frontier-run*)) (bs (car pair)))
   (and (not (fn-sf-statep *fn-bsfk-bad-frontier-state*))
        (fn-bsfk-rename-conclusion bs *fn-bsfk-bad-frontier-state*
                                    ".allocation-1" (cons :eio :issued))))))
(must-fail (assert-event
 (let* ((pair (nth 5 *fn-bsfk-frontier-run*)) (bs (car pair)) (ks (cdr pair)))
   (and (not (equal (fn-sf-phase ks) :frontier-data-durable))
        (fn-bsfk-rename-conclusion bs ks ".allocation-1" (cons :eio :issued))))))
(must-fail (assert-event
 (let* ((pair (nth 7 *fn-bsfk-frontier-run*)) (bs (car pair)) (ks (cdr pair)))
   (and (not (fn-bs-inop (fn-bs-lookup bs :staging ".missing")))
        (fn-bsfk-rename-conclusion bs ks ".missing" (cons :eio :issued))))))
(must-fail (assert-event
 (let* ((pair (nth 7 *fn-bsfk-frontier-run*)) (bs (car pair)) (ks (cdr pair)))
   (and (not (equal (cdr (cons :eio :not-issued)) :issued))
        (fn-bsfk-rename-conclusion bs ks ".allocation-1"
                                    (cons :eio :not-issued))))))

; Full barrier-error facts.  Invalid same-phase kernels show statep is
; essential; pre-barrier phases show the phase premise is essential; an atom
; error outcome cannot supply the reported errno selected by the theorem.
(assert-event
 (let* ((pair (nth 10 *fn-bsfk-record-run*))
        (bs (car pair)) (ks (cdr pair)) (outcome (cons :eio '(:drop))))
   (and (fn-sf-statep ks) (equal (fn-sf-phase ks) :record-attempted)
        (consp outcome) (fn-bsfk-dir-conclusion bs ks :transactions outcome))))
(must-fail (assert-event
 (let* ((pair (nth 10 *fn-bsfk-record-run*)) (bs (car pair)))
   (and (not (fn-sf-statep *fn-bsfk-bad-record-attempted-state*))
        (fn-bsfk-dir-conclusion bs *fn-bsfk-bad-record-attempted-state*
                                 :transactions (cons :eio '(:drop)))))))
(must-fail (assert-event
 (let* ((pair (nth 8 *fn-bsfk-record-run*)) (bs (car pair)) (ks (cdr pair)))
   (and (not (equal (fn-sf-phase ks) :record-attempted))
        (fn-bsfk-dir-conclusion bs ks :transactions (cons :eio '(:drop)))))))
(must-fail (assert-event
 (let* ((pair (nth 10 *fn-bsfk-record-run*)) (bs (car pair)) (ks (cdr pair)))
   (and (not (consp :eio)) (fn-bsfk-dir-conclusion bs ks :transactions :eio)))))

(assert-event
 (let* ((pair (nth 10 *fn-bsfk-frontier-run*))
        (bs (car pair)) (ks (cdr pair)) (outcome (cons :eio '(:apply :drop))))
   (and (fn-sf-statep ks) (equal (fn-sf-phase ks) :frontier-attempted)
        (consp outcome) (fn-bsfk-dir-conclusion bs ks :root outcome))))
(must-fail (assert-event
 (let* ((pair (nth 10 *fn-bsfk-frontier-run*)) (bs (car pair)))
   (and (not (fn-sf-statep *fn-bsfk-bad-frontier-attempted-state*))
        (fn-bsfk-dir-conclusion bs *fn-bsfk-bad-frontier-attempted-state*
                                 :root (cons :eio '(:apply :drop)))))))
(must-fail (assert-event
 (let* ((pair (nth 8 *fn-bsfk-frontier-run*)) (bs (car pair)) (ks (cdr pair)))
   (and (not (equal (fn-sf-phase ks) :frontier-attempted))
        (fn-bsfk-dir-conclusion bs ks :root (cons :eio '(:apply :drop)))))))
(must-fail (assert-event
 (let* ((pair (nth 10 *fn-bsfk-frontier-run*)) (bs (car pair)) (ks (cdr pair)))
   (and (not (consp :eio)) (fn-bsfk-dir-conclusion bs ks :root :eio)))))
