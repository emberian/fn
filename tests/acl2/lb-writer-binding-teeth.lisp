; A1 withdrawal teeth: whole two-row positive, both removals, real held-payload release fault.
(in-package "ACL2")
(include-book "lb-writer-binding-logical-witnesses")
(include-book "../../books/defkeystone")

(defthm fn-lbw-swapped-arena-is-two-real-seals
 (equal (fn-lbw-arena-swapped (create-fn-arena))
        (list *fn-lbw-payload-b* *fn-lbw-payload-b*))
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbw-arena-swapped fn-arena-clear-is-nil fn-arena-seal-list-is-append
 fn-arena-p (:executable-counterpart fn-arena$ap) create-fn-arena)))))

(defthm fn-lbw-withdraw-positive-flat
 (and (fn-lb-arena-is-log (fn-lbw-arena-good (create-fn-arena)) (fn-lbw-two-rows) (fn-lbw-two-log)) (natp 0) (fn-lb-arena-is-log (fn-lbw-arena-good (create-fn-arena)) (fn-cat-withdraw 0 1 (fn-lbw-two-rows)) (fn-lbw-two-log)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbw-withdraw-whole-positive))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbw-good-arena-is-two-real-seals fn-lbw-swapped-arena-is-two-real-seals
 fn-lb-arena-is-log fn-cat-withdraw fn-nntp-payload-bytes fn-arena-count-is-len
 fn-arena-payload-is-nth fn-arena-forget fn-arena$a-forget
 (:executable-counterpart fn-arena$a-forget)
 (:executable-counterpart fn-lbw-two-rows) (:executable-counterpart fn-lbw-two-log)
 (:executable-counterpart fn-cat$a-withdraw) (:executable-counterpart fn-record-payload)
 (:executable-counterpart fn-lb-log-payload))))))

(defthm fn-lbw-withdraw-binding-removal
 (and (natp 0) (not (fn-lb-arena-is-log (fn-lbw-arena-swapped (create-fn-arena)) (fn-lbw-two-rows) (fn-lbw-two-log))) (not (fn-lb-arena-is-log (fn-lbw-arena-swapped (create-fn-arena)) (fn-cat-withdraw 0 1 (fn-lbw-two-rows)) (fn-lbw-two-log))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbw-good-arena-is-two-real-seals fn-lbw-swapped-arena-is-two-real-seals
 fn-lb-arena-is-log fn-cat-withdraw fn-nntp-payload-bytes fn-arena-count-is-len
 fn-arena-payload-is-nth fn-arena-forget fn-arena$a-forget
 (:executable-counterpart fn-arena$a-forget)
 (:executable-counterpart fn-lbw-two-rows) (:executable-counterpart fn-lbw-two-log)
 (:executable-counterpart fn-cat$a-withdraw) (:executable-counterpart fn-record-payload)
 (:executable-counterpart fn-lb-log-payload))))))

(defthm fn-lbw-withdraw-target-removal-flat
 (and (fn-lb-arena-is-log (create-fn-arena) nil '((1 nil ((0 0 0 0 0 nil (9) nil nil))))) (not (natp -1)) (not (fn-lb-arena-is-log (create-fn-arena) (fn-cat-withdraw -1 0 nil) '((1 nil ((0 0 0 0 0 nil (9) nil nil)))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbw-withdraw-natural-target-removal))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbw-good-arena-is-two-real-seals fn-lbw-swapped-arena-is-two-real-seals
 fn-lb-arena-is-log fn-cat-withdraw fn-nntp-payload-bytes fn-arena-count-is-len
 fn-arena-payload-is-nth fn-arena-forget fn-arena$a-forget
 (:executable-counterpart fn-arena$a-forget)
 (:executable-counterpart fn-lbw-two-rows) (:executable-counterpart fn-lbw-two-log)
 (:executable-counterpart fn-cat$a-withdraw) (:executable-counterpart fn-record-payload)
 (:executable-counterpart fn-lb-log-payload))))))

(defthm fn-lbw-withdraw-release-fault
 (and (fn-lb-arena-is-log (fn-lbw-arena-good (create-fn-arena)) (fn-lbw-two-rows) (fn-lbw-two-log)) (natp 0) (fn-lb-arena-is-log (fn-lbw-arena-good (create-fn-arena)) (fn-cat-withdraw 0 1 (fn-lbw-two-rows)) (fn-lbw-two-log)) (not (fn-lb-arena-is-log (fn-arena-forget 0 (fn-lbw-arena-good (create-fn-arena))) (fn-cat-withdraw 0 1 (fn-lbw-two-rows)) (fn-lbw-two-log))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbw-withdraw-whole-positive))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbw-good-arena-is-two-real-seals fn-lbw-swapped-arena-is-two-real-seals
 fn-lb-arena-is-log fn-cat-withdraw fn-nntp-payload-bytes fn-arena-count-is-len
 fn-arena-payload-is-nth fn-arena-forget fn-arena$a-forget
 (:executable-counterpart fn-arena$a-forget)
 (:executable-counterpart fn-lbw-two-rows) (:executable-counterpart fn-lbw-two-log)
 (:executable-counterpart fn-cat$a-withdraw) (:executable-counterpart fn-record-payload)
 (:executable-counterpart fn-lb-log-payload))))))


(defun fn-lbw-teeth-arena (mode fn-arena)
 (declare (xargs :stobjs fn-arena :guard t))
 (cond ((equal mode :swapped) (fn-lbw-arena-swapped fn-arena))
       ((equal mode :empty) (fn-arena-clear fn-arena))
       (t (fn-lbw-arena-good fn-arena))))
(defun fn-lbw-withdraw-scalar (target by rows log fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil))
 (mv (fn-lb-arena-is-log fn-arena (fn-cat$a-withdraw target by rows) log) fn-arena))
(defun fn-lbw-withdraw-forget-scalar (target by rows log fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil))
 (let ((fn-arena (fn-arena-forget 0 fn-arena)))
  (mv (fn-lb-arena-is-log fn-arena (fn-cat$a-withdraw target by rows) log) fn-arena)))

(defteeth fn-lb-arena-is-log-of-withdraw
 :claim (((binding (fn-lb-arena-is-log fn-arena rows log)) (target (natp target)))
         (fn-lb-arena-is-log fn-arena (fn-cat-withdraw target by rows) log))
 :subject fn-cat-withdraw
 :witness ((arena-mode :good) (rows (fn-lbw-two-rows)) (log (fn-lbw-two-log)) (target 0) (by 1))
 :stobjs ((fn-arena (fn-lbw-teeth-arena arena-mode fn-arena)))
 :stobj-checks
 (((fn-lb-arena-is-log fn-arena (fn-cat-withdraw target by rows) log)
   (fn-lbw-withdraw-scalar target by rows log fn-arena)
   :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
     '(fn-lbw-withdraw-scalar fn-cat-withdraw)))))
  ((fn-lb-arena-is-log (fn-arena-forget 0 fn-arena) (fn-cat-withdraw target by rows) log)
   (fn-lbw-withdraw-forget-scalar target by rows log fn-arena)
   :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
     '(fn-lbw-withdraw-forget-scalar fn-cat-withdraw))))))
 :breaks ((binding ((arena-mode :swapped)))
          (target ((arena-mode :empty) (rows nil)
                   (log '((1 nil ((0 0 0 0 0 nil (9) nil nil))))) (target -1) (by 0))
                   :logical "negative target and malformed log are outside the writer guard"))
 :mutations ((release-held-payload
              (:conclusion (fn-lb-arena-is-log (fn-arena-forget 0 fn-arena)
                             (fn-cat-withdraw target by rows) log))
              ((arena-mode :good) (rows (fn-lbw-two-rows)) (log (fn-lbw-two-log)) (target 0) (by 1))
              :fault "withdrawal releases a still-held payload handle"))
 :hints (("Goal" :do-not-induct t
   :use ((:instance fn-lbw-withdraw-target-removal-flat))
   :in-theory (union-theories (theory 'ground-zero)
     '(fn-lbw-teeth-arena fn-arena-clear-is-nil create-fn-arena)))))

(defthm fn-lbw-redecide-natural-removal
 (and (fn-lb-arena-is-log (create-fn-arena) nil '((1 nil ((0 0 0 0 0 nil (9) nil nil)))))
      (< -1 (len nil)) (not (natp -1))
      (not (fn-lb-arena-is-log (create-fn-arena)
             (fn-cat-redecide -1 nil nil) '((1 nil ((0 0 0 0 0 nil (9) nil nil)))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-arena-is-log fn-cat-redecide fn-nntp-payload-bytes
 (:executable-counterpart fn-cat$a-redecide) (:executable-counterpart fn-record-payload)
 (:executable-counterpart fn-lb-log-payload))))))

(defthm fn-lbw-redecide-bound-removal
 (and (fn-lb-arena-is-log (create-fn-arena) nil '((1 nil ((0 0 0 0 0 nil (9) nil nil)))))
      (natp 0) (not (< 0 (len nil)))
      (not (fn-lb-arena-is-log (create-fn-arena)
             (fn-cat-redecide 0 nil nil) '((1 nil ((0 0 0 0 0 nil (9) nil nil)))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-arena-is-log fn-cat-redecide fn-nntp-payload-bytes
 (:executable-counterpart fn-cat$a-redecide) (:executable-counterpart fn-record-payload)
 (:executable-counterpart fn-lb-log-payload))))))

(defun fn-lbw-redecide-scalar (seq context rows log fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil))
 (mv (fn-lb-arena-is-log fn-arena (fn-cat$a-redecide seq context rows) log) fn-arena))
(defun fn-lbw-redecide-forget-scalar (seq context rows log fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil))
 (let ((fn-arena (fn-arena-forget 0 fn-arena)))
  (mv (fn-lb-arena-is-log fn-arena (fn-cat$a-redecide seq context rows) log) fn-arena)))
(defteeth fn-lb-arena-is-log-of-redecide
 :claim (((binding (fn-lb-arena-is-log fn-arena rows log)) (natural (natp seq))
          (bound (< seq (len rows))))
         (fn-lb-arena-is-log fn-arena (fn-cat-redecide seq context rows) log))
 :subject fn-cat-redecide
 :witness ((arena-mode :good) (rows (fn-lbw-two-rows)) (log (fn-lbw-two-log))
           (seq 0) (context (fn-held-context (fn-lbr13-held))))
 :stobjs ((fn-arena (fn-lbw-teeth-arena arena-mode fn-arena)))
 :stobj-checks
 (((fn-lb-arena-is-log fn-arena (fn-cat-redecide seq context rows) log)
   (fn-lbw-redecide-scalar seq context rows log fn-arena)
   :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
     '(fn-lbw-redecide-scalar fn-cat-redecide)))))
  ((fn-lb-arena-is-log (fn-arena-forget 0 fn-arena) (fn-cat-redecide seq context rows) log)
   (fn-lbw-redecide-forget-scalar seq context rows log fn-arena)
   :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
     '(fn-lbw-redecide-forget-scalar fn-cat-redecide))))))
 :breaks ((binding ((arena-mode :swapped)))
          (natural ((arena-mode :empty) (rows nil) (seq -1) (context nil)
                    (log '((1 nil ((0 0 0 0 0 nil (9) nil nil))))))
                    :logical "negative sequence is outside the redecision guard")
          (bound ((arena-mode :empty) (rows nil) (seq 0) (context nil)
                  (log '((1 nil ((0 0 0 0 0 nil (9) nil nil))))))
                  :logical "out-of-bounds sequence is outside the redecision guard"))
 :mutations ((release-held-payload
              (:conclusion (fn-lb-arena-is-log (fn-arena-forget 0 fn-arena)
                             (fn-cat-redecide seq context rows) log))
              ((arena-mode :good) (rows (fn-lbw-two-rows)) (log (fn-lbw-two-log))
               (seq 0) (context (fn-held-context (fn-lbr13-held))))
              :fault "redecision releases a still-held payload handle"))
 :hints (("Goal" :do-not-induct t
   :use ((:instance fn-lbw-redecide-natural-removal)
         (:instance fn-lbw-redecide-bound-removal))
   :in-theory (union-theories (theory 'ground-zero)
     '(fn-lbw-teeth-arena fn-arena-clear-is-nil create-fn-arena)))))

; Commit's remaining four premises are independent; type-only premises were proved redundant.
(defun fn-lbw-future-rows ()
 (declare (xargs :guard t :verify-guards nil))
 (fn-cat$a-commit (update-nth 4 2 (fn-lbr13-held)) nil))
(defun fn-lbw-future-log ()
 (declare (xargs :guard t :verify-guards nil))
 (fn-lb-log-model-append (car (fn-lbw-future-rows)) nil 1 nil))
(defun fn-lbw-reused-handle ()
 (declare (xargs :guard t :verify-guards nil))
 (update-nth 4 0 (fn-lbw-incoming-held)))
(defun fn-lbw-stale-commit-log ()
 (declare (xargs :guard t :verify-guards nil))
 (fn-lb-log-model-append (fn-lbw-incoming-held) *fn-lbr13-payload* 1 (fn-lbw-two-log)))
(defun fn-lbw-commit-scalar (h rows log payload target fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil))
 (let* ((log2 (fn-lb-log-model-append (fn-cat-assign h rows) payload target log))
        (fn-arena (fn-arena-seal-list payload fn-arena)))
  (mv (fn-lb-arena-is-log fn-arena (fn-cat$a-commit h rows) log2) fn-arena)))
(defun fn-lbw-commit-missing-append-scalar (h rows log payload fn-arena)
 (declare (xargs :stobjs fn-arena :verify-guards nil))
 (let ((fn-arena (fn-arena-seal-list payload fn-arena)))
  (mv (fn-lb-arena-is-log fn-arena (fn-cat$a-commit h rows) log) fn-arena)))
(defteeth fn-lb-arena-is-log-of-commit
 :claim (((binding (fn-lb-arena-is-log fn-arena rows log))
          (old-handles (fn-scol-handles-below rows (fn-arena-count fn-arena)))
          (new-handle (equal (fn-record-payload h) (fn-arena-count fn-arena)))
          (fresh-key (not (fn-lb-log-model-row-entry h log))))
         (let* ((arena (fn-arena-seal-list payload fn-arena))
                (log2 (fn-lb-log-model-append (fn-cat-assign h rows) payload target log)))
          (fn-lb-arena-is-log arena (fn-cat-commit h rows) log2)))
 :subject fn-cat-commit
 :witness ((arena-mode :good) (h (fn-lbw-incoming-held)) (rows (fn-lbw-two-rows))
           (log (fn-lbw-two-log)) (payload *fn-lbw-payload-b*) (target 1))
 :stobjs ((fn-arena (fn-lbw-teeth-arena arena-mode fn-arena)))
 :stobj-checks
 (((let* ((arena (fn-arena-seal-list payload fn-arena))
          (log2 (fn-lb-log-model-append (fn-cat-assign h rows) payload target log)))
    (fn-lb-arena-is-log arena (fn-cat-commit h rows) log2))
   (fn-lbw-commit-scalar h rows log payload target fn-arena)
   :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
     '(fn-lbw-commit-scalar fn-cat-commit)))))
  ((fn-lb-arena-is-log (fn-arena-seal-list payload fn-arena) (fn-cat-commit h rows) log)
   (fn-lbw-commit-missing-append-scalar h rows log payload fn-arena)
   :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
     '(fn-lbw-commit-missing-append-scalar fn-cat-commit))))))
 :breaks ((binding ((arena-mode :swapped)))
          (old-handles ((rows (fn-lbw-future-rows)) (log (fn-lbw-future-log))))
          (new-handle ((h (fn-lbw-reused-handle))))
          (fresh-key ((log (fn-lbw-stale-commit-log)))))
 :mutations ((missing-log-append
              (:conclusion (fn-lb-arena-is-log (fn-arena-seal-list payload fn-arena)
                             (fn-cat-commit h rows) log))
              ((arena-mode :good) (h (fn-lbw-incoming-held)) (rows (fn-lbw-two-rows))
               (log (fn-lbw-two-log)) (payload *fn-lbw-payload-b*) (target 1))
              :fault "sealed acceptance updates the catalog without appending its log record")))

; The allocation invariant replaces the fresh-key premise; every other claim term is identical.
(defteeth fn-lb-arena-is-log-of-allocated-commit
 :claim (((binding (fn-lb-arena-is-log fn-arena rows log))
          (old-handles (fn-scol-handles-below rows (fn-arena-count fn-arena)))
          (new-handle (equal (fn-record-payload h) (fn-arena-count fn-arena)))
          (allocated-log (fn-lb-log-handles-below log (fn-arena-count fn-arena))))
         (let* ((arena (fn-arena-seal-list payload fn-arena))
                (log2 (fn-lb-log-model-append (fn-cat-assign h rows) payload target log)))
          (fn-lb-arena-is-log arena (fn-cat-commit h rows) log2)))
 :subject fn-cat-commit
 :witness ((arena-mode :good) (h (fn-lbw-incoming-held)) (rows (fn-lbw-two-rows))
           (log (fn-lbw-two-log)) (payload *fn-lbw-payload-b*) (target 1))
 :stobjs ((fn-arena (fn-lbw-teeth-arena arena-mode fn-arena)))
 :stobj-checks
 (((let* ((arena (fn-arena-seal-list payload fn-arena))
          (log2 (fn-lb-log-model-append (fn-cat-assign h rows) payload target log)))
    (fn-lb-arena-is-log arena (fn-cat-commit h rows) log2))
   (fn-lbw-commit-scalar h rows log payload target fn-arena)
   :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
     '(fn-lbw-commit-scalar fn-cat-commit)))))
  ((fn-lb-arena-is-log (fn-arena-seal-list payload fn-arena) (fn-cat-commit h rows) log)
   (fn-lbw-commit-missing-append-scalar h rows log payload fn-arena)
   :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
     '(fn-lbw-commit-missing-append-scalar fn-cat-commit))))))
 :breaks ((binding ((arena-mode :swapped)))
          (old-handles ((rows (fn-lbw-future-rows)) (log nil)))
          (new-handle ((h (fn-lbw-reused-handle))))
          (allocated-log ((log (fn-lbw-stale-commit-log)))))
 :mutations ((missing-log-append
              (:conclusion (fn-lb-arena-is-log (fn-arena-seal-list payload fn-arena)
                             (fn-cat-commit h rows) log))
              ((arena-mode :good) (h (fn-lbw-incoming-held)) (rows (fn-lbw-two-rows))
               (log (fn-lbw-two-log)) (payload *fn-lbw-payload-b*) (target 1))
              :fault "sealed acceptance updates the catalog without appending its log record")))
