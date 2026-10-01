; Teeth for books/byte-store-state-checkpoint-program and
; books/byte-store-range-read.
(in-package "ACL2")
(include-book "must-fail-checked")
(include-book "../../books/byte-store-state-checkpoint-program")
(include-book "../../books/byte-store-range-read")

; fn-bs-scp-program-crash-is-old-or-new, a reachable run: a quiet store with
; an old checkpoint at inode 3, next inode 5.
(defconst *scp-t-bs*
  (fn-bs-make 4 (list (cons 3 '(7 7)))
              (list (cons :root (list (cons "store-checkpoint.fnsc" 3)))
                    (cons :staging nil))
              nil 5))
(defconst *scp-t-run*
  (fn-bs-run *scp-t-bs* nil (fn-bs-scp-program ".stage-state-checkpoint-1" '(1 2 3))
             nil nil 0))
(assert-event (fn-bs-scp-inputp *scp-t-bs* ".stage-state-checkpoint-1" 3))
(assert-event (equal (len *scp-t-run*) 10))
(defconst *scp-t-renamed* (car (nth 7 *scp-t-run*)))
(assert-event (equal (fn-bs-durable-entry (fn-bs-crash *scp-t-renamed* '(:drop :drop :drop))
                                          :root "store-checkpoint.fnsc")
                     3))
(assert-event (equal (fn-bs-durable-entry (fn-bs-crash *scp-t-renamed* '(:drop :apply :drop))
                                          :root "store-checkpoint.fnsc")
                     5))
(assert-event (fn-bs-scp-old-or-newp
               (fn-bs-crash *scp-t-renamed* '(:drop :drop :drop)) *scp-t-bs* 3 '(1 2 3)))
(assert-event (fn-bs-scp-old-or-newp
               (fn-bs-crash *scp-t-renamed* '(:drop :apply :drop)) *scp-t-bs* 3 '(1 2 3)))
; The first publish: no old checkpoint, the name is absent or new.
(defconst *scp-t-fresh*
  (fn-bs-make 4 (list (cons 3 '(7 7)))
              (list (cons :root nil) (cons :staging nil))
              nil 5))
(assert-event (fn-bs-scp-inputp *scp-t-fresh* ".stage-state-checkpoint-1" nil))
(defconst *scp-t-fresh-run*
  (fn-bs-run *scp-t-fresh* nil (fn-bs-scp-program ".stage-state-checkpoint-1" '(1 2 3))
             nil nil 0))
(assert-event (fn-bs-scp-old-or-newp
               (fn-bs-crash (car (nth 7 *scp-t-fresh-run*)) '(:drop :drop :drop))
               *scp-t-fresh* nil '(1 2 3)))
; Without a quiet store (a pending write to the old inode), a crash image
; holds a third content.
(defconst *scp-t-busy*
  (fn-bs-make 4 (list (cons 3 '(7 7)))
              (list (cons :root (list (cons "store-checkpoint.fnsc" 3)))
                    (cons :staging nil))
              (list (list :write 3 0 '(9 9)))
              5))
(defconst *scp-t-busy-run*
  (fn-bs-run *scp-t-busy* nil (fn-bs-scp-program ".stage-state-checkpoint-1" '(1 2 3))
             nil nil 0))
(must-fail-checked
 (defthm scp-t-crash-without-quiet-store
   (fn-bs-scp-old-or-newp (fn-bs-crash (car (nth 0 *scp-t-busy-run*)) '((:new) :drop))
                          *scp-t-busy* 3 '(1 2 3))))

; fn-bs-read-ranges-concatenate: two ranges of inode 3 read in one state are
; the one range.  Without A-HOST-EXCLUSIVE-READ (a later state whose inode 3
; holds other octets) the second range comes from other content.
(defconst *scp-t-file*
  (fn-bs-make 4 (list (cons 3 '(1 2 3 4 5 6)))
              (list (cons :root (list (cons "store-checkpoint.fnsc" 3))))
              nil 5))
(defconst *scp-t-changed*
  (fn-bs-make 4 (list (cons 3 '(1 2 3 9 9 9)))
              (list (cons :root (list (cons "store-checkpoint.fnsc" 3))))
              nil 5))
(assert-event (equal (append (fn-bs-read-range *scp-t-file* 3 0 2)
                             (fn-bs-read-range *scp-t-file* 3 2 4))
                     (fn-bs-read-range *scp-t-file* 3 0 6)))
(assert-event (equal (append (fn-bs-read-range *scp-t-file* 3 0 2)
                             (fn-bs-read-range *scp-t-file* 3 2 4))
                     (fn-bs-read *scp-t-file* 3)))
(assert-event (not (equal (append (fn-bs-read-range *scp-t-file* 3 0 2)
                                  (fn-bs-read-range *scp-t-changed* 3 2 4))
                          (fn-bs-read-range *scp-t-file* 3 0 6))))
(must-fail-checked
 (defthm scp-t-ranges-without-exclusive-read
   (implies (and (natp off) (natp n) (natp m)
                 (<= (+ off n) (len (fn-bs-content s0 ino))))
            (equal (append (fn-bs-read-range s0 ino off n)
                           (fn-bs-read-range s1 ino (+ off n) m))
                   (fn-bs-read-range s0 ino off (+ n m))))
   :hints (("Goal" :do-not-induct t))))

; -----------------------------------------------------------------------------
; The batched program (PRF-1223): the same quiet store, the file in three
; batches.  Every state of the run, the batch states included, crashes to
; the old checkpoint or the new one under the lose-everything and the
; land-everything choices; before the rename the entry is the old inode at
; every state.  Labelled MUTANT: the batches written at offset 0 each (the
; running offset dropped) crash to a third content at the durable state.
(defconst *scp-t-chunks* '((1 2) (3) (4 5 6)))
(defconst *scp-t-batched-run*
  (fn-bs-run *scp-t-bs* nil (fn-bs-scp-batched-program ".stage-state-checkpoint-1" *scp-t-chunks*)
             nil nil 0))
(assert-event (equal (len *scp-t-batched-run*) 15))
; Choices follow each state's pending operations, including every touched
; write unit.  LANDP selects land-everything; nil selects lose-everything.
(defun scp-t-crash-choices (ops unit landp)
  (if (consp ops)
      (cons (if (equal (car (car ops)) :write)
                (if landp
                    (make-list-ac (fn-bs-unit-count (nth 2 (car ops))
                                              (len (nth 3 (car ops))) unit)
                                  :new nil)
                  nil)
              (if landp :apply :drop))
            (scp-t-crash-choices (cdr ops) unit landp))
    nil))
(defun scp-t-all-choices-admissible (pairs landp)
  (if (consp pairs)
      (let* ((bs (car (car pairs)))
             (ops (fn-bs-pending bs)) (unit (fn-bs-unit bs)))
        (and (fn-bs-crash-choicesp (scp-t-crash-choices ops unit landp) ops unit)
             (scp-t-all-choices-admissible (cdr pairs) landp)))
    t))
(defun scp-t-all-old-or-new (pairs bs old-ino octets landp)
  (if (consp pairs)
      (let* ((s (car (car pairs)))
             (choices (scp-t-crash-choices (fn-bs-pending s) (fn-bs-unit s) landp)))
        (and (fn-bs-scp-old-or-newp (fn-bs-crash s choices) bs old-ino octets)
             (scp-t-all-old-or-new (cdr pairs) bs old-ino octets landp)))
    t))
(defun scp-t-all-entry (pairs landp entry)
  (if (consp pairs)
      (let* ((s (car (car pairs)))
             (choices (scp-t-crash-choices (fn-bs-pending s) (fn-bs-unit s) landp)))
        (and (equal (fn-bs-durable-entry (fn-bs-crash s choices)
                                         :root "store-checkpoint.fnsc")
                    entry)
             (scp-t-all-entry (cdr pairs) landp entry)))
    t))
(assert-event (and (scp-t-all-choices-admissible *scp-t-batched-run* nil)
                   (scp-t-all-choices-admissible *scp-t-batched-run* t)))
(assert-event (scp-t-all-old-or-new *scp-t-batched-run* *scp-t-bs* 3 '(1 2 3 4 5 6) nil))
(assert-event (scp-t-all-old-or-new *scp-t-batched-run* *scp-t-bs* 3 '(1 2 3 4 5 6) t))
; the eleven states before the rename: the old entry under both vectors
(assert-event (and (scp-t-all-entry (take 11 *scp-t-batched-run*) nil 3)
                   (scp-t-all-entry (take 11 *scp-t-batched-run*) t 3)))
; After the last batch, before file fsync: landing really writes the bytes.
(defconst *scp-t-unfenced* (car (nth 8 *scp-t-batched-run*)))
(assert-event (equal (fn-bs-durable-content *scp-t-unfenced* 5) nil))
(assert-event
 (equal (fn-bs-durable-content
         (fn-bs-crash *scp-t-unfenced*
                      (scp-t-crash-choices (fn-bs-pending *scp-t-unfenced*)
                                           (fn-bs-unit *scp-t-unfenced*) t))
         5)
        '(1 2 3 4 5 6)))
; the durable state: the new inode holds exactly the batches
(assert-event (equal (fn-bs-durable-content (car (nth 14 *scp-t-batched-run*)) 5) '(1 2 3 4 5 6)))
; MUTANT: every batch at offset 0
(defun scp-t-write-steps-at-zero (stage chunks)
  (if (consp chunks)
      (list* (list :write-at :staging stage 0 (car chunks))
             (list :cut "state-checkpoint-batch")
             (scp-t-write-steps-at-zero stage (cdr chunks)))
    nil))
(defconst *scp-t-mutant-run*
  (fn-bs-run *scp-t-bs* nil
             (append (list (list :create :staging ".stage-state-checkpoint-1")
                           (list :cut "state-checkpoint-created"))
                     (scp-t-write-steps-at-zero ".stage-state-checkpoint-1" *scp-t-chunks*)
                     (list (list :cut "state-checkpoint-written")
                           (list :fsync-file :staging ".stage-state-checkpoint-1")
                           (list :cut "state-checkpoint-staged-durable")
                           (list :rename :staging ".stage-state-checkpoint-1" :root "store-checkpoint.fnsc")
                           (list :cut "state-checkpoint-replaced")
                           (list :fsync-dir :root)
                           (list :cut "state-checkpoint-durable")))
             nil nil 0))
(assert-event (and (scp-t-all-choices-admissible *scp-t-mutant-run* nil)
                   (scp-t-all-choices-admissible *scp-t-mutant-run* t)))
(assert-event (not (scp-t-all-old-or-new *scp-t-mutant-run* *scp-t-bs* 3 '(1 2 3 4 5 6) nil)))
(assert-event (not (scp-t-all-old-or-new *scp-t-mutant-run* *scp-t-bs* 3 '(1 2 3 4 5 6) t)))

; MUTANT (r22 Q4), mutation witness: zeroing a positive :write-at offset
; only on a non-:ok outcome must fail the content check.  The real step
; accepts (3) at offset 2, reports :eio, and stops before any later batch
; or fsync.  The offset-zero mutant instead leaves the view (3 2).
(defconst *scp-t-error-step*
  '(:write-at :staging ".stage-state-checkpoint-1" 2 (3)))
(defconst *scp-t-before-error* (car (nth 3 *scp-t-batched-run*)))
(assert-event (equal (fn-bs-content *scp-t-before-error* 5) '(1 2)))
(assert-event
 (mv-let (r bs ks)
   (fn-bs-step *scp-t-before-error* nil *scp-t-error-step* '(:eio . 1) nil 0)
   (declare (ignore bs ks))
   (equal r :eio)))
(defconst *scp-t-error-run*
  (fn-bs-run *scp-t-bs* nil
             (fn-bs-scp-batched-program ".stage-state-checkpoint-1" *scp-t-chunks*)
             '(:ok :ok :ok :ok (:eio . 1)) nil 0))
(assert-event (equal (len *scp-t-error-run*) 5))
(defconst *scp-t-after-error* (car (nth 4 *scp-t-error-run*)))
(assert-event
 (mv-let (r bs ks)
   (fn-bs-step *scp-t-before-error* nil *scp-t-error-step* '(:eio . 1) nil 0)
   (declare (ignore r ks))
   (equal *scp-t-after-error* bs)))
(assert-event (equal (car (last (fn-bs-pending *scp-t-after-error*)))
                     '(:write 5 2 (3))))
(assert-event (equal (fn-bs-content *scp-t-after-error* 5) '(1 2 3)))
; No fence or publication happened after the error.
(assert-event (and (equal (fn-bs-durable-content *scp-t-after-error* 5) nil)
                   (equal (fn-bs-lookup *scp-t-after-error* :root "store-checkpoint.fnsc") 3)))
(defconst *scp-t-error-mutant*
  (mv-let (r bs ks)
    (fn-bs-step *scp-t-before-error* nil
                '(:write-at :staging ".stage-state-checkpoint-1" 0 (3))
                '(:eio . 1) nil 0)
    (declare (ignore r ks))
    bs))
(assert-event (equal (fn-bs-content *scp-t-error-mutant* 5) '(3 2)))
(must-fail-checked
 (assert-event (equal (fn-bs-content *scp-t-error-mutant* 5) '(1 2 3))))
