(in-package "ACL2")
(include-book "../../books/snapshot-decode-remap")
; These witnesses exercise the concrete borrowed-node field frame, not the
; pending full parser/source/recovery inverse. Abstraction is non-executable,
; so its ground witnesses are theorems rather than runtime materializers.
(defun odmt-list (nodes)
  (if (consp nodes) (fn-hdc-pair (car nodes) (odmt-list (cdr nodes)))
    (fn-hdc-atom nil)))
(defconst *odmt-pool* '(60 97 64 120 62 83 84 88 65))
(defconst *odmt-held*
  (odmt-list
   (list (fn-hdc-atom 7) (fn-hdc-atom 9) (fn-hdc-atom 9)
         (fn-hdc-span 3 0 0 5) (fn-hdc-atom 23)
         (fn-hdc-atom nil) (fn-hdc-atom 1) (fn-hdc-atom 2)
         (fn-hdc-atom nil) (fn-hdc-atom 42) (fn-hdc-atom 0)
         (fn-hdc-pair (fn-hdc-atom 1) (fn-hdc-atom nil))
         (fn-hdc-pair (fn-hdc-atom 9) (fn-hdc-span 3 0 0 5))
         (fn-hdc-pair (fn-hdc-atom 8) (fn-hdc-atom nil))
         (fn-hdc-atom nil))))
(defconst *odmt-statement*
  (fn-hdc-pair (fn-hdc-span 4 0 5 4)
               (fn-hdc-pair (fn-hdc-atom 9) (fn-hdc-atom nil))))
(defconst *odmt-composite*
  (odmt-list (list (fn-hdc-atom :hstxa) *odmt-statement* *odmt-held*)))
(defthm odmt-held-complete-positive
  (and (fn-odm-prefixp 5 *odmt-held*)
       (equal (fn-hdc-abstract (fn-odm-held *odmt-held* 0) *odmt-pool*)
              (update-nth 4 0 (fn-hdc-abstract *odmt-held* *odmt-pool*))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-odm-held-preserves-the-complete-logical-field-frame (node *odmt-held*) (handle 0) (pool *odmt-pool*)))
           :in-theory (disable (:executable-counterpart fn-odm-held)))))
(defthm odmt-composite-complete-positive
  (and (fn-odm-prefixp 5 (fn-odm-at 2 *odmt-composite*))
       (equal (fn-hdc-abstract (fn-odm-composite *odmt-composite* 0) *odmt-pool*)
              (update-nth 2
                          (update-nth 4 0 (nth 2 (fn-hdc-abstract *odmt-composite* *odmt-pool*)))
                          (fn-hdc-abstract *odmt-composite* *odmt-pool*))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-odm-composite-preserves-the-original-statement-and-held-frame (node *odmt-composite*) (handle 0) (pool *odmt-pool*)))
           :in-theory (disable (:executable-counterpart fn-odm-composite)))))
; Borrowed string, historical context, numbers and original statement nodes
; remain exact references; only the fixed handle path is replaced.
(assert-event
 (and (natp 0)
      (equal (fn-odm-at 3 (fn-odm-held *odmt-held* 0)) (fn-odm-at 3 *odmt-held*))
      (equal (fn-odm-at 12 (fn-odm-held *odmt-held* 0)) (fn-odm-at 12 *odmt-held*))
      (equal (fn-odm-at 13 (fn-odm-held *odmt-held* 0)) (fn-odm-at 13 *odmt-held*))
      (equal (fn-odm-at 1 (fn-odm-composite *odmt-composite* 0)) *odmt-statement*)
      (equal (fn-odm-at 4 (fn-odm-at 2 (fn-odm-composite *odmt-composite* 0)))
             (fn-hdc-atom 0))))
(defthm odmt-put-complete-positive
  (and (natp 4) (fn-odm-prefixp 5 *odmt-held*)
       (equal (fn-hdc-abstract (fn-odm-put 4 (fn-hdc-atom 0) *odmt-held*) *odmt-pool*)
              (update-nth 4 (fn-hdc-abstract (fn-hdc-atom 0) *odmt-pool*)
                          (fn-hdc-abstract *odmt-held* *odmt-pool*))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-odm-put-refines-the-logical-field-replacement (node *odmt-held*) (n 4) (value (fn-hdc-atom 0)) (pool *odmt-pool*)))
           :in-theory (disable (:executable-counterpart fn-odm-put)))))
(defthm odmt-at-complete-positive
  (and (natp 4) (fn-odm-prefixp 5 *odmt-held*)
       (equal (fn-hdc-abstract (fn-odm-at 4 *odmt-held*) *odmt-pool*)
              (nth 4 (fn-hdc-abstract *odmt-held* *odmt-pool*))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-odm-at-refines-the-logical-field-read (node *odmt-held*) (n 4) (pool *odmt-pool*)))
           :in-theory (disable (:executable-counterpart fn-odm-at)))))
; Corrupted representation witness: a list hidden inside an ATOM is not a
; decoded pair spine, so the structural refinement premise is material.
(defconst *odmt-bad* (fn-hdc-atom '(1 2 3 4 5)))
(defthm odmt-prefix-removal-corrupted-representation
  (and (natp 4) (not (fn-odm-prefixp 5 *odmt-bad*))
       (not (equal (fn-hdc-abstract (fn-odm-put 4 (fn-hdc-atom 0) *odmt-bad*) nil)
                   (update-nth 4 0 (fn-hdc-abstract *odmt-bad* nil)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hdc-abstract fn-hdc-atom fn-hdc-pair))))
; Negative logical index retains the prefix premise; executor never calls it.
(defthm odmt-natural-index-removal
  (and (not (natp -1)) (fn-odm-prefixp 0 *odmt-bad*)
       (not (equal (fn-hdc-abstract (fn-odm-put -1 (fn-hdc-atom 0) *odmt-bad*) nil)
                   (update-nth -1 0 (fn-hdc-abstract *odmt-bad* nil)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hdc-abstract fn-hdc-atom fn-hdc-pair))))

(defthm odmt-at-prefix-removal-corrupted-representation
  (and (natp 4) (not (fn-odm-prefixp 5 *odmt-bad*))
       (not (equal (fn-hdc-abstract (fn-odm-at 4 *odmt-bad*) nil)
                   (nth 4 (fn-hdc-abstract *odmt-bad* nil)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hdc-abstract fn-hdc-atom))))
(defthm odmt-at-natural-index-removal
  (and (not (natp -1)) (fn-odm-prefixp 0 *odmt-bad*)
       (not (equal (fn-hdc-abstract (fn-odm-at -1 *odmt-bad*) nil)
                   (nth -1 (fn-hdc-abstract *odmt-bad* nil)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hdc-abstract fn-hdc-atom))))
(defthm odmt-held-prefix-removal-corrupted-representation
  (and (not (fn-odm-prefixp 5 *odmt-bad*))
       (not (equal (fn-hdc-abstract (fn-odm-held *odmt-bad* 0) nil)
                   (update-nth 4 0 (fn-hdc-abstract *odmt-bad* nil)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hdc-abstract fn-hdc-atom fn-hdc-pair))))
(defconst *odmt-bad-inner*
  (odmt-list (list (fn-hdc-atom :hstxa) *odmt-statement* *odmt-bad*)))
(defthm odmt-composite-held-prefix-removal-corrupted-representation
  (and (not (fn-odm-prefixp 5 (fn-odm-at 2 *odmt-bad-inner*)))
       (not (equal (fn-hdc-abstract (fn-odm-composite *odmt-bad-inner* 0) *odmt-pool*)
                   (update-nth 2
                               (update-nth 4 0 (nth 2 (fn-hdc-abstract *odmt-bad-inner* *odmt-pool*)))
                               (fn-hdc-abstract *odmt-bad-inner* *odmt-pool*)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hdc-abstract fn-hdc-atom fn-hdc-pair))))

