; Witnesses and teeth for the committed-history marker program
; (books/byte-store-marker-program.lisp) and K0 at its cuts
; (books/byte-store-k0-marker.lisp).  The witness is the K5 fixture's second
; publication at its completing pair: the Store retains two records, the
; kernel is :completing sequence 1, and the marker program writes the frame
; the host writes for sequence 1 (count 2).  A second marker run from the
; first one's durable state replaces a present marker (count 2 -> 3), so the
; old-or-new claim is exercised with an old marker that is not absent.
(in-package "ACL2")
(include-book "../../books/byte-store-k0-marker")
(include-book "byte-store-stable-prefix-tests")
(include-book "std/testing/must-fail" :dir :system)

(defun bskm-pair () (car (last (bsk5-record-2-run))))
(defun bskm-run (bs ks stage octets)
  (fn-bs-run bs ks (fn-bs-marker-program stage octets) nil *bsk5-groups* *bsk5-capacity*))
(defun bskm-good ()
  (bskm-run (car (bskm-pair)) (cdr (bskm-pair)) ".stage-marker-k0" (fn-hm-after-commit 1)))
(defun bskm-related-at (run k)
  (fn-bs-store-relation (car (nth k run)) (cdr (nth k run))))
(defun bskm-k0-conclusion (run)
  (and (equal (len run) 10)
       (bskm-related-at run 1) (bskm-related-at run 3) (bskm-related-at run 5)
       (fn-bs-store-relation (fn-bs-marker-rename-dropped (car (nth 7 run))) (cdr (nth 7 run)))
       (mv-let (r landed) (fn-bs-fsync-dir (car (nth 7 run)) :root :ok)
         (declare (ignore r))
         (equal landed (car (nth 9 run))))
       (bskm-related-at run 9)))
; Every pending operation lands (a SIGKILL image with every entry applied).
(defun bskm-all-land (ops unit)
  (if (atom ops) nil
    (cons (if (equal (car (car ops)) :write)
              (fn-bs-all-new (fn-bs-unit-count (nth 2 (car ops)) (len (nth 3 (car ops))) unit))
            :apply)
          (bskm-all-land (cdr ops) unit))))
(defun bskm-obs (run k landed)
  (let ((b (car (nth k run))))
    (fn-bs-hm-observation
     (fn-bs-crash b (if landed (bskm-all-land (fn-bs-pending b) (fn-bs-unit b)) nil)))))

; Reachable witness: every hypothesis of fn-bs-k0-marker-cuts-relation holds,
; so does its conclusion, and the marker at each cut is the table's.
(assert-event
 (let ((bs (car (bskm-pair))) (ks (cdr (bskm-pair))) (run (bskm-good))
       (new (list :present (fn-hm-after-commit 1))))
   (and (fn-bs-store-relation bs ks)
        (equal (len (fn-sf-records ks)) 2)
        (fn-bs-finish-inputp ks 1 1)
        (not (fn-bs-lookup bs :staging ".stage-marker-k0"))
        (fn-bs-marker-inputp bs ".stage-marker-k0")
        (bskm-k0-conclusion run)
        (equal (fn-bs-hm-observation bs) '(:absent))
        (equal (bskm-obs run 5 t) '(:absent))
        (equal (bskm-obs run 7 nil) '(:absent))
        (equal (bskm-obs run 7 t) new)
        (equal (bskm-obs run 9 nil) new)
        (equal (fn-hm-open-verdict (bskm-obs run 9 nil) 2) '(:admitted :marked 2))
        (equal (fn-hm-open-verdict (bskm-obs run 9 nil) 1)
               '(:refused :history-short-of-marker 2)))))

; The second marker run: an old marker (count 2) is present and replaced by
; count 3.  Before the rename every image keeps the old frame; at the rename
; either; after the root barrier the new one.  The open at the record count
; the commit leaves admits every one of them.
(defun bskm-second ()
  (bskm-run (car (nth 9 (bskm-good))) (cdr (nth 9 (bskm-good)))
            ".stage-marker-k0b" (fn-hm-after-commit 2)))
(assert-event
 (let* ((bs (car (nth 9 (bskm-good)))) (run (bskm-second))
        (old (list :present (fn-hm-after-commit 1)))
        (new (list :present (fn-hm-after-commit 2))))
   (and (fn-bs-marker-inputp bs ".stage-marker-k0b")
        (fn-bs-store-relation bs (cdr (bskm-pair)))
        (bskm-k0-conclusion run)
        (equal (fn-bs-hm-observation bs) old)
        (equal (bskm-obs run 1 t) old) (equal (bskm-obs run 3 t) old)
        (equal (bskm-obs run 5 t) old)
        (equal (bskm-obs run 7 nil) old) (equal (bskm-obs run 7 t) new)
        (equal (bskm-obs run 9 nil) new)
        (fn-hm-admittedp (cons 2 old))
        (fn-hm-admittedp (cons 3 (bskm-obs run 7 nil)))
        (fn-hm-admittedp (cons 3 (bskm-obs run 7 t)))
        (fn-hm-admittedp (fn-hm-run '((:burn) (:uncertain nil)) (cons 3 (bskm-obs run 9 nil)))))))

; ---------------------------------------------------------------------------
; Teeth for fn-bs-k0-marker-cuts-relation, one per hypothesis.

; Drop the relation: the completing kernel over the initial byte image.
(assert-event (not (fn-bs-store-relation (bsk5-initial) (cdr (bskm-pair)))))
(must-fail
 (assert-event
  (bskm-k0-conclusion (bskm-run (bsk5-initial) (cdr (bskm-pair))
                                ".stage-marker-k0" (fn-hm-after-commit 1)))))

;; The completion window (fn-bs-finish-inputp) is how the proof obtains a
;; quiet root and a kernel outside the recovery window; it is not necessary
;; for the conclusion.  The frontier program's replaced pair (its rename
;; onto the root pending, the kernel :frontier-attempted) satisfies the
;; conclusion too: the root barrier lands both renames and that kernel admits
;; either frontier.  Stated as a test so the premise is not mistaken for
;; teeth (finding in planning/evidence/p10-marker-model-2026-09-25.md).
(defun bskm-frontier-pair ()
  (nth 9 (fn-bs-run (car (bsk5-finished)) (cdr (bsk5-finished))
                    (fn-bs-frontier-program ".allocation-k0" (fn-bs-frontier-encode 2))
                    nil *bsk5-groups* *bsk5-capacity*)))
(assert-event
 (let ((p (bskm-frontier-pair)))
   (and (fn-bs-store-relation (car p) (cdr p))
        (not (fn-bs-finish-inputp (cdr p) 1 1))
        (fn-bs-ops-for-dir (fn-bs-pending (car p)) :root)
        (bskm-k0-conclusion (bskm-run (car p) (cdr p) ".stage-marker-k0"
                                      (fn-hm-after-commit 1))))))

; Drop the stage-name type.
(must-fail
 (assert-event
  (bskm-k0-conclusion (bskm-run (car (bskm-pair)) (cdr (bskm-pair))
                                'not-a-name (fn-hm-after-commit 1)))))

; Drop the free stage name: the stage is already taken, create fails.
(defun bskm-occupied ()
  (let ((bs (car (bskm-pair))))
    (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs)
                (put-assoc-equal :staging
                                 (cons (cons ".stage-marker-k0" 0)
                                       (cdr (assoc-equal :staging (fn-bs-dirs bs))))
                                 (fn-bs-dirs bs))
                (fn-bs-pending bs) (fn-bs-next-ino bs))))
(must-fail
 (assert-event
  (bskm-k0-conclusion (bskm-run (bskm-occupied) (cdr (bskm-pair))
                                ".stage-marker-k0" (fn-hm-after-commit 1)))))

; Drop the octet type.
(must-fail
 (assert-event
  (bskm-k0-conclusion (bskm-run (car (bskm-pair)) (cdr (bskm-pair))
                                ".stage-marker-k0" '(256)))))

; (consp octets) is the domain of the host's frames, not a premise the
; relation needs: an empty write lands nothing and every cut is still
; related.  Stated as a test, so the hypothesis is not mistaken for teeth;
; fn-bs-marker-after-commit-is-a-frame discharges it for every frame the host
; writes, and the host faults before any write when there is none.
(assert-event
 (bskm-k0-conclusion (bskm-run (car (bskm-pair)) (cdr (bskm-pair)) ".stage-marker-k0" nil)))

; ---------------------------------------------------------------------------
; Teeth for fn-bs-marker-crash-is-the-history-table / -open-stays-admitted.

; Drop the fenced old marker: the old marker inode carries a pending write
; (a marker never fenced), and a crash image tears it: the observation before
; the rename is no longer the old one.
(defun bskm-unfenced ()
  (let* ((bs (car (nth 9 (bskm-good))))
         (old (fn-bs-durable-entry bs :root *fn-bs-history-marker-name*)))
    (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs) (fn-bs-dirs bs)
                (append (fn-bs-pending bs) (list (list :write old 0 '(7 7 7))))
                (fn-bs-next-ino bs))))
(assert-event (not (fn-bs-marker-inputp (bskm-unfenced) ".stage-marker-k0b")))
(must-fail
 (assert-event
  (let ((run (bskm-run (bskm-unfenced) (cdr (bskm-pair)) ".stage-marker-k0b" (fn-hm-after-commit 2))))
    (equal (bskm-obs run 5 t) (fn-bs-hm-observation (bskm-unfenced))))))

; Drop the quiet root: a pending root entry for the marker name (another
; writer's rename) lands in the image before this program's rename.
(defun bskm-root-busy ()
  (let ((bs (car (bskm-pair))))
    (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs) (fn-bs-dirs bs)
                (append (fn-bs-pending bs)
                        (list (list :set-entry :root *fn-bs-history-marker-name*
                                    (fn-bs-durable-entry bs :root *fn-bs-scan-config-name*))))
                (fn-bs-next-ino bs))))
(must-fail
 (assert-event
  (let ((run (bskm-run (bskm-root-busy) (cdr (bskm-pair)) ".stage-marker-k0" (fn-hm-after-commit 1))))
    (member-equal (bskm-obs run 5 t)
                  (list (fn-bs-hm-observation (bskm-root-busy))
                        (list :present (fn-hm-after-commit 1)))))))

; Drop admission before the commit: sequence 0 over a marker already at 2
; (a marker ahead of the history).  The open after the commit refuses.
(assert-event (not (fn-hm-admittedp (cons 0 (fn-bs-hm-observation (car (nth 9 (bskm-good))))))))
(must-fail
 (assert-event
  (let ((run (bskm-run (car (nth 9 (bskm-good))) (cdr (bskm-pair))
                       ".stage-marker-k0b" (fn-hm-after-commit 0))))
    (fn-hm-admittedp (cons 1 (bskm-obs run 5 t))))))

; Drop the count domain: at the end of uint32 there is no frame, and the
; marker program the host would run is not a history step.
(assert-event (null (fn-hm-after-commit 4294967295)))
