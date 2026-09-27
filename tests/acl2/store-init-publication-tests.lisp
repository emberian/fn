; Teeth for books/store-init-publication (PRF-217, PKT-647).
(in-package "ACL2")
(include-book "must-fail-checked")
(include-book "../../books/store-init-publication")

; A parent directory with no store at ROOT, next inode 5, no :transactions
; directory yet; init's plan with a three-octet profile, a one-octet
; frontier and a two-octet generation-1 record.
(defconst *init-t-bs* (fn-bs-make 4 nil (list (cons :parent nil)) nil 5))
(defconst *init-t-files* (fn-bs-init-pub-files '(1 2 3) '(0) "000000000001" '(7 7)))
(defconst *init-t-program*
  (fn-bs-init-pub-program "store.init-1" "store" '(1 2 3) '(0) "000000000001" '(7 7)))

; The program is the import's with init's cut names, in the host's order.
(defun init-t-cuts (steps)
  (if (consp steps)
      (if (equal (car (car steps)) :cut)
          (cons (nth 1 (car steps)) (init-t-cuts (cdr steps)))
        (init-t-cuts (cdr steps)))
    nil))
(assert-event
 (equal (init-t-cuts *init-t-program*)
        '("init-stage-created"
          "init-subdir-created" "init-subdir-created" "init-subdir-created"
          "init-file-created" "init-file-written" "init-file-durable"
          "init-file-created" "init-file-written" "init-file-durable"
          "init-file-created" "init-file-written" "init-file-durable"
          "init-subdir-durable" "init-subdir-durable" "init-subdir-durable"
          "init-staged-durable" "init-validated" "init-published" "init-durable")))

; The reachable positive witness: the complete antecedent, every step :ok.
(assert-event (fn-bs-imp-inputp *init-t-bs* "store.init-1" "store"
                                *fn-bs-init-pub-subdirs* *init-t-files* nil))
(assert-event (not (assoc-equal :transactions (fn-bs-dirs *init-t-bs*))))
(assert-event (fn-bs-imp-outcomesp nil))
(defconst *init-t-run* (fn-bs-imp-run *init-t-bs* nil *init-t-program* nil nil 0))
(assert-event (equal (len *init-t-run*) (len *init-t-program*)))
(defconst *init-t-last* (car (car (last *init-t-run*))))
(assert-event (equal (fn-bs-durable-entry (fn-bs-crash *init-t-last* nil) :parent "store") :stage))
(assert-event (fn-bs-imp-completep (fn-bs-crash *init-t-last* nil)
                                   *fn-bs-init-pub-subdirs* *init-t-files* 5))
(assert-event (fn-bs-init-pub-emptyp (fn-bs-crash *init-t-last* nil)))
; The transactions directory exists and is empty.
(assert-event (equal (assoc-equal :transactions (fn-bs-dirs (fn-bs-crash *init-t-last* nil)))
                     '(:transactions)))

; At `init-published' every landing of the three parent operations is
; covered and every verdict is reachable.
(defconst *init-t-published* (car (nth (- (len *init-t-program*) 3) *init-t-run*)))
(defun init-t-verdict (img)
  (fn-bs-imp-classify (fn-bs-durable-entry img :parent "store.init-1")
                      (fn-bs-durable-entry img :parent "store")))
(assert-event (equal (init-t-verdict (fn-bs-crash *init-t-published* '(:apply :apply :drop)))
                     :publication-uncertain))
(assert-event (equal (init-t-verdict (fn-bs-crash *init-t-published* '(:drop :apply :drop)))
                     :store-present))
(assert-event (fn-bs-init-pub-emptyp (fn-bs-crash *init-t-published* '(:drop :apply :drop))))
(assert-event (equal (init-t-verdict (fn-bs-crash *init-t-published* '(:apply :drop :apply)))
                     :no-store))
(assert-event (equal (init-t-verdict (fn-bs-crash *init-t-published* '(:apply :drop :drop)))
                     :not-published))

; Hypothesis-removal witness: the :transactions id already names a directory
; with an entry (the fresh-id hypothesis fails; every other one holds).  The
; mkdir refuses, nothing is published, and the image's transactions
; directory is not empty.
(defconst *init-t-taken*
  (fn-bs-make 4 nil (list (cons :parent nil) (list :transactions (cons "x" 9))) nil 5))
(assert-event (fn-bs-imp-inputp *init-t-taken* "store.init-1" "store"
                                *fn-bs-init-pub-subdirs* *init-t-files* nil))
(assert-event (assoc-equal :transactions (fn-bs-dirs *init-t-taken*)))
(must-fail-checked
 (defthm init-t-without-fresh-transactions
   (fn-bs-init-pub-emptyp
    (fn-bs-crash (car (car (last (fn-bs-imp-run *init-t-taken* nil *init-t-program* nil nil 0))))
                 nil))))

; Hypothesis-removal witness: an outcome (:ok . 1) (a short write reported
; as success): the run completes and ROOT holds a torn profile.
(defconst *init-t-short-outs*
  (append (make-list 10 :initial-element :ok) '((:ok . 1))))
(assert-event (not (fn-bs-imp-outcomesp *init-t-short-outs*)))
(defconst *init-t-short-run*
  (fn-bs-imp-run *init-t-bs* nil *init-t-program* *init-t-short-outs* nil 0))
(assert-event (equal (len *init-t-short-run*) (len *init-t-program*)))
(must-fail-checked
 (defthm init-t-without-honest-outcomes
   (fn-bs-imp-no-store-or-completep (fn-bs-crash (car (car (last *init-t-short-run*))) nil)
                                    "store" *fn-bs-init-pub-subdirs* *init-t-files* 5 nil)))

; The admission: every arm reachable, and it proceeds only on nothing.
(assert-event (equal (fn-bs-init-pub-admission nil nil) :proceed))
(assert-event (equal (fn-bs-init-pub-admission (fn-bs-imp-classify t nil) nil)
                     '(:refused :interrupted-init)))
(assert-event (equal (fn-bs-init-pub-admission (fn-bs-imp-classify t t) t)
                     '(:refused :publication-uncertain)))
(assert-event (equal (fn-bs-init-pub-admission nil t) '(:refused :store-path-exists)))
