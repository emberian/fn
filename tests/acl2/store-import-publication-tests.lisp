; Teeth for books/store-import-publication (PRF-217).
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)
(include-book "../../books/store-import-publication")

; A parent directory with no store at ROOT, next inode 5; the staged tree
; has two subdirectories and three files (config.json and the frontier in
; the staged directory, one transaction record in transactions/).
(defconst *imp-t-bs*
  (fn-bs-make 4 nil (list (cons :parent nil)) nil 5))
(defconst *imp-t-subdirs* '(("transactions" . :txns) ("config" . :cfg)))
(defconst *imp-t-files* '((:stage "config.json" 1 2 3)
                          (:stage "allocation-frontier.json" 0)
                          (:txns "00000000000000000001.txn" 9 8 7 6 5)))
(defconst *imp-t-program*
  (fn-bs-imp-program "store.import-1" "store" *imp-t-subdirs* *imp-t-files*))

; The reachable positive witness: the complete antecedent, every step :ok.
(assert-event (fn-bs-imp-inputp *imp-t-bs* "store.import-1" "store"
                                *imp-t-subdirs* *imp-t-files* nil))
(assert-event (fn-bs-imp-outcomesp nil))
(defconst *imp-t-run* (fn-bs-imp-run *imp-t-bs* nil *imp-t-program* nil nil 0))
(assert-event (equal (len *imp-t-run*) (len *imp-t-program*)))
; After the last step: ROOT is durably the staged directory, complete.
(defconst *imp-t-last* (car (car (last *imp-t-run*))))
(assert-event (equal (fn-bs-durable-entry (fn-bs-crash *imp-t-last* nil) :parent "store") :stage))
(assert-event (fn-bs-imp-completep (fn-bs-crash *imp-t-last* nil) *imp-t-subdirs* *imp-t-files* 5))
(assert-event (fn-bs-imp-no-store-or-completep (fn-bs-crash *imp-t-last* nil) "store"
                                               *imp-t-subdirs* *imp-t-files* 5 nil))

; At the cut `import-published' three parent operations are pending (the
; staged name, ROOT, the staged name's removal).  Every landing is covered,
; and the classification is reachable in every arm:
(defconst *imp-t-published*
  (car (nth (- (len *imp-t-program*) 3) *imp-t-run*)))
(assert-event (equal (len (fn-bs-pending *imp-t-published*)) 3))
(defun imp-t-verdict (img)
  (fn-bs-imp-classify (fn-bs-durable-entry img :parent "store.import-1")
                      (fn-bs-durable-entry img :parent "store")))
; ROOT landed and the source's removal did not: both names present.
(assert-event (equal (imp-t-verdict (fn-bs-crash *imp-t-published* '(:apply :apply :drop)))
                     :publication-uncertain))
(assert-event (fn-bs-imp-no-store-or-completep
               (fn-bs-crash *imp-t-published* '(:apply :apply :drop)) "store"
               *imp-t-subdirs* *imp-t-files* 5 nil))
; Only ROOT: the store, complete.
(assert-event (equal (imp-t-verdict (fn-bs-crash *imp-t-published* '(:drop :apply :drop)))
                     :store-present))
(assert-event (fn-bs-imp-completep (fn-bs-crash *imp-t-published* '(:drop :apply :drop))
                                   *imp-t-subdirs* *imp-t-files* 5))
; ROOT did not land and the staged name was removed: no store at ROOT.
(assert-event (equal (imp-t-verdict (fn-bs-crash *imp-t-published* '(:apply :drop :apply)))
                     :no-store))
; Only the staged name: not published.
(assert-event (equal (imp-t-verdict (fn-bs-crash *imp-t-published* '(:apply :drop :drop)))
                     :not-published))

; An unrelated existing destination is never replaced: the rename answers
; :eexist and ROOT keeps its entry at every cut.
(defconst *imp-t-occupied*
  (fn-bs-make 4 nil (list (cons :parent (list (cons "store" :other)))) nil 5))
(defconst *imp-t-occupied-run*
  (fn-bs-imp-run *imp-t-occupied* nil *imp-t-program* nil nil 0))
(assert-event (< (len *imp-t-occupied-run*) (len *imp-t-program*)))
(assert-event (equal (fn-bs-durable-entry
                      (fn-bs-crash (car (car (last *imp-t-occupied-run*))) '(:apply :apply :apply))
                      :parent "store")
                     :other))

; A failed rename after issue ((:eio . :issued)) and a failed parent barrier
; ((:eio . choices)): the ambiguous outcomes, still old-or-complete.
(defconst *imp-t-outs-ambiguous*
  (append (make-list (- (len *imp-t-program*) 4) :initial-element :ok)
          '((:eio . :issued))))
(assert-event (fn-bs-imp-outcomesp *imp-t-outs-ambiguous*))
(defconst *imp-t-ambiguous-run*
  (fn-bs-imp-run *imp-t-bs* nil *imp-t-program* *imp-t-outs-ambiguous* nil 0))
(assert-event (equal (len *imp-t-ambiguous-run*) (- (len *imp-t-program*) 3)))
(assert-event (fn-bs-imp-no-store-or-completep
               (fn-bs-crash (car (car (last *imp-t-ambiguous-run*))) '(:drop :apply :drop))
               "store" *imp-t-subdirs* *imp-t-files* 5 nil))

; -----------------------------------------------------------------------------
; Hypothesis-removal witnesses: each run violates exactly one hypothesis of
; the keystone, every other one holds, and a crash image falsifies the
; conclusion.

; (1) STAGE = ROOT: the staged directory is created AT ROOT, empty.
(defconst *imp-t-same-run*
  (fn-bs-imp-run *imp-t-bs* nil (fn-bs-imp-program "store" "store" *imp-t-subdirs* *imp-t-files*)
                 nil nil 0))
(assert-event (not (fn-bs-imp-inputp *imp-t-bs* "store" "store" *imp-t-subdirs* *imp-t-files* nil)))
(must-fail
 (defthm imp-t-without-distinct-names
   (fn-bs-imp-no-store-or-completep (fn-bs-crash (car (nth 0 *imp-t-same-run*)) '(:apply))
                                    "store" *imp-t-subdirs* *imp-t-files* 5 nil)))

; (2) Something already pending: an earlier, unfenced binding of ROOT.
(defconst *imp-t-busy*
  (fn-bs-make 4 nil (list (cons :parent nil)) (list (list :set-entry :parent "store" :other)) 5))
(assert-event (not (fn-bs-imp-inputp *imp-t-busy* "store.import-1" "store"
                                     *imp-t-subdirs* *imp-t-files* nil)))
(must-fail
 (defthm imp-t-without-quiet-start
   (fn-bs-imp-no-store-or-completep
    (fn-bs-crash (car (nth 0 (fn-bs-imp-run *imp-t-busy* nil *imp-t-program* nil nil 0))) '(:apply))
    "store" *imp-t-subdirs* *imp-t-files* 5 nil)))

; (3) A plan file outside the staged tree: a file named ROOT in the parent.
(defconst *imp-t-stray-files* '((:parent "store" 1)))
(assert-event (not (fn-bs-imp-inputp *imp-t-bs* "store.import-1" "store"
                                     *imp-t-subdirs* *imp-t-stray-files* nil)))
(must-fail
 (defthm imp-t-without-staged-files
   (fn-bs-imp-no-store-or-completep
    (fn-bs-crash (car (nth 6 (fn-bs-imp-run *imp-t-bs* nil
                                            (fn-bs-imp-program "store.import-1" "store"
                                                               *imp-t-subdirs* *imp-t-stray-files*)
                                            nil nil 0)))
                 '(:apply :apply :apply :apply))
    "store" *imp-t-subdirs* *imp-t-stray-files* 5 nil)))

; (4) The parent directory absent from the table: a subdirectory can take
; the id :parent, and a file in it named ROOT binds ROOT to an inode.
(defconst *imp-t-noparent* (fn-bs-make 4 nil nil nil 5))
(defconst *imp-t-parent-subdirs* '(("x" . :parent)))
(defconst *imp-t-parent-files* '((:parent "store" 1)))
(assert-event (not (fn-bs-imp-inputp *imp-t-noparent* "store.import-1" "store"
                                     *imp-t-parent-subdirs* *imp-t-parent-files* nil)))
(must-fail
 (defthm imp-t-without-parent-directory
   (fn-bs-imp-no-store-or-completep
    (fn-bs-crash (car (nth 4 (fn-bs-imp-run *imp-t-noparent* nil
                                            (fn-bs-imp-program "store.import-1" "store"
                                                               *imp-t-parent-subdirs*
                                                               *imp-t-parent-files*)
                                            nil nil 0)))
                 '(:apply :apply :apply))
    "store" *imp-t-parent-subdirs* *imp-t-parent-files* 5 nil)))

; (5) An outcome (:ok . 1): a write that accepted one octet and reported
; success.  The run completes with a torn record at ROOT.
(defconst *imp-t-short-outs*
  (append (make-list 8 :initial-element :ok) '((:ok . 1))))
(assert-event (not (fn-bs-imp-outcomesp *imp-t-short-outs*)))
(defconst *imp-t-short-run*
  (fn-bs-imp-run *imp-t-bs* nil *imp-t-program* *imp-t-short-outs* nil 0))
(assert-event (equal (len *imp-t-short-run*) (len *imp-t-program*)))
(must-fail
 (defthm imp-t-without-honest-outcomes
   (fn-bs-imp-no-store-or-completep (fn-bs-crash (car (car (last *imp-t-short-run*))) nil)
                                    "store" *imp-t-subdirs* *imp-t-files* 5 nil)))

; (6) OLD is not ROOT's durable entry.
(must-fail
 (defthm imp-t-without-old-entry
   (fn-bs-imp-no-store-or-completep (fn-bs-crash (car (nth 0 *imp-t-run*)) nil)
                                    "store" *imp-t-subdirs* *imp-t-files* 5 :other)))
