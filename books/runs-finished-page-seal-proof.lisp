; Once the hash cursor reaches the end of a page, one writer call stores
; the finalized digest in the parent-held row and marks the page sealed.
(in-package "ACL2")
(include-book "runs-build-sealed-page-proof")

(defmacro fn2-run-finished-hash-state (row fc)
  `(fn2-fc-set-pos ,row 0 (fn2-fc-set-phase ,row *fn2-fc-phase-digest* ,fc)))
(defmacro fn2-run-finished-page-digest (row hrow ds b3)
  `(fn2-digest-copy ,hrow (fn2-digest-slot ,row *fn2-fc-result*)
                    (fn2-b3-finalize (fn2-digest-slot ,row *fn2-fc-result*) ,row ,ds ,b3)))

(local
 (defthm fn2-run-last-hash-span-finalizes
   (implies (and (equal (fn2-fc-phase row fc) *fn2-fc-phase-hash*) (equal (fn2-fc-pos row fc) *fn2-run-page-size*))
            (equal (fn2-fc-advance 4096 row :page t slot gen 0 *fn2-run-page-size* base pk ps pg fc ctx b3 f pool ds)
                   (list :more 1 (fn2-run-finished-hash-state row fc) b3 pool
                         (fn2-b3-finalize (fn2-digest-slot row *fn2-fc-result*) row ds b3))))
   :hints (("Goal" :in-theory (e/d (fn2-fc-advance fn2-fc-page-span fn2-fc-byte)
                            (fn2-fc-phase fn2-fc-pos fn2-fc-pad fn2-fc-pad-end fn2-fc-set-phase fn2-fc-set-pos
                             fn2-digest-slot fn2-b3-finalize fn2-b3-update fn2-b3-byte fn2-fc-prefix-byte))))))

(local
 (defthm fn2-run-finished-digest-copies-to-parent
   (implies (equal (fn2-fc-phase row fc) *fn2-fc-phase-digest*)
            (equal (fn2-fc-run-bytes 4095 row :page t slot gen 0 *fn2-run-page-size* base pk ps pg fc ctx b3 f pool ds)
                   (list :ok fc b3 pool (fn2-digest-copy (fn2-fc-context-hash row ctx) (fn2-digest-slot row *fn2-fc-result*) ds))))
   :hints (("Goal" :expand ((fn2-fc-run-bytes 4095 row :page t slot gen 0 *fn2-run-page-size* base pk ps pg fc ctx b3 f pool ds))
            :in-theory (e/d (fn2-fc-advance fn2-fc-byte)
                       (fn2-fc-run-bytes fn2-fc-phase fn2-fc-pos fn2-digest-slot fn2-digest-copy fn2-fc-context-hash))))))

(local
 (defthm fn2-run-final-hash-phase
   (implies (natp row) (equal (fn2-fc-phase row (fn2-run-finished-hash-state row fc)) *fn2-fc-phase-digest*))
   :hints (("Goal" :in-theory (e/d (fn2-fc-phase fn2-fc-set-phase fn2-fc-set-pos update-fn2-fc-phase$ai
                                   update-fn2-fc-pos$ai nth-update-nth) (nth update-nth))))))

(defthmd fn2-run-finished-checker-stores-page-digest
  (implies (and (natp row) (equal (fn2-fc-phase row fc) *fn2-fc-phase-hash*) (equal (fn2-fc-pos row fc) *fn2-run-page-size*))
           (equal (fn2-format-run :page t row slot gen 0 *fn2-run-page-size* base pk ps pg 4096 fc ctx b3 f pool ds)
                  (list :ok (fn2-fc-reset row (fn2-run-finished-hash-state row fc)) b3 f pool
                        (fn2-run-finished-page-digest row (fn2-fc-context-hash row ctx) ds b3))))
  :hints (("Goal" :expand ((fn2-fc-run-bytes 4096 row :page t slot gen 0 *fn2-run-page-size* base pk ps pg fc ctx b3 f pool ds))
           :in-theory (union-theories (theory 'minimal-theory)
                  '(fn2-format-run fn2-fc-step fn2-run-last-hash-span-finalizes fn2-run-finished-digest-copies-to-parent
                    fn2-run-final-hash-phase eq eql mv-nth car-cons cdr-cons (:e member-equal) (:e posp) (:e zp)
                    (:e binary-+) (:e unary--) (:e equal) (:e <) (:e natp))))))

(defun-nx fn2-run-writer-hash-complete-p (w row hrow writers fc ctx b3 f ds)
  (and (natp row) (equal (fn2-fc-phase row fc) *fn2-fc-phase-hash*) (equal (fn2-fc-pos row fc) *fn2-run-page-size*)
       (equal (fn2-run-writers-phase w writers) *fn2-run-writer-phase-sealing*)
       (< (fn2-digest-slot row *fn2-fc-previous-seal*) 4294967296) (equal (fn2-fc-context-hash row ctx) hrow)
       (fn2-digest-rowp hrow ds) (fn2-digest-rowp (fn2-fc-context-geometry row ctx) ds)
       (fn2-digest-rowp (fn2-fc-context-previous-seal row ctx) ds) (fn2-b3-ready row b3 ds)
       (<= (+ (fn2-run-writers-fields w writers) *fn2-format-sealed-batch-num-fields*) (fn2-fields-rows f))))

(defthmd fn2-run-finished-writer-seals-page
  (implies (fn2-run-writer-hash-complete-p w row hrow writers fc ctx b3 f ds)
           (equal (fn2-run-seal-step w row hrow 4096 writers fc ctx b3 f pool ds)
                  (list :ok (fn2-run-writers-set-phase w *fn2-run-writer-phase-sealed* writers)
                        (fn2-fc-reset row (fn2-run-finished-hash-state row fc)) b3 f pool
                        (fn2-run-finished-page-digest row hrow ds b3))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-finished-checker-stores-page-digest (slot (fn2-run-writers-slot w writers))
                     (gen (fn2-run-writers-gen w writers)) (base (fn2-run-writers-fields w writers))
                     (pk (fn2-run-writers-okind w writers)) (ps (fn2-run-writers-oslot w writers)) (pg (fn2-run-writers-ogen w writers))))
           :in-theory (union-theories (theory 'minimal-theory)
                     '(fn2-run-seal-step fn2-run-writer-hash-complete-p eq eql mv-nth car-cons cdr-cons (:e equal)
                       (:e <) (:e binary-+) (:e zp) (:e mv-nth))))))

(defthmd fn2-run-builder-records-finished-page
  (let* ((w (+ l (fn2-run-builds-wbase 0 builds))) (hrow (+ l (fn2-run-builds-hbase 0 builds)))
         (page (list l (fn2-run-writers-unit w writers) (fn2-run-writers-counter w writers)
                       (fn2-run-writers-slot w writers) (fn2-run-writers-gen w writers)))
         (step (fn2-run-run-onestep layout entries src sg off unit pages builds curs paths cache writers restarts f pool fc ctx b3 ds)))
    (implies (and (fn2-run-build-sealing-at-p l builds writers restarts f fc ctx)
                  (fn2-run-writer-hash-complete-p w (fn2-run-builds-crow 0 builds) hrow writers fc ctx b3 f ds))
             (and (not (car step)) (equal (mv-nth 1 step) :more) (equal (mv-nth 2 step) entries)
                  (equal (mv-nth 3 step) off) (equal (mv-nth 4 step) unit) (equal (mv-nth 5 step) (cons page pages))
                  (equal (mv-nth 13 step) pool))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-run-adapter-seal-records-page
                 (:instance fn2-run-finished-writer-seals-page (w (+ l (fn2-run-builds-wbase 0 builds)))
                      (row (fn2-run-builds-crow 0 builds)) (hrow (+ l (fn2-run-builds-hbase 0 builds)))))
           :in-theory (union-theories (theory 'minimal-theory)
                      '(car-cons eq eql member-equal (:e member-equal) (:e equal))))))
