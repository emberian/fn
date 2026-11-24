; A scheduled page check keeps the builder's workspace valid for the
; next call and exposes the unchanged or sealed writer to the driver.
(in-package "ACL2")
(include-book "runs-build-sealed-page-proof")

(defmacro fn2-run-writer-page-check (w writers fc ctx b3 f pool ds)
  `(fn2-format-run :page t 0 (fn2-run-writers-slot ,w ,writers) (fn2-run-writers-gen ,w ,writers)
             0 65536 (fn2-run-writers-fields ,w ,writers) (fn2-run-writers-okind ,w ,writers)
             (fn2-run-writers-oslot ,w ,writers) (fn2-run-writers-ogen ,w ,writers) 4096
             ,fc ,ctx ,b3 ,f ,pool ,ds))

(defun-nx fn2-run-seal-workspace-p (w hrow writers fc ctx b3 f pool ds)
  (and (equal (fn2-run-writers-phase w writers) *fn2-run-writer-phase-sealing*)
       (equal (fn2-fc-context-hash 0 ctx) hrow)
       (fn2-fcp fc) (fn2-fc-wfp fc) (< 0 (fn2-fc-rows fc))
       (fn2-fc-contextp ctx) (fn2-fc-context-wfp ctx) (< 0 (fn2-fc-context-rows ctx))
       (fn2-fieldsp f) (fn2-fields-wfp f) (natp (fn2-run-writers-fields w writers))
       (<= (+ (fn2-run-writers-fields w writers) *fn2-format-sealed-batch-num-fields*) (fn2-fields-rows f))
       (fn2-b3p b3) (fn2-digestsp ds) (fn2-b3-ready 0 b3 ds) (fn2-digest-rowp hrow ds)
       (fn2-digest-rowp (fn2-fc-context-geometry 0 ctx) ds) (fn2-digest-rowp (fn2-fc-context-previous-seal 0 ctx) ds)
       (fn2-poolp pool) (fn2-pool-wfp pool)))

(defthmd fn2-run-writer-follows-format-check
  (let ((check (fn2-run-writer-page-check w writers fc ctx b3 f pool ds)))
    (implies (fn2-run-seal-workspace-p w hrow writers fc ctx b3 f pool ds)
             (and (equal (fn2-run-seal-step w 0 hrow 4096 writers fc ctx b3 f pool ds)
                         (list (car check) (if (eq (car check) :ok) (fn2-run-writers-set-phase w *fn2-run-writer-phase-sealed* writers) writers)
                            (mv-nth 1 check) (mv-nth 2 check) (mv-nth 3 check) (mv-nth 4 check) (mv-nth 5 check)))
                  (equal (mv-nth 4 check) pool))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-seal-keeps-page-storage (row 0) (budget 4096)))
           :in-theory (union-theories (theory 'minimal-theory)
                       '(fn2-run-seal-workspace-p fn2-run-seal-step eq eql mv-nth car-cons cdr-cons (:t fn2-format-run)
                         (:e fn2-digest-slot) (:e binary-+) (:e <) (:e equal) (:e zp) (:e mv-nth))))))

(defthmd fn2-run-page-check-keeps-seal-workspace
  (let ((check (fn2-run-writer-page-check w writers fc ctx b3 f pool ds)))
    (implies (fn2-run-seal-workspace-p w hrow writers fc ctx b3 f pool ds)
             (and (fn2-run-seal-workspace-p w hrow writers (mv-nth 1 check) ctx (mv-nth 2 check) (mv-nth 3 check) pool (mv-nth 5 check))
                  (equal (fn2-fc-rows (mv-nth 1 check)) (fn2-fc-rows fc))
                  (equal (fn2-fields-rows (mv-nth 3 check)) (fn2-fields-rows f)))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-format-run-shape (kind :page) (sealp t) (row 0)
                     (slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers)) (off 0) (len 65536)
                     (base (fn2-run-writers-fields w writers)) (okind (fn2-run-writers-okind w writers)) (oslot (fn2-run-writers-oslot w writers))
                     (ogen (fn2-run-writers-ogen w writers)) (budget 4096) (fn2-fc fc) (fn2-fc-context ctx) (fn2-b3 b3)
                     (fn2-fields f) (fn2-pool pool) (fn2-digests ds)))
           :in-theory (e/d (fn2-run-seal-workspace-p fn2-b3-ready fn2-digest-rowp fn2-digest-workspacep fn2-b3-words-length)
                       (fn2-format-run fn2-format-run-shape fn2-fcp fn2-fc-wfp fn2-fc-rows fn2-fc-contextp fn2-fc-context-wfp
                        fn2-fc-context-rows fn2-fc-context-hash fn2-fc-context-geometry fn2-fc-context-previous-seal fn2-fieldsp
                        fn2-fields-wfp fn2-fields-rows fn2-poolp fn2-pool-wfp fn2-b3p fn2-b3-wfp fn2-b3-rows fn2-digestsp
                        fn2-digests-wfp fn2-digests-rows fn2-run-writers-phase fn2-run-writers-fields fn2-run-writers-slot
                        fn2-run-writers-gen fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen nth len unsigned-byte-p)))))

(defthmd fn2-run-page-check-keeps-seal-scheduled
  (let* ((w (+ l (fn2-run-builds-wbase 0 builds))) (hrow (+ l (fn2-run-builds-hbase 0 builds)))
         (check (fn2-run-writer-page-check w writers fc ctx b3 f pool ds)))
    (implies (and (fn2-run-build-sealing-at-p l builds writers restarts f fc ctx)
                  (fn2-run-seal-workspace-p w hrow writers fc ctx b3 f pool ds))
             (fn2-run-build-sealing-at-p l builds writers restarts (mv-nth 3 check) (mv-nth 1 check) ctx)))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-page-check-keeps-seal-workspace (w (+ l (fn2-run-builds-wbase 0 builds)))
                             (hrow (+ l (fn2-run-builds-hbase 0 builds)))))
           :in-theory (union-theories (theory 'minimal-theory)
                    '(fn2-run-build-sealing-at-p fn2-run-seal-workspace-p fn2-run-writerp)))))
