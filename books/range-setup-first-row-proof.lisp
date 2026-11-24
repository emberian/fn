; Two actual calls from fresh setup open a leaf and place the first
; admitted input into it. The builder advances by the input line length.
(in-package "ACL2")
(include-book "range-setup-append-state-proof")

(defmacro fn2-range-retry-pending-row (state src sg)
  `(fn2-run-run-onestep *fn2-overview-entry* (mv-nth 2 ,state) ,src ,sg (mv-nth 3 ,state)
        (mv-nth 4 ,state) (mv-nth 5 ,state) (mv-nth 6 ,state) (mv-nth 7 ,state) (mv-nth 8 ,state)
        (mv-nth 9 ,state) (mv-nth 10 ,state) (mv-nth 11 ,state) (mv-nth 12 ,state) (mv-nth 13 ,state)
        (mv-nth 14 ,state) (mv-nth 15 ,state) (mv-nth 16 ,state) (mv-nth 17 ,state)))

(defun-nx fn2-range-first-row-stored-p (step row tail dst dg)
  (let ((w (mv-nth 10 step)))
    (and (not (car step)) (equal (mv-nth 1 step) :more) (equal (mv-nth 2 step) tail)
         (equal (mv-nth 3 step) (len (nth 4 row))) (equal (mv-nth 5 step) nil)
         (fn2-run-open-overview-contents-p (list row) 0 (fn2-run-writers-entries 0 w) (fn2-run-writers-restarts 0 w)
                          (fn2-run-writers-cursor 0 w) dst dg (mv-nth 11 step) (mv-nth 13 step)))))

(local
 (defthmd fn2-range-retrying-stores-pending-row
   (implies (and (fn2-range-first-open-result-p state (cons row tail) unit dst dg)
                 (fn2-range-next-append-state src sg dst dg state) (fn2-run-values-layoutp *fn2-overview-entry* row))
            (fn2-range-first-row-stored-p (fn2-range-retry-pending-row state src sg) row tail dst dg))
   :hints (("Goal" :do-not '(preprocess)
            :use ((:instance fn2-range-empty-leaf-stores-first-row (unit (mv-nth 4 state)) (pages (mv-nth 5 state))
                    (b (mv-nth 6 state)) (curs (mv-nth 7 state)) (paths (mv-nth 8 state)) (cache (mv-nth 9 state))
                    (w (mv-nth 10 state)) (rs (mv-nth 11 state)) (f (mv-nth 12 state)) (p (mv-nth 13 state))
                    (fc (mv-nth 14 state)) (ctx (mv-nth 15 state)) (b3 (mv-nth 16 state)) (ds (mv-nth 17 state))))
            :in-theory (union-theories (theory 'minimal-theory) '(fn2-range-first-open-result-p fn2-range-first-row-stored-p))))))

(defthmd fn2-range-setup-stores-first-overview-row
  (fn2-range-first-builder-bindings
   (let* ((first (fn2-range-initial-build-step)) (second (fn2-range-retry-pending-row first src sg)))
     (implies (and (equal fn2-pool (create-fn2-pool)) (fn2-fieldsp fn2-fields)
                   (fn2-run-buildsp fn2-run-builds) (fn2-run-writersp fn2-run-writers)
                   (natp k) (<= k 5) (fn2-run-values-layoutp *fn2-overview-entry* row))
              (fn2-range-first-row-stored-p second row tail 2 1))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-range-first-builder-input-after-start fn2-range-setup-opens-first-overview-leaf fn2-range-setup-prepares-first-row-append
                 (:instance fn2-range-retrying-stores-pending-row (src 1) (sg 1) (dst 2) (dg 1)
                    (unit (+ 1 (* 1000 k))) (state (fn2-range-first-builder-bindings (fn2-range-initial-build-step)))))
           :in-theory (union-theories (theory 'minimal-theory)
                      '(fn2-range-setup-prepares-first-row-append fn2-range-setup-opens-first-overview-leaf
                        fn2-range-first-builder-input-after-start (:e natp) (:e <) (:e equal) (:e not))))))
