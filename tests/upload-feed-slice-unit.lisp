; Actual six-result slice consumed by the core wrapper, including full effects.
(in-package "ACL2")
(include-book "upload-feed-lf-unit")

; Complete logical snapshot generated from the actual pool schema, including
; every extra scalar field; COPY's reference face is deliberately test-only.
(make-event
 (let* ((name 'fn2-pool)
        (schema (cdr (assoc-eq name (fn2-decl-rows :columns (w state)))))
        (fields (append (fn2-columns-fields name (fn2-decl-get :columns schema))
                        (list (list (fn2-columns-sym name "-ROWS") :type
                                    (list 'integer 0 (- (fn2-decl-get :rows-bound schema) 1)) :initially 0))
                        (fn2-decl-get :extra-fields schema))))
   (cons 'progn (fn2-columns-reference-events name (fn2-columns-sym name "-REF") fields))))


(defun fn2-ufs-run (end budget stale)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-pool
  (mv-let (result fn2-pool)
   (b* ((fn2-pool (fn2-pool-init '((1 . 128) (1 . 128)) 1 1000 fn2-pool))
        ((mv rc rx rg fn2-pool) (fn2-pool-reserve 0 1 1 1 fn2-pool))
        ((mv dc dst dg fn2-pool) (fn2-pool-reserve 1 2 2 2 fn2-pool))
        (wire '(65 13 10 13 10 66 13 10))
        (fn2-pool (fn2-ufu-put wire rx rg fn2-pool))
        (before (fn2-pool-copy fn2-pool))
        ((mv code next mode discard copied fn2-pool)
         (fn2-upload-feed-slice budget 0 end 0 nil t rx (if stale (+ 1 rg) rg)
                                1 1 1 dst dg 2 2 2 fn2-pool))
        (unchanged (equal before (fn2-pool-copy fn2-pool)))
        (first-data (fn2-ufu-read 0 (fn2-gram-fill dst fn2-pool) dst dg fn2-pool))
        ((mv code2 next2 mode2 discard2 copied2 fn2-pool)
         (if (eq code :budget)
          (fn2-upload-feed-slice 100 next end mode discard t rx rg 1 1 1 dst dg 2 2 2 fn2-pool)
          (mv :none next mode discard 0 fn2-pool))))
    (mv (list rc dc code next mode discard copied unchanged first-data
              code2 next2 mode2 discard2 copied2
              (fn2-ufu-read 0 (fn2-gram-fill dst fn2-pool) dst dg fn2-pool))
        fn2-pool)) result)))

(assert-event
 (and
  ; Explicit END is smaller than RX fill; no later bytes are copied.
  (equal (fn2-ufs-run 3 100 nil)
         '(:ok :ok :need-more 3 0 nil 3 nil (65 13 10)
           :none 3 0 nil 0 (65 13 10)))
  ; A blank header line does not cut this face: STOP-HEADER is actually NIL.
  (equal (fn2-ufs-run 8 100 nil)
         '(:ok :ok :need-more 8 0 nil 8 nil (65 13 10 13 10 66 13 10)
           :none 8 0 nil 0 (65 13 10 13 10 66 13 10)))
  ; Positive one-byte progress and continuation use the same actual slice.
  (equal (fn2-ufs-run 8 1 nil)
         '(:ok :ok :budget 1 1 nil 1 nil (65)
           :need-more 8 0 nil 7 (65 13 10 13 10 66 13 10)))
  ; Failed ownership validation preserves the complete generated pool state.
  (equal (fn2-ufs-run 8 100 t)
         '(:ok :ok :fault 0 0 nil 0 t nil :none 0 0 nil 0 nil))))
