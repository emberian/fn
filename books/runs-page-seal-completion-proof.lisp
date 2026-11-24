; From the writer's actual stored header and zero padding, a fresh page
; checker finishes in 70 full-budget calls, preserving every page byte.
(in-package "ACL2")
(include-book "runs-page-hash-prefix-proof")
(include-book "runs-seal-header-read-proof")

(defmacro fn2-run-writer-check-page (fc b3 f ds)
  `(fn2-run-check-written-page ,fc (fn2-run-seal-context w 0 hrow writers ctx) ,b3 ,f ,ds))

(defun-nx fn2-run-written-page-ready-p (w base writers f fc pool)
  (let ((slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers)))
   (let ((pad (+ *fn2-run-header-area* (fn2-run-payload-length w writers))))
     (and (fn2-run-seal-header-readable-p w base writers f pool)
          (posp pad) (<= pad 2048) (fn2-ribbon-zero-region-p (- 65536 pad) pad slot gen pool)
          (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-idle*)))))

(defmacro fn2-run-next-writer-check (previous)
  `(fn2-run-writer-check-page (mv-nth 1 ,previous) (mv-nth 2 ,previous) (mv-nth 3 ,previous) (mv-nth 5 ,previous)))

(local
 (defthmd fn2-run-three-checks-enter-page-hash
   (fn2-run-writer-seal-bindings
    (let* ((a (fn2-run-writer-check-page fc b3 f ds)) (b (fn2-run-next-writer-check a)) (c (fn2-run-next-writer-check b)))
      (implies (fn2-run-written-page-ready-p w base writers f fc pool)
               (and (equal (car a) :more) (equal (car b) :more) (equal (car c) :more)
                    (equal (mv-nth 4 a) pool) (equal (mv-nth 4 b) pool) (equal (mv-nth 4 c) pool)
                    (fn2-run-hash-page-input-p slot gen pk ps pg (mv-nth 1 c) (mv-nth 2 c) pool)))))
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-run-page-checker-starts-writer-hash
                  (:instance fn2-ribbon-hash-init-cursor (key (fn2-digest-slot 0 *fn2-b3-key*)) (fn2-digests ds) (fn2-b3 b3))
                  (:instance fn2-run-checker-hashes-domain-and-page
                    (slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers))
                    (pk (fn2-run-writers-okind w writers)) (ps (fn2-run-writers-oslot w writers)) (pg (fn2-run-writers-ogen w writers))
                    (pad (+ *fn2-run-header-area* (fn2-run-payload-length w writers))) (ctx (fn2-run-seal-context w 0 hrow writers ctx))
                    (fc (fn2-run-writer-seal-bindings (let ((a (fn2-run-writer-check-page fc b3 f ds))) (mv-nth 1 (fn2-run-next-writer-check a)))))
                    (b3 (fn2-run-writer-seal-bindings (let ((a (fn2-run-writer-check-page fc b3 f ds))) (mv-nth 2 (fn2-run-next-writer-check a)))))
                    (f (fn2-run-writer-seal-bindings (let ((a (fn2-run-writer-check-page fc b3 f ds))) (mv-nth 3 (fn2-run-next-writer-check a)))))
                    (ds (fn2-run-writer-seal-bindings (let ((a (fn2-run-writer-check-page fc b3 f ds))) (mv-nth 5 (fn2-run-next-writer-check a)))))))
            :in-theory (union-theories (theory 'minimal-theory)
                      '(fn2-run-written-page-ready-p fn2-run-seal-header-readable-p (:t fn2-run-payload-length) posp natp not
                        (:e natp) (:e <) (:e equal) (:e binary-+) (:e unary--)))))))

(local
 (defthmd fn2-run-remaining-page-hash-fits-fuel
   (let ((r (fn2-format-drive 67 0 :page t slot gen 0 65536 base pk ps pg 4096 fc ctx b3 f pool ds)))
     (implies (fn2-run-hash-page-input-p slot gen pk ps pg fc b3 pool)
              (and (equal (car r) :ok) (equal (mv-nth 4 r) pool))))
   :hints (("Goal" :do-not '(preprocess) :use (fn2-run-valid-hash-step-continues
                       (:instance fn2-run-format-driver-finishes-page-hash (fuel 67)))
            :in-theory (union-theories (theory 'minimal-theory)
                       '(fn2-run-hash-page-or-end-p (:e natp) (:e <) (:e equal)))))))

(local
 (defthmd fn2-run-driver-skips-finished-check
   (let* ((step (fn2-run-check-page-hash)) (run (fn2-format-drive fuel 0 :page t slot gen 0 65536 base pk ps pg 4096 fc ctx b3 f pool ds)))
     (implies (and (posp fuel) (equal (car step) :more) (equal (mv-nth 4 step) pool))
              (equal run (fn2-format-drive (1- fuel) 0 :page t slot gen 0 65536 base pk ps pg 4096
                            (mv-nth 1 step) ctx (mv-nth 2 step) (mv-nth 3 step) pool (mv-nth 5 step)))))
   :hints (("Goal" :expand ((fn2-format-drive fuel 0 :page t slot gen 0 65536 base pk ps pg 4096 fc ctx b3 f pool ds))
            :in-theory (union-theories (theory 'minimal-theory)
                      '(posp zp natp eq eql mv-nth commutativity-of-+ (:t fn2-format-run) (:e zp) (:e equal)))))))

(local
 (defun fn2-run-writer-check-bind (value count)
   (if (zp count) value (fn2-run-writer-check-bind `(fn2-run-next-writer-check ,value) (1- count)))))

(local
 (defun fn2-run-writer-check-instances (n)
   (declare (xargs :measure (nfix n) :ruler-extenders :all))
   (let* ((step (fn2-run-writer-check-bind '(fn2-run-writer-check-page fc b3 f ds) (nfix (1- n))))
          (states (if (zp n) nil
                    (list `(fc (fn2-run-writer-seal-bindings (mv-nth 1 ,step)))
                          `(b3 (fn2-run-writer-seal-bindings (mv-nth 2 ,step)))
                          `(f (fn2-run-writer-seal-bindings (mv-nth 3 ,step)))
                          `(ds (fn2-run-writer-seal-bindings (mv-nth 5 ,step)))))))
     (cons `(:instance ,(if (equal n 3) 'fn2-run-remaining-page-hash-fits-fuel 'fn2-run-driver-skips-finished-check)
               (slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers))
               (pk (fn2-run-writers-okind w writers)) (ps (fn2-run-writers-oslot w writers)) (pg (fn2-run-writers-ogen w writers))
               (ctx (fn2-run-seal-context w 0 hrow writers ctx)) ,@(and (< n 3) (list (list 'fuel (- 70 n)))) ,@states)
           (if (zp n) nil (fn2-run-writer-check-instances (1- n)))))))

(defthmd fn2-run-format-driver-seals-written-page
  (fn2-run-writer-seal-bindings
   (let ((r (fn2-format-drive 70 0 :page t slot gen 0 65536 base pk ps pg 4096 fc
                              (fn2-run-seal-context w 0 hrow writers ctx) b3 f pool ds)))
     (implies (fn2-run-written-page-ready-p w base writers f fc pool)
              (and (equal (car r) :ok) (equal (mv-nth 4 r) pool)))))
  :hints ((list :do-not ''(preprocess) :use (cons 'fn2-run-three-checks-enter-page-hash (fn2-run-writer-check-instances 3))
                :in-theory '(union-theories (theory 'minimal-theory)
                               '((:e posp) (:e equal) (:e binary-+) (:e unary--))))))
