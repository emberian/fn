; The page checker reads the writer's stored outer header over the full
; page. The codec's complete decode and the checker's budget are both 4096.
(in-package "ACL2")
(include-book "runs-stored-header-fields-proof")
(include-book "runs-writer-header-bytes-proof")
(include-book "runs-header-overwrite-proof")

(defmacro fn2-run-seal-header-read ()
  '(fn2-fc-decode-step :page base slot gen 0 65536 pk ps pg 4096 (fn2-fc-start :page base f) pool))

(local
 (defthmd fn2-run-seal-header-decoder
   (equal (fn2-run-seal-header-read) (fn2-format-page-header-decode base slot gen 0 65536 pk ps pg f pool))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                   '(fn2-fc-decode-step fn2-fc-start fn2-format-page-header-decode eql eq (:e equal)))))))

(local
 (defthmd fn2-run-seal-header-full-page-range
   (implies (and (fn2-run-stored-header-p *fn2-format-page-header* vals slot gen 0 *fn2-run-header-area* pk ps pg pool)
                 (fn2-run-filled-page-p slot gen pk ps pg pool))
            (and (fn2-run-stored-header-p *fn2-format-page-header* vals slot gen 0 65536 pk ps pg pool)
                 (<= (len (fn2-layout-octets *fn2-format-page-header* vals)) *fn2-run-header-area*)))
   :hints (("Goal" :use ((:instance fn2-run-filled-page-allows-subrange (start 0) (end 65536) (writep nil)))
            :in-theory (e/d (fn2-run-stored-header-p)
                     (fn2-run-values-layoutp fn2-run-header-scalars-p fn2-poolp fn2-pool-wfp fn2-pool-base
                      fn2-run-read-bytes fn2-layout-octets fn2-layout-range-code len unsigned-byte-p))))))

(defthmd fn2-run-page-checker-reads-stored-header
  (let ((read (fn2-run-seal-header-read)))
    (implies (and (fn2-run-stored-header-p *fn2-format-page-header* vals slot gen 0 *fn2-run-header-area* pk ps pg pool)
                  (fn2-run-filled-page-p slot gen pk ps pg pool)
                  (natp base) (natp field) (< field *fn2-format-page-header-num-fields*)
                  (<= (+ base *fn2-format-page-header-num-fields*) (fn2-fields-rows f)))
             (and (equal (car read) :ok) (natp (mv-nth 1 read)) (<= (mv-nth 1 read) *fn2-run-header-area*)
                  (equal (fn2-fields-value (+ base field) (mv-nth 2 read)) (nth field vals)))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-run-seal-header-decoder fn2-run-seal-header-full-page-range
                 (:instance fn2-format-page-header-reads-stored-field (off 0) (end 65536) (watch (+ base field))))
           :in-theory (e/d () (fn2-run-stored-header-p fn2-fc-decode-step fn2-fc-start fn2-format-page-header-decode
                         fn2-pool-base fn2-layout-range-code fn2-fields-value fn2-fields-rows fn2-layout-octets len nth)))))

(defmacro fn2-run-writer-seal-bindings (&rest body)
  `(let ((slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers))
         (pk (fn2-run-writers-okind w writers)) (ps (fn2-run-writers-oslot w writers))
         (pg (fn2-run-writers-ogen w writers))) ,@body))

(defun-nx fn2-run-seal-header-readable-p (w base writers f pool)
  (fn2-run-writer-seal-bindings
   (and (fn2-run-filled-page-p slot gen pk ps pg pool)
        (fn2-run-stored-header-p *fn2-format-page-header* (fn2-run-outer-header-values w writers)
                                  slot gen 0 *fn2-run-header-area* pk ps pg pool)
        (natp base) (<= (+ base *fn2-format-page-header-num-fields*) (fn2-fields-rows f)))))

(local
 (defthmd fn2-run-writer-field-in-seal-header
   (fn2-run-writer-seal-bindings
    (let ((read (fn2-run-seal-header-read)))
      (implies (and (fn2-run-seal-header-readable-p w base writers f pool) (natp i) (< i *fn2-format-page-header-num-fields*))
               (and (equal (car read) :ok) (natp (mv-nth 1 read)) (<= (mv-nth 1 read) *fn2-run-header-area*)
                    (equal (fn2-fields-value (+ base i) (mv-nth 2 read)) (nth i (fn2-run-outer-header-values w writers)))))))
   :hints (("Goal" :use ((:instance fn2-run-page-checker-reads-stored-header (field i) (vals (fn2-run-outer-header-values w writers))
                     (slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers)) (pk (fn2-run-writers-okind w writers))
                     (ps (fn2-run-writers-oslot w writers)) (pg (fn2-run-writers-ogen w writers))))
            :in-theory (union-theories (theory 'minimal-theory) '(fn2-run-seal-header-readable-p))))))

(local
 (defun fn2-run-seal-field-instances (i)
   (if (zp i) nil
     (cons `(:instance fn2-run-writer-field-in-seal-header (i ,(1- i))) (fn2-run-seal-field-instances (1- i))))))

(defthmd fn2-run-writer-header-matches-seal-context
  (fn2-run-writer-seal-bindings
   (let* ((read (fn2-run-seal-header-read)) (fields (mv-nth 2 read)) (context (fn2-run-seal-context w 0 hrow writers ctx)))
     (implies (fn2-run-seal-header-readable-p w base writers f pool)
              (and (equal (car read) :ok) (natp (mv-nth 1 read)) (<= (mv-nth 1 read) *fn2-run-header-area*)
                   (equal (fn2-fc-identity 0 :page base 65536 context fields) :ok)
                   (equal (fn2-fields-value (+ base *fn2-format-page-header-field-header-length*) fields) *fn2-run-header-area*)
                   (equal (fn2-fields-value (+ base *fn2-format-page-header-field-payload-length*) fields)
                          (fn2-run-payload-length w writers))))))
  :hints ((list :do-not ''(preprocess) :use (fn2-run-seal-field-instances *fn2-format-page-header-num-fields*)
           :in-theory '(e/d (fn2-fc-identity fn2-run-seal-context fn2-fc-context-history fn2-fc-context-incarnation
                       fn2-fc-context-location fn2-fc-context-writer-epoch fn2-fc-context-allocation fn2-fc-context-page-kind
                       fn2-fc-context-encoded-length nth-update-nth)
             (fn2-run-seal-header-readable-p fn2-fields-value fn2-fc-start fn2-fc-decode-step fn2-run-writers-slot
              fn2-run-writers-gen fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen fn2-run-writers-page-kind
              fn2-run-writers-history fn2-run-writers-incarnation fn2-run-writers-unit fn2-run-writers-epoch fn2-run-writers-counter
              fn2-run-payload-length fn2-digest-slot update-nth)))))

(defmacro fn2-run-check-written-page (checker context hash fields digests)
  `(fn2-format-run :page t 0 slot gen 0 65536 base pk ps pg 4096 ,checker ,context ,hash ,fields pool ,digests))

(local
 (defthmd fn2-run-filled-page-starts-decoding
   (let ((r (fn2-run-check-written-page fc ctx b3 f ds))
         (hash (fn2-b3-init 0 0 (fn2-digest-slot 0 *fn2-b3-key*) ds b3)))
     (implies (and (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-idle*)
                   (fn2-run-filled-page-p slot gen pk ps pg pool))
              (equal r (list :more (fn2-fc-set-phase 0 *fn2-fc-phase-decode* fc)
                             (mv-nth 1 hash) (fn2-fc-start :page base f) pool (mv-nth 0 hash)))))
   :hints (("Goal" :use ((:instance fn2-run-filled-page-allows-subrange (start 0) (end 65536) (writep t)))
            :in-theory (union-theories (theory 'minimal-theory)
                         '(fn2-format-run fn2-fc-step (:e natp) eq eql mv-nth car-cons cdr-cons
                           (:e mv-nth) (:e equal) (:e member-equal) (:e <) (:e posp) (:e binary-+) (:e zp)))))))

(local
 (defmacro fn2-run-accepted-seal-header (checker pad)
   `(let* ((v (fn2-fc-set-geom 0 0 ,checker)) (v (fn2-fc-set-previous-seal-offset 0 0 v))
           (v (fn2-fc-set-zero 0 65536 v)) (v (fn2-fc-set-pad 0 ,pad v)) (v (fn2-fc-set-pad-end 0 65536 v))
           (v (fn2-fc-set-pos 0 0 v))) (fn2-fc-set-phase 0 *fn2-fc-phase-prefix* v))))

(local
 (defthmd fn2-run-decoded-writer-sets-padding
   (fn2-run-writer-seal-bindings
    (let* ((read (fn2-run-seal-header-read)) (fields (mv-nth 2 read)) (context (fn2-run-seal-context w 0 hrow writers ctx))
           (pad (+ *fn2-run-header-area* (fn2-run-payload-length w writers)))
           (check (fn2-fc-decoded 0 :page 0 65536 base (mv-nth 1 read) fc context b3 fields pool ds)))
      (implies (and (fn2-run-seal-header-readable-p w base writers f pool) (<= pad 65536))
               (equal check (list :more (fn2-run-accepted-seal-header fc pad))))))
   :hints (("Goal" :do-not '(preprocess) :use fn2-run-writer-header-matches-seal-context
            :in-theory (e/d (fn2-fc-decoded)
                     (fn2-run-seal-header-readable-p fn2-run-payload-length fn2-run-seal-context
                      fn2-fc-identity fn2-fc-start fn2-fc-decode-step fn2-fields-value fn2-fc-set-pos fn2-fc-set-pad
                      fn2-fc-set-zero fn2-fc-set-geom fn2-fc-set-phase fn2-fc-set-previous-seal-offset fn2-fc-set-pad-end
                      fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen))))))

(local
 (defthmd fn2-run-header-acceptance-fields
   (let ((after (fn2-run-accepted-seal-header checker pad)))
     (and (equal (fn2-fc-phase 0 after) *fn2-fc-phase-prefix*) (equal (fn2-fc-pos 0 after) 0)
          (equal (fn2-fc-pad 0 after) pad) (equal (fn2-fc-pad-end 0 after) 65536)))
   :hints (("Goal" :in-theory (e/d (fn2-fc-pos fn2-fc-phase fn2-fc-pad fn2-fc-pad-end fn2-fc-set-geom
                            fn2-fc-set-previous-seal-offset fn2-fc-set-zero fn2-fc-set-pad fn2-fc-set-pad-end fn2-fc-set-phase
                            fn2-fc-set-pos update-fn2-fc-geom$ai update-fn2-fc-previous-seal-offset$ai update-fn2-fc-zero$ai
                            update-fn2-fc-pad$ai update-fn2-fc-pad-end$ai update-fn2-fc-phase$ai update-fn2-fc-pos$ai nth-update-nth)
                        (nth update-nth))))))

(local
 (defthm fn2-run-select-decode-phase
   (equal (fn2-fc-phase 0 (fn2-fc-set-phase 0 *fn2-fc-phase-decode* fc)) *fn2-fc-phase-decode*)
   :hints (("Goal" :in-theory (e/d (fn2-fc-set-phase fn2-fc-phase update-fn2-fc-phase$ai nth-update-nth) (nth update-nth))))))

(local
 (defthmd fn2-run-check-writer-decode-step
   (fn2-run-writer-seal-bindings
    (let* ((context (fn2-run-seal-context w 0 hrow writers ctx)) (pad (+ *fn2-run-header-area* (fn2-run-payload-length w writers)))
           (read (fn2-run-seal-header-read)) (r (fn2-run-check-written-page fc context b3 (fn2-fc-start :page base f) ds)))
      (implies (and (fn2-run-seal-header-readable-p w base writers f pool) (<= pad 65536)
                    (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-decode*))
               (equal r (list :more (fn2-run-accepted-seal-header fc pad) b3 (mv-nth 2 read) pool ds)))))
   :hints (("Goal" :do-not '(preprocess) :use (fn2-run-writer-header-matches-seal-context fn2-run-decoded-writer-sets-padding)
            :in-theory (union-theories (theory 'minimal-theory)
                       '(fn2-format-run fn2-fc-step (:e natp) eq eql mv-nth car-cons cdr-cons
                        (:t fn2-fc-decode-step) (:e mv-nth) (:e equal) (:e member-equal) (:e <) (:e posp) (:e binary-+) (:e zp)))))))

(defthmd fn2-run-page-checker-starts-writer-hash
  (fn2-run-writer-seal-bindings
   (let* ((context (fn2-run-seal-context w 0 hrow writers ctx)) (pad (+ *fn2-run-header-area* (fn2-run-payload-length w writers)))
          (a (fn2-run-check-written-page fc context b3 f ds))
          (b (fn2-run-check-written-page (mv-nth 1 a) context (mv-nth 2 a) (mv-nth 3 a) (mv-nth 5 a)))
          (hash (fn2-b3-init 0 0 (fn2-digest-slot 0 *fn2-b3-key*) ds b3)))
     (implies (and (fn2-run-seal-header-readable-p w base writers f pool) (<= pad 65536)
                   (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-idle*))
              (and (equal (car a) :more) (equal (car b) :more) (equal (mv-nth 4 a) pool) (equal (mv-nth 4 b) pool)
                   (equal (mv-nth 2 b) (mv-nth 1 hash)) (equal (mv-nth 5 b) (mv-nth 0 hash))
                   (equal (fn2-fc-phase 0 (mv-nth 1 b)) *fn2-fc-phase-prefix*) (equal (fn2-fc-pos 0 (mv-nth 1 b)) 0)
                   (equal (fn2-fc-pad 0 (mv-nth 1 b)) pad) (equal (fn2-fc-pad-end 0 (mv-nth 1 b)) 65536)))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-filled-page-starts-decoding
                     (ctx (fn2-run-seal-context w 0 hrow writers ctx)) (slot (fn2-run-writers-slot w writers))
                     (gen (fn2-run-writers-gen w writers)) (pk (fn2-run-writers-okind w writers))
                     (ps (fn2-run-writers-oslot w writers)) (pg (fn2-run-writers-ogen w writers)))
                 (:instance fn2-run-check-writer-decode-step (fc (fn2-fc-set-phase 0 *fn2-fc-phase-decode* fc))
                   (ds (mv-nth 0 (fn2-b3-init 0 0 (fn2-digest-slot 0 *fn2-b3-key*) ds b3)))
                   (b3 (mv-nth 1 (fn2-b3-init 0 0 (fn2-digest-slot 0 *fn2-b3-key*) ds b3))))
                 (:instance fn2-run-header-acceptance-fields (checker (fn2-fc-set-phase 0 *fn2-fc-phase-decode* fc))
                         (pad (+ *fn2-run-header-area* (fn2-run-payload-length w writers)))))
           :in-theory (union-theories (theory 'minimal-theory)
                      '(fn2-run-seal-header-readable-p fn2-run-select-decode-phase mv-nth car-cons cdr-cons
                        (:e mv-nth) (:e equal) (:e zp) (:e binary-+) (:e <))))))
