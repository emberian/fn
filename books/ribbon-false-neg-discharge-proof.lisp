(in-package "ACL2")
(include-book "ribbon-false-neg-finish-proof")
(include-book "owed-discharge")
(include-book "ribbon-false-neg-hash-proof")

(local
 (defthm fn2-ribbon-checker-accepts-identity-and-length
   (let* ((step (fn2-fc-decode-step :page 0 slot gen 0 65536 9 0 1 4096 (fn2-fc-start :page 0 fn2-fields) fn2-pool)) (fields (mv-nth 2 step)))
     (implies (and (posp n) (<= n 256) (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                   (< 301 (fn2-fields-rows fn2-fields)) 
                   (fn2-ribbon-physical-headers-p n slot gen fn2-pool)
                   (fn2-ribbon-arena-p slot gen 9 0 1 65536 65536 fn2-pool) (fn2-ribbon-seal-context-p fn2-fc-context))
              (and (equal (mv-nth 0 step) :ok)
                   (natp (mv-nth 1 step)) (<= (mv-nth 1 step) *fn2-run-header-area*)
                   (equal (fn2-fc-identity 0 :page 0 65536 fn2-fc-context fields) :ok)
                   (equal (fn2-fields-value *fn2-format-page-header-field-header-length* fields) *fn2-run-header-area*)
                   (equal (fn2-fields-value *fn2-format-page-header-field-payload-length* fields)
                          (+ (- *fn2-ribbon-base* *fn2-run-header-area*) (fn2-ribbon-slots n))))))
   :hints (("Goal" :use ((:instance fn2-ribbon-checker-decodes-serialized-page (watch 0))
                       (:instance fn2-ribbon-checker-decodes-serialized-page (watch 1))
                       (:instance fn2-ribbon-checker-decodes-serialized-page (watch 2))
                       (:instance fn2-ribbon-checker-decodes-serialized-page (watch 3))
                       (:instance fn2-ribbon-checker-decodes-serialized-page (watch 4))
                       (:instance fn2-ribbon-checker-decodes-serialized-page (watch 5))
                       (:instance fn2-ribbon-checker-decodes-serialized-page (watch 6))
                       (:instance fn2-ribbon-checker-decodes-serialized-page (watch 7))
                       (:instance fn2-ribbon-checker-decodes-serialized-page (watch 8))
                       (:instance fn2-ribbon-checker-decodes-serialized-page (watch 9)))
            :in-theory (e/d (fn2-fc-identity fn2-ribbon-seal-context-p fn2-ribbon-page-values)
                      (fn2-fc-decode-step fn2-fc-start fn2-fields-value fn2-fields-rows fn2-ribbon-arena-p
                       fn2-ribbon-slots fn2-ribbon-physical-headers-p fn2-layout-range-code))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-decoded-page-enters-prefix
   (let* ((step (fn2-fc-decoded 0 :page 0 65536 0 next fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
          (after (mv-nth 1 step)))
     (implies (and (posp n) (<= n 256) (natp next) (<= next *fn2-run-header-area*)
                   (equal (fn2-fc-identity 0 :page 0 65536 fn2-fc-context fn2-fields) :ok)
                   (equal (fn2-fields-value *fn2-format-page-header-field-header-length* fn2-fields) *fn2-run-header-area*)
                   (equal (fn2-fields-value *fn2-format-page-header-field-payload-length* fn2-fields)
                          (+ (- *fn2-ribbon-base* *fn2-run-header-area*) (fn2-ribbon-slots n))))
              (and (equal (mv-nth 0 step) :more)
                   (equal (fn2-fc-phase 0 after) *fn2-fc-phase-prefix*)
                   (equal (fn2-fc-pos 0 after) 0)
                   (equal (fn2-fc-pad 0 after) (+ *fn2-ribbon-base* (fn2-ribbon-slots n)))
                   (equal (fn2-fc-pad-end 0 after) 65536)
                   (equal (fn2-fc-zero 0 after) 65536))))
   :hints (("Goal" :in-theory (e/d (fn2-fc-decoded
                       fn2-fc-phase fn2-fc-set-phase update-fn2-fc-phase$ai
                       fn2-fc-pos fn2-fc-set-pos update-fn2-fc-pos$ai
                       fn2-fc-pad fn2-fc-set-pad update-fn2-fc-pad$ai
                       fn2-fc-pad-end fn2-fc-set-pad-end update-fn2-fc-pad-end$ai
                       fn2-fc-zero fn2-fc-set-zero update-fn2-fc-zero$ai
                       fn2-fc-geom fn2-fc-set-geom update-fn2-fc-geom$ai
                       fn2-fc-previous-seal-offset fn2-fc-set-previous-seal-offset update-fn2-fc-previous-seal-offset$ai)
                       (nth update-nth fn2-ribbon-slots fn2-fc-identity fn2-fields-value))))
   :rule-classes nil))

(defthm fn2-ribbon-check-establishes-page-hash-bounds
   (let* ((run (fn2-format-run :page sealp 0 slot gen 0 65536 0 9 0 1 4096 fn2-fc fn2-fc-context fn2-b3 (fn2-fc-start :page 0 fn2-fields) fn2-pool fn2-digests))
          (after (mv-nth 1 run)))
     (implies (and (posp n) (<= n 256) (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                   (< 301 (fn2-fields-rows fn2-fields)) 
                   (fn2-ribbon-physical-headers-p n slot gen fn2-pool)
                   (fn2-ribbon-arena-p slot gen 9 0 1 65536 65536 fn2-pool) (fn2-ribbon-seal-context-p fn2-fc-context)
                   (equal (fn2-fc-phase 0 fn2-fc) *fn2-fc-phase-decode*))
              (and (equal (mv-nth 0 run) :more) (equal (mv-nth 2 run) fn2-b3)
                   (equal (mv-nth 4 run) fn2-pool) (equal (mv-nth 5 run) fn2-digests)
                   (equal (fn2-fc-phase 0 after) *fn2-fc-phase-prefix*)
                   (equal (fn2-fc-pos 0 after) 0)
                   (equal (fn2-fc-pad 0 after) (+ *fn2-ribbon-base* (fn2-ribbon-slots n)))
                   (equal (fn2-fc-pad-end 0 after) 65536)
                   (equal (fn2-fc-zero 0 after) 65536))))
   :hints (("Goal" :use (fn2-ribbon-checker-accepts-identity-and-length
                         (:instance fn2-ribbon-decoded-page-enters-prefix
                            (next (mv-nth 1 (fn2-fc-decode-step :page 0 slot gen 0 65536 9 0 1 4096 (fn2-fc-start :page 0 fn2-fields) fn2-pool))) (fn2-fields (mv-nth 2 (fn2-fc-decode-step :page 0 slot gen 0 65536 9 0 1 4096 (fn2-fc-start :page 0 fn2-fields) fn2-pool)))))
            :in-theory (e/d (fn2-format-run fn2-fc-step)
                         (fn2-fc-decoded fn2-fc-decode-step fn2-fc-start fn2-fc-identity fn2-fields-value fn2-fc-phase fn2-fc-pos
                          fn2-fc-pad fn2-fc-pad-end fn2-fc-zero fn2-ribbon-slots fn2-ribbon-physical-headers-p fn2-ribbon-arena-p
                          fn2-ribbon-seal-context-p unsigned-byte-p fn2-fields-rows))))
   :rule-classes nil)

; Each closing iteration preserves all solved bytes and extends the zero padding.
(local
 (defthm fn2-ribbon-close-step-padding-result
   (let* ((r (fn2-ribbon-close-step 0 4096 fn2-ribbon-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool))
          (next (+ cursor pos)) (k (min 4096 (- 65536 next))))
     (implies (and (< 0 (fn2-ribbon-builds-rows fn2-ribbon-builds))
                   (equal (fn2-ribbon-builds-w 0 fn2-ribbon-builds) 0)
                   (fn2-run-writerp 0 fn2-run-writers fn2-run-restarts fn2-fields)
                   (fn2-ribbon-padding-p cursor pos slot gen fn2-run-writers fn2-pool))
              (equal r
                (if (< next 65536)
                    (list :more fn2-ribbon-builds (fn2-run-writers-set-pos 0 (+ pos k) fn2-run-writers) fn2-fields
                          (mv-nth 1 (fn2-run-zero k slot gen next 9 0 1 fn2-pool)))
                  (list :more (fn2-ribbon-builds-set-phase 0 *fn2-ribbon-phase-heading* fn2-ribbon-builds)
                        (fn2-run-writers-set-phase 0 *fn2-run-writer-phase-heading* fn2-run-writers) fn2-fields fn2-pool)))))
   :hints (("Goal" :use ((:instance fn2-ribbon-zero-arena (n (min 4096 (- 65536 (+ cursor pos)))) (pos (+ cursor pos))
                                 (pk 9) (ps 0) (pg 1) (cap 65536)))
            :in-theory (e/d (fn2-ribbon-close-step fn2-run-close-step fn2-ribbon-padding-p)
                     (fn2-ribbon-arena-p fn2-ribbon-zero-arena fn2-run-writerp fn2-run-zero fn2-ribbon-builds-w fn2-ribbon-builds-rows
                      fn2-ribbon-builds-set-phase fn2-run-writers-set-pos fn2-run-writers-set-phase
                      fn2-run-writers-cursor fn2-run-writers-pos fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-okind
                      fn2-run-writers-oslot fn2-run-writers-ogen fn2-run-writers-phase fn2-run-writers-restarts))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-padding-arena-facts
   (implies (fn2-ribbon-padding-p cursor pos slot gen fn2-run-writers fn2-pool)
            (and (natp pos) (natp cursor) (<= (+ cursor pos) 65536)
                 (fn2-ribbon-arena-p slot gen 9 0 1 (+ cursor pos) 65536 fn2-pool)))
   :hints (("Goal" :in-theory (union-theories '(fn2-ribbon-padding-p) (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-next-padding-chunk
   (let* ((next (+ cursor pos)) (k (min 4096 (- 65536 next)))
          (after (mv-nth 1 (fn2-run-zero k slot gen next 9 0 1 fn2-pool))))
     (implies (and (natp cursor) (natp pos) (< next 65536) (natp slots) (equal cursor (+ *fn2-ribbon-base* slots))
                   (fn2-ribbon-arena-p slot gen 9 0 1 next 65536 fn2-pool)
                   (fn2-ribbon-solution-page-p slots slot gen fn2-ribbon-band fn2-pool)
                   (fn2-ribbon-zero-region-p pos cursor slot gen fn2-pool))
              (and (fn2-ribbon-solution-page-p slots slot gen fn2-ribbon-band after)
                   (fn2-ribbon-zero-region-p (+ pos k) cursor slot gen after))))
   :hints (("Goal" :use ((:instance fn2-ribbon-zero-arena(n (min 4096 (- 65536 (+ cursor pos))))
                         (pos (+ cursor pos)) (pk 9) (ps 0) (pg 1) (cap 65536))
                     (:instance fn2-ribbon-arena-base-natural (off (+ cursor pos)) (pk 9) (ps 0) (pg 1) (cap 65536))
                     (:instance fn2-ribbon-padding-keeps-solution (m slots) (pos (+ cursor pos)) (k (min 4096 (- 65536 (+ cursor pos)))))
                     (:instance fn2-ribbon-padding-extends-zero-region (pos (+ cursor pos)) (start cursor)
                                (k (min 4096 (- 65536 (+ cursor pos)))) (count (+ pos (min 4096 (- 65536 (+ cursor pos)))))))
            :in-theory (disable fn2-run-zero fn2-ribbon-zero-arena fn2-ribbon-arena-p fn2-ribbon-solution-page-p
                                fn2-ribbon-zero-region-p fn2-pool-base)))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-close-step-extends-solved-page
   (let* ((r (fn2-ribbon-close-step 0 4096 fn2-ribbon-builds fn2-run-writers fn2-run-restarts fn2-fields fn2-pool))
          (next (+ cursor pos)) (k (min 4096 (- 65536 next))) (pool (mv-nth 4 r)))
     (implies (and (< 0 (fn2-ribbon-builds-rows fn2-ribbon-builds)) (equal (fn2-ribbon-builds-w 0 fn2-ribbon-builds) 0)
                   (fn2-run-writerp 0 fn2-run-writers fn2-run-restarts fn2-fields)
                   (fn2-ribbon-padding-p cursor pos slot gen fn2-run-writers fn2-pool)
                   (< next 65536) (natp slots) (equal cursor (+ *fn2-ribbon-base* slots))
                   (fn2-ribbon-zero-region-p pos cursor slot gen fn2-pool)
                   (fn2-ribbon-solution-page-p slots slot gen fn2-ribbon-band fn2-pool))
              (and (equal (mv-nth 0 r) :more) (equal (mv-nth 1 r) fn2-ribbon-builds)
                   (equal (mv-nth 3 r) fn2-fields)
                   (fn2-ribbon-solution-page-p slots slot gen fn2-ribbon-band pool)
                   (fn2-ribbon-zero-region-p (+ pos k) cursor slot gen pool))))
   :hints (("Goal" :use (fn2-ribbon-close-step-padding-result fn2-ribbon-padding-arena-facts fn2-ribbon-next-padding-chunk)
            :do-not '(preprocess) :in-theory (union-theories '(mv-nth-of-cons car-cons cdr-cons (:e zp) (:e binary-+) (:e equal))
                                    (theory 'minimal-theory))))
   :rule-classes nil))

; Iterate the real 4096-byte closing steps, retaining enough fuel for the subsequent checker.
(local
 (defun fn2-ribbon-closing-invariant-p (n slot gen pos fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)
   (declare (xargs :stobjs (fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-restarts fn2-fields fn2-pool) :verify-guards nil))
   (let* ((slots (fn2-ribbon-slots n)) (cursor (+ *fn2-ribbon-base* slots)))
     (and (fn2-ribbon-build-identity-p n fn2-ribbon-builds)
          (equal (fn2-ribbon-builds-phase 0 fn2-ribbon-builds) *fn2-ribbon-phase-closing*)
          (fn2-ribbon-writer-identity-p slot gen fn2-run-writers)
          (fn2-run-writerp 0 fn2-run-writers fn2-run-restarts fn2-fields)
          (fn2-ribbon-solution-page-p slots slot gen fn2-ribbon-band fn2-pool)
          (fn2-ribbon-zero-region-p pos cursor slot gen fn2-pool)
          (fn2-ribbon-padding-p cursor pos slot gen fn2-run-writers fn2-pool)))))

(local
 (defun-nx fn2-ribbon-padding-end (fuel cursor pos slot gen writers pool)
   (declare (xargs :measure (nfix fuel)))
   (if (zp fuel) (list 0 writers pool)
     (let* ((start (+ cursor pos)) (k (min 4096 (- 65536 start))))
       (if (<= 65536 start)
           (list (1- fuel) (fn2-run-writers-set-phase 0 *fn2-run-writer-phase-heading* writers) pool)
         (fn2-ribbon-padding-end (1- fuel) cursor (+ pos k) slot gen
           (fn2-run-writers-set-pos 0 (+ pos k) writers)
           (mv-nth 1 (fn2-run-zero k slot gen start 9 0 1 pool))))))))

(local
 (defthm fn2-ribbon-position-in-writer
   (and (equal (fn2-ribbon-writer-identity-p slot gen (fn2-run-writers-set-pos 0 value fn2-run-writers))
               (fn2-ribbon-writer-identity-p slot gen fn2-run-writers))
        (implies (and (fn2-run-writerp 0 fn2-run-writers fn2-run-restarts fn2-fields) (unsigned-byte-p 32 value))
                 (fn2-run-writerp 0 (fn2-run-writers-set-pos 0 value fn2-run-writers) fn2-run-restarts fn2-fields)))
   :hints (("Goal" :in-theory (e/d (fn2-run-writers-set-pos update-fn2-run-writers-pos$ai fn2-run-writers-rows fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen fn2-run-writers-fields fn2-run-writers-page-kind fn2-run-writers-schema fn2-run-writers-run fn2-run-writers-unit fn2-run-writers-epoch fn2-run-writers-counter fn2-run-writers-history fn2-run-writers-incarnation fn2-run-writers-restarts)
                    (nth update-nth fn2-fields-wfp fn2-fields-rows fn2-run-restarts-wfp fn2-run-restarts-rows))))))

(local
 (defthm fn2-ribbon-chunk-updates-padding-state
   (let* ((start (+ cursor pos)) (k (min 4096 (- 65536 start)))
          (w (fn2-run-writers-set-pos 0 (+ pos k) fn2-run-writers)) (p (mv-nth 1 (fn2-run-zero k slot gen start 9 0 1 fn2-pool))))
     (implies (and (fn2-ribbon-padding-p cursor pos slot gen fn2-run-writers fn2-pool) (< start 65536))
              (and (unsigned-byte-p 32 (+ pos k)) (fn2-ribbon-padding-p cursor (+ pos k) slot gen w p))))
   :hints (("Goal" :use ((:instance fn2-ribbon-zero-arena (n (min 4096 (- 65536 (+ cursor pos)))) (pos (+ cursor pos)) (cap 65536)
                            (pk 9) (ps 0) (pg 1)))
            :in-theory (e/d (fn2-run-writers-set-pos update-fn2-run-writers-pos$ai
                               fn2-run-writers-phase fn2-run-writers-restarts fn2-run-writers-pos fn2-run-writers-cursor fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen)
                         (fn2-ribbon-arena-p fn2-ribbon-zero-arena fn2-run-zero nth update-nth))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-one-padding-chunk-preserves-invariant
   (let* ((cursor (+ *fn2-ribbon-base* (fn2-ribbon-slots n))) (start (+ cursor pos))
          (k (min 4096 (- 65536 start))) (w (fn2-run-writers-set-pos 0 (+ pos k) fn2-run-writers))
          (p (mv-nth 1 (fn2-run-zero k slot gen start 9 0 1 fn2-pool))))
     (implies (and (fn2-ribbon-closing-invariant-p n slot gen pos fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-restarts fn2-fields fn2-pool) (< start 65536))
              (fn2-ribbon-closing-invariant-p n slot gen (+ pos k) fn2-ribbon-builds fn2-ribbon-band w fn2-run-restarts fn2-fields p)))
   :hints (("Goal" :use ((:instance fn2-ribbon-chunk-updates-padding-state (cursor (+ *fn2-ribbon-base* (fn2-ribbon-slots n))))
                         (:instance fn2-ribbon-padding-arena-facts (cursor (+ *fn2-ribbon-base* (fn2-ribbon-slots n))))
                         (:instance fn2-ribbon-next-padding-chunk (slots (fn2-ribbon-slots n)) (cursor (+ *fn2-ribbon-base* (fn2-ribbon-slots n)))))
            :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-closing-invariant-p fn2-ribbon-position-in-writer
                                 (:t fn2-ribbon-slots) natp (:e not) (:e equal)) (theory 'minimal-theory))))
   :rule-classes nil))

(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

(local
 (defthm fn2-ribbon-closing-drive-one-step
   (let* ((cursor (+ *fn2-ribbon-base* (fn2-ribbon-slots n))) (start (+ cursor pos))
          (k (min 4096 (- 65536 start))))
     (implies (and (posp fuel) (fn2-ribbon-closing-invariant-p n slot gen pos fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-restarts fn2-fields fn2-pool))
              (equal (fn2-rba-call fn2-rba-drive fuel)
                (if (< start 65536)
                    (fn2-rba-drive (1- fuel) fn2-ribbon-builds fn2-ribbon-band
                         (fn2-run-writers-set-pos 0 (+ pos k) fn2-run-writers) fn2-run-restarts fn2-fields
                         (mv-nth 1 (fn2-run-zero k slot gen start 9 0 1 fn2-pool)) fn2-fc fn2-fc-context fn2-b3 fn2-digests)
                  (fn2-rba-drive (1- fuel) (fn2-ribbon-builds-set-phase 0 *fn2-ribbon-phase-heading* fn2-ribbon-builds)
                         fn2-ribbon-band (fn2-run-writers-set-phase 0 *fn2-run-writer-phase-heading* fn2-run-writers)
                         fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)))))
   :hints (("Goal" :use ((:instance fn2-ribbon-close-step-padding-result (cursor (+ *fn2-ribbon-base* (fn2-ribbon-slots n)))))
            :expand ((fn2-rba-call fn2-rba-drive fuel)) :do-not '(preprocess)
            :in-theory (union-theories '(fn2-ribbon-closing-invariant-p fn2-ribbon-build-identity-p fn2-ribbon-work
                             (:e posp) (:e natp) (:e equal) (:e not) (:e binary-+) (:e zp) (:compound-recognizer zp-compound-recognizer) zp-open posp mv-nth-of-cons car-cons cdr-cons)
                         (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-fuel-for-next-chunk
   (let* ((start (+ cursor pos)) (k (min 4096 (- 65536 start))))
     (implies (and (natp cursor) (natp pos) (natp fuel) (natp reserve) (< reserve fuel) (< start 65536)
                   (<= (- 65536 start) (* 4096 (+ -1 fuel (- reserve)))))
              (and (natp (1- fuel)) (< reserve (1- fuel))
                   (<= (- 65536 (+ cursor (+ pos k))) (* 4096 (+ -1 (1- fuel) (- reserve)))))))
   :hints (("Goal" :cases ((equal fuel (1+ reserve)))))
   :rule-classes nil))

(local
 (defun fn2-ribbon-heading-invariant-p (n slot gen fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-pool)
   (declare (xargs :stobjs (fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-pool) :verify-guards nil))
   (let* ((slots (fn2-ribbon-slots n)) (cursor (+ *fn2-ribbon-base* slots)))
     (and (fn2-ribbon-build-identity-p n fn2-ribbon-builds)
          (equal (fn2-ribbon-builds-phase 0 fn2-ribbon-builds) *fn2-ribbon-phase-heading*)
          (fn2-ribbon-writer-identity-p slot gen fn2-run-writers)
          (equal (fn2-run-writers-phase 0 fn2-run-writers) *fn2-run-writer-phase-heading*)
          (equal (fn2-run-writers-cursor 0 fn2-run-writers) cursor)
          (fn2-ribbon-solution-page-p slots slot gen fn2-ribbon-band fn2-pool)
          (fn2-ribbon-zero-region-p (- 65536 cursor) cursor slot gen fn2-pool)
          (fn2-ribbon-arena-p slot gen 9 0 1 65536 65536 fn2-pool)))))

(local
 (defthm fn2-ribbon-heading-phase-observations
   (let ((w (fn2-run-writers-set-phase 0 phase fn2-run-writers)) (b (fn2-ribbon-builds-set-phase 0 phase fn2-ribbon-builds)))
     (and (equal (fn2-ribbon-writer-identity-p slot gen w) (fn2-ribbon-writer-identity-p slot gen fn2-run-writers))
          (equal (fn2-run-writers-phase 0 w) phase) (equal (fn2-run-writers-cursor 0 w) (fn2-run-writers-cursor 0 fn2-run-writers))
          (equal (fn2-ribbon-builds-phase 0 b) phase)))
   :hints (("Goal" :in-theory (e/d (fn2-run-writers-phase fn2-run-writers-set-phase update-fn2-run-writers-phase$ai
                               fn2-run-writers-cursor fn2-ribbon-builds-set-phase fn2-ribbon-builds-phase update-fn2-ribbon-builds-phase$ai
                               fn2-run-writers-rows fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen fn2-run-writers-fields fn2-run-writers-page-kind fn2-run-writers-schema fn2-run-writers-run fn2-run-writers-unit fn2-run-writers-epoch fn2-run-writers-counter fn2-run-writers-history fn2-run-writers-incarnation fn2-run-writers-restarts) (nth update-nth))))))

(local
 (defthm fn2-ribbon-end-of-padding-contents
   (implies (and (fn2-ribbon-padding-p cursor pos slot gen fn2-run-writers fn2-pool)
                 (<= 65536 (+ cursor pos)) (fn2-ribbon-zero-region-p pos cursor slot gen fn2-pool))
            (and (equal (fn2-run-writers-cursor 0 fn2-run-writers) cursor)
                 (fn2-ribbon-zero-region-p (- 65536 cursor) cursor slot gen fn2-pool)
                 (fn2-ribbon-arena-p slot gen 9 0 1 65536 65536 fn2-pool)))
   :hints (("Goal" :cases ((equal pos (- 65536 cursor)))
            :in-theory (disable fn2-ribbon-arena-p fn2-ribbon-zero-region-p fn2-run-writers-phase fn2-run-writers-restarts fn2-run-writers-pos fn2-run-writers-cursor fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen)))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-padding-at-end-prepares-heading
   (implies (and (fn2-ribbon-closing-invariant-p n slot gen pos fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)
                 (<= 65536 (+ (+ *fn2-ribbon-base* (fn2-ribbon-slots n)) pos)))
            (fn2-ribbon-heading-invariant-p n slot gen (fn2-ribbon-builds-set-phase 0 *fn2-ribbon-phase-heading* fn2-ribbon-builds)
               fn2-ribbon-band (fn2-run-writers-set-phase 0 *fn2-run-writer-phase-heading* fn2-run-writers) fn2-pool))
   :hints (("Goal" :use ((:instance fn2-ribbon-end-of-padding-contents (cursor (+ *fn2-ribbon-base* (fn2-ribbon-slots n)))))
            :in-theory (union-theories '(fn2-ribbon-closing-invariant-p fn2-ribbon-heading-invariant-p
                      fn2-ribbon-heading-phase-observations fn2-ribbon-build-identity-across-phase-and-index)
                      (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-closing-invariant-counters
   (implies (fn2-ribbon-closing-invariant-p n slot gen pos fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)
            (and (natp (+ *fn2-ribbon-base* (fn2-ribbon-slots n))) (natp pos)))
   :hints (("Goal" :use ((:instance fn2-ribbon-padding-arena-facts (cursor (+ *fn2-ribbon-base* (fn2-ribbon-slots n)))))
            :in-theory (union-theories '(fn2-ribbon-closing-invariant-p) (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-all-padding-reaches-heading
   (let ((end (fn2-ribbon-padding-end fuel cursor pos slot gen fn2-run-writers fn2-pool)) (b (fn2-ribbon-builds-set-phase 0 *fn2-ribbon-phase-heading* fn2-ribbon-builds)))
     (implies (and (equal cursor (+ *fn2-ribbon-base* (fn2-ribbon-slots n))) (fn2-ribbon-closing-invariant-p n slot gen pos fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)
                   (natp fuel) (natp reserve) (< reserve fuel)
                   (<= (- 65536 (+ cursor pos)) (* 4096 (+ -1 fuel (- reserve)))))
              (and (natp (mv-nth 0 end)) (<= reserve (mv-nth 0 end))
                   (fn2-ribbon-heading-invariant-p n slot gen b fn2-ribbon-band (mv-nth 1 end) (mv-nth 2 end))
                   (equal (fn2-rba-call fn2-rba-drive fuel)
                          (fn2-rba-drive (mv-nth 0 end) b fn2-ribbon-band (mv-nth 1 end) fn2-run-restarts fn2-fields
                              (mv-nth 2 end) fn2-fc fn2-fc-context fn2-b3 fn2-digests)))))
   :hints (("Goal" :induct (fn2-ribbon-padding-end fuel cursor pos slot gen fn2-run-writers fn2-pool) :expand ((fn2-ribbon-padding-end fuel cursor pos slot gen fn2-run-writers fn2-pool)) :do-not '(preprocess)
            :in-theory (disable (:definition fn2-ribbon-padding-end) fn2-ribbon-closing-invariant-p fn2-ribbon-heading-invariant-p
                                 fn2-ribbon-slots fn2-rba-drive fn2-ribbon-builds-set-phase fn2-run-writers-set-phase
                                 fn2-run-writers-set-pos fn2-run-zero))
           ("Subgoal *1/3" :use (fn2-ribbon-closing-drive-one-step fn2-ribbon-one-padding-chunk-preserves-invariant
                                  fn2-ribbon-closing-invariant-counters fn2-ribbon-fuel-for-next-chunk))
           ("Subgoal *1/2" :use (fn2-ribbon-closing-drive-one-step fn2-ribbon-padding-at-end-prepares-heading)))
   :rule-classes nil))

; Carry the constructed page through the remaining zero padding to the header writer.
(local
 (defthm fn2-ribbon-index-preserves-phase
   (equal (fn2-ribbon-builds-phase 0 (fn2-ribbon-builds-set-i 0 i fn2-ribbon-builds)) (fn2-ribbon-builds-phase 0 fn2-ribbon-builds))
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-builds-phase fn2-ribbon-builds-set-i update-fn2-ribbon-builds-i$ai) (nth update-nth))))))

(local
 (defthm fn2-ribbon-emission-metadata
   (let* ((emit (fn2-ribbon-emit-step 0 4096 fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-pool))
          (w (mv-nth 2 emit)) (b (mv-nth 1 emit)))
     (implies (and (fn2-run-writers-wfp fn2-run-writers) (fn2-ribbon-build-identity-p n fn2-ribbon-builds)
                   (equal (fn2-ribbon-builds-w 0 fn2-ribbon-builds) 0) (equal (mv-nth 0 emit) :more)
                   (equal (fn2-run-writers-phase 0 w) *fn2-run-writer-phase-closing*))
              (and (fn2-run-writers-wfp w) (fn2-ribbon-build-identity-p n b)
                   (equal (fn2-ribbon-builds-phase 0 b) *fn2-ribbon-phase-closing*))))
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-emit-step fn2-run-close)
                    (fn2-ribbon-build-identity-p fn2-ribbon-builds-i fn2-ribbon-builds-w fn2-ribbon-builds-rows
                     fn2-ribbon-builds-set-i fn2-ribbon-builds-set-phase fn2-ribbon-builds-phase fn2-ribbon-emit-bytes
                     fn2-run-writers-set-phase fn2-run-writers-set-pos fn2-run-writers-set-cursor fn2-run-writers-wfp
                     fn2-run-writers-rows fn2-run-writers-phase unsigned-byte-p))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-opened-writer-wfp
   (fn2-run-writers-wfp (mv-nth 1 (fn2-ribbon-opened-writer)))
   :hints (("Goal" :in-theory (union-theories '(fn2-run-open-preserves-wfp fn2-run-writers-init-preserves-type create-fn2-run-writers-type fn2-run-writers-init-wfp (:e natp) (:e <)
                        fn2-run-writers-init-rows) (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-initial-checker-and-restart-tables
   (let* ((st (fn2-ribbon-fresh-state n)) (restarts (mv-nth 4 st)) (fc (mv-nth 7 st)) (ctx (mv-nth 8 st))
          (b3 (mv-nth 9 st)) (ds (mv-nth 10 st)))
     (and (fn2-run-restarts-wfp restarts) (equal (fn2-run-restarts-rows restarts) *fn2-run-restart-capacity*)
          (equal (fn2-fc-phase 0 fc) *fn2-fc-phase-idle*) (equal (fn2-fc-rows fc) 1)
          (equal (fn2-fc-context-rows ctx) 1) (fn2-b3-ready 0 b3 ds) (fn2-digest-rowp 136 ds)))
   :hints (("Goal" :expand ((create-fn2-fc) (create-fn2-fc-context) (create-fn2-digests) (create-fn2-b3)) :in-theory (union-theories '(fn2-ribbon-fresh-state fn2-rba-setup mv-nth-of-cons car-cons cdr-cons
                            (:e zp) (:e binary-+) (:e fn2-fc-phase) (:e fn2-fc-rows) (:e fn2-fc-context-rows)
                            (:e create-fn2-fc) (:e create-fn2-fc-context) (:e create-fn2-b3) (:e create-fn2-digests)
                            (:e make-list-ac) (:e cons) (:e create-fn2-run-restarts) (:e fn2-digests-init) (:e fn2-b3-table-init) (:e fn2-fc-init)
                            (:e fn2-fc-context-init) (:e fn2-b3-ready) (:e fn2-digest-rowp)
                            fn2-run-restarts-init-wfp fn2-run-restarts-init-rows (:e natp) (:e <))
                           (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-resource-rows-make-writer
   (implies (and (fn2-ribbon-writer-identity-p slot gen fn2-run-writers) (fn2-run-writers-wfp fn2-run-writers)
                 (fn2-fields-wfp fn2-fields) (equal (fn2-fields-rows fn2-fields) 400)
                 (fn2-run-restarts-wfp fn2-run-restarts) (equal (fn2-run-restarts-rows fn2-run-restarts) *fn2-run-restart-capacity*))
            (fn2-run-writerp 0 fn2-run-writers fn2-run-restarts fn2-fields))
   :hints (("Goal" :in-theory (union-theories '(fn2-ribbon-writer-identity-p fn2-run-writerp (:e natp) (:e binary-+)
                            (:e binary-*) (:e <) (:e equal)) (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-solved-build-identity
   (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256))
            (fn2-ribbon-build-identity-p (len keys) (mv-nth 1 (fn2-ribbon-solved-step keys))))
   :hints (("Goal" :use (fn2-ribbon-fresh-added-environment fn2-ribbon-fresh-finish-enters-emitter fn2-ribbon-fresh-adds-solve-key-equations
                       (:instance fn2-ribbon-finish-starts-solve (slots (fn2-ribbon-slots (len keys))) (seed (fn2-ribbon-seed 7)) (fn2-ribbon-builds (mv-nth 1 (fn2-ribbon-added-state keys))))
                       (:instance fn2-ribbon-solve-maintains-emitter-inputs (n (len keys)) (slots (fn2-ribbon-slots (len keys))) (seed (fn2-ribbon-seed 7))
                                    (fn2-ribbon-builds (mv-nth 1 (fn2-ribbon-finish 0 (mv-nth 1 (fn2-ribbon-added-state keys))))) (fn2-ribbon-band (mv-nth 2 (fn2-ribbon-added-state keys)))))
            :in-theory (union-theories '(fn2-ribbon-insertion-environment-p fn2-ribbon-solved-step fn2-ribbon-finish-maintains-identity)
                          (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-padding-writer-phase
   (implies (fn2-ribbon-padding-p cursor pos slot gen fn2-run-writers fn2-pool)
            (equal (fn2-run-writers-phase 0 fn2-run-writers) *fn2-run-writer-phase-closing*))
   :hints (("Goal" :in-theory (union-theories '(fn2-ribbon-padding-p) (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-build-writer-row
   (implies (fn2-ribbon-build-identity-p n fn2-ribbon-builds) (equal (fn2-ribbon-builds-w 0 fn2-ribbon-builds) 0))
   :hints (("Goal" :in-theory (union-theories '(fn2-ribbon-build-identity-p) (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-image-enters-padding-invariant
   (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256))
            (fn2-ribbon-closing-invariant-p (len keys) 0 1 0 (mv-nth 1 (fn2-ribbon-emitted-step keys)) (mv-nth 2 (fn2-ribbon-solved-step keys)) (mv-nth 2 (fn2-ribbon-emitted-step keys)) (mv-nth 4 (fn2-ribbon-added-state keys)) (mv-nth 5 (fn2-ribbon-added-state keys)) (mv-nth 3 (fn2-ribbon-emitted-step keys))))
   :hints (("Goal" :use (fn2-ribbon-solved-build-identity fn2-ribbon-fresh-added-environment fn2-ribbon-fresh-keys-produce-solution-page
                     fn2-ribbon-opened-writer-wfp (:instance fn2-ribbon-initial-checker-and-restart-tables (n (len keys)))
                     (:instance fn2-ribbon-build-writer-row (n (len keys)) (fn2-ribbon-builds (mv-nth 1 (fn2-ribbon-solved-step keys))))
                     (:instance fn2-ribbon-emission-metadata (n (len keys)) (fn2-ribbon-builds (mv-nth 1 (fn2-ribbon-solved-step keys)))
                         (fn2-ribbon-band (mv-nth 2 (fn2-ribbon-solved-step keys))) (fn2-run-writers (mv-nth 3 (fn2-ribbon-added-state keys))) (fn2-pool (mv-nth 6 (fn2-ribbon-added-state keys))))
                     (:instance fn2-ribbon-padding-writer-phase (cursor (+ *fn2-ribbon-base* (fn2-ribbon-slots (len keys)))) (slot 0) (gen 1) (pos 0)
                         (fn2-run-writers (mv-nth 2 (fn2-ribbon-emitted-step keys))) (fn2-pool (mv-nth 3 (fn2-ribbon-emitted-step keys))))
                     (:instance fn2-ribbon-resource-rows-make-writer (slot 0) (gen 1)
                         (fn2-run-writers (mv-nth 2 (fn2-ribbon-emitted-step keys))) (fn2-fields (mv-nth 5 (fn2-ribbon-added-state keys))) (fn2-run-restarts (mv-nth 4 (fn2-ribbon-added-state keys)))))
            :do-not '(preprocess) :expand ((:free (a b c pool) (fn2-ribbon-zero-region-p 0 a b c pool)))
            :in-theory (union-theories '(fn2-ribbon-closing-invariant-p fn2-ribbon-emitted-step (:e zp) (:e equal) (:e not))
                          (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defun-nx fn2-ribbon-padded-state (keys)
   (let ((emit (fn2-ribbon-emitted-step keys)))
     (fn2-ribbon-padding-end 99998 (+ *fn2-ribbon-base* (fn2-ribbon-slots (len keys))) 0 0 1 (mv-nth 2 emit) (mv-nth 3 emit)))))

(local
 (defthm fn2-ribbon-adapter-fuel-for-page
   (implies (and (posp n) (<= n 256))
            (<= (- 65536 (+ (+ *fn2-ribbon-base* (fn2-ribbon-slots n)) 0)) (* 4096 (+ -1 99998 (- 90000)))))
   :hints (("Goal" :in-theory (disable fn2-ribbon-slots)))))

(local
 (defthm fn2-ribbon-image-reaches-heading
   (let ((p (fn2-ribbon-padded-state keys)) (b (fn2-ribbon-builds-set-phase 0 *fn2-ribbon-phase-heading* (mv-nth 1 (fn2-ribbon-emitted-step keys)))) (z (mv-nth 2 (fn2-ribbon-solved-step keys))) (a (fn2-ribbon-added-state keys)))
     (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256))
              (and (natp (mv-nth 0 p)) (<= 90000 (mv-nth 0 p))
                   (fn2-ribbon-heading-invariant-p (len keys) 0 1 b z (mv-nth 1 p) (mv-nth 2 p))
                   (equal (fn2-ribbon-final-drive keys)
                      (fn2-ribbon-call-with-state fn2-rba-drive ((mv-nth 0 p)) a
                           (1 b) (2 z) (3 (mv-nth 1 p)) (6 (mv-nth 2 p)))))))
   :hints (("Goal" :use (fn2-ribbon-final-drive-reaches-closing fn2-ribbon-image-enters-padding-invariant
                      (:instance fn2-ribbon-adapter-fuel-for-page (n (len keys)))
                      (:instance fn2-ribbon-all-padding-reaches-heading (n (len keys)) (cursor (+ *fn2-ribbon-base* (fn2-ribbon-slots (len keys)))) (fuel 99998) (reserve 90000)
                        (pos 0) (slot 0) (gen 1) (fn2-ribbon-builds (mv-nth 1 (fn2-ribbon-emitted-step keys)))
                     (fn2-ribbon-band (mv-nth 2 (fn2-ribbon-solved-step keys)))
                     (fn2-run-writers (mv-nth 2 (fn2-ribbon-emitted-step keys)))
                     (fn2-run-restarts (mv-nth 4 (fn2-ribbon-added-state keys)))
                     (fn2-fields (mv-nth 5 (fn2-ribbon-added-state keys)))
                     (fn2-pool (mv-nth 3 (fn2-ribbon-emitted-step keys)))
                     (fn2-fc (mv-nth 7 (fn2-ribbon-added-state keys)))
                     (fn2-fc-context (mv-nth 8 (fn2-ribbon-added-state keys)))
                     (fn2-b3 (mv-nth 9 (fn2-ribbon-added-state keys)))
                     (fn2-digests (mv-nth 10 (fn2-ribbon-added-state keys)))))
            :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-padded-state (:e natp) (:e <) (:e equal))
                                     (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defun-nx fn2-ribbon-headed-step (keys)
   (let ((a (fn2-ribbon-added-state keys)) (p (fn2-ribbon-padded-state keys)))
     (fn2-ribbon-head 0 (fn2-ribbon-builds-set-phase 0 *fn2-ribbon-phase-heading* (mv-nth 1 (fn2-ribbon-emitted-step keys))) (mv-nth 1 p) (mv-nth 5 a) (mv-nth 2 p) (mv-nth 8 a)))))

; Write both headers and enter the page hash with the decoded length and padding bounds.
(local
 (defthm fn2-ribbon-image-writes-page-headers
   (let ((h (fn2-ribbon-headed-step keys)) (z (mv-nth 2 (fn2-ribbon-solved-step keys))) (n (len keys)))
     (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256))
       (and (equal (mv-nth 0 h) :more)
            (fn2-ribbon-build-identity-p n (mv-nth 1 h))
            (equal (fn2-ribbon-builds-phase 0 (mv-nth 1 h)) *fn2-ribbon-phase-sealing*)
            (fn2-ribbon-writer-identity-p 0 1 (mv-nth 2 h))
            (equal (fn2-run-writers-phase 0 (mv-nth 2 h)) *fn2-run-writer-phase-sealing*)
            (equal (fn2-fields-rows (mv-nth 3 h)) 400)
            (fn2-ribbon-arena-p 0 1 9 0 1 65536 65536 (mv-nth 4 h))
            (fn2-ribbon-physical-headers-p n 0 1 (mv-nth 4 h))
            (fn2-ribbon-solution-page-p (fn2-ribbon-slots n) 0 1 z (mv-nth 4 h))
            (equal (mv-nth 5 h) (fn2-run-seal-context 0 0 136 (mv-nth 2 h) (mv-nth 8 (fn2-ribbon-added-state keys))))
            (fn2-ribbon-seal-context-p (mv-nth 5 h)))))
   :hints (("Goal" :use (fn2-ribbon-image-reaches-heading fn2-ribbon-fresh-added-environment
                (:instance fn2-ribbon-initial-checker-and-restart-tables (n (len keys)))
                (:instance fn2-ribbon-prepares-seal-context (slot 0) (gen 1) (fn2-run-writers (fn2-run-writers-set-phase 0 *fn2-run-writer-phase-sealing* (mv-nth 1 (fn2-ribbon-padded-state keys)))) (fn2-fc-context (mv-nth 8 (fn2-ribbon-added-state keys))))
                (:instance fn2-ribbon-heading-establishes-serialized-solution
                  (n (len keys)) (slots (fn2-ribbon-slots (len keys))) (slot 0) (gen 1)
                  (fn2-ribbon-builds (fn2-ribbon-builds-set-phase 0 *fn2-ribbon-phase-heading* (mv-nth 1 (fn2-ribbon-emitted-step keys)))) (fn2-run-writers (mv-nth 1 (fn2-ribbon-padded-state keys))) (fn2-fields (mv-nth 5 (fn2-ribbon-added-state keys)))
                  (fn2-pool (mv-nth 2 (fn2-ribbon-padded-state keys))) (fn2-fc-context (mv-nth 8 (fn2-ribbon-added-state keys))) (fn2-ribbon-band (mv-nth 2 (fn2-ribbon-solved-step keys)))))
            :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-headed-step fn2-ribbon-heading-invariant-p
               fn2-ribbon-heading-phase-observations fn2-ribbon-build-identity-across-phase-and-index (:e <) (:e equal))
               (theory 'minimal-theory)))) :rule-classes nil))

(local
 (defthm fn2-ribbon-drive-writes-headers
   (let ((h (fn2-ribbon-head 0 fn2-ribbon-builds fn2-run-writers fn2-fields fn2-pool fn2-fc-context)))
     (implies (and (posp fuel) (< 0 (fn2-ribbon-builds-rows fn2-ribbon-builds))
                   (equal (fn2-ribbon-builds-phase 0 fn2-ribbon-builds) *fn2-ribbon-phase-heading*)
                   (equal (mv-nth 0 h) :more))
              (equal (fn2-rba-call fn2-rba-drive fuel)
                     (fn2-rba-drive (1- fuel) (mv-nth 1 h) fn2-ribbon-band (mv-nth 2 h) fn2-run-restarts
                       (mv-nth 3 h) (mv-nth 4 h) fn2-fc (mv-nth 5 h) fn2-b3 fn2-digests))))
   :hints (("Goal" :expand ((fn2-rba-call fn2-rba-drive fuel))
            :in-theory (e/d (fn2-ribbon-work) (fn2-rba-drive fn2-ribbon-head fn2-ribbon-builds-rows fn2-ribbon-builds-phase))))
   :rule-classes nil))

(local
 (defun-nx fn2-ribbon-sealing-state (keys)
   (let ((h (fn2-ribbon-headed-step keys)) (a (fn2-ribbon-added-state keys)))
     (fn2-ribbon-call-with-state list (:more) a
       (1 (mv-nth 1 h)) (2 (mv-nth 2 (fn2-ribbon-solved-step keys))) (3 (mv-nth 2 h))
       (5 (mv-nth 3 h)) (6 (mv-nth 4 h)) (8 (mv-nth 5 h))))))

(local
 (defthm fn2-ribbon-image-reaches-sealing
   (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256))
     (equal (fn2-ribbon-final-drive keys)
            (fn2-ribbon-call-with-state fn2-rba-drive ((1- (mv-nth 0 (fn2-ribbon-padded-state keys)))) (fn2-ribbon-sealing-state keys))))
   :hints (("Goal" :use (fn2-ribbon-image-reaches-heading fn2-ribbon-image-writes-page-headers
                      (:instance fn2-ribbon-drive-writes-headers (fuel (mv-nth 0 (fn2-ribbon-padded-state keys)))
                  (fn2-ribbon-builds (fn2-ribbon-builds-set-phase 0 *fn2-ribbon-phase-heading* (mv-nth 1 (fn2-ribbon-emitted-step keys))))
                  (fn2-ribbon-band (mv-nth 2 (fn2-ribbon-solved-step keys)))
                  (fn2-run-writers (mv-nth 1 (fn2-ribbon-padded-state keys)))
                  (fn2-run-restarts (mv-nth 4 (fn2-ribbon-added-state keys)))
                  (fn2-fields (mv-nth 5 (fn2-ribbon-added-state keys)))
                  (fn2-pool (mv-nth 2 (fn2-ribbon-padded-state keys)))
                  (fn2-fc (mv-nth 7 (fn2-ribbon-added-state keys)))
                  (fn2-fc-context (mv-nth 8 (fn2-ribbon-added-state keys)))
                  (fn2-b3 (mv-nth 9 (fn2-ribbon-added-state keys)))
                  (fn2-digests (mv-nth 10 (fn2-ribbon-added-state keys)))))
            :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-sealing-state fn2-ribbon-heading-invariant-p
                   fn2-ribbon-build-identity-p fn2-ribbon-headed-step mv-nth-of-cons (:e zp) (:e binary-+)
                   (:e mv-nth) car-cons cdr-cons natp posp (:e <)) (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-context-rows-after-preparation
   (equal (fn2-fc-context-rows (fn2-run-seal-context w row hrow fn2-run-writers fn2-fc-context))
          (fn2-fc-context-rows fn2-fc-context))
   :hints (("Goal" :in-theory (e/d (fn2-run-seal-context fn2-fc-context-rows fn2-fc-context-set-location update-fn2-fc-context-location$ai
                 fn2-fc-context-set-allocation update-fn2-fc-context-allocation$ai
                 fn2-fc-context-set-history update-fn2-fc-context-history$ai
                 fn2-fc-context-set-incarnation update-fn2-fc-context-incarnation$ai
                 fn2-fc-context-set-writer-epoch update-fn2-fc-context-writer-epoch$ai
                 fn2-fc-context-set-page-kind update-fn2-fc-context-page-kind$ai
                 fn2-fc-context-set-encoded-length update-fn2-fc-context-encoded-length$ai
                 fn2-fc-context-set-hash update-fn2-fc-context-hash$ai
                 fn2-fc-context-set-geometry update-fn2-fc-context-geometry$ai
                 fn2-fc-context-set-previous-seal update-fn2-fc-context-previous-seal$ai) (nth update-nth))))))

(local
 (defun fn2-ribbon-sealing-resources-p (n slot gen fn2-ribbon-builds fn2-run-writers fn2-fields fn2-fc fn2-fc-context fn2-b3 fn2-digests)
   (declare (xargs :stobjs (fn2-ribbon-builds fn2-run-writers fn2-fields fn2-fc fn2-fc-context fn2-b3 fn2-digests) :verify-guards nil))
   (and (fn2-ribbon-build-identity-p n fn2-ribbon-builds)
        (equal (fn2-ribbon-builds-phase 0 fn2-ribbon-builds) *fn2-ribbon-phase-sealing*)
        (fn2-ribbon-writer-identity-p slot gen fn2-run-writers)
        (equal (fn2-run-writers-phase 0 fn2-run-writers) *fn2-run-writer-phase-sealing*)
        (fn2-ribbon-seal-context-p fn2-fc-context)
        (< 0 (fn2-fc-context-rows fn2-fc-context)) (< 0 (fn2-fc-rows fn2-fc))
        (< 301 (fn2-fields-rows fn2-fields)) (fn2-b3-ready 0 fn2-b3 fn2-digests)
        (fn2-digest-rowp 136 fn2-digests))))

(local
 (defthm fn2-ribbon-image-sealing-resources
   (let ((st (fn2-ribbon-sealing-state keys)))
     (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256))
       (and (fn2-ribbon-sealing-resources-p (len keys) 0 1 (mv-nth 1 st) (mv-nth 3 st) (mv-nth 5 st) (mv-nth 7 st) (mv-nth 8 st) (mv-nth 9 st) (mv-nth 10 st)) (equal (fn2-fc-phase 0 (mv-nth 7 st)) *fn2-fc-phase-idle*))))
   :hints (("Goal" :use (fn2-ribbon-image-writes-page-headers fn2-ribbon-fresh-added-environment
                         (:instance fn2-ribbon-initial-checker-and-restart-tables (n (len keys))))
            :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-sealing-resources-p fn2-ribbon-sealing-state
                  fn2-ribbon-context-rows-after-preparation mv-nth-of-cons (:e zp) (:e binary-+) (:e mv-nth)
                  car-cons cdr-cons (:e <)) (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-lower-digest-row-available
   (implies (and (fn2-digest-rowp 136 fn2-digests) (natp r) (<= r 136)) (fn2-digest-rowp r fn2-digests))
   :hints (("Goal" :in-theory (e/d (fn2-digest-rowp) (fn2-digests-rows fn2-digests-wfp))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-sealing-continues-format-run
   (let ((run (fn2-format-run :page t 0 slot gen 0 65536 0 9 0 1 4096 fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
     (implies (and (fn2-ribbon-sealing-resources-p n slot gen fn2-ribbon-builds fn2-run-writers fn2-fields fn2-fc fn2-fc-context fn2-b3 fn2-digests) (equal (mv-nth 0 run) :more))
              (equal (fn2-ribbon-seal 0 4096 fn2-ribbon-builds fn2-run-writers fn2-fc fn2-fc-context
                             fn2-b3 fn2-fields fn2-pool fn2-digests)
                     (list :more fn2-ribbon-builds fn2-run-writers (mv-nth 1 run) (mv-nth 2 run)
                           (mv-nth 3 run) (mv-nth 4 run) (mv-nth 5 run)))))
   :hints (("Goal" :use ((:instance fn2-ribbon-lower-digest-row-available (r (fn2-digest-slot 0 *fn2-fc-geometry*)))
                          (:instance fn2-ribbon-lower-digest-row-available (r (fn2-digest-slot 0 *fn2-fc-previous-seal*))))
            :in-theory (union-theories '(fn2-ribbon-seal fn2-run-seal-step fn2-ribbon-sealing-resources-p fn2-ribbon-build-identity-p
                       fn2-ribbon-writer-identity-p fn2-ribbon-seal-context-p (:e equal) (:e <) (:e natp)
                       (:e fn2-digest-slot) (:e binary-+) (:e not) (:e if)) (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-drive-continues-format-run
   (let ((run (fn2-format-run :page t 0 slot gen 0 65536 0 9 0 1 4096 fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
     (implies (and (posp fuel) (fn2-ribbon-sealing-resources-p n slot gen fn2-ribbon-builds fn2-run-writers fn2-fields fn2-fc fn2-fc-context fn2-b3 fn2-digests) (equal (mv-nth 0 run) :more))
              (equal (fn2-rba-call fn2-rba-drive fuel)
                     (fn2-rba-drive (1- fuel) fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-restarts
                       (mv-nth 3 run) (mv-nth 4 run) (mv-nth 1 run) fn2-fc-context (mv-nth 2 run) (mv-nth 5 run)))))
   :hints (("Goal" :use fn2-ribbon-sealing-continues-format-run
            :expand ((fn2-rba-call fn2-rba-drive fuel))
            :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-work fn2-ribbon-sealing-resources-p fn2-ribbon-build-identity-p
               mv-nth-of-cons car-cons cdr-cons (:e natp) (:e <) (:e zp) (:e binary-+) (:e equal) (:e not) zp-open posp
               (:compound-recognizer zp-compound-recognizer)) (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-fresh-hash-after-init
   (let* ((st (fn2-ribbon-fresh-state n)) (init (fn2-b3-init 0 0 (fn2-digest-slot 0 *fn2-b3-key*) (mv-nth 10 st) (mv-nth 9 st))))
     (and (fn2-b3-ready 0 (mv-nth 1 init) (mv-nth 0 init)) (fn2-digest-rowp 136 (mv-nth 0 init))))
   :hints (("Goal" :expand ((create-fn2-fc) (create-fn2-fc-context) (create-fn2-digests) (create-fn2-b3)) :in-theory (union-theories '(fn2-ribbon-fresh-state fn2-rba-setup mv-nth-of-cons car-cons cdr-cons
                            (:e zp) (:e binary-+) (:e fn2-fc-phase) (:e fn2-fc-rows) (:e fn2-fc-context-rows)
                            (:e create-fn2-fc) (:e create-fn2-fc-context) (:e create-fn2-b3) (:e create-fn2-digests)
                            (:e make-list-ac) (:e cons) (:e fn2-digest-slot) (:e fn2-b3-init) (:e mv-nth) (:e create-fn2-run-restarts) (:e fn2-digests-init) (:e fn2-b3-table-init) (:e fn2-fc-init)
                            (:e fn2-fc-context-init) (:e fn2-b3-ready) (:e fn2-digest-rowp)
                            fn2-run-restarts-init-wfp fn2-run-restarts-init-rows (:e natp) (:e <))
                           (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defun-nx fn2-ribbon-next-sealing-state (st)
   (let ((run (fn2-format-run :page t 0 0 1 0 65536 0 9 0 1 4096 (mv-nth 7 st) (mv-nth 8 st)
                             (mv-nth 9 st) (mv-nth 5 st) (mv-nth 6 st) (mv-nth 10 st))))
     (fn2-ribbon-call-with-state list ((mv-nth 0 run)) st
       (5 (mv-nth 3 run)) (6 (mv-nth 4 run)) (7 (mv-nth 1 run)) (9 (mv-nth 2 run)) (10 (mv-nth 5 run))))))

(local
 (defthm fn2-ribbon-drive-after-format-step
   (let ((next (fn2-ribbon-next-sealing-state st)))
     (implies (and (posp fuel) (fn2-ribbon-sealing-resources-p n 0 1 (mv-nth 1 st) (mv-nth 3 st) (mv-nth 5 st) (mv-nth 7 st) (mv-nth 8 st) (mv-nth 9 st) (mv-nth 10 st)) (equal (mv-nth 0 next) :more))
       (equal (fn2-ribbon-call-with-state fn2-rba-drive (fuel) st)
              (fn2-ribbon-call-with-state fn2-rba-drive ((1- fuel)) next))))
   :hints (("Goal" :use ((:instance fn2-ribbon-drive-continues-format-run (slot 0) (gen 1)
                            (fn2-ribbon-builds (mv-nth 1 st)) (fn2-ribbon-band (mv-nth 2 st)) (fn2-run-writers (mv-nth 3 st)) (fn2-run-restarts (mv-nth 4 st)) (fn2-fields (mv-nth 5 st)) (fn2-pool (mv-nth 6 st)) (fn2-fc (mv-nth 7 st)) (fn2-fc-context (mv-nth 8 st)) (fn2-b3 (mv-nth 9 st)) (fn2-digests (mv-nth 10 st))))
            :in-theory (union-theories '(fn2-ribbon-next-sealing-state mv-nth-of-cons (:e zp) (:e binary-+) (:e mv-nth) car-cons cdr-cons (:e <) (:e equal)) (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-decode-start-observations
   (and (equal (fn2-fc-rows (fn2-fc-set-phase 0 v fn2-fc)) (fn2-fc-rows fn2-fc))
        (equal (fn2-fc-phase 0 (fn2-fc-set-phase 0 v fn2-fc)) v)
        (equal (fn2-fields-rows (fn2-fc-start :page 0 fn2-fields)) (fn2-fields-rows fn2-fields)))
   :hints (("Goal" :in-theory (e/d (fn2-fc-start fn2-format-page-header-start fn2-fc-rows fn2-fc-phase fn2-fc-set-phase
                         update-fn2-fc-phase$ai fn2-fields-set-status update-fn2-fields-status$ai) (fn2-fields-rows nth update-nth))))))

(local
 (defthm fn2-ribbon-sealing-starts-decode
   (let ((next (fn2-ribbon-next-sealing-state st)) (init (fn2-b3-init 0 0 (fn2-digest-slot 0 *fn2-b3-key*) (mv-nth 10 st) (mv-nth 9 st))))
     (implies (and (fn2-ribbon-sealing-resources-p n 0 1 (mv-nth 1 st) (mv-nth 3 st) (mv-nth 5 st) (mv-nth 7 st) (mv-nth 8 st) (mv-nth 9 st) (mv-nth 10 st))
                   (equal (fn2-fc-phase 0 (mv-nth 7 st)) *fn2-fc-phase-idle*)
                   (fn2-ribbon-arena-p 0 1 9 0 1 65536 65536 (mv-nth 6 st))
                   (fn2-b3-ready 0 (mv-nth 1 init) (mv-nth 0 init)) (fn2-digest-rowp 136 (mv-nth 0 init)))
         (and (equal (mv-nth 0 next) :more)
              (fn2-ribbon-sealing-resources-p n 0 1 (mv-nth 1 next) (mv-nth 3 next) (mv-nth 5 next) (mv-nth 7 next) (mv-nth 8 next) (mv-nth 9 next) (mv-nth 10 next))
              (equal (mv-nth 5 next) (fn2-fc-start :page 0 (mv-nth 5 st)))
              (equal (mv-nth 6 next) (mv-nth 6 st))
              (equal (fn2-fc-phase 0 (mv-nth 7 next)) *fn2-fc-phase-decode*))))
   :hints (("Goal" :use ((:instance fn2-ribbon-page-begins-check (sealp t) (slot 0) (gen 1)
                       (fn2-fields (mv-nth 5 st)) (fn2-pool (mv-nth 6 st)) (fn2-fc (mv-nth 7 st)) (fn2-fc-context (mv-nth 8 st)) (fn2-b3 (mv-nth 9 st)) (fn2-digests (mv-nth 10 st))))
            :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-next-sealing-state fn2-ribbon-sealing-resources-p
                   fn2-ribbon-decode-start-observations mv-nth-of-cons (:e zp) (:e binary-+) (:e mv-nth) car-cons cdr-cons (:e <) (:e equal)) (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-image-hash-initialization
   (let* ((st (fn2-ribbon-sealing-state keys)) (init (fn2-b3-init 0 0 (fn2-digest-slot 0 *fn2-b3-key*) (mv-nth 10 st) (mv-nth 9 st))))
     (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256))
         (and (fn2-b3-ready 0 (mv-nth 1 init) (mv-nth 0 init)) (fn2-digest-rowp 136 (mv-nth 0 init))
              (fn2-ribbon-arena-p 0 1 9 0 1 65536 65536 (mv-nth 6 st))
              (fn2-ribbon-physical-headers-p (len keys) 0 1 (mv-nth 6 st))
              (equal (fn2-fields-rows (mv-nth 5 st)) 400)
              (fn2-ribbon-seal-context-p (mv-nth 8 st)))))
   :hints (("Goal" :use (fn2-ribbon-image-writes-page-headers fn2-ribbon-fresh-added-environment
                      (:instance fn2-ribbon-fresh-hash-after-init (n (len keys))))
            :in-theory (union-theories '(fn2-ribbon-sealing-state mv-nth-of-cons (:e zp) (:e binary-+) (:e mv-nth) car-cons cdr-cons (:e <) (:e equal)) (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-image-reaches-header-decode
   (let* ((st (fn2-ribbon-sealing-state keys)) (next (fn2-ribbon-next-sealing-state st)))
     (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256))
       (and (fn2-ribbon-sealing-resources-p (len keys) 0 1 (mv-nth 1 next) (mv-nth 3 next) (mv-nth 5 next) (mv-nth 7 next) (mv-nth 8 next) (mv-nth 9 next) (mv-nth 10 next))
            (equal (mv-nth 5 next) (fn2-fc-start :page 0 (mv-nth 5 st)))
            (equal (mv-nth 6 next) (mv-nth 6 st))
            (equal (fn2-fc-phase 0 (mv-nth 7 next)) *fn2-fc-phase-decode*)
            (equal (fn2-ribbon-final-drive keys)
                  (fn2-ribbon-call-with-state fn2-rba-drive ((1- (1- (mv-nth 0 (fn2-ribbon-padded-state keys))))) next)))))
   :hints (("Goal" :use (fn2-ribbon-image-reaches-heading fn2-ribbon-image-reaches-sealing
                         fn2-ribbon-image-sealing-resources fn2-ribbon-image-hash-initialization
                         (:instance fn2-ribbon-sealing-starts-decode (n (len keys)) (st (fn2-ribbon-sealing-state keys)))
                         (:instance fn2-ribbon-drive-after-format-step (n (len keys)) (st (fn2-ribbon-sealing-state keys)) (fuel (1- (mv-nth 0 (fn2-ribbon-padded-state keys))))))
             :do-not '(preprocess) :in-theory (union-theories '(posp natp mv-nth-of-cons (:e zp) (:e binary-+) (:e mv-nth) car-cons cdr-cons (:e <) (:e equal)) (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-sealing-decodes-page
   (let ((next (fn2-ribbon-next-sealing-state st)))
     (implies (and (posp n) (<= n 256) (< 301 (fn2-fields-rows old-fields))
                   (equal (mv-nth 5 st) (fn2-fc-start :page 0 old-fields))
                   (equal (fn2-fc-phase 0 (mv-nth 7 st)) *fn2-fc-phase-decode*)
                   (fn2-ribbon-seal-context-p (mv-nth 8 st))
                   (fn2-ribbon-arena-p 0 1 9 0 1 65536 65536 (mv-nth 6 st))
                   (fn2-ribbon-physical-headers-p n 0 1 (mv-nth 6 st)))
              (and (equal (mv-nth 0 next) :more)
                   (equal (mv-nth 6 next) (mv-nth 6 st)) (equal (mv-nth 9 next) (mv-nth 9 st))
                   (equal (mv-nth 10 next) (mv-nth 10 st))
                   (equal (fn2-fc-phase 0 (mv-nth 7 next)) *fn2-fc-phase-prefix*)
                   (equal (fn2-fc-pos 0 (mv-nth 7 next)) 0)
                   (equal (fn2-fc-pad 0 (mv-nth 7 next)) (+ *fn2-ribbon-base* (fn2-ribbon-slots n)))
                   (equal (fn2-fc-pad-end 0 (mv-nth 7 next)) 65536)
                   (equal (fn2-fc-zero 0 (mv-nth 7 next)) 65536))))
   :hints (("Goal" :use ((:instance fn2-ribbon-check-establishes-page-hash-bounds (sealp t) (slot 0) (gen 1) (fn2-fields old-fields) (fn2-pool (mv-nth 6 st)) (fn2-fc (mv-nth 7 st)) (fn2-fc-context (mv-nth 8 st)) (fn2-b3 (mv-nth 9 st)) (fn2-digests (mv-nth 10 st))))
            :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-next-sealing-state (:e unsigned-byte-p) mv-nth-of-cons (:e zp) (:e binary-+) (:e mv-nth) car-cons cdr-cons (:e <) (:e equal))
                           (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-image-reaches-hash-prefix
   (let* ((st (fn2-ribbon-sealing-state keys)) (decoded (fn2-ribbon-next-sealing-state st)) (prefix (fn2-ribbon-next-sealing-state decoded)))
     (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256))
       (and (equal (mv-nth 6 prefix) (mv-nth 6 st))
            (equal (fn2-fc-phase 0 (mv-nth 7 prefix)) *fn2-fc-phase-prefix*)
            (equal (fn2-fc-pos 0 (mv-nth 7 prefix)) 0)
            (equal (fn2-fc-pad 0 (mv-nth 7 prefix)) (+ *fn2-ribbon-base* (fn2-ribbon-slots (len keys))))
            (equal (fn2-fc-pad-end 0 (mv-nth 7 prefix)) 65536)
            (equal (fn2-fc-zero 0 (mv-nth 7 prefix)) 65536)
            (equal (fn2-ribbon-final-drive keys)
                  (fn2-ribbon-call-with-state fn2-rba-drive ((1- (1- (1- (mv-nth 0 (fn2-ribbon-padded-state keys)))))) prefix)))))
   :hints (("Goal" :use (fn2-ribbon-image-reaches-heading fn2-ribbon-image-reaches-header-decode
                        fn2-ribbon-image-hash-initialization
                        (:instance fn2-ribbon-sealing-decodes-page (n (len keys)) (st (fn2-ribbon-next-sealing-state (fn2-ribbon-sealing-state keys))) (old-fields (mv-nth 5 (fn2-ribbon-sealing-state keys))))
                        (:instance fn2-ribbon-drive-after-format-step (n (len keys)) (st (fn2-ribbon-next-sealing-state (fn2-ribbon-sealing-state keys))) (fuel (1- (1- (mv-nth 0 (fn2-ribbon-padded-state keys)))))))
            :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-sealing-resources-p posp natp mv-nth-of-cons (:e zp) (:e binary-+) (:e mv-nth) car-cons cdr-cons (:e <) (:e equal))
                        (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-image-hash-input-padding
   (let* ((st (fn2-ribbon-sealing-state keys)) (prefix (fn2-ribbon-next-sealing-state (fn2-ribbon-next-sealing-state st)))
          (pad (+ *fn2-ribbon-base* (fn2-ribbon-slots (len keys)))))
     (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256))
              (fn2-ribbon-zero-region-p (- 65536 pad) pad 0 1 (mv-nth 6 prefix))))
   :hints (("Goal" :use (fn2-ribbon-image-reaches-heading fn2-ribbon-image-reaches-hash-prefix
                   fn2-ribbon-fresh-added-environment (:instance fn2-ribbon-initial-checker-and-restart-tables (n (len keys)))
                   (:instance fn2-ribbon-heading-establishes-serialized-solution
                     (count (- 65536 (+ *fn2-ribbon-base* (fn2-ribbon-slots (len keys))))) (start (+ *fn2-ribbon-base* (fn2-ribbon-slots (len keys))))
                     (n (len keys)) (slots (fn2-ribbon-slots (len keys))) (slot 0) (gen 1)
                     (fn2-ribbon-builds (fn2-ribbon-builds-set-phase 0 *fn2-ribbon-phase-heading* (mv-nth 1 (fn2-ribbon-emitted-step keys)))) (fn2-run-writers (mv-nth 1 (fn2-ribbon-padded-state keys))) (fn2-fields (mv-nth 5 (fn2-ribbon-added-state keys)))
                     (fn2-pool (mv-nth 2 (fn2-ribbon-padded-state keys))) (fn2-fc-context (mv-nth 8 (fn2-ribbon-added-state keys))) (fn2-ribbon-band (mv-nth 2 (fn2-ribbon-solved-step keys)))))
            :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-heading-invariant-p fn2-ribbon-sealing-state
                 fn2-ribbon-headed-step (:t fn2-ribbon-slots) natp mv-nth-of-cons (:e zp) (:e binary-+) (:e mv-nth) car-cons cdr-cons (:e <) (:e equal)) (theory 'minimal-theory))))
   :rule-classes nil))

; Connect the public constructor to the driver, checker and probes.
(local
 (defthm fn2-ribbon-setup-fold
   (equal (fn2-rba-setup n (create-fn2-ribbon-builds) (create-fn2-ribbon-band) (create-fn2-run-writers) (create-fn2-run-restarts) (create-fn2-fields) (create-fn2-pool) (create-fn2-fc) (create-fn2-fc-context) (create-fn2-b3) (create-fn2-digests))
          (fn2-ribbon-fresh-state n))
   :hints (("Goal" :in-theory (union-theories '(fn2-ribbon-fresh-state) (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-image-run-result
   (equal (fn2-ribbon-image keys drop queries mutate)
          (mv-nth 0 (fn2-rba-run keys drop queries mutate (create-fn2-ribbon-builds)
                       (create-fn2-ribbon-band)
                       (create-fn2-run-writers)
                       (create-fn2-run-restarts)
                       (create-fn2-fields)
                       (create-fn2-pool)
                       (create-fn2-fc)
                       (create-fn2-fc-context)
                       (create-fn2-b3)
                       (create-fn2-digests))))
   :hints (("Goal" :in-theory (union-theories '(fn2-ribbon-image mv-nth-of-cons (:e zp) (:e binary-+) car-cons cdr-cons)
                                             (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-prelude-initial-columns
   (and (equal (mv-nth 3 (fn2-ribbon-fresh-state n)) (fn2-run-writers-init 1 (create-fn2-run-writers)))
        (equal (mv-nth 6 (fn2-ribbon-fresh-state n)) (fn2-pool-init '((3 . 65536)) 1 100 (create-fn2-pool))))
   :hints (("Goal" :use fn2-ribbon-fresh-state-shape :in-theory (theory 'minimal-theory)))))

(local
 (defthm fn2-ribbon-real-open-success
   (equal (mv-nth 0 (fn2-ribbon-opened-writer)) :ok)
   :hints (("Goal" :use fn2-ribbon-initial-page-and-key-arenas :in-theory (theory 'minimal-theory)))))

(local
 (defthm fn2-ribbon-initial-success-codes
   (let ((n (len keys)))
     (implies (and (fn2-ribbon-keysp keys) (posp n) (<= n 256))
              (and (equal (mv-nth 0 (fn2-ribbon-started-build n)) :ok)
                   (equal (mv-nth 0 (fn2-ribbon-ready-state n)) :ready)
                   (equal (mv-nth 6 (fn2-ribbon-ready-state n)) (mv-nth 2 (fn2-ribbon-opened-writer)))
                   (equal (mv-nth 0 (fn2-ribbon-added-state keys)) :ok)
                   (equal (mv-nth 0 (fn2-ribbon-finish 0 (mv-nth 1 (fn2-ribbon-added-state keys)))) :ok))))
   :hints (("Goal" :use ((:instance fn2-ribbon-fresh-build-clears (n (len keys)))
                          (:instance fn2-ribbon-drive-clears-fresh-band (n (len keys)))
                          fn2-ribbon-fresh-adds-solve-key-equations fn2-ribbon-fresh-finish-enters-emitter)
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm fn2-ribbon-started-build-fold
   (equal (let ((st (fn2-ribbon-fresh-state n)))
     (fn2-ribbon-start 0 0 0 136 0 n (mv-nth 1 st) (mv-nth 2 st) (mv-nth 1 (fn2-ribbon-opened-writer))))
          (fn2-ribbon-started-build n))
   :hints (("Goal" :in-theory (union-theories '(fn2-ribbon-started-build) (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-ready-state-fold
   (equal (fn2-ribbon-call-with-state fn2-rba-drive (100000) (fn2-ribbon-fresh-state n)
     (1 (mv-nth 1 (fn2-ribbon-started-build n))) (3 (mv-nth 1 (fn2-ribbon-opened-writer)))
     (6 (mv-nth 2 (fn2-ribbon-opened-writer))))
          (fn2-ribbon-ready-state n))
   :hints (("Goal" :in-theory (union-theories '(fn2-ribbon-ready-state) (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-added-state-fold
   (equal (let ((reserve (fn2-ribbon-key-reservation)))
     (fn2-ribbon-call-with-state fn2-rba-adds (keys (mv-nth 1 reserve) (mv-nth 2 reserve) 0)
           (fn2-ribbon-ready-state (len keys)) (6 (mv-nth 3 reserve))))
          (fn2-ribbon-added-state keys))
   :hints (("Goal" :in-theory (union-theories '(fn2-ribbon-added-state) (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-final-drive-fold
   (equal (let* ((added (fn2-ribbon-added-state keys)) (finish (fn2-ribbon-finish 0 (mv-nth 1 added))))
     (fn2-ribbon-call-with-state fn2-rba-drive (100000) added (1 (mv-nth 1 finish))))
          (fn2-ribbon-final-drive keys))
   :hints (("Goal" :in-theory (union-theories '(fn2-ribbon-final-drive) (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-final-check-fold
   (equal (fn2-ribbon-call-with-state fn2-rba-check ((mv-nth 1 (fn2-ribbon-first-reservation)) (mv-nth 2 (fn2-ribbon-first-reservation))) (fn2-ribbon-final-drive keys))
          (fn2-ribbon-final-check keys))
   :hints (("Goal" :use fn2-ribbon-initial-page-and-key-arenas :in-theory (union-theories '(fn2-ribbon-final-check) (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-final-answers-fold
   (equal (let* ((checked (fn2-ribbon-final-check keys))
          (q (fn2-pool-reserve 0 9 0 1 (mv-nth 6 checked))))
     (mv-nth 0 (fn2-ribbon-call-with-state fn2-rba-probes
                   (queries (mv-nth 1 q) (mv-nth 2 q) 0 (mv-nth 1 (fn2-ribbon-first-reservation)) (mv-nth 2 (fn2-ribbon-first-reservation))) checked (6 (mv-nth 3 q)))))
          (fn2-ribbon-final-answers keys queries))
   :hints (("Goal" :use fn2-ribbon-initial-page-and-key-arenas :in-theory (union-theories '(fn2-ribbon-final-answers) (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-car-as-status
   (equal (car x) (mv-nth 0 x))
   :hints (("Goal" :in-theory (enable mv-nth)))))

(local
 (defthm fn2-ribbon-first-start-result
   (implies (and (posp n) (<= n 256)) (equal (car (fn2-ribbon-started-build n)) :ok))
   :hints (("Goal" :use fn2-ribbon-fresh-build-clears
            :in-theory (union-theories '(fn2-ribbon-car-as-status) (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-adapter-success-status
   (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256))
            (and (equal (car (fn2-ribbon-ready-state (len keys))) :ready)
                 (equal (car (fn2-ribbon-added-state keys)) :ok)
                 (equal (car (fn2-ribbon-finish 0 (mv-nth 1 (fn2-ribbon-added-state keys)))) :ok)))
   :hints (("Goal" :use fn2-ribbon-initial-success-codes
            :in-theory (union-theories '(fn2-ribbon-car-as-status) (theory 'minimal-theory))))))

(defthm fn2-ribbon-image-reaches-final-drive
   (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256))
            (equal (fn2-ribbon-image keys nil queries nil)
                   (list (mv-nth 0 (fn2-ribbon-final-drive keys)) (mv-nth 0 (fn2-ribbon-final-check keys))
                         (fn2-ribbon-final-answers keys queries))))
   :hints (("Goal" :do-not '(preprocess) :in-theory (union-theories
                      '(fn2-ribbon-image-run-result fn2-rba-run fn2-ribbon-drop fn2-ribbon-setup-fold
                        fn2-ribbon-prelude-initial-columns fn2-ribbon-real-open-success
                        fn2-ribbon-initial-success-codes fn2-ribbon-started-build-fold fn2-ribbon-ready-state-fold
                        fn2-ribbon-added-state-fold fn2-ribbon-final-drive-fold fn2-ribbon-final-check-fold fn2-ribbon-final-answers-fold
                        fn2-ribbon-adapter-success-status fn2-ribbon-first-start-result (:t fn2-ribbon-ready-state) (:t fn2-ribbon-added-state) (:t fn2-ribbon-finish) (:t fn2-ribbon-final-drive) (:t fn2-ribbon-final-check) (:t fn2-ribbon-started-build) mv-nth-of-cons car-cons cdr-cons (:e natp) (:e equal) (:e not) (:e consp) (:e zp) (:e binary-+))
                      (theory 'minimal-theory))))
   :rule-classes nil)

(local (in-theory (disable fn2-ribbon-car-as-status fn2-ribbon-setup-fold fn2-ribbon-started-build-fold
                           fn2-ribbon-ready-state-fold fn2-ribbon-added-state-fold fn2-ribbon-final-drive-fold
                           fn2-ribbon-final-check-fold fn2-ribbon-final-answers-fold)))


(local
 (defthm fn2-ribbon-image-padding-scan-succeeds
   (let* ((prefix (fn2-ribbon-next-sealing-state (fn2-ribbon-next-sealing-state (fn2-ribbon-sealing-state keys)))) (pool (mv-nth 6 prefix)) (pad (+ *fn2-ribbon-base* (fn2-ribbon-slots (len keys)))))
     (implies (and (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256)) (natp pos) (natp span) (<= pad pos) (<= (+ pos span) 65536))
              (equal (fn2-fc-zero-prefix (+ (fn2-pool-base 0 pool) pos) span pool) span)))
   :hints (("Goal" :use (fn2-ribbon-image-hash-input-padding fn2-ribbon-image-reaches-hash-prefix
                          fn2-ribbon-image-hash-initialization
                   (:instance fn2-ribbon-arena-base-natural (slot 0) (gen 1) (pk 9) (ps 0) (pg 1)
                           (off 65536) (cap 65536) (fn2-pool (mv-nth 6 (fn2-ribbon-next-sealing-state (fn2-ribbon-next-sealing-state (fn2-ribbon-sealing-state keys))))))
                   (:instance fn2-ribbon-checker-accepts-padding-span (slot 0) (gen 1) (pad (+ *fn2-ribbon-base* (fn2-ribbon-slots (len keys)))) (fn2-pool (mv-nth 6 (fn2-ribbon-next-sealing-state (fn2-ribbon-next-sealing-state (fn2-ribbon-sealing-state keys)))))))
            :do-not '(preprocess) :in-theory (union-theories '(natp (:t fn2-ribbon-slots)) (theory 'minimal-theory))))
   :rule-classes nil))

; Trace the page and solved band through both the sealing drive and the independent checker.
(local
 (defthm fn2-ribbon-continued-seal-keeps-build
   (implies (equal (mv-nth 0 (fn2-ribbon-seal 0 4096 fn2-ribbon-builds fn2-run-writers fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)) :more)
            (equal (mv-nth 1 (fn2-ribbon-seal 0 4096 fn2-ribbon-builds fn2-run-writers fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)) fn2-ribbon-builds))
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-seal) (fn2-run-seal-step fn2-ribbon-builds-rows fn2-ribbon-builds-w fn2-ribbon-builds-crow
           fn2-ribbon-builds-hrow fn2-run-writers-rows fn2-fc-rows fn2-fc-context-rows fn2-ribbon-builds-set-phase))))))

(local
 (defthm fn2-ribbon-sealing-work-preserves-page-and-band
   (let ((w (fn2-ribbon-work 0 4096 fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)))
     (implies (equal (fn2-ribbon-builds-phase 0 fn2-ribbon-builds) *fn2-ribbon-phase-sealing*)
       (and (equal (mv-nth 2 w) fn2-ribbon-band) (equal (mv-nth 5 w) fn2-pool)
            (implies (equal (mv-nth 0 w) :more) (equal (mv-nth 1 w) fn2-ribbon-builds)))))
   :hints (("Goal" :in-theory (union-theories '(fn2-ribbon-work fn2-ribbon-seal-preserves-page
         fn2-ribbon-continued-seal-keeps-build (:e natp) mv-nth-of-cons (:e zp) (:e binary-+) (:e mv-nth) car-cons cdr-cons (:e <) (:e equal)) (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-sealing-drive-preserves-page-and-band
   (let ((drive (fn2-rba-call fn2-rba-drive fuel)))
     (implies (equal (fn2-ribbon-builds-phase 0 fn2-ribbon-builds) *fn2-ribbon-phase-sealing*)
              (and (equal (mv-nth 2 drive) fn2-ribbon-band) (equal (mv-nth 6 drive) fn2-pool))))
   :hints (("Goal" :induct (fn2-rba-call fn2-rba-drive fuel) :expand ((fn2-rba-call fn2-rba-drive fuel))
            :in-theory (union-theories '((:i fn2-rba-drive) fn2-ribbon-sealing-work-preserves-page-and-band
                 mv-nth-of-cons (:e zp) (:e binary-+) (:e mv-nth) car-cons cdr-cons (:e <) (:e equal)) (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-check-keeps-band
   (equal (mv-nth 2 (fn2-rba-call fn2-rba-check slot gen)) fn2-ribbon-band)
   :hints (("Goal" :in-theory (union-theories '(fn2-rba-check mv-nth-of-cons (:e zp) (:e binary-+) (:e mv-nth) car-cons cdr-cons (:e <) (:e equal)) (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-checked-page-holds-key-equations
   (let* ((n (len keys)) (slots (fn2-ribbon-slots n)) (checked (fn2-ribbon-final-check keys))
          (page (mv-nth 6 checked)) (band (mv-nth 2 checked)))
     (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256))
              (and (equal page (mv-nth 4 (fn2-ribbon-headed-step keys)))
                   (fn2-ribbon-physical-headers-p n 0 1 page)
                   (fn2-ribbon-solution-page-p slots 0 1 band page)
                   (fn2-ribbon-key-equations-p keys slots (fn2-ribbon-seed 7) (fn2-ribbon-band-suffix 0 slots band)))))
   :hints (("Goal" :use (fn2-ribbon-image-reaches-sealing fn2-ribbon-image-writes-page-headers
                         fn2-ribbon-fresh-keys-produce-solution-page
                   (:instance fn2-ribbon-sealing-drive-preserves-page-and-band (fuel (1- (mv-nth 0 (fn2-ribbon-padded-state keys))))
                             (fn2-ribbon-builds (mv-nth 1 (fn2-ribbon-sealing-state keys))) (fn2-ribbon-band (mv-nth 2 (fn2-ribbon-sealing-state keys))) (fn2-run-writers (mv-nth 3 (fn2-ribbon-sealing-state keys))) (fn2-run-restarts (mv-nth 4 (fn2-ribbon-sealing-state keys))) (fn2-fields (mv-nth 5 (fn2-ribbon-sealing-state keys))) (fn2-pool (mv-nth 6 (fn2-ribbon-sealing-state keys))) (fn2-fc (mv-nth 7 (fn2-ribbon-sealing-state keys))) (fn2-fc-context (mv-nth 8 (fn2-ribbon-sealing-state keys))) (fn2-b3 (mv-nth 9 (fn2-ribbon-sealing-state keys))) (fn2-digests (mv-nth 10 (fn2-ribbon-sealing-state keys)))))
            :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-final-check fn2-ribbon-sealing-state
                 fn2-ribbon-rba-check-preserves-page fn2-ribbon-check-keeps-band mv-nth-of-cons (:e zp) (:e binary-+) (:e mv-nth) car-cons cdr-cons (:e <) (:e equal)) (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-padding-leaves-query-slot-free
   (implies (fn2-ribbon-query-slot-free-p fn2-pool) (fn2-ribbon-query-slot-free-p (mv-nth 1 (fn2-run-zero k slot gen off pk ps pg fn2-pool))))
   :hints (("Goal" :induct (fn2-run-zero k slot gen off pk ps pg fn2-pool) :in-theory (e/d (fn2-run-zero) (fn2-ribbon-query-slot-free-p fn2-pool-write fn2-ribbon-band-z))))))

(local
 (defthm fn2-ribbon-emission-leaves-query-slot-free
   (implies (fn2-ribbon-query-slot-free-p fn2-pool) (fn2-ribbon-query-slot-free-p (mv-nth 1 (fn2-ribbon-emit-bytes k i base slot gen dst pk ps pg fn2-ribbon-band fn2-pool))))
   :hints (("Goal" :induct (fn2-ribbon-emit-bytes k i base slot gen dst pk ps pg fn2-ribbon-band fn2-pool) :in-theory (e/d (fn2-ribbon-emit-bytes) (fn2-ribbon-query-slot-free-p fn2-pool-write fn2-ribbon-band-z))))))

(local
 (defun fn2-ribbon-initial-query-slot-check (fn2-run-writers fn2-pool)
   (declare (xargs :stobjs (fn2-run-writers fn2-pool) :verify-guards nil))
   (b* ((fn2-pool (fn2-pool-init '((3 . 65536)) 1 100 fn2-pool))
        ((mv & p pg fn2-pool) (fn2-pool-reserve 0 9 0 1 fn2-pool))
        (fn2-run-writers (fn2-run-writers-init 1 fn2-run-writers))
        ((mv & fn2-run-writers fn2-pool) (fn2-run-open 0 p pg 1 1 0 7 0 *page-kind-partitioned-filter* 5 2 3 1 1 9 0 1 0 65536 fn2-run-writers fn2-pool))
        ((mv & & & fn2-pool) (fn2-pool-reserve 0 9 0 1 fn2-pool)))
     (mv (fn2-ribbon-query-slot-free-p fn2-pool) fn2-run-writers fn2-pool))))

(local
 (defun fn2-ribbon-fresh-query-slot-check ()
   (declare (xargs :verify-guards nil))
   (fn2-run-with-local (fn2-run-writers fn2-pool) (fn2-ribbon-initial-query-slot-check fn2-run-writers fn2-pool))))

(local
 (defthm fn2-ribbon-fresh-query-slot-available (fn2-ribbon-fresh-query-slot-check)
   :hints (("Goal" :in-theory (union-theories '((:e fn2-ribbon-fresh-query-slot-check)) (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-query-slot-after-key-reservation
   (fn2-ribbon-query-slot-free-p (mv-nth 3 (fn2-ribbon-key-reservation)))
   :hints (("Goal" :use fn2-ribbon-fresh-query-slot-available
            :in-theory (union-theories '(fn2-ribbon-fresh-query-slot-check fn2-ribbon-initial-query-slot-check mv-nth-of-cons (:e zp) (:e binary-+) (:e mv-nth) car-cons cdr-cons (:e <) (:e equal))
                         (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-reserving-query-slot-establishes-arena
   (let* ((r (fn2-pool-reserve 0 9 0 1 fn2-pool)) (after (mv-nth 3 r)))
     (implies (fn2-ribbon-query-slot-free-p fn2-pool)
        (and (equal (mv-nth 0 r) :ok) (equal (mv-nth 1 r) 2) (equal (mv-nth 2 r) 1)
             (fn2-ribbon-arena-p 2 1 9 0 1 0 65536 after) (fn2-ribbon-page-before-arena-p 0 2 after)
             (equal (fn2-pool-read 0 1 i 9 0 1 after) (fn2-pool-read 0 1 i 9 0 1 fn2-pool)))))
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-query-slot-free-p fn2-pool-reserve fn2-pool-reservable-count
               fn2-pool-reserve-body fn2-ribbon-page-before-arena-p fn2-ribbon-arena-p fn2-pool-workspace-code
               fn2-pool-handle-code fn2-pool-readable-code fn2-pool-ownerp fn2-pool-read fn2-pool-datai
               fn2-pool-fill fn2-pool-owner-kind fn2-pool-owner-slot fn2-pool-owner-gen
               update-fn2-pool-class-headsi update-fn2-pool-class-countsi fn2-pool-nclasses fn2-pool-rows fn2-pool-credit-configured fn2-pool-class-countsi fn2-pool-class-headsi fn2-pool-state fn2-pool-class fn2-pool-out-count fn2-pool-query-ref-count fn2-pool-gen fn2-pool-base fn2-pool-cap fn2-pool-data-length fn2-pool-set-state update-fn2-pool-state$ai fn2-pool-set-owner-kind update-fn2-pool-owner-kind$ai fn2-pool-set-owner-slot update-fn2-pool-owner-slot$ai fn2-pool-set-owner-gen update-fn2-pool-owner-gen$ai fn2-pool-set-out-count update-fn2-pool-out-count$ai fn2-pool-set-query-ref-count update-fn2-pool-query-ref-count$ai fn2-pool-set-fill update-fn2-pool-fill$ai)
                    (nth update-nth))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-emitter-keeps-query-slot
   (implies (fn2-ribbon-query-slot-free-p fn2-pool)
     (fn2-ribbon-query-slot-free-p (mv-nth 3 (fn2-ribbon-emit-step f budget fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-pool))))
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-emit-step) (fn2-ribbon-query-slot-free-p fn2-ribbon-emit-bytes
                fn2-run-writers-rows fn2-ribbon-builds-rows fn2-ribbon-builds-w fn2-ribbon-builds-base fn2-ribbon-builds-i
                fn2-ribbon-builds-slots fn2-ribbon-builds-set-i fn2-ribbon-builds-set-phase fn2-run-writers-phase))))))

(local
 (defthm fn2-ribbon-padding-end-keeps-query-slot
   (implies (fn2-ribbon-query-slot-free-p pool)
            (fn2-ribbon-query-slot-free-p (mv-nth 2 (fn2-ribbon-padding-end fuel cursor pos slot gen writers pool))))
   :hints (("Goal" :induct (fn2-ribbon-padding-end fuel cursor pos slot gen writers pool)
            :in-theory (e/d (fn2-ribbon-padding-end) (fn2-ribbon-query-slot-free-p fn2-run-zero fn2-run-writers-set-pos
                 fn2-run-writers-set-phase))))))

; Reserve the third arena and apply the serialized-page probe theorem to the public image.
(local
 (defthm fn2-ribbon-query-reservation-preserves-page-range
   (implies (fn2-ribbon-query-slot-free-p fn2-pool)
      (equal (fn2-layout-range-code 0 1 off end nil 9 0 1 (mv-nth 3 (fn2-pool-reserve 0 9 0 1 fn2-pool)))
             (fn2-layout-range-code 0 1 off end nil 9 0 1 fn2-pool)))
   :hints (("Goal" :in-theory (e/d (fn2-layout-range-code fn2-pool-slot-base fn2-pool-slot-fill fn2-pool-slot-cap fn2-pool-capacity-bytes fn2-ribbon-query-slot-free-p fn2-pool-reserve fn2-pool-reservable-count
               fn2-pool-reserve-body fn2-ribbon-page-before-arena-p fn2-ribbon-arena-p fn2-pool-workspace-code
               fn2-pool-handle-code fn2-pool-readable-code fn2-pool-ownerp fn2-pool-read fn2-pool-datai
               fn2-pool-fill fn2-pool-owner-kind fn2-pool-owner-slot fn2-pool-owner-gen
               update-fn2-pool-class-headsi update-fn2-pool-class-countsi fn2-pool-nclasses fn2-pool-rows fn2-pool-credit-configured fn2-pool-class-countsi fn2-pool-class-headsi fn2-pool-state fn2-pool-class fn2-pool-out-count fn2-pool-query-ref-count fn2-pool-gen fn2-pool-base fn2-pool-cap fn2-pool-data-length fn2-pool-set-state update-fn2-pool-state$ai fn2-pool-set-owner-kind update-fn2-pool-owner-kind$ai fn2-pool-set-owner-slot update-fn2-pool-owner-slot$ai fn2-pool-set-owner-gen update-fn2-pool-owner-gen$ai fn2-pool-set-out-count update-fn2-pool-out-count$ai fn2-pool-set-query-ref-count update-fn2-pool-query-ref-count$ai fn2-pool-set-fill update-fn2-pool-fill$ai)
                    (nth update-nth unsigned-byte-p))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-query-reservation-preserves-page-read
   (implies (fn2-ribbon-query-slot-free-p fn2-pool)
     (equal (fn2-pool-read 0 1 i 9 0 1 (mv-nth 3 (fn2-pool-reserve 0 9 0 1 fn2-pool))) (fn2-pool-read 0 1 i 9 0 1 fn2-pool)))
   :hints (("Goal" :use fn2-ribbon-reserving-query-slot-establishes-arena :in-theory (theory 'minimal-theory)))))

(local
 (defthm fn2-ribbon-bytes-at-p-after-query-reservation
   (implies (fn2-ribbon-query-slot-free-p fn2-pool)
            (equal (fn2-ribbon-bytes-at-p bytes 0 1 off 9 0 1 (mv-nth 3 (fn2-pool-reserve 0 9 0 1 fn2-pool))) (fn2-ribbon-bytes-at-p bytes 0 1 off 9 0 1 fn2-pool)))
   :hints (("Goal" :induct (fn2-ribbon-bytes-at-p bytes 0 1 off 9 0 1 fn2-pool)
            :in-theory (e/d (fn2-ribbon-bytes-at-p) (fn2-ribbon-query-slot-free-p fn2-pool-reserve fn2-pool-read fn2-ribbon-band-z fn2-ribbon-band-rows))))))

(local
 (defthm fn2-ribbon-solution-page-p-after-query-reservation
   (implies (fn2-ribbon-query-slot-free-p fn2-pool)
            (equal (fn2-ribbon-solution-page-p n 0 1 fn2-ribbon-band (mv-nth 3 (fn2-pool-reserve 0 9 0 1 fn2-pool))) (fn2-ribbon-solution-page-p n 0 1 fn2-ribbon-band fn2-pool)))
   :hints (("Goal" :induct (fn2-ribbon-solution-page-p n 0 1 fn2-ribbon-band fn2-pool)
            :in-theory (e/d (fn2-ribbon-solution-page-p) (fn2-ribbon-query-slot-free-p fn2-pool-reserve fn2-pool-read fn2-ribbon-band-z fn2-ribbon-band-rows))))))

(local
 (defthm fn2-ribbon-headers-after-query-reservation
   (implies (fn2-ribbon-query-slot-free-p fn2-pool)
       (equal (fn2-ribbon-physical-headers-p n 0 1 (mv-nth 3 (fn2-pool-reserve 0 9 0 1 fn2-pool)))
              (fn2-ribbon-physical-headers-p n 0 1 fn2-pool)))
   :hints (("Goal" :use ((:instance fn2-ribbon-query-reservation-preserves-page-range (off 0) (end *fn2-run-header-area*))
                      (:instance fn2-ribbon-query-reservation-preserves-page-range (off *fn2-run-header-area*) (end *fn2-ribbon-base*)))
            :in-theory (union-theories '(fn2-ribbon-physical-headers-p fn2-ribbon-bytes-at-p-after-query-reservation)
                            (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-load-leaves-query-slot-free
   (implies (fn2-ribbon-query-slot-free-p fn2-pool) (fn2-ribbon-query-slot-free-p (mv-nth 1 (fn2-run-load-bytes bytes slot gen off pk ps pg fn2-pool))))
   :hints (("Goal" :induct (fn2-run-load-bytes bytes slot gen off pk ps pg fn2-pool) :in-theory (e/d (fn2-run-load-bytes) (fn2-ribbon-query-slot-free-p fn2-pool-write fn2-ribbon-band-z))))))

(local
 (defthm fn2-ribbon-padding-leaves-query-arena-free
   (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256)) (fn2-ribbon-query-slot-free-p (mv-nth 2 (fn2-ribbon-padded-state keys))))
   :hints (("Goal" :use (fn2-ribbon-query-slot-after-key-reservation fn2-ribbon-fresh-added-environment)
            :in-theory (union-theories '(fn2-ribbon-padded-state fn2-ribbon-emitted-step fn2-ribbon-padding-end-keeps-query-slot
                           fn2-ribbon-emitter-keeps-query-slot) (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-checked-page-leaves-query-slot-free
   (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256)) (fn2-ribbon-query-slot-free-p (mv-nth 6 (fn2-ribbon-final-check keys))))
   :hints (("Goal" :use (fn2-ribbon-image-reaches-heading fn2-ribbon-checked-page-holds-key-equations fn2-ribbon-padding-leaves-query-arena-free
                   fn2-ribbon-fresh-added-environment (:instance fn2-ribbon-initial-checker-and-restart-tables (n (len keys)))
                   (:instance fn2-ribbon-heading-establishes-serialized-solution
                     (count (- 65536 (+ *fn2-ribbon-base* (fn2-ribbon-slots (len keys))))) (start (+ *fn2-ribbon-base* (fn2-ribbon-slots (len keys))))
                     (n (len keys)) (slots (fn2-ribbon-slots (len keys))) (slot 0) (gen 1)
                     (fn2-ribbon-builds (fn2-ribbon-builds-set-phase 0 *fn2-ribbon-phase-heading* (mv-nth 1 (fn2-ribbon-emitted-step keys)))) (fn2-run-writers (mv-nth 1 (fn2-ribbon-padded-state keys))) (fn2-fields (mv-nth 5 (fn2-ribbon-added-state keys)))
                     (fn2-pool (mv-nth 2 (fn2-ribbon-padded-state keys))) (fn2-fc-context (mv-nth 8 (fn2-ribbon-added-state keys))) (fn2-ribbon-band (mv-nth 2 (fn2-ribbon-solved-step keys)))))
            :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-heading-invariant-p fn2-ribbon-sealing-state
                 fn2-ribbon-load-leaves-query-slot-free fn2-ribbon-headed-step (:t fn2-ribbon-slots) natp mv-nth-of-cons (:e zp) (:e binary-+) (:e mv-nth) car-cons cdr-cons (:e <) (:e equal)) (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-format-step-keeps-field-count
   (equal (fn2-fields-rows (mv-nth 3 (fn2-format-run :page sealp row slot gen off len base pk ps pg budget fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))) (fn2-fields-rows fn2-fields))
   :hints (("Goal" :do-not '(preprocess) :in-theory (union-theories '(fn2-format-run fn2-fc-step fn2-fc-start fn2-fc-decode-step
                       (:t fn2-format-page-header-decode-step) fn2-format-page-header-decode-step-rows fn2-format-page-header-start-rows mv-nth-of-cons (:e zp) (:e binary-+) (:e mv-nth) car-cons cdr-cons (:e <) (:e equal)) (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-format-drive-keeps-field-count
   (equal (fn2-fields-rows (mv-nth 3 (fn2-format-drive fuel row :page sealp slot gen off len base pk ps pg budget fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))) (fn2-fields-rows fn2-fields))
   :hints (("Goal" :induct (fn2-format-drive fuel row :page sealp slot gen off len base pk ps pg budget fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests) :expand ((fn2-format-drive fuel row :page sealp slot gen off len base pk ps pg budget fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
            :in-theory (union-theories '((:i fn2-format-drive) (:t fn2-format-run) fn2-ribbon-format-step-keeps-field-count mv-nth-of-cons (:e zp) (:e binary-+) (:e mv-nth) car-cons cdr-cons (:e <) (:e equal)) (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-check-keeps-field-count
   (equal (fn2-fields-rows (mv-nth 5 (fn2-rba-call fn2-rba-check slot gen))) (fn2-fields-rows fn2-fields))
   :hints (("Goal" :in-theory (union-theories '(fn2-rba-check fn2-ribbon-format-drive-keeps-field-count mv-nth-of-cons (:e zp) (:e binary-+) (:e mv-nth) car-cons cdr-cons (:e <) (:e equal)) (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-run-seal-keeps-field-count
   (equal (fn2-fields-rows (mv-nth 4 (fn2-run-seal-step w row hrow budget fn2-run-writers fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
          (fn2-fields-rows fn2-fields))
   :hints (("Goal" :in-theory (union-theories '(fn2-run-seal-step (:t fn2-format-run) fn2-ribbon-format-step-keeps-field-count mv-nth-of-cons (:e zp) (:e binary-+) (:e mv-nth) car-cons cdr-cons (:e <) (:e equal)) (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-seal-keeps-field-count
   (equal (fn2-fields-rows (mv-nth 5 (fn2-ribbon-seal 0 4096 fn2-ribbon-builds fn2-run-writers fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))) (fn2-fields-rows fn2-fields))
   :hints (("Goal" :in-theory (union-theories '(fn2-ribbon-seal (:t fn2-run-seal-step) fn2-ribbon-run-seal-keeps-field-count mv-nth-of-cons (:e zp) (:e binary-+) (:e mv-nth) car-cons cdr-cons (:e <) (:e equal))
                           (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-sealing-work-keeps-field-count
   (implies (equal (fn2-ribbon-builds-phase 0 fn2-ribbon-builds) *fn2-ribbon-phase-sealing*)
            (equal (fn2-fields-rows (mv-nth 4 (fn2-ribbon-work 0 4096 fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))) (fn2-fields-rows fn2-fields)))
   :hints (("Goal" :in-theory (union-theories '(fn2-ribbon-work (:t fn2-ribbon-seal) fn2-ribbon-seal-keeps-field-count
                    (:e natp) mv-nth-of-cons (:e zp) (:e binary-+) (:e mv-nth) car-cons cdr-cons (:e <) (:e equal)) (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-sealing-drive-keeps-field-count
   (let ((drive (fn2-rba-call fn2-rba-drive fuel)))
     (implies (equal (fn2-ribbon-builds-phase 0 fn2-ribbon-builds) *fn2-ribbon-phase-sealing*)
              (equal (fn2-fields-rows (mv-nth 5 drive)) (fn2-fields-rows fn2-fields))))
   :hints (("Goal" :induct (fn2-rba-call fn2-rba-drive fuel) :expand ((fn2-rba-call fn2-rba-drive fuel))
            :in-theory (union-theories '((:i fn2-rba-drive) (:t fn2-ribbon-work) fn2-ribbon-sealing-work-keeps-field-count fn2-ribbon-sealing-work-preserves-page-and-band
                 mv-nth-of-cons (:e zp) (:e binary-+) (:e mv-nth) car-cons cdr-cons (:e <) (:e equal)) (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-checked-fields-ready-for-queries
   (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256)) (equal (fn2-fields-rows (mv-nth 5 (fn2-ribbon-final-check keys))) 400))
   :hints (("Goal" :use (fn2-ribbon-image-reaches-sealing fn2-ribbon-image-writes-page-headers
                         
                   (:instance fn2-ribbon-sealing-drive-keeps-field-count (fuel (1- (mv-nth 0 (fn2-ribbon-padded-state keys))))
                             (fn2-ribbon-builds (mv-nth 1 (fn2-ribbon-sealing-state keys))) (fn2-ribbon-band (mv-nth 2 (fn2-ribbon-sealing-state keys))) (fn2-run-writers (mv-nth 3 (fn2-ribbon-sealing-state keys))) (fn2-run-restarts (mv-nth 4 (fn2-ribbon-sealing-state keys))) (fn2-fields (mv-nth 5 (fn2-ribbon-sealing-state keys))) (fn2-pool (mv-nth 6 (fn2-ribbon-sealing-state keys))) (fn2-fc (mv-nth 7 (fn2-ribbon-sealing-state keys))) (fn2-fc-context (mv-nth 8 (fn2-ribbon-sealing-state keys))) (fn2-b3 (mv-nth 9 (fn2-ribbon-sealing-state keys))) (fn2-digests (mv-nth 10 (fn2-ribbon-sealing-state keys)))))
            :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-final-check fn2-ribbon-sealing-state
                 fn2-ribbon-check-keeps-field-count mv-nth-of-cons (:e zp) (:e binary-+) (:e mv-nth) car-cons cdr-cons (:e <) (:e equal)) (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-adapter-probe-answers-sound
   (implies (and (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256)) (fn2-ribbon-keysp queries))
            (fn2-ribbon-answers-sound keys queries (fn2-ribbon-final-answers keys queries)))
   :hints (("Goal" :use (fn2-ribbon-checked-fields-ready-for-queries fn2-ribbon-checked-page-leaves-query-slot-free
                         fn2-ribbon-checked-page-holds-key-equations
                         (:instance fn2-ribbon-reserving-query-slot-establishes-arena (fn2-pool (mv-nth 6 (fn2-ribbon-final-check keys))))
                         (:instance fn2-ribbon-probes-on-serialized-solution (pslot 0) (pgen 1) (slot 2) (gen 1) (off 0)
                           (fn2-ribbon-builds (mv-nth 1 (fn2-ribbon-final-check keys)))
                           (fn2-ribbon-band (mv-nth 2 (fn2-ribbon-final-check keys)))
                           (fn2-run-writers (mv-nth 3 (fn2-ribbon-final-check keys)))
                           (fn2-run-restarts (mv-nth 4 (fn2-ribbon-final-check keys)))
                           (fn2-fields (mv-nth 5 (fn2-ribbon-final-check keys)))
                           (fn2-pool (mv-nth 3 (fn2-pool-reserve 0 9 0 1 (mv-nth 6 (fn2-ribbon-final-check keys)))))
                           (fn2-fc (mv-nth 7 (fn2-ribbon-final-check keys)))
                           (fn2-fc-context (mv-nth 8 (fn2-ribbon-final-check keys)))
                           (fn2-b3 (mv-nth 9 (fn2-ribbon-final-check keys)))
                           (fn2-digests (mv-nth 10 (fn2-ribbon-final-check keys)))))
            :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-final-answers fn2-ribbon-headers-after-query-reservation
                 fn2-ribbon-solution-page-p-after-query-reservation (:e natp) (:e <) (:e unsigned-byte-p))
                          (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-image-probe-answers-sound
   (implies (and (fn2-ribbon-keysp keys) (consp keys) (<= (len keys) 256) (fn2-ribbon-keysp queries))
            (fn2-ribbon-answers-sound keys queries (caddr (fn2-ribbon-image keys nil queries nil))))
   :hints (("Goal" :use (fn2-ribbon-image-reaches-final-drive fn2-ribbon-adapter-probe-answers-sound)
            :expand ((len keys)) :in-theory (union-theories '(posp (:t len) car-cons cdr-cons) (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defun fn2-ribbon-typed-pool-p (fn2-pool)
  (declare (xargs :stobjs fn2-pool :verify-guards nil))
  (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))))

(local
 (defthm fn2-ribbon-byte-write-keeps-typed-pool
   (implies (fn2-ribbon-typed-pool-p fn2-pool)
      (fn2-ribbon-typed-pool-p (mv-nth 1 (fn2-pool-write slot gen idx byte okind oslot ogen fn2-pool))))
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-typed-pool-p) (fn2-pool-write fn2-poolp fn2-pool-wfp))))))

(local
 (defthm fn2-ribbon-load-keeps-pool-type
   (implies (fn2-ribbon-typed-pool-p fn2-pool) (fn2-ribbon-typed-pool-p (mv-nth 1 (fn2-run-load-bytes bytes slot gen off pk ps pg fn2-pool))))
   :hints (("Goal" :induct (fn2-run-load-bytes bytes slot gen off pk ps pg fn2-pool) :in-theory (e/d (fn2-run-load-bytes) (fn2-ribbon-typed-pool-p fn2-pool-write fn2-ribbon-band-z))))))

(local
 (defthm fn2-ribbon-padding-keeps-pool-type
   (implies (fn2-ribbon-typed-pool-p fn2-pool) (fn2-ribbon-typed-pool-p (mv-nth 1 (fn2-run-zero k slot gen off pk ps pg fn2-pool))))
   :hints (("Goal" :induct (fn2-run-zero k slot gen off pk ps pg fn2-pool) :in-theory (e/d (fn2-run-zero) (fn2-ribbon-typed-pool-p fn2-pool-write fn2-ribbon-band-z))))))

(local
 (defthm fn2-ribbon-emission-keeps-pool-type
   (implies (fn2-ribbon-typed-pool-p fn2-pool) (fn2-ribbon-typed-pool-p (mv-nth 1 (fn2-ribbon-emit-bytes k i base slot gen dst pk ps pg fn2-ribbon-band fn2-pool))))
   :hints (("Goal" :induct (fn2-ribbon-emit-bytes k i base slot gen dst pk ps pg fn2-ribbon-band fn2-pool) :in-theory (e/d (fn2-ribbon-emit-bytes) (fn2-ribbon-typed-pool-p fn2-pool-write fn2-ribbon-band-z))))))

(local
 (defthm fn2-ribbon-emitter-keeps-pool-type
   (implies (fn2-ribbon-typed-pool-p fn2-pool)
     (fn2-ribbon-typed-pool-p (mv-nth 3 (fn2-ribbon-emit-step f budget fn2-ribbon-builds fn2-ribbon-band fn2-run-writers fn2-pool))))
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-emit-step) (fn2-ribbon-typed-pool-p fn2-ribbon-emit-bytes
                fn2-run-writers-rows fn2-ribbon-builds-rows fn2-ribbon-builds-w fn2-ribbon-builds-base fn2-ribbon-builds-i
                fn2-ribbon-builds-slots fn2-ribbon-builds-set-i fn2-ribbon-builds-set-phase fn2-run-writers-phase))))))

(local
 (defthm fn2-ribbon-padding-end-keeps-pool-type
   (implies (fn2-ribbon-typed-pool-p pool)
            (fn2-ribbon-typed-pool-p (mv-nth 2 (fn2-ribbon-padding-end fuel cursor pos slot gen writers pool))))
   :hints (("Goal" :induct (fn2-ribbon-padding-end fuel cursor pos slot gen writers pool)
            :in-theory (e/d (fn2-ribbon-padding-end) (fn2-ribbon-typed-pool-p fn2-run-zero fn2-run-writers-set-pos
                 fn2-run-writers-set-phase))))))

(local
 (defthm fn2-ribbon-key-reservation-has-typed-pool
   (fn2-ribbon-typed-pool-p (mv-nth 3 (fn2-ribbon-key-reservation)))
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-typed-pool-p) (fn2-pool-reserve fn2-run-open fn2-pool-init fn2-poolp fn2-pool-wfp
                        fn2-run-writers-init create-fn2-pool create-fn2-run-writers))))))


(local
 (defthm fn2-ribbon-adding-keys-keeps-pool-type
   (let ((result (fn2-rba-call fn2-rba-adds keys slot gen off)))
     (implies (and (fn2-ribbon-typed-pool-p fn2-pool) (fn2-ribbon-keysp keys)
                   (fn2-ribbon-adding-p (len keys) slots seed fn2-ribbon-builds)
                   (fn2-ribbon-band-ready-p slots fn2-ribbon-band)
                   (< 300 (fn2-fields-rows fn2-fields)) (natp off) (<= off 32768)
                   (fn2-ribbon-arena-p slot gen 9 0 1 off 65536 fn2-pool))
              (fn2-ribbon-typed-pool-p (mv-nth 6 result))))
   :hints (("Goal"
            :induct (fn2-rba-call fn2-ribbon-adds-induct keys slot gen off)
            :in-theory (e/d (fn2-rba-adds)
                         (fn2-ribbon-typed-pool-p fn2-ribbon-adding-p fn2-ribbon-band-ready-p fn2-ribbon-arena-p
                          fn2-ribbon-key-placement fn2-ribbon-key-equation fn2-ribbon-band-satisfied-p
                          fn2-ribbon-bytes-at-p fn2-ribbon-bytesp fn2-run-load-values fn2-run-load-bytes
                          fn2-ribbon-add fn2-rba-drive fn2-ribbon-key-reference
                          fn2-ribbon-emit-reads fn2-ribbon-probe-dot fn2-fields-rows))
            :expand ((fn2-rba-call fn2-rba-adds keys slot gen off) (len keys) (fn2-ribbon-keysp keys) (fn2-ribbon-key-equations-p keys slots seed z)))
           ("Subgoal *1/2"
            :use ((:instance fn2-ribbon-adapter-adds-one-equation (bytes (car keys)) (remaining (len keys)))
                  (:instance fn2-ribbon-key-reference (bytes (car keys)) (row 300))
                  (:instance fn2-ribbon-key-load-in-arena (bytes (car keys)) (row 300)))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-emitted-and-padded-pool-typed
   (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256)) (fn2-ribbon-typed-pool-p (mv-nth 2 (fn2-ribbon-padded-state keys))))
   :hints (("Goal" :use (fn2-ribbon-key-reservation-has-typed-pool fn2-ribbon-initial-page-and-key-arenas
                        (:instance fn2-ribbon-drive-clears-fresh-band (n (len keys))) (:instance fn2-ribbon-fresh-state-shape (n (len keys)))
                        (:instance fn2-ribbon-adding-keys-keeps-pool-type (slot (mv-nth 1 (fn2-ribbon-key-reservation))) (gen (mv-nth 2 (fn2-ribbon-key-reservation)))
                   (slots (fn2-ribbon-slots (len keys))) (seed (fn2-ribbon-seed 7)) (off 0)
                   (fn2-ribbon-builds (mv-nth 1 (fn2-ribbon-ready-state (len keys))))
                   (fn2-ribbon-band (mv-nth 2 (fn2-ribbon-ready-state (len keys))))
                   (fn2-run-writers (mv-nth 3 (fn2-ribbon-ready-state (len keys))))
                   (fn2-run-restarts (mv-nth 4 (fn2-ribbon-ready-state (len keys))))
                   (fn2-fields (mv-nth 5 (fn2-ribbon-ready-state (len keys))))
                   (fn2-pool (mv-nth 3 (fn2-ribbon-key-reservation)))
                   (fn2-fc (mv-nth 7 (fn2-ribbon-ready-state (len keys))))
                   (fn2-fc-context (mv-nth 8 (fn2-ribbon-ready-state (len keys))))
                   (fn2-b3 (mv-nth 9 (fn2-ribbon-ready-state (len keys))))
                   (fn2-digests (mv-nth 10 (fn2-ribbon-ready-state (len keys))))))
            :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-padded-state fn2-ribbon-emitted-step fn2-ribbon-added-state
                  fn2-ribbon-emitter-keeps-pool-type fn2-ribbon-padding-end-keeps-pool-type mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp))
                        (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-page-at-sealing-typed
   (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256)) (fn2-ribbon-typed-pool-p (mv-nth 6 (fn2-ribbon-sealing-state keys))))
   :hints (("Goal" :use (fn2-ribbon-image-reaches-heading fn2-ribbon-emitted-and-padded-pool-typed
                   fn2-ribbon-fresh-added-environment (:instance fn2-ribbon-initial-checker-and-restart-tables (n (len keys)))
                   (:instance fn2-ribbon-heading-establishes-serialized-solution
                     (count (- 65536 (+ *fn2-ribbon-base* (fn2-ribbon-slots (len keys))))) (start (+ *fn2-ribbon-base* (fn2-ribbon-slots (len keys))))
                     (n (len keys)) (slots (fn2-ribbon-slots (len keys))) (slot 0) (gen 1)
                     (fn2-ribbon-builds (fn2-ribbon-builds-set-phase 0 *fn2-ribbon-phase-heading* (mv-nth 1 (fn2-ribbon-emitted-step keys)))) (fn2-run-writers (mv-nth 1 (fn2-ribbon-padded-state keys))) (fn2-fields (mv-nth 5 (fn2-ribbon-added-state keys)))
                     (fn2-pool (mv-nth 2 (fn2-ribbon-padded-state keys))) (fn2-fc-context (mv-nth 8 (fn2-ribbon-added-state keys))) (fn2-ribbon-band (mv-nth 2 (fn2-ribbon-solved-step keys)))))
            :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-heading-invariant-p fn2-ribbon-sealing-state
                 fn2-ribbon-load-keeps-pool-type fn2-ribbon-headed-step (:t fn2-ribbon-slots) natp mv-nth-of-cons (:e zp) (:e binary-+) (:e mv-nth) car-cons cdr-cons (:e <) (:e equal)) (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-page-decoded-keeps-checker-rows
   (equal (fn2-fc-rows (mv-nth 1 (fn2-fc-decoded 0 :page 0 65536 0 next fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))) (fn2-fc-rows fn2-fc))
   :hints (("Goal" :in-theory (e/d (fn2-fc-decoded fn2-fc-rows fn2-fc-set-geom update-fn2-fc-geom$ai fn2-fc-set-previous-seal-offset update-fn2-fc-previous-seal-offset$ai fn2-fc-set-zero update-fn2-fc-zero$ai fn2-fc-set-pad update-fn2-fc-pad$ai fn2-fc-set-pad-end update-fn2-fc-pad-end$ai fn2-fc-set-pos update-fn2-fc-pos$ai fn2-fc-set-phase update-fn2-fc-phase$ai) (fn2-fc-identity fn2-fields-value nth update-nth))))))

(local
 (defthm fn2-ribbon-header-decode-keeps-checker-rows
   (let ((r (fn2-format-run :page sealp 0 0 1 0 65536 0 9 0 1 4096 fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
     (implies (and (equal (fn2-fc-phase 0 fn2-fc) *fn2-fc-phase-decode*) (equal (mv-nth 0 r) :more))
        (equal (fn2-fc-rows (mv-nth 1 r)) (fn2-fc-rows fn2-fc))))
   :hints (("Goal" :in-theory (union-theories '(fn2-format-run fn2-fc-step fn2-ribbon-page-decoded-keeps-checker-rows
                          (:t fn2-fc-decoded) (:t fn2-fc-decode-step) (:e member-equal) (:e posp) mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-fresh-hash-workspace-after-init
   (let* ((st (fn2-ribbon-fresh-state n)) (init (fn2-b3-init 0 0 (fn2-digest-slot 0 *fn2-b3-key*) (mv-nth 10 st) (mv-nth 9 st))))
     (fn2-ribbon-hash-workspace-p (mv-nth 1 init) (mv-nth 0 init)))
   :hints (("Goal" :expand ((create-fn2-fc) (create-fn2-fc-context) (create-fn2-digests) (create-fn2-b3)) :in-theory (union-theories '(fn2-ribbon-fresh-state fn2-rba-setup mv-nth-of-cons car-cons cdr-cons
                            (:e zp) (:e binary-+) (:e fn2-fc-phase) (:e fn2-fc-rows) (:e fn2-fc-context-rows)
                            (:e create-fn2-fc) (:e create-fn2-fc-context) (:e create-fn2-b3) (:e create-fn2-digests)
                            (:e make-list-ac) (:e cons) (:e fn2-digest-slot) (:e fn2-b3-init) (:e mv-nth) (:e create-fn2-run-restarts) (:e fn2-digests-init) (:e fn2-b3-table-init) (:e fn2-fc-init)
                            (:e fn2-fc-context-init) (:e fn2-ribbon-hash-workspace-p) (:e fn2-b3-ready) (:e fn2-digest-rowp)
                            fn2-run-restarts-init-wfp fn2-run-restarts-init-rows (:e natp) (:e <))
                           (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-image-starts-hash-workspace
   (let* ((st (fn2-ribbon-sealing-state keys)) (dec (fn2-ribbon-next-sealing-state st)))
     (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256))
        (and (fn2-ribbon-hash-workspace-p (mv-nth 9 dec) (mv-nth 10 dec))
             (fn2-ribbon-hash-cursor-p 0 (mv-nth 9 dec)))))
   :hints (("Goal" :use (fn2-ribbon-image-sealing-resources fn2-ribbon-image-hash-initialization
                         fn2-ribbon-fresh-added-environment (:instance fn2-ribbon-fresh-hash-workspace-after-init (n (len keys)))
                         (:instance fn2-ribbon-page-begins-check (sealp t) (slot 0) (gen 1) (fn2-fields (mv-nth 5 (fn2-ribbon-sealing-state keys)))
                    (fn2-pool (mv-nth 6 (fn2-ribbon-sealing-state keys)))
                    (fn2-fc (mv-nth 7 (fn2-ribbon-sealing-state keys)))
                    (fn2-fc-context (mv-nth 8 (fn2-ribbon-sealing-state keys)))
                    (fn2-b3 (mv-nth 9 (fn2-ribbon-sealing-state keys)))
                    (fn2-digests (mv-nth 10 (fn2-ribbon-sealing-state keys)))))
            :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-next-sealing-state fn2-ribbon-sealing-state
                       (:t fn2-b3-init) fn2-ribbon-hash-init-cursor mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defun-nx fn2-ribbon-seal-hash-state-p (n pad st)
   (and (fn2-ribbon-sealing-resources-p n 0 1 (mv-nth 1 st) (mv-nth 3 st) (mv-nth 5 st) (mv-nth 7 st) (mv-nth 8 st) (mv-nth 9 st) (mv-nth 10 st))
        (fn2-ribbon-typed-pool-p (mv-nth 6 st))
        (fn2-ribbon-hash-input-p pad (mv-nth 6 st))
        (fn2-ribbon-hash-state-p pad (mv-nth 7 st) (mv-nth 9 st) (mv-nth 10 st)))))

(local
 (defthm fn2-ribbon-format-snapshot-frames
   (let ((next (fn2-ribbon-next-sealing-state st)))
     (and (equal (mv-nth 1 next) (mv-nth 1 st))
          (equal (mv-nth 2 next) (mv-nth 2 st))
          (equal (mv-nth 3 next) (mv-nth 3 st))
          (equal (mv-nth 4 next) (mv-nth 4 st))
          (equal (mv-nth 8 next) (mv-nth 8 st))
          (equal (fn2-fields-rows (mv-nth 5 next)) (fn2-fields-rows (mv-nth 5 st)))
          (implies (and (equal (fn2-fc-phase 0 (mv-nth 7 st)) *fn2-fc-phase-decode*) (equal (mv-nth 0 next) :more))
                   (equal (fn2-fc-rows (mv-nth 7 next)) (fn2-fc-rows (mv-nth 7 st))))))
   :hints (("Goal" :in-theory (union-theories '(fn2-ribbon-next-sealing-state fn2-ribbon-format-step-keeps-field-count
                     fn2-ribbon-header-decode-keeps-checker-rows (:t fn2-format-run) mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-image-prefix-has-hashing-invariant
   (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256)) (fn2-ribbon-seal-hash-state-p (len keys) (+ *fn2-ribbon-base* (fn2-ribbon-slots (len keys))) (fn2-ribbon-next-sealing-state (fn2-ribbon-next-sealing-state (fn2-ribbon-sealing-state keys)))))
   :hints (("Goal" :use ((:instance fn2-ribbon-adapter-slot-bound (n (len keys))) fn2-ribbon-page-at-sealing-typed fn2-ribbon-image-reaches-hash-prefix fn2-ribbon-image-hash-input-padding
                        fn2-ribbon-image-starts-hash-workspace fn2-ribbon-image-reaches-header-decode fn2-ribbon-image-hash-initialization
                        (:instance fn2-ribbon-sealing-decodes-page (n (len keys)) (st (fn2-ribbon-next-sealing-state (fn2-ribbon-sealing-state keys))) (old-fields (mv-nth 5 (fn2-ribbon-sealing-state keys)))))
            :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-seal-hash-state-p fn2-ribbon-sealing-resources-p
                fn2-ribbon-hash-state-p fn2-ribbon-hash-input-p fn2-ribbon-format-snapshot-frames
                posp natp (:t fn2-ribbon-slots) (:e equal) (:e <)) (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-next-sealing-state-hashes
   (let* ((next (fn2-ribbon-next-sealing-state st)) (remaining (fn2-ribbon-hash-remaining (mv-nth 7 st))))
      (implies (and (fn2-ribbon-seal-hash-state-p n pad st) (< 0 remaining))
        (and (equal (mv-nth 0 next) :more) (fn2-ribbon-seal-hash-state-p n pad next)
             (< (fn2-ribbon-hash-remaining (mv-nth 7 next)) remaining))))
   :hints (("Goal" :use ((:instance fn2-ribbon-page-hash-step-progress (sealp t) (fn2-fields (mv-nth 5 st)) (fn2-pool (mv-nth 6 st)) (fn2-fc (mv-nth 7 st)) (fn2-fc-context (mv-nth 8 st)) (fn2-b3 (mv-nth 9 st)) (fn2-digests (mv-nth 10 st))))
          :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-seal-hash-state-p fn2-ribbon-sealing-resources-p
                 fn2-ribbon-typed-pool-p fn2-ribbon-hash-state-p fn2-ribbon-hash-workspace-p
                 fn2-ribbon-next-sealing-state (:t fn2-format-run) mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-sealing-completes-format-run
   (let ((run (fn2-format-run :page t 0 slot gen 0 65536 0 9 0 1 4096 fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
     (implies (and (fn2-ribbon-sealing-resources-p n slot gen fn2-ribbon-builds fn2-run-writers fn2-fields fn2-fc fn2-fc-context fn2-b3 fn2-digests) (equal (mv-nth 0 run) :ok))
              (equal (fn2-ribbon-seal 0 4096 fn2-ribbon-builds fn2-run-writers fn2-fc fn2-fc-context
                             fn2-b3 fn2-fields fn2-pool fn2-digests)
                     (list :sealed (fn2-ribbon-builds-set-phase 0 *fn2-ribbon-phase-sealed* fn2-ribbon-builds)
                             (fn2-run-writers-set-phase 0 *fn2-run-writer-phase-sealed* fn2-run-writers) (mv-nth 1 run) (mv-nth 2 run)
                           (mv-nth 3 run) (mv-nth 4 run) (mv-nth 5 run)))))
   :hints (("Goal" :use ((:instance fn2-ribbon-lower-digest-row-available (r (fn2-digest-slot 0 *fn2-fc-geometry*)))
                          (:instance fn2-ribbon-lower-digest-row-available (r (fn2-digest-slot 0 *fn2-fc-previous-seal*))))
            :in-theory (union-theories '(fn2-ribbon-seal fn2-run-seal-step fn2-ribbon-sealing-resources-p fn2-ribbon-build-identity-p
                       fn2-ribbon-writer-identity-p fn2-ribbon-seal-context-p (:e equal) (:e <) (:e natp)
                       (:e fn2-digest-slot) (:e binary-+) (:e not) (:e if)) (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-drive-returns-completed-page
   (let ((run (fn2-format-run :page t 0 slot gen 0 65536 0 9 0 1 4096 fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
     (implies (and (posp fuel) (fn2-ribbon-sealing-resources-p n slot gen fn2-ribbon-builds fn2-run-writers fn2-fields fn2-fc fn2-fc-context fn2-b3 fn2-digests) (equal (mv-nth 0 run) :ok))
              (equal (fn2-rba-call fn2-rba-drive fuel)
                     (list :sealed (fn2-ribbon-builds-set-phase 0 *fn2-ribbon-phase-sealed* fn2-ribbon-builds)
                         fn2-ribbon-band (fn2-run-writers-set-phase 0 *fn2-run-writer-phase-sealed* fn2-run-writers) fn2-run-restarts
                       (mv-nth 3 run) (mv-nth 4 run) (mv-nth 1 run) fn2-fc-context (mv-nth 2 run) (mv-nth 5 run)))))
   :hints (("Goal" :use fn2-ribbon-sealing-completes-format-run
            :expand ((fn2-rba-call fn2-rba-drive fuel))
            :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-work fn2-ribbon-sealing-resources-p fn2-ribbon-build-identity-p
               mv-nth-of-cons car-cons cdr-cons (:e natp) (:e <) (:e zp) (:e binary-+) (:e equal) (:e not) zp-open posp
               (:compound-recognizer zp-compound-recognizer)) (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defun-nx fn2-ribbon-before-finalization (fuel st)
   (declare (xargs :measure (nfix fuel)))
   (if (or (zp fuel) (not (< 0 (fn2-ribbon-hash-remaining (mv-nth 7 st))))) st
     (fn2-ribbon-before-finalization (1- fuel) (fn2-ribbon-next-sealing-state st)))))

(local
 (defun-nx fn2-ribbon-sealed-output (st)
   (let* ((fc (mv-nth 7 st)) (b3 (mv-nth 9 st)) (ds (mv-nth 10 st))
          (final (fn2-b3-finalize 125 0 ds b3))
          (ctx-fc (fn2-fc-set-pos 0 0 (fn2-fc-set-phase 0 *fn2-fc-phase-digest* fc))))
    (fn2-ribbon-call-with-state list (:sealed) st
       (1 (fn2-ribbon-builds-set-phase 0 *fn2-ribbon-phase-sealed* (mv-nth 1 st)))
       (3 (fn2-run-writers-set-phase 0 *fn2-run-writer-phase-sealed* (mv-nth 3 st)))
       (7 (fn2-fc-reset 0 ctx-fc)) (10 (fn2-digest-copy 136 125 final))))))

(local
 (defthm fn2-ribbon-complete-hash-returns-sealed-output
    (implies (and (posp fuel) (fn2-ribbon-seal-hash-state-p n pad st) (equal (fn2-ribbon-hash-remaining (mv-nth 7 st)) 0))
      (equal (fn2-ribbon-call-with-state fn2-rba-drive (fuel) st) (fn2-ribbon-sealed-output st)))
    :hints (("Goal" :use ((:instance fn2-ribbon-page-hash-completes-seal (fn2-fields (mv-nth 5 st)) (fn2-pool (mv-nth 6 st)) (fn2-fc (mv-nth 7 st)) (fn2-fc-context (mv-nth 8 st)) (fn2-b3 (mv-nth 9 st)) (fn2-digests (mv-nth 10 st)))
                           (:instance fn2-ribbon-drive-returns-completed-page (slot 0) (gen 1) (fn2-ribbon-builds (mv-nth 1 st)) (fn2-ribbon-band (mv-nth 2 st)) (fn2-run-writers (mv-nth 3 st)) (fn2-run-restarts (mv-nth 4 st)) (fn2-fields (mv-nth 5 st)) (fn2-pool (mv-nth 6 st)) (fn2-fc (mv-nth 7 st)) (fn2-fc-context (mv-nth 8 st)) (fn2-b3 (mv-nth 9 st)) (fn2-digests (mv-nth 10 st))))
             :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-sealed-output fn2-ribbon-seal-hash-state-p
                    fn2-ribbon-sealing-resources-p fn2-ribbon-seal-context-p mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory))))
    :rule-classes nil))

(local
 (defthm fn2-ribbon-sealing-remaining-bounds
    (implies (fn2-ribbon-seal-hash-state-p n pad st) (and (natp (fn2-ribbon-hash-remaining (mv-nth 7 st))) (<= (fn2-ribbon-hash-remaining (mv-nth 7 st)) 65557)))
    :hints (("Goal" :use ((:instance fn2-ribbon-hash-remaining-bounds (fn2-fc (mv-nth 7 st)) (fn2-b3 (mv-nth 9 st)) (fn2-digests (mv-nth 10 st))))
             :in-theory (union-theories '(fn2-ribbon-seal-hash-state-p) (theory 'minimal-theory))))
    :rule-classes nil))

(local (defthm fn2-ribbon-hashing-resources (implies (fn2-ribbon-seal-hash-state-p n pad st) (fn2-ribbon-sealing-resources-p n 0 1 (mv-nth 1 st) (mv-nth 3 st) (mv-nth 5 st) (mv-nth 7 st) (mv-nth 8 st) (mv-nth 9 st) (mv-nth 10 st))) :hints (("Goal" :in-theory (union-theories '(fn2-ribbon-seal-hash-state-p) (theory 'minimal-theory)))) :rule-classes nil))

(local
 (defthm fn2-ribbon-sealing-drive-runs-hash-to-completion
   (let ((end (fn2-ribbon-before-finalization fuel st)))
     (implies (and (natp fuel) (fn2-ribbon-seal-hash-state-p n pad st) (< (fn2-ribbon-hash-remaining (mv-nth 7 st)) fuel))
       (and (equal (fn2-ribbon-call-with-state fn2-rba-drive (fuel) st) (fn2-ribbon-sealed-output end))
            (fn2-ribbon-seal-hash-state-p n pad end)
            (equal (fn2-ribbon-hash-remaining (mv-nth 7 end)) 0))))
   :hints (("Goal" :induct (fn2-ribbon-before-finalization fuel st)
            :expand ((fn2-ribbon-before-finalization fuel st))
            :do-not '(preprocess) :in-theory (union-theories '((:i fn2-ribbon-before-finalization)
                    (:compound-recognizer zp-compound-recognizer) zp-open natp posp mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory)))
           ("Subgoal *1/1" :use (fn2-ribbon-sealing-remaining-bounds fn2-ribbon-complete-hash-returns-sealed-output))
           ("Subgoal *1/2" :use (fn2-ribbon-hashing-resources fn2-ribbon-sealing-remaining-bounds fn2-ribbon-next-sealing-state-hashes fn2-ribbon-drive-after-format-step
                       (:instance fn2-ribbon-sealing-remaining-bounds (st (fn2-ribbon-next-sealing-state st))))
             :in-theory (union-theories '((:compound-recognizer zp-compound-recognizer) natp posp zp-open mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory))))
   :rule-classes nil))

(local (defun-nx fn2-ribbon-sealer-end (keys) (fn2-ribbon-before-finalization (1- (1- (1- (mv-nth 0 (fn2-ribbon-padded-state keys))))) (fn2-ribbon-next-sealing-state (fn2-ribbon-next-sealing-state (fn2-ribbon-sealing-state keys))))))

(local (defthm fn2-ribbon-final-drive-completes-sealing (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256)) (and (equal (fn2-ribbon-final-drive keys) (fn2-ribbon-sealed-output (fn2-ribbon-sealer-end keys))) (fn2-ribbon-seal-hash-state-p (len keys) (+ *fn2-ribbon-base* (fn2-ribbon-slots (len keys))) (fn2-ribbon-sealer-end keys)) (equal (fn2-ribbon-hash-remaining (mv-nth 7 (fn2-ribbon-sealer-end keys))) 0))) :hints (("Goal" :use (fn2-ribbon-image-reaches-heading fn2-ribbon-image-reaches-hash-prefix fn2-ribbon-image-prefix-has-hashing-invariant (:instance fn2-ribbon-sealing-remaining-bounds (n (len keys)) (pad (+ *fn2-ribbon-base* (fn2-ribbon-slots (len keys)))) (st (fn2-ribbon-next-sealing-state (fn2-ribbon-next-sealing-state (fn2-ribbon-sealing-state keys))))) (:instance fn2-ribbon-sealing-drive-runs-hash-to-completion (fuel (1- (1- (1- (mv-nth 0 (fn2-ribbon-padded-state keys)))))) (n (len keys)) (pad (+ *fn2-ribbon-base* (fn2-ribbon-slots (len keys)))) (st (fn2-ribbon-next-sealing-state (fn2-ribbon-next-sealing-state (fn2-ribbon-sealing-state keys)))))) :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-sealer-end natp posp mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory)))) :rule-classes nil))

(defthm fn2-ribbon-image-seals (implies (and (fn2-ribbon-keysp keys) (consp keys) (<= (len keys) 256)) (equal (car (fn2-ribbon-image keys nil queries nil)) :sealed)) :hints (("Goal" :use (fn2-ribbon-image-reaches-final-drive fn2-ribbon-final-drive-completes-sealing) :expand ((len keys)) :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-sealed-output posp (:t len) mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory)))) :rule-classes nil)

(local
 (defun-nx fn2-ribbon-next-checking-state (st)
   (let ((run (fn2-format-run :page nil 0 0 1 0 65536 0 9 0 1 4096 (mv-nth 7 st) (mv-nth 8 st)
                             (mv-nth 9 st) (mv-nth 5 st) (mv-nth 6 st) (mv-nth 10 st))))
     (fn2-ribbon-call-with-state list ((mv-nth 0 run)) st
       (5 (mv-nth 3 run)) (6 (mv-nth 4 run)) (7 (mv-nth 1 run)) (9 (mv-nth 2 run)) (10 (mv-nth 5 run))))))

(local
 (defun-nx fn2-ribbon-before-check-finalization (fuel st)
   (declare (xargs :measure (nfix fuel)))
   (if (or (zp fuel) (not (< 0 (fn2-ribbon-hash-remaining (mv-nth 7 st))))) st
     (fn2-ribbon-before-check-finalization (1- fuel) (fn2-ribbon-next-checking-state st)))))

(local
 (defthm fn2-ribbon-page-init-keeps-workspace
   (implies (and (fn2-ribbon-hash-workspace-p fn2-b3 fn2-digests) t)
      (fn2-ribbon-hash-workspace-p (mv-nth 1 (fn2-b3-init 0 0 1 fn2-digests fn2-b3)) (mv-nth 0 (fn2-b3-init 0 0 1 fn2-digests fn2-b3))))
   :hints (("Goal" :use ((:instance fn2-b3-init-shape (row 0) (mode 0) (key 1)))
            :in-theory (e/d (mv-nth fn2-ribbon-hash-workspace-p fn2-b3-ready fn2-digest-rowp fn2-digest-workspacep fn2-b3-words-length) (fn2-b3p fn2-digestsp fn2-b3-wfp fn2-digests-wfp fn2-b3-rows fn2-digests-rows fn2-poolp fn2-pool-wfp nth fn2-b3-init fn2-b3-init-shape))))))

(local
 (defthm fn2-ribbon-finalize-keeps-workspace
   (implies (and (fn2-ribbon-hash-workspace-p fn2-b3 fn2-digests) t)
      (fn2-ribbon-hash-workspace-p fn2-b3 (fn2-b3-finalize 125 0 fn2-digests fn2-b3)))
   :hints (("Goal" :use ((:instance fn2-b3-finalize-shape (row 0) (dst 125)))
            :in-theory (e/d (fn2-ribbon-hash-workspace-p fn2-b3-ready fn2-digest-rowp fn2-digest-workspacep fn2-b3-words-length) (fn2-b3p fn2-digestsp fn2-b3-wfp fn2-digests-wfp fn2-b3-rows fn2-digests-rows fn2-poolp fn2-pool-wfp nth fn2-b3-finalize fn2-b3-finalize-shape))))))

(local
 (defthm fn2-ribbon-copy-keeps-workspace
   (implies (and (fn2-ribbon-hash-workspace-p fn2-b3 fn2-digests) t)
      (fn2-ribbon-hash-workspace-p fn2-b3 (fn2-digest-copy 136 125 fn2-digests)))
   :hints (("Goal" :use ((:instance fn2-digest-copy-shape (src 125) (dst 136)))
            :in-theory (e/d (fn2-ribbon-hash-workspace-p fn2-b3-ready fn2-digest-rowp fn2-digest-workspacep fn2-b3-words-length) (fn2-b3p fn2-digestsp fn2-b3-wfp fn2-digests-wfp fn2-b3-rows fn2-digests-rows fn2-poolp fn2-pool-wfp nth fn2-digest-copy fn2-digest-copy-shape))))))

(local
 (defthm fn2-ribbon-hashing-observes-fc-updates
   (let ((p (fn2-fc-set-pos 0 v fn2-fc)) (s (fn2-fc-set-phase 0 v fn2-fc)))
     (and (equal (fn2-fc-phase 0 p) (fn2-fc-phase 0 fn2-fc))
          (equal (fn2-fc-phase 0 s) v)
          (equal (fn2-fc-pos 0 p) v)
          (equal (fn2-fc-pos 0 s) (fn2-fc-pos 0 fn2-fc))
          (equal (fn2-fc-pad 0 p) (fn2-fc-pad 0 fn2-fc))
          (equal (fn2-fc-pad 0 s) (fn2-fc-pad 0 fn2-fc))
          (equal (fn2-fc-pad-end 0 p) (fn2-fc-pad-end 0 fn2-fc))
          (equal (fn2-fc-pad-end 0 s) (fn2-fc-pad-end 0 fn2-fc))
          (equal (fn2-fc-rows p) (fn2-fc-rows fn2-fc))
          (equal (fn2-fc-rows s) (fn2-fc-rows fn2-fc))))
   :hints (("Goal" :in-theory (enable fn2-fc-phase fn2-fc-pos fn2-fc-pad fn2-fc-pad-end fn2-fc-rows fn2-fc-set-pos update-fn2-fc-pos$ai fn2-fc-set-phase update-fn2-fc-phase$ai)))))

(local
 (defthm fn2-ribbon-checking-snapshot-frames
   (let ((next (fn2-ribbon-next-checking-state st)))
     (and (equal (mv-nth 1 next) (mv-nth 1 st))
          (equal (mv-nth 2 next) (mv-nth 2 st))
          (equal (mv-nth 3 next) (mv-nth 3 st))
          (equal (mv-nth 4 next) (mv-nth 4 st))
          (equal (mv-nth 8 next) (mv-nth 8 st))
          (equal (fn2-fields-rows (mv-nth 5 next)) (fn2-fields-rows (mv-nth 5 st)))
          (implies (and (equal (fn2-fc-phase 0 (mv-nth 7 st)) *fn2-fc-phase-decode*) (equal (mv-nth 0 next) :more))
                   (equal (fn2-fc-rows (mv-nth 7 next)) (fn2-fc-rows (mv-nth 7 st))))))
   :hints (("Goal" :in-theory (union-theories '(fn2-ribbon-next-checking-state fn2-ribbon-format-step-keeps-field-count
                     fn2-ribbon-header-decode-keeps-checker-rows (:t fn2-format-run) mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory))))))

(local
 (defthm fn2-ribbon-checking-decodes-page
   (let ((next (fn2-ribbon-next-checking-state st)))
     (implies (and (posp n) (<= n 256) (< 301 (fn2-fields-rows old-fields))
                   (equal (mv-nth 5 st) (fn2-fc-start :page 0 old-fields))
                   (equal (fn2-fc-phase 0 (mv-nth 7 st)) *fn2-fc-phase-decode*)
                   (fn2-ribbon-seal-context-p (mv-nth 8 st))
                   (fn2-ribbon-arena-p 0 1 9 0 1 65536 65536 (mv-nth 6 st))
                   (fn2-ribbon-physical-headers-p n 0 1 (mv-nth 6 st)))
              (and (equal (mv-nth 0 next) :more)
                   (equal (mv-nth 6 next) (mv-nth 6 st)) (equal (mv-nth 9 next) (mv-nth 9 st))
                   (equal (mv-nth 10 next) (mv-nth 10 st))
                   (equal (fn2-fc-phase 0 (mv-nth 7 next)) *fn2-fc-phase-prefix*)
                   (equal (fn2-fc-pos 0 (mv-nth 7 next)) 0)
                   (equal (fn2-fc-pad 0 (mv-nth 7 next)) (+ *fn2-ribbon-base* (fn2-ribbon-slots n)))
                   (equal (fn2-fc-pad-end 0 (mv-nth 7 next)) 65536)
                   (equal (fn2-fc-zero 0 (mv-nth 7 next)) 65536))))
   :hints (("Goal" :use ((:instance fn2-ribbon-check-establishes-page-hash-bounds (sealp nil) (slot 0) (gen 1) (fn2-fields old-fields) (fn2-pool (mv-nth 6 st)) (fn2-fc (mv-nth 7 st)) (fn2-fc-context (mv-nth 8 st)) (fn2-b3 (mv-nth 9 st)) (fn2-digests (mv-nth 10 st))))
            :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-next-checking-state (:e unsigned-byte-p) mv-nth-of-cons (:e zp) (:e binary-+) (:e mv-nth) car-cons cdr-cons (:e <) (:e equal))
                           (theory 'minimal-theory))))
   :rule-classes nil))

(local (defun-nx fn2-ribbon-checker-entry-p (pad st)
 (and (fn2-ribbon-seal-context-p (mv-nth 8 st)) (< 301 (fn2-fields-rows (mv-nth 5 st)))
      (< 0 (fn2-fc-rows (mv-nth 7 st))) (equal (fn2-fc-phase 0 (mv-nth 7 st)) *fn2-fc-phase-idle*)
      (fn2-ribbon-hash-workspace-p (mv-nth 9 st) (mv-nth 10 st)) (fn2-ribbon-hash-input-p pad (mv-nth 6 st))
      (fn2-ribbon-typed-pool-p (mv-nth 6 st)))))

(local (defthm fn2-ribbon-sealed-output-ready-for-checker
 (implies (fn2-ribbon-seal-hash-state-p n pad st) (fn2-ribbon-checker-entry-p pad (fn2-ribbon-sealed-output st)))
 :hints (("Goal" :in-theory (union-theories '(fn2-ribbon-seal-hash-state-p fn2-ribbon-sealing-resources-p fn2-ribbon-hash-state-p fn2-ribbon-checker-entry-p fn2-ribbon-sealed-output fn2-ribbon-finalize-keeps-workspace fn2-ribbon-copy-keeps-workspace fn2-fc-reset fn2-ribbon-hashing-observes-fc-updates mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory)))) :rule-classes nil))

(local (defthm fn2-ribbon-sealed-image-ready-for-checker
  (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256)) (and (fn2-ribbon-checker-entry-p (+ *fn2-ribbon-base* (fn2-ribbon-slots (len keys))) (fn2-ribbon-final-drive keys)) (fn2-ribbon-physical-headers-p (len keys) 0 1 (mv-nth 6 (fn2-ribbon-final-drive keys)))))
  :hints (("Goal" :use (fn2-ribbon-final-drive-completes-sealing (:instance fn2-ribbon-sealed-output-ready-for-checker (n (len keys)) (pad (+ *fn2-ribbon-base* (fn2-ribbon-slots (len keys)))) (st (fn2-ribbon-sealer-end keys))) fn2-ribbon-checked-page-holds-key-equations)
    :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-final-check fn2-ribbon-rba-check-preserves-page mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory)))) :rule-classes nil))

(local (defun-nx fn2-ribbon-check-hash-state-p (pad st)
  (and (fn2-ribbon-hash-input-p pad (mv-nth 6 st)) (fn2-ribbon-typed-pool-p (mv-nth 6 st))
       (fn2-ribbon-seal-context-p (mv-nth 8 st)) (fn2-ribbon-hash-state-p pad (mv-nth 7 st) (mv-nth 9 st) (mv-nth 10 st)))))

(local (defthm fn2-ribbon-check-starts-decode
  (let ((next (fn2-ribbon-next-checking-state st)) (init (fn2-b3-init 0 0 1 (mv-nth 10 st) (mv-nth 9 st))))
   (implies (fn2-ribbon-checker-entry-p pad st)
     (and (equal (mv-nth 0 next) :more) (equal (mv-nth 6 next) (mv-nth 6 st))
          (equal (mv-nth 5 next) (fn2-fc-start :page 0 (mv-nth 5 st))) (equal (fn2-fc-phase 0 (mv-nth 7 next)) *fn2-fc-phase-decode*)
          (equal (fn2-fc-rows (mv-nth 7 next)) (fn2-fc-rows (mv-nth 7 st)))
          (equal (mv-nth 9 next) (mv-nth 1 init)) (equal (mv-nth 10 next) (mv-nth 0 init)))))
  :hints (("Goal" :use ((:instance fn2-ribbon-page-begins-check (slot 0) (gen 1) (sealp nil) (fn2-fields (mv-nth 5 st)) (fn2-pool (mv-nth 6 st)) (fn2-fc (mv-nth 7 st)) (fn2-fc-context (mv-nth 8 st)) (fn2-b3 (mv-nth 9 st)) (fn2-digests (mv-nth 10 st)))) :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-checker-entry-p fn2-ribbon-hash-input-p fn2-ribbon-next-checking-state fn2-ribbon-hashing-observes-fc-updates (:e fn2-digest-slot) mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory)))) :rule-classes nil))

(local (defthm fn2-ribbon-check-starts-hash-at-zero
 (let ((next (fn2-ribbon-next-checking-state st))) (implies (fn2-ribbon-checker-entry-p pad st) (and (fn2-ribbon-hash-workspace-p (mv-nth 9 next) (mv-nth 10 next)) (fn2-ribbon-hash-cursor-p 0 (mv-nth 9 next)))))
 :hints (("Goal" :use (fn2-ribbon-check-starts-decode (:instance fn2-ribbon-page-init-keeps-workspace (fn2-digests (mv-nth 10 st)) (fn2-b3 (mv-nth 9 st))) (:instance fn2-ribbon-hash-init-cursor (key 1) (fn2-digests (mv-nth 10 st)) (fn2-b3 (mv-nth 9 st)))) :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-checker-entry-p (:e fn2-digest-slot)) (theory 'minimal-theory)))) :rule-classes nil))

(local (defthm fn2-ribbon-check-establishes-hash-invariant
 (let* ((pad (+ *fn2-ribbon-base* (fn2-ribbon-slots n))) (decoded (fn2-ribbon-next-checking-state st)) (prefix (fn2-ribbon-next-checking-state decoded)))
   (implies (and (posp n) (<= n 256) (fn2-ribbon-checker-entry-p pad st) (fn2-ribbon-physical-headers-p n 0 1 (mv-nth 6 st)))
    (and (equal (mv-nth 0 decoded) :more) (equal (mv-nth 0 prefix) :more) (fn2-ribbon-check-hash-state-p pad prefix))))
 :hints (("Goal" :use ((:instance fn2-ribbon-check-starts-decode (pad (+ *fn2-ribbon-base* (fn2-ribbon-slots n)))) (:instance fn2-ribbon-check-starts-hash-at-zero (pad (+ *fn2-ribbon-base* (fn2-ribbon-slots n)))) (:instance fn2-ribbon-checking-decodes-page (old-fields (mv-nth 5 st)) (st (fn2-ribbon-next-checking-state st))) (:instance fn2-ribbon-hash-init-cursor (fn2-digests (mv-nth 10 st)) (fn2-b3 (mv-nth 9 st)))) :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-check-hash-state-p fn2-ribbon-checker-entry-p fn2-ribbon-checking-snapshot-frames fn2-ribbon-hash-state-p fn2-ribbon-hash-input-p fn2-ribbon-page-init-keeps-workspace (:e fn2-digest-slot) mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory)))) :rule-classes nil))

(local
 (defthm fn2-ribbon-next-checking-state-hashes
   (let* ((next (fn2-ribbon-next-checking-state st)) (remaining (fn2-ribbon-hash-remaining (mv-nth 7 st))))
      (implies (and (fn2-ribbon-check-hash-state-p pad st) (< 0 remaining))
        (and (equal (mv-nth 0 next) :more) (fn2-ribbon-check-hash-state-p pad next)
             (< (fn2-ribbon-hash-remaining (mv-nth 7 next)) remaining))))
   :hints (("Goal" :use ((:instance fn2-ribbon-page-hash-step-progress (sealp nil) (fn2-fields (mv-nth 5 st)) (fn2-pool (mv-nth 6 st)) (fn2-fc (mv-nth 7 st)) (fn2-fc-context (mv-nth 8 st)) (fn2-b3 (mv-nth 9 st)) (fn2-digests (mv-nth 10 st))))
          :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-check-hash-state-p fn2-ribbon-checking-snapshot-frames
                 fn2-ribbon-typed-pool-p fn2-ribbon-hash-state-p fn2-ribbon-hash-workspace-p
                 fn2-ribbon-next-checking-state (:t fn2-format-run) mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-checking-remaining-bounds
    (implies (fn2-ribbon-check-hash-state-p pad st) (and (natp (fn2-ribbon-hash-remaining (mv-nth 7 st))) (<= (fn2-ribbon-hash-remaining (mv-nth 7 st)) 65557)))
    :hints (("Goal" :use ((:instance fn2-ribbon-hash-remaining-bounds (fn2-fc (mv-nth 7 st)) (fn2-b3 (mv-nth 9 st)) (fn2-digests (mv-nth 10 st))))
             :in-theory (union-theories '(fn2-ribbon-check-hash-state-p) (theory 'minimal-theory))))
    :rule-classes nil))

(local (defun-nx fn2-ribbon-check-status (fuel st) (mv-nth 0 (fn2-format-drive fuel 0 :page nil 0 1 0 65536 0 9 0 1 4096 (mv-nth 7 st) (mv-nth 8 st) (mv-nth 9 st) (mv-nth 5 st) (mv-nth 6 st) (mv-nth 10 st)))))

(local (defthm fn2-ribbon-check-drive-step
 (let ((next (fn2-ribbon-next-checking-state st))) (implies (posp fuel) (equal (fn2-ribbon-check-status fuel st) (if (equal (mv-nth 0 next) :more) (fn2-ribbon-check-status (1- fuel) next) (mv-nth 0 next)))))
 :hints (("Goal" :expand ((fn2-format-drive fuel 0 :page nil 0 1 0 65536 0 9 0 1 4096 (mv-nth 7 st) (mv-nth 8 st) (mv-nth 9 st) (mv-nth 5 st) (mv-nth 6 st) (mv-nth 10 st))) :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-check-status fn2-ribbon-next-checking-state (:t fn2-format-run) (:compound-recognizer zp-compound-recognizer) zp-open posp mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory)))) :rule-classes nil))

(local (defmacro fn2-ribbon-page-call (op prefix sealp)
   (append (list op) prefix (list 0 :page sealp) '(slot gen 0 *fn2-run-page-size* 0 9 0 1)
           '(fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))))

(local
 (defthm fn2-ribbon-matching-digest-byte
   (implies (fn2-digest-equal (fn2-digest-slot 0 *fn2-fc-result*) (fn2-fc-context-hash 0 fn2-fc-context) fn2-digests)
            (equal (fn2-fc-digest-byte 0 i fn2-fc fn2-digests)
                   (fn2-fc-word-byte (fn2-fc-context-hash-word 0 (floor i 4) fn2-fc-context fn2-digests) (mod i 4))))
   :hints (("Goal" :in-theory (e/d (fn2-fc-digest-byte fn2-fc-context-hash-word fn2-digest-equal fn2-digest-word)
                       (nth floor mod fn2-fc-word-byte fn2-fc-context-hash))))))

(local
 (defthm fn2-ribbon-compare-page-hash-byte
   (let ((pos (fn2-fc-pos 0 fn2-fc)) (step (fn2-ribbon-page-call fn2-fc-advance (fuel) nil)))
     (implies (and (equal (fn2-fc-phase 0 fn2-fc) *fn2-fc-phase-digest*)
                   (natp pos) (< pos 32)
                   (fn2-digest-equal (fn2-digest-slot 0 *fn2-fc-result*) (fn2-fc-context-hash 0 fn2-fc-context) fn2-digests))
              (equal step (list (if (equal pos 31) :ok :more) 1 (fn2-fc-set-pos 0 (+ 1 pos) fn2-fc)
                                fn2-b3 fn2-pool fn2-digests))))
   :hints (("Goal" :use ((:instance fn2-ribbon-matching-digest-byte (i (fn2-fc-pos 0 fn2-fc)))) :in-theory (e/d (fn2-fc-advance fn2-fc-byte)
                       (fn2-ribbon-matching-digest-byte nth fn2-fc-phase fn2-fc-pos fn2-fc-set-pos fn2-fc-context-hash fn2-digest-equal
                        fn2-fc-word-byte fn2-fc-context-hash-word fn2-fc-digest-byte fn2-fc-page-span))))))

(local
 (defthm fn2-ribbon-fc-position-update
   (and (equal (fn2-fc-pos 0 (fn2-fc-set-pos 0 i fn2-fc)) i)
        (equal (fn2-fc-phase 0 (fn2-fc-set-pos 0 i fn2-fc)) (fn2-fc-phase 0 fn2-fc)))
   :hints (("Goal" :in-theory (e/d (fn2-fc-pos fn2-fc-phase fn2-fc-set-pos update-fn2-fc-pos$ai)
                                   (nth update-nth))))))

(local
 (defun fn2-ribbon-digest-induct (fuel fn2-fc)
   (declare (xargs :stobjs fn2-fc :verify-guards nil :measure (nfix fuel)))
   (if (zp fuel) fn2-fc
     (let ((fn2-fc (fn2-fc-set-pos 0 (1+ (fn2-fc-pos 0 fn2-fc)) fn2-fc)))
       (fn2-ribbon-digest-induct (1- fuel) fn2-fc)))))

(local
 (defthm fn2-ribbon-page-check-matching-digest
   (let ((pos (fn2-fc-pos 0 fn2-fc)) (run (fn2-ribbon-page-call fn2-fc-run-bytes (fuel) nil)))
     (implies (and (equal (fn2-fc-phase 0 fn2-fc) *fn2-fc-phase-digest*)
                   (natp pos) (< pos 32) (natp fuel) (<= (- 32 pos) fuel)
                   (fn2-digest-equal (fn2-digest-slot 0 *fn2-fc-result*) (fn2-fc-context-hash 0 fn2-fc-context) fn2-digests))
              (and (equal (mv-nth 0 run) :ok) (equal (mv-nth 2 run) fn2-b3)
                   (equal (mv-nth 3 run) fn2-pool) (equal (mv-nth 4 run) fn2-digests))))
   :hints (("Goal" :induct (fn2-ribbon-digest-induct fuel fn2-fc)
            :expand ((fn2-ribbon-page-call fn2-fc-run-bytes (fuel) nil))
            :in-theory (disable nth fn2-fc-run-bytes fn2-fc-advance fn2-fc-set-pos fn2-fc-phase fn2-fc-pos
                                fn2-digest-equal fn2-fc-context-hash)))
   :rule-classes nil))

(local
 (defthm fn2-ribbon-hash-end-position
   (implies (and (fn2-ribbon-hash-state-p pad fn2-fc fn2-b3 fn2-digests) (equal (fn2-ribbon-hash-remaining fn2-fc) 0))
      (and (equal (fn2-fc-phase 0 fn2-fc) *fn2-fc-phase-hash*) (equal (fn2-fc-pos 0 fn2-fc) 65536)))
   :hints (("Goal" :in-theory (e/d (fn2-ribbon-hash-state-p fn2-ribbon-hash-remaining)
                (fn2-fc-phase fn2-fc-pos fn2-fc-pad fn2-fc-pad-end fn2-fc-rows fn2-ribbon-hash-workspace-p)))) :rule-classes nil))

(local
 (defthm fn2-ribbon-hash-end-finalizes
   (implies (and (equal (fn2-fc-phase 0 fn2-fc) *fn2-fc-phase-hash*) (equal (fn2-fc-pos 0 fn2-fc) 65536))
      (equal (fn2-fc-advance fuel 0 :page sealp 0 1 0 65536 0 9 0 1 fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests) (list :more 1 (fn2-fc-set-pos 0 0 (fn2-fc-set-phase 0 *fn2-fc-phase-digest* fn2-fc)) fn2-b3 fn2-pool (fn2-b3-finalize 125 0 fn2-digests fn2-b3))))
   :hints (("Goal" :in-theory (e/d (fn2-fc-advance fn2-fc-page-span fn2-fc-byte)
                    (fn2-fc-phase fn2-fc-pos fn2-fc-pad fn2-fc-pad-end fn2-fc-rows fn2-fc-set-phase fn2-fc-set-pos fn2-b3-finalize fn2-b3-update fn2-b3-byte fn2-fc-prefix-byte))))))

(local
 (defthm fn2-ribbon-page-hash-check-accepts-final-digest
   (implies (and (fn2-ribbon-hash-state-p pad fn2-fc fn2-b3 fn2-digests) (equal (fn2-ribbon-hash-remaining fn2-fc) 0)
                 (equal (fn2-fc-context-hash 0 fn2-fc-context) 136) (fn2-digest-equal 125 136 (fn2-b3-finalize 125 0 fn2-digests fn2-b3)))
     (equal (mv-nth 0 (fn2-format-run :page nil 0 0 1 0 65536 0 9 0 1 4096 fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)) :ok))
   :hints (("Goal" :use (fn2-ribbon-hash-end-position (:instance fn2-ribbon-page-check-matching-digest (fuel 4095) (slot 0) (gen 1) (fn2-fc (fn2-fc-set-pos 0 0 (fn2-fc-set-phase 0 *fn2-fc-phase-digest* fn2-fc))) (fn2-digests (fn2-b3-finalize 125 0 fn2-digests fn2-b3))))
           :expand ((fn2-fc-run-bytes 4096 0 :page nil 0 1 0 65536 0 9 0 1 fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
           :in-theory (union-theories '(fn2-format-run fn2-fc-step fn2-ribbon-hash-end-finalizes (:t fn2-fc-run-bytes) (:e fn2-digest-slot)
               fn2-ribbon-hashing-observes-fc-updates (:e member-equal) (:e posp) (:e unary--) mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory))))
   :rule-classes nil))

(local (defun-nx fn2-ribbon-check-digest-matches-p (st)
 (fn2-digest-equal 125 136 (fn2-b3-finalize 125 0 (mv-nth 10 st) (mv-nth 9 st)))))

(local (defthm fn2-ribbon-check-accepts-at-matching-end
  (implies (and (fn2-ribbon-check-hash-state-p pad st) (equal (fn2-ribbon-hash-remaining (mv-nth 7 st)) 0) (fn2-ribbon-check-digest-matches-p st))
   (equal (mv-nth 0 (fn2-ribbon-next-checking-state st)) :ok))
  :hints (("Goal" :use ((:instance fn2-ribbon-page-hash-check-accepts-final-digest (fn2-fields (mv-nth 5 st)) (fn2-pool (mv-nth 6 st)) (fn2-fc (mv-nth 7 st)) (fn2-fc-context (mv-nth 8 st)) (fn2-b3 (mv-nth 9 st)) (fn2-digests (mv-nth 10 st)))) :do-not '(preprocess)
    :in-theory (union-theories '(fn2-ribbon-check-digest-matches-p fn2-ribbon-check-hash-state-p fn2-ribbon-seal-context-p fn2-ribbon-next-checking-state mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory)))) :rule-classes nil))

(local
 (defthm fn2-ribbon-checking-drive-runs-hash-to-completion
   (let ((end (fn2-ribbon-before-check-finalization fuel st)))
     (implies (and (natp fuel) (fn2-ribbon-check-hash-state-p pad st) (< (fn2-ribbon-hash-remaining (mv-nth 7 st)) fuel))
       (and (implies (fn2-ribbon-check-digest-matches-p end) (equal (fn2-ribbon-check-status fuel st) :ok))
            (fn2-ribbon-check-hash-state-p pad end)
            (equal (fn2-ribbon-hash-remaining (mv-nth 7 end)) 0))))
   :hints (("Goal" :induct (fn2-ribbon-before-check-finalization fuel st)
            :expand ((fn2-ribbon-before-check-finalization fuel st))
            :do-not '(preprocess) :in-theory (union-theories '((:i fn2-ribbon-before-check-finalization)
                    (:compound-recognizer zp-compound-recognizer) zp-open natp posp mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory)))
           ("Subgoal *1/1" :use (fn2-ribbon-checking-remaining-bounds fn2-ribbon-check-accepts-at-matching-end fn2-ribbon-check-drive-step))
           ("Subgoal *1/2" :use (fn2-ribbon-checking-remaining-bounds fn2-ribbon-next-checking-state-hashes fn2-ribbon-check-drive-step
                       (:instance fn2-ribbon-checking-remaining-bounds (st (fn2-ribbon-next-checking-state st))))
             :in-theory (union-theories '((:compound-recognizer zp-compound-recognizer) natp posp zp-open mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory))))
   :rule-classes nil))

(local (defun-nx fn2-ribbon-checker-end (keys)
 (fn2-ribbon-before-check-finalization 135270 (fn2-ribbon-next-checking-state (fn2-ribbon-next-checking-state (fn2-ribbon-final-drive keys))))))

(local (defthm fn2-ribbon-final-check-status
 (equal (mv-nth 0 (fn2-ribbon-final-check keys)) (fn2-ribbon-check-status 135272 (fn2-ribbon-final-drive keys)))
 :hints (("Goal" :in-theory (union-theories '(fn2-ribbon-final-check fn2-rba-check fn2-ribbon-check-status (:e fn2-format-fuel) (:t fn2-format-drive) mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory)))) :rule-classes nil))

(local (defthm fn2-ribbon-final-check-hashes-all-bytes
 (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256)) (and (fn2-ribbon-check-hash-state-p (+ *fn2-ribbon-base* (fn2-ribbon-slots (len keys))) (fn2-ribbon-checker-end keys)) (equal (fn2-ribbon-hash-remaining (mv-nth 7 (fn2-ribbon-checker-end keys))) 0)
   (implies (fn2-ribbon-check-digest-matches-p (fn2-ribbon-checker-end keys)) (equal (mv-nth 0 (fn2-ribbon-final-check keys)) :ok))))
 :hints (("Goal" :use (fn2-ribbon-final-check-status fn2-ribbon-sealed-image-ready-for-checker
   (:instance fn2-ribbon-check-establishes-hash-invariant (n (len keys)) (st (fn2-ribbon-final-drive keys)))
   (:instance fn2-ribbon-check-drive-step (fuel 135272) (st (fn2-ribbon-final-drive keys)))
   (:instance fn2-ribbon-check-drive-step (fuel 135271) (st (fn2-ribbon-next-checking-state (fn2-ribbon-final-drive keys))))
   (:instance fn2-ribbon-checking-remaining-bounds (pad (+ *fn2-ribbon-base* (fn2-ribbon-slots (len keys)))) (st (fn2-ribbon-next-checking-state (fn2-ribbon-next-checking-state (fn2-ribbon-final-drive keys)))))
   (:instance fn2-ribbon-checking-drive-runs-hash-to-completion (pad (+ *fn2-ribbon-base* (fn2-ribbon-slots (len keys)))) (st (fn2-ribbon-next-checking-state (fn2-ribbon-next-checking-state (fn2-ribbon-final-drive keys)))) (fuel 135270)))
  :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-checker-end (:e posp) mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory)))) :rule-classes nil))

(local (defun-nx fn2-ribbon-replaying-states-p (n pad sx sy)
 (and (fn2-ribbon-seal-hash-state-p n pad sx) (fn2-ribbon-check-hash-state-p pad sy)
      (equal (mv-nth 6 sx) (mv-nth 6 sy)) (fn2-ribbon-page-hash-agree (mv-nth 7 sx) (mv-nth 9 sx) (mv-nth 10 sx) (mv-nth 7 sy) (mv-nth 9 sy) (mv-nth 10 sy)))))

(local (defthm fn2-ribbon-replay-measure
 (implies (fn2-ribbon-replaying-states-p n pad sx sy) (and (equal (fn2-ribbon-hash-remaining (mv-nth 7 sx)) (fn2-ribbon-hash-remaining (mv-nth 7 sy))) (natp (fn2-ribbon-hash-remaining (mv-nth 7 sx))) (<= (fn2-ribbon-hash-remaining (mv-nth 7 sx)) 65557)))
 :hints (("Goal" :use ((:instance fn2-ribbon-sealing-remaining-bounds (st sx)) (:instance fn2-ribbon-agreement-implies-equal-remaining (fa (mv-nth 7 sx)) (a (mv-nth 9 sx)) (da (mv-nth 10 sx)) (fb (mv-nth 7 sy)) (b (mv-nth 9 sy)) (db (mv-nth 10 sy)))) :in-theory (union-theories '(fn2-ribbon-replaying-states-p) (theory 'minimal-theory)))) :rule-classes nil))

(local (defthm fn2-ribbon-replay-step-observations
 (let ((next-x (fn2-ribbon-next-sealing-state sx)) (next-y (fn2-ribbon-next-checking-state sy)))
 (implies (and (fn2-ribbon-replaying-states-p n pad sx sy) (< 0 (fn2-ribbon-hash-remaining (mv-nth 7 sx)))) (and (fn2-ribbon-page-hash-agree (mv-nth 7 next-x) (mv-nth 9 next-x) (mv-nth 10 next-x) (mv-nth 7 next-y) (mv-nth 9 next-y) (mv-nth 10 next-y)) (equal (mv-nth 6 next-x) (mv-nth 6 next-y))
    (equal (fn2-digest-list 136 (mv-nth 10 next-y)) (fn2-digest-list 136 (mv-nth 10 sy))))))
 :hints (("Goal" :use (fn2-ribbon-replay-measure
 (:instance fn2-ribbon-check-step-replays-sealing (fa (mv-nth 7 sx)) (ca (mv-nth 8 sx)) (a (mv-nth 9 sx)) (va (mv-nth 5 sx)) (da (mv-nth 10 sx)) (fb (mv-nth 7 sy)) (cb (mv-nth 8 sy)) (b (mv-nth 9 sy)) (vb (mv-nth 5 sy)) (db (mv-nth 10 sy)) (fn2-pool (mv-nth 6 sx)))
 (:instance fn2-ribbon-page-hash-step-progress (sealp t) (fn2-fields (mv-nth 5 sx)) (fn2-pool (mv-nth 6 sx)) (fn2-fc (mv-nth 7 sx)) (fn2-fc-context (mv-nth 8 sx)) (fn2-b3 (mv-nth 9 sx)) (fn2-digests (mv-nth 10 sx))) (:instance fn2-ribbon-page-hash-step-progress (sealp nil) (fn2-fields (mv-nth 5 sy)) (fn2-pool (mv-nth 6 sy)) (fn2-fc (mv-nth 7 sy)) (fn2-fc-context (mv-nth 8 sy)) (fn2-b3 (mv-nth 9 sy)) (fn2-digests (mv-nth 10 sy))))
 :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-replaying-states-p fn2-ribbon-seal-hash-state-p fn2-ribbon-check-hash-state-p fn2-ribbon-typed-pool-p fn2-ribbon-next-sealing-state fn2-ribbon-next-checking-state (:t fn2-format-run) mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory)))) :rule-classes nil))

(local (defthm fn2-ribbon-replaying-states-step
 (implies (and (fn2-ribbon-replaying-states-p n pad sx sy) (< 0 (fn2-ribbon-hash-remaining (mv-nth 7 sx))))
 (and (fn2-ribbon-replaying-states-p n pad (fn2-ribbon-next-sealing-state sx) (fn2-ribbon-next-checking-state sy)) (< (fn2-ribbon-hash-remaining (mv-nth 7 (fn2-ribbon-next-sealing-state sx))) (fn2-ribbon-hash-remaining (mv-nth 7 sx)))
      (equal (fn2-digest-list 136 (mv-nth 10 (fn2-ribbon-next-checking-state sy))) (fn2-digest-list 136 (mv-nth 10 sy)))))
 :hints (("Goal" :use (fn2-ribbon-replay-measure fn2-ribbon-replay-step-observations (:instance fn2-ribbon-next-sealing-state-hashes (st sx)) (:instance fn2-ribbon-next-checking-state-hashes (st sy)))
 :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-replaying-states-p) (theory 'minimal-theory)))) :rule-classes nil))

(local (defun-nx fn2-ribbon-dual-hash-induct (fx fy sx sy)
 (declare (xargs :measure (nfix fx)))
 (if (or (zp fx) (zp fy) (not (< 0 (fn2-ribbon-hash-remaining (mv-nth 7 sx))))) t
 (fn2-ribbon-dual-hash-induct (1- fx) (1- fy) (fn2-ribbon-next-sealing-state sx) (fn2-ribbon-next-checking-state sy)))))

(local (defthm fn2-ribbon-completed-hash-runs-agree
 (let ((x (fn2-ribbon-before-finalization fx sx)) (y (fn2-ribbon-before-check-finalization fy sy)))
 (implies (and (fn2-ribbon-replaying-states-p n pad sx sy) (natp fx) (natp fy) (< (fn2-ribbon-hash-remaining (mv-nth 7 sx)) fx) (< (fn2-ribbon-hash-remaining (mv-nth 7 sx)) fy))
 (and (fn2-ribbon-replaying-states-p n pad x y) (equal (fn2-digest-list 136 (mv-nth 10 y)) (fn2-digest-list 136 (mv-nth 10 sy))))))
 :hints (("Goal" :induct (fn2-ribbon-dual-hash-induct fx fy sx sy)
 :expand ((fn2-ribbon-before-finalization fx sx) (fn2-ribbon-before-check-finalization fy sy)) :do-not '(preprocess)
 :in-theory (union-theories '((:i fn2-ribbon-dual-hash-induct) (:compound-recognizer zp-compound-recognizer) zp-open natp posp mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory)))
 ("Subgoal *1/1" :use fn2-ribbon-replay-measure)
 ("Subgoal *1/2" :use (fn2-ribbon-replay-measure fn2-ribbon-replaying-states-step (:instance fn2-ribbon-replay-measure (sx (fn2-ribbon-next-sealing-state sx)) (sy (fn2-ribbon-next-checking-state sy)))))) :rule-classes nil))

(local (defthm fn2-ribbon-sealing-initializes-hasher
 (implies (and (equal (fn2-fc-phase 0 (mv-nth 7 st)) *fn2-fc-phase-idle*) (fn2-ribbon-arena-p 0 1 9 0 1 65536 65536 (mv-nth 6 st))) (and (equal (mv-nth 9 (fn2-ribbon-next-sealing-state st)) (mv-nth 1 (fn2-b3-init 0 0 1 (mv-nth 10 st) (mv-nth 9 st)))) (equal (mv-nth 10 (fn2-ribbon-next-sealing-state st)) (mv-nth 0 (fn2-b3-init 0 0 1 (mv-nth 10 st) (mv-nth 9 st))))))
 :hints (("Goal" :use ((:instance fn2-ribbon-page-begins-check (sealp t) (slot 0) (gen 1) (fn2-fields (mv-nth 5 st)) (fn2-pool (mv-nth 6 st)) (fn2-fc (mv-nth 7 st)) (fn2-fc-context (mv-nth 8 st)) (fn2-b3 (mv-nth 9 st)) (fn2-digests (mv-nth 10 st)))) :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-next-sealing-state (:e fn2-digest-slot) mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory)))) :rule-classes nil))

(local (defthm fn2-ribbon-sealer-prefix-initialized
 (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256)) (and (equal (mv-nth 9 (fn2-ribbon-next-sealing-state (fn2-ribbon-next-sealing-state (fn2-ribbon-sealing-state keys)))) (mv-nth 1 (fn2-b3-init 0 0 1 (mv-nth 10 (fn2-ribbon-sealing-state keys)) (mv-nth 9 (fn2-ribbon-sealing-state keys))))) (equal (mv-nth 10 (fn2-ribbon-next-sealing-state (fn2-ribbon-next-sealing-state (fn2-ribbon-sealing-state keys)))) (mv-nth 0 (fn2-b3-init 0 0 1 (mv-nth 10 (fn2-ribbon-sealing-state keys)) (mv-nth 9 (fn2-ribbon-sealing-state keys)))))))
 :hints (("Goal" :use (fn2-ribbon-image-hash-initialization fn2-ribbon-image-sealing-resources fn2-ribbon-image-reaches-header-decode (:instance fn2-ribbon-sealing-initializes-hasher (st (fn2-ribbon-sealing-state keys)))
 (:instance fn2-ribbon-sealing-decodes-page (n (len keys)) (old-fields (mv-nth 5 (fn2-ribbon-sealing-state keys))) (st (fn2-ribbon-next-sealing-state (fn2-ribbon-sealing-state keys)))))
 :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-format-snapshot-frames (:e <) (:e fn2-digest-slot)) (theory 'minimal-theory)))) :rule-classes nil))

(local (defthm fn2-ribbon-checker-prefix-initialized
 (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256)) (and (equal (mv-nth 9 (fn2-ribbon-next-checking-state (fn2-ribbon-next-checking-state (fn2-ribbon-final-drive keys)))) (mv-nth 1 (fn2-b3-init 0 0 1 (mv-nth 10 (fn2-ribbon-final-drive keys)) (mv-nth 9 (fn2-ribbon-final-drive keys))))) (equal (mv-nth 10 (fn2-ribbon-next-checking-state (fn2-ribbon-next-checking-state (fn2-ribbon-final-drive keys)))) (mv-nth 0 (fn2-b3-init 0 0 1 (mv-nth 10 (fn2-ribbon-final-drive keys)) (mv-nth 9 (fn2-ribbon-final-drive keys))))) (equal (mv-nth 6 (fn2-ribbon-next-checking-state (fn2-ribbon-next-checking-state (fn2-ribbon-final-drive keys)))) (mv-nth 6 (fn2-ribbon-final-drive keys)))
    (equal (fn2-fc-phase 0 (mv-nth 7 (fn2-ribbon-next-checking-state (fn2-ribbon-next-checking-state (fn2-ribbon-final-drive keys))))) *fn2-fc-phase-prefix*) (equal (fn2-fc-pos 0 (mv-nth 7 (fn2-ribbon-next-checking-state (fn2-ribbon-next-checking-state (fn2-ribbon-final-drive keys))))) 0)))
 :hints (("Goal" :use (fn2-ribbon-sealed-image-ready-for-checker (:instance fn2-ribbon-check-starts-decode (st (fn2-ribbon-final-drive keys)) (pad (+ *fn2-ribbon-base* (fn2-ribbon-slots (len keys)))))
 (:instance fn2-ribbon-checking-decodes-page (n (len keys)) (old-fields (mv-nth 5 (fn2-ribbon-final-drive keys))) (st (fn2-ribbon-next-checking-state (fn2-ribbon-final-drive keys)))))
 :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-checker-entry-p fn2-ribbon-checking-snapshot-frames fn2-ribbon-hash-input-p mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory)))) :rule-classes nil))

(local (defthm fn2-ribbon-check-and-seal-start-on-same-page
 (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256)) (equal (mv-nth 6 (fn2-ribbon-next-sealing-state (fn2-ribbon-next-sealing-state (fn2-ribbon-sealing-state keys)))) (mv-nth 6 (fn2-ribbon-next-checking-state (fn2-ribbon-next-checking-state (fn2-ribbon-final-drive keys))))))
 :hints (("Goal" :use (fn2-ribbon-image-reaches-hash-prefix fn2-ribbon-checker-prefix-initialized fn2-ribbon-checked-page-holds-key-equations) :do-not '(preprocess)
 :in-theory (union-theories '(fn2-ribbon-sealing-state fn2-ribbon-final-check fn2-ribbon-rba-check-preserves-page mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory)))) :rule-classes nil))

(local (defthm fn2-ribbon-image-starts-matching-hash-runs
 (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256)) (fn2-ribbon-replaying-states-p (len keys) (+ *fn2-ribbon-base* (fn2-ribbon-slots (len keys))) (fn2-ribbon-next-sealing-state (fn2-ribbon-next-sealing-state (fn2-ribbon-sealing-state keys))) (fn2-ribbon-next-checking-state (fn2-ribbon-next-checking-state (fn2-ribbon-final-drive keys)))))
 :hints (("Goal" :use (fn2-ribbon-check-and-seal-start-on-same-page fn2-ribbon-sealer-prefix-initialized fn2-ribbon-checker-prefix-initialized fn2-ribbon-image-reaches-hash-prefix fn2-ribbon-sealed-image-ready-for-checker fn2-ribbon-image-prefix-has-hashing-invariant
 (:instance fn2-ribbon-check-establishes-hash-invariant (st (fn2-ribbon-final-drive keys)) (n (len keys)))
 (:instance fn2-ribbon-initialized-hashers-agree (a (mv-nth 9 (fn2-ribbon-sealing-state keys))) (da (mv-nth 10 (fn2-ribbon-sealing-state keys))) (b (mv-nth 9 (fn2-ribbon-final-drive keys))) (db (mv-nth 10 (fn2-ribbon-final-drive keys)))))
 :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-replaying-states-p fn2-ribbon-page-hash-agree (:e fn2-digest-slot)) (theory 'minimal-theory)))) :rule-classes nil))

(local (defthm fn2-ribbon-image-finishes-matching-hash-runs
 (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256)) (and (fn2-ribbon-replaying-states-p (len keys) (+ *fn2-ribbon-base* (fn2-ribbon-slots (len keys))) (fn2-ribbon-sealer-end keys) (fn2-ribbon-checker-end keys)) (equal (fn2-digest-list 136 (mv-nth 10 (fn2-ribbon-checker-end keys))) (fn2-digest-list 136 (mv-nth 10 (fn2-ribbon-next-checking-state (fn2-ribbon-next-checking-state (fn2-ribbon-final-drive keys))))))))
 :hints (("Goal" :use (fn2-ribbon-image-starts-matching-hash-runs fn2-ribbon-image-reaches-heading
 (:instance fn2-ribbon-replay-measure (n (len keys)) (pad (+ *fn2-ribbon-base* (fn2-ribbon-slots (len keys)))) (sx (fn2-ribbon-next-sealing-state (fn2-ribbon-next-sealing-state (fn2-ribbon-sealing-state keys)))) (sy (fn2-ribbon-next-checking-state (fn2-ribbon-next-checking-state (fn2-ribbon-final-drive keys)))))
 (:instance fn2-ribbon-completed-hash-runs-agree (n (len keys)) (pad (+ *fn2-ribbon-base* (fn2-ribbon-slots (len keys)))) (sx (fn2-ribbon-next-sealing-state (fn2-ribbon-next-sealing-state (fn2-ribbon-sealing-state keys)))) (sy (fn2-ribbon-next-checking-state (fn2-ribbon-next-checking-state (fn2-ribbon-final-drive keys)))) (fx (1- (1- (1- (mv-nth 0 (fn2-ribbon-padded-state keys)))))) (fy 135270)))
 :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-sealer-end fn2-ribbon-checker-end natp mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory)))) :rule-classes nil))

(local (defthm fn2-ribbon-checked-parent-is-sealer-result
 (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256)) (equal (fn2-digest-list 136 (mv-nth 10 (fn2-ribbon-next-checking-state (fn2-ribbon-next-checking-state (fn2-ribbon-final-drive keys))))) (fn2-digest-list 125 (fn2-b3-finalize 125 0 (mv-nth 10 (fn2-ribbon-sealer-end keys)) (mv-nth 9 (fn2-ribbon-sealer-end keys))))))
 :hints (("Goal" :use (fn2-ribbon-checker-prefix-initialized fn2-ribbon-final-drive-completes-sealing (:instance fn2-ribbon-init-preserves-parent-digest (fn2-digests (mv-nth 10 (fn2-ribbon-final-drive keys))) (fn2-b3 (mv-nth 9 (fn2-ribbon-final-drive keys)))))
 :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-sealed-output fn2-ribbon-seal-saves-result-in-parent mv-nth-of-cons car-cons cdr-cons (:e mv-nth) (:e zp) (:e binary-+) (:e equal) (:e <) (:e not) (:e natp)) (theory 'minimal-theory)))) :rule-classes nil))

(local (defthm fn2-ribbon-image-recomputes-stored-digest
 (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256)) (fn2-ribbon-check-digest-matches-p (fn2-ribbon-checker-end keys)))
 :hints (("Goal" :use (fn2-ribbon-image-finishes-matching-hash-runs fn2-ribbon-checked-parent-is-sealer-result
 (:instance fn2-ribbon-finalized-results-agree (a (mv-nth 9 (fn2-ribbon-sealer-end keys))) (da (mv-nth 10 (fn2-ribbon-sealer-end keys))) (b (mv-nth 9 (fn2-ribbon-checker-end keys))) (db (mv-nth 10 (fn2-ribbon-checker-end keys))))
 (:instance fn2-ribbon-equal-rows-pass-digest-comparison (d (fn2-b3-finalize 125 0 (mv-nth 10 (fn2-ribbon-checker-end keys)) (mv-nth 9 (fn2-ribbon-checker-end keys))))))
 :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-replaying-states-p fn2-ribbon-check-digest-matches-p fn2-ribbon-page-hash-agree fn2-ribbon-finalize-preserves-parent-digest) (theory 'minimal-theory)))) :rule-classes nil))

(local
 (defthm fn2-ribbon-image-check-returns-ok
   (implies (and (fn2-ribbon-keysp keys) (consp keys) (<= (len keys) 256))
            (equal (cadr (fn2-ribbon-image keys nil queries nil)) :ok))
   :hints (("Goal" :use (fn2-ribbon-image-recomputes-stored-digest
                          fn2-ribbon-final-check-hashes-all-bytes
                          fn2-ribbon-image-reaches-final-drive)
            :expand ((len keys))
            :in-theory (union-theories '(posp (:t len) car-cons cdr-cons)
                                       (theory 'minimal-theory))))
   :rule-classes nil))

(defthm fn2-ribbon-no-false-negative-proved
  (fn2-ribbon-no-false-negative$owed keys queries)
  :hints (("Goal" :use (fn2-ribbon-image-seals
                        fn2-ribbon-image-check-returns-ok
                        fn2-ribbon-image-probe-answers-sound)
           :in-theory (union-theories '(fn2-ribbon-no-false-negative$owed)
                                      (theory 'minimal-theory))))
  :rule-classes nil)

(fn2-owed-discharge fn2-ribbon-no-false-negative fn2-ribbon-no-false-negative-proved)
