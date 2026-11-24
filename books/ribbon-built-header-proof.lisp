(in-package "ACL2")
(include-book "ribbon-adapter-check-proof")
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

(defun-nx fn2-ribbon-padding-end (fuel cursor pos slot gen writers pool)
   (declare (xargs :measure (nfix fuel)))
   (if (zp fuel) (list 0 writers pool)
     (let* ((start (+ cursor pos)) (k (min 4096 (- 65536 start))))
       (if (<= 65536 start)
           (list (1- fuel) (fn2-run-writers-set-phase 0 *fn2-run-writer-phase-heading* writers) pool)
         (fn2-ribbon-padding-end (1- fuel) cursor (+ pos k) slot gen
           (fn2-run-writers-set-pos 0 (+ pos k) writers)
           (mv-nth 1 (fn2-run-zero k slot gen start 9 0 1 pool)))))))

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
          (fn2-ribbon-arena-p slot gen 9 0 1 65536 65536 fn2-pool))))

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
   :rule-classes nil)

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

(defun-nx fn2-ribbon-padded-state (keys)
   (let ((emit (fn2-ribbon-emitted-step keys)))
     (fn2-ribbon-padding-end 99998 (+ *fn2-ribbon-base* (fn2-ribbon-slots (len keys))) 0 0 1 (mv-nth 2 emit) (mv-nth 3 emit))))

(local
 (defthm fn2-ribbon-adapter-fuel-for-page
   (implies (and (posp n) (<= n 256))
            (<= (- 65536 (+ (+ *fn2-ribbon-base* (fn2-ribbon-slots n)) 0)) (* 4096 (+ -1 99998 (- 90000)))))
   :hints (("Goal" :in-theory (disable fn2-ribbon-slots)))))

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
   :rule-classes nil)

(defun-nx fn2-ribbon-headed-step (keys)
   (let ((a (fn2-ribbon-added-state keys)) (p (fn2-ribbon-padded-state keys)))
     (fn2-ribbon-head 0 (fn2-ribbon-builds-set-phase 0 *fn2-ribbon-phase-heading* (mv-nth 1 (fn2-ribbon-emitted-step keys))) (mv-nth 1 p) (mv-nth 5 a) (mv-nth 2 p) (mv-nth 8 a))))

; Write both headers and enter the page hash with the decoded length and padding bounds.
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
               (theory 'minimal-theory)))) :rule-classes nil)

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

(defun-nx fn2-ribbon-sealing-state (keys)
   (let ((h (fn2-ribbon-headed-step keys)) (a (fn2-ribbon-added-state keys)))
     (fn2-ribbon-call-with-state list (:more) a
       (1 (mv-nth 1 h)) (2 (mv-nth 2 (fn2-ribbon-solved-step keys))) (3 (mv-nth 2 h))
       (5 (mv-nth 3 h)) (6 (mv-nth 4 h)) (8 (mv-nth 5 h)))))

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
   :rule-classes nil)

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

(defun fn2-ribbon-sealing-resources-p (n slot gen fn2-ribbon-builds fn2-run-writers fn2-fields fn2-fc fn2-fc-context fn2-b3 fn2-digests)
   (declare (xargs :stobjs (fn2-ribbon-builds fn2-run-writers fn2-fields fn2-fc fn2-fc-context fn2-b3 fn2-digests) :verify-guards nil))
   (and (fn2-ribbon-build-identity-p n fn2-ribbon-builds)
        (equal (fn2-ribbon-builds-phase 0 fn2-ribbon-builds) *fn2-ribbon-phase-sealing*)
        (fn2-ribbon-writer-identity-p slot gen fn2-run-writers)
        (equal (fn2-run-writers-phase 0 fn2-run-writers) *fn2-run-writer-phase-sealing*)
        (fn2-ribbon-seal-context-p fn2-fc-context)
        (< 0 (fn2-fc-context-rows fn2-fc-context)) (< 0 (fn2-fc-rows fn2-fc))
        (< 301 (fn2-fields-rows fn2-fields)) (fn2-b3-ready 0 fn2-b3 fn2-digests)
        (fn2-digest-rowp 136 fn2-digests)))

(defthm fn2-ribbon-image-sealing-resources
   (let ((st (fn2-ribbon-sealing-state keys)))
     (implies (and (fn2-ribbon-keysp keys) (posp (len keys)) (<= (len keys) 256))
       (and (fn2-ribbon-sealing-resources-p (len keys) 0 1 (mv-nth 1 st) (mv-nth 3 st) (mv-nth 5 st) (mv-nth 7 st) (mv-nth 8 st) (mv-nth 9 st) (mv-nth 10 st)) (equal (fn2-fc-phase 0 (mv-nth 7 st)) *fn2-fc-phase-idle*))))
   :hints (("Goal" :use (fn2-ribbon-image-writes-page-headers fn2-ribbon-fresh-added-environment
                         (:instance fn2-ribbon-initial-checker-and-restart-tables (n (len keys))))
            :do-not '(preprocess) :in-theory (union-theories '(fn2-ribbon-sealing-resources-p fn2-ribbon-sealing-state
                  fn2-ribbon-context-rows-after-preparation mv-nth-of-cons (:e zp) (:e binary-+) (:e mv-nth)
                  car-cons cdr-cons (:e <)) (theory 'minimal-theory))))
   :rule-classes nil)

(defthm fn2-ribbon-lower-digest-row-available
   (implies (and (fn2-digest-rowp 136 fn2-digests) (natp r) (<= r 136)) (fn2-digest-rowp r fn2-digests))
   :hints (("Goal" :in-theory (e/d (fn2-digest-rowp) (fn2-digests-rows fn2-digests-wfp))))
   :rule-classes nil)

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

(defun-nx fn2-ribbon-next-sealing-state (st)
   (let ((run (fn2-format-run :page t 0 0 1 0 65536 0 9 0 1 4096 (mv-nth 7 st) (mv-nth 8 st)
                             (mv-nth 9 st) (mv-nth 5 st) (mv-nth 6 st) (mv-nth 10 st))))
     (fn2-ribbon-call-with-state list ((mv-nth 0 run)) st
       (5 (mv-nth 3 run)) (6 (mv-nth 4 run)) (7 (mv-nth 1 run)) (9 (mv-nth 2 run)) (10 (mv-nth 5 run)))))

(defthm fn2-ribbon-drive-after-format-step
   (let ((next (fn2-ribbon-next-sealing-state st)))
     (implies (and (posp fuel) (fn2-ribbon-sealing-resources-p n 0 1 (mv-nth 1 st) (mv-nth 3 st) (mv-nth 5 st) (mv-nth 7 st) (mv-nth 8 st) (mv-nth 9 st) (mv-nth 10 st)) (equal (mv-nth 0 next) :more))
       (equal (fn2-ribbon-call-with-state fn2-rba-drive (fuel) st)
              (fn2-ribbon-call-with-state fn2-rba-drive ((1- fuel)) next))))
   :hints (("Goal" :use ((:instance fn2-ribbon-drive-continues-format-run (slot 0) (gen 1)
                            (fn2-ribbon-builds (mv-nth 1 st)) (fn2-ribbon-band (mv-nth 2 st)) (fn2-run-writers (mv-nth 3 st)) (fn2-run-restarts (mv-nth 4 st)) (fn2-fields (mv-nth 5 st)) (fn2-pool (mv-nth 6 st)) (fn2-fc (mv-nth 7 st)) (fn2-fc-context (mv-nth 8 st)) (fn2-b3 (mv-nth 9 st)) (fn2-digests (mv-nth 10 st))))
            :in-theory (union-theories '(fn2-ribbon-next-sealing-state mv-nth-of-cons (:e zp) (:e binary-+) (:e mv-nth) car-cons cdr-cons (:e <) (:e equal)) (theory 'minimal-theory))))
   :rule-classes nil)

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
   :rule-classes nil)

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
   :rule-classes nil)

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
   :rule-classes nil)

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
   :rule-classes nil)

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
   :rule-classes nil)




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
