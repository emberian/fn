; A sealed child's first stored key and digest form an admissible parent
; row. The reference fields name the digest workspace used by promotion.
(in-package "ACL2")
(include-book "runs-index-values-proof")
(include-book "runs-promoted-first-key-proof")
(include-book "runs-layout-id-proof")

(defthmd fn2-run-promoted-key-width
   (implies (and (consp rows) (fn2-run-entries-layoutp (fn2-run-overview-layout-at level) rows))
            (and (unsigned-byte-p 60 (nth 0 (car rows))) (unsigned-byte-p 60 (nth 1 (car rows)))))
   :hints (("Goal" :cases ((zp level)) :do-not-induct t
            :use ((:instance fn2-run-layout-id-width (layout (fn2-run-overview-layout-at level)) (values (car rows)) (i 0) (id 'group))
                  (:instance fn2-run-layout-id-width (layout (fn2-run-overview-layout-at level)) (values (car rows)) (i 1) (id 'group-number)))
            :expand ((:free (layout) (fn2-run-entries-layoutp layout rows)))
            :in-theory (disable fn2-run-entries-layoutp fn2-run-values-layoutp unsigned-byte-p nth))))

(local
 (defthm fn2-run-child-ref-sets-digest-source
   (let* ((ref (fn2-run-child-ref w level (+ ib 2) (+ ib 2 *fn2-format-ref-num-fields*) hrow hslot hgen 9 0 1 writers f pool ds))
          (rf (mv-nth 1 ref)) (i (+ ib 2 *fn2-format-ref-field-expected-hash*)))
     (implies (fn2-run-child-reference-room-p w level ib hrow hslot hgen writers f pool ds)
              (and (equal (fn2-fields-value i rf) 1) (equal (fn2-fields-ref-len i rf) 32)
                   (equal (fn2-fields-ref-slot i rf) hslot) (equal (fn2-fields-ref-gen i rf) hgen)
                   (equal (fn2-fields-ref-off i rf) (* 32 level)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-run-child-digest-occupies-slot (slot hslot) (gen hgen) (off (* 32 level))
                              (row hrow) (pk 9) (ps 0) (pg 1)))
            :in-theory (e/d (fn2-run-child-ref fn2-run-child-reference-room-p
                              fn2-fields-value fn2-fields-ref-slot fn2-fields-ref-gen fn2-fields-ref-off fn2-fields-ref-len
                              fn2-fields-set-value update-fn2-fields-value$ai fn2-fields-set-ref-slot update-fn2-fields-ref-slot$ai
                              fn2-fields-set-ref-gen update-fn2-fields-ref-gen$ai fn2-fields-set-ref-off update-fn2-fields-ref-off$ai
                              fn2-fields-set-ref-len update-fn2-fields-ref-len$ai nth-update-nth)
                         (fn2-run-writersp fn2-run-writers-wfp fn2-run-writers-rows fn2-run-writers-entries
                          fn2-run-writers-unit fn2-run-writers-epoch fn2-run-writers-counter fn2-run-writers-page-kind fn2-digest-store
                          fn2-pool-base fn2-layout-range-code fn2-fields-rows fn2-digest-rowp fn2-digest-list
                          fn2-page-parent-octets fn2-run-load-bytes fn2-run-read-bytes nth update-nth))))))

(defmacro fn2-run-encoded-child-input-p (w level ib hrow hslot hgen rows bvals cvals writers f pool ds)
  `(and (consp ,rows)
        (fn2-run-encoded-overview-page-p ,rows ,level ,bvals ,cvals (fn2-run-writers-slot ,w ,writers)
                       (fn2-run-writers-gen ,w ,writers) 9 0 1 ,pool)
        (equal (fn2-run-writers-cursor ,w ,writers) (fn2-run-overview-directory-offset ,level ,rows))
        (fn2-fieldsp ,f) (fn2-fields-wfp ,f)
        (fn2-run-child-reference-room-p ,w ,level ,ib ,hrow ,hslot ,hgen ,writers ,f ,pool ,ds)
        (< (fn2-run-writers-page-kind ,w ,writers) (len (caddr *fn2-format-page-kind*)))))

(defmacro fn2-run-child-first-read (w level ib writers f pool)
  `(fn2-run-layout-decode 3 ,level ,ib (fn2-run-writers-slot ,w ,writers) (fn2-run-writers-gen ,w ,writers)
                          *fn2-run-entries-base* (fn2-run-writers-cursor ,w ,writers) 9 0 1 ,f ,pool))

(local
 (defthm fn2-run-child-read-keeps-reference-space
   (implies (and (fn2-run-child-reference-room-p w level ib hrow hslot hgen writers f pool ds)
                 (fn2-fieldsp f) (fn2-fields-wfp f))
            (fn2-run-child-reference-room-p w level ib hrow hslot hgen writers
                                (mv-nth 2 (fn2-run-child-first-read w level ib writers f pool)) pool ds))
   :hints (("Goal" :in-theory (e/d (fn2-run-child-reference-room-p)
                       (fn2-fields-rows fn2-run-layout-decode fn2-run-writers-rows fn2-run-writersp fn2-run-writers-wfp
                        fn2-fieldsp fn2-fields-wfp fn2-layout-range-code fn2-pool-base fn2-digest-rowp unsigned-byte-p))))))

(local
 (defthm fn2-run-encoded-child-has-admissible-reference
   (implies (fn2-run-encoded-child-input-p w level ib hrow hslot hgen rows bvals cvals writers f pool ds)
            (fn2-run-values-layoutp *fn2-overview-index*
                     (fn2-run-overview-child-row (list (nth 0 (car rows)) (nth 1 (car rows))) w hrow writers ds)))
   :rule-classes nil
   :hints (("Goal" :use (fn2-run-promoted-key-width
                         (:instance fn2-run-child-row-has-canonical-encoding (key (list (nth 0 (car rows)) (nth 1 (car rows))))))
            :in-theory (union-theories (theory 'minimal-theory)
                         '(fn2-run-child-reference-room-p fn2-run-encoded-overview-page-p car-cons cdr-cons (:e len) (:e cdr) (:e car)))))))

(local
 (defthm fn2-run-reference-load-in-typed-pool
   (implies (fn2-run-encoded-overview-page-p rows level bvals cvals slot gen pk ps pg pool)
            (let ((after (mv-nth 1 (fn2-run-load-bytes bytes dst dg off 9 0 1 pool))))
              (and (fn2-poolp after) (fn2-pool-wfp after))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-run-load-preserves-pool (slot dst) (gen dg) (pk 9) (ps 0) (pg 1)))
            :in-theory (union-theories (theory 'minimal-theory) '(fn2-run-encoded-overview-page-p))))))

(defthmd fn2-run-promoted-index-row-is-admitted
  (let* ((ref (fn2-run-promotion-input level w ib (fn2-run-writers-cursor w writers) hrow hslot hgen writers f pool ds))
         (rf (mv-nth 1 ref)) (after (mv-nth 2 ref)) (i (+ ib 2 *fn2-format-ref-field-expected-hash*))
         (row (fn2-run-unload-values *fn2-overview-index* ib rf after)))
    (implies (fn2-run-encoded-child-input-p w level ib hrow hslot hgen rows bvals cvals writers f pool ds)
             (and (equal (car ref) :ok) (fn2-run-values-layoutp *fn2-overview-index* row)
                  (fn2-poolp after) (fn2-pool-wfp after)
                  (equal after (mv-nth 1 (fn2-run-load-bytes (fn2-page-parent-octets 0 32 (fn2-digest-list hrow ds))
                                                     hslot hgen (* 32 level) 9 0 1 pool)))
                  (equal (fn2-fields-value i rf) 1) (equal (fn2-fields-ref-len i rf) 32)
                  (equal (fn2-fields-ref-slot i rf) hslot) (equal (fn2-fields-ref-gen i rf) hgen)
                  (equal (fn2-fields-ref-off i rf) (* 32 level)))))
  :hints (("Goal" :do-not '(preprocess) :do-not-induct t
           :use (fn2-run-encoded-child-supplies-promotion-input fn2-run-encoded-child-has-admissible-reference
                 fn2-run-child-read-keeps-reference-space
                 (:instance fn2-run-child-ref-sets-digest-source (f (mv-nth 2 (fn2-run-child-first-read w level ib writers f pool))))
                 (:instance fn2-run-child-reference-records-sealed-writer (f (mv-nth 2 (fn2-run-child-first-read w level ib writers f pool))))
                 (:instance fn2-run-reference-load-in-typed-pool
                   (slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers)) (pk 9) (ps 0) (pg 1)
                   (bytes (fn2-page-parent-octets 0 32 (fn2-digest-list hrow ds))) (dst hslot) (dg hgen) (off (* 32 level))))
           :in-theory (theory 'minimal-theory))))
