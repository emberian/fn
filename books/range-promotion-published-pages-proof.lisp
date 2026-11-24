; Both the parent append and the retry on a full parent retain all older
; published leaves and index pages, including the selected child.
(in-package "ACL2")
(include-book "range-published-page-write-proof")
(include-book "range-builder-promotion-step-proof")

(local
 (defthm fn2-range-stored-parent-hash-size
   (equal (len (fn2-page-parent-octets i n words)) (nfix n))
   :hints (("Goal" :induct (fn2-page-parent-octets i n words)
            :in-theory (e/d (fn2-page-parent-octets) (fn2-fc-word-byte floor mod nth))))))

(local
 (defthmd fn2-range-parent-hash-offset-fits
   (implies (fn2-run-overview-promotion-ready-p level builds writers)
            (and (natp (* 32 level)) (<= (+ (* 32 level) 32) 65536)))
   :hints (("Goal" :in-theory (e/d (fn2-run-overview-promotion-ready-p)
                    (fn2-run-builds-height fn2-run-writers-rows fn2-run-builds-wbase fn2-run-builds-fields
                     fn2-run-builds-schema fn2-run-writers-phase fn2-run-builds-hbase fn2-run-builds-okind
                     fn2-run-builds-oslot fn2-run-builds-ogen))))))

(local
 (defthmd fn2-range-fitting-parent-extent
   (implies (and (fn2-run-parent-index-position-p w parent-rows writers) (fn2-run-index-fits-writer w bytes writers))
            (and (natp (fn2-run-writers-cursor w writers))
                 (<= (+ (fn2-run-writers-cursor w writers) (len bytes)) 65536)))
   :hints (("Goal" :in-theory (e/d (fn2-run-parent-index-position-p fn2-run-pack-bound)
                        (fn2-run-writers-cursor fn2-run-writers-entries fn2-run-writers-restarts fn2-run-writers-limit
                         fn2-run-entries-layoutp fn2-run-entries-octets fn2-run-restart-offsets-spec mod len))))))

(local
 (defthmd fn2-range-promotion-stored-pool
   (implies (fn2-run-parent-promotion-effects)
            (equal (mv-nth 5 promote) (if fits (mv-nth 1 (fn2-run-load-bytes bytes dst dg off 9 0 1 rp)) rp)))
   :hints (("Goal" :cases (fits) :in-theory (union-theories (theory 'minimal-theory) '(fn2-run-index-promotion-result-p))))))

(local
 (defthm fn2-range-parent-promotion-writes
   (fn2-run-promoting-index-row
    (let ((hash-pool (mv-nth 1 (fn2-run-load-bytes (fn2-page-parent-octets 0 32 (fn2-digest-list hrow ds))
                                                  hslot hgen (* 32 level) 9 0 1 pool))))
      (and (fn2-run-parent-promotion-effects)
           (equal (mv-nth 5 promote) (if fits (mv-nth 1 (fn2-run-load-bytes bytes dst dg off 9 0 1 hash-pool)) hash-pool)))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-run-builder-appends-or-retries-promoted-index
                 (:instance fn2-run-promoted-index-row-is-admitted (w level) (ib *fn2-run-build-index*) (hrow (+ 136 level))
                      (hslot (fn2-run-builds-hslot 0 builds)) (hgen (fn2-run-builds-hgen 0 builds)))
                 (:instance fn2-range-promotion-stored-pool (w (1+ level)) (ordinal (1+ (fn2-run-writers-ordinal level writers)))
                       (idx (fn2-run-writers-entries (1+ level) writers)) (nr (fn2-run-writers-restarts (1+ level) writers))
                       (dst (fn2-run-writers-slot (1+ level) writers)) (dg (fn2-run-writers-gen (1+ level) writers))
                       (off (fn2-run-writers-cursor (1+ level) writers))
                       (bytes (fn2-run-child-index-bytes rows level (+ 136 level) writers ds))
                       (fits (fn2-run-index-fits-writer (1+ level) (fn2-run-child-index-bytes rows level (+ 136 level) writers ds) writers))
                       (promote (fn2-run-build-promote 0 level builds writers restarts f pool ds))
                       (rp (mv-nth 2 (fn2-run-promotion-input level level *fn2-run-build-index* (fn2-run-writers-cursor level writers)
                                   (+ 136 level) (fn2-run-builds-hslot 0 builds) (fn2-run-builds-hgen 0 builds) writers f pool ds)))
                       (commit (let* ((ref (fn2-run-promotion-input level level *fn2-run-build-index*
                                        (fn2-run-writers-cursor level writers) (+ 136 level) (fn2-run-builds-hslot 0 builds)
                                        (fn2-run-builds-hgen 0 builds) writers f pool ds))
                                      (parent (fn2-run-add (1+ level) 3 *fn2-run-build-index* writers restarts
                                                           (mv-nth 1 ref) (mv-nth 2 ref))))
                                 (fn2-run-promote-commit level (car parent) (mv-nth 1 parent))))))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm fn2-range-promotion-retains-records
   (fn2-run-promoting-index-row
    (implies (and (fn2-range-published-run-pages-p records pages pool)
                  (fn2-range-fixed-page-slot-p hslot pool) (fn2-range-published-slots-apart-p pages hslot pool)
                  (implies fits (and (fn2-range-fixed-page-slot-p dst pool) (fn2-range-published-slots-apart-p pages dst pool))))
             (and (fn2-run-parent-promotion-effects) (fn2-range-published-run-pages-p records pages (mv-nth 5 promote)))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-range-parent-promotion-writes fn2-range-parent-hash-offset-fits
                 (:instance fn2-range-fitting-parent-extent (w (1+ level)) (bytes (fn2-run-child-index-bytes rows level (+ 136 level) writers ds)))
                 (:instance fn2-range-two-writes-retain-published-pages
                      (first-bytes (fn2-page-parent-octets 0 32 (fn2-digest-list (+ 136 level) ds)))
                      (first-slot (fn2-run-builds-hslot 0 builds)) (first-gen (fn2-run-builds-hgen 0 builds)) (first-off (* 32 level))
                      (dst (fn2-run-writers-slot (1+ level) writers)) (dg (fn2-run-writers-gen (1+ level) writers))
                      (off (fn2-run-writers-cursor (1+ level) writers))
                      (bytes (fn2-run-child-index-bytes rows level (+ 136 level) writers ds))
                      (secondp (fn2-run-index-fits-writer (1+ level) (fn2-run-child-index-bytes rows level (+ 136 level) writers ds) writers))))
           :in-theory (union-theories (theory 'minimal-theory) '(fn2-range-stored-parent-hash-size (:e nfix)))))))

(defthm fn2-range-promoting-parent-keeps-published-pages
  (fn2-run-promoting-index-row
   (let* ((height (fn2-run-builds-height 0 builds)) (crow (fn2-run-builds-crow 0 builds))
          (step (fn2-run-run-onestep layout entries src sg at unit pages builds curs paths cache writers restarts f pool fc ctx b3 ds)))
     (implies (and (posp height) (<= height *fn2-run-max-levels*)
                   (fn2-run-higher-writers-available-p (1- height) w writers)
                   (fn2-run-writerp level writers restarts f) (< crow (fn2-fc-rows fc)) (< crow (fn2-fc-context-rows ctx))
                   (fn2-range-published-run-pages-p records pages pool)
                   (fn2-range-fixed-page-slot-p hslot pool) (fn2-range-published-slots-apart-p pages hslot pool)
                   (implies fits (and (fn2-range-fixed-page-slot-p dst pool) (fn2-range-published-slots-apart-p pages dst pool))))
              (and (fn2-run-parent-promotion-effects)
                   (equal step (list nil :more entries at unit pages (mv-nth 1 promote) curs paths cache (mv-nth 2 promote)
                                     (mv-nth 3 promote) (mv-nth 4 promote) (mv-nth 5 promote) fc ctx b3 (mv-nth 6 promote)))
                   (fn2-range-published-run-pages-p records pages (mv-nth 5 promote))))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess) :use (fn2-run-driver-promotes-sealed-child fn2-range-promotion-retains-records)
           :in-theory (theory 'minimal-theory))))
