; A sealing writer changes to a published address. The address denotes
; exactly the rows previously held at that level, including all children.
(in-package "ACL2")
(include-book "range-builder-input")
(local (include-book "columns-observation-frames"))

(defun-nx fn2-range-child-lists-exclude-page-p (page children)
  (if (atom children) t
    (and (not (member-equal page (car children))) (fn2-range-child-lists-exclude-page-p page (cdr children)))))

(local
 (defthm fn2-range-new-page-outside-child-list
   (implies (not (member-equal (car node) addresses))
            (equal (fn2-range-child-entry-lists addresses (cons node records))
                   (fn2-range-child-entry-lists addresses records)))
   :hints (("Goal" :induct (len addresses)
            :in-theory (e/d (fn2-range-child-entry-lists member-equal assoc-equal) (nth))))))

(local
 (defthm fn2-range-new-page-outside-level
   (implies (and (natp i) (fn2-range-child-lists-exclude-page-p page children))
            (not (member-equal page (nth i children))))
   :hints (("Goal" :induct (nth i children) :in-theory (enable fn2-range-child-lists-exclude-page-p)))))

(local (defcolumns-observation-frame fn2-range-phase-keeps-page-unit fn2-run-writers unit phase))
(local (defcolumns-observation-frame fn2-range-phase-keeps-page-counter fn2-run-writers counter phase))
(local (defcolumns-observation-frame fn2-range-phase-keeps-page-slot fn2-run-writers slot phase))
(local (defcolumns-observation-frame fn2-range-phase-keeps-page-generation fn2-run-writers gen phase))

(local
 (defthm fn2-range-sealing-keeps-page-address
   (equal (fn2-range-writer-page-address i r (fn2-run-writers-set-phase w phase writers))
          (fn2-range-writer-page-address i r writers))
   :hints (("Goal" :in-theory (e/d (fn2-range-writer-page-address)
                         (fn2-run-writers-unit fn2-run-writers-counter fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-set-phase))))))

(local
 (defthm fn2-range-phase-of-writer-after-publication
   (implies (and (natp w) (natp r))
            (equal (fn2-run-writers-phase r (fn2-run-writers-set-phase w phase writers))
                   (if (equal r w) phase (fn2-run-writers-phase r writers))))
   :hints (("Goal" :in-theory (e/d (fn2-run-writers-phase fn2-run-writers-set-phase
                                    update-fn2-run-writers-phase$ai nth-update-nth)
                                  (nth update-nth))))))

(local
 (defthm fn2-range-level-of-writer-page
   (equal (car (fn2-range-writer-page-address i r writers)) i)
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn2-range-writer-page-address car-cons))))))

(local
 (defthm fn2-range-different-levels-have-different-addresses
   (implies (not (equal i l))
            (not (equal (fn2-range-writer-page-address i r writers) (fn2-range-writer-page-address l w writers))))
   :hints (("Goal" :in-theory (e/d (fn2-range-writer-page-address)
                                   (fn2-run-writers-unit fn2-run-writers-counter fn2-run-writers-slot fn2-run-writers-gen))))))

(local
 (defthmd fn2-range-publication-preserves-one-level
   (let* ((w (+ base l)) (page (fn2-range-writer-page-address l w writers))
          (after (fn2-run-writers-set-phase w *fn2-run-writer-phase-sealed* writers)))
     (implies (and (natp base) (natp l) (natp i) (equal (car node) page)
                   (fn2-range-child-lists-exclude-page-p page children)
                   (equal (nth 4 node) (fn2-range-writer-covered-rows l w leaves children records writers)))
              (equal (fn2-range-writer-covered-rows i (+ base i) leaves children (cons node records) after)
                     (fn2-range-writer-covered-rows i (+ base i) leaves children records writers))))
   :hints (("Goal" :cases ((equal i l))
            :expand ((:free (addr) (assoc-equal addr (cons node records))))
            :in-theory (e/d (fn2-range-writer-covered-rows)
                    (fn2-run-writers-phase fn2-run-writers-set-phase fn2-range-writer-page-address
                     fn2-range-child-lists-exclude-page-p fn2-range-child-entry-lists assoc-equal
                     append-lst nth member-equal))))))

(defthmd fn2-range-publication-preserves-builder-input
  (let* ((w (+ base l)) (page (fn2-range-writer-page-address l w writers))
         (after (fn2-run-writers-set-phase w *fn2-run-writer-phase-sealed* writers)))
    (implies (and (natp base) (natp l) (equal (car node) page)
                  (fn2-range-child-lists-exclude-page-p page children)
                  (equal (nth 4 node) (fn2-range-writer-covered-rows l w leaves children records writers)))
             (equal (fn2-range-builder-input height base leaves children (cons node records) after pending)
                    (fn2-range-builder-input height base leaves children records writers pending))))
  :hints (("Goal" :induct (fn2-range-builder-input height base leaves children records writers pending)
           :in-theory (e/d (fn2-range-builder-input)
                    (fn2-range-writer-covered-rows fn2-run-writers-set-phase fn2-range-writer-page-address
                     fn2-range-child-lists-exclude-page-p nth binary-append)))
          ("Subgoal *1/2" :use ((:instance fn2-range-publication-preserves-one-level (i (1- height)))))))
