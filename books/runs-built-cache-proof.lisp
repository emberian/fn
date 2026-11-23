; The page list installed by the range adapter supplies the cursor's child references.
(in-package "ACL2")
(include-book "runs-served")

(local
 (defthm fn2-run-cache-lookup-installed-page
  (let* ((row (mod u (fn2-run-cache-rows cache))) (rows (fn2-run-cache-rows cache))
         (after (mv-nth 1 (fn2-run-cache-install u a s g cache))))
    (implies (and (unsigned-byte-p 60 u) (unsigned-byte-p 60 a)
                  (unsigned-byte-p 32 s) (unsigned-byte-p 60 g)
                  (posp rows) (natp unit))
             (equal (fn2-run-cache-lookup unit counter after)
                    (if (equal (mod unit rows) row)
                        (if (and (equal unit u) (equal counter a))
                            (list :ok s g) (list :miss 0 0))
                      (fn2-run-cache-lookup unit counter cache)))))
  :hints (("Goal" :in-theory
           (e/d (fn2-run-cache-install fn2-run-cache-lookup fn2-run-cache-row
                 fn2-run-cache-state fn2-run-cache-unit fn2-run-cache-counter
                 fn2-run-cache-slot fn2-run-cache-gen fn2-run-cache-rows
                 fn2-run-cache-set-state fn2-run-cache-set-unit fn2-run-cache-set-counter
                 fn2-run-cache-set-slot fn2-run-cache-set-gen
                 update-fn2-run-cache-state$ai update-fn2-run-cache-unit$ai
                 update-fn2-run-cache-counter$ai update-fn2-run-cache-slot$ai
                 update-fn2-run-cache-gen$ai nth-update-nth)
                (nth update-nth mod unsigned-byte-p))))))

(defun fn2-run-page-addressp (page)
  (declare (xargs :guard t))
  (and (true-listp page) (equal (len page) 5)
       (unsigned-byte-p 60 (nth 1 page)) (unsigned-byte-p 60 (nth 2 page))
       (unsigned-byte-p 32 (nth 3 page)) (unsigned-byte-p 60 (nth 4 page))))

(defun fn2-run-cache-compatible-pages-p (page pages rows)
  (declare (xargs :guard (and (fn2-run-page-addressp page) (true-listp pages) (posp rows))))
  (if (atom pages) t
    (let ((p (car pages)))
      (and (fn2-run-page-addressp p)
           (or (not (equal (mod (nth 1 page) rows) (mod (nth 1 p) rows)))
               (equal (cdr page) (cdr p)))
           (fn2-run-cache-compatible-pages-p page (cdr pages) rows)))))

(defthm fn2-run-built-cache-supplies-page
  (let* ((unit (nth 1 page)) (counter (nth 2 page))
         (hit (list :ok (nth 3 page) (nth 4 page))))
    (implies (and (fn2-run-page-addressp page) (posp (fn2-run-cache-rows cache))
                  (fn2-run-cache-compatible-pages-p page pages (fn2-run-cache-rows cache))
                  (or (member-equal page pages)
                      (equal (fn2-run-cache-lookup unit counter cache) hit)))
             (equal (fn2-run-cache-lookup unit counter (fn2-run-run-cache-all pages cache)) hit)))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-run-run-cache-all pages cache)
           :in-theory (e/d (fn2-run-run-cache-all fn2-run-cache-compatible-pages-p
                            fn2-run-page-addressp)
                           (fn2-run-cache-lookup fn2-run-cache-install fn2-run-cache-rows
                            mod unsigned-byte-p)))))

(local
 (defthm fn2-run-cursor-save-child-page
  (let ((res (fn2-run-cursor-save c *fn2-run-cursor-phase-header* level slot gen
                                  0 0 0 0 unit counter curs)))
    (implies (and (natp c) (< c (fn2-run-cursors-rows curs))
                  (unsigned-byte-p 8 level) (unsigned-byte-p 32 slot)
                  (unsigned-byte-p 60 gen) (unsigned-byte-p 60 unit) (unsigned-byte-p 60 counter))
             (and (equal (car res) :ok)
                  (equal (fn2-run-cursors-phase c (mv-nth 1 res)) *fn2-run-cursor-phase-header*)
                  (equal (fn2-run-cursors-level c (mv-nth 1 res)) level)
                  (equal (fn2-run-cursors-slot c (mv-nth 1 res)) slot)
                  (equal (fn2-run-cursors-gen c (mv-nth 1 res)) gen)
                  (equal (fn2-run-cursors-unit c (mv-nth 1 res)) unit)
                  (equal (fn2-run-cursors-counter c (mv-nth 1 res)) counter))))
  :hints (("Goal" :in-theory
           (e/d (fn2-run-cursor-save nth-update-nth
                 fn2-run-cursors-phase fn2-run-cursors-level fn2-run-cursors-slot
                 fn2-run-cursors-gen fn2-run-cursors-unit fn2-run-cursors-counter
                 fn2-run-cursors-set-phase
                 fn2-run-cursors-set-level
                 fn2-run-cursors-set-slot
                 fn2-run-cursors-set-gen
                 fn2-run-cursors-set-lo
                 fn2-run-cursors-set-hi
                 fn2-run-cursors-set-idx
                 fn2-run-cursors-set-off
                 fn2-run-cursors-set-unit
                 fn2-run-cursors-set-counter
                 update-fn2-run-cursors-phase$ai
                 update-fn2-run-cursors-level$ai
                 update-fn2-run-cursors-slot$ai
                 update-fn2-run-cursors-gen$ai
                 update-fn2-run-cursors-lo$ai
                 update-fn2-run-cursors-hi$ai
                 update-fn2-run-cursors-idx$ai
                 update-fn2-run-cursors-off$ai
                 update-fn2-run-cursors-unit$ai
                 update-fn2-run-cursors-counter$ai)
                (fn2-run-cursors-rows nth update-nth unsigned-byte-p))))))

(local
 (defthm fn2-run-child-level-fits
  (implies (and (posp level) (< level *fn2-run-max-levels*))
           (and (natp level) (< 0 level) (unsigned-byte-p 8 (1- level))))))

(defthm fn2-run-cursor-descends-to-built-page
  (let* ((unit (nth 1 page)) (counter (nth 2 page))
         (decoded (fn2-run-nth sid level idx slot gen rb ok os og f pool))
         (fields (mv-nth 2 decoded)) (cb (+ rb *fn2-run-reader-entry* nkeys))
         (step (fn2-run-step-child c sid t level nkeys slot gen lo hi idx off parent alloc rb
                                   ok os og curs paths (fn2-run-run-cache-all pages cache) f pool))
         (after (mv-nth 1 step)))
    (implies (and (fn2-run-page-addressp page) (member-equal page pages)
                  (posp (fn2-run-cache-rows cache))
                  (fn2-run-cache-compatible-pages-p page pages (fn2-run-cache-rows cache))
                  (natp c) (< c (fn2-run-cursors-rows curs))
                  (posp level) (< level *fn2-run-max-levels*)
                  (< (fn2-run-path-row c level) (fn2-run-paths-rows paths))
                  (unsigned-byte-p 32 idx) (eq (car decoded) :ok)
                  (<= (+ cb *fn2-format-ref-num-fields*) (fn2-fields-rows fields))
                  (equal (fn2-fields-value (+ cb *fn2-format-ref-field-physical-unit*) fields) unit)
                  (equal (fn2-fields-value (+ cb *fn2-format-ref-field-allocation*) fields) counter))
             (and (equal (car step) :more)
                  (equal (fn2-run-cursors-phase c after) *fn2-run-cursor-phase-header*)
                  (equal (fn2-run-cursors-level c after) (1- level))
                  (equal (fn2-run-cursors-slot c after) (nth 3 page))
                  (equal (fn2-run-cursors-gen c after) (nth 4 page))
                  (equal (fn2-run-cursors-unit c after) unit)
                  (equal (fn2-run-cursors-counter c after) counter))))
  :rule-classes nil
  :hints (("Goal" :use (fn2-run-built-cache-supplies-page
                         (:instance fn2-run-cursor-save-child-page (level (1- level))
                                    (slot (nth 3 page)) (gen (nth 4 page))
                                    (unit (nth 1 page)) (counter (nth 2 page))))
           :in-theory (union-theories (theory 'minimal-theory)
                         '(fn2-run-step-child fn2-run-path-take fn2-run-page-addressp
                           fn2-run-child-level-fits eq not mv-nth (:e mv-nth)
                           car-cons cdr-cons (:e equal) (:e not) (:e nth) (:e binary-+) (:e zp) (:e unary--) (:e <) (:e cons))))))
