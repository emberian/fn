; Installing a completed run exposes the last sealed page as the root and
; makes each child address available through the cursor's page cache.
(in-package "ACL2")
(include-book "range-served")
(include-book "runs-built-cache-proof")

(defun-nx fn2-run-installed-root (r inst)
  (list (fn2-run-installed-top r inst) (fn2-run-installed-unit r inst)
        (fn2-run-installed-counter r inst) (fn2-run-installed-slot r inst)
        (fn2-run-installed-gen r inst)))

(defun-nx fn2-run-installed-source (r inst)
  (list (fn2-run-installed-state r inst) (fn2-run-installed-schema r inst)
        (fn2-run-installed-run r inst) (fn2-run-installed-entries r inst)
        (fn2-run-installed-okind r inst) (fn2-run-installed-oslot r inst)
        (fn2-run-installed-ogen r inst)))

(local
 (defthm fn2-run-install-records-source-and-root
   (let* ((write (fn2-run-install k sid run top slot gen unit counter count 9 0 1 inst))
          (after (mv-nth 1 write)))
     (implies (and (natp k) (< k (fn2-run-installed-rows inst))
                   (equal (fn2-run-installed-state k inst) *fn2-run-installed-state-free*)
                   (unsigned-byte-p 60 sid) (unsigned-byte-p 60 run) (unsigned-byte-p 60 count)
                   (unsigned-byte-p 8 top) (< top *fn2-run-max-levels*)
                   (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                   (unsigned-byte-p 60 unit) (unsigned-byte-p 60 counter)
                   (natp r) (< r (fn2-run-installed-rows inst)))
              (and (equal (car write) :ok)
                   (equal (fn2-run-installed-root r after)
                          (if (equal r k) (list top unit counter slot gen) (fn2-run-installed-root r inst)))
                   (equal (fn2-run-installed-source r after)
                          (if (equal r k) (list *fn2-run-installed-state-live* sid run count 9 0 1)
                            (fn2-run-installed-source r inst))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-run-install fn2-run-installed-root fn2-run-installed-source
                                    nth-update-nth
                  fn2-run-installed-state fn2-run-installed-schema fn2-run-installed-run
                  fn2-run-installed-top fn2-run-installed-slot fn2-run-installed-gen
                  fn2-run-installed-unit fn2-run-installed-counter fn2-run-installed-entries
                  fn2-run-installed-okind fn2-run-installed-oslot fn2-run-installed-ogen
                  fn2-run-installed-set-state fn2-run-installed-set-schema fn2-run-installed-set-run
                  fn2-run-installed-set-top fn2-run-installed-set-slot fn2-run-installed-set-gen
                  fn2-run-installed-set-unit fn2-run-installed-set-counter
                  fn2-run-installed-set-entries fn2-run-installed-set-okind fn2-run-installed-set-oslot
                  fn2-run-installed-set-ogen fn2-run-installed-set-filter fn2-run-installed-set-funit
                  fn2-run-installed-set-fcounter
                  update-fn2-run-installed-state$ai update-fn2-run-installed-schema$ai
                  update-fn2-run-installed-run$ai update-fn2-run-installed-top$ai
                  update-fn2-run-installed-slot$ai update-fn2-run-installed-gen$ai
                  update-fn2-run-installed-unit$ai update-fn2-run-installed-counter$ai
                  update-fn2-run-installed-entries$ai update-fn2-run-installed-okind$ai
                  update-fn2-run-installed-oslot$ai update-fn2-run-installed-ogen$ai
                  update-fn2-run-installed-filter$ai update-fn2-run-installed-funit$ai
                  update-fn2-run-installed-fcounter$ai)
                 (fn2-run-installed-rows nth update-nth unsigned-byte-p))))))

(local
 (defthm fn2-run-address-fields-reconstruct-page
   (implies (fn2-run-page-addressp page)
            (equal (list (nth 0 page) (nth 1 page) (nth 2 page) (nth 3 page) (nth 4 page)) page))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn2-run-page-addressp)
            :expand ((len page) (len (cdr page)) (len (cddr page)) (len (cdddr page))
                     (len (cddddr page)) (len (cdr (cddddr page))))))))

(defthmd fn2-range-installed-pages-supply-root
  (let* ((write (fn2-rga-install-pages sid k count pages inst cache))
         (after (mv-nth 1 write)) (root (car pages)))
    (implies (and (natp k) (< k (fn2-run-installed-rows inst))
                  (equal (fn2-run-installed-state k inst) *fn2-run-installed-state-free*)
                  (unsigned-byte-p 60 sid) (unsigned-byte-p 60 (1+ k)) (unsigned-byte-p 60 count)
                  (fn2-run-page-addressp root) (unsigned-byte-p 8 (car root)) (< (car root) *fn2-run-max-levels*)
                  (natp r) (< r (fn2-run-installed-rows inst)))
             (and (equal (car write) :ok)
                  (equal (fn2-run-installed-root r after) (if (equal r k) root (fn2-run-installed-root r inst)))
                  (equal (fn2-run-installed-source r after)
                         (if (equal r k) (list *fn2-run-installed-state-live* sid (1+ k) count 9 0 1)
                           (fn2-run-installed-source r inst))))))
  :hints (("Goal" :use ((:instance fn2-run-install-records-source-and-root
                         (run (1+ k)) (top (car (car pages))) (slot (nth 3 (car pages))) (gen (nth 4 (car pages)))
                         (unit (nth 1 (car pages))) (counter (nth 2 (car pages))))
                        (:instance fn2-run-address-fields-reconstruct-page (page (car pages))))
           :in-theory (e/d (fn2-rga-install-pages fn2-run-page-addressp)
                     (fn2-run-installed-root fn2-run-installed-source fn2-run-install fn2-run-run-cache-all
                      fn2-run-installed-state fn2-run-installed-rows unsigned-byte-p)))))

(defthmd fn2-range-installed-pages-supply-child
  (let* ((unit (nth 1 page)) (counter (nth 2 page)) (hit (list :ok (nth 3 page) (nth 4 page)))
         (write (fn2-rga-install-pages sid k count pages inst cache)))
    (implies (and (fn2-run-page-addressp page) (posp (fn2-run-cache-rows cache))
                  (fn2-run-cache-compatible-pages-p page pages (fn2-run-cache-rows cache))
                  (or (member-equal page pages) (equal (fn2-run-cache-lookup unit counter cache) hit)))
             (equal (fn2-run-cache-lookup unit counter (mv-nth 2 write)) hit)))
  :hints (("Goal" :use fn2-run-built-cache-supplies-page
           :in-theory (e/d (fn2-rga-install-pages)
                     (fn2-run-install fn2-run-run-cache-all fn2-run-cache-lookup
                      fn2-run-cache-compatible-pages-p fn2-run-page-addressp fn2-run-cache-rows nth)))))
