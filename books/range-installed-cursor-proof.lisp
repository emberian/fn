; The first run-source advance opens the cursor on the root recorded by
; the adapter, with the reader and query owned by the range.
(in-package "ACL2")
(include-book "range-installed-pages-proof")

(defmacro fn2-range-open-source-cursor (s sid rs inst curs)
  `(let ((r (fn2-range-sources-src ,s ,rs)))
     (fn2-run-cursor-start (fn2-range-sources-cursor ,s ,rs) ,sid
       (fn2-run-installed-top r ,inst) (fn2-run-installed-slot r ,inst) (fn2-run-installed-gen r ,inst)
       (fn2-run-installed-unit r ,inst) (fn2-run-installed-counter r ,inst) (fn2-range-sources-rb ,s ,rs)
       (fn2-run-installed-okind r ,inst) (fn2-run-installed-oslot r ,inst) (fn2-run-installed-ogen r ,inst) ,curs)))

(defthmd fn2-range-fresh-source-scans-opened-cursor
  (let* ((c (fn2-range-sources-cursor s rs)) (open (fn2-range-open-source-cursor s sid rs inst curs))
         (scan (fn2-run-scan-step c budget qbase qk qs qg (mv-nth 1 open) paths cache f pool))
         (step (fn2-range-advance-run s sid budget qbase qk qs qg rs inst curs paths cache f pool)))
    (implies (and (natp s) (< s (fn2-range-sources-rows rs))
                  (< (fn2-range-sources-src s rs) (fn2-run-installed-rows inst))
                  (equal (fn2-range-sources-state s rs) *fn2-range-state-seek*)
                  (equal (car open) :ok))
             (and (equal (mv-nth 2 step) (mv-nth 1 scan))
                  (equal (mv-nth 3 step) (mv-nth 2 scan))
                  (equal (mv-nth 4 step) (mv-nth 3 scan))
                  (equal (car step) (case (car scan) ((:entry :end) :ok) (:lost :more) (otherwise (car scan)))))))
  :hints (("Goal" :in-theory (e/d (fn2-range-advance-run)
             (fn2-run-cursor-start fn2-run-scan-step fn2-range-sources-src fn2-range-sources-state fn2-range-sources-cursor
              fn2-range-sources-rb fn2-run-installed-rows fn2-range-sources-rows fn2-run-installed-top
              fn2-run-installed-slot fn2-run-installed-gen fn2-run-installed-unit fn2-run-installed-counter
              fn2-run-installed-okind fn2-run-installed-oslot fn2-run-installed-ogen fn2-range-sources-set-state)))))

(local
 (defthm fn2-range-cursor-starts-at-source
   (let* ((start (fn2-run-cursor-start c sid top slot gen unit counter rb 9 0 1 curs))
          (after (mv-nth 1 start)))
     (implies (and (natp c) (< c (fn2-run-cursors-rows curs)) (unsigned-byte-p 60 sid)
                   (unsigned-byte-p 8 top) (< top *fn2-run-max-levels*) (unsigned-byte-p 32 rb)
                   (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                   (unsigned-byte-p 60 unit) (unsigned-byte-p 60 counter))
              (and (equal (car start) :ok)
                   (equal (fn2-run-cursors-phase c after) *fn2-run-cursor-phase-header*)
                   (equal (fn2-run-cursors-level c after) top) (equal (fn2-run-cursors-top c after) top)
                   (equal (fn2-run-cursors-slot c after) slot) (equal (fn2-run-cursors-gen c after) gen)
                   (equal (fn2-run-cursors-unit c after) unit) (equal (fn2-run-cursors-counter c after) counter)
                   (equal (fn2-run-cursors-rb c after) rb))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-run-cursor-start nth-update-nth
                 fn2-run-cursors-phase fn2-run-cursors-level fn2-run-cursors-top fn2-run-cursors-slot
                 fn2-run-cursors-gen fn2-run-cursors-unit fn2-run-cursors-counter fn2-run-cursors-rb
                 fn2-run-cursors-set-phase fn2-run-cursors-set-schema fn2-run-cursors-set-level
                 fn2-run-cursors-set-top fn2-run-cursors-set-left fn2-run-cursors-set-slot
                 fn2-run-cursors-set-gen fn2-run-cursors-set-lo fn2-run-cursors-set-hi
                 fn2-run-cursors-set-idx fn2-run-cursors-set-off fn2-run-cursors-set-unit
                 fn2-run-cursors-set-counter fn2-run-cursors-set-rb fn2-run-cursors-set-okind
                 fn2-run-cursors-set-oslot fn2-run-cursors-set-ogen
                 update-fn2-run-cursors-phase$ai update-fn2-run-cursors-schema$ai
                 update-fn2-run-cursors-level$ai update-fn2-run-cursors-top$ai
                 update-fn2-run-cursors-left$ai update-fn2-run-cursors-slot$ai
                 update-fn2-run-cursors-gen$ai update-fn2-run-cursors-lo$ai update-fn2-run-cursors-hi$ai
                 update-fn2-run-cursors-idx$ai update-fn2-run-cursors-off$ai update-fn2-run-cursors-unit$ai
                 update-fn2-run-cursors-counter$ai update-fn2-run-cursors-rb$ai
                 update-fn2-run-cursors-okind$ai update-fn2-run-cursors-oslot$ai
                 update-fn2-run-cursors-ogen$ai)
                 (fn2-run-cursors-rows nth update-nth unsigned-byte-p))))))

(local
 (defthm fn2-range-root-source-selectors
   (implies (and (equal (fn2-run-installed-root k inst) root)
                 (equal (fn2-run-installed-source k inst)
                        (list *fn2-run-installed-state-live* sid run count 9 0 1)))
            (and (equal (fn2-run-installed-top k inst) (nth 0 root))
                 (equal (fn2-run-installed-unit k inst) (nth 1 root))
                 (equal (fn2-run-installed-counter k inst) (nth 2 root))
                 (equal (fn2-run-installed-slot k inst) (nth 3 root))
                 (equal (fn2-run-installed-gen k inst) (nth 4 root))
                 (equal (fn2-run-installed-okind k inst) 9)
                 (equal (fn2-run-installed-oslot k inst) 0)
                 (equal (fn2-run-installed-ogen k inst) 1)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn2-run-installed-root fn2-run-installed-source)
                      (fn2-run-installed-top fn2-run-installed-unit fn2-run-installed-counter
                       fn2-run-installed-gen fn2-run-installed-slot fn2-run-installed-state
                       fn2-run-installed-schema fn2-run-installed-run fn2-run-installed-entries
                       fn2-run-installed-okind fn2-run-installed-oslot fn2-run-installed-ogen))))))

(defthmd fn2-range-cursor-opens-installed-page
  (let* ((root (car pages)) (c (fn2-range-sources-cursor s rs)) (rb (fn2-range-sources-rb s rs))
         (write (fn2-rga-install-pages sid k count pages inst cache))
         (open (fn2-range-open-source-cursor s sid rs (mv-nth 1 write) curs)) (after (mv-nth 1 open)))
    (implies (and (natp k) (< k (fn2-run-installed-rows inst))
                  (equal (fn2-run-installed-state k inst) *fn2-run-installed-state-free*)
                  (unsigned-byte-p 60 sid) (unsigned-byte-p 60 (1+ k)) (unsigned-byte-p 60 count)
                  (fn2-run-page-addressp root) (unsigned-byte-p 8 (car root)) (< (car root) *fn2-run-max-levels*)
                  (equal (fn2-range-sources-src s rs) k)
                  (natp c) (< c (fn2-run-cursors-rows curs)) (unsigned-byte-p 32 rb))
             (and (equal (car open) :ok)
                  (equal (fn2-run-cursors-phase c after) *fn2-run-cursor-phase-header*)
                  (equal (fn2-run-cursors-level c after) (car root)) (equal (fn2-run-cursors-top c after) (car root))
                  (equal (fn2-run-cursors-unit c after) (nth 1 root)) (equal (fn2-run-cursors-counter c after) (nth 2 root))
                  (equal (fn2-run-cursors-slot c after) (nth 3 root)) (equal (fn2-run-cursors-gen c after) (nth 4 root))
                  (equal (fn2-run-cursors-rb c after) rb))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-range-installed-pages-supply-root (r k))
                 (:instance fn2-range-root-source-selectors (root (car pages)) (run (1+ k))
                            (inst (mv-nth 1 (fn2-rga-install-pages sid k count pages inst cache))))
                 (:instance fn2-range-cursor-starts-at-source (c (fn2-range-sources-cursor s rs)) (rb (fn2-range-sources-rb s rs))
                            (top (car (car pages))) (unit (nth 1 (car pages))) (counter (nth 2 (car pages)))
                            (slot (nth 3 (car pages))) (gen (nth 4 (car pages)))))
           :in-theory (union-theories (theory 'minimal-theory)
                          '(fn2-run-page-addressp nth (:e zp) (:e nth) (:e unary--) (:e binary-+))))))
