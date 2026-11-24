; Appending a row changes the writer's byte offsets and counters. Its
; phase and page address at every level still select the same stored rows.
(in-package "ACL2")
(include-book "range-builder-input")
(include-book "runs-served")

(local
 (defmacro fn2-range-writer-read-theory (&rest operations)
   `(e/d (,@operations fn2-range-writer-covered-rows fn2-range-writer-page-address
          fn2-run-writers-unit fn2-run-writers-counter fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-phase
          fn2-run-writers-set-cursor fn2-run-writers-set-entries fn2-run-writers-set-prev fn2-run-writers-set-restarts
          fn2-run-writers-set-pos fn2-run-writers-set-phase nth-update-nth
          update-fn2-run-writers-cursor$ai update-fn2-run-writers-entries$ai update-fn2-run-writers-prev$ai
          update-fn2-run-writers-restarts$ai update-fn2-run-writers-phase$ai update-fn2-run-writers-pos$ai)
         (fn2-range-child-entry-lists append-lst nth update-nth assoc-equal unsigned-byte-p mod
          fn2-run-writers-entries fn2-run-writers-restarts fn2-run-writers-cursor
          fn2-run-restarts-rows fn2-run-restarts-set-offset))))

(local
 (defthm fn2-range-noting-restart-keeps-covered-rows
   (let ((after (mv-nth 1 (fn2-run-note-restart w writers restarts))))
     (equal (fn2-range-writer-covered-rows i r leaves children records after)
            (fn2-range-writer-covered-rows i r leaves children records writers)))
   :hints (("Goal" :in-theory (fn2-range-writer-read-theory fn2-run-note-restart)))))

(local
 (defthm fn2-range-successful-append-keeps-writer-selection
   (let ((commit (fn2-run-add-commit w code end writers)))
     (implies (equal (car commit) :ok)
              (equal (fn2-range-writer-covered-rows i r leaves children records (mv-nth 1 commit))
                     (fn2-range-writer-covered-rows i r leaves children records writers))))
   :hints (("Goal" :cases ((equal code :ok)) :in-theory (fn2-range-writer-read-theory fn2-run-add-commit)))))

(defthmd fn2-range-appending-row-keeps-writer-selection
  (let ((add (fn2-run-add w sid base writers restarts f pool)))
    (implies (equal (car add) :ok)
             (equal (fn2-range-writer-covered-rows i r leaves children records (mv-nth 1 add))
                    (fn2-range-writer-covered-rows i r leaves children records writers))))
  :hints (("Goal" :in-theory (e/d (fn2-run-add fn2-run-add-write)
                  (fn2-range-writer-covered-rows fn2-run-add-ready fn2-run-add-check fn2-run-layout-encode
                   fn2-run-layout-decode fn2-run-add-commit fn2-run-note-restart fn2-fields-rows
                   fn2-run-writers-fields fn2-run-writers-level fn2-run-writers-slot fn2-run-writers-gen
                   fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen fn2-run-writers-cursor nfix)))))

(defthmd fn2-range-appending-row-keeps-builder-selection
  (let ((add (fn2-run-add w sid base writers restarts f pool)))
    (implies (equal (car add) :ok)
             (equal (fn2-range-builder-input height wbase leaves children records (mv-nth 1 add) pending)
                    (fn2-range-builder-input height wbase leaves children records writers pending))))
  :hints (("Goal" :induct (fn2-range-builder-input height wbase leaves children records writers pending)
           :in-theory (e/d (fn2-range-builder-input fn2-range-appending-row-keeps-writer-selection)
                          (fn2-run-add fn2-range-writer-covered-rows binary-append)))))

(defthmd fn2-range-starting-leaf-close-keeps-writer-selection
  (let ((next (fn2-run-writers-set-phase w *fn2-run-writer-phase-closing* (fn2-run-writers-set-pos w 0 writers))))
    (implies (and (natp w) (natp r) (equal (fn2-run-writers-phase w writers) *fn2-run-writer-phase-open*))
             (equal (fn2-range-writer-covered-rows i r leaves children records next)
                    (fn2-range-writer-covered-rows i r leaves children records writers))))
  :hints (("Goal" :cases ((equal w r)) :in-theory (fn2-range-writer-read-theory))))

(defthmd fn2-range-starting-leaf-close-keeps-builder-input
  (let ((next (fn2-run-writers-set-phase w *fn2-run-writer-phase-closing* (fn2-run-writers-set-pos w 0 writers))))
    (implies (and (natp w) (natp wbase) (equal (fn2-run-writers-phase w writers) *fn2-run-writer-phase-open*))
             (equal (fn2-range-builder-input height wbase leaves children records next pending)
                    (fn2-range-builder-input height wbase leaves children records writers pending))))
  :hints (("Goal" :induct (fn2-range-builder-input height wbase leaves children records writers pending)
           :in-theory (e/d (fn2-range-builder-input fn2-range-starting-leaf-close-keeps-writer-selection)
                          (fn2-run-writers-phase fn2-run-writers-set-phase fn2-run-writers-set-pos
                           fn2-range-writer-covered-rows binary-append)))))
