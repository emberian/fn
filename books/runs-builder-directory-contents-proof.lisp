; Closing a populated writer leaves its full encoded body and writes
; the restart directory for those same rows immediately after it.
(in-package "ACL2")
(include-book "runs-builder-page-contents-proof")
(include-book "runs-build-close-proof")

(local (defthm fn2-run-directory-proper-list
  (implies (true-listp x) (equal (true-list-fix x) x))))

(local
 (defthm fn2-run-close-returns-directory-octets
   (let* ((cursor (fn2-run-writers-cursor w writers)) (nr (fn2-run-writers-restarts w writers))
          (slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers))
          (pk (fn2-run-writers-okind w writers)) (ps (fn2-run-writers-oslot w writers)) (pg (fn2-run-writers-ogen w writers))
          (bytes (fn2-run-directory-octets (fn2-run-saved-offsets nr (* w *fn2-run-restart-capacity*) restarts)))
          (close (fn2-run-close-step w 4096 writers restarts f pool)))
     (implies (and (fn2-run-closing-page-ready-p w writers restarts pool)
                   (equal (fn2-run-writers-pos w writers) 0) (posp nr))
              (and (equal (car close) :more)
                   (equal (fn2-run-read-bytes (* 4 nr) slot gen cursor pk ps pg (mv-nth 3 close)) bytes))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :use (fn2-run-close-writes-directory
                  (:instance fn2-run-load-bytes-roundtrip (bytes (fn2-run-directory-octets
                         (fn2-run-saved-offsets (fn2-run-writers-restarts w writers) (* w *fn2-run-restart-capacity*) restarts)))
                    (slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers))
                    (pk (fn2-run-writers-okind w writers)) (ps (fn2-run-writers-oslot w writers)) (pg (fn2-run-writers-ogen w writers))
                    (off (fn2-run-writers-cursor w writers)) (cap (+ (fn2-run-writers-cursor w writers) (* 4 (fn2-run-writers-restarts w writers))))))
            :in-theory (e/d (fn2-run-closing-page-ready-p fn2-run-directory-shape fn2-run-saved-offset-count)
                      (fn2-run-read-bytes fn2-run-load-bytes fn2-run-saved-offsets fn2-run-directory-octets fn2-run-close-step
                       fn2-run-writers-cursor fn2-run-writers-restarts fn2-run-writers-slot fn2-run-writers-gen
                       fn2-run-writers-okind fn2-run-writers-oslot fn2-run-writers-ogen fn2-run-writers-phase
                       fn2-run-writers-pos fn2-run-writers-fields fn2-run-writers-set-pos fn2-run-write-restarts
                       fn2-run-restarts-rows fn2-run-restartsp fn2-run-restarts-wfp fn2-pool-base fn2-layout-range-code
                       true-list-fix))))))

(defthmd fn2-run-adapter-closes-overview-contents
  (let* ((w (+ l (fn2-run-builds-wbase 0 builds))) (cursor (fn2-run-writers-cursor w writers))
         (nr (fn2-run-writers-restarts w writers)) (slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers))
         (idx (fn2-run-writers-entries w writers))
         (body (fn2-run-entries-octets *fn2-overview-entry* rows))
         (offsets (fn2-run-restart-offsets-spec *fn2-overview-entry* rows 0 *fn2-run-entries-base*))
         (step (fn2-run-run-onestep layout entries src sg off unit pages builds curs paths cache writers restarts f pool fc ctx b3 ds))
         (after (mv-nth 13 step)))
    (implies (and (fn2-run-build-closing-at-p l builds writers restarts f fc ctx)
                  (fn2-run-closing-page-ready-p w writers restarts pool)
                  (equal (fn2-run-writers-pos w writers) 0) (posp nr)
                  (equal (fn2-run-writers-okind w writers) 9) (equal (fn2-run-writers-oslot w writers) 0)
                  (equal (fn2-run-writers-ogen w writers) 1)
                  (fn2-run-open-overview-contents-p rows w idx nr cursor slot gen restarts pool))
             (and (not (car step)) (equal (mv-nth 1 step) :more)
                  (equal (fn2-run-read-bytes (len body) slot gen *fn2-run-entries-base* 9 0 1 after) body)
                  (equal (fn2-run-read-bytes (* 4 (len offsets)) slot gen cursor 9 0 1 after)
                         (fn2-run-directory-octets offsets)))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-run-adapter-performs-close-step
                 (:instance fn2-run-adapter-close-preserves-page-prefix (inoff off)
                            (at *fn2-run-entries-base*) (size (len (fn2-run-entries-octets *fn2-overview-entry* rows))))
                 (:instance fn2-run-close-returns-directory-octets (w (+ l (fn2-run-builds-wbase 0 builds)))))
           :in-theory (e/d (fn2-run-open-overview-contents-p)
                     (fn2-run-build-closing-at-p fn2-run-closing-page-ready-p fn2-run-adapter-performs-close-step
                      fn2-run-builds-wbase fn2-run-close-step fn2-run-run-onestep fn2-run-directory-octets
                      fn2-run-entries-octets fn2-run-restart-offsets-spec fn2-run-saved-offsets fn2-run-read-bytes
                      fn2-run-writers-cursor fn2-run-writers-restarts fn2-run-writers-pos fn2-run-writers-entries
                      fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-oslot fn2-run-writers-okind fn2-run-writers-ogen
                      fn2-run-writers-set-pos fn2-run-writers-set-phase len)))))
