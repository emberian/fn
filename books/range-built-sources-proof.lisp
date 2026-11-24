; A successful build installs nonempty inputs in their original slots.
; Empty runs occupy input positions but leave their descriptor untouched.
(in-package "ACL2")
(include-book "range-installed-pages-proof")

(local
 (defthm fn2-range-successful-install-source
   (let ((write (fn2-rga-install-pages sid k count pages inst cache)))
     (implies (and (natp r) (< r (fn2-run-installed-rows inst))
                   (equal (car write) :ok))
              (and (equal (fn2-run-installed-source r (mv-nth 1 write))
                          (if (equal r k)
                              (list *fn2-run-installed-state-live* sid (1+ k) count 9 0 1)
                            (fn2-run-installed-source r inst)))
                   (equal (fn2-run-installed-rows (mv-nth 1 write)) (fn2-run-installed-rows inst)))))
   :hints (("Goal" :in-theory (e/d (fn2-rga-install-pages fn2-run-install fn2-run-installed-source
                 fn2-run-installed-state fn2-run-installed-schema fn2-run-installed-run fn2-run-installed-entries
                 fn2-run-installed-okind fn2-run-installed-oslot fn2-run-installed-ogen fn2-run-installed-rows
                 fn2-run-installed-set-state fn2-run-installed-set-schema fn2-run-installed-set-run
                 fn2-run-installed-set-top fn2-run-installed-set-slot fn2-run-installed-set-gen
                 fn2-run-installed-set-unit fn2-run-installed-set-counter fn2-run-installed-set-entries
                 fn2-run-installed-set-okind fn2-run-installed-set-oslot fn2-run-installed-set-ogen
                 fn2-run-installed-set-filter fn2-run-installed-set-funit fn2-run-installed-set-fcounter
                 update-fn2-run-installed-state$ai update-fn2-run-installed-schema$ai update-fn2-run-installed-run$ai
                 update-fn2-run-installed-top$ai update-fn2-run-installed-slot$ai update-fn2-run-installed-gen$ai
                 update-fn2-run-installed-unit$ai update-fn2-run-installed-counter$ai update-fn2-run-installed-entries$ai
                 update-fn2-run-installed-okind$ai update-fn2-run-installed-oslot$ai update-fn2-run-installed-ogen$ai
                 update-fn2-run-installed-filter$ai update-fn2-run-installed-funit$ai update-fn2-run-installed-fcounter$ai
                 nth-update-nth)
                (fn2-run-run-cache-all nth update-nth unsigned-byte-p))))))

(defthmd fn2-range-build-records-input-source
  (let* ((build (fn2-rga-call fn2-rga-build sid layout entries k))
         (inst (mv-nth 5 build)))
    (implies (and (natp r) (< r (fn2-run-installed-rows fn2-run-installed))
                  (equal (car build) :ok))
             (and (equal (fn2-run-installed-rows inst) (fn2-run-installed-rows fn2-run-installed))
                  (equal (fn2-run-installed-source r inst)
                         (if (and (consp entries) (equal r k))
                             (list *fn2-run-installed-state-live* sid (1+ k) (len entries) 9 0 1)
                           (fn2-run-installed-source r fn2-run-installed))))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                       '(fn2-rga-build fn2-range-successful-install-source atom eq eql not
                         mv-nth car-cons cdr-cons (:e mv-nth) (:e equal) (:e zp)
                         (:e unary--) (:e binary-+) (:e consp))))))

(defthmd fn2-range-builds-record-input-sources
  (let* ((build (fn2-rga-call fn2-rga-builds sid layout runs k))
         (inst (mv-nth 6 build))
         (rows (nth (- r k) runs)))
    (implies (and (natp k) (natp r) (< r (fn2-run-installed-rows fn2-run-installed))
                  (equal (car build) :ok))
             (and (equal (mv-nth 1 build) (+ k (len runs)))
                  (equal (fn2-run-installed-rows inst) (fn2-run-installed-rows fn2-run-installed))
                  (equal (fn2-run-installed-source r inst)
                         (if (and (<= k r) (consp rows))
                             (list *fn2-run-installed-state-live* sid (1+ r) (len rows) 9 0 1)
                           (fn2-run-installed-source r fn2-run-installed))))))
  :hints (("Goal" :induct (fn2-rga-call fn2-rga-builds sid layout runs k)
           :do-not '(preprocess)
           :expand ((:free (i) (nth i runs)))
           :in-theory (e/d (fn2-range-build-records-input-source)
                    (fn2-rga-build fn2-run-installed-source fn2-run-installed-rows)))))

(defthmd fn2-range-setup-empty-run-descriptor
  (let ((inst (mv-nth 5 (fn2-rga-call fn2-rga-setup))))
    (and (equal (fn2-run-installed-rows inst) 16)
         (implies (and (natp r) (< r 16))
                  (equal (fn2-run-installed-source r inst)
                         (list *fn2-run-installed-state-free* 0 0 0 0 0 0)))))
  :hints (("Goal" :cases ((equal r 0) (equal r 1) (equal r 2) (equal r 3)
                          (equal r 4) (equal r 5) (equal r 6) (equal r 7)
                          (equal r 8) (equal r 9) (equal r 10) (equal r 11)
                          (equal r 12) (equal r 13) (equal r 14) (equal r 15))
           :in-theory (e/d (fn2-rga-setup fn2-run-installed-source fn2-run-installed-state
                       fn2-run-installed-schema fn2-run-installed-run fn2-run-installed-entries
                       fn2-run-installed-okind fn2-run-installed-oslot fn2-run-installed-ogen)
                    (fn2-pool-init fn2-run-installed-init)))))

(defmacro fn2-range-build-from-setup (sid layout runs)
  `(b* (((mv & ,@*fn2-rga-stobjs*) (fn2-rga-call fn2-rga-setup)))
     (fn2-rga-call fn2-rga-builds ,sid ,layout ,runs 0)))

(defthmd fn2-range-built-source-at-input-index
  (let* ((build (fn2-range-build-from-setup sid layout runs))
         (inst (mv-nth 6 build)) (rows (nth r runs)))
    (implies (and (natp r) (< r 16) (equal (car build) :ok))
             (and (equal (mv-nth 1 build) (len runs))
                  (equal (fn2-run-installed-rows inst) 16)
                  (equal (fn2-run-installed-source r inst)
                         (if (consp rows)
                             (list *fn2-run-installed-state-live* sid (1+ r) (len rows) 9 0 1)
                           (list *fn2-run-installed-state-free* 0 0 0 0 0 0))))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                              '(fn2-range-builds-record-input-sources fn2-range-setup-empty-run-descriptor
                                unicity-of-0 commutativity-of-+ fix (:type-prescription len) (:type-prescription natp) (:e natp) (:e unary--) (:e binary-+)))
           :use (fn2-range-setup-empty-run-descriptor (:instance (:definition natp) (x r))))))
