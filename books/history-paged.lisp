; P3 history authority. The resident image is immutable between root adoption;
; append writes only the arbitrary-event tail. Message-ID buckets name ordinal
; rows, never retain their events. Root generation is allocated at adoption.
(in-package "ACL2")
(include-book "history-columns-foundation")
(include-book "history-pages-resident")
(include-book "history-records")
(local (include-book "arithmetic/top" :dir :system))

(defstobj fn-hist$p
  (fn-hist$p-root :type fn-hrecs$c)
  (fn-hist$p-mids :type (hash-table eql))
  (fn-hist$p-salt :type (unsigned-byte 32) :initially 0)
  (fn-hist$p-generation :type (integer 0 *) :initially 0)
  (fn-hist$p-bound :type (integer 0 1) :initially 0)
  :inline t)

(defun fn-hist$p-root-ready (fn-hrecs$c)
  (declare (xargs :stobjs fn-hrecs$c :guard (fn-hrc-wfp fn-hrecs$c)
                  :guard-hints (("Goal" :in-theory (enable fn-hrc-wfp)))))
  (or (equal (fn-hrc-img fn-hrecs$c) 0)
      (and (fn-hp-resident-row-boundsp (max 0 (- (fn-hrc-nimg fn-hrecs$c) 1))
                   (fn-hrc-lens fn-hrecs$c) (fn-hrc-starts fn-hrecs$c)
                   (fn-hrc-npages fn-hrecs$c))
           (stobj-let ((pgs-mem (fn-hrc-pgs fn-hrecs$c)))
                      (v) (fn-hp-x-ready-range 0 (fn-hrc-npages fn-hrecs$c) pgs-mem)
                      (equal v :ok)))))

(defun fn-hist$p-wfp (fn-hist$p)
  (declare (xargs :stobjs fn-hist$p))
  (stobj-let ((fn-hrecs$c (fn-hist$p-root fn-hist$p)))
             (ok) (and (fn-hrc-wfp fn-hrecs$c) (fn-hist$p-root-ready fn-hrecs$c)) ok))

(local
 (defthm fn-hist$p-row-bounds-monotone
   (implies (and (natp seq) (natp last) (<= seq last)
                 (fn-hp-resident-row-boundsp last lens starts np))
            (fn-hp-resident-row-boundsp seq lens starts np))
   :hints (("Goal" :in-theory (enable fn-hp-resident-row-boundsp)))))

(defthm fn-hist$p-root-at-ready
  (implies (and (fn-hrecs$cp c) (fn-hrc-wfp c) (fn-hist$p-root-ready c)
                (natp seq))
           (equal (mv-nth 0 (fn-hrc-at seq c)) :ok))
  :hints (("Goal" :do-not-induct t
           :cases ((< seq (fn-hrc-nimg c)))
           :use ((:instance fn-hist$p-row-bounds-monotone
                            (last (max 0 (- (fn-hrc-nimg c) 1)))
                            (lens (fn-hrc-lens c)) (starts (fn-hrc-starts c))
                            (np (fn-hrc-npages c)))
                 (:instance fn-hp-resident-at-ready
                            (n (fn-hrc-nimg c)) (np (fn-hrc-npages c))
                            (lens (fn-hrc-lens c)) (starts (fn-hrc-starts c))
                            (salt (fn-hrc-salt c)) (pgs-mem (fn-hrc-pgs c))))
           :in-theory (e/d (fn-hist$p-root-ready fn-hrc-at fn-hrc-wfp
                            fn-hrecs$cp fn-hrc-pgs)
                          (fn-hp-x-at fn-hp-x-ready-range fn-hp-resident-at-ready
                           fn-hp-x-cell fn-hp-x-pool-ready fn-hp-resident-row-boundsp
                           mv-nth nfix fix)))))

(defun fn-hist$p-count (fn-hist$p)
  (declare (xargs :stobjs fn-hist$p :guard (fn-hist$p-wfp fn-hist$p)))
  (stobj-let ((fn-hrecs$c (fn-hist$p-root fn-hist$p)))
             (n) (fn-hrc-count fn-hrecs$c) n))

(defthm fn-hist$p-count-natp
  (implies (fn-hist$p-wfp p) (natp (fn-hist$p-count p)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (fn-hist$p-count fn-hist$p-wfp fn-hrc-count fn-hrc-wfp)
                                   (fn-hrecs$cp)))))

(defun fn-hist$p-at (seq fn-hist$p)
  (declare (xargs :stobjs fn-hist$p
                  :guard (and (fn-hist$p-wfp fn-hist$p) (natp seq)
                              (< seq (fn-hist$p-count fn-hist$p)))
                  :guard-hints (("Goal" :in-theory (e/d (fn-hist$p-wfp)
                     (fn-hrc-wfp fn-hrc-at fn-hrc-count fn-hrecs$cp))))))
  (stobj-let ((fn-hrecs$c (fn-hist$p-root fn-hist$p)))
             (v answer) (fn-hrc-at seq fn-hrecs$c)
             (if (eq v :ok) (if (and (consp answer) (consp (cdr answer))) (cadr answer) nil)
               (prog2$ (er hard 'fn-hist$p-at
                           "An installed resident history root lost page readiness: ~x0" v)
                       nil))))

(defun fn-hist$p-append (ev fn-hist$p)
  (declare (xargs :stobjs fn-hist$p :guard (fn-hist$p-wfp fn-hist$p)
                  :verify-guards nil))
  (let ((n (fn-hist$p-count fn-hist$p)) (m (fn-hist-key-msgid ev)))
    (stobj-let ((fn-hrecs$c (fn-hist$p-root fn-hist$p)))
               (fn-hrecs$c) (fn-hrc-append ev fn-hrecs$c)
               (if (stringp m)
                   (let ((key (fn-hist-hash m (fn-hist$p-salt fn-hist$p))))
                     (fn-hist$p-mids-put key (cons n (fn-hist$p-mids-get key fn-hist$p))
                                        fn-hist$p))
                 fn-hist$p))))

(defun fn-hist$p-clear (salt fn-hist$p)
  (declare (xargs :stobjs fn-hist$p :guard (unsigned-byte-p 32 salt)))
  (stobj-let ((fn-hrecs$c (fn-hist$p-root fn-hist$p)))
             (fn-hrecs$c) (fn-hrc-reset salt fn-hrecs$c)
             (let* ((fn-hist$p (fn-hist$p-mids-clear fn-hist$p))
                    (fn-hist$p (update-fn-hist$p-salt salt fn-hist$p))
                    (fn-hist$p (update-fn-hist$p-bound 0 fn-hist$p)))
               (update-fn-hist$p-generation (+ 1 (fn-hist$p-generation fn-hist$p))
                                           fn-hist$p))))

(defun fn-hist$p-collect (msgid seqs acc fn-hist$p)
  (declare (xargs :stobjs fn-hist$p
                  :guard (and (stringp msgid) (fn-hist$p-wfp fn-hist$p))
                  :verify-guards nil))
  (if (consp seqs)
      (let ((i (car seqs)))
        (if (and (natp i) (< i (fn-hist$p-count fn-hist$p)))
            (let ((record (fn-cei-event-article (fn-hist$p-at i fn-hist$p))))
              (fn-hist$p-collect msgid (cdr seqs)
                (if (and (fn-held-p record) (equal msgid (fn-record-msgid record)))
                    (cons record acc) acc) fn-hist$p))
          (fn-hist$p-collect msgid (cdr seqs) acc fn-hist$p)))
    acc))

(defun fn-hist$p-msgid-records (msgid fn-hist$p)
  (declare (xargs :stobjs fn-hist$p
                  :guard (and (stringp msgid) (fn-hist$p-wfp fn-hist$p))
                  :verify-guards nil))
  (fn-hist$p-collect msgid
    (fn-hist$p-mids-get (fn-hist-hash msgid (fn-hist$p-salt fn-hist$p)) fn-hist$p)
    nil fn-hist$p))

; The correspondence owns page truth and residency. It is established once by
; private construction/adoption, never recomputed by a served read.
(defun-nx fn-hist$pcorr (fn-hist$p h)
  (let ((root (nth 0 fn-hist$p)))
    (and (fn-hist$pp fn-hist$p) (fn-hist$p-wfp fn-hist$p)
         (fn-hrc-wfp root) (fn-hrs-rel h root)
         (or (equal (fn-hrc-img root) 0)
             (equal (fn-hp-x-ready-range 0 (fn-hrc-npages root) (fn-hrc-pgs root)) :ok))
         (equal (nth 1 fn-hist$p)
                (nth 2 (fn-hist-build h (fn-hist$c-empty (nth 2 fn-hist$p))))))))

(defthm fn-hist$p-append-keeps-resident-prefix
  (equal (fn-hist$p-root-ready (fn-hrc-append ev c))
         (fn-hist$p-root-ready c))
  :hints (("Goal" :in-theory (e/d (fn-hist$p-root-ready fn-hrc-append)
                                  (fn-hp-x-ready-range fn-hp-resident-row-boundsp
                                   fn-hrc-fields fn-hrc-updaters)))))

(verify-guards fn-hist$p-append
  :hints (("Goal" :in-theory (e/d (fn-hist$p-wfp)
                                  (fn-hrc-wfp fn-hist$p-root-ready fn-hist$p-count
                                   fn-hrecs$cp fn-hrc-append)))))
(verify-guards fn-hist$p-collect
  :hints (("Goal" :in-theory (disable fn-hist$p-wfp fn-hist$p-at fn-hist$p-count))))
(verify-guards fn-hist$p-msgid-records
  :hints (("Goal" :in-theory (disable fn-hist$p-collect fn-hist$p-wfp))))

(defthm fn-hist$p-count-is-history-count
  (implies (fn-hist$pcorr p h) (equal (fn-hist$p-count p) (len h)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrc-count-is-len (fn-hrecs$c (nth 0 p))))
           :in-theory (e/d (fn-hist$pcorr fn-hist$p-count fn-hist$p-root)
                          (fn-hrc-count fn-hrc-wfp fn-hrs-rel fn-hist$pp fn-hist-build)))))

(local
 (defthm fn-hist$p-root-cp
   (implies (fn-hist$pp p) (fn-hrecs$cp (nth 0 p)))
   :hints (("Goal" :in-theory (e/d (fn-hist$pp nth) (fn-hrecs$cp))))))

(defthm fn-hist$p-at-is-history-nth
  (implies (and (fn-hist$pcorr p h) (fn-hist$p-wfp p)
                (natp seq) (< seq (len h)))
           (equal (fn-hist$p-at seq p) (nth seq h)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hist$p-root-cp)
                 (:instance fn-hrc-at-is-nth (fn-hrecs$c (nth 0 p)))
                 (:instance fn-hist$p-root-at-ready (c (nth 0 p))))
           :in-theory (e/d (fn-hist$pcorr fn-hist$p-wfp fn-hist$p-at fn-hist$p-root)
                          (fn-hrc-at fn-hrs-rel fn-hist$p-root-ready fn-hrc-wfp
                           fn-hist$pp fn-hist-build fn-hrecs$cp)))))

; Abstract attachment obligations: no new executable owner decisions.
(local (in-theory (disable adt-nth-0 adt-nth-1+ adt-car-of-update-nth adt-cdr-of-update-nth)))

(defthm fn-hist$pcorr-implies-wfp
  (implies (fn-hist$pcorr p h) (fn-hist$p-wfp p))
  :hints (("Goal" :in-theory (e/d (fn-hist$pcorr) (fn-hist$p-wfp fn-hrs-rel fn-hist-build fn-hist$pp)))))
(defthm fn-hist$pcorr-implies-logicalp
  (implies (fn-hist$pcorr p h) (fn-hist$ap h))
  :hints (("Goal" :use ((:instance fn-hrs-rel-true-listp (c (nth 0 p))))
           :in-theory (e/d (fn-hist$pcorr fn-hist$ap) (fn-hrs-rel fn-hist$p-wfp fn-hist-build fn-hist$pp)))))
(local
 (defthm fn-hist$p-salt-of-corr
   (implies (fn-hist$pcorr p h) (unsigned-byte-p 32 (nth 2 p)))
   :hints (("Goal" :in-theory (e/d (fn-hist$pcorr fn-hist$pp nth)
                                   (fn-hrs-rel fn-hist$p-wfp fn-hist-build fn-hrecs$cp))))))

(local
 (defthm fn-hist$p-columns-row-agreement
  (implies (and (fn-hist$pcorr p h) (natp seq) (< seq (len h)))
    (let ((c (fn-hist-build h (fn-hist$c-empty (nth 2 p)))))
      (and (< seq (len (nth 0 c)))
           (equal (fn-hist$p-at seq p) (nth seq (nth 0 c))))))
  :hints (("Goal" :use ((:instance fn-hist$p-at-is-history-nth)
                        (:instance fn-hist$pcorr-implies-logicalp)
                        (:instance fn-hist-fold-table-facts (salt (nth 2 p))))
           :in-theory (union-theories
                         '(fn-hist$pcorr-implies-wfp fn-hist$pcorr-implies-logicalp
                           fn-hist$p-salt-of-corr fn-hist$ap)
                         (theory 'minimal-theory))))))

(local
 (defthm fn-hist$p-collect-is-columns
   (implies (and (fn-hist$pcorr p h) (fn-hist-below-p seqs (len h)))
            (equal (fn-hist$p-collect msgid seqs acc p)
                   (fn-hist$c-collect msgid seqs acc
                     (fn-hist-build h (fn-hist$c-empty (nth 2 p))))))
   :hints (("Goal" :induct (fn-hist$p-collect msgid seqs acc p)
            :in-theory (union-theories
                         '(nfix natp (:type-prescription len)
                           fn-hist$p-collect fn-hist$c-collect fn-hist-below-p
                           fn-hist$c-rowsi fn-hist$c-rows-length
                           fn-hist$p-count-is-history-count
                           fn-hist$p-columns-row-agreement)
                         (theory 'minimal-theory))))))


(defthm fn-hist$p-msgid-records-is-history-records
  (implies (and (fn-hist$pcorr p h) (stringp msgid))
           (equal (fn-hist$p-msgid-records msgid p)
                  (fn-cei-article-records-for msgid h)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hist$pcorr-implies-logicalp)
                 (:instance fn-hist$p-salt-of-corr)
                 (:instance fn-hist-fold-establishes-correspondence (salt (nth 2 p)))
                 (:instance fn-hist-fold-table-facts
                            (salt (nth 2 p)) (key (fn-hist-hash msgid (nth 2 p))))
                 (:instance fn-hist$p-collect-is-columns
                            (acc nil)
                            (seqs (fn-hist$c-bucket (fn-hist-hash msgid (nth 2 p))
                                     (fn-hist-build h (fn-hist$c-empty (nth 2 p))))))
                 (:instance fn-hist-msgid-records{correspondence}
                            (fn-hist$c (fn-hist-build h (fn-hist$c-empty (nth 2 p))))
                            (fn-hist h)))
           :in-theory (union-theories
                       '(fn-hist$pcorr fn-hist$p-msgid-records fn-hist$p-salt
                         fn-hist$p-mids-get fn-hist$c-bucket fn-hist$c-msgid-records
                         fn-hist$c-salt fn-hist$c-mids-get fn-hist$a-msgid-records
                         fn-hist$ap)
                       (theory 'minimal-theory)))))

(defthm create-fn-hist-paged{correspondence}
  (fn-hist$pcorr (create-fn-hist$p) (create-fn-hist$a))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-hist$pcorr fn-hist$p-wfp fn-hist$p-root-ready
                                    fn-hist-build fn-hist$c-empty fn-hrc-wfp fn-hrs-rel fn-hrs-img-ok))))
(defthm create-fn-hist-paged{preserved}
  (fn-hist$ap (create-fn-hist$a))
  :rule-classes nil)
(defthm fn-hist-paged-count{correspondence}
  (implies (and (fn-hist$pcorr fn-hist$p fn-hist-paged) (fn-hist$ap fn-hist-paged))
    (equal (fn-hist$p-count fn-hist$p) (fn-hist$a-count fn-hist-paged)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-hist$p-count-is-history-count
                                   (p fn-hist$p) (h fn-hist-paged)))
           :in-theory (union-theories '(fn-hist$a-count) (theory 'minimal-theory)))))
(defthm fn-hist-paged-count{guard-thm}
  (implies (and (fn-hist$pcorr fn-hist$p fn-hist-paged) (fn-hist$ap fn-hist-paged))
           (fn-hist$p-wfp fn-hist$p))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-hist$pcorr-implies-wfp
                                   (p fn-hist$p) (h fn-hist-paged)))
           :in-theory (theory 'minimal-theory))))
(defthm fn-hist-paged-at{correspondence}
  (implies (and (fn-hist$pcorr fn-hist$p fn-hist-paged) (natp seq)
                (fn-hist$ap fn-hist-paged) (< seq (fn-hist$a-count fn-hist-paged)))
           (equal (fn-hist$p-at seq fn-hist$p) (fn-hist$a-at seq fn-hist-paged)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-hist$pcorr-implies-wfp
                                   (p fn-hist$p) (h fn-hist-paged))
                        (:instance fn-hist$p-at-is-history-nth
                                   (p fn-hist$p) (h fn-hist-paged)))
           :in-theory (union-theories '(fn-hist$a-at fn-hist$a-count) (theory 'minimal-theory)))))
(defthm fn-hist-paged-at{guard-thm}
  (implies (and (fn-hist$pcorr fn-hist$p fn-hist-paged) (natp seq)
                (fn-hist$ap fn-hist-paged) (< seq (fn-hist$a-count fn-hist-paged)))
           (and (fn-hist$p-wfp fn-hist$p) (natp seq) (< seq (fn-hist$p-count fn-hist$p))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-hist$pcorr-implies-wfp
                                   (p fn-hist$p) (h fn-hist-paged))
                        (:instance fn-hist$p-count-is-history-count
                                   (p fn-hist$p) (h fn-hist-paged)))
           :in-theory (union-theories '(fn-hist$a-count) (theory 'minimal-theory)))))
(defthm fn-hist-paged-msgid-records{correspondence}
  (implies (and (fn-hist$pcorr fn-hist$p fn-hist-paged)
                (stringp msgid) (fn-hist$ap fn-hist-paged))
           (equal (fn-hist$p-msgid-records msgid fn-hist$p)
                  (fn-hist$a-msgid-records msgid fn-hist-paged)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-hist$p-msgid-records-is-history-records
                                   (p fn-hist$p) (h fn-hist-paged)))
           :in-theory (union-theories '(fn-hist$a-msgid-records) (theory 'minimal-theory)))))
(defthm fn-hist-paged-msgid-records{guard-thm}
  (implies (and (fn-hist$pcorr fn-hist$p fn-hist-paged)
                (stringp msgid) (fn-hist$ap fn-hist-paged))
           (and (stringp msgid) (fn-hist$p-wfp fn-hist$p)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-hist$pcorr-implies-wfp
                                   (p fn-hist$p) (h fn-hist-paged)))
           :in-theory (theory 'minimal-theory))))

(local
 (defthm fn-hist$p-root-append-physical
   (implies (and (fn-hrecs$cp c) (fn-hrc-wfp c))
            (fn-hrecs$cp (fn-hrc-append ev c)))
   :hints (("Goal" :in-theory (e/d (fn-hrc-append fn-hrecs$cp fn-hrc-wfp
                                    fn-hrc-fields fn-hrc-updaters)
                                   (fn-hp-x-ready-range fn-hp-resident-row-boundsp
                                    pgs-memp))))))

(local
 (defthm fn-hist$p-root-append-fields
  (and (equal (fn-hrc-img (fn-hrc-append ev c)) (fn-hrc-img c))
       (equal (fn-hrc-npages (fn-hrc-append ev c)) (fn-hrc-npages c))
       (equal (fn-hrc-pgs (fn-hrc-append ev c)) (fn-hrc-pgs c)))
  :hints (("Goal" :in-theory (e/d (fn-hrc-append)
                                  (fn-hrc-fields fn-hrc-updaters))))))

(defthm fn-hist-paged-append{correspondence}
 (implies (and (fn-hist$pcorr fn-hist$p fn-hist-paged) (fn-hist$ap fn-hist-paged))
  (fn-hist$pcorr (fn-hist$p-append ev fn-hist$p)
                 (fn-hist$a-append ev fn-hist-paged)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-hist-fold-mids-of-append
                           (h fn-hist-paged) (salt (nth 2 fn-hist$p)))
                (:instance fn-hist$p-count-is-history-count (p fn-hist$p) (h fn-hist-paged))
                (:instance fn-hist$p-root-append-physical (c (nth 0 fn-hist$p)))
                (:instance fn-hrc-append-rel (h fn-hist-paged) (fn-hrecs$c (nth 0 fn-hist$p))))
          :in-theory (union-theories
            '(fn-hist$pcorr fn-hist$p-append fn-hist$a-append fn-hist$p-wfp
              fn-hist$ap fn-hist$pp fn-hist$p-rootp fn-hist$p-saltp
              fn-hist$p-generationp fn-hist$p-boundp
              fn-hist$p-root fn-hist$p-salt fn-hist$p-mids-get
              fn-hist$p-mids-put update-fn-hist$p-root
              fn-hist$p-root-append-fields fn-hist$p-root-append-physical
              fn-hist$p-append-keeps-resident-prefix fn-hrc-append-wfp fn-hrc-append-rel
              integer-range-p unsigned-byte-p natp nfix zp len true-listp nth update-nth
              nth-update-nth true-listp-update-nth)
            (theory 'ground-zero)))))

(local
 (defthm fn-hist$p-root-reset-physical
  (implies (and (fn-hrecs$cp c) (natp salt))
           (fn-hrecs$cp (fn-hrc-reset salt c)))
  :hints (("Goal" :in-theory (e/d (fn-hrc-reset fn-hrecs$cp fn-hrs-pgs-empty
                                   fn-hrc-fields fn-hrc-updaters resize-pgs-tv pgs-memp)
                                  (fn-hp-x-ready-range fn-hp-resident-row-boundsp))))))

(defthm fn-hist-paged-append{guard-thm}
 (implies (and (fn-hist$pcorr fn-hist$p fn-hist-paged) (fn-hist$ap fn-hist-paged))
          (fn-hist$p-wfp fn-hist$p))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-hist$pcorr-implies-wfp
                                  (p fn-hist$p) (h fn-hist-paged)))
          :in-theory (theory 'minimal-theory))))
(defthm fn-hist-paged-append{preserved}
 (implies (fn-hist$ap fn-hist-paged)
          (fn-hist$ap (fn-hist$a-append ev fn-hist-paged)))
 :rule-classes nil)
(defthm fn-hist-paged-clear{correspondence}
 (implies (and (fn-hist$pcorr fn-hist$p fn-hist-paged)
               (unsigned-byte-p 32 salt))
          (fn-hist$pcorr (fn-hist$p-clear salt fn-hist$p)
                         (fn-hist$a-clear salt fn-hist-paged)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-hist$p-root-reset-physical (c (nth 0 fn-hist$p))))
          :in-theory (union-theories
            '(fn-hist$pcorr fn-hist$p-clear fn-hist$a-clear fn-hist$p-wfp
              fn-hist$pp fn-hist$p-rootp fn-hist$p-saltp fn-hist$p-generationp fn-hist$p-boundp
              fn-hist$p-root fn-hist$p-salt fn-hist$p-generation
              fn-hist$p-mids-clear update-fn-hist$p-root update-fn-hist$p-salt
              update-fn-hist$p-bound update-fn-hist$p-generation
              fn-hist$p-root-ready fn-hrc-reset fn-hrc-wfp fn-hrs-rel fn-hrs-img-ok
              fn-hrc-fields fn-hrc-updaters fn-hist-build fn-hist$c-empty
              integer-range-p unsigned-byte-p natp nfix zp len true-listp nth update-nth
              nth-update-nth true-listp-update-nth)
            (theory 'ground-zero)))))
(defthm fn-hist-paged-clear{preserved}
 (implies (and (fn-hist$ap fn-hist-paged) (unsigned-byte-p 32 salt))
          (fn-hist$ap (fn-hist$a-clear salt fn-hist-paged)))
 :rule-classes nil)
(defabsstobj fn-hist-paged
 :foundation fn-hist$p
 :recognizer (fn-hist-paged-p :logic fn-hist$ap :exec fn-hist$pp)
 :creator (create-fn-hist-paged :logic create-fn-hist$a :exec create-fn-hist$p)
 :corr-fn fn-hist$pcorr
 :exports ((fn-hist-paged-count :logic fn-hist$a-count :exec fn-hist$p-count)
           (fn-hist-paged-at :logic fn-hist$a-at :exec fn-hist$p-at)
           (fn-hist-paged-msgid-records :logic fn-hist$a-msgid-records :exec fn-hist$p-msgid-records)
           (fn-hist-paged-append :logic fn-hist$a-append :exec fn-hist$p-append :protect t)
           (fn-hist-paged-clear :logic fn-hist$a-clear :exec fn-hist$p-clear :protect t))
 :corr-fn-exists t)
