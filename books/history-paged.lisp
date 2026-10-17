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
