; Private P3 root transfer. A fresh history foundation owns the constructed
; resident image; swap-stobjs returns its previous empty backing to the
; publisher. No page image is copied and no live old root is overwritten.
(in-package "ACL2")
(include-book "history-paged")
(local (include-book "arithmetic/top" :dir :system))

(defstobj fn-hrecs$s
  (fn-hrs-stage-pgs :type pgs-mem)
  (fn-hrs-stage-oct :type fn-octets-pg)
  (fn-hrs-stage-img :type (integer 0 1) :initially 0)
  (fn-hrs-stage-salt :type (integer 0 *) :initially 0)
  (fn-hrs-stage-nimg :type (integer 0 *) :initially 0)
  (fn-hrs-stage-lens :type t :initially (0 0 0 0 0))
  (fn-hrs-stage-starts :type t :initially (1 1 1 1 1))
  (fn-hrs-stage-npages :type (integer 0 *) :initially 0)
  (fn-hrs-stage-txid :type (integer 0 *) :initially 0)
  (fn-hrs-stage-sfx :type (array t (0)) :initially nil :resizable t)
  (fn-hrs-stage-lo :type (integer 0 *) :initially 0)
  (fn-hrs-stage-hi :type (integer 0 *) :initially 0)
  :congruent-to fn-hrecs$c :inline t)

(defun fn-hist$p-adopt-stage (generation fn-hrecs$s fn-hist$p)
  (declare (xargs :stobjs (fn-hrecs$s fn-hist$p)
                  :guard (and (posp generation) (fn-hrc-wfp fn-hrecs$s)
                              (fn-hist$p-root-ready fn-hrecs$s)
                              (unsigned-byte-p 32 (fn-hrc-salt fn-hrecs$s))
                              (fn-hist$p-wfp fn-hist$p)
                              (equal (fn-hist$p-count fn-hist$p) 0)
                              (equal (fn-hist$p-bound fn-hist$p) 0))
                  :verify-guards nil))
  (let ((salt (fn-hrc-salt fn-hrecs$s)))
   (stobj-let ((fn-hrecs$c (fn-hist$p-root fn-hist$p)))
             (fn-hrecs$c fn-hrecs$s)
             (swap-stobjs fn-hrecs$c fn-hrecs$s)
             (let* ((fn-hist$p (fn-hist$p-mids-clear fn-hist$p))
                    (fn-hist$p (update-fn-hist$p-generation generation fn-hist$p))
                    (fn-hist$p (update-fn-hist$p-salt salt fn-hist$p)))
               (mv fn-hrecs$s fn-hist$p)))))

(defun fn-hist$p-index-root-row (ordinal fn-hist$p)
  (declare (xargs :stobjs fn-hist$p
                  :guard (and (fn-hist$p-wfp fn-hist$p) (natp ordinal)
                              (< ordinal (fn-hist$p-count fn-hist$p)))
                  :verify-guards nil))
  (let ((m (fn-hist-key-msgid (fn-hist$p-at ordinal fn-hist$p))))
    (if (stringp m)
        (let ((key (fn-hist-hash m (fn-hist$p-salt fn-hist$p))))
          (fn-hist$p-mids-put key (cons ordinal (fn-hist$p-mids-get key fn-hist$p))
                             fn-hist$p))
      fn-hist$p)))

(defun fn-hist$p-root-index-next (ordinal fn-hist$p)
  (declare (xargs :stobjs fn-hist$p
                  :guard (and (fn-hist$p-wfp fn-hist$p) (natp ordinal))
                  :verify-guards nil))
  (let ((count (fn-hist$p-count fn-hist$p)))
    (cond ((< count ordinal) (mv '(:refused :history-index-ordinal) ordinal fn-hist$p))
          ((equal ordinal count)
           (let ((fn-hist$p (update-fn-hist$p-bound 1 fn-hist$p)))
             (mv :done ordinal fn-hist$p)))
          (t (let ((fn-hist$p (fn-hist$p-index-root-row ordinal fn-hist$p)))
               (mv :yield (+ 1 ordinal) fn-hist$p))))))

(defun fn-hist$p-root-generation (fn-hist$p)
  (declare (xargs :stobjs fn-hist$p))
  (and (equal (fn-hist$p-bound fn-hist$p) 1) (fn-hist$p-generation fn-hist$p)))

(verify-guards fn-hist$p-adopt-stage
 :hints (("Goal" :in-theory (union-theories '(posp natp) (theory 'minimal-theory)))))
(verify-guards fn-hist$p-index-root-row
 :hints (("Goal" :in-theory (disable fn-hist$p-wfp fn-hist$p-at fn-hist$p-count))))
(verify-guards fn-hist$p-root-index-next
 :hints (("Goal" :in-theory (disable fn-hist$p-wfp fn-hist$p-at fn-hist$p-count fn-hist$p-index-root-row))))

(defthm fn-hist$p-root-is-physical
 (implies (fn-hist$pp p) (fn-hrecs$cp (fn-hist$p-root p)))
 :hints (("Goal" :in-theory (e/d (fn-hist$pp fn-hist$p-root nth) (fn-hrecs$cp)))))
(defun fn-hist$p-read (ordinal fn-hist$p)
 (declare (xargs :stobjs fn-hist$p
                 :guard (and (natp ordinal) (fn-hist$p-wfp fn-hist$p))
                 :guard-hints (("Goal" :in-theory (disable fn-hist$p-wfp fn-hist$p-at fn-hist$p-count)))))
 (if (< ordinal (fn-hist$p-count fn-hist$p))
     (list :ok (fn-hist$p-at ordinal fn-hist$p))
   '(:refused :history-root-ordinal)))
(defthm fn-hist$p-read-is-history-row
 (implies (and (fn-hist$pcorr p h) (natp ordinal) (< ordinal (len h)))
          (equal (fn-hist$p-read ordinal p) (list :ok (nth ordinal h))))
 :hints (("Goal" :use ((:instance fn-hist$p-at-is-history-nth (seq ordinal)))
          :in-theory (e/d (fn-hist$p-read)
                           (fn-hist$pcorr fn-hist$p-wfp fn-hist$p-at fn-hist$p-count)))))
(defthm fn-hist$p-append-keeps-wfp
 (implies (and (fn-hist$pp p) (fn-hist$p-wfp p))
          (fn-hist$p-wfp (fn-hist$p-append ev p)))
 :hints (("Goal" :use ((:instance fn-hrc-append-wfp (fn-hrecs$c (fn-hist$p-root p))))
          :in-theory (union-theories
             '(fn-hist$p-append fn-hist$p-wfp fn-hist$p-root fn-hist$p-mids-put
               update-fn-hist$p-root fn-hist$pp fn-hist$p-rootp fn-hist$p-saltp
               fn-hist$p-generationp fn-hist$p-boundp nth update-nth nth-update-nth
               len true-listp nfix natp zp car-cons cdr-cons adt-car-of-update-nth
               fn-hist$p-append-keeps-resident-prefix)
             (theory 'minimal-theory)))))

(defthm fn-hist$p-index-next-keeps-wfp
 (implies (and (fn-hist$pp p) (fn-hist$p-wfp p) (natp ordinal))
          (fn-hist$p-wfp (mv-nth 2 (fn-hist$p-root-index-next ordinal p))))
 :hints (("Goal" :in-theory (union-theories
  '(fn-hist$p-root-index-next fn-hist$p-index-root-row fn-hist$p-wfp
    fn-hist$p-root fn-hist$p-mids-put update-fn-hist$p-bound
    fn-hist$pp fn-hist$p-rootp fn-hist$p-saltp fn-hist$p-generationp fn-hist$p-boundp
    nth update-nth nth-update-nth car-cons cdr-cons len true-listp nfix natp zp
    adt-car-of-update-nth adt-consp-of-update-nth)
  (theory 'minimal-theory)))))
(defthm fn-hist$p-adopt-stage-keeps-wfp
 (implies (and (posp generation) (fn-hrc-wfp stage) (fn-hist$p-root-ready stage))
          (fn-hist$p-wfp (mv-nth 1 (fn-hist$p-adopt-stage generation stage p))))
 :hints (("Goal" :in-theory (union-theories
  '(fn-hist$p-adopt-stage fn-hist$p-wfp fn-hist$p-root fn-hist$p-mids-clear
    update-fn-hist$p-root update-fn-hist$p-salt update-fn-hist$p-generation
    nth update-nth nth-update-nth car-cons cdr-cons nfix natp zp
    adt-car-of-update-nth adt-consp-of-update-nth)
  (theory 'minimal-theory)))))
