; Provider-owned COW row-page source traversal. The old root is retained in
; the actual generation reservation; no caller supplies a root or ordinal.
(in-package "ACL2")
(logic)
(include-book "index-backing-assignment")
(include-book "index-page-issuer")
(local (include-book "arithmetic-5/top" :dir :system))

(defun fn-ibp-writer-row-source-ready-p (fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard t))
 (let* ((builder (fn-ibp-builder fn-index-backing))
        (source (fn-omk-at 18 builder)))
  (and (fn-omk-widthp builder 20) (true-listp builder)
       (eq (fn-omk-at 1 builder) :row-source)
       (fn-omk-widthp source 3) (true-listp source)
       (eq (fn-omk-at 0 source) :row-source)
       (natp (fn-omk-at 1 source))
       (fn-ibp-directory-cursorp (fn-omk-at 2 source)))))

(defun fn-ibp-writer-row-source-begin (fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard (natp fuel)))
 (let* ((builder (fn-ibp-builder fn-index-backing))
        (old (fn-omk-at 2 (fn-omk-at 7 (fn-omk-at 19 builder))))
        (count (fn-omk-at 6 builder)) (depth (fn-ipub-row-depth old)))
  (cond
   ((zp fuel) (mv :yield fuel fn-index-backing))
   ((not (and (fn-omk-widthp builder 20) (true-listp builder)
              (eq (fn-omk-at 1 builder) :layout) (null (fn-omk-at 18 builder))
              (fn-ipub-shapep old) (natp count) (natp depth)
              (equal count (fn-ipub-count old))
              (fn-omk-widthp (fn-omk-at 8 builder) 8)
              (eq (fn-omk-at 0 (fn-omk-at 8 builder)) :assigned)))
    (mv :recovery-required fuel fn-index-backing))
   (t
    (let* ((page (floor count 256))
           (freshp (equal (mod count 256) 0))
           (continuation
            (if freshp (list :page-request :rows page nil)
              (list :row-source page
                (fn-ibp-directory-start (fn-ipub-row-root old) page depth))))
           (next (update-nth 18 continuation
                   (update-nth 1 (if freshp :layout :row-source) builder)))
           (fn-index-backing (update-fn-ibp-builder next fn-index-backing)))
     (mv (if freshp :page-request :row-source) (- fuel 1) fn-index-backing))))))

(defun fn-ibp-writer-row-source-one (fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :verify-guards nil
                 :guard (and (natp fuel) (fn-ibp-writer-row-source-ready-p fn-index-backing))))
 (if (zp fuel) (mv :yield fuel fn-index-backing)
  (let* ((builder (fn-ibp-builder fn-index-backing))
         (source (fn-omk-at 18 builder)))
   (mv-let (word cursor descriptor left)
    (fn-ibp-directory-step (fn-omk-at 2 source) 1)
    (let* ((next
            (cond ((eq word :yield)
                   (update-nth 18 (list :row-source (fn-omk-at 1 source) cursor) builder))
                  ((eq word :borrow-ready)
                   (update-nth 1 :layout
                    (update-nth 18 (list :page-request :rows (fn-omk-at 1 source) descriptor) builder)))
                  (t (update-nth 1 :recovery-required builder))))
           (fn-index-backing (update-fn-ibp-builder next fn-index-backing)))
     (mv (cond ((eq word :yield) :row-source)
               ((eq word :borrow-ready) :page-request)
               (t :recovery-required))
         (+ (- fuel 1) left) fn-index-backing))))))
(verify-guards fn-ibp-writer-row-source-one
 :hints (("Goal" :in-theory (enable fn-ibp-writer-row-source-ready-p fn-ibp-directory-cursorp))))

(local
 (defthm fn-ibp-omk-at-is-nth
  (implies (natp i) (equal (fn-omk-at i xs) (nth i xs)))
  :hints (("Goal" :induct (fn-omk-at i xs)
                  :in-theory (enable fn-omk-at nth)))))

(local
 (defun fn-ibp-update-width-induct (i n xs)
  (declare (xargs :measure (nfix i)))
  (if (zp i) (list n xs)
   (fn-ibp-update-width-induct (1- i) (1- n) (cdr xs)))))

(local
 (defthm fn-ibp-width-update-nth
  (implies (and (natp i) (natp n) (< i n) (fn-omk-widthp xs n))
           (fn-omk-widthp (update-nth i value xs) n))
  :hints (("Goal" :induct (fn-ibp-update-width-induct i n xs)
                  :in-theory (enable fn-omk-widthp update-nth)))))


(local
 (defthm fn-ibp-directory-step-preserves-cursor
  (implies (and (fn-ibp-directory-cursorp cursor) (natp fuel))
   (fn-ibp-directory-cursorp (mv-nth 1 (fn-ibp-directory-step cursor fuel))))
  :hints (("Goal" :induct (fn-ibp-directory-step cursor fuel)
                  :in-theory (enable fn-ibp-directory-step fn-ibp-directory-cursorp)))))

(defthm fn-ibp-row-source-begin-establishes-ready
 (implies (equal (mv-nth 0 (fn-ibp-writer-row-source-begin fuel fn-index-backing)) :row-source)
  (fn-ibp-writer-row-source-ready-p
   (mv-nth 2 (fn-ibp-writer-row-source-begin fuel fn-index-backing))))
 :hints (("Goal" :in-theory
  (e/d (fn-ibp-writer-row-source-begin fn-ibp-writer-row-source-ready-p
        fn-ibp-directory-start fn-ibp-directory-cursorp fn-omk-widthp)
       (fn-ipub-shapep)))))

(defthm fn-ibp-row-source-one-preserves-ready
 (implies (and (fn-ibp-writer-row-source-ready-p fn-index-backing)
               (equal (mv-nth 0 (fn-ibp-writer-row-source-one fuel fn-index-backing)) :row-source))
  (fn-ibp-writer-row-source-ready-p
   (mv-nth 2 (fn-ibp-writer-row-source-one fuel fn-index-backing))))
 :hints (("Goal" :in-theory
  (enable fn-ibp-writer-row-source-one fn-ibp-writer-row-source-ready-p
          fn-ibp-directory-cursorp fn-omk-widthp))))

(defun fn-mio-writer-row-source-ready-p (fn-mio$c)
 (declare (xargs :stobjs fn-mio$c :guard t))
 (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
  (ready) (fn-ibp-writer-row-source-ready-p fn-index-backing) ready))
(defun fn-mio-writer-row-source-begin (fuel fn-mio$c)
 (declare (xargs :stobjs fn-mio$c :guard (natp fuel)))
 (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
  (word left fn-index-backing) (fn-ibp-writer-row-source-begin fuel fn-index-backing)
  (mv word left fn-mio$c)))
(defun fn-mio-writer-row-source-one (fuel fn-mio$c)
 (declare (xargs :stobjs fn-mio$c :verify-guards nil
                 :guard (and (natp fuel) (fn-mio-writer-row-source-ready-p fn-mio$c))))
 (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
  (word left fn-index-backing) (fn-ibp-writer-row-source-one fuel fn-index-backing)
  (mv word left fn-mio$c)))
(verify-guards fn-mio-writer-row-source-one
 :hints (("Goal" :in-theory (enable fn-mio-writer-row-source-ready-p))))
