; Actual provider-held prepared-row assignment and number-root staging.
; The ready/cursor predicates are carried guards, never hot revalidators.
(in-package "ACL2")
(logic)
(include-book "index-generation-issuer")
(include-book "group-number-source-pending")
(include-book "group-number-source-stage")

(defun fn-ibp-writer-assignment-ready-p (fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard t))
 (let ((builder (fn-ibp-builder fn-index-backing)))
  (and (fn-omk-widthp builder 20) (true-listp builder)
       (eq (fn-omk-at 1 builder) :assigning)
       (fn-gns-assign-cursorp (fn-omk-at 18 builder)))))
(defun fn-ibp-writer-number-ready-p (fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard t))
 (let ((builder (fn-ibp-builder fn-index-backing)))
  (and (fn-omk-widthp builder 20) (true-listp builder)
       (eq (fn-omk-at 1 builder) :numbers)
       (fn-gns-stage-cursorp (fn-omk-at 18 builder)))))

(defun fn-ibp-writer-assignment-begin (fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard (natp fuel)))
 (let* ((builder (fn-ibp-builder fn-index-backing))
        (receipt (fn-omk-at 19 builder)) (pc (fn-omk-at 6 receipt))
        (association (fn-omk-at 7 receipt))
        (publication (fn-omk-at 2 association)))
  (cond ((zp fuel) (mv :yield fuel fn-index-backing))
        ((not (and (fn-omk-widthp builder 20) (true-listp builder)
                   (eq (fn-omk-at 0 builder) :index-builder)
                   (eq (fn-omk-at 1 builder) :arena-held)
                   (eq (fn-omk-at 0 receipt) :generation-reservation)
                   (eq (fn-omk-at 0 association) :installed-publication)
                   (fn-ipub-shapep publication)
                   (equal (fn-ipub-count publication) (fn-pc-expected pc))
                   (natp (fn-ipub-number-id publication))
                   (equal (fn-omk-at 7 builder) (fn-pc-token pc))
                   (equal (fn-omk-at 6 builder) (fn-pc-expected pc))))
         (mv :recovery-required fuel fn-index-backing))
        (t
         (let* ((cursor (fn-gns-pending-begin pc (fn-ipub-number-root publication)
                                                (fn-ipub-number-id publication)))
                (next (update-nth 1 :assigning (update-nth 18 cursor builder)))
                (fn-index-backing (update-fn-ibp-builder next fn-index-backing)))
          (mv :assigning (- fuel 1) fn-index-backing))))))

(defun fn-ibp-writer-assignment-one (fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing
                 :guard (and (natp fuel) (fn-ibp-writer-assignment-ready-p fn-index-backing))
                 :verify-guards nil))
 (if (zp fuel) (mv :yield fuel fn-index-backing)
   (let* ((builder (fn-ibp-builder fn-index-backing))
          (cursor (fn-gns-assign-step (fn-omk-at 18 builder)))
          (phase (fn-gns-at 0 cursor)))
    (cond
     ((eq phase :done)
      (let* ((assigned (fn-gns-pending-result cursor))
             (stage (fn-gns-stage-begin (fn-omk-at 6 assigned) (fn-omk-at 6 builder)
                                       (fn-gns-at 2 cursor)))
             (next (update-nth 1 :numbers (update-nth 8 assigned (update-nth 18 stage builder))))
             (fn-index-backing (update-fn-ibp-builder next fn-index-backing)))
       (mv :numbers (- fuel 1) fn-index-backing)))
     ((eq phase :refused)
      (let ((fn-index-backing (update-fn-ibp-builder (update-nth 1 :recovery-required builder) fn-index-backing)))
       (mv :recovery-required (- fuel 1) fn-index-backing)))
     (t
      (let ((fn-index-backing (update-fn-ibp-builder (update-nth 18 cursor builder) fn-index-backing)))
       (mv :assigning (- fuel 1) fn-index-backing)))))))
(verify-guards fn-ibp-writer-assignment-one
 :hints (("Goal" :in-theory (e/d (fn-ibp-writer-assignment-ready-p)
                                   (fn-gns-assign-step fn-gns-assign-cursorp)))))

(defun fn-ibp-writer-number-one (fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing
                 :guard (and (natp fuel) (fn-ibp-writer-number-ready-p fn-index-backing))
                 :verify-guards nil))
 (if (zp fuel) (mv :yield fuel fn-index-backing)
   (let* ((builder (fn-ibp-builder fn-index-backing))
          (cursor (fn-gns-stage-step (fn-omk-at 18 builder)))
          (phase (fn-gns-at 0 cursor)))
    (cond
     ((eq phase :done)
      (let* ((next (update-nth 1 :layout
                     (update-nth 15 (fn-gns-at 2 cursor)
                      (update-nth 16 (fn-omk-at 1 (fn-omk-at 2 builder))
                       (update-nth 18 nil builder)))))
             (fn-index-backing (update-fn-ibp-builder next fn-index-backing)))
       (mv :layout (- fuel 1) fn-index-backing)))
     ((eq phase :refused)
      (let ((fn-index-backing (update-fn-ibp-builder (update-nth 1 :recovery-required builder) fn-index-backing)))
       (mv :recovery-required (- fuel 1) fn-index-backing)))
     (t
      (let ((fn-index-backing (update-fn-ibp-builder (update-nth 18 cursor builder) fn-index-backing)))
       (mv :numbers (- fuel 1) fn-index-backing)))))))
(verify-guards fn-ibp-writer-number-one
 :hints (("Goal" :in-theory (e/d (fn-ibp-writer-number-ready-p)
                                   (fn-gns-stage-step fn-gns-stage-cursorp)))))

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

(defthm fn-ibp-assignment-begin-establishes-ready
 (implies (equal (mv-nth 0 (fn-ibp-writer-assignment-begin fuel fn-index-backing)) :assigning)
  (fn-ibp-writer-assignment-ready-p
   (mv-nth 2 (fn-ibp-writer-assignment-begin fuel fn-index-backing))))
 :hints (("Goal" :in-theory
  (e/d (fn-ibp-writer-assignment-begin fn-ibp-writer-assignment-ready-p
        fn-gns-pending-begin)
       (fn-gns-assign-begin fn-gns-assign-cursorp fn-ipub-shapep)))))

(defthm fn-ibp-assignment-one-preserves-ready
 (implies (and (fn-ibp-writer-assignment-ready-p fn-index-backing)
               (equal (mv-nth 0 (fn-ibp-writer-assignment-one fuel fn-index-backing)) :assigning))
  (fn-ibp-writer-assignment-ready-p
   (mv-nth 2 (fn-ibp-writer-assignment-one fuel fn-index-backing))))
 :hints (("Goal" :in-theory
  (e/d (fn-ibp-writer-assignment-one fn-ibp-writer-assignment-ready-p)
       (fn-gns-assign-step fn-gns-assign-cursorp fn-gns-pending-result
        fn-gns-stage-begin)))))

(defthm fn-ibp-assignment-one-establishes-number-ready
 (implies (and (fn-ibp-writer-assignment-ready-p fn-index-backing)
               (equal (mv-nth 0 (fn-ibp-writer-assignment-one fuel fn-index-backing)) :numbers))
  (fn-ibp-writer-number-ready-p
   (mv-nth 2 (fn-ibp-writer-assignment-one fuel fn-index-backing))))
 :hints (("Goal" :in-theory
  (e/d (fn-ibp-writer-assignment-one fn-ibp-writer-assignment-ready-p
        fn-ibp-writer-number-ready-p)
       (fn-gns-assign-step fn-gns-assign-cursorp fn-gns-pending-result
        fn-gns-stage-begin fn-gns-stage-cursorp)))))

(defthm fn-ibp-number-one-preserves-ready
 (implies (and (fn-ibp-writer-number-ready-p fn-index-backing)
               (equal (mv-nth 0 (fn-ibp-writer-number-one fuel fn-index-backing)) :numbers))
  (fn-ibp-writer-number-ready-p
   (mv-nth 2 (fn-ibp-writer-number-one fuel fn-index-backing))))
 :hints (("Goal" :in-theory
  (e/d (fn-ibp-writer-number-one fn-ibp-writer-number-ready-p)
       (fn-gns-stage-step fn-gns-stage-cursorp)))))

; Concrete provider holder boundary. Ready predicates occur in carried guards;
; the one-action bodies do not revalidate cursor/root graphs.
(defun fn-mio-writer-assignment-ready-p (fn-mio$c)
 (declare (xargs :stobjs fn-mio$c :guard t))
 (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
  (ready) (fn-ibp-writer-assignment-ready-p fn-index-backing) ready))
(defun fn-mio-writer-number-ready-p (fn-mio$c)
 (declare (xargs :stobjs fn-mio$c :guard t))
 (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
  (ready) (fn-ibp-writer-number-ready-p fn-index-backing) ready))
(defun fn-mio-writer-assignment-begin (fuel fn-mio$c)
 (declare (xargs :stobjs fn-mio$c :guard (natp fuel)))
 (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
  (word left fn-index-backing)
  (fn-ibp-writer-assignment-begin fuel fn-index-backing)
  (mv word left fn-mio$c)))
(defun fn-mio-writer-assignment-one (fuel fn-mio$c)
 (declare (xargs :stobjs fn-mio$c :verify-guards nil
                 :guard (and (natp fuel) (fn-mio-writer-assignment-ready-p fn-mio$c))))
 (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
  (word left fn-index-backing)
  (fn-ibp-writer-assignment-one fuel fn-index-backing)
  (mv word left fn-mio$c)))
(verify-guards fn-mio-writer-assignment-one
 :hints (("Goal" :in-theory (enable fn-mio-writer-assignment-ready-p))))
(defun fn-mio-writer-number-one (fuel fn-mio$c)
 (declare (xargs :stobjs fn-mio$c :verify-guards nil
                 :guard (and (natp fuel) (fn-mio-writer-number-ready-p fn-mio$c))))
 (stobj-let ((fn-index-backing (fn-mio$c-provider fn-mio$c)))
  (word left fn-index-backing)
  (fn-ibp-writer-number-one fuel fn-index-backing)
  (mv word left fn-mio$c)))
(verify-guards fn-mio-writer-number-one
 :hints (("Goal" :in-theory (enable fn-mio-writer-number-ready-p))))
