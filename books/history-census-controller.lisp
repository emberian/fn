; The producer's row-at-a-time census. Source offers come from the captured
; source adapter; no history-list conversion or whole-record codec executes.
(in-package "ACL2")
(include-book "history-record-cursor")
(include-book "history-image-census")

; Seven fixed cells: phase, expected rows, completed count, padded pool bytes,
; pending codec continuation, capture context, resource lease reference.
(defun fn-hct-shapep (c)
  (declare (xargs :guard t))
  (and (fn-hrcur-widthp c 7)
       (member-eq (fn-hrcur-field 0 c) '(:need-row :codec :prepared :refused))
       (unsigned-byte-p 61 (fn-hrcur-field 1 c))
       (natp (fn-hrcur-field 2 c)) (<= (fn-hrcur-field 2 c) (fn-hrcur-field 1 c))
       (unsigned-byte-p 64 (fn-hrcur-field 3 c))
       (implies (eq (fn-hrcur-field 0 c) :prepared)
                (equal (fn-hrcur-field 2 c) (fn-hrcur-field 1 c)))
       (implies (member-eq (fn-hrcur-field 0 c) '(:need-row :codec))
                (< (fn-hrcur-field 2 c) (fn-hrcur-field 1 c)))))

(defun fn-hct-begin (expected capture lease)
  (declare (xargs :guard t))
  (if (unsigned-byte-p 61 expected)
      (list (if (zp expected) :prepared :need-row) expected 0 0 nil capture lease)
    (list :refused 0 0 0 nil capture lease)))

(defun fn-hct-offer (c ordinal source)
  (declare (xargs :guard t))
  (if (not (and (fn-hct-shapep c) (eq (fn-hrcur-field 0 c) :need-row)
                 (equal ordinal (fn-hrcur-field 2 c))))
      (mv :stale c)
    (let ((capture (fn-hrcur-field 5 c)) (lease (fn-hrcur-field 6 c)))
      (mv :started
          (list :codec (fn-hrcur-field 1 c) ordinal (fn-hrcur-field 3 c)
                (fn-hrcur-census-begin source (list capture ordinal) lease) capture lease)))))

(defun fn-hct-tick (c)
  (declare (xargs :guard t))
  (if (not (fn-hct-shapep c)) (mv '(:refused :cursor) nil c)
    (let ((phase (fn-hrcur-field 0 c)) (expected (fn-hrcur-field 1 c))
          (count (fn-hrcur-field 2 c)) (pool (fn-hrcur-field 3 c))
          (codec (fn-hrcur-field 4 c))
          (capture (fn-hrcur-field 5 c)) (lease (fn-hrcur-field 6 c)))
      (cond
       ((eq phase :prepared) (mv :prepared (list count pool) c))
       ((eq phase :need-row) (mv :need-row count c))
       ((eq phase :refused) (mv '(:refused :census) nil c))
       (t
        (mv-let (v encoded next) (fn-hrcur-census-tick codec)
          (cond
           ((eq v :continue)
            (mv :continue nil (list :codec expected count pool next capture lease)))
           ((and (eq v :prepared) (unsigned-byte-p 64 encoded))
            (mv-let (v2 count2 pool2) (fn-hcc-row count pool count encoded)
              (if (eq v2 :counted)
                  (mv :row-done encoded
                      (list (if (equal count2 expected) :prepared :need-row)
                            expected count2 pool2 nil capture lease))
                (mv (list :refused v2) nil
                    (list :refused expected count pool nil capture lease)))))
           (t (mv '(:refused :codec) nil
                  (list :refused expected count pool nil capture lease))))))))))

(defthm fn-hct-begin-keeps-shape
  (fn-hct-shapep (fn-hct-begin expected capture lease)))

(defthm fn-hct-offer-keeps-shape
  (implies (fn-hct-shapep c)
           (fn-hct-shapep (mv-nth 1 (fn-hct-offer c ordinal source))))
  :hints (("Goal" :in-theory (disable fn-hrcur-census-begin))))

(defthm fn-hct-offered-resident-establishes-codec
  (implies (and (fn-hct-shapep c)
                (equal (fn-hrcur-field 0 c) :need-row)
                (equal ordinal (fn-hrcur-field 2 c))
                (fn-hrcur-tree-domainp row)
                (< (len (fn-scc-encode row)) *fn-hrcur-u64-bound*))
           (let ((next (mv-nth 1 (fn-hct-offer c ordinal (list :resident row)))))
             (and (fn-hrcur-census-invariantp (fn-hrcur-field 4 next))
                  (equal (fn-hrcur-census-total (fn-hrcur-field 4 next))
                         (len (fn-scc-encode row))))))
  :hints (("Goal" :use ((:instance fn-hrcur-census-begin-refines-length
                          (capture (list (fn-hrcur-field 5 c) ordinal))
                          (lease (fn-hrcur-field 6 c))))
           :in-theory
           (union-theories
            '(fn-hct-offer fn-hrcur-field mv-nth car-cons cdr-cons
              (:e equal) (:e zp) (:e binary-+) (:e consp))
            (theory 'minimal-theory)))))

(defthm fn-hct-tick-keeps-shape
  (implies (fn-hct-shapep c)
           (fn-hct-shapep (mv-nth 2 (fn-hct-tick c))))
  :hints (("Goal" :in-theory (e/d (fn-hcc-row)
                                      (fn-hrcur-census-tick fn-hp-pad8-count)))))

(defthm fn-hct-tick-keeps-capture-and-lease
  (and (equal (fn-hrcur-field 5 (mv-nth 2 (fn-hct-tick c)))
              (fn-hrcur-field 5 c))
       (equal (fn-hrcur-field 6 (mv-nth 2 (fn-hct-tick c)))
              (fn-hrcur-field 6 c)))
  :hints (("Goal" :in-theory (disable fn-hrcur-census-tick fn-hcc-row))))

; The child codec invariant and exact total are carried proof state. Neither
; is evaluated by the controller's guard or scheduling step.
(defthm fn-hct-continuation-keeps-census
  (implies (not (equal (mv-nth 0 (fn-hct-tick c)) :row-done))
           (and (equal (fn-hrcur-field 2 (mv-nth 2 (fn-hct-tick c)))
                       (fn-hrcur-field 2 c))
                (equal (fn-hrcur-field 3 (mv-nth 2 (fn-hct-tick c)))
                       (fn-hrcur-field 3 c))))
  :hints (("Goal" :in-theory (disable fn-hrcur-census-tick fn-hcc-row))))

(defthm fn-hct-continuation-keeps-codec-total
  (implies (and (fn-hct-shapep c)
                (equal (fn-hrcur-field 0 c) :codec)
                (fn-hrcur-census-invariantp (fn-hrcur-field 4 c))
                (equal (mv-nth 0 (fn-hct-tick c)) :continue))
           (and (fn-hrcur-census-invariantp
                 (fn-hrcur-field 4 (mv-nth 2 (fn-hct-tick c))))
                (equal (fn-hrcur-census-total
                        (fn-hrcur-field 4 (mv-nth 2 (fn-hct-tick c))))
                       (fn-hrcur-census-total (fn-hrcur-field 4 c)))))
  :hints (("Goal" :use ((:instance fn-hrcur-census-tick-refines-length
                                  (c (fn-hrcur-field 4 c))))
           :in-theory (disable fn-hrcur-census-tick fn-hcc-row
                         fn-hrcur-census-invariantp fn-hrcur-census-total
                         fn-hrcur-census-tick-refines-length))))

(local
 (defthm fn-hct-completed-row-with-shape
  (implies
   (and (fn-hct-shapep c)
        (equal (fn-hrcur-field 0 c) :codec)
        (equal (fn-hrcur-field 2 c) (len h))
        (equal (fn-hrcur-field 3 c) (fn-hp-pes-len h))
        (fn-hrcur-census-invariantp (fn-hrcur-field 4 c))
        (equal (fn-hrcur-census-total (fn-hrcur-field 4 c))
               (len (fn-scc-encode ev)))
        (equal (mv-nth 0 (fn-hct-tick c)) :row-done))
   (and (equal (fn-hrcur-field 2 (mv-nth 2 (fn-hct-tick c)))
                (len (append h (list ev))))
        (equal (fn-hrcur-field 3 (mv-nth 2 (fn-hct-tick c)))
                (fn-hp-pes-len (append h (list ev))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrcur-census-tick-refines-length
                             (c (fn-hrcur-field 4 c)))
                 (:instance fn-hcc-counted-row-preserves-history-census
                            (count (fn-hrcur-field 2 c))
                            (pool (fn-hrcur-field 3 c))
                            (ordinal (fn-hrcur-field 2 c))
                            (encoded (mv-nth 1 (fn-hrcur-census-tick
                                               (fn-hrcur-field 4 c))))))
           :in-theory (disable fn-hrcur-census-tick
                        fn-hrcur-census-invariantp fn-hrcur-census-total
                        fn-hrcur-census-tick-refines-length
                        fn-hcc-counted-row-preserves-history-census
                        fn-hcc-row fn-hp-pes-len fn-scc-encode fn-scc-program fn-scc-encode-is-program len)))))

; Shape and codec phase follow from :row-done. The weakened boundary was
; proved before removing those redundant hypotheses.
(defthm fn-hct-completed-row-refines-history-census
  (implies
   (and (equal (fn-hrcur-field 2 c) (len h))
        (equal (fn-hrcur-field 3 c) (fn-hp-pes-len h))
        (fn-hrcur-census-invariantp (fn-hrcur-field 4 c))
        (equal (fn-hrcur-census-total (fn-hrcur-field 4 c))
               (len (fn-scc-encode ev)))
        (equal (mv-nth 0 (fn-hct-tick c)) :row-done))
   (and (equal (fn-hrcur-field 2 (mv-nth 2 (fn-hct-tick c)))
                (len (append h (list ev))))
        (equal (fn-hrcur-field 3 (mv-nth 2 (fn-hct-tick c)))
                (fn-hp-pes-len (append h (list ev))))))
  :hints (("Goal" :use ((:instance fn-hct-completed-row-with-shape))
           :in-theory (union-theories
              '(fn-hct-tick fn-hct-shapep member-equal mv-nth car-cons cdr-cons
                (:e equal) (:e zp) (:e binary-+) (:e consp))
              (theory 'minimal-theory)))))

(in-theory (disable fn-hct-shapep fn-hct-begin fn-hct-offer fn-hct-tick))
