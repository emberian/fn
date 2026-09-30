; PRF-1081/HST-040: snapshot-specific payload handle remapping.
; Captured held metadata is retained, rather than reparsed at NIL keys/gen0.
; Payload bytes remain in the source arena and are streamed by its writer.
(in-package "ACL2")
(include-book "snapshot-held-remap")
(include-book "store-events")
(include-book "store-intern")
; Bounded outer-spine recognition never traverses a payload or a retained
; suffix.  Source validity is a carried invariant, not the execution guard.
(defun fn-orm-spinep (n x)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (zp n) (null x)
    (and (consp x) (fn-orm-spinep (- n 1) (cdr x)))))
(defthm fn-orm-spinep-is-exact-length
  (implies (natp n)
           (equal (fn-orm-spinep n x)
                  (and (true-listp x) (equal (len x) n))))
  :hints (("Goal" :induct (fn-orm-spinep n x))))

; Host-called execution dispatches only by fixed outer shape.  The source
; invariant establishes that these arms are the retained event kinds; even
; malformed inputs cannot cause an unbounded recognizer in this function.
(defun fn-orm-row (row handle)
  (declare (xargs :guard (natp handle)))
  (cond ((fn-orm-spinep 16 row) (fn-orm-held row handle))
        ((and (consp row) (eq (car row) :hstxa))
         (fn-hstxa-make (fn-hstxa-stxa row)
                        (fn-orm-held (fn-hstxa-held row) handle)))
        (t row)))

(defun fn-orm-projection (row)
  (declare (xargs :guard t))
  (cond ((fn-held-p row) (list :article (fn-orm-metadata row)))
        ((fn-hstxa-p row)
         (list :accepted-statement (fn-hstxa-stxa row)
               (fn-orm-metadata (fn-hstxa-held row))))
        (t row)))
(local
 (defthm fn-orm-valid-row-dispatch-by-definition
   (implies (fn-store-event-p row)
            (and (equal (fn-orm-spinep 16 row) (fn-held-p row))
                 (equal (and (consp row) (equal (car row) :hstxa))
                        (fn-hstxa-p row))))
   :hints (("Goal" :do-not-induct t :in-theory
            (enable fn-store-event-p fn-store-retention-event-p
                    fn-held-p fn-held-shapep
                    fn-stxe-p fn-stxe-shapep fn-stxk-p fn-stxk-shapep
                    fn-hstxa-p fn-cpe-eventp fn-th-topic-eventp
                    fn-th-local-admin-eventp fn-th-at fn-cp-nth
                    fn-stxe-internals fn-stxk-internals)))))

(local
 (defthm fn-orm-row-on-valid-input-by-definition
   (implies (fn-store-event-p row)
            (equal (fn-orm-row row handle)
                   (cond ((fn-held-p row) (fn-orm-held row handle))
                         ((fn-hstxa-p row)
                          (fn-hstxa-make (fn-hstxa-stxa row)
                                         (fn-orm-held (fn-hstxa-held row) handle)))
                         (t row))))
   :hints (("Goal" :use (fn-orm-valid-row-dispatch-by-definition)
            :in-theory (e/d (fn-orm-row)
                                   (fn-orm-valid-row-dispatch-by-definition
                                    fn-orm-spinep fn-store-event-p fn-held-p fn-hstxa-p
                                    fn-orm-held fn-hstxa-make fn-hstxa-stxa fn-hstxa-held))))))
(local
 (defthm fn-orm-held-is-store-event-by-definition
   (implies (fn-held-p row) (fn-store-event-p row))
   :hints (("Goal" :in-theory (enable fn-store-event-p)))))
(local
 (defthm fn-orm-composite-is-store-event-by-definition
   (implies (fn-hstxa-p row) (fn-store-event-p row))
   :hints (("Goal" :in-theory (enable fn-store-event-p)))))

(defthm fn-orm-row-retains-the-complete-payload-independent-projection
  (implies (and (fn-store-event-p row) (natp handle))
           (and (fn-store-event-p (fn-orm-row row handle))
                (equal (fn-orm-projection (fn-orm-row row handle))
                       (fn-orm-projection row))))
  :hints (("Goal" :do-not-induct t :cases ((fn-held-p row) (fn-hstxa-p row))
           :in-theory (e/d (fn-orm-projection fn-orm-metadata)
                           (fn-orm-row fn-store-event-p fn-hstxa-p fn-hstxa-make
                            fn-hstxa-stxa fn-hstxa-held fn-orm-held fn-held-p fn-stxa-p
                            fn-store-retention-event-p fn-stxe-p fn-stxk-p
                            fn-cpe-eventp fn-th-topic-eventp)))))

(defun fn-orm-sealsp (row)
  (declare (xargs :guard t))
  (or (fn-orm-spinep 16 row) (and (consp row) (eq (car row) :hstxa))))
(defun fn-orm-rowsp (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (and (fn-store-event-p (car rows)) (fn-orm-rowsp (cdr rows)))
    (null rows)))
(defun fn-orm-capture (rows h)
  (declare (xargs :guard (and (fn-orm-rowsp rows) (natp h))))
  (if (atom rows) nil
    (cons (fn-orm-row (car rows) h)
          (fn-orm-capture (cdr rows)
                          (if (fn-orm-sealsp (car rows)) (+ 1 h) h)))))
(defun fn-orm-at (n x)
  (declare (xargs :guard (natp n)))
  (fn-cp-nth n x))
(defun fn-orm-begin (rows)
  (declare (xargs :guard t))
  (list :remap rows 0 nil nil))
(defun fn-orm-tick (cursor)
  (declare (xargs :guard (natp (fn-orm-at 2 cursor))))
  (let ((phase (fn-orm-at 0 cursor)) (rows (fn-orm-at 1 cursor))
        (h (fn-orm-at 2 cursor)) (rev (fn-orm-at 3 cursor))
        (out (fn-orm-at 4 cursor)))
    (cond
     ((equal phase :remap)
      (if (consp rows)
          (list :continue
                (list :remap (cdr rows)
                      (if (fn-orm-sealsp (car rows)) (+ 1 h) h)
                      (cons (fn-orm-row (car rows) h) rev) out))
        (if (null rows) (list :continue (list :reverse rev h nil nil))
          (list :refused :improper-rows))))
     ((equal phase :reverse)
      (if (consp rows)
          (list :continue (list :reverse (cdr rows) h nil (cons (car rows) out)))
        (if (null rows) (list :done out) (list :refused :improper-reverse))))
     (t (list :refused :phase)))))
(defun fn-orm-value (cursor)
  (declare (xargs :guard t :verify-guards nil))
  (if (equal (fn-orm-at 0 cursor) :remap)
      (revappend (fn-orm-at 3 cursor)
                 (fn-orm-capture (fn-orm-at 1 cursor) (fn-orm-at 2 cursor)))
    (revappend (fn-orm-at 1 cursor) (fn-orm-at 4 cursor))))
(defthm fn-orm-tick-is-the-context-preserving-row-continuation
  (implies (and (member-equal (fn-orm-at 0 cursor) '(:remap :reverse))
                (true-listp (fn-orm-at 1 cursor)))
           (let ((tick (fn-orm-tick cursor)))
             (equal (fn-orm-value cursor)
                    (if (equal (car tick) :continue)
                        (fn-orm-value (nth 1 tick)) (nth 1 tick)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-orm-tick fn-orm-value fn-orm-at fn-cp-nth
                            fn-orm-capture revappend)
                           (fn-orm-row fn-orm-sealsp revappend-removal)))))

(defthm fn-orm-store-event-has-at-most-sixteen-outer-cells
  (implies (fn-store-event-p row) (<= (len row) 16))
  :hints (("Goal" :do-not-induct t :in-theory
           (enable fn-store-event-p fn-held-p fn-held-shapep
                   fn-store-retention-event-p fn-stxe-p fn-stxe-shapep
                   fn-stxk-p fn-stxk-shapep fn-hstxa-p fn-cpe-eventp
                   fn-th-topic-eventp fn-th-local-admin-eventp))))
(defthm fn-orm-continue-is-one-row-or-one-reverse-cell
  (let ((tick (fn-orm-tick cursor)))
    (implies (equal (car tick) :continue)
             (or (and (equal (fn-orm-at 0 cursor) :remap)
                      (consp (fn-orm-at 1 cursor))
                      (equal (fn-orm-at 0 (nth 1 tick)) :remap)
                      (equal (fn-orm-at 1 (nth 1 tick)) (cdr (fn-orm-at 1 cursor))))
                 (and (equal (fn-orm-at 0 cursor) :remap)
                      (null (fn-orm-at 1 cursor))
                      (equal (nth 1 tick)
                             (list :reverse (fn-orm-at 3 cursor)
                                   (fn-orm-at 2 cursor) nil nil)))
                 (and (equal (fn-orm-at 0 cursor) :reverse)
                      (consp (fn-orm-at 1 cursor))
                      (equal (fn-orm-at 0 (nth 1 tick)) :reverse)
                      (equal (fn-orm-at 1 (nth 1 tick)) (cdr (fn-orm-at 1 cursor)))
                      (equal (fn-orm-at 4 (nth 1 tick))
                             (cons (car (fn-orm-at 1 cursor))
                                   (fn-orm-at 4 cursor)))))))
  :hints (("Goal" :in-theory (e/d (fn-orm-tick fn-orm-at fn-cp-nth)
                                  (fn-orm-row fn-orm-sealsp)))))
(defthm fn-orm-continue-keeps-the-executable-cursor
  (implies (and (natp (fn-orm-at 2 cursor))
                (implies (equal (fn-orm-at 0 cursor) :remap)
                         (fn-orm-rowsp (fn-orm-at 1 cursor)))
                (true-listp (fn-orm-at 1 cursor))
                (true-listp (fn-orm-at 3 cursor))
                (true-listp (fn-orm-at 4 cursor))
                (equal (car (fn-orm-tick cursor)) :continue))
           (let ((next (nth 1 (fn-orm-tick cursor))))
             (and (natp (fn-orm-at 2 next))
                  (implies (equal (fn-orm-at 0 next) :remap)
                           (fn-orm-rowsp (fn-orm-at 1 next)))
                  (true-listp (fn-orm-at 1 next))
                  (true-listp (fn-orm-at 3 next))
                  (true-listp (fn-orm-at 4 next)))))
  :hints (("Goal" :in-theory (e/d (fn-orm-tick fn-orm-at fn-cp-nth fn-orm-rowsp)
                                  (fn-orm-row fn-orm-sealsp fn-store-event-p)))))

; Source and target arenas may name the same payload at different handles.
; This is the abstraction boundary used with the actual arena writer/load
; correspondence, which must establish the stated payload equality.
(defthm fn-orm-remapped-row-has-the-same-alpha-under-payload-correspondence
  (implies (and (fn-store-event-p row) (natp handle)
                (implies (fn-held-p row)
                         (equal (fn-row-bytes (fn-orm-row row handle) target)
                                (fn-row-bytes row source))))
           (equal (fn-row-wire-of (fn-orm-row row handle) target)
                  (fn-row-wire-of row source)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-orm-row fn-row-wire-of fn-hstxa-p
                            fn-hstxa-make fn-hstxa-stxa fn-hstxa-held)
                           (fn-orm-held fn-held-p fn-row-bytes fn-stxa-p)))))

(defun fn-orm-project-rows (rows)
  (declare (xargs :guard t))
  (if (atom rows) nil
    (cons (fn-orm-projection (car rows)) (fn-orm-project-rows (cdr rows)))))
(defthm fn-orm-capture-keeps-all-retained-row-projections
  (implies (and (fn-orm-rowsp rows) (natp h))
           (and (fn-orm-rowsp (fn-orm-capture rows h))
                (equal (len (fn-orm-capture rows h)) (len rows))
                (equal (fn-orm-project-rows (fn-orm-capture rows h))
                       (fn-orm-project-rows rows))))
  :hints (("Goal" :induct (fn-orm-capture rows h)
           :in-theory (e/d (fn-orm-capture fn-orm-rowsp fn-orm-project-rows)
                           (fn-orm-row fn-orm-row-on-valid-input-by-definition fn-orm-held
                            fn-orm-sealsp fn-orm-projection fn-store-event-p)))))

; Complete retained-row abstraction: the composite's held payload remains
; part of the promise even though its wire projection returns the original
; stxa.  This is proof vocabulary, never a producer-side revalidation.
(defun fn-orm-payload-bytes (row fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (cond ((fn-held-p row) (fn-row-bytes row fn-arena))
        ((fn-hstxa-p row) (fn-row-bytes (fn-hstxa-held row) fn-arena))
        (t nil)))
(defun fn-orm-retained-alpha (row fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (list (fn-orm-projection row) (fn-orm-payload-bytes row fn-arena)))
(defthm fn-orm-retained-alpha-under-the-physical-payload-map
  (implies (and (fn-store-event-p row) (natp handle)
                (equal (fn-orm-payload-bytes (fn-orm-row row handle) target)
                       (fn-orm-payload-bytes row source)))
           (equal (fn-orm-retained-alpha (fn-orm-row row handle) target)
                  (fn-orm-retained-alpha row source)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-orm-retained-alpha)
                                  (fn-orm-projection fn-orm-row
                                   fn-orm-row-on-valid-input-by-definition
                                   fn-orm-payload-bytes fn-store-event-p)))))

; Definitions stay closed in consumers.  A tick's execution guard is only
; its fixed-position natural handle, not this proof's suffix recognizer.
(in-theory (disable fn-orm-tail fn-orm-held fn-orm-spinep fn-orm-row fn-orm-metadata
                    fn-orm-projection fn-orm-sealsp fn-orm-rowsp fn-orm-capture
                    fn-orm-at fn-orm-begin fn-orm-tick fn-orm-value
                    fn-orm-project-rows fn-orm-payload-bytes fn-orm-retained-alpha))
