; Internal active cell for the SAME registered immutable held row.
; Actual registered producer must establish source authorization and visibility.
; This draft is not an admitted or installed host entry.
(in-package "ACL2")
(include-book "held-message-id-cursor")
(include-book "over-held-row-establishment")

; Six cells retain the original range, exact source origin and row pointer.
(defun fn-osh-make (range origin row phase active)
  (declare (xargs :guard t))
  (list :selected-held-row range origin row phase active))

(defun fn-osh-begin (range origin row)
  (declare (xargs :guard t))
  (fn-osh-make range origin row :msgid
               (fn-hmid-begin (fn-record-msgid row))))

; This carry is proof/guard vocabulary. The selected callback does not run it.
(defun fn-osh-ready-p (cell fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (and (true-listp cell) (equal (len cell) 6)
       (equal (nth 0 cell) :selected-held-row)
       (true-listp (nth 1 cell))
       (natp (fn-record-payload (nth 3 cell)))
       (< (fn-record-payload (nth 3 cell)) (fn-arena-count fn-arena))
       (or (not (fn-hf-nov (fn-held-facts (nth 3 cell))))
           (fn-hnov-p (fn-hf-nov (fn-held-facts (nth 3 cell)))))
       (case (nth 4 cell)
         (:msgid (and (fn-hmid-ready-p (nth 5 cell))
                      (equal (fn-hmid-at 1 (nth 5 cell))
                             (if (stringp (fn-record-msgid (nth 3 cell)))
                                 (fn-record-msgid (nth 3 cell)) ""))))
         (:row (and (fn-ohr-carried-p (nth 5 cell) fn-arena)
                    (implies (member-eq (nth 2 (nth 5 cell)) '(:parse :emit))
                      (and (equal (nth 0 (nth 5 cell))
                                  (if (eq (nth 2 (nth 5 cell)) :emit)
                                      (fn-obc-next-range (nth 1 cell) nil)
                                    (nth 1 cell)))
                           (equal (nth 1 (nth 5 cell)) (nth 2 cell))))))
         (:skip t)
         (otherwise nil))))

(defun fn-osh-one (cell fn-arena)
  (declare (xargs :stobjs fn-arena :guard (fn-osh-ready-p cell fn-arena)
                  :verify-guards nil))
  (let ((range (nth 1 cell)) (origin (nth 2 cell)) (row (nth 3 cell))
        (active (nth 5 cell)))
    (case (nth 4 cell)
      (:msgid
       (let* ((next (fn-hmid-one active)) (word (fn-hmid-status next)))
         (cond
          ((eq word :yield)
           (mv nil (fn-osh-make range origin row :msgid next)))
          ((eq word :invalid)
           (mv nil (fn-osh-make range origin row :skip
                     (fn-obc-begin (fn-obc-next-range range (nth 5 range)) origin))))
          (t (mv nil (fn-osh-make range origin row :row
                        (fn-ohr-selected-row-begin range origin row fn-arena)))))))
      (:row
       (if (member-eq (nth 2 active) '(:parse :emit))
           (mv-let (out next) (fn-ohr-active-one active fn-arena)
             (mv out (and next (fn-osh-make range origin row :row next))))
         (mv nil (fn-osh-make range origin row :skip active))))
      (otherwise (mv nil cell)))))

(local
 (defthm fn-osh-carried-row-is-true-list
   (implies (fn-ohr-carried-p s fn-arena) (true-listp s))
   :hints (("Goal" :in-theory
             (e/d (fn-ohr-carried-p) (fn-lpc-ready-p fn-npw-piecesp))))))

(verify-guards fn-osh-one
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-ohr-carried-active-is-active
                            (s (nth 5 cell))))
           :in-theory (e/d (fn-osh-ready-p fn-hmid-ready-p)
                           (fn-hmid-one fn-hmid-cursorp fn-ohr-active-p
                            fn-ohr-carried-p fn-ohr-active-one
                            fn-ohr-selected-row-begin nth)))))

(defthm fn-osh-one-retains-original-row-source-and-range-unfolds
  (let ((next (mv-nth 1 (fn-osh-one cell fn-arena))))
    (implies next
      (and (equal (nth 1 next) (nth 1 cell))
           (equal (nth 2 next) (nth 2 cell))
           (equal (nth 3 next) (nth 3 cell)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
            (e/d (fn-osh-one fn-osh-make)
                 (fn-hmid-one fn-hmid-status fn-ohr-active-one
                  fn-ohr-selected-row-begin fn-obc-begin fn-obc-next-range)))))

(defthm fn-osh-begin-establishes-held-row-carry
  (implies (and (true-listp range)
                (natp (fn-record-payload row))
                (< (fn-record-payload row) (fn-arena-count fn-arena))
                (or (not (fn-hf-nov (fn-held-facts row)))
                    (fn-hnov-p (fn-hf-nov (fn-held-facts row)))))
           (fn-osh-ready-p (fn-osh-begin range origin row) fn-arena))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hmid-begin-establishes-original-predicate-carry
                            (text (fn-record-msgid row))))
           :in-theory (e/d (fn-osh-begin fn-osh-make fn-osh-ready-p
                            fn-hmid-begin fn-hmid-at fn-ag-car fn-ag-cdr)
                           (fn-hmid-ready-p fn-hmid-suffix-ok
                            fn-scat-msgid-idp)))))

(local
 (defthm fn-osh-row-begin-coordinates
   (let ((s (fn-ohr-selected-row-begin range origin row fn-arena)))
     (implies (member-eq (nth 2 s) '(:parse :emit))
       (and (equal (nth 0 s)
                   (if (eq (nth 2 s) :emit) (fn-obc-next-range range nil) range))
            (equal (nth 1 s) origin))))
   :hints (("Goal" :in-theory
     (e/d (fn-ohr-selected-row-begin fn-obc-row-ready fn-obc-make fn-obc-begin)
          (fn-lpc-begin fn-npw-column-pieces fn-obc-next-range))))))
(local
 (defthm fn-osh-row-one-coordinates
   (let ((next (mv-nth 1 (fn-ohr-active-one s fn-arena))))
     (implies (member-eq (nth 2 next) '(:parse :emit))
       (and (equal (nth 0 next)
                   (if (and (eq (nth 2 s) :parse) (eq (nth 2 next) :emit))
                       (fn-obc-next-range (nth 0 s) nil) (nth 0 s)))
            (equal (nth 1 next) (nth 1 s)))))
   :hints (("Goal" :in-theory
     (e/d (fn-ohr-active-one fn-obc-row-ready fn-obc-make fn-obc-begin)
          (fn-lpc-tick fn-npw-one fn-obc-next-range fn-obc-parser-pieces
           fn-lpc-tombstonep))))))

(local
 (defthm fn-osh-row-one-parse-only-from-parse
   (implies (equal (nth 2 (mv-nth 1 (fn-ohr-active-one s fn-arena))) :parse)
            (equal (nth 2 s) :parse))
   :hints (("Goal" :in-theory
     (e/d (fn-ohr-active-one fn-obc-row-ready fn-obc-make fn-obc-begin)
          (fn-lpc-tick fn-npw-one fn-obc-next-range fn-obc-parser-pieces
           fn-lpc-tombstonep))))))

(defthm fn-osh-one-preserves-held-row-carry
  (implies (fn-osh-ready-p cell fn-arena)
    (let ((next (mv-nth 1 (fn-osh-one cell fn-arena))))
      (or (not next) (fn-osh-ready-p next fn-arena))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hmid-one-preserves-original-predicate-carry
                            (cursor (nth 5 cell)))
                 (:instance fn-ohr-active-one-preserves-carried-row-domain
                            (s (nth 5 cell)))
                 (:instance fn-ohr-selected-row-begin-establishes-carried-row-domain
                            (range (nth 1 cell)) (origin (nth 2 cell))
                            (row (nth 3 cell))))
           :in-theory
           (e/d (fn-osh-one fn-osh-make fn-osh-ready-p fn-hmid-one
                  fn-hmid-ready-p fn-hmid-at fn-ag-car fn-ag-cdr)
                (fn-hmid-cursorp fn-hmid-char-ok fn-hmid-suffix-ok fn-hmid-status
                 fn-scat-msgid-idp fn-ohr-active-one fn-ohr-carried-p
                 fn-ohr-selected-row-begin fn-obc-begin fn-obc-next-range nth)))))

; The actual bounded validator installs a row only under the original
; Message-ID predicate on the SAME retained held-row string.
(defthm fn-osh-msgid-one-row-install-has-original-msgid
  (implies (and (fn-osh-ready-p cell fn-arena)
                (equal (nth 4 cell) :msgid)
                (equal (nth 4 (mv-nth 1 (fn-osh-one cell fn-arena))) :row))
           (fn-scat-msgid-idp (fn-record-msgid (nth 3 cell))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hmid-one-preserves-original-predicate-carry
                            (cursor (nth 5 cell)))
                 (:instance fn-hmid-completed-status-is-original-predicate
                            (cursor (fn-hmid-one (nth 5 cell)))))
           :in-theory
           (e/d (fn-osh-ready-p fn-osh-one fn-osh-make fn-hmid-one
                  fn-hmid-status fn-hmid-at fn-ag-car fn-ag-cdr)
                (fn-hmid-ready-p fn-hmid-cursorp fn-hmid-char-ok
                 fn-ohr-selected-row-begin fn-obc-begin fn-obc-next-range
                 fn-scat-msgid-idp fn-ohr-active-one)))))
