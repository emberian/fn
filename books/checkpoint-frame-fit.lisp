; Publication's frame bound, checked from concrete held lengths before any
; payload is materialized. The generic arena deliberately remains unbounded.
(in-package "ACL2")
(include-book "store-intern")
(local (include-book "arithmetic/top" :dir :system))

(defun fn-pck-frame-length (w)
  (declare (xargs :guard t))
  (if (fn-record-shapep w) (len (fn-record-payload w)) 0))
(defun fn-pck-frame-lengths (delta)
  (declare (xargs :guard t))
  (if (atom delta) nil
    (cons (fn-pck-frame-length (car delta)) (fn-pck-frame-lengths (cdr delta)))))
(defun fn-pck-frame-verdict (lengths)
  (declare (xargs :guard t))
  (cond ((atom lengths) (if (null lengths) :ok '(:refused :payload-over-frame)))
        ((and (natp (car lengths)) (< (+ 1 (car lengths)) 18446744073709551616))
         (fn-pck-frame-verdict (cdr lengths)))
        (t '(:refused :payload-over-frame))))

(defthm pck-frame-verdict-kind
  (and (not (equal (car (fn-pck-frame-verdict lengths)) :commit))
       (implies (not (eq (fn-pck-frame-verdict lengths) :ok))
                (equal (fn-pck-frame-verdict lengths) '(:refused :payload-over-frame))))
  :hints (("Goal" :induct (fn-pck-frame-verdict lengths))))

(defun fn-pck-x-frame-length (row fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (fn-held-p row)
      (let ((h (fn-record-payload row)))
        (if (and (natp h) (< h (fn-arena-count fn-arena)))
            (fn-arena-payload-len h fn-arena)
          0))
    (fn-pck-frame-length (fn-row-wire-of row fn-arena))))
(defun fn-pck-x-frame-preflight (rows fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (if (atom rows) :ok
    (if (eq (fn-pck-frame-verdict (list (fn-pck-x-frame-length (car rows) fn-arena))) :ok)
        (fn-pck-x-frame-preflight (cdr rows) fn-arena)
      '(:refused :payload-over-frame))))

(defthm fn-pck-x-frame-length-is-the-wire-length
  (equal (fn-pck-x-frame-length row fn-arena)
         (fn-pck-frame-length (fn-row-wire-of row fn-arena)))
  :hints (("Goal" :in-theory (enable fn-pck-x-frame-length fn-pck-frame-length
                                     fn-row-wire-of fn-row-bytes fn-held-wire))))
(defthm fn-pck-x-frame-preflight-is-the-wire-preflight
  (equal (fn-pck-x-frame-preflight rows fn-arena)
         (fn-pck-frame-verdict (fn-pck-frame-lengths (fn-rows-wire-of rows fn-arena))))
  :hints (("Goal" :induct (fn-pck-x-frame-preflight rows fn-arena)
           :in-theory (disable fn-pck-x-frame-length fn-pck-frame-length fn-row-wire-of))))

(defthm fn-pck-x-preflight-establishes-frame-fit
  (implies (and (equal (fn-pck-x-frame-preflight rows fn-arena) :ok)
                (member-equal row rows))
           (and (natp (fn-pck-x-frame-length row fn-arena))
                (< (+ 1 (fn-pck-x-frame-length row fn-arena)) 18446744073709551616)))
  :hints (("Goal" :induct (fn-pck-x-frame-preflight rows fn-arena)
           :in-theory (disable fn-pck-x-frame-length-is-the-wire-length fn-pck-x-frame-length
                               fn-pck-x-frame-preflight-is-the-wire-preflight))))
