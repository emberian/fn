(in-package "ACL2")
(include-book "def-loop-fixture-dep")

(defun fn-xrt-srcs-handles-loop (srcs k rev)
  (declare (xargs :guard (and (natp k) (true-listp rev))))
  (if (or (atom srcs) (zp k))
      (revappend rev nil)
    (fn-xrt-srcs-handles-loop (cdr srcs) (1- k)
                              (cons (and (natp (car srcs)) (car srcs)) rev))))

(defun fn-xrt-srcs-handles (srcs k)
  (declare (xargs :guard (natp k) :verify-guards nil))
  (mbe :logic (if (or (atom srcs) (zp k))
                  nil
                (cons (and (natp (car srcs)) (car srcs))
                      (fn-xrt-srcs-handles (cdr srcs) (1- k))))
       :exec (fn-xrt-srcs-handles-loop srcs k nil)))

(defthm fn-xrt-srcs-handles-loop-is-srcs-handles
  (equal (fn-xrt-srcs-handles-loop srcs k rev)
         (revappend rev (fn-xrt-srcs-handles srcs k))))

(verify-guards fn-xrt-srcs-handles)

(defun fn-xrt-quiet-files-loop (retired named fn-arena$x rev)
  (declare (xargs :stobjs fn-arena$x
                  :guard (and (nat-listp retired) (true-listp named) (true-listp rev))))
  (cond ((atom retired) (revappend rev nil))
        ((and (not (member (car retired) named))
              (equal (fn-arx-file-count (car retired) fn-arena$x) 0))
         (fn-xrt-quiet-files-loop (cdr retired) named fn-arena$x (cons (car retired) rev)))
        (t (fn-xrt-quiet-files-loop (cdr retired) named fn-arena$x rev))))

(defun fn-xrt-quiet-files (retired named fn-arena$x)
  (declare (xargs :stobjs fn-arena$x
                  :guard (and (nat-listp retired) (true-listp named))
                  :verify-guards nil))
  (mbe :logic
       (cond ((atom retired) nil)
             ((and (not (member (car retired) named))
                   (equal (fn-arx-file-count (car retired) fn-arena$x) 0))
              (cons (car retired) (fn-xrt-quiet-files (cdr retired) named fn-arena$x)))
             (t (fn-xrt-quiet-files (cdr retired) named fn-arena$x)))
       :exec (fn-xrt-quiet-files-loop retired named fn-arena$x nil)))

(defthm fn-xrt-quiet-files-loop-is-quiet-files
  (equal (fn-xrt-quiet-files-loop retired named fn-arena$x rev)
         (revappend rev (fn-xrt-quiet-files retired named fn-arena$x)))
  :hints (("Goal" :in-theory (disable fn-arx-file-count))))

(verify-guards fn-xrt-quiet-files)

