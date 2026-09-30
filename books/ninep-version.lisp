; Fixed-work version negotiation and literal base9P2000 reply bytes.
(in-package "ACL2")
(include-book "ninep-fields")
(local (include-book "arithmetic/top" :dir :system))

(defun fn-9p-u16-octets (value)
 (declare (xargs :guard (natp value)))
 (list (mod value 256) (mod (floor value 256) 256)))

(defun fn-9p-u32-octets (value)
 (declare (xargs :guard (natp value)))
 (list (mod value 256) (mod (floor value 256) 256)
       (mod (floor value 65536) 256) (mod (floor value 16777216) 256)))

(defun fn-9p-version-base-p (begin count fn-octets)
 (declare (xargs :stobjs fn-octets
                 :guard (and (natp begin) (natp count)
                             (<= (+ begin count) (fn-octets-len fn-octets)))))
 (and (<= 6 count)
      (equal (fn-octets-get begin fn-octets) 57)
      (equal (fn-octets-get (+ 1 begin) fn-octets) 80)
      (equal (fn-octets-get (+ 2 begin) fn-octets) 50)
      (equal (fn-octets-get (+ 3 begin) fn-octets) 48)
      (equal (fn-octets-get (+ 4 begin) fn-octets) 48)
      (equal (fn-octets-get (+ 5 begin) fn-octets) 48)
      (or (equal count 6)
          (equal (fn-octets-get (+ 6 begin) fn-octets) 46))))

(defun fn-9p-version-base-reference (begin count octets)
 (declare (xargs :guard (and (natp begin) (natp count)
                            (<= (+ begin count) (len octets)))
                 :verify-guards nil))
 (and (<= 6 count)
      (equal (nth begin octets) 57)
      (equal (nth (+ 1 begin) octets) 80)
      (equal (nth (+ 2 begin) octets) 50)
      (equal (nth (+ 3 begin) octets) 48)
      (equal (nth (+ 4 begin) octets) 48)
      (equal (nth (+ 5 begin) octets) 48)
      (or (equal count 6) (equal (nth (+ 6 begin) octets) 46))))

(defthm fn-9p-version-base-is-literal-octet-reference
 (equal (fn-9p-version-base-p begin count fn-octets)
        (fn-9p-version-base-reference begin count fn-octets))
 :hints (("Goal" :in-theory
          (enable fn-9p-version-base-p fn-9p-version-base-reference))))

(defun fn-9p-version-response (server-msize client-msize basep)
 (declare (xargs :guard t))
 (cond
  ((not (fn-9p-profile-msizep server-msize)) '(:close :profile-unrepresentable))
  ((not (fn-9p-profile-msizep client-msize)) '(:close :invalid-msize))
  (t (let* ((msize (min server-msize client-msize))
            (version (if basep '(57 80 50 48 48 48) '(117 110 107 110 111 119 110)))
            (size (if basep 19 20)))
       (if (< msize size)
           '(:close :msize-too-small)
         (list :version msize (if basep :base :unknown)
               (append (fn-9p-u32-octets size) '(101 255 255)
                       (fn-9p-u32-octets msize)
                       (fn-9p-u16-octets (len version)) version)))))))

; The host supplies the actual parsed cursor and concrete buffer, never a
; host-decoded version string or selected reply. Only constant-size metadata
; and six source octets are inspected, independent of the requested string.
(defun fn-9p-metadata-at (index row)
 (declare (xargs :guard (natp index)))
 (if (consp row)
     (if (zp index) (car row) (fn-9p-metadata-at (1- index) (cdr row)))
   nil))

(defun fn-9p-version-at (server-msize cursor fn-octets)
 (declare (xargs :stobjs fn-octets :guard t))
 (let* ((values (fn-9p-metadata-at 6 cursor)) (client-msize (fn-9p-metadata-at 0 values))
        (span (fn-9p-metadata-at 1 values)) (begin (fn-9p-metadata-at 1 span)) (count (fn-9p-metadata-at 2 span)))
  (cond
   ((not (and (equal (fn-9p-metadata-at 0 cursor) :ninep-fields)
              (equal (fn-9p-metadata-at 1 cursor) 100) (equal (fn-9p-metadata-at 2 cursor) 65535)
              (equal (fn-9p-metadata-at 9 cursor) :parsed)
              (consp values) (consp (cdr values)) (null (cddr values))
              (consp span) (consp (cdr span)) (consp (cddr span))
              (null (cdddr span)) (equal (car span) :string)
              (natp begin) (natp count)
              (<= (+ begin count) (fn-octets-len fn-octets))))
    '(:close :invalid-version-request))
   (t (fn-9p-version-response server-msize client-msize
          (fn-9p-version-base-p begin count fn-octets))))))

(defthm fn-9p-version-negotiation-never-increases-msize
 (implies (equal (car (fn-9p-version-response server client basep)) :version)
  (and (<= (cadr (fn-9p-version-response server client basep)) server)
       (<= (cadr (fn-9p-version-response server client basep)) client)))
 :hints (("Goal" :in-theory (enable fn-9p-version-response fn-9p-profile-msizep))))

(defthm fn-9p-version-response-fits-negotiated-message
 (implies (equal (car (fn-9p-version-response server client basep)) :version)
  (and (<= (len (nth 3 (fn-9p-version-response server client basep)))
           (cadr (fn-9p-version-response server client basep)))
       (<= (len (nth 3 (fn-9p-version-response server client basep))) 20)))
 :hints (("Goal" :in-theory
          (enable fn-9p-version-response fn-9p-u32-octets fn-9p-u16-octets))))
